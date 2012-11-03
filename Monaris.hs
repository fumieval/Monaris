{-# LANGUAGE MonadComprehensions, TupleSections, ImplicitParams, FlexibleContexts #-}
import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Monad.Reader
import Data.List
import Data.Function
import Data.Array
import Data.Char
import Data.Vect.Double
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.Free
import FreeGame
import FreeGame.Backends.DXFI

type Coord = (Int, Int)
(a, b) #+# (c, d) = (a + c, b + d)
(a, b) #-# (c, d) = (a - c, b - d)
k *# (a, b) = (k * a, k * b)
(a, b) #/ k = (div a k, div b k)

data Color = Red | Yellow | Green | Cyan | Blue | Magenta | Orange deriving (Eq, Ord, Enum)

type Polyomino = [Coord]
translate :: Coord -> Polyomino -> Polyomino
translate = map . (#+#)

type Field = Array Coord (Maybe Color)

polyominos = [([(0,0),(0,1),(0,2),(0,3)], Cyan)
             ,([(0,0),(0,1),(1,0),(1,1)], Yellow)
             ,([(0,0),(0,1),(0,2),(1,2)], Orange)
             ,([(0,0),(0,1),(0,2),(-1,2)], Blue)
             ,([(0,0),(0,1),(1,1),(1,2)], Green)
             ,([(0,0),(0,1),(-1,1),(-1,2)], Red)
             ,([(0,0),(-1,0),(1,0),(0,1)], Magenta)]

data Rotation = CCW | CW deriving (Show, Eq, Ord)

rotate :: Rotation -> Coord -> Polyomino -> Polyomino
rotate CCW center = map $ (#/2) . (#+#center) . (\(x, y) -> (-y, x)) . (#-#center) . (2*#)
rotate CW center  = map $ (#/2) . (#+#center) . (\(x, y) -> (y, -x)) . (#-#center) . (2*#)

centers :: Polyomino -> [Coord]
centers cs = cs' ++ [i | i@(c, r) <- map ((1,1)#+#) cs'
    , let c0 = minimum (map fst cs'), let c1 = maximum (map fst cs')
    , let r0 = minimum (map snd cs'), let r1 = maximum (map snd cs')
    , c0 < c && c < c1, r0 < r && r < r1] where cs' = map (2*#) cs

completeLines :: Field -> [Int]
completeLines field = [r | r <- [r0..r1], all isJust [field ! (c, r) | c <- [c0..c1]]] where
    ((c0, r0), (c1, r1)) = bounds field

deleteLine :: Field -> Int -> Field
deleteLine field n = array bnd [ a' | a@(ix@(c, r), _) <- assocs field
    , let a' | r == r0 = (ix, Nothing)
             | r <= n = (ix, field ! (c, r - 1))
             | otherwise = a] where
         bnd@((_, r0), _) = bounds field

putToField :: Color -> Field -> Polyomino -> Maybe Field
putToField color field omino = [field // map (,Just color) omino
    | all (inRange $ bounds field) omino
    , all (isNothing . (field !)) omino]

getPolyomino = liftF $ Randomness (0, length polyominos - 1) (polyominos!!)
type Inp = ((Bool, Bool, Bool, Bool, Bool, Bool), (Bool, Bool, Bool, Bool, Bool, Bool))
place :: (?picBlocks :: M.Map (Color, Int) Picture, ?blockSize :: Double, ?picBlockBackground :: Picture)
    => Polyomino -> Color -> Field -> Int -> Free Game (Maybe Field)
place polyomino color field period = do
    let p = translate (5, negate $ minimum $ map snd polyomino) polyomino
    if isJust $ putF p
        then run 0 (Left handleNotLandingParam) (False, False, False, False, False, False) `evalStateT` p
        else return Nothing
    where
    run t param ks = do
        [l',r',u',d',z',x'] <- lift $ mapM askInput [KeyLeft, KeyRight, KeyUp, KeyDown, KeyChar 'Z', KeyChar 'X']
        when (t `mod` period == 0) $ void $ move (0, 1)

        omino <- get
        
        drawPicture $ renderPolyomino 6 (below omino) color
        drawPicture $ renderField field
        
        param' <- if isNothing $ putF $ translate (0, 1) omino
            then fmap Right <$> handleLanding (either (const handleLandingParam) id param)
                `runReaderT` (ks, (l',r',u',d',z',x'))
            else fmap Left <$> handleNotLanding (either id (const handleNotLandingParam) param)
                `runReaderT` (ks, (l',r',u',d',z',x'))
        drawPicture $ renderPolyomino 0 omino color        
        case param' of
            Just p -> tick >> run (succ t) p (l',r',u',d',z',x')
            Nothing -> return (putF omino)
    
    handleCommon :: ReaderT Inp (StateT Polyomino (Free Game)) Bool
    handleCommon = do
        ((l,r,u,d,z,x),(l',r',u',d',z',x')) <- ask
        a <- case (not l && l', not r && r') of
            (True, False) -> move (-1, 0)
            (False, True) -> move (1, 0)
            _ -> return False
                
        b <- case (not z && z', not x && x') of
            (True, False) -> rot CCW
            (False, True) -> rot CW
            _ -> return False
        return $ a || b
    
    handleLandingParam = (60, 120)
    handleLanding (0, _) = return Nothing
    handleLanding (play, playBound) = do
        ((l,r,u,d,z,x),(l',r',u',d',z',x')) <- ask
        omino <- get
        drawPicture $ renderPolyomino 7 (below omino) color
        if not u && u' || not d && d' then return Nothing else do
            f <- handleCommon
            if f
                then return $ Just (playBound / 2, playBound - 10)
                else return $ Just (play - 1, playBound)
    
    handleNotLandingParam = 0
    handleNotLanding t = do
        handleCommon
        ((l,r,u,d,z,x),(l',r',u',d',z',x')) <- ask
        when (not u && u') $ modify below
        if d'
            then do
                when (t `mod` 5 == 0) $ void $ move (0, 1)
                return (Just (succ t))
            else do
                return (Just 0)

    putF = putToField color field
    
    move dir = do omino <- translate dir <$> get
                  if isJust $ putF omino
                      then put omino >> return True
                      else return False
    
    rot dir = do
        omino <- get
        case [omino' | center <- centers omino
                          , let omino' = rotate dir center omino
                          , isJust (putF omino')]
                          ++ [omino' | center <- centers omino
                          , let omino' = translate (0,-1) $ rotate dir center omino
                          , isJust (putF omino')] of
            [] -> return False
            xs -> put (maximumBy (compare `on` ev omino) xs) >> return True
        where
            g xs = fromIntegral (sum (map snd xs)) / fromIntegral (length xs)
            ev original omino = sum [fromEnum (g original <= g omino)
                + sum [1 | c <- [c0..c1], isJust $ fromJust (putF omino) ! (c, r)] ^ 2
                | r <- S.toList $ S.fromList $ map snd omino]
            bnd@((c0, _), (c1, _)) = bounds field

    below omino
        | isNothing $ putF omino' = omino
        | otherwise = below omino'
        where omino' = translate (0, 1) omino

eliminate :: (?picBlocks :: M.Map (Color, Int) Picture, ?blockSize :: Double, ?picBlockBackground::Picture)
    => Field -> Free Game (Field, Int)
eliminate field = do
    forM_ [0..5] $ \i -> replicateM_ 2 $ draw i >> tick
    return (foldl deleteLine field rows, length rows)
    where
        rows = completeLines field
        draw n = drawPicture $ flip renderFieldBy field
                $ \(_, r) color -> ?picBlocks M.! (color, if r `elem` rows then n else 0)

gameOver field = do
    let pics = [Translate (Vec2 x y) (?picBlocks M.! (p, 0)) | (ix@(c, r), color) <- assocs field
            , let x = ?blockSize * fromIntegral c, let y = ?blockSize * fromIntegral r
            , p <- maybeToList color]
    objs <- forM pics $ \pic -> do
        dx <- randomness (-1,1)
        return (zero, Vec2 dx (-4), pic)
    run 120 objs
    where
        update (pos, v, pic) = drawPicture (Translate pos pic)
            >> return (pos &+ v, v &+ Vec2 0 0.2, pic)
        run 0 _ = return ()
        run n objs = do
            objs' <- mapM update objs
            tick
            run (n - 1) objs'

gameMain :: (?picBlocks :: M.Map (Color, Int) Picture
    , ?blockSize :: Double
    , ?picCharWidth :: Double
    , ?picChars :: M.Map Char Picture
    , ?picBackground :: Picture
    , ?picBlockBackground :: Picture)
    => Field -> Int -> Int -> (Polyomino, Color) -> (Polyomino, Color) -> Int -> Free Game Int
gameMain field total hiscore (omino, color) next period = do
    r <- embed $ place omino color field period
    case r of
        Nothing -> embed (gameOver field) >> return total
        Just field' -> do
            (field'', n) <- embed $ eliminate field'
            next' <- getPolyomino
            gameMain field'' (total + n ^ 2) hiscore next next' (max 1 $ period - n)
    where
        embed (Pure a) = return a
        embed m = do
            drawPicture $ Translate (Vec2 320 240) ?picBackground
            cont <- hoistFree (transPicture $ Translate (Vec2 24 24)) $ do
                drawPicture $ renderFieldBackground field
                untick m
            drawPicture $ Translate (Vec2 480 133) $ renderString $ show total
            drawPicture $ Translate (Vec2 480 166) $ renderString $ show hiscore
            drawPicture $ Translate (Vec2 500 200) $ uncurry (renderPolyomino 0) next
            Free $ Tick (embed cont)

renderFieldBackground :: (?picBlockBackground :: Picture, ?blockSize :: Double) => Field -> Picture
renderFieldBackground field = Pictures $ [Translate (Vec2 x y) ?picBlockBackground
    | (c, r) <- indices field , let x = ?blockSize * fromIntegral c, let y = ?blockSize * fromIntegral r]

renderField :: (?picBlocks :: M.Map (Color, Int) Picture, ?blockSize :: Double, ?picBlockBackground :: Picture)
    => Field -> Picture
renderField = renderFieldBy $ \_ color -> ?picBlocks M.! (color, 0)

renderFieldBy :: (?blockSize :: Double)
    => (Coord -> Color -> Picture) -> Field -> Picture
renderFieldBy f field = Pictures $ [Translate (Vec2 x y) pic
    | (ix@(c, r), color) <- assocs field
    , let x = ?blockSize * fromIntegral c, let y = ?blockSize * fromIntegral r
    , pic <- maybeToList (f ix <$> color)]

renderPolyomino :: (?picBlocks :: M.Map (Color, Int) Picture, ?blockSize :: Double) => Int -> Polyomino -> Color -> Picture
renderPolyomino i omino color = Pictures [Translate (Vec2 x y) (?picBlocks M.! (color, i))
    | (c, r) <- omino
    , let x = ?blockSize * fromIntegral c
    , let y = ?blockSize * fromIntegral r]

renderString :: (?picCharWidth :: Double, ?picChars :: M.Map Char Picture) => String -> Picture
renderString str = Pictures [Translate (Vec2 (?picCharWidth * i) 0) $ ?picChars M.! ch
    | (i, ch) <- zip [0..] str]

main :: IO ()
main = void $ runGame True "Monaris" 60 $ do
    let colors = enumFrom Red

    imgChars <- loadImgFromFile "images/numbers.png"
    picChars' <- liftM M.fromAscList $ forM [0..9]
        $ \n -> (,) (intToDigit n) <$> loadImage (cropImg imgChars (24, 32) (n * 24, 0))
    let ?picCharWidth = 18
        ?picChars = picChars'
    
    imgBlocks <- loadImgFromFile "images/Block.png"
    picBlocks' <- liftM M.fromAscList $ forM ((,) <$> zip [0..] colors <*> [0..7])
        $ \((i, color), j) -> (,) (color, j) <$> loadImage (cropImg imgBlocks (48, 48) (i * 48, j * 48))

    let ?blockSize = 24
        ?picBlocks = picBlocks'

    imgBackground <- loadImgFromFile "images/background.png" >>= loadImage
    imgBlockBackground <- loadImgFromFile "images/block-background.png" >>= loadImage
    
    let ?picBackground = imgBackground
        ?picBlockBackground = imgBlockBackground
    
    imgTitle <- loadImgFromFile "images/title.png" >>= loadImage
    
    let initialField = listArray ((0,0), (9,18)) (repeat Nothing)
    let loop hiscore = do
            let w = do
                z <- askInput (KeyChar 'Z')
                drawPicture $ Translate (Vec2 320 240) imgTitle
                drawPicture $ Translate (Vec2 490 182) $ renderString (show hiscore)
                tick
                when (not z) w
            w
            score <- join $ gameMain initialField 0 hiscore <$> getPolyomino <*> getPolyomino <*> pure 60
            loop (max score hiscore)
    loop 0
