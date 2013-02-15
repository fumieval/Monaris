{-# LANGUAGE MonadComprehensions, TupleSections, ImplicitParams, FlexibleContexts #-}
import Control.Applicative
import Control.Monad
import Control.Monad.Free
import Data.List
import Data.Function
import Data.Array
import Data.Maybe
import Data.Vect
import qualified Data.Map as M
import System.Directory
import Graphics.FreeGame
import Paths_Monaris

type Field = Array Coord (Maybe Color)
type Color = Int
type Coord = (Int, Int)
type Polyomino = [Coord]

pair f (x, y) = (f x, f y)
pair2 f (a, b) (c, d) = (f a c, f b d)

polyominos = [([(0,0),(0,1),(0,2),(0,3)], 3)
             ,([(0,0),(0,1),(1,0),(1,1)], 1)
             ,([(0,0),(0,1),(0,2),(1,2)], 6)
             ,([(0,0),(0,1),(0,2),(-1,2)], 4)
             ,([(0,0),(0,1),(1,1),(1,2)], 2)
             ,([(0,0),(0,1),(-1,1),(-1,2)], 0)
             ,([(0,0),(-1,0),(1,0),(0,1)], 5)]

translate :: Coord -> Polyomino -> Polyomino
translate = map . pair2 (+)

spin :: (Coord -> Coord) -> Coord -> Polyomino -> Polyomino
spin t center = map $ pair (`div`2) . pair2 (+) center . t . pair2 subtract center . pair (2*) where 

centers :: Polyomino -> [Coord]
centers cs = cs' ++ [i | i@(c, r) <- map (pair2 (+) (1,1)) cs'
    , let c0 = minimum (map fst cs'), let c1 = maximum (map fst cs')
    , let r0 = minimum (map snd cs'), let r1 = maximum (map snd cs')
    , c0 < c && c < c1, r0 < r && r < r1] where cs' = map (pair (2*)) cs

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
    | all ((&&) <$> inRange (bounds field) <*> fmap isNothing (field !)) omino]

spinStrategy :: Polyomino -> Field -> [Polyomino] -> Polyomino
spinStrategy original field = maximumBy (compare `on` ev) where
    g xs = fromIntegral (sum (map snd xs)) / fromIntegral (length xs)
    ev x = sum [fromEnum (g original <= g x)
               + sum [1 | c <- neighbors, not (inRange (bounds field) c) || isJust (field ! c)] ^ 2
            | r <- nub $ map snd x] 
        where neighbors = nub $ pair2 (+) <$> x <*> [(0, 1), (0, -1), (1, 0), (1, 1)]

getPolyomino :: Game (Polyomino, Color)
getPolyomino = (polyominos!!) <$> randomness (0, length polyominos - 1)

place :: (?env :: Environment) => Polyomino -> Color -> Field -> Int -> Game (Maybe Field)
place polyomino color field period
    | or [isJust $ field ! (c, r) | (c, r) <- range ((c0, r0), (c1, -1))] = return Nothing
    | otherwise = do 
        let            
            mover = proc omino -> do
                r <- keyDown KeyLeft *** keyDown KeyRight
                let omino' = flip translate omino $ case r of
                    (True, False) -> (-1, 0)
                    (False, True) -> (1, 0)
                    _ -> (0, 0)
                returnA -< case putF omino' of
                    Nothing -> omino
                    Just _ -> omino'

            spinner = proc omino -> do
                r <- keyDown (KeyChar 'Z') &&& keyDown (KeyChar 'X')
                returnA -< case filter (isJust . putF) . ($centers omino) $ case r of
                        (True, False) -> map (spin omino \(x, y) -> (-y, x))
                        (False, True) -> map (spin omino \(x, y) -> (y, -x))
                        _ -> const []
                        of
                    [] -> omino
                    xs -> spinStrategy omino field xs

            landing = wrapStateful_ $ do
                drawPicture $ renderPolyomino 7 omino color

            faller = wrapStateful 0 $ \omino -> do
                t <- get
                put (t + 1)
                drawPicture $ renderPolyomino 6 (destination omino) color
                if t `mod` 5 == 0
                    then translate (0, 1) omino
                    else omino
            
            initial = translate (5, -1 - maximum (map snd polyomino)) polyomino

        run (spinner >>> mover) (faller >>> midair) landing polyomino

    where
        run common midair landing omino =  do
            (omino, common') <- runVein common ()
            drawPicture $ renderPolyomino 0 omino color
            case putF $ translate (0, 1) omino of
                Just _ -> do
                    (omino', midair') <- runVein midair omino
                    tick
                    run common midair landing omino'
                Nothing -> do
                    (o, landing') <- execVein landing ()
                    tick
                    i run common' midair landing'

    ((c0, r0), (c1, r1)) = bounds field
    putF = putToField color field
    destination omino
        | isNothing $ putF omino' = omino
        | otherwise = destination omino'
        where omino' = translate (0, 1) omino

eliminate :: (?env :: Environment) => Field -> Game (Field, Int)
eliminate field = (foldl deleteLine field rows, length rows)
    <$ (unless (null rows) $ forM_ [0..5] $ \i -> replicateM_ 2 $ draw i >> tick)
    where
        rows = completeLines field
        draw n = drawPicture $ flip renderFieldBy field
                $ \(_, r) color -> picBlocks ?env M.! (color, if r `elem` rows then n else 0)

gameMain :: (?env :: Environment, ?highScore :: Int) => Field -> Int -> Float -> (Polyomino, Color) -> (Polyomino, Color) -> Game Int
gameMain field total line (omino, color) next = do
    r <- embed $ place omino color field (floor $ 60 * 2**(-line/40))
    case r of
        Nothing -> total <$ embed (gameOver field)
        Just field' -> do
            (field'', n) <- embed $ eliminate field'
            next' <- getPolyomino
            gameMain field'' (total + n ^ 2) (line + fromIntegral n) next next'
    where
        embed (Pure a) = return a
        embed m = do
            let drawTo x y = drawPicture . Translate (Vec2 x y)
            drawTo 320 240 $ picBackground ?env
            cont <- hoistFree (transPicture $ Translate (Vec2 24 24)) $ do
                drawPicture $ renderFieldBackground field
                untickGame m
            drawTo 480 133 $ renderString $ show total
            drawTo 480 166 $ renderString $ show ?highScore
            drawTo 500 220 $ uncurry (renderPolyomino 0) next
            tick
            embed cont

gameTitle :: (?env :: Environment, ?highScore :: Int) => Game ()
gameTitle = do
    z <- askInput (KeyChar 'Z')
    drawPicture $ Translate (Vec2 320 240) (picTitle ?env)
    drawPicture $ Translate (Vec2 490 182) $ renderString $ show ?highScore
    tick
    when (not z) gameTitle

blockPos :: (?env :: Environment) => Int -> Int -> Vec2
blockPos c r = blockSize ?env *& Vec2 (fromIntegral c) (fromIntegral r)

gameOver :: (?env :: Environment) => Field -> Game ()
gameOver field = do
    let pics = [Translate (blockPos c r) (picBlocks ?env M.! (p, 0))
            | ((c, r), color) <- assocs field, p <- maybeToList color]
    objs <- forM pics $ \pic -> do
        dx <- randomness (-1,1)
        return (zero, Vec2 dx (-3), pic)
    void $ foldM run objs [1..120]
    where
        update (pos, v, pic) = (pos &+ v, v &+ Vec2 0 0.2, pic) <$ drawPicture (Translate pos pic)
        run objs = const $ mapM update objs <* tick

renderFieldBackground :: (?env :: Environment) => Field -> Picture
renderFieldBackground field = Pictures [blockPos c r `Translate` picBlockBackground ?env | (c, r) <- indices field, r >= 0]

renderField :: (?env :: Environment) => Field -> Picture
renderField = renderFieldBy $ \_ color -> picBlocks ?env M.! (color, 0)

renderFieldBy :: (?env :: Environment) => (Coord -> Color -> Picture) -> Field -> Picture
renderFieldBy f field = Pictures [blockPos c r `Translate` pic
    | (ix@(c, r), color) <- assocs field, r >= 0, pic <- maybeToList $ f ix <$> color]

renderPolyomino :: (?env :: Environment) => Int -> Polyomino -> Color -> Picture
renderPolyomino i omino color = Pictures [blockPos c r `Translate` (picBlocks ?env M.! (color, i))
    | (c, r) <- omino, r >= 0]

renderString :: (?env :: Environment) => String -> Picture
renderString str = Pictures [Vec2 (picCharWidth ?env * i) 0 `Translate` (picChars ?env M.! ch) | (i, ch) <- zip [0..] str]

data Environment = Environment
    { picBlocks :: M.Map (Color, Int) Picture
    , picChars :: M.Map Char Picture
    , picBlockBackground :: Picture
    , picBackground :: Picture
    , picTitle :: Picture
    , blockSize :: Float
    , picCharWidth :: Float
    }

main :: IO ()
main = void $ runGame (defaultGameParam {windowTitle="Monaris"}) $ do

    let initialField = listArray ((0,-4), (9,18)) (repeat Nothing)
        load path = embedIO $ getDataFileName path >>= loadBitmapFromFile

    imgChars            <- load "images/numbers.png"
    imgBlocks           <- load "images/Block.png"
    imgBackground       <- load "images/background.png"
    imgBlockBackground  <- load "images/block-background.png"
    imgTitle            <- load "images/title.png"

    highscorePath <- embedIO $ (++"/.monaris_highscore") <$> getHomeDirectory

    let ?env = Environment
                (M.fromAscList [((color, j), BitmapPicture $ cropBitmap imgBlocks (48, 48) (i * 48, j * 48))
                    | (i, color) <- zip [0..] (enumFrom Red), j <- [0..7]])
                (M.fromAscList [(intToDigit n, BitmapPicture $ cropBitmap imgChars (24, 32) (n * 24, 0))
                    | n <- [0..9]])
                (BitmapPicture imgBlockBackground)
                (BitmapPicture imgBackground)
                (BitmapPicture imgTitle)
                48
                24

    let loop h = do
            let ?highScore = h
            gameTitle
            
            score <- join $ gameMain initialField 0 0 <$> getPolyomino <*> getPolyomino
            when (?highScore < score) $ embedIO $ writeFile highscorePath (show score)
            
            loop (max score h)

    f <- embedIO $ doesFileExist highscorePath
    (if f then embedIO $ read <$> readFile highscorePath else return 0) >>= loop
