{-# LANGUAGE MonadComprehensions, TupleSections, ImplicitParams, FlexibleContexts, TemplateHaskell #-}
import Control.Lens (view)
import Control.Monad
import Control.Monad.State
import Data.List
import Data.Function
import Data.Array
import Data.Char
import Data.Maybe
import qualified Data.Map as M
import System.Directory
import FreeGame
import Paths_Monaris

loadBitmapsWith [e|getDataFileName|] "images"

picBlocks :: Picture2D m => M.Map (Int, Int) (m ())
picBlocks = M.fromAscList [((i, j), bitmap $ cropBitmap _blocks_png (48, 48) (i * 48, j * 48))
    | i <- [0..6], j <- [0..7]]

picChars :: Picture2D m => M.Map Char (m ())
picChars = M.fromAscList [(intToDigit n, bitmap $ cropBitmap _numbers_png (24, 32) (n * 24, 0))
    | n <- [0..9]]

blockSize, picCharWidth :: Double
blockSize = 24
picCharWidth = 24

type Field = Array Coord (Maybe BlockColor)
type BlockColor = Int
type Coord = V2 Int
type Polyomino = [Coord]

polyominos :: [(Polyomino, BlockColor)]
polyominos = [([V2 0 0,V2 0 1,V2 0 2,V2 0 3], 3)
             ,([V2 0 0,V2 0 1,V2 1 0,V2 1 1], 1)
             ,([V2 0 0,V2 0 1,V2 0 2,V2 1 2], 6)
             ,([V2 0 0,V2 0 1,V2 0 2,V2 (-1) 2], 4)
             ,([V2 0 0,V2 0 1,V2 1 1,V2 1 2], 2)
             ,([V2 0 0,V2 0 1,V2 (-1) 1,V2 (-1) 2], 0)
             ,([V2 0 0,V2 (-1) 0,V2 1 0,V2 0 1], 5)]

translateP :: Coord -> Polyomino -> Polyomino
translateP = map . (+)

spin :: (Coord -> Coord) -> Coord -> Polyomino -> Polyomino
spin t center = map $ fmap (`div`2) . (^+^center) . t . (^-^center) . fmap (2*)

centers :: Polyomino -> [Coord]
centers cs = cs' ++ [i | i@(V2 c r) <- map (V2 1 1+) cs'
    , let c0 = minimum (map (view _x) cs'), let c1 = maximum (map (view _x) cs')
    , let r0 = minimum (map (view _y) cs'), let r1 = maximum (map (view _y) cs')
    , c0 < c && c < c1, r0 < r && r < r1] where cs' = map (fmap (2*)) cs

completeLines :: Field -> [Int]
completeLines field = [r | r <- [r0..r1], all isJust [field ! V2 c r | c <- [c0..c1]]] where
    (V2 c0 r0, V2 c1 r1) = bounds field

deleteLine :: Field -> Int -> Field
deleteLine field n = array bnd [ a' | a@(ix@(V2 c r), _) <- assocs field
    , let a' | r == r0 = (ix, Nothing)
             | r <= n = (ix, field ! V2 c (r - 1))
             | otherwise = a] where
         bnd@(V2 _ r0, _) = bounds field

putToField :: BlockColor -> Field -> Polyomino -> Maybe Field
putToField col field omino = [field // map (,Just col) omino
    | all ((&&) <$> inRange (bounds field) <*> fmap isNothing (field !)) omino]

getPolyomino :: Game (Polyomino, BlockColor)
getPolyomino = (polyominos!!) <$> randomness (0, length polyominos - 1)

spinStrategy :: Polyomino -> Field -> [Polyomino] -> Polyomino
spinStrategy original field = maximumBy (compare `on` ev) where
    g :: Polyomino -> Double
    g xs = fromIntegral (sum (map (view _y) xs)) / fromIntegral (length xs)
    ev :: Polyomino -> Int
    ev x = sum [fromEnum (g original <= g x)
               + sum [1 | c <- neighbors
                  , not (inRange (bounds field) c) || isJust (field ! c)] ^ (2 :: Int)
            | _ <- nub $ map (view _y) x]
        where neighbors = nub $ (+) <$> x <*> [V2 0 1, V2 0 (-1), V2 1 0, V2 (-1) 0]

place :: Polyomino -> BlockColor -> Field -> Int -> Game (Maybe Field)
place polyomino col field period = run 1 (Left 0)
    `evalStateT` translateP (V2 5 initialY) polyomino
    where
    initialY = -1 - maximum (map (view _y) polyomino)
    putF = putToField col field

    run :: Int -> Either Int (Double, Double) -> StateT Polyomino Game (Maybe Field)
    run t param = do
        when (t `mod` period == 0) $ void $ move (V2 0 1)

        omino <- get

        param' <- if isNothing $ putF $ translateP (V2 0 1) omino
                then fmap Right <$> handleLanding (either (const (60, 120)) id param)
                else fmap Left <$> handleNotLanding (either id (const 0) param)
        renderField field
        renderPolyomino 0 omino col
        case param' of
            Just p -> delay $ run (succ t) p
            Nothing -> return (putF omino)

    handleCommon = do
        l <- keyDown KeyLeft
        r <- keyDown KeyRight
        a <- case (l, r) of
            (True, False) -> move (V2 (-1) 0)
            (False, True) -> move (V2 1 0)
            _ -> return False
        z <- keyDown KeyZ
        x <- keyDown KeyX
        b <- case (z, x) of
            (True, False) -> sp $ \(V2 s t) -> V2 (-t) s
            (False, True) -> sp $ \(V2 s t) -> V2 t (-s)
            _ -> return False
        return $ a || b

    handleLanding (0, _) = return Nothing
    handleLanding (play, playBound) = do
        omino <- get
        renderPolyomino 7 omino col
        u <- keyDown KeyUp
        d <- keyDown KeyDown
        if u || d then return Nothing else do
            f <- handleCommon
            return $ Just $ if f then (playBound / 2, playBound - 10) else (play - 1, playBound)

    handleNotLanding t = do
        _ <- handleCommon
        omino <- get
        renderPolyomino 6 (destination omino) col
        whenM (keyDown KeyUp) $ modify destination
        ifThenElseM (keyPress KeyDown)
            (do
                when (t `mod` 5 == 0) $ void $ move (V2 0 1)
                return (Just (succ t)))
            (return (Just 0))

    move dir = do omino <- translateP dir <$> get
                  if isJust $ putF omino
                      then put omino >> return True
                      else return False

    sp dir = do omino <- get
                case filter (isJust . putF) $ map (flip (spin dir) omino) $ centers omino of
                     [] -> return False
                     xs -> put (spinStrategy omino field xs) >> return True

    destination omino
        | isNothing $ putF omino' = omino
        | otherwise = destination omino'
        where omino' = translateP (V2 0 1) omino

eliminate :: Field -> [Int] -> Game Field
eliminate field rows = do
    draw' 0
    delay $ draw' 0
    forM_ [1..5] $ replicateM_ 2 . delay . draw'
    return (foldl' deleteLine field rows)
    where
        draw' n = flip renderFieldBy field
            $ \(V2 _ r) col -> picBlocks M.! (col, if r `elem` rows then n else 0)

gameMain :: Int -> Field -> Int -> Double -> (Polyomino, BlockColor) -> (Polyomino, BlockColor) -> Game Int
gameMain highScore field total count (omino, col) next = if isGameover
    then total <$ embed (gameOver field)
    else do
        r <- embed $ place omino col field $ floor $ 50 * 2 ** (-count/30)
        case r of
            Nothing -> total <$ embed (gameOver field)
            Just field' -> do
                let rows = completeLines field'
                let n = length rows
                field'' <- if n == 0
                    then return field'
                    else embed $ eliminate field' rows
                next' <- getPolyomino
                gameMain highScore field'' (total + n * n) (count + fromIntegral n) next next'
    where
        isGameover = or [isJust $ field ! V2 c r | V2 c r <- range (V2 c0 r0, V2 c1 (-1))]
        (V2 c0 r0, V2 c1 _) = bounds field
        embed m = delay $ do
            translate (V2 320 240) $ bitmap _background_png
            cont <- translate (V2 24 24) $ do
                renderFieldBackground field
                liftFrame $ untick m
            translate (V2 480 133) $ renderString $ show total
            translate (V2 480 166) $ renderString $ show highScore
            translate (V2 500 220) $ uncurry (renderPolyomino 0) next
            either embed return cont

gameTitle :: Int -> Game ()
gameTitle highScore = do
    translate (V2 320 240) $ bitmap _title_png
    translate (V2 490 182) $ renderString $ show highScore
    unlessM (keyPress KeyZ) $ delay $ gameTitle highScore

blockPos :: Int -> Int -> V2 Double
blockPos c r = blockSize *^ fmap fromIntegral (V2 c r)

gameOver :: Field -> Game ()
gameOver field = do
    let pics = [translate (blockPos c r) (picBlocks M.! (p, 0))
            | (V2 c r, col) <- assocs field, p <- maybeToList col]
    objs <- forM pics $ \pic -> do
        dx <- randomness (-1,1)
        return (zero, V2 dx (-3), pic)
    objs' <- mapM update objs
    void $ foldM run objs' [1 :: Int ..120]
    where
        update (pos, v, pic) = (pos ^+^ v, v ^+^ V2 0 0.2, pic) <$ translate pos pic
        run objs = const $ delay $ mapM update objs

renderFieldBackground :: (Monad m, Picture2D m) => Field -> m ()
renderFieldBackground field = sequence_
    [blockPos c r `translate` bitmap _block_background_png
    | V2 c r <- indices field, r >= 0]

renderField :: (Monad m, Picture2D m) => Field -> m ()
renderField = renderFieldBy $ \_ col -> picBlocks M.! (col, 0)

renderFieldBy :: (Monad m, Picture2D m) => (Coord -> BlockColor -> m ()) -> Field -> m ()
renderFieldBy f field = sequence_ [blockPos c r `translate` pic
    | (ix@(V2 c r), col) <- assocs field, r >= 0, pic <- maybeToList $ f ix <$> col]

renderPolyomino :: (Monad m, Picture2D m) => Int -> Polyomino -> BlockColor -> m ()
renderPolyomino i omino col = sequence_ [blockPos c r `translate` picBlocks M.! (col, i)
    | V2 c r <- omino, r >= 0]

renderString :: (Monad m, Picture2D m) => String -> m ()
renderString str = sequence_ [V2 (picCharWidth * i) 0 `translate` picChars M.! ch | (i, ch) <- zip [0..] str]

main :: IO ()
main = void $ runGameDefault $ do
    let initialField = listArray (V2 0 (-4), V2 9 18) (repeat Nothing)
    highscorePath <- liftIO $ (++"/.monaris_highscore") <$> getHomeDirectory
    setTitle "Monaris"
    let loop h = do
            gameTitle h
            score <- join $ gameMain h initialField 0 0 <$> getPolyomino <*> getPolyomino
            when (h < score) $ liftIO $ writeFile highscorePath (show score)

            loop (max score h)
    f <- liftIO $ doesFileExist highscorePath
    (if f then liftIO $ read <$> readFile highscorePath else return 0) >>= loop
