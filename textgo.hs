module TextGo where

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Foldable as F
import Data.Maybe
import Data.Char
import Control.Monad
import System.Console.Haskeline

x_FILL = 2 -- assumes board smaller than 99x99 ...

union_map f set = S.unions $ map f $ S.toList set
union_filter p set = S.unions $ filter p $ S.toList set

strip = rdrop . rdrop
   where rdrop = reverse . dropWhile isSpace
padding size str = replicate (size - length str) ' '
lpad size str = padding size str ++ str
rpad size str = str ++ padding size str

alpha_labels = map (: []) alpha ++ [ch0 : [ch1] | ch0 <- alpha, ch1 <- alpha]
  where alpha = 'I' `L.delete` ['A'..'Z']

type Coord = (Int, Int)
c_from_label str = do
  let (lx, ly) = break isDigit str
  cx <- L.elemIndex lx alpha_labels
  return (cx, read ly - 1 :: Int)
c_map size f = [f (cx, cy) | cy <- indices, cx <- indices]
  where indices = [0 .. size - 1]
c_adj (cx, cy) = [(cx - 1, cy), (cx + 1, cy), (cx, cy - 1), (cx, cy + 1)]

data Stone = Empty | Black | White deriving (Show, Eq)
s_char Empty = '.'
s_char Black = 'X'
s_char White = 'O'
s_invert Black = White
s_invert White = Black

type BoardState = M.Map Coord Stone
data Board = Board {b_size :: Int, b_state :: BoardState} deriving (Show, Eq)
b_empty size = Board size $ M.fromList empty_assocs
  where empty_assocs = c_map size $ \coord -> (coord, Empty)
in_bounds size (cx, cy) = and [cx >= 0, cx < size, cy >= 0, cy < size]
within_bounds board coord result =
  if not $ in_bounds (b_size board) coord then Nothing else result
b_get board coord = within_bounds board coord $ M.lookup coord $ b_state board
b_put board coord stone = within_bounds board coord $ Just board'
  where board' = board {b_state=M.insert coord stone $ b_state board}
b_puts board coords stone = fromJust $ F.foldl' try_put (Just board) coords
  where try_put mboard coord = do
          board <- mboard
          b_put board coord stone `mplus` mboard
b_render board = L.intercalate "\n" rows ++ x_labels
  where size = b_size board
        rows = rows'
          where next_rows (rows, rest, idx) = (row' : rows, rest', idx + 1)
                  where (row, rest') = splitAt size rest
                        row' = lpad x_FILL (show idx) ++ " " ++ map s_char row
                stones = catMaybes $ c_map size $ b_get board
                (rows', _, _) = iterate next_rows ([], stones, 1) !! size
        x_labels = indent ++ L.intercalate indent labels
          where indent = "\n " ++ replicate x_FILL ' '
                labels = L.transpose $ map (rpad label_fill) pre_labels
                pre_labels = take size alpha_labels
                label_fill = foldr (max . length) 0 pre_labels

adj_match board stone coord = S.fromList $ mapMaybe is_match $ c_adj coord
  where is_match crd = b_get board crd >>= guard . (stone ==) >> return crd
coord_libs board = adj_match board Empty
get_contig board coord stone = iter (S.singleton coord) S.empty
  where iter pending finished =
          if S.null pending then finished' else iter pending' finished'
          where next = union_map (adj_match board stone) pending
                finished' = pending `S.union` finished
                pending' = next `S.difference` finished'
get_group board coord = liftM (get_contig board coord) $ b_get board coord
group_libs board = union_map $ coord_libs board
is_dead board group = S.size (group_libs board group) == 0

capture_around board coord stone = (board'', caps)
  where opponent_groups = S.fromList $ mapMaybe (get_group board) $
          S.toList $ adj_match board (s_invert stone) coord
        captures = union_filter (is_dead board) opponent_groups
        ncaps = S.size captures
        board' = b_puts board captures Empty
        this_group = fromJust $ get_group board' coord
        suicides = if is_dead board' this_group then this_group else S.empty
        nsuicides = S.size suicides
        board'' = b_puts board' suicides Empty
        caps = if stone == Black then Captures nsuicides ncaps
               else Captures ncaps nsuicides

try_move prev_board board stone coord = do
  should_be_empty <- b_get board coord
  guard $ should_be_empty == Empty
  board' <- b_put board coord stone
  let (board'', caps) = capture_around board' coord stone
  guard $ board'' /= prev_board -- naive check for ko
  return (board'', caps)

data Captures = Captures {cp_bcaps, cp_wcaps :: Int} deriving Show
cp_add caps0 caps1 = Captures {cp_bcaps=cp_bcaps caps0 + cp_bcaps caps1,
                               cp_wcaps=cp_wcaps caps0 + cp_wcaps caps1}

data GameState = GameState {g_board :: Board, g_turn :: Stone,
                            g_movenum :: Int, g_caps :: Captures,
                            g_hist :: [GameState]} deriving Show
g_empty size = gs
  where board = b_empty size
        gs = GameState board Black 0 (Captures 0 0) (repeat gs)
g_pboard gs = g_board $ head $ g_hist gs
g_render gs =
  L.intercalate "\n"
    ["Move " ++ show (g_movenum gs), caps Black cp_bcaps, caps White cp_wcaps,
     show (g_turn gs) ++ " to play", b_render $ g_board gs]
  where caps stone proj = show stone ++ " stones captured: " ++
          show (proj $ g_caps gs)
g_advance gs (board, caps) =
  gs {g_board=board, g_turn=s_invert (g_turn gs), g_movenum=1 + g_movenum gs,
      g_caps=cp_add caps (g_caps gs), g_hist=gs : g_hist gs}
g_play gs coord =
  liftM (g_advance gs) $ try_move (g_pboard gs) (g_board gs) (g_turn gs) coord
g_pass gs = g_advance gs (g_board gs, g_caps gs)

get_move = runInputT defaultSettings (getInputLine "Choose a move: ") >>=
  maybe get_move return
i_play gs = do
  putStrLn $ g_render gs
  move <- get_move
  let next = case map toUpper $ strip move of
               "UNDO" -> return $ g_hist gs !! 1
               "PASS" -> return $ g_pass gs
               move' -> c_from_label move' >>= g_play gs
  maybe (putStrLn "You can't play there!" >> i_play gs) i_play next

test_gs = do
  let gs0 = g_empty 9
  gs1 <- g_plays gs0 [(3, 3), (2, 3), (4, 4), (3, 4), (4, 2), (3, 2), (5, 3)]
  gs2 <- g_plays gs1 [(4, 3)]
  gs3 <- g_plays gs2 [(3, 3)] -- comment this line to see ko setup in test_ko
  return gs2
  where g_plays = foldM g_play
test_render board = putStr (b_render board) >> putStrLn ""
test_board0 = b_empty 30
test_board1 = liftM fst $ try_move test_board0 test_board0 Black (10, 10)
test0 = test_render test_board0
test1 = test_render $ fromJust test_board1
test_ko = putStrLn $ g_render $ fromJust test_gs

play19 = i_play $ g_empty 19
