module Main where

import Control.Monad
import Data.Maybe
import qualified Data.Map as M
import Data.Traversable (Traversable(..))
import System.Environment

import Happy
import HappyData

main :: IO ()
main = do
    [s] <- getArgs
    
    let ParseOK root_id forest = happyParse $ map return s -- GLR parser expects a list of possible tokens at each position
    
    -- Show the parse forest
    mapM_ print $ M.toList forest
    
    -- Show all possible parses. This is not so cool for our grammar because there are infinitely many derivations,
    -- so in fact this just stack overflows trying to build an infinitely large one:
    --mapM_ print $ rebuildAST (fromJust . flip M.lookup forest) root_id


-- Fixed points of functors, for rebuildAST
newtype Fix f = Fix { unFix :: f (Fix f) }

instance Show1 f => Show (Fix f) where
    show = show1 . unFix


-- Turn the graph output by the parser into a simple list of normal Haskell data types
rebuildAST :: (ForestId -> [Branch]) -> ForestId -> [Fix AST]
rebuildAST find = go
  where go = concatMap (map Fix . traverse go . unpack . b_sem) . find
