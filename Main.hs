module Database where

import Data.Set (Set)
import Data.List (groupBy)
import Data.Function (on)
import qualified Data.Set as Set

type FD a = (Set a, Set a) 

attrClosure :: Ord a => Set a -> Set (FD a) -> Set a
attrClosure lhs fs
  | new == lhs = lhs
  | otherwise = attrClosure new fs
  where new = Set.union lhs $ Set.foldl Set.union Set.empty
                $ Set.map snd $ Set.filter (flip Set.isSubsetOf lhs . fst) fs

unionRule :: Ord a => Set (FD a) -> Set (FD a)
unionRule = Set.fromList . map merge . groupByFst
  where merge fs = (fst . head $ fs, Set.unions . snd . unzip $ fs)
        groupByFst = groupBy (on (==) fst) . Set.toAscList

isLhsExt :: Ord a => Set (FD a) -> FD a -> a -> Bool
isLhsExt fs f@(alpha, beta) a = 
  Set.isSubsetOf beta $ attrClosure (Set.delete a alpha) fs

isRhsExt :: Ord a => Set (FD a) -> FD a -> a -> Bool
isRhsExt fs f@(alpha, beta) a = 
  Set.member a $ attrClosure alpha
    $ Set.insert (alpha, Set.delete a beta) (Set.delete f fs)

hasLExt :: Ord a => Set (FD a) -> FD a -> Bool
hasLExt fs f@(alpha, beta) = 
  Set.foldl (\acc a -> acc || (isLhsExt fs f a)) False alpha

hasRExt :: Ord a => Set (FD a) -> FD a -> Bool
hasRExt fs f@(alpha, beta) = 
  Set.foldl (\acc a -> acc || (isRhsExt fs f a)) False beta

hasExt :: Ord a => Set (FD a) -> FD a -> Bool
hasExt fs f = hasLExt fs f || hasRExt fs f


canonCover :: Ord a => Set (FD a) -> Set (FD a)
canonCover fs
  | null exts = gs
  | otherwise = canonCover $Set.insert 
                  (if null lExts
                   then (alpha, Set.delete (Set.findMin rExts) beta)
                   else (Set.delete (Set.findMin lExts) alpha, beta))
                $ Set.delete f gs
  where gs = unionRule fs
        exts = Set.filter (hasExt gs) gs
        f@(alpha, beta) = Set.findMin exts
        lExts = Set.filter (isLhsExt gs f) alpha
        rExts = Set.filter (isRhsExt gs f) beta
