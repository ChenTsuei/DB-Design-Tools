module Database where

import Data.Set (Set)
import Data.List (groupBy)
import Data.Function (on)
import qualified Data.Set as Set

type FD a = (Set a, Set a) 

-- Calculate the restriction of F in alpha
restrict :: Ord a => Set a -> Set (FD a) -> Set (FD a)
restrict alpha = Set.filter $ flip Set.isSubsetOf alpha . fst

-- Calculate (alpha)+ under fs
attrClosure :: Ord a => Set a -> Set (FD a) -> Set a
attrClosure alpha fs
  | alpha == new = alpha
  | otherwise = attrClosure new fs
  where new = Set.union alpha $ Set.unions . Set.toAscList
                $ Set.map snd . restrict alpha $ fs

-- Merge all the alpha -> beta1, alpha -> beta2 to alpha -> beta1 beta2
unionRule :: Ord a => Set (FD a) -> Set (FD a)
unionRule = Set.fromList . map merge . groupByFst
  where merge fs = (fst . head $ fs, Set.unions . snd . unzip $ fs)
        groupByFst = groupBy (on (==) fst) . Set.toAscList

-- Check whether a attribute is extraneous in the left hand side
isLhsExt :: Ord a => Set (FD a) -> FD a -> a -> Bool
isLhsExt fs f@(alpha, beta) a = 
  Set.isSubsetOf beta $ attrClosure (Set.delete a alpha) fs

-- Check whether a attribute is extraneous in the right hand side
isRhsExt :: Ord a => Set (FD a) -> FD a -> a -> Bool
isRhsExt fs f@(alpha, beta) a = 
  Set.member a $ attrClosure alpha
    $ Set.insert (alpha, Set.delete a beta) $ Set.delete f fs

-- Check whether alpha has an extraneous attribute
hasLExt :: Ord a => Set (FD a) -> FD a -> Bool
hasLExt fs f@(alpha, beta) = 
  Set.foldl (\acc a -> acc || (isLhsExt fs f a)) False alpha

-- Check whether beta has an extraneous attribute
hasRExt :: Ord a => Set (FD a) -> FD a -> Bool
hasRExt fs f@(alpha, beta) = 
  Set.foldl (\acc a -> acc || (isRhsExt fs f a)) False beta

-- Check whether alpha -> alpha has an extraneous attribute
hasExt :: Ord a => Set (FD a) -> FD a -> Bool
hasExt fs f = hasLExt fs f || hasRExt fs f

-- Calcute the canonical cover
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

-- Check whether a decomposion of a Function Dependency set is dependency preserving
dependPreserve :: Ord a => Set (FD a) -> Set (Set a) -> Bool
dependPreserve fs rs = Set.foldl (\acc (alpha, beta) -> acc 
                                    && (Set.isSubsetOf beta $ loop alpha)) True fs
  where loop alpha = if alpha == new then alpha else loop new
          where new = Set.foldl (\acc r -> Set.union acc 
                                   $ Set.intersection r $ attrClosure (Set.intersection acc r) fs) alpha rs
