---- CSci 119, Fall 2019, Lab 2 ----
-- Richard Mojarro
-- CSCI 119
-- Sept 8, 2019

-- As in Lab 1, we will be working with the finite universe U = [1..8]
import Data.List
u = [1..8]


----- PART 1:  Relations on u -----

-- A relation, R, on U is a list of the ordered pairs of elements of U:
type Reln = [(Int,Int)]
              
-- For example, here are the < and <= relations
less_reln :: Reln
less_reln = [(i,j) | j <- [1..8], i <- [1..j-1]]

leq_reln :: Reln
leq_reln  = [(i,j) | j <- [1..8], i <- [1..j]]
            
-- and here is the relation of equivalence mod 3:
eqmod3_reln :: Reln
eqmod3_reln = [(i,j) | i <- [1..8], j <- [1..8], (j - i) `mod` 3 == 0]


-- Write a function refl that tests whether a relation is reflexive:
-- R is reflexive if: forall a, (a,a) in R
-- Example: [(1,1),(2,2),(3,3),(4,4),(5,5),(6,6),(7,7),(8,8)] is the
-- smallest reflexive relation over u. Anything that does not contain
-- these 8 elements is not reflexive
refl :: Reln -> Bool
refl rs = and [ (n,n) `elem` rs | n <- u]

-- Write a function symm that tests whether a relation is symmetric:
-- R is symmetric if: forall a b, (a,b) in R -> (b,a) in R
-- Example: [(1,1), (1,2), (2,1)] is symmetric but [(1,1), (1,2)] is not.
symm :: Reln -> Bool
symm rs =  and [ (n,y) `elem` rs | (y,n) <- rs]

-- Write a function trans that tests whether a relation is transitive:
-- R is transistive if: forall a b c, (a,b) in R /\ (b,c) in R -> (a,c) in R
-- Example: [(1,2),(2,3),(1,3),(4,4)] is transitive but [(2,3),(3,2)] is not
trans :: Reln -> Bool
trans rs = and [ (n,r) `elem` rs | (n,y) <- rs, (z,r) <- rs, y == z]


-- Use the functions above to check the less, leq, and eqmod3 relations for
-- relexivity, symmetry, and transitivity


-- For each of the 8 possible combinations of yes/no on reflexivity,
-- symmetry, and transitivity, find a MINIMAL relation on u that has exactly
-- that combination of properties. Add a test to check whether you got the
-- properties right. (I'll do the first one as an example.)

-- refl, symm, trans
rst :: Reln
rst = [(1,1), (2,2), (3,3), (4,4), (5,5), (6,6), (7,7), (8,8)]
rst_test = refl rst && symm rst && trans rst

-- refl, symm, not trans
rst' :: Reln
rst' = [(1,1), (2,2), (3,3), (4,4), (5,5), (6,6), (7,7), (8,8), (2,3), (3,2), (3,4), (4,3)]
rst'_test = not(trans rst') && (refl rst' && symm rst')

-- refl, not symm, trans
rs't :: Reln
rs't = [(1,1), (2,2), (3,3), (4,4), (5,5), (6,6), (7,7), (8,8), (1,3)]
rs't_test = (trans rs't && refl rs't) && not(symm rs't)

-- refl, not symm, not trans
rs't' :: Reln
rs't' = [(1,1), (2,2), (3,3), (4,4), (5,5), (6,6), (7,7), (8,8), (2,3), (3,8)]
rs't'_test = (not (trans rs't')) && (not (symm rs't')) && refl rs't'

-- not refl, symm, trans
r'st :: Reln
r'st = [(2,2)]
r'st_test = (symm r'st && trans r'st) && not(refl r'st)

-- not refl, symm, not trans
r'st' :: Reln
r'st' = [(2,3), (3,2)]
r'st'_test = not(trans r'st') && symm r'st' && not(refl r'st')

-- not refl, not symm, trans
r's't :: Reln
r's't = [(2,3), (3,4), (2,4)]
r's't_test = not(refl r's't) && not(symm r's't) && trans r's't

-- not refl, not symm, not trans
r's't' :: Reln
r's't' = [(2,3), (3,4)]
r's't'_test = not(refl r's't') && not(symm r's't') && not(trans r's't')


---- PART 2: Partitions of u -----

-- A partitition, P, of u is a list of blocks, which are lists of elements
-- of u, that satisfies certain these conditions:
-- nontrivial: forall X in P, exists x in U, x in X, or
--             {} not in P
-- total: forall x in U, exists X in P, x in X
-- disjoint: forall X,Y in P (exists a, a in X /\ a in Y) -> X = Y, or
--           forall X,Y in P, X /= Y -> X intersect Y = {}
-- For example, here is the partitition of u corresponding to equivalence mod 3:
eqmod3_part :: [[Int]]
eqmod3_part = [[1,4,7], [2,5,8], [3,6]]

-- Write a function part that tests whether a list of lists is a partition of u

-- Helper functions

-- check if a list contains an empty set
-- Empty set can't be in the partitions
noEmpty :: [[Int]] -> Bool
noEmpty xr = not(null(head(sort xr)))
-- Sort from Data.List works on list of lists
-- Sort first, empty list will be in front if any
-- take the first list and check if it is null
-- false if empty set, true if no empty set

-- Check if all the lists combined cover all the values of x
-- Dont care about dupilcates yet
coverall :: [[Int]] -> Bool
coverall xr = and [x `elem` (concat xr) | x <- u]

-- Check if there are any duplicates
-- false if there are dups, true if there are
-- Easy check - Since all values must be present of u
-- simply check if the length of the list with duplicates
-- is the same length of the list with no duplicates
noDup :: [[Int]] -> Bool
noDup xr = (length (concat xr)) == (length(nub(concat xr))) 

part :: [[Int]] -> Bool
part bs = noEmpty bs && coverall bs && noDup bs

-- Write a function eq2part that takes an equivalence relation on u as input
-- and returns the associated partition of u. You can assume that the input is
-- really an equivalence relation on u.
eq2part :: Reln -> [[Int]]
eq2part rs = undefined


-- Write a function part2eq that takes a partition of u as input and returns
-- the associated equivalence relation on u. You can assume that the argument
-- is really a partition of u.
part2eq :: [[Int]] -> Reln
part2eq bs = undefined