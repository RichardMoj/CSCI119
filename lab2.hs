---- CSci 119, Fall 2019, Lab 2 ----

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
-- undefined--[ (a,b) == (b,a) | a <- u, b <- u]
-- and [ (`elem` (n,n)) | n <- u]
-- [ (n,n) `elem` rs | n <- u]
-- [ (n,n) `elem` [(1,1)] | n <- u]
-- returns [T F F F F F F F]
-- refl should take a type Reln and output a Bool
-- Take a list of  ordered pair of ints and output true/false
-- So check to see if ordered reflexive pairs are found in
-- the input list?

-- elem returns whether something is in a list, usually used by infix
-- function returning true/false



-- Write a function symm that tests whether a relation is symmetric:
-- R is symmetric if: forall a b, (a,b) in R -> (b,a) in R
-- Example: [(1,1), (1,2), (2,1)] is symmetric but [(1,1), (1,2)] is not.
symm :: Reln -> Bool
symm rs =  and [ (n,y) `elem` rs | (y,n) <- rs]

--[( ((n,y) `elem` [(1,1), (1,2), (2,1)]) && 
 --((y,n) `elem` [(1,1), (1,2), (2,1)]) | n <- u, y<-u)]

--[((n,y) `elem` [(1,1), (1,2), (2,1)]) && ((y,n) `elem` [(1,1), (1,2), (2,1)]) | n<-[1..2], y<-[1]]
 -- Checks if (1,1) and (1,1) are elements
 -- checks if (1,2) and (2,1) are elements
 -- No need to check further
 -- issue is y is already known and this is tailored for a specific value
 -- not the solution?

 -- [[((n,y) `elem` [(1,1), (1,2), (2,1)]) && ((y,n) `elem` [(1,1), (1,2), (2,1)]) | n<-[1..2]] | y<-[1..2]]
 -- Checks for 1,1 then 2,1 - T/T
 -- checks for 1,2 then 2,2 - T/F
 -- get or? as long as one ordered pair and it's reverse exists?
 -- then get the and?


-- [[((y,n) `elem` [(1,1), (1,2), (2,1)]) && ((n,y) `elem` [(1,1), (1,2), (2,1)]) | n<-[1..2]] | y<-[1..2]]
-- Nearly Identical to ^, but checks through all possible variations
-- of (y, n), where 'y' stays a single number first
-- Ex: 1,1, 1,2 1,3, 1,4
-- still not the solution
-- The condition must be that if an ordered pair exists in the input list
-- then the reverse ordered pair must exist as well


 -- 1,1     1,2,     2,1,          2,2
 -- 1,1 & 1,1,     1,2 & 2,1,      2,1 && 1,2


-- Still check if an ordered pair is in the input list
-- 
-- [ (n,y) `elem` [(1,1), (1,2), (2,1)] |  (y,n) <- [(1,1), (1,2), (2,1)]]
-- checks if an reversed ordered pair exists in the input list
-- for every ordered pair in the input list.


-- Write a function trans that tests whether a relation is transitive:
-- R is transistive if: forall a b c, (a,b) in R /\ (b,c) in R -> (a,c) in R
-- Example: [(1,2),(2,3),(1,3),(4,4)] is transitive but [(2,3),(3,2)] is not
trans :: Reln -> Bool
trans rs = and [not (null[ (n,r) `elem` [(2,3)] | 
 (n,y) <- [(2,3)], (z,r) <- [(2,3)], y == z])]


-- and [ (n,r) `elem` rs | (n,y) <- rs, (z,r) <- rs, y == z]
-- There is an issue with this found during the last Q of the relations Q's
-- 3 different ways a relation can be trans

-- [(1,2), (2,3), (1,3)], a minimum of 3 pairs must exist if there is no
-- reflexive pair

-- [(1,1), (1,2)], two pairs can exist as long as one is reflexive and the
-- the other builds off the reflexive pair

-- [(1,1)], A single reflexive pair is also trans

-- the last question [(2,3)] counted as trans. This is because it found
-- (n,y) pair, but could not find a (z,r) pair and then returned []
-- which defaulted to true.


-- [ (n,y) `elem` rs && (y,r) `elem` rs <= (n,r) `elem` rs ]

-- [ ((y,r) `elem` rs) && ((n,r) `elem` rs) | (n,y) <- rs]
-- variable r not in scope

-- [(n,r) `elem` rs | (n,y) <- rs, (y,r) <- rs]

-- *Main> [ (n,r) `elem` [(1,2),(2,3),(1,3),(4,4)]  | (n,y) <- [--(1,2),(2,3),(1,3),(4,4)], (y,r) <- [(1,2),(2,3),(1,3),(4,4)]]
--[True,True,True,False,False,True,True,False,True,True,True,False,False,False,--False,True]
 -- issue: grabbing first pair for n,y and grabbing same first pair for y,r
 -- y,r should be a differrent pair, need to find a way to grab a second pair
 -- that starts with the first y.



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

-- Adding a single extra order pair without it's reverse makes it non-sym
-- Make that extra order pair non trans

-- not refl, symm, trans
r'st :: Reln
r'st = [(2,2)]
r'st_test = (symm r'st && trans r'st) && not(refl r'st)

-- In order for something to be sym - there must be 2 pairs
-- If the first ordered pair is not reflexive.
-- [(2,3), (3,2)]
-- [(2,2)]

-- In order for something to be transitive - there must be 3 pairs
-- If the first order pair is not reflexive.
-- Can also be just a reflexive pair itself
-- [(2,3), (3,4), (2,4)]
-- [(2,2), (2,3)]
-- [(2,2)]

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
r's't'_test = trans r's't'
-- not(refl r's't') && not(symm r's't') && not(trans r's't')


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

-- In order for something to be a valid partition
-- Must not have empty set
-- all values in the parition combined must cover all of u
-- none of the partitions must have anything in common
-- ^ no duplicates in other words


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

-- Without this, [[1,1,2]..[]] would be false
-- But sets don't care about duplicates, ^ equal to [[1,2]..[]]
-- concat and then checking length could result in not being a part
-- when infact it is a part due to the bug above.
-- This fixes it, by removing all internal dups inside of each list
rmInternalDups :: [[Int]] -> [[Int]]
rmInternalDups ls = [ nub(head([x])) | x <- ls]


noDup :: [[Int]] -> Bool
noDup xr = (length (concat(rmInternalDups xr))) == (length(nub(concat xr)))

-- (length (concat xr)) == (length(nub(concat xr))) 

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

-- take in a list of lists of ints
-- output a list of ordered pairs