-- CSci 119, Lab 4

import Data.List (sort, stripPrefix) -- for your solution to Lab 3
import Control.Monad (replicateM)    -- for strings function at the end


-- Normalize a list: sort and remove duplicates
norm :: Ord a => [a] -> [a]
norm xs = rad $ sort xs where
  rad :: Eq a => [a] -> [a]  -- Remove adjacent duplicates
  rad [] = []
  rad [x] = [x]
  rad (x:ys@(y:zs)) | x == y = rad ys
                    | otherwise = x : rad ys

-- Length-Ordered Lists over "character type" a (aka "strings")
-- Invariant: In LOL n xs, n == length xs
data LOL a = LOL Int [a] deriving (Eq,Ord)

instance Show a => Show (LOL a) where
  show (LOL n xs) = show xs

-- Empty list (epsilon)
eps :: LOL a
eps = LOL 0 []

-- Smart constructor for LOL a, establishes invariant
lol :: [a] -> LOL a
lol xs = LOL (length xs) xs

-- Normalized lists of LOLs (aka "languages")
-- Invariant: xs :: Lang a implies xs is sorted with no duplicates
type Lang a = [LOL a]

-- Smart constructor for (finite) languages
lang :: Ord a => [[a]] -> Lang a
lang xs = norm $ map lol xs

---- Regular expressions, along with input and output
data RegExp = Empty                -- Empty language
            | Let Char             -- Single letter language
            | Union RegExp RegExp  -- Union
            | Cat RegExp RegExp    -- Concatenation
            | Star RegExp          -- Kleene star
            deriving (Show, Eq)

-- Compact display form for RegExp
newtype Compact = Compact RegExp

instance (Show Compact) where    -- use precedence to minimize parentheses
  showsPrec d (Compact r) = sp d r where
    sp d Empty         = showString "@"
    sp d (Let c)       = showString [c]
    sp d (Union r1 r2) = showParen (d > 6) $  -- prec(Union) = 6
                         sp 6 r1 .
                         showString "+" .
                         sp 6 r2
    sp d (Cat r1 r2)   = showParen (d > 7) $  -- prec(Cat) = 7
                         sp 7 r1 .
                         sp 7 r2
    sp d (Star r1)     = sp 9 r1 .     -- prec(Star) = 8
                         showString "*"

-- Quick and dirty postfix RegExp parser, gives non-exaustive match on error
toRE :: String -> RegExp
toRE w = go w [] where
  go [] [r]              = r
  go ('+':xs) (r2:r1:rs) = go xs (Union r1 r2:rs)
  go ('.':xs) (r2:r1:rs) = go xs (Cat r1 r2:rs)
  go ('*':xs) (r:rs)     = go xs (Star r:rs)
  go ('@':xs) rs         = go xs (Empty:rs)
  go (x:xs) rs           = go xs (Let x:rs)


---------------- Your solution to Lab 3 ----------------

-- Include part of your solution to Lab 3 here for testing purposes.
-- After a few days, I will release my solution for you to use. Don't
-- duplicate the code just given above.


---------------- Part 1 ----------------

-- Membership for languages that satisfy the invariant (sorted, no duplicates),
-- even if they are infinite. Only look at the contents of a string when it is
-- necessary to do so, and stop as soon as you know the answer.
memb :: Ord a => LOL a -> Lang a -> Bool
memb (LOL n ys) [] = False
memb (LOL n ys) (x:xs) 
  | (LOL n ys) > x = memb (LOL n ys) (xs)
  | (LOL n ys) == x = True
  | otherwise = False;



-- Implement the seven recursive predications/operations on RegExp given in
-- Section 3.3 of the notes; call them empty, unitary, byp, inf, rever, lq,
-- and nep. Each should begin with a type declaration. Include several tests
-- for each function.

empty :: RegExp -> Bool
empty (Empty) = True
empty (Let a) = False
empty (Union r1 r2) = (empty (r1)) && (empty (r2))
empty (Cat r1 r2) = (empty (r1)) || (empty (r2))
empty (Star r1) = False

unitary :: RegExp -> Bool
unitary (Empty) = False
unitary (Let a) = False
unitary (Union r1 r2) = (unitary r1 && empty r2) || (empty r2 && unitary r1) || (unitary r1 && unitary r2)
unitary (Cat r1 r2) = unitary r1 && unitary r2
unitary (Star r1) = empty r1 || unitary r1

byp :: RegExp -> Bool
byp (Empty) = False
byp (Let a) = False
byp (Union r1 r2) = byp r1 || byp r2
byp (Cat r1 r2) = byp r1 && byp r2
byp (Star r1) = True

inf :: RegExp -> Bool
inf (Empty) = False
inf (Let a) = False
inf (Union r1 r2) = inf r1 || inf r2
inf (Cat r1 r2) = (inf r1 && not(empty r2)) || (inf r2 && not(empty r1))
inf (Star r1) = not(empty r1) && not(unitary r1)

rever :: RegExp -> RegExp
rever (Empty) = Empty
rever (Let a) = Let a
rever ( Union r1 r2) = Union (rever r1) (rever r2)
rever (Cat r1 r2) = Cat (rever r2) (rever r1)
rever (Star r1) = Star (rever r1)

lq :: Char -> RegExp -> RegExp
lq s (Empty) = Empty
lq s (Let a) 
  | s == a = (Star (Empty))
  | otherwise = Empty
lq s (Union r1 r2) = Union (lq s r1) (lq s r2)
lq s (Cat r1 r2) 
  | byp (r1) = Union (Cat (lq s r1) r2) (lq s r2)
  | otherwise = Cat (lq s r1) r2
lq s (Star r1) = Cat (lq s r1) (Star r1)

nep :: RegExp -> RegExp
nep (Empty) = Empty
nep (Let a) = Let a
nep (Union r1 r2) = Union (nep r1) (nep r2)
nep (Cat r1 r2) 
  | byp r1 = Union (Cat (nep r1) r2) (nep r2)
  | otherwise = Cat (nep (r1)) (r2)
nep (Star r1) = Cat (nep (r1)) (Star r1)






{- Part 1 Testing

memb

*Main> memb (LOL 4 "abab") [(LOL 2 "ab"),(LOL 3 "aba"),(LOL 4 "abab")]
True
*Main> memb (LOL 2 "ab") [(LOL 2 "ab"),(LOL 3 "aba"),(LOL 4 "abab")]
True
*Main> memb (LOL 2 "ab") [(LOL 2 "bb"),(LOL 3 "aba"),(LOL 4 "abab")]
False
*Main> memb (LOL 2 "ab") [(LOL 2 "aa"),(LOL 3 "aba"),(LOL 4 "abab")]
False
*Main> memb (LOL 2 "ab") [(LOL 3 "aba"),(LOL 4 "abab")]
False


-}


---------------- Part 2 ----------------

-- Implement the two matching algorithms given in Section 3.4 of the notes.
-- Call them match1 and match2. Start by implementing splits:

-- splits xs = list of all possible splits of xs, in order. For example,
-- splits "abc" = [("","abc"), ("a","bc"), ("ab","c"), ("abc","")]
splits :: [a] -> [([a], [a])]
splits xs = [ (take r list, drop r list) | r<- [0..length xs], list <- [xs] ]

match1 :: RegExp -> String -> Bool
match1 Empty w = False
match1 (Let a) w 
  | (length w == 1) = (Let a == (toRE w))
  | otherwise = False
match1 (Union r1 r2) w = match1 r1 w || match1 r2 w
match1 (Cat r1 r2) w = or [(match1 r1 w1) && (match1 r2 w2) | (w1, w2) <- splits w]
match1 (Star r1) w =  (null w) || or[(match1 r1 w1) && (match1 (Star r1) w2) | (w1,w2) <- splits w, not(null w1)]





-- Helper function
match2' :: [RegExp] -> Bool -> String -> Bool
match2' (r:rs) b w 
  | null (r:rs) = False       --Empty list, dont care about b or w
  | r == Empty = False        -- If head of the list is Empty
  | otherwise = True



match2 :: RegExp -> String -> Bool
match2 r w = undefined




-- Some regular expressions for testing. Also, test them on other solutions
-- to the exercises of Section 3.2 (as many as you can get). 

sigma = ['a', 'b']                -- Alphabet used in all examples below

ab   = toRE "aa.bb.+*"            -- every letter is duplicated
ttla = toRE "ab+*a.ab+.ab+."      -- third to last letter is a
ena  = toRE "b*a.b*.a.*b*."       -- even number of a's
bb1  = toRE "aba.+*b.b.aab.+*."   -- contains bb exactly once


-- For your tests, you may also find the following helpful. For example,
-- you can generate all strings of length 10 (or 20) or less and then test
-- to see whether match1 r w == memb (lol w) (lang_of r) for each such w.

-- All strings on sigma of length <= n (useful for testing)
strings :: Int -> [String]
strings n = concat $ [replicateM i sigma | i <- [0..n]]



{- Part 2 Testing









-}