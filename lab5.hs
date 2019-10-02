-- CSci 119, Lab 5
-- Reference: Lecture notes, Sections 4.1, 4.2
import Data.List(nub)

-- Again, for this (and most) labs, the alphabet will be {a,b} to keep testing
-- easier, but your code should work just as well for any finite list.
sigma = ['a', 'b']

-- Finite State Machine M = (Q, s, F, d) with integer states
type FSM = ([Int], Int, [Int], Int -> Char -> Int)

-- Check whether a finite state machine (qs, s, fs, ts) is correct/complete:
-- (1) States qs are unique (no duplicates)
-- (2) Start state is a state (s is in qs)
-- (3) Final states are states (fs is a subset of qs)
-- (4) Transition function gives a state in qs for every state in qs and
--     letter from sigma

-- Helper Functions

-- Check if states in qs are unique
uniqueStates :: [Int] -> Bool
uniqueStates xs = length xs == length(nub xs)

-- Check if start state is a state found in qs
isState :: Int -> [Int] -> Bool
isState n xs = n `elem` xs

finalIsSubset :: [Int] -> [Int] -> Bool
finalIsSubset [] _ = False
finalIsSubset final@(x:xs) start@(y:ys) = and [ n `elem` y| n <- final, y <- [(start)]]

-- transitionCheck should take in all states, QS all leters from Sigma
-- and gives back a state. The returned state should be a state from QS 
transitionCheck :: (Int -> Char -> Int) -> [Int] -> [Char] -> Bool
transitionCheck func qs@(x:xs) sig@(y:ys) = and [ (func q c) `elem` l | q <- qs, c <- sig, l <- [qs]]



checkFSM :: FSM -> Bool
-- checkFSM ([Int], Int, [Int], Int-Char -> Int)
checkFSM (qs, s, fs, ts) = undefined
-- checkFSM (qs, s, fs, ts) = 
--	uniqueStates qs && isState s qs && finalIsSubset fs qs && 

-- Gives the delta* function (recursive in w)
delta_star :: FSM -> Int -> [Char] -> Int
delta_star m q w = undefined

-- Machine acceptance, Definition 1 (via delta*)
accept1 :: FSM -> [Char] -> Bool
accept1 m w = undefined


-- Machine acceptance, Definition 2 (via L_q(M))

-- accept2_aux m q w = whether m, starting in q, accepts w (recursive in w)
accept2_aux :: FSM -> Int -> [Char] -> Bool
accept2_aux m q w = undefined

-- Acceptance, defined (non-recursively) in terms of accept2_aux
accept2 :: FSM -> [Char] -> Bool
accept2 m w = undefined


---- FSM construction

-- Define a machine that accepts exactly the strings with an odd number of b's
-- and test it adequately
oddbs :: FSM
oddbs = undefined

-- Define a machine that accepts exactly the strings that do not contain "aab"
-- as a substring and test it adequately
avoid_aab :: FSM
avoid_aab = undefined

-- Define a machine that accepts all strings that end in "ab" and test
end_ab :: FSM
end_ab = undefined

-- Define a function that takes a string and returns a machine that excepts
-- exactly that string and nothing else
exactly :: String -> FSM
exactly s = undefined


-- TESTING
-- test1 = and [accept1 FSM x == accept2 FSM x | x <- strings 5]