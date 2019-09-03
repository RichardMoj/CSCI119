-- Richard Mojarro
-- CSCI 119
-- 2019FA

---- CSci 119, Lab 1 ----

-- Note: you will replace all instances of "undefined" below with your answers.


---- Boolean operators

-- The following code tests whether "and" is commutative:
bools = [True, False]
and_commutes = and [(p && q) == (q && p) | p <- bools, q <- bools]

-- Write similar defintions that test whether "or" is commutative,
-- "and" and "or" are associative, "and" distributes over "or",
-- "or" distributes over "and"
or_commutes = and [(p || q) == (q || p) | p <- bools, q <- bools]

and_assoc = and [((p && q) && r) == (p && (q && r))
 | p <- bools, q <- bools, r <- bools]

or_assoc = and [((p || q) || r) == (p || (q || r)) 
 | p <- bools, q <- bools, r <- bools]

and_dist = and [(p) && (q || r) == ((p && q) || (p && r)) 
 | p <- bools, q <- bools, r <- bools]

or_dist = and [(p) || (q && r) == (p || q) && (p || r) 
 | p <- bools, q <- bools, r <- bools]
          
-- The exclusive-or operation on Bool in Haskell is equivalent to /=.
-- Test the properties of this operation (commutativity, associativity,
-- distributivity over and+or, and distributivity of and+or over it)
-- using the same method as above
xor_commutes = and [(p /= q) == (q /= p) | p <- bools, q <- bools]

xor_assoc    = and [((p /= q) /= r) == (p /= (q /= r)) 
 | p <- bools, q <- bools, r <- bools]

xor_dist_and = and [(p /= (q && r)) == ((p /= q) && (p /= r)) 
 | p <- bools, q <- bools, r <- bools]

xor_dist_or  = and [(p /= (q || r)) == ((p /= q) || (p /= r)) 
 | p <- bools, q <- bools, r <- bools]

and_dist_xor = and [(p && (q /= r)) == ((p && q) /= (p && r)) 
 | p <- bools, q <- bools, r <- bools]

or_dist_xor  = and [(p || (q /= r)) == ((p || q) /= (p || r)) 
 | p <- bools, q <- bools, r <- bools]
               
-- The implication operator on Bool in Haskell is equivalent to <=.
-- Check whether implication is associative or commutative:
assoc_imp = and [(p <= (q <= r)) == ((p && q) <= r) 
 | p <- bools, q <- bools, r <- bools]
comm_imp = and [(p <= q) == (q <= p) | p <- bools, q <- bools]


----- Evaluating statements involving quantifiers

-- Assume that the universe of discourse is the set {1,2,3,4,5,6,7,8},
-- that is, that the word "number" temporarily means 1, 2, ..., 8.
-- Your solutions to the problems below should work no matter what
-- finite list of integers u is. For example, u = [5, 2, 17, 58, 21].

u = [1..8]

-- Translate each of the following statements first, in a comment, into a
-- logical statement involving forall, exists, and, or, imp, and not,
-- and then into Haskell code that checks ("brute force") whether
-- the statement is true. I'll work one example.

-- 1. "Every number that's greater than 2 is greater than 1"
-- A: forall n, (n > 2) imp (n > 1)
prob1_1 = and [(n > 2) <= (n > 1) | n <- u]   -- direct translation
prob1_2 = and [n > 1 | n <- u, n > 2]         -- using bounded quantifier

-- 2. Every number is either greater than 1 or less than 2
-- A: forall n, (n > 1) or (n < 2)
prob2 =  and [(n > 1) || (n < 2) | n <- u]

-- 3. Every two numbers are comparable with <= (i.e., either one is <=
--    the other or vice-versa)
-- A: forall n, y, n <= y or y <= n 
prob3 = and [((n <= y) || (y <= n)) | n <- u, y <- u]

-- 4. There is an odd number greater than 4
-- A: Exists n, odd(n) && (n > 4)
prob4 = or [n > 4 | n <- u, odd n]

-- 5: There are two odd numbers that add up to 10
-- A: There exists n1 and n2, odd (n) and odd (n2) and (n1 + n2 = 10)
prob5 = or [n + y == 10 | n <- u, y <- u, odd n, odd y]

-- 6. For every odd number, there is a greater even number (use the Haskell
--    predicates odd, even :: Integral a => a -> Bool)
-- A: Forall y, there exists n, n > y and even n and odd y
prob6 = and [or[n > y | n <- u, even n] | y <- u, odd y]

-- GOAL
-- Compare all even numbers to a single odd number, and repeat that
-- for however many odd number there are.

-- [((n,y),(n > y)) | n <- u, y <- u, even n] 
-- compares all even numbers to all values of y ( the whole universe)

-- [[((n,y),(n > y)) | n <- u, y <- u, even n]] 
-- No difference, except its a list inside of a list

-- [[((n,y), (n > y)) | n <- u, y <- u, even n] | y <- u, odd y]
-- Compares all even numbers to all numbers in the universe, 4 times
-- (4 lists inside of a list)
-- Why 4 times? Most likely due to there being 4 odd numbers (odd y)

-- [[((n,y),(n > y)) | n <- u, even n] | y <- u, odd y]
-- compares all even numbers to a single odd number each iteration
-- 4 times (4 Lists inside of a list)

-- 7. For every even number, there is a greater odd number
-- A: Forall y, there exists n, n > y and even and odd n 
prob7 = and [or[n > y | n <- u, odd n] | y <- u, even y]

-- Repeat of Q6, just switch some things around. Compare all odd
-- numbers to a single even number and repeat that for however
-- many even numbers there are


-- 8. There are two odd numbers that add up to 6
-- A:  There exists n1 and n2, odd(n1) and odd(n2) and (n1 + n2 = 6)
prob8 = or [n + y == 6 | n <- u, y <- u, odd n, odd y]

-- 9. There is a number that is at least as large as every number
--    (i.e., according to >=)
-- A: There exists y, forall n, y >= n
prob9 = or [and[y >= n| n <- u] | y <-u]

-- Similar idea to Q6 and Q7. Compare all values of n to a single 
-- value of y, for however many y values there are.
-- Unlike the previous ones, not looking for a single instance
-- to be true in each iteration, but a whole iteration to be true
-- 8 >= all n values




-- 10. For every number, there is a different number such that there are no
--    numbers between these two.
-- A: 
prob10 = undefined