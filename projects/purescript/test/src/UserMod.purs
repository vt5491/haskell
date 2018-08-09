module UserMod where

import Data.Maybe
import Data.String
import Prelude

import Control.Comonad (extract)
import Data.Array (filter, (..))
import Data.Array.NonEmpty (singleton, uncons)
import Data.Enum (class BoundedEnum)
import Data.Foldable (product)
import Data.String as S
import Data.String.CodePoints as CP
import Effect.Console (log)
-- import Data.Ord (Ord)

vtVal :: Int
vtVal = 7

factors :: Int -> Array (Array Int)
factors n = filter (\xs -> product xs == n) $ do
-- factors n = filter (\xs -> product xs == n)  do
  i <- 1 .. n
  j <- i .. n
  pure [i, j]

factors' = do
  i <- 1 .. 6
  j <- i .. 6
  let k = i
  pure [i, j, k]

factors'' = do
  i <- 1 .. 6
  j <- 1 .. 6
  pure [i, j]

-- primes :: Int -> Array Int
-- -- primes n = (filter \x -> (x `mod` 2) == 0)  (1..n)
-- primes n =
  -- do
    -- (filter \x -> x `mod` 2  == 1)  (1..n)
    -- i <- (filter \x -> x `mod` 2  == 1)  (1..n)


-- is n a factor of m
-- isFactorOf 10 5
isFactorOf :: Int -> Int -> Boolean
isFactorOf m n = m `mod` n == 0

isFactorable :: Int -> Boolean
-- isPrime 1 = false
-- isPrime n = if isFactorOf n n / 2
--               then true
--               else isPrime
-- isPrime n = do
--   seed <- n / 2
-- isPrime n = if isFactorOf n n / 2 || isPrime $ n - 1
-- isPrime n = if isFactor n $ n - 1
isFactorable n = if isFactorOf n $ n / 2
              then true
              else isFactorable2 n $ (n / 2) -1

isFactorable2 :: Int -> Int -> Boolean
isFactorable2 n 1 = false
isFactorable2 n x = if isFactorOf n x
                 then true
                 else isFactorable2 n $ x -1


-- gcd n m = if n > m
--             then gcd (n - m) m
--             else gcd n (m - n)

-- data TrafficLight :: Red | Yellow | Green
-- class RomaNumClass :: String
-- data RomanSeq = [M D C L V I]
-- class (Bounded a, Enum a) <= BoundedEnum a where
-- instance enumRomanDigit :: BoundedEnum RomanDigit where
--   succ I = V
--   pred V = I
-- data RomanNum = "M" | "D" | "C" | "L" | "V" | "I" deriving (Ord)
-- data RomanDigit a = M  | D | C | L | V | I deriving Ord)
-- data RomanDigit a = M | D | C | L | V | I
-- data RomanDigit a = M | D
-- data RomanDigit  = M | D | C | L | V | I deriving (Eq)
--
-- newRomanDigit :: Int -> RomanDigit
-- newRomanDigit 1000 = M
-- newRomanDigit 500 = D
-- newRomanDigit _ = I

-- instance showRomanDigit ::
--   -- where show (Foo {bar}) = "Foo bar=" ++ show bar
--   where show M = "M"

-- instance showRomanDigit :: where show (M) = M

-- instance showRomanDigit :: Show RomanDigit where
--   -- show x = "Foo bar=" <> show x
--   show M = "M"
--   show D = "D"
--   show C = "C"
--   show L = "L"
--   show V = "V"
--   show I = "I"

-- instance showRomanDigit :: Compare RomanDigit where
--   (>) M D = true

-- class Eq a <= Ord a where
--   compare :: a -> a -> RomanDigit

-- class Ord a <= Ord a where
--   compare :: a -> a -> RomanDigit

-- instance eqRomanDigit :: Eq RomanDigit where
  -- eq (RomanDigit a) (RomanDigit b) = a == b
  -- a b = a == b
  -- eq M M = true
  -- eq _ _ = true
  -- M == M = True
  -- D == D = True
  -- eq (ByEmail a) (ByEmail b) = a == b
  -- eq (ByPhone a) (ByPhone b) = a == b
  -- eq _ _ = false

-- instance Eq RomanDigit where
--   M == M = True
--   D == D = True
-- derive instance ordRomanDigit :: Ord RomanDigit

-- derive instance ordRomanDigit :: Ord a => Ord (RomanDigit a)
-- instance Ord RomanDigit where
--   M (>) D = true

-- compareRomDig :: RomanDigit -> RomanDigit -> Boolean
-- compareRomDig a b = a > b

compRomDig :: Int -> Int -> Boolean
compRomDig a b = a > b
-- instance ordRomanNum :: Ord RomaNum where
--   compare = unsafeCompare

-- do it recursively, then try to do it using list functions
-- recursively  _
-- list functions _

-- M, m= 0x4d  , 0x6d
-- D, d= 0x44  , 0x64
-- C, c= 0x43  , 0x63
-- L, c= 0x4C  , 0x6c
-- X, x= 0x58  , 0x78
-- V, v= 0x56  , 0x76
-- I, i= 0x49  , 0x69

-- convert roman number string to a arabic digits
-- e.g. MCMI -> 1901
-- romanToArabic :: String -> Int
-- romanToArabic s =  r2a h t 0 0
--   where
--     u = S.uncons s
--     h = extractHead u
--     t = extractTail u
--
--
-- r2a :: Array Char -> Int
-- the workhorse of romanToArabic.  Has an accumulator for recursion.
-- it takes the head and tail of a string, accumlator, final result
-- r2a :: String -> String -> Int -> Int
-- r2a h t a | h == "M" = 1000
--           | otherwise = 7
-- h = head, t= tail, a=accumular, b=buffer (temp accumlator)
-- r2a :: String -> String -> Int -> Int -> Int
-- -- r2a h t a | h == "M" = r2a $ extractHead (uncons t) $ extractTail (uncons t) $ 1000
-- -- r2a h t a | h == "M" = r2a h' t' 1000
--               -- where
--               --   u = S.uncons t
--               --   h' = extractHead u
--               --   t' = extractTail u
-- r2a h t a b| h == "M" = r2a h' t'  1000  0
--           where
--             u = S.uncons t
--             h' = extractHead u
--             t' = extractTail u
--           | h == "D" = r2a (extractHead u) (extractTail $ S.uncons t) (a + 500)  (0)
--           where
--             u = S.uncons t
--           | h == "C" = r2a (extractHead u) (extractTail $ S.uncons t) (a + 100)  (0)
--           where
--             u = S.uncons t
--           | otherwise = a + 7
            -- a1 = "C"
            -- a2 = "C"
-- r2a :: String -> String -> Int -> Int -> Int
-- r2a h t a b
--           | h == "M" = r2a h' t'  1000  0
--           where
--             u = S.uncons t
--             h' = extractHead u
--             t' = extractTail u
--           | h == "D" = r2a h' t' (a + 500) 0
--           where
--             u = S.uncons t
--             h' = extractHead u
--             t' = extractTail u
--           | h == "C" = r2a h' t' a  100
--           where
--             u = S.uncons t
--             h' = extractHead u
--             t' = extractTail u
--           | otherwise = a + 7



-- c= fromMaybe (codePointFromChar 'a') (codePointAt 0 "abc")
-- returns
-- > :type c
-- CodePoint
-- to convert to a string:
-- CP.singleton c
-- return "c"
-- arabicToRoman ::

-- how to reference a record in a maybe
-- maybe 0 (\x -> x.b + 1) a
-- where a= (Just { a: 7, b: 8 })
-- maybe (codePointFromChar ' ') (\x -> x.head) r
-- maybe "" (\x -> x.tail) r
-- r=S.uncons "abcd"
-- Note: cannot get the compiler to accept my type on this
-- Note: the following three are to get at the Maybe created by 'uncons <str>'
extractHead' :: Maybe { head :: CodePoint , tail :: String } -> CodePoint
extractHead' r = maybe (codePointFromChar ' ') (\x -> x.head) r

extractHead :: Maybe { head :: CodePoint , tail :: String } -> String
extractHead r = S.singleton $ maybe (codePointFromChar ' ') (\x -> x.head) r

extractTail :: Maybe { head :: CodePoint , tail :: String } -> String
extractTail r = maybe "" (\x -> x.tail) r

-- extractCharAsStr :: n -> String
-- example: extractCharAsStr 0 "abc"
-- returns: "a"
extractCharAsStr :: Int -> String -> String
extractCharAsStr n s =
  -- default to a space if we get a Nothing
  CP.singleton (fromMaybe (codePointFromChar ' ') (codePointAt n s))

extractCharAsStr' :: String -> Int -> String
extractCharAsStr' s n =
  -- default to a space if we get a Nothing
  CP.singleton (fromMaybe (codePointFromChar ' ') (codePointAt n s))
