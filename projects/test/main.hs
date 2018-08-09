simp :: Int -> String
simp n = "hello"

main = do
  -- let msg = simp 1
  -- print msg
  -- "hello"
  putStrLn "hello"

data RomanDigit = I | V | X | L | C | D | M deriving (Eq, Ord)

toRomanDigit :: String -> RomanDigit
toRomanDigit "M" = M
toRomanDigit "D" = D
toRomanDigit "C" = C
toRomanDigit "L" = L
toRomanDigit "X" = X
toRomanDigit "V" = V
toRomanDigit "I" = I

romanDigitValue :: RomanDigit -> Int
romanDigitValue M = 1000
romanDigitValue D = 500
romanDigitValue C = 100
romanDigitValue L = 50
romanDigitValue X = 10
romanDigitValue V = 5
romanDigitValue I = 1

instance Show RomanDigit where
  show M = "M"
  show D = "D"
  show C = "C"
  show L = "L"
  show X = "X"
  show V = "V"
  show I = "I"

romanToArabic :: String -> Int
romanToArabic s = r2a (toRomanDigit $ take 1 s) (tail s) 0
-- r2a :: RomanDigit -> String -> Int -> Int
-- r2a a b c = 7
-- d =digit, t=tail, a=accumulator, b=buffer
-- r2a' :: RomanDigit -> String -> Int -> Int -> Int
-- r2a' h "" a b = a + romanDigitValue h
-- r2a' h t a b
--       | h == M = r2a' (toRomanDigit $ take 1 t) (tail t) (a + romanDigitValue h) 0
--       | h == C = r2a' (toRomanDigit $ take 1 t) (tail t) (a + romanDigitValue h) 0
--       | otherwise = a + 9
-- r2a :: RomanDigit -> String -> Int ->  Int
-- r2a d "" a  = a + romanDigitValue d
-- r2a d t a  = if d >= firstTailDigit
--                 then r2a (toRomanDigit $ take 1 t) (tail t) (a + romanDigitValue d)
--                 else r2a secondTailDigit (tail $ tail t) (a + romanDigitValue firstTailDigit -  romanDigitValue d)
--               where firstTailDigit = toRomanDigit $ take 1 t
--                     secondTailDigit = getSecondDigit t

-- If its monotonically decreasing e.g no "pre-modifiers" like "CM", it's a
-- straight recursive accumulation.  If we do have a pre-modifier, we basically
-- process the digit and the first tail digit at the same time in the 'else'.
-- In short the only "tricky" thing is processing two digits in one recursive
-- iteration interval instead of one if we are not purely monotonically
-- decreasing.
r2a :: RomanDigit -> String -> Int ->  Int
r2a d "" a  = a + romanDigitValue d
r2a d t a  = if d >= firstTailDigit
                then r2a (toRomanDigit $ take 1 t) (tail t) (a + romanDigitValue d)
                else if (length t) > 1
                  then r2a secondTailDigit (tail $ tail t) (a + romanDigitValue firstTailDigit -  romanDigitValue d)
                  else (a + romanDigitValue firstTailDigit -  romanDigitValue d)
              where firstTailDigit = toRomanDigit $ take 1 t
                    secondTailDigit = getSecondDigit t

getSecondDigit :: String -> RomanDigit
getSecondDigit s = toRomanDigit $ tail $take 2 s

-- getThirdDigit :: String -> String
-- getThirdDigit s = toRomanDigit $ tail $take 3 s
-- r2a ::String -> String -> Int -> Int -> Int
-- r2a h t a b = 7

--------------- second Kata : Bird names to bird code
---- see https://edabit.com/challenge/MDixWSYxH5JZX3xo3
