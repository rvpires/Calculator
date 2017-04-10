--Calculator in Haskell - Rodrigo Maia e Costa Vaz Pires - maiar@student.chalmers.se

module Expr where

import Data.Char
import Data.List
import Parsing
import System.Random
import Data.Maybe
import Data.List
import Test.QuickCheck
import Test.QuickCheck.Gen
import Test.QuickCheck.Random

data Expr = Num Double
          | Add Expr Expr
          | Mul Expr Expr
          | X
          | Sin Expr
          | Cos Expr
    deriving(Eq, Ord)

example1 = (Cos (Add (Num 3) (Mul (Num 5) (X)))) --cos(3+5x)
example2 = (Mul (Num 5) (X)) --5*x
example3 = (Sin(Cos (Add (Num 3) (Mul (Num 5) (X))))) --sin (cos(3+5x))
example4 = Mul (Num 5) (Num 5)
----------------------- PART A-----------------------------------------------

showExpr :: Expr -> String
showExpr (Num n)   = show n
showExpr (Add a b) = showExpr a ++ "+" ++ showExpr b
showExpr (Mul a b) = showFactor a ++ "*" ++ showFactor b
showExpr X         = "x"
showExpr (Sin n)   = "sin " ++ showSC n
showExpr (Cos n)   = "cos " ++ showSC n

showFactor :: Expr -> String
showFactor (Add a b) = "(" ++ showExpr (Add a b) ++")"
showFactor e         = showExpr e

showSC :: Expr -> String
showSC X           = "x"
showSC (Num n)     = show n
showSC x@(Add a b) = "(" ++ showExpr x ++ ")"
showSC x@(Mul a b) = "(" ++ showFactor x ++ ")"
showSC x           = showExpr x

instance Show Expr where
  show = showExpr

-------------------------------------------------------------------------

eval :: Expr -> Double -> Double
eval (Num n) x   = n
eval (Add a b) x = eval a x + eval b x
eval (Mul a b) x = eval a x * eval b x
eval X x         = x
eval (Sin n) x   = sin (eval n x)
eval (Cos n) x   = cos (eval n x)


-------------------------------------------------------------------------
readExpr :: String -> Maybe Expr
readExpr s = case parsed of
    Just (e,_) -> Just e
    _ -> Nothing
    where parsed = parse expr (filter (' ' /=) s)

--Following code modified from ParsingExamples.hs

expr, term, factor :: Parser Expr

expr = leftAssoc Add term (char '+')

term = leftAssoc Mul factor (char '*')

--modified to include sin, cos, var
factor =
    sinCosParse Sin "sin" <|>         --sin
    sinCosParse Cos "cos" <|>         --cos
    char 'x' *> return X <|>         --unknown variables
    Num <$> readsP <|>                 --floats
    (char '(' *> expr <* char ')')    --parenthesis

-- | Parse a list of items with separators
-- (also available in the Parsing module)
leftAssoc :: (t->t->t) -> Parser t -> Parser sep -> Parser t
leftAssoc op item sep = do i:is <- chain item sep
                           return (foldl op i is)

--Added
sinCosParse :: (Expr -> Expr) -> String -> Parser Expr
sinCosParse f (x:xs) = foldl (\b a -> b *> char a) (char x) xs *> (f <$> factor)

prop_ShowReadExpr :: Expr -> Bool
prop_ShowReadExpr e = ordExpr a == ordExpr e
  where
    a = fromJust (readExpr(showExpr e))

instance Arbitrary Expr where
  arbitrary = sized arbExpr

arbExpr :: Int -> Gen Expr
arbExpr s =
  frequency [ (1, do n <- arbitrary
                     return (Num n))
            , (s, do a <- arbExpr $ div s 5
                     b <- arbExpr $ div s 5
                     return (Add a b))
            , (s, do a <- arbExpr $ div s 5
                     b <- arbExpr $ div s 5
                     return (Mul a b))
            , (s, do a <- arbExpr $ div s 5
                     return (Cos a))
            , (s, do a <- arbExpr $ div s 5
                     return (Sin a))
            , (s, do return X)
            ]

--orders expression : 5 * cos(x) + 0.5 * sin (2.0*x) -> cos(x) * 5 + sin (x * 2.0) * 0.5
ordExpr :: Expr -> Expr
ordExpr (Add a b) = ordAdd a b
ordExpr (Mul a b) = ordMul a b
ordExpr (Sin a)   = Sin (ordExpr a)
ordExpr (Cos a)   = Cos (ordExpr a)
ordExpr e         = e

ordAdd :: Expr -> Expr -> Expr
ordAdd a b = foldl Add x xs
  where l = ordAdd' a b
        (x:xs) = sort l

ordAdd' :: Expr -> Expr -> [Expr]
ordAdd' (Add a b) (Add c d) = ordAdd' (ordExpr a) (ordExpr b) ++ ordAdd' (ordExpr c) (ordExpr d)
ordAdd' a         (Add b c) = (ordExpr a) : ordAdd' (ordExpr b) (ordExpr c)
ordAdd' (Add a b) c         = (ordExpr c) : ordAdd' (ordExpr a) (ordExpr b)
ordAdd' a         b         = [(ordExpr a),(ordExpr b)]

ordMul :: Expr -> Expr -> Expr
ordMul a b = foldl Mul x xs
  where l = ordMul' a b
        (x:xs) = sort l

ordMul' :: Expr -> Expr -> [Expr]
ordMul' (Mul a b) (Mul c d) = ordMul' (ordExpr a) (ordExpr b) ++ ordMul' (ordExpr c) (ordExpr d)
ordMul' a         (Mul b c) = (ordExpr a) : ordMul' (ordExpr b) (ordExpr c)
ordMul' (Mul a b) c         = (ordExpr c) : ordMul' (ordExpr a) (ordExpr b)
ordMul' a         b         = [(ordExpr a),(ordExpr b)]

-------------------------------------------------------------------------
simplify :: Expr -> Expr
simplify e = simplify' (ordExpr e)

simplify' :: Expr -> Expr
simplify' (Add x y)  =   add (simplify' x) (simplify' y)
simplify' (Mul x y)  =   mul (simplify' x) (simplify' y)
simplify' (Sin x)    =   Sin (simplify' x)
simplify' (Cos x)    =   Cos (simplify' x)
simplify' x          =   x

--multiplication rules
mul :: Expr -> Expr -> Expr
mul x       (Num 0)   = Num 0
mul (Num 0) y         = Num 0
mul x       (Num 1)   = x
mul (Num 1) y         = y
mul (Num x) (Num y)   = Num (x*y)
mul x       y         = Mul x y

--addition rules
add :: Expr -> Expr -> Expr
add x       (Num 0)   = x
add (Num 0) y         = y
add (Num x) (Num y)   = Num (x+y)
add x       y         = Add x y

prop_simplify :: Expr -> Double -> Bool
prop_simplify e n = eval e n  == eval newe n
  where newe = simplify ecd
---------------------------------------------------------------------------

differentiate :: Expr -> Expr
differentiate e = differentiate' (ordExpr e)

differentiate' :: Expr -> Expr
differentiate' (Num n)   = Num 0
differentiate' X       = Num 1
differentiate' (Add x y) = simplify (Add (differentiate' x) (differentiate' y))
differentiate' (Mul x y) = simplify (Add (Mul x (differentiate' y))
                                (Mul y (differentiate' x)))
differentiate' (Sin x)   = simplify (Mul (differentiate' x) (Cos x))
differentiate' (Cos x)   = simplify (mul (Num (-1)) (mul (differentiate' x) (Sin x)))


-------------------------------------------------------------------------
