--------------------------------------------------------------------------------
-- Author       : Marcel Schütz
-- Year         : 2020
-- Description  : A simple implementation of finite monoids and groups.
--------------------------------------------------------------------------------

module Group where

import Prelude hiding (Monoid, (>>), and)
import Data.List hiding (and)
import Data.Char


-- Quantifiers

{- Check whether all elements of a list satisfy a unary predicate -}
forall :: [a] -> (a -> Bool) -> Bool
forall xs p = all p xs

{- Check whether all elements of a list satisfy a binary predicate -}
forall2 :: [a] -> (a -> a -> Bool) -> Bool
forall2 xs p = forall xs $ forall xs . p

{- Check whether all elements of a list satisfy a ternary predicate -}
forall3 :: [a] -> (a -> a -> a -> Bool) -> Bool
forall3 xs p = forall2 xs (\x y -> forall xs (p x y))

{- Check whether some element of a list satisfies a unary predicate -}
exists :: [a] -> (a -> Bool) -> Bool
exists xs p = any p xs


-- Group axioms

{- Check whether a function is of the form X -> X -}
closed1 :: Eq a => [a] -> (a -> a) -> Bool
closed1 carrier f = forall carrier (\x -> f x `elem` carrier)

{- Check whether a function is of the form X \times X -> X -}
closed2 :: Eq a => [a] -> (a -> a -> a) -> Bool
closed2 carrier f = forall2 carrier (\x y -> f x y `elem` carrier)

{- Check whether a function is associative -}
asso :: Eq a => [a] -> (a -> a -> a) -> Bool
asso carrier f = forall3 carrier (\x y z -> f x (f y z) == f (f x y) z)

{- Check whether an element is a neutral element -}
neutr :: Eq a => [a] -> a -> (a -> a -> a) -> Bool
neutr carrier e mul = e `elem` carrier &&
  forall carrier (\x -> (mul x e == x) && mul e x == x)

{- Check whether a function maps every element to its inverse -}
invers :: Eq a => [a] -> (a -> a -> a) -> (a -> a) -> a -> Bool
invers carrier mul inv e = forall carrier (\x -> mul x (inv x) == e &&
  mul (inv x) x == e)


-- Helpers

(>>) :: a -> (a -> b) -> b
x >> f = f x

and :: (a -> Bool) -> (a -> Bool) -> (a -> Bool)
and p q x = p x && q x


-- Groups

{- A group: A set together with a binary operation, a unary operation and a
constant -}
data Group a = Group [a] (a -> a -> a) (a -> a) a

{- Check whether an instance of 'Group' satisfies the group axioms -}
isAGroup :: Eq a => Group a -> Bool
isAGroup (Group carrier mul inv e) =     -- ATTENTION: 'carrier' must be finite!
  closed2 carrier mul &&
  asso carrier mul &&
  neutr carrier e mul &&
  closed1 carrier inv &&
  invers carrier mul inv e


-- Examples

{- The trivial group -}
theTrivialGroup :: Group Int
theTrivialGroup = Group [0] (+) (\x -> -x) 0

{- The factor group Z/nZ -}
theGroupOfIntegersModulo :: Int -> Group Int
theGroupOfIntegersModulo n = Group [0 .. (n-1)] (\x y -> (x + y) `mod` n)
  (\x -> (n - x) `mod` n) 0


-- Homomorphisms

{- A group homomorphism: The domain, The actual function and the codomain -}
data Homomorphism a b = Homomorphism (Group a) (a -> b) (Group b)

{- Check whether an instance of 'Homomorphism' is a group homomorphism -}
isAHomomorphism :: Eq b => Homomorphism a b -> Bool
isAHomomorphism (Homomorphism (Group x mulX _ _) f (Group y mulY _ _)) =
  forall2 x (\u v -> f (mulX u v) == mulY (f u) (f v))

{- Check whether an instance of 'Homomorphism' is injective -}
isInjective :: Eq a => Eq b => Homomorphism a b -> Bool
isInjective (Homomorphism (Group x _ _ _) f _) =
  forall2 x (\u v -> (f u /= f v) || u == v)

{- Check whether an instance of 'Homomorphism' is surjective -}
isSurjective :: Eq b => Homomorphism a b -> Bool
isSurjective (Homomorphism (Group x _ _ _) f (Group y _ _ _)) =
  forall y (\v -> exists x (\u -> f u == v))

{- Check whether an instance of 'Homomorphism' is bijective -}
isBijective :: Eq a => Eq b => Homomorphism a b -> Bool
isBijective f = isInjective f && isSurjective f

{- Check whether an instance of 'Homomorphism' is an isomorphism -}
isAnIsomorphism :: Eq a => Eq b => Homomorphism a b -> Bool
isAnIsomorphism f = f >> (isAHomomorphism `and` isBijective)


-- Examples

{- The identity function on a group -}
theIdentityFunctionOn :: Group a -> Homomorphism a a
theIdentityFunctionOn g = Homomorphism g id g


{-
Some example commands for using the functions defined above:

> theTrivialGroup >> isAGroup
> theGroupOfIntegersModulo 35 >> isAGroup
> theIdentityFunctionOn theTrivialGroup >> isAHomomorphism
> theIdentityFunctionOn (theGroupOfIntegersModulo 5) >> isAnIsomorphism

-}
