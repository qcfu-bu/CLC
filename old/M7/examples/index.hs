module Index where

import qualified Prelude

data Nat =
   O
 | S Nat

data Prod a b =
   Pair a b

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
add :: Nat -> Nat -> Nat
add n m =
  case n of {
   O -> m;
   S p -> S (add p m)}

data Le =
   Le_n
 | Le_S Nat Le

type Lt = Le

get :: Nat -> Prod a1 ()
get =
  Prelude.error "AXIOM TO BE REALIZED"

type Array a = Nat

index :: Nat -> Nat -> Lt -> (Array a1) -> Prod a1 (Array a1)
index m _ _ a =
  case get (add a m) of {
   Pair x _ -> Pair x a}

