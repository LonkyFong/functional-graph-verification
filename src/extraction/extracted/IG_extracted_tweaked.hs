module IG_extracted_tweaked where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

false_rect :: a1
false_rect =
  Prelude.error "absurd case"

false_rec :: a1
false_rec =
  false_rect

and_rect :: (() -> () -> a1) -> a1
and_rect f =
  f __ __

and_rec :: (() -> () -> a1) -> a1
and_rec =
  and_rect

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect _ f _ =
  f

eq_rec :: a1 -> a2 -> a1 -> a2
eq_rec =
  eq_rect

eq_rec_r :: a1 -> a2 -> a1 -> a2
eq_rec_r =
  eq_rec

andb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> Prelude.False}

orb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
orb b1 b2 =
  case b1 of {
   Prelude.True -> Prelude.True;
   Prelude.False -> b2}

xorb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
xorb b1 b2 =
  case b1 of {
   Prelude.True ->
    case b2 of {
     Prelude.True -> Prelude.False;
     Prelude.False -> Prelude.True};
   Prelude.False -> b2}

negb :: Prelude.Bool -> Prelude.Bool
negb b =
  case b of {
   Prelude.True -> Prelude.False;
   Prelude.False -> Prelude.True}

nat_rect :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
nat_rect f f0 n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> f)
    (\n0 -> f0 n0 (nat_rect f f0 n0))
    n

nat_rec :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
nat_rec =
  nat_rect

data Option a =
   Some a
 | None
      deriving (Prelude.Show)

data Sum a b =
   Inl a
 | Inr b

fst :: ((,) a1 a2) -> a1
fst p =
  case p of {
   (,) x _ -> x}

snd :: ((,) a1 a2) -> a2
snd p =
  case p of {
   (,) _ y -> y}

length :: ([] a1) -> Prelude.Integer
length l =
  case l of {
   [] -> 0;
   (:) _ l' -> Prelude.succ (length l')}

app :: ([] a1) -> ([] a1) -> [] a1
app l m =
  case l of {
   [] -> m;
   (:) a l1 -> (:) a (app l1 m)}

data Comparison =
   Eq
 | Lt
 | Gt

compOpp :: Comparison -> Comparison
compOpp r =
  case r of {
   Eq -> Eq;
   Lt -> Gt;
   Gt -> Lt}

data CompareSpecT =
   CompEqT
 | CompLtT
 | CompGtT

compareSpec2Type :: Comparison -> CompareSpecT
compareSpec2Type c =
  case c of {
   Eq -> CompEqT;
   Lt -> CompLtT;
   Gt -> CompGtT}

type CompSpecT a = CompareSpecT

compSpec2Type :: a1 -> a1 -> Comparison -> CompSpecT a1
compSpec2Type _ _ =
  compareSpec2Type

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
sig_rect :: (a1 -> () -> a2) -> a1 -> a2
sig_rect f s =
  f s __

sig_rec :: (a1 -> () -> a2) -> a1 -> a2
sig_rec =
  sig_rect

data Sumbool =
   Left
 | Right

sumbool_rect :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rect f f0 s =
  case s of {
   Left -> f __;
   Right -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rec =
  sumbool_rect

data Uint =
   Nil
 | D0 Uint
 | D1 Uint
 | D2 Uint
 | D3 Uint
 | D4 Uint
 | D5 Uint
 | D6 Uint
 | D7 Uint
 | D8 Uint
 | D9 Uint

data Signed_int =
   Pos Uint
 | Neg Uint

nzhead :: Uint -> Uint
nzhead d =
  case d of {
   D0 d0 -> nzhead d0;
   _ -> d}

unorm :: Uint -> Uint
unorm d =
  case nzhead d of {
   Nil -> D0 Nil;
   x -> x}

norm :: Signed_int -> Signed_int
norm d =
  case d of {
   Pos d0 -> Pos (unorm d0);
   Neg d0 -> case nzhead d0 of {
              Nil -> Pos (D0 Nil);
              x -> Neg x}}

revapp :: Uint -> Uint -> Uint
revapp d d' =
  case d of {
   Nil -> d';
   D0 d0 -> revapp d0 (D0 d');
   D1 d0 -> revapp d0 (D1 d');
   D2 d0 -> revapp d0 (D2 d');
   D3 d0 -> revapp d0 (D3 d');
   D4 d0 -> revapp d0 (D4 d');
   D5 d0 -> revapp d0 (D5 d');
   D6 d0 -> revapp d0 (D6 d');
   D7 d0 -> revapp d0 (D7 d');
   D8 d0 -> revapp d0 (D8 d');
   D9 d0 -> revapp d0 (D9 d')}

rev :: Uint -> Uint
rev d =
  revapp d Nil

succ :: Uint -> Uint
succ d =
  case d of {
   Nil -> D1 Nil;
   D0 d0 -> D1 d0;
   D1 d0 -> D2 d0;
   D2 d0 -> D3 d0;
   D3 d0 -> D4 d0;
   D4 d0 -> D5 d0;
   D5 d0 -> D6 d0;
   D6 d0 -> D7 d0;
   D7 d0 -> D8 d0;
   D8 d0 -> D9 d0;
   D9 d0 -> D0 (succ d0)}

data Uint0 =
   Nil0
 | D10 Uint0
 | D11 Uint0
 | D12 Uint0
 | D13 Uint0
 | D14 Uint0
 | D15 Uint0
 | D16 Uint0
 | D17 Uint0
 | D18 Uint0
 | D19 Uint0
 | Da Uint0
 | Db Uint0
 | Dc Uint0
 | Dd Uint0
 | De Uint0
 | Df Uint0

data Signed_int0 =
   Pos0 Uint0
 | Neg0 Uint0

nzhead0 :: Uint0 -> Uint0
nzhead0 d =
  case d of {
   D10 d0 -> nzhead0 d0;
   _ -> d}

unorm0 :: Uint0 -> Uint0
unorm0 d =
  case nzhead0 d of {
   Nil0 -> D10 Nil0;
   x -> x}

norm0 :: Signed_int0 -> Signed_int0
norm0 d =
  case d of {
   Pos0 d0 -> Pos0 (unorm0 d0);
   Neg0 d0 -> case nzhead0 d0 of {
               Nil0 -> Pos0 (D10 Nil0);
               x -> Neg0 x}}

revapp0 :: Uint0 -> Uint0 -> Uint0
revapp0 d d' =
  case d of {
   Nil0 -> d';
   D10 d0 -> revapp0 d0 (D10 d');
   D11 d0 -> revapp0 d0 (D11 d');
   D12 d0 -> revapp0 d0 (D12 d');
   D13 d0 -> revapp0 d0 (D13 d');
   D14 d0 -> revapp0 d0 (D14 d');
   D15 d0 -> revapp0 d0 (D15 d');
   D16 d0 -> revapp0 d0 (D16 d');
   D17 d0 -> revapp0 d0 (D17 d');
   D18 d0 -> revapp0 d0 (D18 d');
   D19 d0 -> revapp0 d0 (D19 d');
   Da d0 -> revapp0 d0 (Da d');
   Db d0 -> revapp0 d0 (Db d');
   Dc d0 -> revapp0 d0 (Dc d');
   Dd d0 -> revapp0 d0 (Dd d');
   De d0 -> revapp0 d0 (De d');
   Df d0 -> revapp0 d0 (Df d')}

rev0 :: Uint0 -> Uint0
rev0 d =
  revapp0 d Nil0

succ0 :: Uint0 -> Uint0
succ0 d =
  case d of {
   Nil0 -> D11 Nil0;
   D10 d0 -> D11 d0;
   D11 d0 -> D12 d0;
   D12 d0 -> D13 d0;
   D13 d0 -> D14 d0;
   D14 d0 -> D15 d0;
   D15 d0 -> D16 d0;
   D16 d0 -> D17 d0;
   D17 d0 -> D18 d0;
   D18 d0 -> D19 d0;
   D19 d0 -> Da d0;
   Da d0 -> Db d0;
   Db d0 -> Dc d0;
   Dc d0 -> Dd d0;
   Dd d0 -> De d0;
   De d0 -> Df d0;
   Df d0 -> D10 (succ0 d0)}

data Uint1 =
   UIntDecimal Uint
 | UIntHexadecimal Uint0

data Signed_int1 =
   IntDecimal Signed_int
 | IntHexadecimal Signed_int0

add :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> m)
    (\p -> Prelude.succ (add p m))
    n

max :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
max n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> m)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> n)
      (\m' -> Prelude.succ (max n' m'))
      m)
    n

min :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
min n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> 0)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> 0)
      (\m' -> Prelude.succ (min n' m'))
      m)
    n

acc_rect :: (a1 -> () -> (a1 -> () -> a2) -> a2) -> a1 -> a2
acc_rect f x =
  f x __ (\y _ -> acc_rect f y)

type Decidable =
  Prelude.Bool
  -- singleton inductive, whose constructor was Build_Decidable
  
data Reflect =
   ReflectT
 | ReflectF

iff_reflect :: Prelude.Bool -> Reflect
iff_reflect b =
  case b of {
   Prelude.True -> and_rec (\_ _ -> ReflectT);
   Prelude.False -> and_rec (\_ _ -> ReflectF)}

add0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add0 n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> m)
    (\p -> Prelude.succ (add0 p m))
    n

mul :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
mul n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> 0)
    (\p -> add0 m (mul p m))
    n

sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> n)
    (\k ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> n)
      (\l -> sub k l)
      m)
    n

eqb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
eqb n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.True)
      (\_ -> Prelude.False)
      m)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.False)
      (\m' -> eqb n' m')
      m)
    n

compare :: Prelude.Integer -> Prelude.Integer -> Comparison
compare n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Eq)
      (\_ -> Lt)
      m)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Gt)
      (\m' -> compare n' m')
      m)
    n

max0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
max0 n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> m)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> n)
      (\m' -> Prelude.succ (max0 n' m'))
      m)
    n

min0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
min0 n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> 0)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> 0)
      (\m' -> Prelude.succ (min0 n' m'))
      m)
    n

even :: Prelude.Integer -> Prelude.Bool
even n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Prelude.True)
    (\n0 ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.False)
      (\n' -> even n')
      n0)
    n

divmod :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer ->
          Prelude.Integer -> (,) Prelude.Integer Prelude.Integer
divmod x y q u =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> (,) q u)
    (\x' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> divmod x' y (Prelude.succ q) y)
      (\u' -> divmod x' y q u')
      u)
    x

div :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
div x y =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> y)
    (\y' -> fst (divmod x y' 0 y'))
    y

modulo :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
modulo x y =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> x)
    (\y' -> sub y' (snd (divmod x y' 0 y')))
    y

gcd :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
gcd a b =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> b)
    (\a' -> gcd (modulo b (Prelude.succ a')) (Prelude.succ a'))
    a

eq_dec :: Prelude.Integer -> Prelude.Integer -> Sumbool
eq_dec n =
  nat_rec (\m ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Left)
      (\_ -> Right)
      m) (\_ iHn m ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Right)
      (\n0 -> iHn n0)
      m) n

type EvenT = Prelude.Integer

type OddT = Prelude.Integer

evenT_0 :: EvenT
evenT_0 =
  0

evenT_2 :: Prelude.Integer -> EvenT -> EvenT
evenT_2 _ h0 =
  Prelude.succ h0

oddT_1 :: OddT
oddT_1 =
  0

oddT_2 :: Prelude.Integer -> OddT -> OddT
oddT_2 _ h0 =
  Prelude.succ h0

evenT_S_OddT :: Prelude.Integer -> EvenT -> OddT
evenT_S_OddT n h =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> false_rec)
    (\n0 -> eq_rec_r (add0 n0 (Prelude.succ (add0 n0 0))) n0 n)
    h

oddT_S_EvenT :: Prelude.Integer -> OddT -> EvenT
oddT_S_EvenT n h =
  eq_rec_r (add0 h (add0 h 0)) (\_ -> h) n __

even_EvenT :: Prelude.Integer -> EvenT
even_EvenT n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> evenT_0)
    (\n0 ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> false_rec)
      (\n1 -> let {he = even_EvenT n1} in evenT_2 n1 he)
      n0)
    n

odd_OddT :: Prelude.Integer -> OddT
odd_OddT n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> false_rec)
    (\n0 ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> oddT_1)
      (\n1 -> let {he = odd_OddT n1} in oddT_2 n1 he)
      n0)
    n

even_EvenT0 :: Prelude.Integer -> EvenT
even_EvenT0 =
  even_EvenT

odd_OddT0 :: Prelude.Integer -> OddT
odd_OddT0 =
  odd_OddT

evenT_OddT_dec :: Prelude.Integer -> Sum EvenT OddT
evenT_OddT_dec n =
  case even n of {
   Prelude.True -> Inl (even_EvenT n);
   Prelude.False -> Inr (odd_OddT n)}

oddT_EvenT_rect :: (Prelude.Integer -> EvenT -> a2 -> a1) -> a2 ->
                   (Prelude.Integer -> OddT -> a1 -> a2) -> Prelude.Integer
                   -> OddT -> a1
oddT_EvenT_rect hQP hQ0 hPQ n0 h =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> false_rect)
      (\_ -> false_rect)
      h)
    (\n ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> hQP 0 evenT_0 hQ0)
      (\n1 ->
      let {hES = oddT_S_EvenT (Prelude.succ n1) h} in
      let {hO = evenT_S_OddT n1 hES} in
      hQP (Prelude.succ n1) hES
        (hPQ n1 hO (oddT_EvenT_rect hQP hQ0 hPQ n1 hO)))
      n)
    n0

evenT_OddT_rect :: (Prelude.Integer -> EvenT -> a2 -> a1) -> a2 ->
                   (Prelude.Integer -> OddT -> a1 -> a2) -> Prelude.Integer
                   -> EvenT -> a2
evenT_OddT_rect hQP hQ0 hPQ n0 hES =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> hQ0)
    (\n ->
    let {hO = evenT_S_OddT n hES} in
    hPQ n hO (oddT_EvenT_rect hQP hQ0 hPQ n hO))
    n0

data Positive =
   XI Positive
 | XO Positive
 | XH
    deriving (Prelude.Show)


data Z =
   Z0
 | Zpos Positive
 | Zneg Positive
      deriving (Prelude.Show)


succ1 :: Positive -> Positive
succ1 x =
  case x of {
   XI p -> XO (succ1 p);
   XO p -> XI p;
   XH -> XO XH}

add1 :: Positive -> Positive -> Positive
add1 x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add1 p q);
     XH -> XO (succ1 p)};
   XO p ->
    case y of {
     XI q -> XI (add1 p q);
     XO q -> XO (add1 p q);
     XH -> XI p};
   XH -> case y of {
          XI q -> XO (succ1 q);
          XO q -> XI q;
          XH -> XO XH}}

add_carry :: Positive -> Positive -> Positive
add_carry x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XI (add_carry p q);
     XO q -> XO (add_carry p q);
     XH -> XI (succ1 p)};
   XO p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add1 p q);
     XH -> XO (succ1 p)};
   XH -> case y of {
          XI q -> XI (succ1 q);
          XO q -> XO (succ1 q);
          XH -> XI XH}}

pred_double :: Positive -> Positive
pred_double x =
  case x of {
   XI p -> XI (XO p);
   XO p -> XI (pred_double p);
   XH -> XH}

compare_cont :: Comparison -> Positive -> Positive -> Comparison
compare_cont r x y =
  case x of {
   XI p ->
    case y of {
     XI q -> compare_cont r p q;
     XO q -> compare_cont Gt p q;
     XH -> Gt};
   XO p ->
    case y of {
     XI q -> compare_cont Lt p q;
     XO q -> compare_cont r p q;
     XH -> Gt};
   XH -> case y of {
          XH -> r;
          _ -> Lt}}

compare0 :: Positive -> Positive -> Comparison
compare0 =
  compare_cont Eq

map :: (a1 -> a2) -> ([] a1) -> [] a2
map f l =
  case l of {
   [] -> [];
   (:) a t -> (:) (f a) (map f t)}

fold_right :: (a2 -> a1 -> a1) -> a1 -> ([] a2) -> a1
fold_right f a0 l =
  case l of {
   [] -> a0;
   (:) b t -> f b (fold_right f a0 t)}

filter :: (a1 -> Prelude.Bool) -> ([] a1) -> [] a1
filter f l =
  case l of {
   [] -> [];
   (:) x l0 ->
    case f x of {
     Prelude.True -> (:) x (filter f l0);
     Prelude.False -> filter f l0}}

double :: Z -> Z
double x =
  case x of {
   Z0 -> Z0;
   Zpos p -> Zpos (XO p);
   Zneg p -> Zneg (XO p)}

succ_double :: Z -> Z
succ_double x =
  case x of {
   Z0 -> Zpos XH;
   Zpos p -> Zpos (XI p);
   Zneg p -> Zneg (pred_double p)}

pred_double0 :: Z -> Z
pred_double0 x =
  case x of {
   Z0 -> Zneg XH;
   Zpos p -> Zpos (pred_double p);
   Zneg p -> Zneg (XI p)}

pos_sub :: Positive -> Positive -> Z
pos_sub x y =
  case x of {
   XI p ->
    case y of {
     XI q -> double (pos_sub p q);
     XO q -> succ_double (pos_sub p q);
     XH -> Zpos (XO p)};
   XO p ->
    case y of {
     XI q -> pred_double0 (pos_sub p q);
     XO q -> double (pos_sub p q);
     XH -> Zpos (pred_double p)};
   XH ->
    case y of {
     XI q -> Zneg (XO q);
     XO q -> Zneg (pred_double q);
     XH -> Z0}}

add2 :: Z -> Z -> Z
add2 x y =
  case x of {
   Z0 -> y;
   Zpos x' ->
    case y of {
     Z0 -> x;
     Zpos y' -> Zpos (add1 x' y');
     Zneg y' -> pos_sub x' y'};
   Zneg x' ->
    case y of {
     Z0 -> x;
     Zpos y' -> pos_sub y' x';
     Zneg y' -> Zneg (add1 x' y')}}

compare1 :: Z -> Z -> Comparison
compare1 x y =
  case x of {
   Z0 -> case y of {
          Z0 -> Eq;
          Zpos _ -> Lt;
          Zneg _ -> Gt};
   Zpos x' -> case y of {
               Zpos y' -> compare0 x' y';
               _ -> Gt};
   Zneg x' -> case y of {
               Zneg y' -> compOpp (compare0 x' y');
               _ -> Lt}}

ltb :: Z -> Z -> Prelude.Bool
ltb x y =
  case compare1 x y of {
   Lt -> Prelude.True;
   _ -> Prelude.False}

max1 :: Z -> Z -> Z
max1 n m =
  case compare1 n m of {
   Lt -> m;
   _ -> n}

data Compare x =
   LT
 | EQ
 | GT

compare_rect :: a1 -> a1 -> (() -> a2) -> (() -> a2) -> (() -> a2) ->
                (Compare a1) -> a2
compare_rect _ _ f f0 f1 c =
  case c of {
   LT -> f __;
   EQ -> f0 __;
   GT -> f1 __}

compare_rec :: a1 -> a1 -> (() -> a2) -> (() -> a2) -> (() -> a2) -> (Compare
               a1) -> a2
compare_rec =
  compare_rect

type T = Prelude.Integer

compare2 :: Prelude.Integer -> Prelude.Integer -> Compare Prelude.Integer
compare2 x y =
  case compare x y of {
   Eq -> EQ;
   Lt -> LT;
   Gt -> GT}

eq_dec0 :: Prelude.Integer -> Prelude.Integer -> Sumbool
eq_dec0 =
  eq_dec

type T0 = Z

_0 :: Z
_0 =
  Z0

_1 :: Z
_1 =
  Zpos XH

_2 :: Z
_2 =
  Zpos (XO XH)

add3 :: Z -> Z -> Z
add3 =
  add2

max2 :: Z -> Z -> Z
max2 =
  max1

gt_le_dec :: Z -> Z -> Sumbool
gt_le_dec i j =
  let {b = ltb j i} in
  case b of {
   Prelude.True -> Left;
   Prelude.False -> Right}

ge_lt_dec :: Z -> Z -> Sumbool
ge_lt_dec i j =
  let {b = ltb i j} in
  case b of {
   Prelude.True -> Right;
   Prelude.False -> Left}

type Node = T

type T1 = Prelude.Integer

compare3 :: Prelude.Integer -> Prelude.Integer -> Compare Prelude.Integer
compare3 x y =
  case compare x y of {
   Eq -> EQ;
   Lt -> LT;
   Gt -> GT}

eq_dec1 :: Prelude.Integer -> Prelude.Integer -> Sumbool
eq_dec1 =
  eq_dec

type Key = Prelude.Integer

data Tree elt =
   Leaf
 | Node0 (Tree elt) Key elt (Tree elt) T0
     deriving (Prelude.Show)


tree_rect :: a2 -> ((Tree a1) -> a2 -> Key -> a1 -> (Tree a1) -> a2 -> T0 ->
             a2) -> (Tree a1) -> a2
tree_rect f f0 t =
  case t of {
   Leaf -> f;
   Node0 t0 k y t1 t2 ->
    f0 t0 (tree_rect f f0 t0) k y t1 (tree_rect f f0 t1) t2}

tree_rec :: a2 -> ((Tree a1) -> a2 -> Key -> a1 -> (Tree a1) -> a2 -> T0 ->
            a2) -> (Tree a1) -> a2
tree_rec =
  tree_rect

height :: (Tree a1) -> T0
height m =
  case m of {
   Leaf -> _0;
   Node0 _ _ _ _ h -> h}

cardinal :: (Tree a1) -> Prelude.Integer
cardinal m =
  case m of {
   Leaf -> 0;
   Node0 l _ _ r _ -> Prelude.succ (add (cardinal l) (cardinal r))}

empty :: Tree a1
empty =
  Leaf

is_empty :: (Tree a1) -> Prelude.Bool
is_empty m =
  case m of {
   Leaf -> Prelude.True;
   Node0 _ _ _ _ _ -> Prelude.False}

mem :: Prelude.Integer -> (Tree a1) -> Prelude.Bool
mem x m =
  case m of {
   Leaf -> Prelude.False;
   Node0 l y _ r _ ->
    case compare2 x y of {
     LT -> mem x l;
     EQ -> Prelude.True;
     GT -> mem x r}}

find :: Prelude.Integer -> (Tree a1) -> Option a1
find x m =
  case m of {
   Leaf -> None;
   Node0 l y d r _ ->
    case compare2 x y of {
     LT -> find x l;
     EQ -> Some d;
     GT -> find x r}}

create :: (Tree a1) -> Key -> a1 -> (Tree a1) -> Tree a1
create l x e r =
  Node0 l x e r (add3 (max2 (height l) (height r)) _1)

assert_false :: (Tree a1) -> Key -> a1 -> (Tree a1) -> Tree a1
assert_false =
  create

bal :: (Tree a1) -> Key -> a1 -> (Tree a1) -> Tree a1
bal l x d r =
  let {hl = height l} in
  let {hr = height r} in
  case gt_le_dec hl (add3 hr _2) of {
   Left ->
    case l of {
     Leaf -> assert_false l x d r;
     Node0 ll lx ld lr _ ->
      case ge_lt_dec (height ll) (height lr) of {
       Left -> create ll lx ld (create lr x d r);
       Right ->
        case lr of {
         Leaf -> assert_false l x d r;
         Node0 lrl lrx lrd lrr _ ->
          create (create ll lx ld lrl) lrx lrd (create lrr x d r)}}};
   Right ->
    case gt_le_dec hr (add3 hl _2) of {
     Left ->
      case r of {
       Leaf -> assert_false l x d r;
       Node0 rl rx rd rr _ ->
        case ge_lt_dec (height rr) (height rl) of {
         Left -> create (create l x d rl) rx rd rr;
         Right ->
          case rl of {
           Leaf -> assert_false l x d r;
           Node0 rll rlx rld rlr _ ->
            create (create l x d rll) rlx rld (create rlr rx rd rr)}}};
     Right -> create l x d r}}

add4 :: Key -> a1 -> (Tree a1) -> Tree a1
add4 x d m =
  case m of {
   Leaf -> Node0 Leaf x d Leaf _1;
   Node0 l y d' r h ->
    case compare2 x y of {
     LT -> bal (add4 x d l) y d' r;
     EQ -> Node0 l y d r h;
     GT -> bal l y d' (add4 x d r)}}

remove_min :: (Tree a1) -> Key -> a1 -> (Tree a1) -> (,) (Tree a1)
              ((,) Key a1)
remove_min l x d r =
  case l of {
   Leaf -> (,) r ((,) x d);
   Node0 ll lx ld lr _ ->
    case remove_min ll lx ld lr of {
     (,) l' m -> (,) (bal l' x d r) m}}

merge :: (Tree a1) -> (Tree a1) -> Tree a1
merge s1 s2 =
  case s1 of {
   Leaf -> s2;
   Node0 _ _ _ _ _ ->
    case s2 of {
     Leaf -> s1;
     Node0 l2 x2 d2 r2 _ ->
      case remove_min l2 x2 d2 r2 of {
       (,) s2' p -> case p of {
                     (,) x d -> bal s1 x d s2'}}}}

remove :: Prelude.Integer -> (Tree a1) -> Tree a1
remove x m =
  case m of {
   Leaf -> Leaf;
   Node0 l y d r _ ->
    case compare2 x y of {
     LT -> bal (remove x l) y d r;
     EQ -> merge l r;
     GT -> bal l y d (remove x r)}}

join :: (Tree a1) -> Key -> a1 -> (Tree a1) -> Tree a1
join l =
  case l of {
   Leaf -> add4;
   Node0 ll lx ld lr lh -> (\x d ->
    let {
     join_aux r =
       case r of {
        Leaf -> add4 x d l;
        Node0 rl rx rd rr rh ->
         case gt_le_dec lh (add3 rh _2) of {
          Left -> bal ll lx ld (join lr x d r);
          Right ->
           case gt_le_dec rh (add3 lh _2) of {
            Left -> bal (join_aux rl) rx rd rr;
            Right -> create l x d r}}}}
    in join_aux)}

data Triple elt =
   Mktriple (Tree elt) (Option elt) (Tree elt)

t_left :: (Triple a1) -> Tree a1
t_left t =
  case t of {
   Mktriple t_left0 _ _ -> t_left0}

t_opt :: (Triple a1) -> Option a1
t_opt t =
  case t of {
   Mktriple _ t_opt0 _ -> t_opt0}

t_right :: (Triple a1) -> Tree a1
t_right t =
  case t of {
   Mktriple _ _ t_right0 -> t_right0}

split :: Prelude.Integer -> (Tree a1) -> Triple a1
split x m =
  case m of {
   Leaf -> Mktriple Leaf None Leaf;
   Node0 l y d r _ ->
    case compare2 x y of {
     LT ->
      case split x l of {
       Mktriple ll o rl -> Mktriple ll o (join rl y d r)};
     EQ -> Mktriple l (Some d) r;
     GT ->
      case split x r of {
       Mktriple rl o rr -> Mktriple (join l y d rl) o rr}}}

concat :: (Tree a1) -> (Tree a1) -> Tree a1
concat m1 m2 =
  case m1 of {
   Leaf -> m2;
   Node0 _ _ _ _ _ ->
    case m2 of {
     Leaf -> m1;
     Node0 l2 x2 d2 r2 _ ->
      case remove_min l2 x2 d2 r2 of {
       (,) m2' xd -> join m1 (fst xd) (snd xd) m2'}}}

elements_aux :: ([] ((,) Key a1)) -> (Tree a1) -> [] ((,) Key a1)
elements_aux acc m =
  case m of {
   Leaf -> acc;
   Node0 l x d r _ -> elements_aux ((:) ((,) x d) (elements_aux acc r)) l}

elements :: (Tree a1) -> [] ((,) Key a1)
elements =
  elements_aux []

fold :: (Key -> a1 -> a2 -> a2) -> (Tree a1) -> a2 -> a2
fold f m a =
  case m of {
   Leaf -> a;
   Node0 l x d r _ -> fold f r (f x d (fold f l a))}

data Enumeration elt =
   End
 | More Key elt (Tree elt) (Enumeration elt)

enumeration_rect :: a2 -> (Key -> a1 -> (Tree a1) -> (Enumeration a1) -> a2
                    -> a2) -> (Enumeration a1) -> a2
enumeration_rect f f0 e =
  case e of {
   End -> f;
   More k e0 t e1 -> f0 k e0 t e1 (enumeration_rect f f0 e1)}

enumeration_rec :: a2 -> (Key -> a1 -> (Tree a1) -> (Enumeration a1) -> a2 ->
                   a2) -> (Enumeration a1) -> a2
enumeration_rec =
  enumeration_rect

cons :: (Tree a1) -> (Enumeration a1) -> Enumeration a1
cons m e =
  case m of {
   Leaf -> e;
   Node0 l x d r _ -> cons l (More x d r e)}

equal_more :: (a1 -> a1 -> Prelude.Bool) -> Prelude.Integer -> a1 ->
              ((Enumeration a1) -> Prelude.Bool) -> (Enumeration a1) ->
              Prelude.Bool
equal_more cmp x1 d1 cont e2 =
  case e2 of {
   End -> Prelude.False;
   More x2 d2 r2 e3 ->
    case compare2 x1 x2 of {
     EQ ->
      case cmp d1 d2 of {
       Prelude.True -> cont (cons r2 e3);
       Prelude.False -> Prelude.False};
     _ -> Prelude.False}}

equal_cont :: (a1 -> a1 -> Prelude.Bool) -> (Tree a1) -> ((Enumeration 
              a1) -> Prelude.Bool) -> (Enumeration a1) -> Prelude.Bool
equal_cont cmp m1 cont e2 =
  case m1 of {
   Leaf -> cont e2;
   Node0 l1 x1 d1 r1 _ ->
    equal_cont cmp l1 (equal_more cmp x1 d1 (equal_cont cmp r1 cont)) e2}

equal_end :: (Enumeration a1) -> Prelude.Bool
equal_end e2 =
  case e2 of {
   End -> Prelude.True;
   More _ _ _ _ -> Prelude.False}

equal :: (a1 -> a1 -> Prelude.Bool) -> (Tree a1) -> (Tree a1) -> Prelude.Bool
equal cmp m1 m2 =
  equal_cont cmp m1 equal_end (cons m2 End)

map0 :: (a1 -> a2) -> (Tree a1) -> Tree a2
map0 f m =
  case m of {
   Leaf -> Leaf;
   Node0 l x d r h -> Node0 (map0 f l) x (f d) (map0 f r) h}

mapi :: (Key -> a1 -> a2) -> (Tree a1) -> Tree a2
mapi f m =
  case m of {
   Leaf -> Leaf;
   Node0 l x d r h -> Node0 (mapi f l) x (f x d) (mapi f r) h}

map_option :: (Key -> a1 -> Option a2) -> (Tree a1) -> Tree a2
map_option f m =
  case m of {
   Leaf -> Leaf;
   Node0 l x d r _ ->
    case f x d of {
     Some d' -> join (map_option f l) x d' (map_option f r);
     None -> concat (map_option f l) (map_option f r)}}

map2_opt :: (Key -> a1 -> (Option a2) -> Option a3) -> ((Tree a1) -> Tree 
            a3) -> ((Tree a2) -> Tree a3) -> (Tree a1) -> (Tree a2) -> Tree
            a3
map2_opt f mapl mapr m1 m2 =
  case m1 of {
   Leaf -> mapr m2;
   Node0 l1 x1 d1 r1 _ ->
    case m2 of {
     Leaf -> mapl m1;
     Node0 _ _ _ _ _ ->
      case split x1 m2 of {
       Mktriple l2' o2 r2' ->
        case f x1 d1 o2 of {
         Some e ->
          join (map2_opt f mapl mapr l1 l2') x1 e
            (map2_opt f mapl mapr r1 r2');
         None ->
          concat (map2_opt f mapl mapr l1 l2') (map2_opt f mapl mapr r1 r2')}}}}

map2 :: ((Option a1) -> (Option a2) -> Option a3) -> (Tree a1) -> (Tree 
        a2) -> Tree a3
map2 f =
  map2_opt (\_ d o -> f (Some d) o) (map_option (\_ d -> f (Some d) None))
    (map_option (\_ d' -> f None (Some d')))

type T2 = Prelude.Integer

eq_dec2 :: Prelude.Integer -> Prelude.Integer -> Sumbool
eq_dec2 =
  eq_dec0

lt_dec :: Prelude.Integer -> Prelude.Integer -> Sumbool
lt_dec x y =
  compare_rec x y (\_ -> Left) (\_ -> Right) (\_ -> Right) (compare2 x y)

eqb0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
eqb0 x y =
  case eq_dec2 x y of {
   Left -> Prelude.True;
   Right -> Prelude.False}

type T3 = Prelude.Integer

eq_dec3 :: Prelude.Integer -> Prelude.Integer -> Sumbool
eq_dec3 =
  eq_dec0

lt_dec0 :: Prelude.Integer -> Prelude.Integer -> Sumbool
lt_dec0 x y =
  compare_rec x y (\_ -> Left) (\_ -> Right) (\_ -> Right) (compare2 x y)

eqb1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
eqb1 x y =
  case eq_dec3 x y of {
   Left -> Prelude.True;
   Right -> Prelude.False}

type T4 = Prelude.Integer

eq_dec4 :: Prelude.Integer -> Prelude.Integer -> Sumbool
eq_dec4 =
  eq_dec0

lt_dec1 :: Prelude.Integer -> Prelude.Integer -> Sumbool
lt_dec1 x y =
  compare_rec x y (\_ -> Left) (\_ -> Right) (\_ -> Right) (compare2 x y)

eqb2 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
eqb2 x y =
  case eq_dec4 x y of {
   Left -> Prelude.True;
   Right -> Prelude.False}

type T5 = Prelude.Integer

eq_dec5 :: Prelude.Integer -> Prelude.Integer -> Sumbool
eq_dec5 =
  eq_dec0

lt_dec2 :: Prelude.Integer -> Prelude.Integer -> Sumbool
lt_dec2 x y =
  compare_rec x y (\_ -> Left) (\_ -> Right) (\_ -> Right) (compare2 x y)

eqb3 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
eqb3 x y =
  case eq_dec5 x y of {
   Left -> Prelude.True;
   Right -> Prelude.False}

type Key0 = Prelude.Integer

type T6 elt = [] ((,) Prelude.Integer elt)

empty0 :: T6 a1
empty0 =
  []

is_empty0 :: (T6 a1) -> Prelude.Bool
is_empty0 l =
  case l of {
   [] -> Prelude.True;
   (:) _ _ -> Prelude.False}

mem0 :: Key0 -> (T6 a1) -> Prelude.Bool
mem0 k s =
  case s of {
   [] -> Prelude.False;
   (:) p l ->
    case p of {
     (,) k' _ ->
      case compare2 k k' of {
       LT -> Prelude.False;
       EQ -> Prelude.True;
       GT -> mem0 k l}}}

find0 :: Key0 -> (T6 a1) -> Option a1
find0 k s =
  case s of {
   [] -> None;
   (:) p s' ->
    case p of {
     (,) k' x ->
      case compare2 k k' of {
       LT -> None;
       EQ -> Some x;
       GT -> find0 k s'}}}

add5 :: Key0 -> a1 -> (T6 a1) -> T6 a1
add5 k x s =
  case s of {
   [] -> (:) ((,) k x) [];
   (:) p l ->
    case p of {
     (,) k' y ->
      case compare2 k k' of {
       LT -> (:) ((,) k x) s;
       EQ -> (:) ((,) k x) l;
       GT -> (:) ((,) k' y) (add5 k x l)}}}

remove0 :: Key0 -> (T6 a1) -> T6 a1
remove0 k s =
  case s of {
   [] -> [];
   (:) p l ->
    case p of {
     (,) k' x ->
      case compare2 k k' of {
       LT -> s;
       EQ -> l;
       GT -> (:) ((,) k' x) (remove0 k l)}}}

elements0 :: (T6 a1) -> T6 a1
elements0 m =
  m

fold0 :: (Key0 -> a1 -> a2 -> a2) -> (T6 a1) -> a2 -> a2
fold0 f m acc =
  case m of {
   [] -> acc;
   (:) p m' -> case p of {
                (,) k e -> fold0 f m' (f k e acc)}}

equal0 :: (a1 -> a1 -> Prelude.Bool) -> (T6 a1) -> (T6 a1) -> Prelude.Bool
equal0 cmp m m' =
  case m of {
   [] -> case m' of {
          [] -> Prelude.True;
          (:) _ _ -> Prelude.False};
   (:) p l ->
    case p of {
     (,) x e ->
      case m' of {
       [] -> Prelude.False;
       (:) p0 l' ->
        case p0 of {
         (,) x' e' ->
          case compare2 x x' of {
           EQ -> andb (cmp e e') (equal0 cmp l l');
           _ -> Prelude.False}}}}}

map1 :: (a1 -> a2) -> (T6 a1) -> T6 a2
map1 f m =
  case m of {
   [] -> [];
   (:) p m' -> case p of {
                (,) k e -> (:) ((,) k (f e)) (map1 f m')}}

mapi0 :: (Key0 -> a1 -> a2) -> (T6 a1) -> T6 a2
mapi0 f m =
  case m of {
   [] -> [];
   (:) p m' -> case p of {
                (,) k e -> (:) ((,) k (f k e)) (mapi0 f m')}}

option_cons :: Key0 -> (Option a1) -> ([] ((,) Key0 a1)) -> [] ((,) Key0 a1)
option_cons k o l =
  case o of {
   Some e -> (:) ((,) k e) l;
   None -> l}

map2_l :: ((Option a1) -> (Option a2) -> Option a3) -> (T6 a1) -> T6 a3
map2_l f m =
  case m of {
   [] -> [];
   (:) p l ->
    case p of {
     (,) k e -> option_cons k (f (Some e) None) (map2_l f l)}}

map2_r :: ((Option a1) -> (Option a2) -> Option a3) -> (T6 a2) -> T6 a3
map2_r f m' =
  case m' of {
   [] -> [];
   (:) p l' ->
    case p of {
     (,) k e' -> option_cons k (f None (Some e')) (map2_r f l')}}

map3 :: ((Option a1) -> (Option a2) -> Option a3) -> (T6 a1) -> (T6 a2) -> T6
        a3
map3 f m =
  case m of {
   [] -> map2_r f;
   (:) p l ->
    case p of {
     (,) k e ->
      let {
       map2_aux m' =
         case m' of {
          [] -> map2_l f m;
          (:) p0 l' ->
           case p0 of {
            (,) k' e' ->
             case compare2 k k' of {
              LT -> option_cons k (f (Some e) None) (map3 f l m');
              EQ -> option_cons k (f (Some e) (Some e')) (map3 f l l');
              GT -> option_cons k' (f None (Some e')) (map2_aux l')}}}}
      in map2_aux}}

combine :: (T6 a1) -> (T6 a2) -> T6 ((,) (Option a1) (Option a2))
combine m =
  case m of {
   [] -> map1 (\e' -> (,) None (Some e'));
   (:) p l ->
    case p of {
     (,) k e ->
      let {
       combine_aux m' =
         case m' of {
          [] -> map1 (\e0 -> (,) (Some e0) None) m;
          (:) p0 l' ->
           case p0 of {
            (,) k' e' ->
             case compare2 k k' of {
              LT -> (:) ((,) k ((,) (Some e) None)) (combine l m');
              EQ -> (:) ((,) k ((,) (Some e) (Some e'))) (combine l l');
              GT -> (:) ((,) k' ((,) None (Some e'))) (combine_aux l')}}}}
      in combine_aux}}

fold_right_pair :: (a1 -> a2 -> a3 -> a3) -> ([] ((,) a1 a2)) -> a3 -> a3
fold_right_pair f l i =
  fold_right (\p -> f (fst p) (snd p)) i l

map2_alt :: ((Option a1) -> (Option a2) -> Option a3) -> (T6 a1) -> (T6 
            a2) -> [] ((,) Key0 a3)
map2_alt f m m' =
  let {m0 = combine m m'} in
  let {m1 = map1 (\p -> f (fst p) (snd p)) m0} in
  fold_right_pair option_cons m1 []

at_least_one :: (Option a1) -> (Option a2) -> Option
                ((,) (Option a1) (Option a2))
at_least_one o o' =
  case o of {
   Some _ -> Some ((,) o o');
   None -> case o' of {
            Some _ -> Some ((,) o o');
            None -> None}}

at_least_one_then_f :: ((Option a1) -> (Option a2) -> Option a3) -> (Option
                       a1) -> (Option a2) -> Option a3
at_least_one_then_f f o o' =
  case o of {
   Some _ -> f o o';
   None -> case o' of {
            Some _ -> f o o';
            None -> None}}

data R_mem elt =
   R_mem_0 (Tree elt)
 | R_mem_1 (Tree elt) (Tree elt) Key elt (Tree elt) T0 Prelude.Bool (R_mem
                                                                    elt)
 | R_mem_2 (Tree elt) (Tree elt) Key elt (Tree elt) T0
 | R_mem_3 (Tree elt) (Tree elt) Key elt (Tree elt) T0 Prelude.Bool (R_mem
                                                                    elt)

r_mem_rect :: Prelude.Integer -> ((Tree a1) -> () -> a2) -> ((Tree a1) ->
              (Tree a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> () -> () ->
              Prelude.Bool -> (R_mem a1) -> a2 -> a2) -> ((Tree a1) -> (Tree
              a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> () -> () -> a2) ->
              ((Tree a1) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T0 -> ()
              -> () -> () -> Prelude.Bool -> (R_mem a1) -> a2 -> a2) -> (Tree
              a1) -> Prelude.Bool -> (R_mem a1) -> a2
r_mem_rect x f f0 f1 f2 _ _ r =
  case r of {
   R_mem_0 m -> f m __;
   R_mem_1 m l y _x r0 _x0 _res r1 ->
    f0 m l y _x r0 _x0 __ __ __ _res r1 (r_mem_rect x f f0 f1 f2 l _res r1);
   R_mem_2 m l y _x r0 _x0 -> f1 m l y _x r0 _x0 __ __ __;
   R_mem_3 m l y _x r0 _x0 _res r1 ->
    f2 m l y _x r0 _x0 __ __ __ _res r1 (r_mem_rect x f f0 f1 f2 r0 _res r1)}

r_mem_rec :: Prelude.Integer -> ((Tree a1) -> () -> a2) -> ((Tree a1) ->
             (Tree a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> () -> () ->
             Prelude.Bool -> (R_mem a1) -> a2 -> a2) -> ((Tree a1) -> (Tree
             a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> () -> () -> a2) ->
             ((Tree a1) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T0 -> () ->
             () -> () -> Prelude.Bool -> (R_mem a1) -> a2 -> a2) -> (Tree 
             a1) -> Prelude.Bool -> (R_mem a1) -> a2
r_mem_rec =
  r_mem_rect

data R_find elt =
   R_find_0 (Tree elt)
 | R_find_1 (Tree elt) (Tree elt) Key elt (Tree elt) T0 (Option elt) 
 (R_find elt)
 | R_find_2 (Tree elt) (Tree elt) Key elt (Tree elt) T0
 | R_find_3 (Tree elt) (Tree elt) Key elt (Tree elt) T0 (Option elt) 
 (R_find elt)

r_find_rect :: Prelude.Integer -> ((Tree a1) -> () -> a2) -> ((Tree a1) ->
               (Tree a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> () -> () ->
               (Option a1) -> (R_find a1) -> a2 -> a2) -> ((Tree a1) -> (Tree
               a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> () -> () -> a2)
               -> ((Tree a1) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T0 ->
               () -> () -> () -> (Option a1) -> (R_find a1) -> a2 -> a2) ->
               (Tree a1) -> (Option a1) -> (R_find a1) -> a2
r_find_rect x f f0 f1 f2 _ _ r =
  case r of {
   R_find_0 m -> f m __;
   R_find_1 m l y d r0 _x _res r1 ->
    f0 m l y d r0 _x __ __ __ _res r1 (r_find_rect x f f0 f1 f2 l _res r1);
   R_find_2 m l y d r0 _x -> f1 m l y d r0 _x __ __ __;
   R_find_3 m l y d r0 _x _res r1 ->
    f2 m l y d r0 _x __ __ __ _res r1 (r_find_rect x f f0 f1 f2 r0 _res r1)}

r_find_rec :: Prelude.Integer -> ((Tree a1) -> () -> a2) -> ((Tree a1) ->
              (Tree a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> () -> () ->
              (Option a1) -> (R_find a1) -> a2 -> a2) -> ((Tree a1) -> (Tree
              a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> () -> () -> a2) ->
              ((Tree a1) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T0 -> ()
              -> () -> () -> (Option a1) -> (R_find a1) -> a2 -> a2) -> (Tree
              a1) -> (Option a1) -> (R_find a1) -> a2
r_find_rec =
  r_find_rect

data R_bal elt =
   R_bal_0 (Tree elt) Key elt (Tree elt)
 | R_bal_1 (Tree elt) Key elt (Tree elt) (Tree elt) Key elt (Tree elt) 
 T0
 | R_bal_2 (Tree elt) Key elt (Tree elt) (Tree elt) Key elt (Tree elt) 
 T0
 | R_bal_3 (Tree elt) Key elt (Tree elt) (Tree elt) Key elt (Tree elt) 
 T0 (Tree elt) Key elt (Tree elt) T0
 | R_bal_4 (Tree elt) Key elt (Tree elt)
 | R_bal_5 (Tree elt) Key elt (Tree elt) (Tree elt) Key elt (Tree elt) 
 T0
 | R_bal_6 (Tree elt) Key elt (Tree elt) (Tree elt) Key elt (Tree elt) 
 T0
 | R_bal_7 (Tree elt) Key elt (Tree elt) (Tree elt) Key elt (Tree elt) 
 T0 (Tree elt) Key elt (Tree elt) T0
 | R_bal_8 (Tree elt) Key elt (Tree elt)

r_bal_rect :: ((Tree a1) -> Key -> a1 -> (Tree a1) -> () -> () -> () -> a2)
              -> ((Tree a1) -> Key -> a1 -> (Tree a1) -> () -> () -> (Tree
              a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> () -> () -> a2) ->
              ((Tree a1) -> Key -> a1 -> (Tree a1) -> () -> () -> (Tree 
              a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> () -> () -> () ->
              a2) -> ((Tree a1) -> Key -> a1 -> (Tree a1) -> () -> () ->
              (Tree a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> () -> () ->
              (Tree a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> a2) ->
              ((Tree a1) -> Key -> a1 -> (Tree a1) -> () -> () -> () -> () ->
              () -> a2) -> ((Tree a1) -> Key -> a1 -> (Tree a1) -> () -> ()
              -> () -> () -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T0 -> ()
              -> () -> () -> a2) -> ((Tree a1) -> Key -> a1 -> (Tree 
              a1) -> () -> () -> () -> () -> (Tree a1) -> Key -> a1 -> (Tree
              a1) -> T0 -> () -> () -> () -> () -> a2) -> ((Tree a1) -> Key
              -> a1 -> (Tree a1) -> () -> () -> () -> () -> (Tree a1) -> Key
              -> a1 -> (Tree a1) -> T0 -> () -> () -> () -> (Tree a1) -> Key
              -> a1 -> (Tree a1) -> T0 -> () -> a2) -> ((Tree a1) -> Key ->
              a1 -> (Tree a1) -> () -> () -> () -> () -> a2) -> (Tree 
              a1) -> Key -> a1 -> (Tree a1) -> (Tree a1) -> (R_bal a1) -> a2
r_bal_rect f f0 f1 f2 f3 f4 f5 f6 f7 _ _ _ _ _ r0 =
  case r0 of {
   R_bal_0 l x d r -> f l x d r __ __ __;
   R_bal_1 l x d r x0 x1 x2 x3 x4 -> f0 l x d r __ __ x0 x1 x2 x3 x4 __ __ __;
   R_bal_2 l x d r x0 x1 x2 x3 x4 ->
    f1 l x d r __ __ x0 x1 x2 x3 x4 __ __ __ __;
   R_bal_3 l x d r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 ->
    f2 l x d r __ __ x0 x1 x2 x3 x4 __ __ __ x5 x6 x7 x8 x9 __;
   R_bal_4 l x d r -> f3 l x d r __ __ __ __ __;
   R_bal_5 l x d r x0 x1 x2 x3 x4 ->
    f4 l x d r __ __ __ __ x0 x1 x2 x3 x4 __ __ __;
   R_bal_6 l x d r x0 x1 x2 x3 x4 ->
    f5 l x d r __ __ __ __ x0 x1 x2 x3 x4 __ __ __ __;
   R_bal_7 l x d r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 ->
    f6 l x d r __ __ __ __ x0 x1 x2 x3 x4 __ __ __ x5 x6 x7 x8 x9 __;
   R_bal_8 l x d r -> f7 l x d r __ __ __ __}

r_bal_rec :: ((Tree a1) -> Key -> a1 -> (Tree a1) -> () -> () -> () -> a2) ->
             ((Tree a1) -> Key -> a1 -> (Tree a1) -> () -> () -> (Tree 
             a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> () -> () -> a2) ->
             ((Tree a1) -> Key -> a1 -> (Tree a1) -> () -> () -> (Tree 
             a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> () -> () -> () ->
             a2) -> ((Tree a1) -> Key -> a1 -> (Tree a1) -> () -> () -> (Tree
             a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> () -> () -> (Tree
             a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> a2) -> ((Tree 
             a1) -> Key -> a1 -> (Tree a1) -> () -> () -> () -> () -> () ->
             a2) -> ((Tree a1) -> Key -> a1 -> (Tree a1) -> () -> () -> () ->
             () -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> () ->
             () -> a2) -> ((Tree a1) -> Key -> a1 -> (Tree a1) -> () -> () ->
             () -> () -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T0 -> () ->
             () -> () -> () -> a2) -> ((Tree a1) -> Key -> a1 -> (Tree 
             a1) -> () -> () -> () -> () -> (Tree a1) -> Key -> a1 -> (Tree
             a1) -> T0 -> () -> () -> () -> (Tree a1) -> Key -> a1 -> (Tree
             a1) -> T0 -> () -> a2) -> ((Tree a1) -> Key -> a1 -> (Tree 
             a1) -> () -> () -> () -> () -> a2) -> (Tree a1) -> Key -> a1 ->
             (Tree a1) -> (Tree a1) -> (R_bal a1) -> a2
r_bal_rec =
  r_bal_rect

data R_add elt =
   R_add_0 (Tree elt)
 | R_add_1 (Tree elt) (Tree elt) Key elt (Tree elt) T0 (Tree elt) (R_add elt)
 | R_add_2 (Tree elt) (Tree elt) Key elt (Tree elt) T0
 | R_add_3 (Tree elt) (Tree elt) Key elt (Tree elt) T0 (Tree elt) (R_add elt)

r_add_rect :: Key -> a1 -> ((Tree a1) -> () -> a2) -> ((Tree a1) -> (Tree 
              a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> () -> () -> (Tree
              a1) -> (R_add a1) -> a2 -> a2) -> ((Tree a1) -> (Tree a1) ->
              Key -> a1 -> (Tree a1) -> T0 -> () -> () -> () -> a2) -> ((Tree
              a1) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> () ->
              () -> (Tree a1) -> (R_add a1) -> a2 -> a2) -> (Tree a1) ->
              (Tree a1) -> (R_add a1) -> a2
r_add_rect x d f f0 f1 f2 _ _ r =
  case r of {
   R_add_0 m -> f m __;
   R_add_1 m l y d' r0 h _res r1 ->
    f0 m l y d' r0 h __ __ __ _res r1 (r_add_rect x d f f0 f1 f2 l _res r1);
   R_add_2 m l y d' r0 h -> f1 m l y d' r0 h __ __ __;
   R_add_3 m l y d' r0 h _res r1 ->
    f2 m l y d' r0 h __ __ __ _res r1 (r_add_rect x d f f0 f1 f2 r0 _res r1)}

r_add_rec :: Key -> a1 -> ((Tree a1) -> () -> a2) -> ((Tree a1) -> (Tree 
             a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> () -> () -> (Tree
             a1) -> (R_add a1) -> a2 -> a2) -> ((Tree a1) -> (Tree a1) -> Key
             -> a1 -> (Tree a1) -> T0 -> () -> () -> () -> a2) -> ((Tree 
             a1) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> () ->
             () -> (Tree a1) -> (R_add a1) -> a2 -> a2) -> (Tree a1) -> (Tree
             a1) -> (R_add a1) -> a2
r_add_rec =
  r_add_rect

data R_remove_min elt =
   R_remove_min_0 (Tree elt) Key elt (Tree elt)
 | R_remove_min_1 (Tree elt) Key elt (Tree elt) (Tree elt) Key elt (Tree elt) 
 T0 ((,) (Tree elt) ((,) Key elt)) (R_remove_min elt) (Tree elt) ((,) 
                                                                 Key 
                                                                 elt)

r_remove_min_rect :: ((Tree a1) -> Key -> a1 -> (Tree a1) -> () -> a2) ->
                     ((Tree a1) -> Key -> a1 -> (Tree a1) -> (Tree a1) -> Key
                     -> a1 -> (Tree a1) -> T0 -> () -> ((,) (Tree a1)
                     ((,) Key a1)) -> (R_remove_min a1) -> a2 -> (Tree 
                     a1) -> ((,) Key a1) -> () -> a2) -> (Tree a1) -> Key ->
                     a1 -> (Tree a1) -> ((,) (Tree a1) ((,) Key a1)) ->
                     (R_remove_min a1) -> a2
r_remove_min_rect f f0 _ _ _ _ _ r0 =
  case r0 of {
   R_remove_min_0 l x d r -> f l x d r __;
   R_remove_min_1 l x d r ll lx ld lr _x _res r1 l' m ->
    f0 l x d r ll lx ld lr _x __ _res r1
      (r_remove_min_rect f f0 ll lx ld lr _res r1) l' m __}

r_remove_min_rec :: ((Tree a1) -> Key -> a1 -> (Tree a1) -> () -> a2) ->
                    ((Tree a1) -> Key -> a1 -> (Tree a1) -> (Tree a1) -> Key
                    -> a1 -> (Tree a1) -> T0 -> () -> ((,) (Tree a1)
                    ((,) Key a1)) -> (R_remove_min a1) -> a2 -> (Tree 
                    a1) -> ((,) Key a1) -> () -> a2) -> (Tree a1) -> Key ->
                    a1 -> (Tree a1) -> ((,) (Tree a1) ((,) Key a1)) ->
                    (R_remove_min a1) -> a2
r_remove_min_rec =
  r_remove_min_rect

data R_merge elt =
   R_merge_0 (Tree elt) (Tree elt)
 | R_merge_1 (Tree elt) (Tree elt) (Tree elt) Key elt (Tree elt) T0
 | R_merge_2 (Tree elt) (Tree elt) (Tree elt) Key elt (Tree elt) T0 (Tree
                                                                    elt) 
 Key elt (Tree elt) T0 (Tree elt) ((,) Key elt) Key elt

r_merge_rect :: ((Tree a1) -> (Tree a1) -> () -> a2) -> ((Tree a1) -> (Tree
                a1) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> ()
                -> a2) -> ((Tree a1) -> (Tree a1) -> (Tree a1) -> Key -> a1
                -> (Tree a1) -> T0 -> () -> (Tree a1) -> Key -> a1 -> (Tree
                a1) -> T0 -> () -> (Tree a1) -> ((,) Key a1) -> () -> Key ->
                a1 -> () -> a2) -> (Tree a1) -> (Tree a1) -> (Tree a1) ->
                (R_merge a1) -> a2
r_merge_rect f f0 f1 _ _ _ r =
  case r of {
   R_merge_0 s1 s2 -> f s1 s2 __;
   R_merge_1 s1 s2 _x _x0 _x1 _x2 _x3 -> f0 s1 s2 _x _x0 _x1 _x2 _x3 __ __;
   R_merge_2 s1 s2 _x _x0 _x1 _x2 _x3 l2 x2 d2 r2 _x4 s2' p x d ->
    f1 s1 s2 _x _x0 _x1 _x2 _x3 __ l2 x2 d2 r2 _x4 __ s2' p __ x d __}

r_merge_rec :: ((Tree a1) -> (Tree a1) -> () -> a2) -> ((Tree a1) -> (Tree
               a1) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> ()
               -> a2) -> ((Tree a1) -> (Tree a1) -> (Tree a1) -> Key -> a1 ->
               (Tree a1) -> T0 -> () -> (Tree a1) -> Key -> a1 -> (Tree 
               a1) -> T0 -> () -> (Tree a1) -> ((,) Key a1) -> () -> Key ->
               a1 -> () -> a2) -> (Tree a1) -> (Tree a1) -> (Tree a1) ->
               (R_merge a1) -> a2
r_merge_rec =
  r_merge_rect

data R_remove elt =
   R_remove_0 (Tree elt)
 | R_remove_1 (Tree elt) (Tree elt) Key elt (Tree elt) T0 (Tree elt) 
 (R_remove elt)
 | R_remove_2 (Tree elt) (Tree elt) Key elt (Tree elt) T0
 | R_remove_3 (Tree elt) (Tree elt) Key elt (Tree elt) T0 (Tree elt) 
 (R_remove elt)

r_remove_rect :: Prelude.Integer -> ((Tree a1) -> () -> a2) -> ((Tree 
                 a1) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> ()
                 -> () -> (Tree a1) -> (R_remove a1) -> a2 -> a2) -> ((Tree
                 a1) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> ()
                 -> () -> a2) -> ((Tree a1) -> (Tree a1) -> Key -> a1 ->
                 (Tree a1) -> T0 -> () -> () -> () -> (Tree a1) -> (R_remove
                 a1) -> a2 -> a2) -> (Tree a1) -> (Tree a1) -> (R_remove 
                 a1) -> a2
r_remove_rect x f f0 f1 f2 _ _ r =
  case r of {
   R_remove_0 m -> f m __;
   R_remove_1 m l y d r0 _x _res r1 ->
    f0 m l y d r0 _x __ __ __ _res r1 (r_remove_rect x f f0 f1 f2 l _res r1);
   R_remove_2 m l y d r0 _x -> f1 m l y d r0 _x __ __ __;
   R_remove_3 m l y d r0 _x _res r1 ->
    f2 m l y d r0 _x __ __ __ _res r1 (r_remove_rect x f f0 f1 f2 r0 _res r1)}

r_remove_rec :: Prelude.Integer -> ((Tree a1) -> () -> a2) -> ((Tree 
                a1) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> ()
                -> () -> (Tree a1) -> (R_remove a1) -> a2 -> a2) -> ((Tree
                a1) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> ()
                -> () -> a2) -> ((Tree a1) -> (Tree a1) -> Key -> a1 -> (Tree
                a1) -> T0 -> () -> () -> () -> (Tree a1) -> (R_remove 
                a1) -> a2 -> a2) -> (Tree a1) -> (Tree a1) -> (R_remove 
                a1) -> a2
r_remove_rec =
  r_remove_rect

data R_concat elt =
   R_concat_0 (Tree elt) (Tree elt)
 | R_concat_1 (Tree elt) (Tree elt) (Tree elt) Key elt (Tree elt) T0
 | R_concat_2 (Tree elt) (Tree elt) (Tree elt) Key elt (Tree elt) T0 
 (Tree elt) Key elt (Tree elt) T0 (Tree elt) ((,) Key elt)

r_concat_rect :: ((Tree a1) -> (Tree a1) -> () -> a2) -> ((Tree a1) -> (Tree
                 a1) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> ()
                 -> a2) -> ((Tree a1) -> (Tree a1) -> (Tree a1) -> Key -> a1
                 -> (Tree a1) -> T0 -> () -> (Tree a1) -> Key -> a1 -> (Tree
                 a1) -> T0 -> () -> (Tree a1) -> ((,) Key a1) -> () -> a2) ->
                 (Tree a1) -> (Tree a1) -> (Tree a1) -> (R_concat a1) -> a2
r_concat_rect f f0 f1 _ _ _ r =
  case r of {
   R_concat_0 m1 m2 -> f m1 m2 __;
   R_concat_1 m1 m2 _x _x0 _x1 _x2 _x3 -> f0 m1 m2 _x _x0 _x1 _x2 _x3 __ __;
   R_concat_2 m1 m2 _x _x0 _x1 _x2 _x3 l2 x2 d2 r2 _x4 m2' xd ->
    f1 m1 m2 _x _x0 _x1 _x2 _x3 __ l2 x2 d2 r2 _x4 __ m2' xd __}

r_concat_rec :: ((Tree a1) -> (Tree a1) -> () -> a2) -> ((Tree a1) -> (Tree
                a1) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> ()
                -> a2) -> ((Tree a1) -> (Tree a1) -> (Tree a1) -> Key -> a1
                -> (Tree a1) -> T0 -> () -> (Tree a1) -> Key -> a1 -> (Tree
                a1) -> T0 -> () -> (Tree a1) -> ((,) Key a1) -> () -> a2) ->
                (Tree a1) -> (Tree a1) -> (Tree a1) -> (R_concat a1) -> a2
r_concat_rec =
  r_concat_rect

data R_split elt =
   R_split_0 (Tree elt)
 | R_split_1 (Tree elt) (Tree elt) Key elt (Tree elt) T0 (Triple elt) 
 (R_split elt) (Tree elt) (Option elt) (Tree elt)
 | R_split_2 (Tree elt) (Tree elt) Key elt (Tree elt) T0
 | R_split_3 (Tree elt) (Tree elt) Key elt (Tree elt) T0 (Triple elt) 
 (R_split elt) (Tree elt) (Option elt) (Tree elt)

r_split_rect :: Prelude.Integer -> ((Tree a1) -> () -> a2) -> ((Tree 
                a1) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> ()
                -> () -> (Triple a1) -> (R_split a1) -> a2 -> (Tree a1) ->
                (Option a1) -> (Tree a1) -> () -> a2) -> ((Tree a1) -> (Tree
                a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> () -> () -> a2)
                -> ((Tree a1) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T0 ->
                () -> () -> () -> (Triple a1) -> (R_split a1) -> a2 -> (Tree
                a1) -> (Option a1) -> (Tree a1) -> () -> a2) -> (Tree 
                a1) -> (Triple a1) -> (R_split a1) -> a2
r_split_rect x f f0 f1 f2 _ _ r =
  case r of {
   R_split_0 m -> f m __;
   R_split_1 m l y d r0 _x _res r1 ll o rl ->
    f0 m l y d r0 _x __ __ __ _res r1 (r_split_rect x f f0 f1 f2 l _res r1)
      ll o rl __;
   R_split_2 m l y d r0 _x -> f1 m l y d r0 _x __ __ __;
   R_split_3 m l y d r0 _x _res r1 rl o rr ->
    f2 m l y d r0 _x __ __ __ _res r1 (r_split_rect x f f0 f1 f2 r0 _res r1)
      rl o rr __}

r_split_rec :: Prelude.Integer -> ((Tree a1) -> () -> a2) -> ((Tree a1) ->
               (Tree a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> () -> () ->
               (Triple a1) -> (R_split a1) -> a2 -> (Tree a1) -> (Option 
               a1) -> (Tree a1) -> () -> a2) -> ((Tree a1) -> (Tree a1) ->
               Key -> a1 -> (Tree a1) -> T0 -> () -> () -> () -> a2) ->
               ((Tree a1) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T0 -> ()
               -> () -> () -> (Triple a1) -> (R_split a1) -> a2 -> (Tree 
               a1) -> (Option a1) -> (Tree a1) -> () -> a2) -> (Tree 
               a1) -> (Triple a1) -> (R_split a1) -> a2
r_split_rec =
  r_split_rect

data R_map_option elt x =
   R_map_option_0 (Tree elt)
 | R_map_option_1 (Tree elt) (Tree elt) Key elt (Tree elt) T0 x (Tree x) 
 (R_map_option elt x) (Tree x) (R_map_option elt x)
 | R_map_option_2 (Tree elt) (Tree elt) Key elt (Tree elt) T0 (Tree x) 
 (R_map_option elt x) (Tree x) (R_map_option elt x)

r_map_option_rect :: (Key -> a1 -> Option a2) -> ((Tree a1) -> () -> a3) ->
                     ((Tree a1) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T0
                     -> () -> a2 -> () -> (Tree a2) -> (R_map_option 
                     a1 a2) -> a3 -> (Tree a2) -> (R_map_option a1 a2) -> a3
                     -> a3) -> ((Tree a1) -> (Tree a1) -> Key -> a1 -> (Tree
                     a1) -> T0 -> () -> () -> (Tree a2) -> (R_map_option 
                     a1 a2) -> a3 -> (Tree a2) -> (R_map_option a1 a2) -> a3
                     -> a3) -> (Tree a1) -> (Tree a2) -> (R_map_option 
                     a1 a2) -> a3
r_map_option_rect f f0 f1 f2 _ _ r =
  case r of {
   R_map_option_0 m -> f0 m __;
   R_map_option_1 m l x d r0 _x d' _res0 r1 _res r2 ->
    f1 m l x d r0 _x __ d' __ _res0 r1
      (r_map_option_rect f f0 f1 f2 l _res0 r1) _res r2
      (r_map_option_rect f f0 f1 f2 r0 _res r2);
   R_map_option_2 m l x d r0 _x _res0 r1 _res r2 ->
    f2 m l x d r0 _x __ __ _res0 r1 (r_map_option_rect f f0 f1 f2 l _res0 r1)
      _res r2 (r_map_option_rect f f0 f1 f2 r0 _res r2)}

r_map_option_rec :: (Key -> a1 -> Option a2) -> ((Tree a1) -> () -> a3) ->
                    ((Tree a1) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T0
                    -> () -> a2 -> () -> (Tree a2) -> (R_map_option a1 
                    a2) -> a3 -> (Tree a2) -> (R_map_option a1 a2) -> a3 ->
                    a3) -> ((Tree a1) -> (Tree a1) -> Key -> a1 -> (Tree 
                    a1) -> T0 -> () -> () -> (Tree a2) -> (R_map_option 
                    a1 a2) -> a3 -> (Tree a2) -> (R_map_option a1 a2) -> a3
                    -> a3) -> (Tree a1) -> (Tree a2) -> (R_map_option 
                    a1 a2) -> a3
r_map_option_rec =
  r_map_option_rect

data R_map2_opt elt x0 x =
   R_map2_opt_0 (Tree elt) (Tree x0)
 | R_map2_opt_1 (Tree elt) (Tree x0) (Tree elt) Key elt (Tree elt) T0
 | R_map2_opt_2 (Tree elt) (Tree x0) (Tree elt) Key elt (Tree elt) T0 
 (Tree x0) Key x0 (Tree x0) T0 (Tree x0) (Option x0) (Tree x0) x (Tree x) 
 (R_map2_opt elt x0 x) (Tree x) (R_map2_opt elt x0 x)
 | R_map2_opt_3 (Tree elt) (Tree x0) (Tree elt) Key elt (Tree elt) T0 
 (Tree x0) Key x0 (Tree x0) T0 (Tree x0) (Option x0) (Tree x0) (Tree x) 
 (R_map2_opt elt x0 x) (Tree x) (R_map2_opt elt x0 x)

r_map2_opt_rect :: (Key -> a1 -> (Option a2) -> Option a3) -> ((Tree 
                   a1) -> Tree a3) -> ((Tree a2) -> Tree a3) -> ((Tree 
                   a1) -> (Tree a2) -> () -> a4) -> ((Tree a1) -> (Tree 
                   a2) -> (Tree a1) -> Key -> a1 -> (Tree a1) -> T0 -> () ->
                   () -> a4) -> ((Tree a1) -> (Tree a2) -> (Tree a1) -> Key
                   -> a1 -> (Tree a1) -> T0 -> () -> (Tree a2) -> Key -> a2
                   -> (Tree a2) -> T0 -> () -> (Tree a2) -> (Option a2) ->
                   (Tree a2) -> () -> a3 -> () -> (Tree a3) -> (R_map2_opt 
                   a1 a2 a3) -> a4 -> (Tree a3) -> (R_map2_opt a1 a2 
                   a3) -> a4 -> a4) -> ((Tree a1) -> (Tree a2) -> (Tree 
                   a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> (Tree 
                   a2) -> Key -> a2 -> (Tree a2) -> T0 -> () -> (Tree 
                   a2) -> (Option a2) -> (Tree a2) -> () -> () -> (Tree 
                   a3) -> (R_map2_opt a1 a2 a3) -> a4 -> (Tree a3) ->
                   (R_map2_opt a1 a2 a3) -> a4 -> a4) -> (Tree a1) -> (Tree
                   a2) -> (Tree a3) -> (R_map2_opt a1 a2 a3) -> a4
r_map2_opt_rect f mapl mapr f0 f1 f2 f3 _ _ _ r =
  case r of {
   R_map2_opt_0 m1 m2 -> f0 m1 m2 __;
   R_map2_opt_1 m1 m2 l1 x1 d1 r1 _x -> f1 m1 m2 l1 x1 d1 r1 _x __ __;
   R_map2_opt_2 m1 m2 l1 x1 d1 r1 _x _x0 _x1 _x2 _x3 _x4 l2' o2 r2' e _res0
    r0 _res r2 ->
    f2 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ e __
      _res0 r0 (r_map2_opt_rect f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0) _res
      r2 (r_map2_opt_rect f mapl mapr f0 f1 f2 f3 r1 r2' _res r2);
   R_map2_opt_3 m1 m2 l1 x1 d1 r1 _x _x0 _x1 _x2 _x3 _x4 l2' o2 r2' _res0 r0
    _res r2 ->
    f3 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ __ _res0
      r0 (r_map2_opt_rect f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0) _res r2
      (r_map2_opt_rect f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)}

r_map2_opt_rec :: (Key -> a1 -> (Option a2) -> Option a3) -> ((Tree a1) ->
                  Tree a3) -> ((Tree a2) -> Tree a3) -> ((Tree a1) -> (Tree
                  a2) -> () -> a4) -> ((Tree a1) -> (Tree a2) -> (Tree 
                  a1) -> Key -> a1 -> (Tree a1) -> T0 -> () -> () -> a4) ->
                  ((Tree a1) -> (Tree a2) -> (Tree a1) -> Key -> a1 -> (Tree
                  a1) -> T0 -> () -> (Tree a2) -> Key -> a2 -> (Tree 
                  a2) -> T0 -> () -> (Tree a2) -> (Option a2) -> (Tree 
                  a2) -> () -> a3 -> () -> (Tree a3) -> (R_map2_opt a1 
                  a2 a3) -> a4 -> (Tree a3) -> (R_map2_opt a1 a2 a3) -> a4 ->
                  a4) -> ((Tree a1) -> (Tree a2) -> (Tree a1) -> Key -> a1 ->
                  (Tree a1) -> T0 -> () -> (Tree a2) -> Key -> a2 -> (Tree
                  a2) -> T0 -> () -> (Tree a2) -> (Option a2) -> (Tree 
                  a2) -> () -> () -> (Tree a3) -> (R_map2_opt a1 a2 a3) -> a4
                  -> (Tree a3) -> (R_map2_opt a1 a2 a3) -> a4 -> a4) -> (Tree
                  a1) -> (Tree a2) -> (Tree a3) -> (R_map2_opt a1 a2 
                  a3) -> a4
r_map2_opt_rec =
  r_map2_opt_rect

fold' :: (Key -> a1 -> a2 -> a2) -> (Tree a1) -> a2 -> a2
fold' f s =
  fold0 f (elements s)

flatten_e :: (Enumeration a1) -> [] ((,) Key a1)
flatten_e e =
  case e of {
   End -> [];
   More x e0 t r -> (:) ((,) x e0) (app (elements t) (flatten_e r))}

type Bst elt = Tree elt
  -- singleton inductive, whose constructor was Bst
  
this :: (Bst a1) -> Tree a1
this b =
  b

type T7 elt = Bst elt

type Key1 = Prelude.Integer

empty1 :: T7 a1
empty1 =
  empty

is_empty1 :: (T7 a1) -> Prelude.Bool
is_empty1 m =
  is_empty (this m)

add6 :: Key1 -> a1 -> (T7 a1) -> T7 a1
add6 x e m =
  add4 x e (this m)

remove1 :: Key1 -> (T7 a1) -> T7 a1
remove1 x m =
  remove x (this m)

mem1 :: Key1 -> (T7 a1) -> Prelude.Bool
mem1 x m =
  mem x (this m)

find1 :: Key1 -> (T7 a1) -> Option a1
find1 x m =
  find x (this m)

map4 :: (a1 -> a2) -> (T7 a1) -> T7 a2
map4 f m =
  map0 f (this m)

mapi1 :: (Key1 -> a1 -> a2) -> (T7 a1) -> T7 a2
mapi1 f m =
  mapi f (this m)

map5 :: ((Option a1) -> (Option a2) -> Option a3) -> (T7 a1) -> (T7 a2) -> T7
        a3
map5 f m m' =
  map2 f (this m) (this m')

elements1 :: (T7 a1) -> [] ((,) Key1 a1)
elements1 m =
  elements (this m)

cardinal0 :: (T7 a1) -> Prelude.Integer
cardinal0 m =
  cardinal (this m)

fold1 :: (Key1 -> a1 -> a2 -> a2) -> (T7 a1) -> a2 -> a2
fold1 f m i =
  fold f (this m) i

equal1 :: (a1 -> a1 -> Prelude.Bool) -> (T7 a1) -> (T7 a1) -> Prelude.Bool
equal1 cmp m m' =
  equal cmp (this m) (this m')

type T8 = Prelude.Integer

zero :: Prelude.Integer
zero =
  0

one :: Prelude.Integer
one =
  Prelude.succ 0

two :: Prelude.Integer
two =
  Prelude.succ (Prelude.succ 0)

succ2 :: Prelude.Integer -> Prelude.Integer
succ2 x =
  Prelude.succ x

pred :: Prelude.Integer -> Prelude.Integer
pred n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> n)
    (\u -> u)
    n

add7 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add7 n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> m)
    (\p -> Prelude.succ (add7 p m))
    n

double0 :: Prelude.Integer -> Prelude.Integer
double0 n =
  add7 n n

mul0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
mul0 n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> 0)
    (\p -> add7 m (mul0 p m))
    n

sub0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub0 n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> n)
    (\k ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> n)
      (\l -> sub0 k l)
      m)
    n

eqb4 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
eqb4 n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.True)
      (\_ -> Prelude.False)
      m)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.False)
      (\m' -> eqb4 n' m')
      m)
    n

leb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
leb n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Prelude.True)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.False)
      (\m' -> leb n' m')
      m)
    n

ltb0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
ltb0 n m =
  leb (Prelude.succ n) m

compare4 :: Prelude.Integer -> Prelude.Integer -> Comparison
compare4 n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Eq)
      (\_ -> Lt)
      m)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Gt)
      (\m' -> compare4 n' m')
      m)
    n

max3 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
max3 n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> m)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> n)
      (\m' -> Prelude.succ (max3 n' m'))
      m)
    n

min1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
min1 n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> 0)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> 0)
      (\m' -> Prelude.succ (min1 n' m'))
      m)
    n

even0 :: Prelude.Integer -> Prelude.Bool
even0 n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Prelude.True)
    (\n0 ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.False)
      (\n' -> even0 n')
      n0)
    n

odd :: Prelude.Integer -> Prelude.Bool
odd n =
  negb (even0 n)

pow :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pow n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Prelude.succ 0)
    (\m0 -> mul0 n (pow n m0))
    m

tail_add :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
tail_add n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> m)
    (\n0 -> tail_add n0 (Prelude.succ m))
    n

tail_addmul :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer ->
               Prelude.Integer
tail_addmul r n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> r)
    (\n0 -> tail_addmul (tail_add m r) n0 m)
    n

tail_mul :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
tail_mul n m =
  tail_addmul 0 n m

of_uint_acc :: Uint -> Prelude.Integer -> Prelude.Integer
of_uint_acc d acc =
  case d of {
   Nil -> acc;
   D0 d0 ->
    of_uint_acc d0
      (tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ 0)))))))))) acc);
   D1 d0 ->
    of_uint_acc d0 (Prelude.succ
      (tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ 0)))))))))) acc));
   D2 d0 ->
    of_uint_acc d0 (Prelude.succ (Prelude.succ
      (tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ 0)))))))))) acc)));
   D3 d0 ->
    of_uint_acc d0 (Prelude.succ (Prelude.succ (Prelude.succ
      (tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ 0)))))))))) acc))));
   D4 d0 ->
    of_uint_acc d0 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ 0)))))))))) acc)))));
   D5 d0 ->
    of_uint_acc d0 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ
      (tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ 0)))))))))) acc))))));
   D6 d0 ->
    of_uint_acc d0 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ
      (tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ 0)))))))))) acc)))))));
   D7 d0 ->
    of_uint_acc d0 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ
      (tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ 0)))))))))) acc))))))));
   D8 d0 ->
    of_uint_acc d0 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ 0)))))))))) acc)))))))));
   D9 d0 ->
    of_uint_acc d0 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ 0)))))))))) acc))))))))))}

of_uint :: Uint -> Prelude.Integer
of_uint d =
  of_uint_acc d 0

of_hex_uint_acc :: Uint0 -> Prelude.Integer -> Prelude.Integer
of_hex_uint_acc d acc =
  case d of {
   Nil0 -> acc;
   D10 d0 ->
    of_hex_uint_acc d0
      (tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ 0)))))))))))))))) acc);
   D11 d0 ->
    of_hex_uint_acc d0 (Prelude.succ
      (tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ 0)))))))))))))))) acc));
   D12 d0 ->
    of_hex_uint_acc d0 (Prelude.succ (Prelude.succ
      (tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ 0)))))))))))))))) acc)));
   D13 d0 ->
    of_hex_uint_acc d0 (Prelude.succ (Prelude.succ (Prelude.succ
      (tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ 0)))))))))))))))) acc))));
   D14 d0 ->
    of_hex_uint_acc d0 (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ
      (tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ 0)))))))))))))))) acc)))));
   D15 d0 ->
    of_hex_uint_acc d0 (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ
      (tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ 0)))))))))))))))) acc))))));
   D16 d0 ->
    of_hex_uint_acc d0 (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ
      (tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ 0)))))))))))))))) acc)))))));
   D17 d0 ->
    of_hex_uint_acc d0 (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ 0)))))))))))))))) acc))))))));
   D18 d0 ->
    of_hex_uint_acc d0 (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ 0)))))))))))))))) acc)))))))));
   D19 d0 ->
    of_hex_uint_acc d0 (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ
      (tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ 0)))))))))))))))) acc))))))))));
   Da d0 ->
    of_hex_uint_acc d0 (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ
      (tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ 0)))))))))))))))) acc)))))))))));
   Db d0 ->
    of_hex_uint_acc d0 (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ
      (tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ 0)))))))))))))))) acc))))))))))));
   Dc d0 ->
    of_hex_uint_acc d0 (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ 0)))))))))))))))) acc)))))))))))));
   Dd d0 ->
    of_hex_uint_acc d0 (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ 0)))))))))))))))) acc))))))))))))));
   De d0 ->
    of_hex_uint_acc d0 (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ
      (tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ 0)))))))))))))))) acc)))))))))))))));
   Df d0 ->
    of_hex_uint_acc d0 (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ
      (tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ 0)))))))))))))))) acc))))))))))))))))}

of_hex_uint :: Uint0 -> Prelude.Integer
of_hex_uint d =
  of_hex_uint_acc d 0

of_num_uint :: Uint1 -> Prelude.Integer
of_num_uint d =
  case d of {
   UIntDecimal d0 -> of_uint d0;
   UIntHexadecimal d0 -> of_hex_uint d0}

to_little_uint :: Prelude.Integer -> Uint -> Uint
to_little_uint n acc =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> acc)
    (\n0 -> to_little_uint n0 (succ acc))
    n

to_uint :: Prelude.Integer -> Uint
to_uint n =
  rev (to_little_uint n (D0 Nil))

to_little_hex_uint :: Prelude.Integer -> Uint0 -> Uint0
to_little_hex_uint n acc =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> acc)
    (\n0 -> to_little_hex_uint n0 (succ0 acc))
    n

to_hex_uint :: Prelude.Integer -> Uint0
to_hex_uint n =
  rev0 (to_little_hex_uint n (D10 Nil0))

to_num_uint :: Prelude.Integer -> Uint1
to_num_uint n =
  UIntDecimal (to_uint n)

to_num_hex_uint :: Prelude.Integer -> Uint1
to_num_hex_uint n =
  UIntHexadecimal (to_hex_uint n)

of_int :: Signed_int -> Option Prelude.Integer
of_int d =
  case norm d of {
   Pos u -> Some (of_uint u);
   Neg _ -> None}

of_hex_int :: Signed_int0 -> Option Prelude.Integer
of_hex_int d =
  case norm0 d of {
   Pos0 u -> Some (of_hex_uint u);
   Neg0 _ -> None}

of_num_int :: Signed_int1 -> Option Prelude.Integer
of_num_int d =
  case d of {
   IntDecimal d0 -> of_int d0;
   IntHexadecimal d0 -> of_hex_int d0}

to_int :: Prelude.Integer -> Signed_int
to_int n =
  Pos (to_uint n)

to_hex_int :: Prelude.Integer -> Signed_int0
to_hex_int n =
  Pos0 (to_hex_uint n)

to_num_int :: Prelude.Integer -> Signed_int1
to_num_int n =
  IntDecimal (to_int n)

divmod0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer ->
           Prelude.Integer -> (,) Prelude.Integer Prelude.Integer
divmod0 x y q u =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> (,) q u)
    (\x' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> divmod0 x' y (Prelude.succ q) y)
      (\u' -> divmod0 x' y q u')
      u)
    x

div0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
div0 x y =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> y)
    (\y' -> fst (divmod0 x y' 0 y'))
    y

modulo0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
modulo0 x y =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> x)
    (\y' -> sub0 y' (snd (divmod0 x y' 0 y')))
    y

gcd0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
gcd0 a b =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> b)
    (\a' -> gcd0 (modulo0 b (Prelude.succ a')) (Prelude.succ a'))
    a

square :: Prelude.Integer -> Prelude.Integer
square n =
  mul0 n n

sqrt_iter :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer ->
             Prelude.Integer -> Prelude.Integer
sqrt_iter k p q r =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> p)
    (\k' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ ->
      sqrt_iter k' (Prelude.succ p) (Prelude.succ (Prelude.succ q))
        (Prelude.succ (Prelude.succ q)))
      (\r' -> sqrt_iter k' p q r')
      r)
    k

sqrt :: Prelude.Integer -> Prelude.Integer
sqrt n =
  sqrt_iter n 0 0 0

log2_iter :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer ->
             Prelude.Integer -> Prelude.Integer
log2_iter k p q r =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> p)
    (\k' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> log2_iter k' (Prelude.succ p) (Prelude.succ q) q)
      (\r' -> log2_iter k' p (Prelude.succ q) r')
      r)
    k

log2 :: Prelude.Integer -> Prelude.Integer
log2 n =
  log2_iter (pred n) 0 (Prelude.succ 0) 0

iter :: Prelude.Integer -> (a1 -> a1) -> a1 -> a1
iter n f x =
  nat_rect x (\_ -> f) n

div2 :: Prelude.Integer -> Prelude.Integer
div2 n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> 0)
    (\n0 ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> 0)
      (\n' -> Prelude.succ (div2 n'))
      n0)
    n

testbit :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
testbit a n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> odd a)
    (\n0 -> testbit (div2 a) n0)
    n

shiftl :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
shiftl a =
  nat_rect a (\_ -> double0)

shiftr :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
shiftr a =
  nat_rect a (\_ -> div2)

bitwise :: (Prelude.Bool -> Prelude.Bool -> Prelude.Bool) -> Prelude.Integer
           -> Prelude.Integer -> Prelude.Integer -> Prelude.Integer
bitwise op n a b =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> 0)
    (\n' ->
    add7
      (case op (odd a) (odd b) of {
        Prelude.True -> Prelude.succ 0;
        Prelude.False -> 0})
      (mul0 (Prelude.succ (Prelude.succ 0))
        (bitwise op n' (div2 a) (div2 b))))
    n

land :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
land a b =
  bitwise andb a a b

lor :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
lor a b =
  bitwise orb (max3 a b) a b

ldiff :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
ldiff a b =
  bitwise (\b0 b' -> andb b0 (negb b')) a a b

lxor :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
lxor a b =
  bitwise xorb (max3 a b) a b

recursion :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
recursion =
  nat_rect

decidable_eq_nat :: Prelude.Integer -> Prelude.Integer -> Decidable
decidable_eq_nat =
  eqb4

decidable_le_nat :: Prelude.Integer -> Prelude.Integer -> Decidable
decidable_le_nat =
  leb

eq_dec6 :: Prelude.Integer -> Prelude.Integer -> Sumbool
eq_dec6 n =
  nat_rec (\m ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Left)
      (\_ -> Right)
      m) (\_ iHn m ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Right)
      (\n0 -> iHn n0)
      m) n

leb_spec0 :: Prelude.Integer -> Prelude.Integer -> Reflect
leb_spec0 x y =
  iff_reflect (leb x y)

ltb_spec0 :: Prelude.Integer -> Prelude.Integer -> Reflect
ltb_spec0 x y =
  iff_reflect (ltb0 x y)

measure_right_induction :: (a1 -> Prelude.Integer) -> Prelude.Integer -> (a1
                           -> () -> (a1 -> () -> a2) -> a2) -> a1 -> a2
measure_right_induction f _ iH x =
  let {t0 = f x} in
  acc_rect (\n _ iH' _ y _ ->
    eq_rect (f y) (\_ iH'0 -> iH y __ (\y' _ -> iH'0 (f y') __ __ y' __)) n
      __ iH') t0 __ x __

measure_left_induction :: (a1 -> Prelude.Integer) -> Prelude.Integer -> (a1
                          -> () -> (a1 -> () -> a2) -> a2) -> a1 -> a2
measure_left_induction f _ iH x =
  let {t0 = f x} in
  acc_rect (\n _ iH' _ y _ ->
    eq_rect (f y) (\_ iH'0 -> iH y __ (\y' _ -> iH'0 (f y') __ __ y' __)) n
      __ iH') t0 __ x __

measure_induction :: (a1 -> Prelude.Integer) -> (a1 -> (a1 -> () -> a2) ->
                     a2) -> a1 -> a2
measure_induction f iH x =
  measure_right_induction f 0 (\y _ iH' -> iH y (\y0 _ -> iH' y0 __)) x

max_case_strong :: Prelude.Integer -> Prelude.Integer -> (Prelude.Integer ->
                   Prelude.Integer -> () -> a1 -> a1) -> (() -> a1) -> (() ->
                   a1) -> a1
max_case_strong n m compat hl hr =
  let {c = compSpec2Type n m (compare n m)} in
  case c of {
   CompGtT -> compat n (max0 n m) __ (hl __);
   _ -> compat m (max0 n m) __ (hr __)}

max_case :: Prelude.Integer -> Prelude.Integer -> (Prelude.Integer ->
            Prelude.Integer -> () -> a1 -> a1) -> a1 -> a1 -> a1
max_case n m x x0 x1 =
  max_case_strong n m x (\_ -> x0) (\_ -> x1)

max_dec :: Prelude.Integer -> Prelude.Integer -> Sumbool
max_dec n m =
  max_case n m (\_ _ _ h0 -> h0) Left Right

min_case_strong :: Prelude.Integer -> Prelude.Integer -> (Prelude.Integer ->
                   Prelude.Integer -> () -> a1 -> a1) -> (() -> a1) -> (() ->
                   a1) -> a1
min_case_strong n m compat hl hr =
  let {c = compSpec2Type n m (compare n m)} in
  case c of {
   CompGtT -> compat m (min0 n m) __ (hr __);
   _ -> compat n (min0 n m) __ (hl __)}

min_case :: Prelude.Integer -> Prelude.Integer -> (Prelude.Integer ->
            Prelude.Integer -> () -> a1 -> a1) -> a1 -> a1 -> a1
min_case n m x x0 x1 =
  min_case_strong n m x (\_ -> x0) (\_ -> x1)

min_dec :: Prelude.Integer -> Prelude.Integer -> Sumbool
min_dec n m =
  min_case n m (\_ _ _ h0 -> h0) Left Right

max_case_strong0 :: Prelude.Integer -> Prelude.Integer -> (() -> a1) -> (()
                    -> a1) -> a1
max_case_strong0 n m x x0 =
  max_case_strong n m (\_ _ _ x1 -> eq_rect __ x1 __) x x0

max_case0 :: Prelude.Integer -> Prelude.Integer -> a1 -> a1 -> a1
max_case0 n m x x0 =
  max_case_strong0 n m (\_ -> x) (\_ -> x0)

max_dec0 :: Prelude.Integer -> Prelude.Integer -> Sumbool
max_dec0 =
  max_dec

min_case_strong0 :: Prelude.Integer -> Prelude.Integer -> (() -> a1) -> (()
                    -> a1) -> a1
min_case_strong0 n m x x0 =
  min_case_strong n m (\_ _ _ x1 -> eq_rect __ x1 __) x x0

min_case0 :: Prelude.Integer -> Prelude.Integer -> a1 -> a1 -> a1
min_case0 n m x x0 =
  min_case_strong0 n m (\_ -> x) (\_ -> x0)

min_dec0 :: Prelude.Integer -> Prelude.Integer -> Sumbool
min_dec0 =
  min_dec

iter_rect :: (a1 -> a1) -> a1 -> a2 -> (Prelude.Integer -> a1 -> a2 -> a2) ->
             Prelude.Integer -> a2
iter_rect f a h0 hS n =
  nat_rect h0 (\n0 hn ->
    hS n0
      (let {
        f0 n1 =
          (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
            (\_ -> a)
            (\n2 -> f (f0 n2))
            n1}
       in f0 n0) hn) n

sqrt_up :: Prelude.Integer -> Prelude.Integer
sqrt_up a =
  case compare4 0 a of {
   Lt -> Prelude.succ (sqrt (pred a));
   _ -> 0}

log2_up :: Prelude.Integer -> Prelude.Integer
log2_up a =
  case compare4 (Prelude.succ 0) a of {
   Lt -> Prelude.succ (log2 (pred a));
   _ -> 0}

lcm :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
lcm a b =
  mul a (div b (gcd a b))

lcm0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
lcm0 a b =
  mul0 a (div0 b (gcd0 a b))

eqb_spec :: Prelude.Integer -> Prelude.Integer -> Reflect
eqb_spec x y =
  iff_reflect (eqb4 x y)

b2n :: Prelude.Bool -> Prelude.Integer
b2n b =
  case b of {
   Prelude.True -> Prelude.succ 0;
   Prelude.False -> 0}

setbit :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
setbit a n =
  lor a (shiftl (Prelude.succ 0) n)

clearbit :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
clearbit a n =
  ldiff a (shiftl (Prelude.succ 0) n)

ones :: Prelude.Integer -> Prelude.Integer
ones n =
  pred (shiftl (Prelude.succ 0) n)

lnot :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
lnot a n =
  lxor a (ones n)

even_Odd_dec :: Prelude.Integer -> Sumbool
even_Odd_dec n =
  nat_rec Left (\_ iHn -> sumbool_rec (\_ -> Right) (\_ -> Left) iHn) n

type EvenT0 = Prelude.Integer

type OddT0 = Prelude.Integer

evenT_1 :: EvenT0
evenT_1 =
  evenT_0

evenT_3 :: Prelude.Integer -> EvenT0 -> EvenT0
evenT_3 =
  evenT_2

oddT_0 :: OddT0
oddT_0 =
  oddT_1

oddT_3 :: Prelude.Integer -> OddT0 -> OddT0
oddT_3 =
  oddT_2

evenT_S_OddT0 :: Prelude.Integer -> EvenT0 -> OddT0
evenT_S_OddT0 =
  evenT_S_OddT

oddT_S_EvenT0 :: Prelude.Integer -> OddT0 -> EvenT0
oddT_S_EvenT0 =
  oddT_S_EvenT

even_EvenT1 :: Prelude.Integer -> EvenT0
even_EvenT1 =
  even_EvenT

odd_OddT1 :: Prelude.Integer -> OddT0
odd_OddT1 =
  odd_OddT

even_EvenT2 :: Prelude.Integer -> EvenT0
even_EvenT2 =
  even_EvenT0

odd_OddT2 :: Prelude.Integer -> OddT0
odd_OddT2 =
  odd_OddT0

evenT_OddT_dec0 :: Prelude.Integer -> Sum EvenT0 OddT0
evenT_OddT_dec0 =
  evenT_OddT_dec

oddT_EvenT_rect0 :: (Prelude.Integer -> EvenT0 -> a2 -> a1) -> a2 ->
                    (Prelude.Integer -> OddT0 -> a1 -> a2) -> Prelude.Integer
                    -> OddT0 -> a1
oddT_EvenT_rect0 =
  oddT_EvenT_rect

evenT_OddT_rect0 :: (Prelude.Integer -> EvenT0 -> a2 -> a1) -> a2 ->
                    (Prelude.Integer -> OddT0 -> a1 -> a2) -> Prelude.Integer
                    -> EvenT0 -> a2
evenT_OddT_rect0 =
  evenT_OddT_rect

type Node1 = T8

type Adj b = [] ((,) b Node1)

type Context a b = (,) ((,) ((,) (Adj b) Node1) a) (Adj b)

type MContext a b = Option (Context a b)

type Context' a b = (,) ((,) (Adj b) a) (Adj b)

type IG a b = T7 (Context' a b)

type Decomp a b = (,) (MContext a b) (IG a b)

type LNode a = (,) Node1 a

type LEdge b = (,) ((,) Node1 Node1) b

iG_empty :: IG a1 a2
iG_empty =
  empty1

iG_isEmpty :: (IG a1 a2) -> Prelude.Bool
iG_isEmpty =
  is_empty1

_updateEntry :: Node1 -> ((Context' a1 a2) -> Context' a1 a2) -> (IG 
                a1 a2) -> IG a1 a2
_updateEntry node f ig =
  case find1 node ig of {
   Some v -> add6 node (f v) ig;
   None -> ig}

_addSucc :: Node1 -> a2 -> (Context' a1 a2) -> Context' a1 a2
_addSucc node label context' =
  case context' of {
   (,) p tos -> (,) p ((:) ((,) label node) tos)}

_addPred :: Node1 -> a2 -> (Context' a1 a2) -> Context' a1 a2
_addPred node label context' =
  case context' of {
   (,) p tos ->
    case p of {
     (,) froms l -> (,) ((,) ((:) ((,) label node) froms) l) tos}}

_clearSucc :: Node1 -> (Context' a1 a2) -> Context' a1 a2
_clearSucc node context' =
  case context' of {
   (,) p tos -> (,) p
    (filter (\pat -> case pat of {
                      (,) _ n -> negb (eqb n node)}) tos)}

_clearPred :: Node1 -> (Context' a1 a2) -> Context' a1 a2
_clearPred node context' =
  case context' of {
   (,) p tos ->
    case p of {
     (,) froms label -> (,) ((,)
      (filter (\pat -> case pat of {
                        (,) _ n -> negb (eqb n node)}) froms) label) tos}}

_updAdj :: (Adj a2) -> (a2 -> (Context' a1 a2) -> Context' a1 a2) -> (IG 
           a1 a2) -> IG a1 a2
_updAdj adj f ig =
  fold_right (\pat acc -> case pat of {
                           (,) l n -> _updateEntry n (f l) acc}) ig adj

_cleanSplit :: Node1 -> (Context' a1 a2) -> (IG a1 a2) -> (,) (Context a1 a2)
               (IG a1 a2)
_cleanSplit node context' ig =
  case context' of {
   (,) p tos ->
    case p of {
     (,) froms label ->
      let {
       rmLoops = filter (\pat -> case pat of {
                                  (,) _ n -> negb (eqb n node)})}
      in
      let {froms' = rmLoops froms} in
      let {tos' = rmLoops tos} in
      let {context = (,) ((,) ((,) froms' node) label) tos} in
      let {ig' = _updAdj froms' (\_ y -> _clearSucc node y) ig} in
      let {ig'' = _updAdj tos' (\_ y -> _clearPred node y) ig'} in
      (,) context ig''}}

iG_match :: Node1 -> (IG a1 a2) -> Decomp a1 a2
iG_match node ig =
  case find1 node ig of {
   Some context' ->
    case _cleanSplit node context' (remove1 node ig) of {
     (,) context rest -> (,) (Some context) rest};
   None -> (,) None ig}

iG_and :: (Context a1 a2) -> (IG a1 a2) -> IG a1 a2
iG_and context ig =
  case context of {
   (,) p tos ->
    case p of {
     (,) p0 label ->
      case p0 of {
       (,) froms node ->
        case mem1 node ig of {
         Prelude.True -> ig;
         Prelude.False ->
          let {ig' = add6 node ((,) ((,) froms label) tos) ig} in
          let {ig'' = _updAdj tos (_addPred node) ig'} in
          _updAdj froms (_addSucc node) ig''}}}}

_insNode :: (LNode a1) -> (IG a1 a2) -> IG a1 a2
_insNode node ig =
  case node of {
   (,) n l -> iG_and ((,) ((,) ((,) [] n) l) []) ig}

_insNodes :: ([] (LNode a1)) -> (IG a1 a2) -> IG a1 a2
_insNodes nodes ig =
  fold_right _insNode ig nodes

_insEdge :: (LEdge a2) -> (IG a1 a2) -> IG a1 a2
_insEdge edge ig =
  case edge of {
   (,) p l ->
    case p of {
     (,) from to ->
      case iG_match from ig of {
       (,) mcxt ig' ->
        case mcxt of {
         Some c ->
          case c of {
           (,) p0 tos ->
            case p0 of {
             (,) p1 label ->
              case p1 of {
               (,) froms _ ->
                iG_and ((,) ((,) ((,) froms from) label) ((:) ((,) l to)
                  tos)) ig'}}};
         None -> ig}}}}

_insEdges :: ([] (LEdge a2)) -> (IG a1 a2) -> IG a1 a2
_insEdges edges ig =
  fold_right _insEdge ig edges

iG_mkGraph :: ([] (LNode a1)) -> ([] (LEdge a2)) -> IG a1 a2
iG_mkGraph nodes edges =
  _insEdges edges (_insNodes nodes iG_empty)

iG_labNodes :: (IG a1 a2) -> [] (LNode a1)
iG_labNodes ig =
  map (\pat ->
    case pat of {
     (,) v y -> case y of {
                 (,) y0 _ -> case y0 of {
                              (,) _ l -> (,) v l}}}) (elements1 ig)

iG_matchAny :: (IG a1 a2) -> Decomp a1 a2
iG_matchAny ig =
  case iG_labNodes ig of {
   [] -> (,) None ig;
   (:) node _ -> iG_match (fst node) ig}

iG_noNodes :: (IG a1 a2) -> Prelude.Integer
iG_noNodes ig =
  length (iG_labNodes ig)

_minimum :: Prelude.Integer -> ([] Prelude.Integer) -> Prelude.Integer
_minimum n l =
  fold_right min n l

_maximum :: Prelude.Integer -> ([] Prelude.Integer) -> Prelude.Integer
_maximum n l =
  fold_right max n l

iG_nodeRange :: (IG a1 a2) -> (,) Node1 Node1
iG_nodeRange ig =
  case map fst (iG_labNodes ig) of {
   [] -> (,) 0 0;
   (:) node nodes -> (,) (_minimum node nodes) (_maximum node nodes)}

iG_labEdges :: (IG a1 a2) -> [] (LEdge a2)
iG_labEdges ig =
  fold_right (\pat acc ->
    case pat of {
     (,) node y ->
      case y of {
       (,) _ tos ->
        app
          (map (\pat0 -> case pat0 of {
                          (,) l to -> (,) ((,) node to) l}) tos) acc}}) []
    (elements1 ig)

iG_ufold :: ((Context a1 a2) -> a3 -> a3) -> a3 -> (IG a1 a2) -> a3
iG_ufold f acc ig =
  case iG_matchAny ig of {
   (,) m i ->
    case m of {
     Some c -> sig_rect (\rec_res _ -> f c rec_res) (iG_ufold f acc i);
     None -> acc}}

iG_gmap :: ((Context a1 a2) -> Context a3 a4) -> (IG a1 a2) -> IG a3 a4
iG_gmap f ig =
  iG_ufold (\c acc -> iG_and (f c) acc) iG_empty ig

_transposeContext :: (Context a1 a2) -> Context a1 a2
_transposeContext c =
  case c of {
   (,) p tos ->
    case p of {
     (,) p0 label ->
      case p0 of {
       (,) froms node -> (,) ((,) ((,) tos node) label) froms}}}

iG_transpose :: (IG a1 a2) -> IG a1 a2
iG_transpose ig =
  iG_gmap _transposeContext ig

suc :: (Context a1 a2) -> [] Node
suc c =
  case c of {
   (,) _ tos -> map snd tos}

_DFS_rec :: ((,) (IG a1 a2) ([] Node)) -> [] Node
_DFS_rec x1 =
  and_rect (\_ _ ->
    and_rect (\_ _ _ _ igNodes ->
      let {
       hrec igNodes0 =
         case igNodes0 of {
          (,) i l ->
           case l of {
            [] -> [];
            (:) n l0 ->
             case iG_isEmpty i of {
              Prelude.True -> [];
              Prelude.False ->
               case iG_match n i of {
                (,) m i0 ->
                 case m of {
                  Some c ->
                   sig_rec (\rec_res _ -> (:) n rec_res)
                     (hrec ((,) i0 (app (suc c) l0)));
                  None -> sig_rec (\rec_res _ -> rec_res) (hrec ((,) i0 l0))}}}}}}
      in hrec igNodes)) __ __ x1

iG_DFS :: ([] Node) -> (IG a1 a2) -> [] Node
iG_DFS nodes ig =
  _DFS_rec ((,) ig nodes)
