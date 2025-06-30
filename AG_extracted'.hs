module AG_extracted' where

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

data Z =
   Z0
 | Zpos Positive
 | Zneg Positive

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

leb :: Z -> Z -> Prelude.Bool
leb x y =
  case compare1 x y of {
   Gt -> Prelude.False;
   _ -> Prelude.True}

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

type T = Z

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

ltb0 :: Z -> Z -> Prelude.Bool
ltb0 =
  ltb

leb0 :: Z -> Z -> Prelude.Bool
leb0 =
  leb

type T0 = Prelude.Integer

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

add4 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add4 n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> m)
    (\p -> Prelude.succ (add4 p m))
    n

double0 :: Prelude.Integer -> Prelude.Integer
double0 n =
  add4 n n

mul0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
mul0 n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> 0)
    (\p -> add4 m (mul0 p m))
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

eqb0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
eqb0 n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.True)
      (\_ -> Prelude.False)
      m)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.False)
      (\m' -> eqb0 n' m')
      m)
    n

leb1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
leb1 n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Prelude.True)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.False)
      (\m' -> leb1 n' m')
      m)
    n

ltb1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
ltb1 n m =
  leb1 (Prelude.succ n) m

compare2 :: Prelude.Integer -> Prelude.Integer -> Comparison
compare2 n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Eq)
      (\_ -> Lt)
      m)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Gt)
      (\m' -> compare2 n' m')
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
    add4
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
  eqb0

decidable_le_nat :: Prelude.Integer -> Prelude.Integer -> Decidable
decidable_le_nat =
  leb1

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

leb_spec0 :: Prelude.Integer -> Prelude.Integer -> Reflect
leb_spec0 x y =
  iff_reflect (leb1 x y)

ltb_spec0 :: Prelude.Integer -> Prelude.Integer -> Reflect
ltb_spec0 x y =
  iff_reflect (ltb1 x y)

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
  case compare2 0 a of {
   Lt -> Prelude.succ (sqrt (pred a));
   _ -> 0}

log2_up :: Prelude.Integer -> Prelude.Integer
log2_up a =
  case compare2 (Prelude.succ 0) a of {
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
  iff_reflect (eqb0 x y)

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

type Node = T0

type Elt = Prelude.Integer

data Tree =
   Leaf
 | Node0 T Tree Prelude.Integer Tree

empty :: Tree
empty =
  Leaf

is_empty :: Tree -> Prelude.Bool
is_empty t =
  case t of {
   Leaf -> Prelude.True;
   Node0 _ _ _ _ -> Prelude.False}

mem :: Prelude.Integer -> Tree -> Prelude.Bool
mem x t =
  case t of {
   Leaf -> Prelude.False;
   Node0 _ l k r ->
    case let {
          compare10 n m =
            (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
              (\_ ->
              (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                (\_ -> Eq)
                (\_ -> Lt)
                m)
              (\n' ->
              (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                (\_ -> Gt)
                (\m' -> compare10 n' m')
                m)
              n}
         in compare10 x k of {
     Eq -> Prelude.True;
     Lt -> mem x l;
     Gt -> mem x r}}

min_elt :: Tree -> Option Elt
min_elt t =
  case t of {
   Leaf -> None;
   Node0 _ l x _ -> case l of {
                     Leaf -> Some x;
                     Node0 _ _ _ _ -> min_elt l}}

max_elt :: Tree -> Option Elt
max_elt t =
  case t of {
   Leaf -> None;
   Node0 _ _ x r -> case r of {
                     Leaf -> Some x;
                     Node0 _ _ _ _ -> max_elt r}}

choose :: Tree -> Option Elt
choose =
  min_elt

fold :: (Elt -> a1 -> a1) -> Tree -> a1 -> a1
fold f t base =
  case t of {
   Leaf -> base;
   Node0 _ l x r -> fold f r (f x (fold f l base))}

elements_aux :: ([] Prelude.Integer) -> Tree -> [] Prelude.Integer
elements_aux acc s =
  case s of {
   Leaf -> acc;
   Node0 _ l x r -> elements_aux ((:) x (elements_aux acc r)) l}

elements :: Tree -> [] Prelude.Integer
elements =
  elements_aux []

rev_elements_aux :: ([] Prelude.Integer) -> Tree -> [] Prelude.Integer
rev_elements_aux acc s =
  case s of {
   Leaf -> acc;
   Node0 _ l x r -> rev_elements_aux ((:) x (rev_elements_aux acc l)) r}

rev_elements :: Tree -> [] Prelude.Integer
rev_elements =
  rev_elements_aux []

cardinal :: Tree -> Prelude.Integer
cardinal s =
  case s of {
   Leaf -> 0;
   Node0 _ l _ r -> Prelude.succ (add (cardinal l) (cardinal r))}

maxdepth :: Tree -> Prelude.Integer
maxdepth s =
  case s of {
   Leaf -> 0;
   Node0 _ l _ r -> Prelude.succ (max (maxdepth l) (maxdepth r))}

mindepth :: Tree -> Prelude.Integer
mindepth s =
  case s of {
   Leaf -> 0;
   Node0 _ l _ r -> Prelude.succ (min (mindepth l) (mindepth r))}

for_all :: (Elt -> Prelude.Bool) -> Tree -> Prelude.Bool
for_all f s =
  case s of {
   Leaf -> Prelude.True;
   Node0 _ l x r ->
    case case f x of {
          Prelude.True -> for_all f l;
          Prelude.False -> Prelude.False} of {
     Prelude.True -> for_all f r;
     Prelude.False -> Prelude.False}}

exists_ :: (Elt -> Prelude.Bool) -> Tree -> Prelude.Bool
exists_ f s =
  case s of {
   Leaf -> Prelude.False;
   Node0 _ l x r ->
    case case f x of {
          Prelude.True -> Prelude.True;
          Prelude.False -> exists_ f l} of {
     Prelude.True -> Prelude.True;
     Prelude.False -> exists_ f r}}

data Enumeration =
   End
 | More Elt Tree Enumeration

cons :: Tree -> Enumeration -> Enumeration
cons s e =
  case s of {
   Leaf -> e;
   Node0 _ l x r -> cons l (More x r e)}

compare_more :: Prelude.Integer -> (Enumeration -> Comparison) -> Enumeration
                -> Comparison
compare_more x1 cont e2 =
  case e2 of {
   End -> Gt;
   More x2 r2 e3 ->
    case let {
          compare10 n m =
            (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
              (\_ ->
              (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                (\_ -> Eq)
                (\_ -> Lt)
                m)
              (\n' ->
              (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                (\_ -> Gt)
                (\m' -> compare10 n' m')
                m)
              n}
         in compare10 x1 x2 of {
     Eq -> cont (cons r2 e3);
     x -> x}}

compare_cont0 :: Tree -> (Enumeration -> Comparison) -> Enumeration ->
                 Comparison
compare_cont0 s1 cont e2 =
  case s1 of {
   Leaf -> cont e2;
   Node0 _ l1 x1 r1 ->
    compare_cont0 l1 (compare_more x1 (compare_cont0 r1 cont)) e2}

compare_end :: Enumeration -> Comparison
compare_end e2 =
  case e2 of {
   End -> Eq;
   More _ _ _ -> Lt}

compare3 :: Tree -> Tree -> Comparison
compare3 s1 s2 =
  compare_cont0 s1 compare_end (cons s2 End)

equal :: Tree -> Tree -> Prelude.Bool
equal s1 s2 =
  case compare3 s1 s2 of {
   Eq -> Prelude.True;
   _ -> Prelude.False}

subsetl :: (Tree -> Prelude.Bool) -> Prelude.Integer -> Tree -> Prelude.Bool
subsetl subset_l1 x1 s2 =
  case s2 of {
   Leaf -> Prelude.False;
   Node0 _ l2 x2 r2 ->
    case let {
          compare10 n m =
            (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
              (\_ ->
              (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                (\_ -> Eq)
                (\_ -> Lt)
                m)
              (\n' ->
              (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                (\_ -> Gt)
                (\m' -> compare10 n' m')
                m)
              n}
         in compare10 x1 x2 of {
     Eq -> subset_l1 l2;
     Lt -> subsetl subset_l1 x1 l2;
     Gt ->
      case mem x1 r2 of {
       Prelude.True -> subset_l1 s2;
       Prelude.False -> Prelude.False}}}

subsetr :: (Tree -> Prelude.Bool) -> Prelude.Integer -> Tree -> Prelude.Bool
subsetr subset_r1 x1 s2 =
  case s2 of {
   Leaf -> Prelude.False;
   Node0 _ l2 x2 r2 ->
    case let {
          compare10 n m =
            (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
              (\_ ->
              (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                (\_ -> Eq)
                (\_ -> Lt)
                m)
              (\n' ->
              (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                (\_ -> Gt)
                (\m' -> compare10 n' m')
                m)
              n}
         in compare10 x1 x2 of {
     Eq -> subset_r1 r2;
     Lt ->
      case mem x1 l2 of {
       Prelude.True -> subset_r1 s2;
       Prelude.False -> Prelude.False};
     Gt -> subsetr subset_r1 x1 r2}}

subset :: Tree -> Tree -> Prelude.Bool
subset s1 s2 =
  case s1 of {
   Leaf -> Prelude.True;
   Node0 _ l1 x1 r1 ->
    case s2 of {
     Leaf -> Prelude.False;
     Node0 _ l2 x2 r2 ->
      case let {
            compare10 n m =
              (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                (\_ ->
                (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                  (\_ -> Eq)
                  (\_ -> Lt)
                  m)
                (\n' ->
                (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                  (\_ -> Gt)
                  (\m' -> compare10 n' m')
                  m)
                n}
           in compare10 x1 x2 of {
       Eq ->
        case subset l1 l2 of {
         Prelude.True -> subset r1 r2;
         Prelude.False -> Prelude.False};
       Lt ->
        case subsetl (subset l1) x1 l2 of {
         Prelude.True -> subset r1 s2;
         Prelude.False -> Prelude.False};
       Gt ->
        case subsetr (subset r1) x1 r2 of {
         Prelude.True -> subset l1 s2;
         Prelude.False -> Prelude.False}}}}

type T1 = Tree

height :: T1 -> T
height s =
  case s of {
   Leaf -> _0;
   Node0 h _ _ _ -> h}

singleton :: Prelude.Integer -> Tree
singleton x =
  Node0 _1 Leaf x Leaf

create :: T1 -> Prelude.Integer -> T1 -> Tree
create l x r =
  Node0 (add3 (max2 (height l) (height r)) _1) l x r

assert_false :: T1 -> Prelude.Integer -> T1 -> Tree
assert_false =
  create

bal :: T1 -> Prelude.Integer -> T1 -> Tree
bal l x r =
  let {hl = height l} in
  let {hr = height r} in
  case ltb0 (add3 hr _2) hl of {
   Prelude.True ->
    case l of {
     Leaf -> assert_false l x r;
     Node0 _ ll lx lr ->
      case leb0 (height lr) (height ll) of {
       Prelude.True -> create ll lx (create lr x r);
       Prelude.False ->
        case lr of {
         Leaf -> assert_false l x r;
         Node0 _ lrl lrx lrr ->
          create (create ll lx lrl) lrx (create lrr x r)}}};
   Prelude.False ->
    case ltb0 (add3 hl _2) hr of {
     Prelude.True ->
      case r of {
       Leaf -> assert_false l x r;
       Node0 _ rl rx rr ->
        case leb0 (height rl) (height rr) of {
         Prelude.True -> create (create l x rl) rx rr;
         Prelude.False ->
          case rl of {
           Leaf -> assert_false l x r;
           Node0 _ rll rlx rlr ->
            create (create l x rll) rlx (create rlr rx rr)}}};
     Prelude.False -> create l x r}}

add5 :: Prelude.Integer -> Tree -> Tree
add5 x s =
  case s of {
   Leaf -> Node0 _1 Leaf x Leaf;
   Node0 h l y r ->
    case let {
          compare10 n m =
            (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
              (\_ ->
              (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                (\_ -> Eq)
                (\_ -> Lt)
                m)
              (\n' ->
              (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                (\_ -> Gt)
                (\m' -> compare10 n' m')
                m)
              n}
         in compare10 x y of {
     Eq -> Node0 h l y r;
     Lt -> bal (add5 x l) y r;
     Gt -> bal l y (add5 x r)}}

join :: Tree -> Elt -> T1 -> T1
join l =
  case l of {
   Leaf -> add5;
   Node0 lh ll lx lr -> (\x ->
    let {
     join_aux r =
       case r of {
        Leaf -> add5 x l;
        Node0 rh rl rx rr ->
         case ltb0 (add3 rh _2) lh of {
          Prelude.True -> bal ll lx (join lr x r);
          Prelude.False ->
           case ltb0 (add3 lh _2) rh of {
            Prelude.True -> bal (join_aux rl) rx rr;
            Prelude.False -> create l x r}}}}
    in join_aux)}

remove_min :: Tree -> Elt -> T1 -> (,) T1 Elt
remove_min l x r =
  case l of {
   Leaf -> (,) r x;
   Node0 _ ll lx lr ->
    case remove_min ll lx lr of {
     (,) l' m -> (,) (bal l' x r) m}}

merge :: Tree -> Tree -> Tree
merge s1 s2 =
  case s1 of {
   Leaf -> s2;
   Node0 _ _ _ _ ->
    case s2 of {
     Leaf -> s1;
     Node0 _ l2 x2 r2 ->
      case remove_min l2 x2 r2 of {
       (,) s2' m -> bal s1 m s2'}}}

remove :: Prelude.Integer -> Tree -> Tree
remove x s =
  case s of {
   Leaf -> Leaf;
   Node0 _ l y r ->
    case let {
          compare10 n m =
            (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
              (\_ ->
              (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                (\_ -> Eq)
                (\_ -> Lt)
                m)
              (\n' ->
              (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                (\_ -> Gt)
                (\m' -> compare10 n' m')
                m)
              n}
         in compare10 x y of {
     Eq -> merge l r;
     Lt -> bal (remove x l) y r;
     Gt -> bal l y (remove x r)}}

concat :: Tree -> Tree -> Tree
concat s1 s2 =
  case s1 of {
   Leaf -> s2;
   Node0 _ _ _ _ ->
    case s2 of {
     Leaf -> s1;
     Node0 _ l2 x2 r2 ->
      case remove_min l2 x2 r2 of {
       (,) s2' m -> join s1 m s2'}}}

data Triple =
   Mktriple T1 Prelude.Bool T1

t_left :: Triple -> T1
t_left t =
  case t of {
   Mktriple t_left0 _ _ -> t_left0}

t_in :: Triple -> Prelude.Bool
t_in t =
  case t of {
   Mktriple _ t_in0 _ -> t_in0}

t_right :: Triple -> T1
t_right t =
  case t of {
   Mktriple _ _ t_right0 -> t_right0}

split :: Prelude.Integer -> Tree -> Triple
split x s =
  case s of {
   Leaf -> Mktriple Leaf Prelude.False Leaf;
   Node0 _ l y r ->
    case let {
          compare10 n m =
            (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
              (\_ ->
              (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                (\_ -> Eq)
                (\_ -> Lt)
                m)
              (\n' ->
              (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                (\_ -> Gt)
                (\m' -> compare10 n' m')
                m)
              n}
         in compare10 x y of {
     Eq -> Mktriple l Prelude.True r;
     Lt ->
      case split x l of {
       Mktriple ll b rl -> Mktriple ll b (join rl y r)};
     Gt ->
      case split x r of {
       Mktriple rl b rr -> Mktriple (join l y rl) b rr}}}

inter :: Tree -> Tree -> Tree
inter s1 s2 =
  case s1 of {
   Leaf -> Leaf;
   Node0 _ l1 x1 r1 ->
    case s2 of {
     Leaf -> Leaf;
     Node0 _ _ _ _ ->
      case split x1 s2 of {
       Mktriple l2' pres r2' ->
        case pres of {
         Prelude.True -> join (inter l1 l2') x1 (inter r1 r2');
         Prelude.False -> concat (inter l1 l2') (inter r1 r2')}}}}

diff :: Tree -> Tree -> Tree
diff s1 s2 =
  case s1 of {
   Leaf -> Leaf;
   Node0 _ l1 x1 r1 ->
    case s2 of {
     Leaf -> s1;
     Node0 _ _ _ _ ->
      case split x1 s2 of {
       Mktriple l2' pres r2' ->
        case pres of {
         Prelude.True -> concat (diff l1 l2') (diff r1 r2');
         Prelude.False -> join (diff l1 l2') x1 (diff r1 r2')}}}}

union :: Tree -> Tree -> Tree
union s1 s2 =
  case s1 of {
   Leaf -> s2;
   Node0 _ l1 x1 r1 ->
    case s2 of {
     Leaf -> s1;
     Node0 _ _ _ _ ->
      case split x1 s2 of {
       Mktriple l2' _ r2' -> join (union l1 l2') x1 (union r1 r2')}}}

filter0 :: (Elt -> Prelude.Bool) -> Tree -> Tree
filter0 f s =
  case s of {
   Leaf -> Leaf;
   Node0 _ l x r ->
    let {l' = filter0 f l} in
    let {r' = filter0 f r} in
    case f x of {
     Prelude.True -> join l' x r';
     Prelude.False -> concat l' r'}}

partition :: (Elt -> Prelude.Bool) -> T1 -> (,) T1 T1
partition f s =
  case s of {
   Leaf -> (,) Leaf Leaf;
   Node0 _ l x r ->
    case partition f l of {
     (,) l1 l2 ->
      case partition f r of {
       (,) r1 r2 ->
        case f x of {
         Prelude.True -> (,) (join l1 x r1) (concat l2 r2);
         Prelude.False -> (,) (concat l1 r1) (join l2 x r2)}}}}

ltb_tree :: Prelude.Integer -> Tree -> Prelude.Bool
ltb_tree x s =
  case s of {
   Leaf -> Prelude.True;
   Node0 _ l y r ->
    case let {
          compare10 n m =
            (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
              (\_ ->
              (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                (\_ -> Eq)
                (\_ -> Lt)
                m)
              (\n' ->
              (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                (\_ -> Gt)
                (\m' -> compare10 n' m')
                m)
              n}
         in compare10 x y of {
     Gt -> andb (ltb_tree x l) (ltb_tree x r);
     _ -> Prelude.False}}

gtb_tree :: Prelude.Integer -> Tree -> Prelude.Bool
gtb_tree x s =
  case s of {
   Leaf -> Prelude.True;
   Node0 _ l y r ->
    case let {
          compare10 n m =
            (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
              (\_ ->
              (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                (\_ -> Eq)
                (\_ -> Lt)
                m)
              (\n' ->
              (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                (\_ -> Gt)
                (\m' -> compare10 n' m')
                m)
              n}
         in compare10 x y of {
     Lt -> andb (gtb_tree x l) (gtb_tree x r);
     _ -> Prelude.False}}

isok :: Tree -> Prelude.Bool
isok s =
  case s of {
   Leaf -> Prelude.True;
   Node0 _ l x r ->
    andb (andb (andb (isok l) (isok r)) (ltb_tree x l)) (gtb_tree x r)}

type T2 = Prelude.Integer

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

eq_dec0 :: Prelude.Integer -> Prelude.Integer -> Sumbool
eq_dec0 =
  eq_dec

type T3 = Prelude.Integer

compare5 :: Prelude.Integer -> Prelude.Integer -> Comparison
compare5 n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Eq)
      (\_ -> Lt)
      m)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Gt)
      (\m' -> compare5 n' m')
      m)
    n

eq_dec1 :: Prelude.Integer -> Prelude.Integer -> Sumbool
eq_dec1 =
  eq_dec0

eq_dec2 :: Prelude.Integer -> Prelude.Integer -> Sumbool
eq_dec2 =
  eq_dec

lt_dec :: Prelude.Integer -> Prelude.Integer -> Sumbool
lt_dec x y =
  let {
   c = compSpec2Type x y
         (let {
           compare10 n m =
             (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
               (\_ ->
               (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                 (\_ -> Eq)
                 (\_ -> Lt)
                 m)
               (\n' ->
               (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                 (\_ -> Gt)
                 (\m' -> compare10 n' m')
                 m)
               n}
          in compare10 x y)}
  in
  case c of {
   CompLtT -> Left;
   _ -> Right}

eqb1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
eqb1 x y =
  case eq_dec2 x y of {
   Left -> Prelude.True;
   Right -> Prelude.False}

type T4 = Prelude.Integer

compare6 :: Prelude.Integer -> Prelude.Integer -> Comparison
compare6 n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Eq)
      (\_ -> Lt)
      m)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Gt)
      (\m' -> compare6 n' m')
      m)
    n

eq_dec3 :: Prelude.Integer -> Prelude.Integer -> Sumbool
eq_dec3 =
  eq_dec

type T5 = Prelude.Integer

compare7 :: Prelude.Integer -> Prelude.Integer -> Comparison
compare7 n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Eq)
      (\_ -> Lt)
      m)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Gt)
      (\m' -> compare7 n' m')
      m)
    n

eq_dec4 :: Prelude.Integer -> Prelude.Integer -> Sumbool
eq_dec4 =
  eq_dec3

eq_dec5 :: Prelude.Integer -> Prelude.Integer -> Sumbool
eq_dec5 =
  eq_dec

lt_dec0 :: Prelude.Integer -> Prelude.Integer -> Sumbool
lt_dec0 x y =
  let {
   c = compSpec2Type x y
         (let {
           compare10 n m =
             (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
               (\_ ->
               (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                 (\_ -> Eq)
                 (\_ -> Lt)
                 m)
               (\n' ->
               (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                 (\_ -> Gt)
                 (\m' -> compare10 n' m')
                 m)
               n}
          in compare10 x y)}
  in
  case c of {
   CompLtT -> Left;
   _ -> Right}

eqb2 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
eqb2 x y =
  case eq_dec5 x y of {
   Left -> Prelude.True;
   Right -> Prelude.False}

flatten_e :: Enumeration -> [] Elt
flatten_e e =
  case e of {
   End -> [];
   More x t r -> (:) x (app (elements t) (flatten_e r))}

data R_bal =
   R_bal_0 T1 Prelude.Integer T1
 | R_bal_1 T1 Prelude.Integer T1 T Tree Prelude.Integer Tree
 | R_bal_2 T1 Prelude.Integer T1 T Tree Prelude.Integer Tree
 | R_bal_3 T1 Prelude.Integer T1 T Tree Prelude.Integer Tree T Tree Prelude.Integer 
 Tree
 | R_bal_4 T1 Prelude.Integer T1
 | R_bal_5 T1 Prelude.Integer T1 T Tree Prelude.Integer Tree
 | R_bal_6 T1 Prelude.Integer T1 T Tree Prelude.Integer Tree
 | R_bal_7 T1 Prelude.Integer T1 T Tree Prelude.Integer Tree T Tree Prelude.Integer 
 Tree
 | R_bal_8 T1 Prelude.Integer T1

data R_remove_min =
   R_remove_min_0 Tree Elt T1
 | R_remove_min_1 Tree Elt T1 T Tree Prelude.Integer Tree ((,) T1 Elt) 
 R_remove_min T1 Elt

data R_merge =
   R_merge_0 Tree Tree
 | R_merge_1 Tree Tree T Tree Prelude.Integer Tree
 | R_merge_2 Tree Tree T Tree Prelude.Integer Tree T Tree Prelude.Integer 
 Tree T1 Elt

data R_concat =
   R_concat_0 Tree Tree
 | R_concat_1 Tree Tree T Tree Prelude.Integer Tree
 | R_concat_2 Tree Tree T Tree Prelude.Integer Tree T Tree Prelude.Integer 
 Tree T1 Elt

data R_inter =
   R_inter_0 Tree Tree
 | R_inter_1 Tree Tree T Tree Prelude.Integer Tree
 | R_inter_2 Tree Tree T Tree Prelude.Integer Tree T Tree Prelude.Integer 
 Tree T1 Prelude.Bool T1 Tree R_inter Tree R_inter
 | R_inter_3 Tree Tree T Tree Prelude.Integer Tree T Tree Prelude.Integer 
 Tree T1 Prelude.Bool T1 Tree R_inter Tree R_inter

data R_diff =
   R_diff_0 Tree Tree
 | R_diff_1 Tree Tree T Tree Prelude.Integer Tree
 | R_diff_2 Tree Tree T Tree Prelude.Integer Tree T Tree Prelude.Integer 
 Tree T1 Prelude.Bool T1 Tree R_diff Tree R_diff
 | R_diff_3 Tree Tree T Tree Prelude.Integer Tree T Tree Prelude.Integer 
 Tree T1 Prelude.Bool T1 Tree R_diff Tree R_diff

data R_union =
   R_union_0 Tree Tree
 | R_union_1 Tree Tree T Tree Prelude.Integer Tree
 | R_union_2 Tree Tree T Tree Prelude.Integer Tree T Tree Prelude.Integer 
 Tree T1 Prelude.Bool T1 Tree R_union Tree R_union

type T6 = Prelude.Integer

compare8 :: Prelude.Integer -> Prelude.Integer -> Comparison
compare8 n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Eq)
      (\_ -> Lt)
      m)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Gt)
      (\m' -> compare8 n' m')
      m)
    n

eq_dec6 :: Prelude.Integer -> Prelude.Integer -> Sumbool
eq_dec6 =
  eq_dec

type Elt0 = Prelude.Integer

type T_ = T1
  -- singleton inductive, whose constructor was Mkt
  
this :: T_ -> T1
this t =
  t

type T7 = T_

mem0 :: Elt0 -> T7 -> Prelude.Bool
mem0 x s =
  mem x (this s)

add6 :: Elt0 -> T7 -> T7
add6 x s =
  add5 x (this s)

remove0 :: Elt0 -> T7 -> T7
remove0 x s =
  remove x (this s)

singleton0 :: Elt0 -> T7
singleton0 =
  singleton

union0 :: T7 -> T7 -> T7
union0 s s' =
  union (this s) (this s')

inter0 :: T7 -> T7 -> T7
inter0 s s' =
  inter (this s) (this s')

diff0 :: T7 -> T7 -> T7
diff0 s s' =
  diff (this s) (this s')

equal0 :: T7 -> T7 -> Prelude.Bool
equal0 s s' =
  equal (this s) (this s')

subset0 :: T7 -> T7 -> Prelude.Bool
subset0 s s' =
  subset (this s) (this s')

empty0 :: T7
empty0 =
  empty

is_empty0 :: T7 -> Prelude.Bool
is_empty0 s =
  is_empty (this s)

elements0 :: T7 -> [] Elt0
elements0 s =
  elements (this s)

choose0 :: T7 -> Option Elt0
choose0 s =
  choose (this s)

fold0 :: (Elt0 -> a1 -> a1) -> T7 -> a1 -> a1
fold0 f s =
  fold f (this s)

cardinal0 :: T7 -> Prelude.Integer
cardinal0 s =
  cardinal (this s)

filter1 :: (Elt0 -> Prelude.Bool) -> T7 -> T7
filter1 f s =
  filter0 f (this s)

for_all0 :: (Elt0 -> Prelude.Bool) -> T7 -> Prelude.Bool
for_all0 f s =
  for_all f (this s)

exists_0 :: (Elt0 -> Prelude.Bool) -> T7 -> Prelude.Bool
exists_0 f s =
  exists_ f (this s)

partition0 :: (Elt0 -> Prelude.Bool) -> T7 -> (,) T7 T7
partition0 f s =
  let {p = partition f (this s)} in (,) (fst p) (snd p)

eq_dec7 :: T7 -> T7 -> Sumbool
eq_dec7 s0 s'0 =
  let {b = equal s0 s'0} in
  case b of {
   Prelude.True -> Left;
   Prelude.False -> Right}

compare9 :: T7 -> T7 -> Comparison
compare9 s s' =
  compare3 (this s) (this s')

min_elt0 :: T7 -> Option Elt0
min_elt0 s =
  min_elt (this s)

max_elt0 :: T7 -> Option Elt0
max_elt0 s =
  max_elt (this s)

natSet_fromList :: ([] Node) -> T7
natSet_fromList l =
  fold_right add6 empty0 l

data AG a =
   AG_empty
 | AG_vertex a
 | AG_overlay (AG a) (AG a)
 | AG_connect (AG a) (AG a)

aG_vertices :: ([] a1) -> AG a1
aG_vertices l =
  fold_right (\x x0 -> AG_overlay x x0) AG_empty (map (\x -> AG_vertex x) l)

aG_edge :: a1 -> a1 -> AG a1
aG_edge a1 a2 =
  AG_connect (AG_vertex a1) (AG_vertex a2)

aG_edges :: ([] ((,) a1 a1)) -> AG a1
aG_edges l =
  fold_right (\x x0 -> AG_overlay x x0) AG_empty
    (map (\x -> aG_edge (fst x) (snd x)) l)

aG_makeGraph :: ([] a1) -> ([] ((,) a1 a1)) -> AG a1
aG_makeGraph vs es =
  AG_overlay (aG_vertices vs) (aG_edges es)

aG_transpose :: (AG a1) -> AG a1
aG_transpose ag =
  case ag of {
   AG_overlay ag1 ag2 -> AG_overlay (aG_transpose ag1) (aG_transpose ag2);
   AG_connect ag1 ag2 -> AG_connect (aG_transpose ag2) (aG_transpose ag1);
   x -> x}

aG_toList :: (AG a1) -> [] a1
aG_toList ag =
  case ag of {
   AG_empty -> [];
   AG_vertex x -> (:) x [];
   AG_overlay ag1 ag2 -> app (aG_toList ag1) (aG_toList ag2);
   AG_connect ag1 ag2 -> app (aG_toList ag1) (aG_toList ag2)}

aG_gmap :: (a1 -> a2) -> (AG a1) -> AG a2
aG_gmap f ag =
  case ag of {
   AG_empty -> AG_empty;
   AG_vertex x -> AG_vertex (f x);
   AG_overlay ag1 ag2 -> AG_overlay (aG_gmap f ag1) (aG_gmap f ag2);
   AG_connect ag1 ag2 -> AG_connect (aG_gmap f ag1) (aG_gmap f ag2)}

aG_mergeVertices :: (a1 -> Prelude.Bool) -> a1 -> (AG a1) -> AG a1
aG_mergeVertices f v ag =
  aG_gmap (\x -> case f x of {
                  Prelude.True -> v;
                  Prelude.False -> x}) ag

aG_bind :: (a1 -> AG a2) -> (AG a1) -> AG a2
aG_bind f ag =
  case ag of {
   AG_empty -> AG_empty;
   AG_vertex x -> f x;
   AG_overlay ag1 ag2 -> AG_overlay (aG_bind f ag1) (aG_bind f ag2);
   AG_connect ag1 ag2 -> AG_connect (aG_bind f ag1) (aG_bind f ag2)}

aG_induce :: (a1 -> Prelude.Bool) -> (AG a1) -> AG a1
aG_induce f ag =
  aG_bind (\a ->
    case f a of {
     Prelude.True -> AG_vertex a;
     Prelude.False -> AG_empty}) ag

aG_removeVertex :: Prelude.Integer -> (AG Prelude.Integer) -> AG
                   Prelude.Integer
aG_removeVertex x ag =
  aG_induce (\y -> negb (eqb x y)) ag

aG_removeEdge :: Prelude.Integer -> Prelude.Integer -> (AG Prelude.Integer)
                 -> AG Prelude.Integer
aG_removeEdge x y ag =
  case ag of {
   AG_overlay ag1 ag2 -> AG_overlay (aG_removeEdge x y ag1)
    (aG_removeEdge x y ag2);
   AG_connect ag1 ag2 -> AG_overlay (AG_connect (aG_removeVertex x ag1)
    (aG_removeEdge x y ag2)) (AG_connect (aG_removeEdge x y ag1)
    (aG_removeVertex y ag2));
   x0 -> x0}

aG_nodeSet :: (AG Prelude.Integer) -> T7
aG_nodeSet ag =
  let {leftAndRight = \ag1 ag2 -> union0 (aG_nodeSet ag1) (aG_nodeSet ag2)}
  in
  case ag of {
   AG_empty -> empty0;
   AG_vertex x -> singleton0 x;
   AG_overlay ag1 ag2 -> leftAndRight ag1 ag2;
   AG_connect ag1 ag2 -> leftAndRight ag1 ag2}

aG_nodeAmount :: (AG Prelude.Integer) -> Prelude.Integer
aG_nodeAmount ag =
  cardinal0 (aG_nodeSet ag)

natList_filterOutOf :: T7 -> ([] Prelude.Integer) -> [] Prelude.Integer
natList_filterOutOf remove1 from =
  filter (\x -> negb (mem0 x remove1)) from

_singleStep :: T7 -> (AG Prelude.Integer) -> T7
_singleStep from ag =
  let {
   leftAndRight = \ag1 ag2 from0 ->
    union0 (_singleStep from0 ag1) (_singleStep from0 ag2)}
  in
  case ag of {
   AG_overlay ag1 ag2 -> leftAndRight ag1 ag2 from;
   AG_connect ag1 ag2 ->
    union0 (leftAndRight ag1 ag2 from)
      (let {lHS = aG_nodeSet ag1} in
       let {rHS = aG_nodeSet ag2} in
       case is_empty0 (inter0 lHS from) of {
        Prelude.True -> empty0;
        Prelude.False -> rHS});
   _ -> empty0}

_upToNStepsCap_rec :: T7 -> T7 -> (AG Prelude.Integer) -> Prelude.Integer ->
                      [] T7
_upToNStepsCap_rec from visited ag n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> [])
    (\n' -> (:) from
    (let {next = _singleStep from ag} in
     let {nextVisited = union0 visited next} in
     case equal0 visited nextVisited of {
      Prelude.True -> [];
      Prelude.False -> _upToNStepsCap_rec next nextVisited ag n'}))
    n

_upToNStepsCap :: T7 -> (AG Prelude.Integer) -> Prelude.Integer -> [] T7
_upToNStepsCap from ag n =
  let {trimmedFrom = inter0 from (aG_nodeSet ag)} in
  _upToNStepsCap_rec trimmedFrom trimmedFrom ag (Prelude.succ n)

aG_BFS :: ([] Prelude.Integer) -> (AG Prelude.Integer) -> [] Prelude.Integer
aG_BFS from ag =
  fold_right (\next acc ->
    app (elements0 next) (natList_filterOutOf next acc)) []
    (_upToNStepsCap (natSet_fromList from) ag (aG_nodeAmount ag))

