{-# OPTIONS --no-positivity-check #-} -- F G are strictly positive, but how should Agda know?
{-# OPTIONS --no-termination-check #-} -- elim applied to smaller arguments etc

module simple where

--should be parameters
postulate
  F : (X : Set)(Y : X -> Set) -> Set
  G : (X : Set)(Y : X -> Set) -> F X Y -> Set

mutual
  data A : Set where
    c : F A B -> A

  data B : A -> Set where
    d : (x : F A B) -> G A B x -> B (c x)

-- to be filled in
-- should be taking A as parameter as well
postulate
  boxF : (P : A -> Set)(Q : (a : A) -> B a -> P a -> Set) ->
         F A B -> Set
  boxG : (P : A -> Set)(Q : (a : A) -> B a -> P a -> Set) ->
         (x : F A B) -> G A B x -> boxF P Q x -> Set

  dmapF : (P : A -> Set)(Q : (a : A) -> B a -> P a -> Set) ->
          (f : (a : A) -> P a) -> (g : (a : A) -> (b : B a) -> Q a b (f a)) ->
          (x : F A B) -> boxF P Q x
  dmapG : (P : A -> Set)(Q : (a : A) -> B a -> P a -> Set) ->
          (f : (a : A) -> P a) -> (g : (a : A) -> (b : B a) -> Q a b (f a)) ->
          (x : F A B) -> (y : G A B x) -> boxG P Q x y (dmapF P Q f g x)

mutual
  elimF : (P : A -> Set)(Q : (a : A) -> B a -> P a -> Set) ->
          (cbar : (x : F A B) -> boxF P Q x -> P (c x)) ->
          (dbar : (x : F A B) -> (y : G A B x) -> (xbar : boxF P Q x)
                     -> boxG P Q x y xbar -> Q (c x) (d x y) (cbar x xbar)) ->
          (x : A) -> P x
  elimF P Q cbar dbar (c x) = cbar x (dmapF P Q f g x)
        where
          f = elimF P Q cbar dbar
          g = elimG P Q cbar dbar

  elimG : (P : A -> Set)(Q : (a : A) -> B a -> P a -> Set) ->
          (cbar : (x : F A B) -> boxF P Q x -> P (c x)) ->
          (dbar : (x : F A B) -> (y : G A B x) -> (xbar : boxF P Q x)
                     -> boxG P Q x y xbar -> Q (c x) (d x y) (cbar x xbar)) ->
          (x : A) -> (y : B x) -> Q x y (elimF P Q cbar dbar x)
  elimG P Q cbar dbar (c x) (d .x y) = dbar x y (dmapF P Q f g x) (dmapG P Q f g x y)
        where
          f = elimF P Q cbar dbar
          g = elimG P Q cbar dbar
