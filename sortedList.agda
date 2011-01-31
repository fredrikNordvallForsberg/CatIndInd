module sortedList where

open import Data.Nat 
open import Relation.Nullary
open import Relation.Binary as RB
open import Data.Empty
open import Data.Unit using (⊤)

-------------------------------------------------------------------------
-- Introduction rules
-------------------------------------------------------------------------
mutual
  data SList : Set where
    [] : SList
    _::_〈_ : (x : ℕ) -> (ys : SList) -> x ≤L ys → SList

  data _≤L_ (n : ℕ) : SList -> Set where
    triv : n ≤L []
    cons : {x : ℕ} -> {ys : SList} -> {p : x ≤L ys} -> 
           (n ≤ x) -> n ≤L ys -> n ≤L (x :: ys 〈 p)
-------------------------------------------------------------------------

-------------------------------------------------------------------------
-- Example of sorted and non-sorted list
-------------------------------------------------------------------------
ex1 : SList
ex1 = 0 :: 1 :: 2 :: 3 :: [] 〈 triv 〈 cons (s≤s (s≤s z≤n)) triv 〈 cons (s≤s z≤n) 
                                 (cons (s≤s z≤n) triv) 〈 cons z≤n (cons z≤n (cons z≤n triv)) 

--non-ex2 : SList 
--non-ex2 = 2 :: 1 :: 3 :: [] 〈 triv 〈 cons (s≤s z≤n) triv  〈 cons {!!} (cons (s≤s (s≤s z≤n)) triv)

-------------------------------------------------------------------------

-------------------------------------------------------------------------
-- Elimination rules
-------------------------------------------------------------------------
mutual
  elim : (P : SList -> Set)(Q : (n : ℕ) -> (ys : SList) -> n ≤L ys -> P ys -> Set) ->
         (P[] : P [])
         (P:: : (x : ℕ) -> (ys : SList) -> (p : x ≤L ys) -> (pp : P ys) -> Q x ys p pp 
             -> P (x :: ys 〈 p)) ->
         (Q[] : (n : ℕ) -> Q n [] triv P[])
         (Q:: : (n : ℕ) -> {x : ℕ} -> {ys : SList} -> {p : x ≤L ys} -> 
               (n ≤ x) -> (q' : n ≤L ys) -> (q : n ≤L (x :: ys 〈 p)) ->
               (pp : P ys) -> (qq : Q x ys p pp) -> (qqq : Q n ys q' pp)
                 -> Q n (x :: ys 〈 p) q (P:: x ys p pp qq))
         (ys : SList) -> P ys
  elim P Q P[] P:: Q[] Q:: [] = P[]
  elim P Q P[] P:: Q[] Q:: (x :: ys 〈 p) = P:: x ys p (elim P Q P[] P:: Q[] Q:: ys)
                                              (elim' P Q P[] P:: Q[] Q:: x ys p)

  elim' : (P : SList -> Set)(Q : (n : ℕ) -> (ys : SList) -> n ≤L ys -> P ys -> Set) ->
         (P[] : P [])
         (P:: : (x : ℕ) -> (ys : SList) -> (p : x ≤L ys) -> (pp : P ys) -> Q x ys p pp 
             -> P (x :: ys 〈 p)) ->
         (Q[] : (n : ℕ) -> Q n [] triv P[])
         (Q:: : (n : ℕ) -> {x : ℕ} -> {ys : SList} -> {p : x ≤L ys} -> 
               (n ≤ x) -> (q' : n ≤L ys) -> (q : n ≤L (x :: ys 〈 p)) ->
               (pp : P ys) -> (qq : Q x ys p pp) -> (qqq : Q n ys q' pp)
                 -> Q n (x :: ys 〈 p) q (P:: x ys p pp qq))
         (n : ℕ) -> (ys : SList) -> (p : n ≤L ys)-> Q n ys p (elim P Q P[] P:: Q[] Q:: ys)
  elim' P Q P[] P:: Q[] Q:: n .[] triv = Q[] n
  elim' P Q P[] P:: Q[] Q:: n .(x :: ys 〈 p) (cons {x} {ys} {p} n<x n<ys)
    = Q:: n n<x n<ys (cons n<x n<ys) (elim P Q P[] P:: Q[] Q:: ys) 
          (elim' P Q P[] P:: Q[] Q:: x ys p) (elim' P Q P[] P:: Q[] Q:: n ys n<ys)
-------------------------------------------------------------------------

-------------------------------------------------------------------------
-- Some lemmas about ℕ and, and transitivity of ≤L
-------------------------------------------------------------------------
trans : ∀ {k m n} -> k ≤ m -> m ≤ n -> k ≤ n
trans = RB.IsDecTotalOrder.trans (RB.DecTotalOrder.isDecTotalOrder Data.Nat.decTotalOrder)

≤L-trans : ∀ {x y} -> (zs : SList) -> x ≤ y -> y ≤L zs -> x ≤L zs
≤L-trans [] x<y all = triv
≤L-trans (y' :: ys 〈 p) x<y (cons y<y' y<ys) = cons (trans x<y y<y') (≤L-trans ys x<y y<ys)

≤L-trans' : ∀ {x y} -> (zs : SList) -> x ≤ y -> y ≤L zs -> x ≤L zs
≤L-trans' {x} {y} ys x<y y<ys = elim' (λ _ → ⊤) (λ n zs p _ → x ≤ n -> x ≤L zs) _
                                                (λ _ _ _ _ _ → _) (λ _ _ → triv)
                                      (λ y {y'} {ys} {p} y<y' x<ys x<y'::ys _ qq qqq x<y
                                           → cons (trans x<y y<y') (qqq x<y))
                                       y ys y<ys x<y

¬x<y→y<x : {x y : ℕ} -> (x ≤ y -> ⊥) -> y ≤ x
¬x<y→y<x {zero} {suc n} p = ⊥-elim (p z≤n)
¬x<y→y<x {y = zero} p = z≤n
¬x<y→y<x {suc n} {suc m} p = s≤s (¬x<y→y<x (λ x → p (s≤s x)))
-------------------------------------------------------------------------

-------------------------------------------------------------------------
-- Insert using pattern matching
-------------------------------------------------------------------------
mutual
  insert : (x : ℕ) -> SList -> SList
  insert x [] = x :: [] 〈 triv
  insert x (y :: ys 〈 p) with x ≤? y
  ... | yes q =  x :: y :: ys 〈 p 〈 (cons q (≤L-trans ys q p))
  ... | no ¬q = y :: (insert x ys) 〈 lemma (¬x<y→y<x ¬q) p

  lemma : ∀ {x y ys} -> y ≤ x -> y ≤L ys -> y ≤L (insert x ys)
  lemma {x} {y} {[]} y≤x y≤ys = cons y≤x y≤ys
  lemma {x} {y} {y' :: ys 〈 p} y≤x (cons y≤y' y≤ys) with x ≤? y'
  ... | yes q = cons y≤x (cons y≤y' y≤ys)
  ... | no ¬q = cons y≤y' (lemma {x} {y} {ys} y≤x y≤ys)
-------------------------------------------------------------------------

-------------------------------------------------------------------------
-- and translated to using pure eliminators
-------------------------------------------------------------------------
P : SList -> Set
P ys = (n : ℕ) -> SList

Q : (y : ℕ) -> (ys : SList) -> y ≤L ys -> P ys -> Set
Q y ys p insert[_,ys] = (x : ℕ) -> y ≤ x ->  y ≤L insert[_,ys] x

P[] : P []
P[] x = x :: [] 〈 triv

P:: : (x : ℕ) -> (ys : SList) -> (p : x ≤L ys) -> (pp : P ys) -> Q x ys p pp 
             -> P (x :: ys 〈 p)
P:: y ys p insert[_,ys] lemma[_,ys,p] x with x ≤? y 
... | yes q = x :: y :: ys 〈 p 〈 cons q (≤L-trans ys q p)
... | no ¬q = y :: (insert[_,ys] x) 〈 lemma[_,ys,p] x (¬x<y→y<x ¬q)

Q[] : (n : ℕ) -> Q n [] triv P[]
Q[] y x y<x = cons y<x triv

Q:: : (n : ℕ) -> {x : ℕ} -> {ys : SList} -> {p : x ≤L ys} -> 
     (n ≤ x) -> (q' : n ≤L ys) -> (q : n ≤L (x :: ys 〈 p)) ->
     (pp : P ys) -> (qq : Q x ys p pp) -> (qqq : Q n ys q' pp)
        -> Q n (x :: ys 〈 p) q (P:: x ys p pp qq)
Q:: y {y'} {ys} {p} y<y' y<ys y<y'::ys insert[_,ys] lemma[_,ys,p] lemma[_,ys,y<ys] x y<x with x ≤? y'
... | yes q = cons y<x (cons y<y' y<ys)
... | no ¬q = cons y<y' (lemma[_,ys,y<ys] x y<x)

insert' : (x : ℕ) -> SList -> SList
insert' x ys = elim P Q P[] P:: Q[] Q:: ys x

lemma' : ∀ {x y ys} -> y ≤ x -> y ≤L ys -> y ≤L (insert' x ys)
lemma' {x} {y} {ys} y<x y<ys = elim' P Q P[] P:: Q[] Q:: y ys y<ys x y<x
-------------------------------------------------------------------------

-------------------------------------------------------------------------
-- an example to see that it works
-------------------------------------------------------------------------
data List : Set where
  ε : List
  _::_ : ℕ -> List -> List

forget : SList -> List
forget [] = ε
forget (x :: ys 〈 y) = x :: (forget ys)

forget' : SList -> List
forget' = elim (λ _ → List) (λ _ _ _ _ → ⊤) ε (λ x ys p forget[ys] _ → x :: forget[ys])
               (λ _ → _) (λ _ _ _ _ _ _ _ → _) 

ex3 : List
ex3 = forget' (insert' 5 (insert' 6 (insert' 2 (insert' 7 (insert' 3 [])))))
-------------------------------------------------------------------------
