module famcwf where
{-
record Σ (A : Set)(B : A -> Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ
-}

data Σ (A : Set)(B : A -> Set) : Set where
  _,_ : (x : A) -> B x -> Σ A B

fst : {A : Set}{B : A -> Set} -> Σ A B -> A
fst (a , b) = a

snd : {A : Set}{B : A -> Set} -> (x : Σ A B) -> B (fst x)
snd (a , b) = b


record ⊤ : Set where

data _==_ {A : Set1} (x : A) : A -> Set where
  refl : x == x

---------------------------------------------------
-- Fam(Set)

record FamSet : Set1 where
 constructor _,_
 field
   A : Set
   B : A -> Set
open FamSet

record _⇒_ (X X' : FamSet) : Set1 where
  constructor _,_
  field
    f : A X -> A X'
    g : (x : A X) -> B X x -> B X' (f x)


_∘_ : {X Y Z : FamSet} -> Y ⇒ Z -> X ⇒ Y -> X ⇒ Z
(f , g) ∘ (f' , g') = (λ x → f (f' x)) , λ x y → g ((f' x)) (g' x y)

id : {X : FamSet} -> X ⇒ X
id = (λ x → x) , (λ x y → y)


-----
idleft : {X Y : FamSet} -> (f : X ⇒ Y) -> (id ∘ f) == f
idleft f = refl

idright : {X Y : FamSet} -> (f : X ⇒ Y) -> (f ∘ id) == f
idright f = refl

assoc : {X Y Z W : FamSet} ->
        (f : Z ⇒ W) ->
        (g : Y ⇒ Z) ->
        (h : X ⇒ Y) ->
        ((f ∘ g) ∘ h) == (f ∘ (g ∘ h))
assoc f g h = refl
------

one : FamSet
one = ⊤ , λ _ → ⊤

! : {X : FamSet} -> X ⇒ one
! = (λ x → _) , (λ x y → _)

-----
!-unique : {X : FamSet} -> (f : X ⇒ one) -> f == !
!-unique f = refl
-- (isn't eta for one wonderful?)
-----

---------------------------------------------------
-- The functor (Ty, Tm) : Fam(Set) -> Fam(Set)

record Ty (XY : FamSet) : Set1 where
  constructor _,_
  field
    ATy : A XY -> Set
    BTy : (x : A XY) -> B XY x -> ATy x -> Set
open Ty

record Tm (XY : FamSet) (AB : Ty XY) : Set1 where
  constructor _,_
  field
    h : (x : A XY) -> ATy AB x
    k : (x : A XY) -> (y : B XY x) -> BTy AB x y (h x)

---------------------------------------------------
-- Morphism part

_[_]Ty : {XY XY' : FamSet} -> (AB : Ty XY') -> (fg : XY ⇒ XY') -> Ty XY
(A , B) [ (f , g) ]Ty = ((λ x → A (f x)) , λ x y → B (f x) (g x y))

_[_]Tm : {XY XY' : FamSet} -> {AB : Ty XY'} -> (hk : Tm XY' AB) -> (fg : XY ⇒ XY') -> Tm XY (AB [ fg ]Ty)
(h , k) [ (f , g) ]Tm = (λ x → h (f x)) , λ x y → k (f x) (g x y)

---------------------------------------------------
-- Comprehension


_∙_ : (Γ : FamSet) -> Ty Γ -> FamSet
(X , Y) ∙ (A , B) = Σ X A , λ x → Σ (Y (fst x)) (λ y → B (fst x) y (snd x))

p : {Γ : FamSet} -> {σ : Ty Γ} -> (Γ ∙ σ) ⇒ Γ
p = fst , λ x → fst

q : {Γ : FamSet} -> {σ : Ty Γ} -> Tm (Γ ∙ σ) (σ [ p {Γ} {σ} ]Ty)
q = snd , λ x → snd

θ : {XY XY' : FamSet}{AB : Ty XY} -> (fg : XY' ⇒ XY) -> (hk : Tm XY' (AB [ fg ]Ty)) -> XY' ⇒ (XY ∙ AB)
θ (f , g) (h , k) = ((λ x → (f x) , (h x)) , λ x y → (g x y) , (k x y))

-----
eqfst : {XY XY' : FamSet}{AB : Ty XY} -> {f : XY' ⇒ XY} -> {M : Tm XY' (AB [ f ]Ty)} ->
               (p {σ = AB} ∘ (θ {AB = AB} f M)) == f
eqfst = refl

eqsnd : {XY XY' : FamSet}{AB : Ty XY} -> {f : XY' ⇒ XY} -> {M : Tm XY' (AB [ f ]Ty)} ->
               (q {σ = AB} [ θ {AB = AB} f M ]Tm) == M
eqsnd = refl
-----

