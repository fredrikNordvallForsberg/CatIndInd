module sigma_DiAlg where

open import Relation.Binary.HeterogeneousEquality
--open import Relation.Binary.PropositionalEquality
--open import Relation.Binary.PropositionalEquality.TrustMe

_∘_ : {X Y Z : Set} -> (Y -> Z) -> (X -> Y) -> X -> Z
(f ∘ g) x = f (g x)

record FamSet : Set1 where
  constructor _,_ 
  field 
    A : Set
    B : A -> Set

open FamSet

U : FamSet -> Set
U (A , B) = A

record FamSetMor (X Y : FamSet) : Set where
  constructor _,_
  field
   f : (A X) -> (A Y)
   g : (x : A X) -> (B X x) -> (B Y (f x))
open FamSetMor

Umor : {X Y : FamSet} -> FamSetMor X Y -> U X -> U Y
Umor (f , g) = f

_∘FAM_ : {X Y Z : FamSet} -> FamSetMor Y Z -> FamSetMor X Y -> FamSetMor X Z
(f , g) ∘FAM (f' , g') = (f ∘ f') , λ x → g (f' x) ∘ (g' x)

data Σ (AB : FamSet) : Set where
  _,_ : (x : A AB) -> B AB x -> Σ AB

ΣMor : {A B : FamSet} -> FamSetMor A B -> Σ A -> Σ B
ΣMor (f , g) (x , y) = (f x) , g x y

_×_ : Set -> Set -> Set
A × B = Σ (A , λ _ → B )

π₀ : {AB : FamSet} -> Σ AB -> A AB
π₀ (a , b) = a

π₁ : {AB : FamSet} -> (x : Σ AB) -> B AB (π₀ x)
π₁ (a , b) = b

--subst : {A : Set} -> (P : A -> Set) -> {x y : A} -> x == y -> P x -> P y
--subst P refl z = z

--trans : {A : Set} -> {x y z : A} -> x == y -> y == z -> x == z
--trans refl refl = refl

symm : {A : Set} -> {x y : A} -> x ≅ y -> y ≅ x
symm refl = refl

,-cong : {A : Set}{B : A -> Set} -> {x x' : A}{y : B x}{y' : B x'} ->
         (p : x ≅ x') -> y ≅ y' -> _≅_ {A = Σ (A , B)} (x , y) {B = Σ (A , B)} (x' , y')
,-cong refl refl =  refl

--cong : {A B : Set} -> (f : A -> B) -> {x y : A} -> x == y -> f x == f y
--cong f refl = refl

ΣFAM : (A : Set)(B : A -> Set)(P : A -> Set)(Q : (x : A) -> B x -> P x -> Set) -> FamSet
ΣFAM A B P Q = (Σ (A , P) , λ x → Σ (B (π₀ x) , λ b → Q (π₀ x) b (π₁ x)))


--should be parameters
postulate
  F : FamSet -> Set
  Fmor : {X Y : FamSet} -> FamSetMor X Y -> F X -> F Y
  ---------
  Ffunctorlawid : {X : FamSet}{x : F X} -> Fmor ((λ x → x) , (λ x y → y)) x ≅ x
  Ffunctorlawcomp : {X Y Z : FamSet}{f : FamSetMor Y Z}{g : FamSetMor X Y}{x : F X}
                     -> ((Fmor f) ∘ (Fmor g)) x ≅ Fmor (f ∘FAM g) x





boxF : (A : Set)(B : A -> Set)(P : A -> Set)(Q : (x : A) -> B x -> P x -> Set) -> F (A , B) -> Set
boxF A B P Q x =  Σ (F (ΣFAM A B P Q) , λ y → Fmor {Y = (A , B)} (record { f = π₀; g = λ x → π₀ {AB = (B (π₀ x) , λ b → Q (π₀ x) b (π₁ x))}}) y ≅ x )
  

φ : {A : Set}{B : A -> Set}{P : A -> Set}{Q : (x : A) -> B x -> P x -> Set} ->
    F (ΣFAM A B P Q) -> Σ (F (A , B) , (boxF A B P Q))
φ x = (Fmor (record { f = π₀; g = λ x y → π₀ y }) x) , (x , refl)


ψ : {A : Set}{B : A -> Set}{P : A -> Set}{Q : (x : A) -> B x -> P x -> Set} ->
    Σ (F (A , B) , (boxF A B P Q)) -> F (ΣFAM A B P Q)
ψ (._ , (x , refl)) = x


φ∘ψ=id : {A : Set}{B : A -> Set}{P : A -> Set}{Q : (x : A) -> B x -> P x -> Set} ->
         (x : Σ (F (A , B) , (boxF A B P Q))) -> φ {A} {B} {P} {Q} (ψ {A} {B} {P} {Q} x) ≅ x
φ∘ψ=id (._ , (x , refl)) = refl

ψ∘φ=id : {A : Set}{B : A -> Set}{P : A -> Set}{Q : (x : A) -> B x -> P x -> Set} ->
         (x : F (ΣFAM A B P Q)) -> ψ {A} {B} {P} {Q} (φ {A} {B} {P} {Q} x) ≅ x
ψ∘φ=id x = refl


record DiAlgFU : Set1 where
  constructor _,_
  field
    X : FamSet
    FUf : F X -> U X
open DiAlgFU

V : DiAlgFU -> FamSet
V (X  , f) = X


record FUMor (A B : DiAlgFU) : Set where
  constructor _,_
  field
    h : FamSetMor (X A) (X B)
    .eq : {x : F (X A)} -> ((Umor h) ∘ FUf A) x ≅ (FUf B ∘ Fmor h) x

Vmor : {X Y : DiAlgFU} -> FUMor X Y -> FamSetMor (V X) (V Y)
Vmor (h , eq) = h

postulate
  G : (X : DiAlgFU) -> F (V X) -> Set
  Gmor : {X Y : DiAlgFU} -> (h : FUMor X Y) -> (x : F (V X)) -> G X x -> G Y (Fmor (Vmor h) x)
  ---------
--  Gfunctorlawid : {X : DiAlgFU}{x : F (V X)}{y : G X x} -> Gmor (((λ x → x) , (λ x y → y)) , refl) x y ≅ y
--  Gfunctorlawcomp : {X Y Z : FamSet}{f : FamSetMor Y Z}{g : FamSetMor X Y}{x : F X}
--                     -> ((Fmor f) ∘ (Fmor g)) x == Fmor (f ∘FAM g) x


G^ : DiAlgFU -> FamSet
G^ X = (F (V X)) , G X


boxG : (A : Set)(B : A -> Set)(P : A -> Set)(Q : (x : A) -> B x -> P x -> Set) ->
       (inF : F (A , B) -> A) ->
       (inFbar : (x : F (A , B)) -> boxF A B P Q x -> P (inF x)) ->
       (x : F (A , B)) -> G ((A , B) , inF) x -> boxF A B P Q x -> Set
boxG A B P Q inF inFbar x b y
  = Σ (G (ΣFAM A B P Q , (ΣMor (inF , inFbar) ∘ φ {Q = Q})) (π₀ y) ,
       λ z → subst (G ((A , B) , inF)) (π₁ y) (Gmor ((_,_ π₀ (λ x → π₀ {AB = (B (π₀ x) , λ b → Q (π₀ x) b (π₁ x))})) , refl) (π₀ y) z) ≅ b)

φG : {A : Set}{B : A -> Set}{P : A -> Set}{Q : (x : A) -> B x -> P x -> Set} ->
     {inF : F (A , B) -> A} ->
     {inFbar : (x : F (A , B)) -> boxF A B P Q x -> P (inF x)} ->
    (x : F (ΣFAM A B P Q)) -> G (ΣFAM A B P Q , (ΣMor (inF , inFbar) ∘ φ {Q = Q})) x
      -> Σ (G ((A , B) , inF) (π₀ (φ {Q = Q} x)) , λ y → boxG A B P Q inF inFbar (π₀ (φ {Q = Q} x)) y (π₁ (φ {Q = Q} x)) )
φG x y = Gmor ((π₀ , λ _ → π₀) , refl) x y , (y , refl)




ψG : {A : Set}{B : A -> Set}{P : A -> Set}{Q : (x : A) -> B x -> P x -> Set} ->
     {inF : F (A , B) -> A} ->
     {inFbar : (x : F (A , B)) -> boxF A B P Q x -> P (inF x)} ->
    (x : F (ΣFAM A B P Q)) -> Σ (G ((A , B) , inF) (π₀ (φ {Q = Q} x)) , λ y → boxG A B P Q inF inFbar (π₀ (φ {Q = Q} x)) y (π₁ (φ {Q = Q} x)) )
       -> G (ΣFAM A B P Q , (ΣMor (inF , inFbar) ∘ φ {Q = Q})) x
ψG x (._ , (y , refl)) = y


postulate 
  conjecture : {A : Set} -> A



dmapF : (A : Set)(B : A -> Set)(P : A -> Set)(Q : (x : A) -> B x -> P x -> Set) ->
        (f : (x : A) -> P x) ->
        (g : (x : A) -> (y : B x) -> Q x y (f x)) ->
        (x : F (A , B)) -> boxF A B P Q x
dmapF A B P Q f g x = (Fmor ((λ x → x , f x) , λ x y → y , g x y) x) ,
                      trans (trans Ffunctorlawcomp refl) Ffunctorlawid

dmapG : (A : Set)(B : A -> Set)(P : A -> Set)(Q : (x : A) -> B x -> P x -> Set) ->
        (inF : F (A , B) -> A) ->
        (inFbar : (x : F (A , B)) -> boxF A B P Q x -> P (inF x)) ->
        (f : (x : A) -> P x) ->
        (g : (x : A) -> (y : B x) -> Q x y (f x)) ->
        (x : F (A , B)) -> (y : G ((A , B) , inF) x)
          -> boxG A B P Q inF inFbar x y (dmapF A B P Q f g x)
dmapG A B P Q inF inFbar f g x y = (Gmor ((((λ x → x , f x)) , λ x y → y , g x y) , λ {x} → ,-cong (cong inF (symm (trans Ffunctorlawcomp Ffunctorlawid))) conjecture) x y) , conjecture

