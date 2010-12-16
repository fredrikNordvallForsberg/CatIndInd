{-# OPTIONS --no-positivity-check #-} -- F G are strictly positive, but how should Agda know?

module elimtoinit where

open import sigma_DiAlg

mutual
  data A : Set where
    inF : F (A , B) -> A

  data B : A -> Set where
    inG : (x : F (A , B)) -> G ((A , B) , inF) x -> B (inF x)


mutual
  elimF : --(A : Set)(B : A -> Set)
          (P : A -> Set)(Q : (x : A) -> B x -> P x -> Set)
          --(inF : F (A , B) -> A)
          --(inG : (x : F (A , B)) -> G ((A , B) , inF) x -> B (inF x))
          (inFbar : (x : F (A , B)) -> boxF A B P Q x -> P (inF x))
          (inGbar : (x : F (A , B)) -> (y :  G ((A , B) , inF) x) -> (xbar : boxF A B P Q x)
            -> boxG A B P Q inF inFbar x y xbar -> Q (inF x) (inG x y) (inFbar x xbar))
           -> (x : A) -> P x
  elimF P Q inFbar inGbar (inF x) = inFbar x (dmapF A B P Q (elimF P Q inFbar inGbar) (elimG P Q inFbar inGbar) x)


  elimG : --(A : Set)(B : A -> Set)
          (P : A -> Set)(Q : (x : A) -> B x -> P x -> Set)
          --(inF : F (A , B) -> A)
          --(inG : (x : F (A , B)) -> G ((A , B) , inF) x -> B (inF x))
          (inFbar : (x : F (A , B)) -> boxF A B P Q x -> P (inF x))
          (inGbar : (x : F (A , B)) -> (y :  G ((A , B) , inF) x) -> (xbar : boxF A B P Q x)
            -> boxG A B P Q inF inFbar x y xbar -> Q (inF x) (inG x y) (inFbar x xbar))
           -> (x : A) -> (y : B x) -> Q x y (elimF P Q inFbar inGbar x)
  elimG P Q inFbar inGbar (inF x) (inG .x y) = inGbar x y (dmapF A B P Q (elimF P Q inFbar inGbar) (elimG P Q inFbar inGbar) x) (dmapG A B P Q inF inFbar (elimF P Q inFbar inGbar) (elimG P Q inFbar inGbar) x y) 

foldF : (X : Set)(Y : X -> Set)
        (c : F (X , Y) -> X)(d : (x : F (X , Y)) -> G ((X , Y) , c) x -> Y(c(x))) ->
        A -> X
foldF X Y c d = elimF (λ _ → X) (λ _ _ x → Y x) (λ x y → c (trala x y)) (λ x y xbar ybar → d (trala x xbar) (Gmor ((π₁ {A , λ _ → X} , λ x → π₁ { B (π₀ x) , λ _ → Y (π₁ x)}) , refl) (π₀ xbar) (π₀ ybar)))
  where trala : (x : F (A , B)) -> boxF A B (λ _ → X) (λ _ _ x → Y x) x -> F (X , Y)
        trala x y = Fmor (π₁ {A , λ _ → X} , λ x → π₁ { B (π₀ x) , λ _ → Y (π₁ x)}) (π₀ y)

foldG : (X : Set)(Y : X -> Set)
        (c : F (X , Y) -> X)(d : (x : F (X , Y)) -> G ((X , Y) , c) x -> Y(c(x))) ->
        (x : A) -> B(x) -> Y (foldF X Y c d x)
foldG X Y c d = elimG (λ _ → X) (λ _ _ x → Y x) (λ x y → c (trala x y)) (λ x y xbar ybar → d (trala x xbar) (Gmor ((π₁ {A , λ _ → X} , λ x → π₁ { B (π₀ x) , λ _ → Y (π₁ x)}) , refl) (π₀ xbar) (π₀ ybar)))
  where trala : (x : F (A , B)) -> boxF A B (λ _ → X) (λ _ _ x → Y x) x -> F (X , Y)
        trala x y = Fmor (π₁ {A , λ _ → X} , λ x → π₁ { B (π₀ x) , λ _ → Y (π₁ x)}) (π₀ y)

cong2 : {A B C : Set} -> (f : A -> B -> C) -> {x y : A}{x' y' : B} -> x == y -> x' == y'
            -> f x x' == f y y'
cong2 f refl refl = refl

eq1 :  (X : Set)(Y : X -> Set)
       (c : F (X , Y) -> X)(d : (x : F (X , Y)) -> G ((X , Y) , c) x -> Y(c(x))) ->
       (a : F (A , B)) ->
       foldF X Y c d (inF a) == c (Fmor (foldF X Y c d , foldG X Y c d) a)
eq1 X Y c d a = cong c (trans Ffunctorlawcomp (cong2 Fmor refl refl))
