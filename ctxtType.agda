--{-# OPTIONS --termination-depth=1 #-}

module ctxtType where


mutual
  
  data Ctxt : Set where
    ε : Ctxt
    _◃_ : (Γ : Ctxt) -> Type Γ -> Ctxt
  
  data Type : Ctxt -> Set where
    ι : (Γ : Ctxt) -> Type Γ
    Π : (Γ : Ctxt) -> (A : Type Γ) -> (B : Type (Γ ◃ A)) -> Type Γ





open import Data.Sum
open import Data.Product
open import Data.Unit

ArgA : (A : Set)(B : A -> Set) -> Set
ArgA A B = ⊤ ⊎ (Σ[ Γ ∶ A ] B Γ)

ArgB : (A : Set)(B : A -> Set)(c : ArgA A B -> A) -> ArgA A B -> Set
ArgB A B c x = ⊤ ⊎ (Σ[ σ ∶ B (c x) ] B (c (inj₂ ((c x) , σ))))

mutual
  data Ctx : Set where
    c : ArgA Ctx Ty -> Ctx
  
  data Ty : Ctx -> Set where
    d : (x : ArgA Ctx Ty) -> ArgB Ctx Ty c x -> Ty (c x)

elimCrude : (P : Ctx -> Set) ->
            (f : (x : ArgA Ctx Ty) -> P (c x)) ->
            (x : Ctx) -> P x
elimCrude P f (c x) = f x

ε' : Ctx
ε' = c (inj₁ _)

_◃'_ : (Γ : Ctx) -> Ty Γ -> Ctx
Γ ◃' A = c (inj₂ (Γ , A))

ι' : (Γ : Ctx) -> Ty Γ
ι' (c x) = d x (inj₁ tt)

Π' : (Γ : Ctx) -> (A : Ty Γ) -> (B : Ty (Γ ◃' A)) -> Ty Γ
Π' (c x) A B = d x (inj₂ (A , B))


mutual

  elimC : (P : Ctxt -> Set)(Q : (Γ : Ctxt) -> Type Γ -> P Γ -> Set) ->
          (Pε : P ε) ->
          (Pcons : (Γ : Ctxt) -> (PΓ : P Γ) -> (A : Type Γ) -> Q Γ A PΓ -> P (Γ ◃ A))
          (Qι : (Γ : Ctxt) -> (PΓ : P Γ) -> Q Γ (ι Γ) PΓ) ->
          (QΠ : (Γ : Ctxt) -> (PΓ : P Γ) -> (A : Type Γ) -> (QA : Q Γ A PΓ) ->
                  (B : Type (Γ ◃ A)) -> (QB : Q (Γ ◃ A) B (Pcons Γ PΓ A QA)) -> Q Γ (Π Γ A B) PΓ)
          (Γ : Ctxt) -> P Γ
  elimC P Q Pε Pcons Qι QΠ ε = Pε
  elimC P Q Pε Pcons Qι QΠ (Γ ◃ A) = Pcons Γ (elimC P Q Pε Pcons Qι QΠ Γ)
                                           A (elimT P Q Pε Pcons Qι QΠ Γ A)

  elimT : (P : Ctxt -> Set)(Q : (Γ : Ctxt) -> Type Γ -> P Γ -> Set) ->
          (Pε : P ε) ->
          (Pcons : (Γ : Ctxt) -> (PΓ : P Γ) -> (A : Type Γ) -> Q Γ A PΓ -> P (Γ ◃ A))
          (Qι : (Γ : Ctxt) -> (PΓ : P Γ) -> Q Γ (ι Γ) PΓ) ->
          (QΠ : (Γ : Ctxt) -> (PΓ : P Γ) -> (A : Type Γ) -> (QA : Q Γ A PΓ) ->
                  (B : Type (Γ ◃ A)) -> (QB : Q (Γ ◃ A) B (Pcons Γ PΓ A QA)) -> Q Γ (Π Γ A B) PΓ)
          (Γ : Ctxt) -> (A : Type Γ) -> Q Γ A (elimC P Q Pε Pcons Qι QΠ Γ)
  elimT P Q Pε Pcons Qι QΠ Γ (ι .Γ) = Qι Γ (elimC P Q Pε Pcons Qι QΠ Γ)
  elimT P Q Pε Pcons Qι QΠ Γ (Π .Γ A B) = QΠ Γ (elimC P Q Pε Pcons Qι QΠ Γ)
                                             A (elimT P Q Pε Pcons Qι QΠ Γ A)
                                             B (elimT P Q Pε Pcons Qι QΠ (Γ ◃ A) B)


mutual

  _++_ : Ctxt -> Ctxt -> Ctxt
  x ++ ε = x
  x ++ (Γ ◃ A) = (x ++ Γ) ◃ wk Γ A x

  wk : (Γ : Ctxt) -> (A : Type Γ) -> (x : Ctxt) -> Type (x ++ Γ)
  wk Γ (ι .Γ) x = ι (x ++ Γ)
  wk Γ (Π .Γ A B) x = Π (x ++ Γ) (wk Γ A x) (wk (Γ ◃ A) B x)





module withFold where

  A : Set
  A = Ctx -> Ctx

  B : A -> Set
  B Γ++ = (x : Ctx) -> Ty (Γ++ x)

  inA : ArgA A B -> A
  inA (inj₁ _) Δ = Δ
  inA (inj₂ (a , b)) Δ = a Δ ◃' b Δ

  inB : (x : ArgA A B) -> ArgB A B inA x -> B (inA x)
  inB Γ (inj₁ tt) y = ι' (inA Γ y)
  inB Γ (inj₂ (g , h )) y = Π' (inA Γ y) (g y) (h y)


module withElim where

       P : Ctxt -> Set
       P _ = Ctxt -> Ctxt

       Q : (Γ : Ctxt) -> Type Γ -> P Γ -> Set
       Q Γ A Γ++ = (x : Ctxt) -> Type (Γ++ x)

       Pε : P ε
       Pε x = x

       Pcons : (Γ : Ctxt) -> (PΓ : P Γ) -> (A : Type Γ) -> Q Γ A PΓ -> P (Γ ◃ A)
       Pcons Γ Γ++ A wk[Γ,A] x = (Γ++ x) ◃ wk[Γ,A] x

       Qι : (Γ : Ctxt) -> (PΓ : P Γ) -> Q Γ (ι Γ) PΓ
       Qι Γ Γ++ x = ι (Γ++ x)

       QΠ : (Γ : Ctxt) -> (PΓ : P Γ) -> (A : Type Γ) -> (QA : Q Γ A PΓ) ->
               (B : Type (Γ ◃ A)) -> (QB : Q (Γ ◃ A) B (Pcons Γ PΓ A QA)) -> Q Γ (Π Γ A B) PΓ
       QΠ Γ Γ++ A wk[Γ,A] B wk[Γ◃A,B] x = Π (Γ++ x) (wk[Γ,A] x) (wk[Γ◃A,B] x)


       _++'_ : Ctxt -> Ctxt -> Ctxt
       x ++' Γ = elimC P Q Pε Pcons Qι QΠ Γ x -- x and Γ flipped

       wk' : (Γ : Ctxt) -> (A : Type Γ) -> (x : Ctxt) -> Type (x ++' Γ)
       wk' = elimT P Q Pε Pcons Qι QΠ

data simpleTy : Set where
  nat : simpleTy
  _⇒_ : simpleTy -> simpleTy -> simpleTy

data simpleCtxt : Set where
  nil : simpleCtxt
  _,_ : simpleCtxt -> simpleTy -> simpleCtxt

infixl 5 _,_

mutual

  forgetC : Ctxt -> simpleCtxt
  forgetC ε = nil
  forgetC (Γ ◃ A) = (forgetC Γ) , (forgetT Γ A)

  forgetT : (Γ : Ctxt) -> Type Γ -> simpleTy
  forgetT Γ (ι .Γ) = nat
  forgetT Γ (Π .Γ A B) = forgetT Γ A ⇒ forgetT (Γ ◃ A) B




test = forgetC (((ε ◃ ι _) ◃ (ι _) ) ++ (ε ◃ Π _ (ι _) (ι _)))

module admissibleTimes where

  mutual
    
    data Ctxt'' : Set where
      ε : Ctxt''
      _◃_ : (Γ : Ctxt'') -> Type'' Γ -> Ctxt''
  
    data Type'' : Ctxt'' -> Set where
      ι : (Γ : Ctxt'') -> Type'' Γ
      Π : (Γ : Ctxt'') -> (A : Type'' Γ) -> (B : Type'' (Γ ◃ A)) -> Type'' Γ
      times : (Γ : Ctxt'') -> (A : Type'' Γ) -> (B : Type'' Γ) -> Type'' Γ


  mutual
 
    _++''_ : Ctxt'' -> Ctxt'' -> Ctxt''
    x ++'' ε = x
    x ++'' (Γ ◃ A) = (x ++'' Γ) ◃ wk'' Γ A x

    wk'' : (Γ : Ctxt'') -> (A : Type'' Γ) -> (x : Ctxt'') -> Type'' (x ++'' Γ)
    wk'' Γ (ι .Γ) x = ι (x ++'' Γ)
    wk'' Γ (Π .Γ A B) x = Π (x ++'' Γ) (wk'' Γ A x) (wk'' (Γ ◃ A) B x)
    wk'' Γ (times .Γ A B) x = times (x ++'' Γ) (wk'' Γ A x) (wk'' Γ B x)

  comm : (Γ Σ : Ctxt'') ->  Type'' (Σ ++'' Γ) -> Type'' (Γ ++'' Σ)
  comm Σ Γ (ι .(Γ ++'' Σ)) = ι (Σ ++'' Γ)
  comm Σ Γ (Π .(Γ ++'' Σ) A B) = Π (Σ ++'' Γ) (comm Σ Γ A) {!comm!}
  comm Σ Γ (times .(Γ ++'' Σ) A B) = times (Σ ++'' Γ) (comm Σ Γ A) (comm Σ Γ B)



  times'' : (Γ Σ : Ctxt'') -> (A : Type'' Γ) -> (B : Type'' Σ) -> Type'' (Σ ++'' Γ)
  times'' Γ Σ A B = times (Σ ++'' Γ) (wk'' Γ A Σ) (comm Σ Γ (wk'' Σ B Γ))
