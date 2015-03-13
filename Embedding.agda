module Embedding where

{-

  This file defines the embedding of the effect 
  calculus into the session calculus, embedding
  effect annotations as session types. 

-}

open import Sessions
open import Effects
open Effect
open import Context

open import Data.List hiding (map)

open import Basics
open import Data.Nat
open import Data.Fin
open import Data.Maybe hiding (map)
open import Data.Vec hiding (map;_++_)
open import Relation.Binary.PropositionalEquality using (trans;cong;inspect;[_]) 

{- Embed types -}
interpT : Type -> VType
interpT nat = nat
interpT unit = unit

{- Embed memership witnessess -}
interpMem : forall {Γ τ} -> (mem : τ <: Γ) -> (interpT τ <: (map interpT Γ))
interpMem here = here
interpMem (there mem) = there (interpMem mem)

{- Abstracted interface for embedding various kinds of effect system -}
record Embedding (eff : Effect) : Set where
  field
   -- Interpretation of effect annotations
   interpEff :  (Carrier eff) -> SType 

   purityToEnd : interpEff (I eff) ≡ end
   altToBranch : (f g : Carrier eff) -> 
                    interpEff (_⊕_ eff f g) ≡ ⊕ (("L" , interpEff f) ∷ 
                                                 ("R" , interpEff g) ∷ [])

   -- Interpretation of operations
   opEmbed : (Γ : Context Type) -> (τ : Type) -> (F : Carrier eff) 
          -> (Γ' : Context Type) -> (τ' : Type) -> {G : Carrier eff} 
          -> (op : operations eff (just (Γ' , τ')) Γ τ F) 
          -> (x : eff , Γ' !- τ' , (I eff)) 
          -> (map interpT Γ * (((Em , [ interpT τ ]!∙ end) , [ sess (interpEff (_•_ eff F G)) ]?∙ end), [ sess (interpEff G) ]!∙ end) |- proc)

   -- Interpretation of constants
   constEmbed : (Γ : Context Type) -> (τ : Type) -> (F : Carrier eff) -> {G : Carrier eff} 
            -> (op : operations eff nothing Γ τ F)
            -> (map interpT Γ * (((Em , [ interpT τ ]!∙ end) , [ sess (interpEff (_•_ eff F G)) ]?∙ end), [ sess (interpEff G) ]!∙ end) |- proc)

open Embedding


{- Core intermeddiate embedding -}
{- This definition is very explicit in parts to make it easier to understand -} 
embedInterm : forall  {eff : Effect} {Γ τ} {F G : Carrier eff} {emb : Embedding eff}
                -> (M : eff , Γ !- τ , F)
                -> (map interpT Γ * (((Em , [ interpT τ ]!∙ end) , [ sess (interpEff emb (_•_ eff F G)) ]?∙ end), [ sess (interpEff emb G) ]!∙ end) |- proc)

-- Variables
embedInterm {eff} {Γ = Γ} {G = G} {emb} (var {τ = τ} x) rewrite (left-unit eff {e = G}) = 
   let e = (inr here) !< var {Γ = map interpT Γ} {Σ = Em , end} (interpMem x) >∙ (nil {n = 2})
       esB = _<->∙_ {Γ = map interpT Γ} {S = interpEff emb G} {T = end} (there here) e
       esA = (there (there (there here))) [ here ]∙ esB
   in exchg esA

-- Let binding
embedInterm {eff} {Γ} {F = .(_•_ eff f g)} {G}  {emb} 
     (letb {σ = σ} {τ} {f = f} {g = g} m n) rewrite (symm (assoc eff f g G)) = 
  let m0 = embedInterm {eff = eff} {G = (_•_ eff g G)} {emb = emb} m 
      n0 = embedInterm {eff = eff} {G = G} {emb = emb} n
      n1 = weaken {wS = end} n0
      n2 = here ?[-]∙ n1
      e0 = par m0 n2

      Σ0 = ((((((Em , ([ interpT σ ]!∙ end)) 
                    , ([ sess (interpEff emb (_•_ eff f (_•_ eff g G))) ]?∙ end))
                    , ([ sess (interpEff emb (_•_ eff g G)) ]!∙ end))
                    , ([ interpT τ ]!∙ end))
                    , ([ sess (interpEff emb (_•_ eff g G)) ]?∙ end))
                    , ([ sess (interpEff emb G) ]!∙ end))
                    , ([ interpT σ ]?∙ end)
      e1 = restrict {Σ = Σ0} e0 (th (th (th (th (th (th here)))))) here {refl}
      Σ1 = (((((Em , ([ sess (interpEff emb (_•_ eff f (_•_ eff g G))) ]?∙ end))
                   , ([ sess (interpEff emb (_•_ eff g G)) ]!∙ end))
                   , ([ interpT τ ]!∙ end))
                   , ([ sess (interpEff emb (_•_ eff g G)) ]?∙ end))
                   , ([ sess (interpEff emb G) ]!∙ end))
      e2 = restrict {Σ = Σ1} e1 (th (th (th here))) (th here) {refl}
  in exchgE e2

-- Unit constant
embedInterm {eff} {Γ} {F = .(I eff)} {G} {emb} unit rewrite left-unit eff {e = G} = 
      let esB = _<->∙_ {Γ = map interpT Γ} {S = interpEff emb G} {T = end} here (nil {n = 2}) 
          e = (inr here) !< unit {Σ = Em , end} >∙ esB
          esA = (there (there (there here))) [ there here ]∙ e
      in exchg (exchgE esA)

-- Zero constant
embedInterm {eff} {Γ} {F = .(I eff)} {G} {emb} nzero rewrite left-unit eff {e = G} = 
      let esB = _<->∙_ {Γ = map interpT Γ} {S = interpEff emb G} {T = end} here (nil {n = 2}) 
          e = (inr here) !< nzero {Σ = Em , end} >∙ esB
          esA = (there (there (there here))) [ there here ]∙ e
      in exchg (exchgE esA)

-- Successor operation
embedInterm {eff} {Γ} {G = G}  {emb} (nsucc e) = 
      let ea = embedInterm {eff} {F = I eff} {G = G} {emb} e
          v = nsucc (var {Γ = map interpT Γ , nat} {Σ = Em} here)
          eb = _?[-]∙_ (there here) (_!<_>∙_ (inl here) v (nil {n = 2}))
          e' = par eb ea
      in restrict e' (th (th here)) (th (th here)) {refl}

-- Case
embedInterm {eff} {Γ} {F = .((_•_ eff) f ((_⊕_ eff) g h))} {G} {emb} (case {.Γ} {τ} {f} {g} {h} m n1 n2)  rewrite symm (assoc eff f (_⊕_ eff g h) G) = --  | (dist eff g h G)  = 
       let em = embedInterm {eff} {Γ} {F = f} {G = (_•_ eff ((_⊕_ eff) g h) G)} {emb} m 
           en1 = embedInterm {eff} {Γ} {F = g} {G = G} {emb} n1
           en2 = embedInterm {eff} {Γ , nat} {F = h} {G = G} {emb} n2
           
           ea0 = _!<_>∙_ (inl here) (var {Γ = map interpT Γ , nat} {Σ = Em} here) (nil {n = 2})
           ea1 = _◁[_]∙_ {S = [ nat ]!∙ end} {Ls = "LL" ∷ "RR" ∷ []} here (var {Γ = map interpT Γ , nat} here) ea0
           ea2 = _?[-]∙_ (there here) ea1

           ebA0 = weakenG {wT = nat} (weaken {wS = end} (weaken {wS = end} en1))
           ebA1 = here ?[-]∙ ebA0
           ebA2 = (th here) <->∙ ebA1 
           ebA3 = here ◁ here ∙ ebA2
           ebA4 = restrict ebA3 (th (th (th (th here)))) (there here) {refl}

           ebB0 = weaken {wS = end} (weaken {wS = end} en2)
           ebB1 = here ?[-]∙ ebB0
           ebB2 = (th here) <->∙ ebB1 
           ebB3 = _◁_∙_ {S = ("R" , interpEff emb (_•_ eff h G))} here  (there here) ebB2
           ebB4 = restrict ebB3 (th (th (th (th here)))) (there here) {refl}

           deVec = Cons (exchg ebA4) (Cons (exchg ebB4) [])
           Sii = ("LL" , [ nat ]?∙ end) ∷ ("RR" , [ nat ]?∙ end) ∷ []
           eb0 = _▷[_] {Si = Sii} here deVec 
           eb1 = here [ there here ]∙ (weaken {wS = end} eb0)

           ec0 = par eb1 ea2
           ec1 = par ec0 em

           ec2 = restrict ec1 (th (th (th here))) (th (th here)) {refl}
           ec3 = restrict ec2 (th (th (th (th here)))) (th (th here)) {refl}
           prf = cong (\w -> [ sess w ]!∙ end)
                        (trans (cong (\w -> interpEff emb w) (dist eff g h G))
                                (altToBranch emb (_•_ eff g G) (_•_ eff h G)))
           ec4 = restrict ec3 (th (th here)) here {symm prf}
           ec5 = exchg ec4
       in ec5

{- Top-level embedding -}
embed : forall {eff : Effect} {Γ τ} {F : Carrier eff} {emb : Embedding eff}
               -> (e : eff , Γ !- τ , F)
               -> (map interpT Γ) * ((Em , [ interpT τ ]!∙ end) , interpEff emb F) |- proc
embed {eff} {Γ} {τ} {F} {emb} e = 
          let  -- Perform the intermediate embedding, instantiating the universaly quantified effect G to I
              eI = embedInterm {eff} {Γ} {τ} {F} {G = I eff} {emb} e

              -- Use the right-identity property to turn F • I -> F
              eI1 = cong-coerce (\f -> map interpT Γ * (((Em , [ interpT τ ]!∙ end) , [ sess (interpEff emb f) ]?∙ end) , [ sess (interpEff emb (I eff)) ]!∙ end) |- proc) ((right-unit eff) {e = F}) eI

              -- Use the pure embedding property to turn ⟦ I ⟧ -> end
              p = cong-coerce (\f -> map interpT Γ * (((Em , [ interpT τ ]!∙ end) , [ sess (interpEff emb F) ]?∙ end) , [ sess f ]!∙ end) |- proc) (purityToEnd emb) eI1

              j0 = nil {n = 3}
              j1 = here [ here ]∙ j0
              j2 = _<->∙_ {S = interpEff emb F} (there here) j1
              e0 = par p j2
              e1 = restrict e0 (th (th (th (th here)))) (there here) {refl}
              e2 = restrict e1 (th (th here)) (th here) {refl}
          in e2


          