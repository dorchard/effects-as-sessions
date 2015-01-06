module Embedding where

{-

  This file defines the embedding of the effect 
  calculus into the session calculus, embedding
  effect annotations as session types. 

-}

open import Sessions
open import Effects
open import Context

open import Data.List hiding (map)

open import Basics
open import Data.Nat
open import Data.Fin
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

{- The following two lemmas are used in the pure embedding -}
-- If the composition of two effects is pure, then each effect is also pure.
emptyInverseL : forall {f g} -> (f ++ g ≡ pure) -> f ≡ pure
emptyInverseL {[]} refl = refl
emptyInverseL {x ∷ f} ()

emptyInverseR : forall {f g} -> (f ++ g ≡ pure) -> g ≡ pure
emptyInverseR {[]} refl = refl
emptyInverseR {x ∷ f} ()

{- Structural transformations on session terms -}
postulate
  weaken : forall {Γ Σ wS pt} -> (e : Γ * Σ |- pt) -> Γ * (Σ , wS) |- pt
  exchg : forall {Γ Σ S T pt} -> (e : Γ * ((Σ , S), T) |- pt) -> Γ * ((Σ , T) , S) |- pt
  weakenE : forall {Γ Σ S T pt} -> (e : Γ * (Σ , S) |- pt) -> Γ * ((Σ , T), S) |- pt
  
{- Specialised embedding for a pure a term -}
embedPure' : forall {Γ τ f}
                  (e : stEff , Γ !- τ , f) -> (purity : f ≡ pure)
               -> (map interpT Γ * Em , [ interpT τ ]!∙ end |- proc)

embedPure' (var x) refl = (inl here) !< var {Σ = Em} (interpMem x) >∙ (nil {n = 1})
embedPure' {f = .(F ++ G)} (letb {σ = σ} {τ} {F} {G} m n) p =

      let m0 = embedPure' m (emptyInverseL p)
          n0 = embedPure' n (emptyInverseR {f = F} {g = G} p)
          n1 = weaken {wS = end} n0
          n2 = here ?[-]∙ n1
          e0 = par m0 n2
          e1 = restrict {Σ = ((Em , ([ interpT σ ]!∙ end)) , ([ interpT τ ]!∙ end)) , ([ interpT σ ]?∙ end)} e0 here (there here) {refl}
      in e1

embedPure' (op Put e) ()
embedPure' (const Get) ()
embedPure' unit p = (inl here) !< unit {Σ = Em} >∙ (nil {n = 1})
embedPure' nzero p = (inl here) !< nzero {Σ = Em} >∙ (nil {n = 1})
embedPure' {Γ} (nsucc e) p = 
                        let e0 = embedPure' e p 
                            e1 = (inl here) !< nsucc {Σ = Em , end} (var {Γ = map interpT Γ , nat} here) >∙ (nil {n = 1}) 
                            e2 = (there here) ?[-]∙ e1
                            ep = par e0 e2
                            ep' = restrict ep here (there here) {refl}
                        in ep'

{- Top-level pure embedding -}
embedPure : forall {Γ τ} -> (e : stEff , Γ !- τ , []) 
                         -> (map interpT Γ * Em , [ interpT τ ]!∙ end |- proc)
embedPure e = embedPure' e refl

{- Embedding of state effect annotations as session types -}
interpEff : List StateEff -> SType
interpEff [] = end
interpEff (Get t ∷ xs) = ⊕ (("get" , ([ interpT t ]?∙ (interpEff xs))) ∷ []) 
interpEff (Put t ∷ xs) = ⊕ (("put" , ([ interpT t ]!∙ (interpEff xs))) ∷ [])

{- Core intermeddiate embedding -}
{- This definition is very explicit in parts to make it easier to understand -} 
embedInterm : forall {Γ τ F G} 
                -> (M : stEff , Γ !- τ , F)
                -> (map interpT Γ * ((Em , [ interpT τ ]!∙ end) , [ sess (interpEff (F ++ G)) ]?∙ [ sess (interpEff G) ]!∙ end) |- proc)

-- Variables
embedInterm {Γ = Γ} {G = G} (var {τ = τ} x) = 
   let esB = _<->∙_ {Γ = map interpT Γ} {S = interpEff G} {T = end} here (nil {n = 1}) 
       e = (inr here) !< var {Γ = map interpT Γ} {Σ = Em , end} (interpMem x) >∙ esB
       esA = (there (there here)) [ there here ]∙ e
   in esA  

-- Let binding
embedInterm {Γ} {F = .(f ++ g)} {G} (letb {σ = σ} {τ} {f = f} {g = g} m n) rewrite (symm (assoc-list {a = f} {b = g} {c = G})) = 
  let m0 = embedInterm {G = (g ++ G)} m 
      
      n0 = embedInterm {G = G} n
      n1 = weaken {wS = end} n0
      n2 = here ?[-]∙ n1

      j0 = _<->∙_ {S = interpEff G} here (nil {n = 3})
      j1 = (there (there here)) [ here ]∙ j0
      j2 = _<->∙_ {S = interpEff (g ++ G)} here j1
      j3 = (there (there (there here))) [ here ]∙ j2
      j4 = _<->∙_ {S = interpEff (f ++ g ++ G)} here j3
      j5 = (there (there (there here))) [ here ]∙ j4

      e0 = par (par m0 n2) j5

      Σ0 = (((((((Em , ([ interpT σ ]!∙ end))
                     , ([ sess (interpEff (f ++ g ++ G)) ]?∙ ([ sess (interpEff (g ++ G)) ]!∙ end)))
                     , ([ interpT τ ]!∙ end))
                     , ([ sess (interpEff (g ++ G)) ]?∙ ([ sess (interpEff G) ]!∙ end)))
                     , ([ interpT σ ]?∙ end))
                     , ([ sess (interpEff (g ++ G)) ]!∙ ([ sess (interpEff G) ]?∙ end)))
                     , ([ sess (interpEff (f ++ g ++ G)) ]!∙ ([ sess (interpEff (g ++ G)) ]?∙ end)))
                     , ([ sess (interpEff (f ++ g ++ G)) ]?∙ ([ sess (interpEff G) ]!∙ end))
      
      e1 = restrict {Σ = Σ0} e0 (th (th (th (th (th (th (th here)))))))
                                (th (th (th here))) {refl}
      Σ1 = (((((Em , ([ sess (interpEff (f ++ g ++ G)) ]?∙ ([ sess (interpEff (g ++ G)) ]!∙ end)))
                   , ([ interpT τ ]!∙ end))
                   , ([ sess (interpEff (g ++ G)) ]?∙ ([ sess (interpEff G) ]!∙ end)))
                   , ([ sess (interpEff (g ++ G)) ]!∙ ([ sess (interpEff G) ]?∙ end)))
                   , ([ sess (interpEff (f ++ g ++ G)) ]!∙ ([ sess (interpEff (g ++ G)) ]?∙ end)))
                   , ([ sess (interpEff (f ++ g ++ G)) ]?∙ ([ sess (interpEff G) ]!∙ end))

      e2 = restrict {Σ = Σ1} e1 (th (th (th (th (th here))))) (th here) {refl}
      e3 = restrict e2 (th (th here)) (th here) {refl}

  in e3
  
-- Put operation
embedInterm {Γ = Γ} {F = .(Put τ ∷ [])} {G = G} (op {τ' = τ} Put e) = 
       let  F = (Put τ ∷ G)
            e0 = embedPure e
            
            ed = _<->∙_ {S = interpEff G} here (nil {n = 1})
            ee = (inr here) !< unit {Γ = map interpT (Γ , τ)} {Σ = Em , end} >∙ ed
            ef = (inl (there here)) !< var {Σ = Em , end} here >∙ ee
            S = [ interpT τ ]!∙ (interpEff G)
            eg = _◁_∙_ {Si = ("put" , S) ∷ []} here here ef
            ei = (there here) ?[-]∙ eg
            ek = (there (there (there here))) [ (there here) ]∙ ei
            el = par e0 ek

            F' = sess (interpEff F)

            Σ1 = (((Em , ([ interpT τ ]!∙ end)) 
                       , ([ unit ]!∙ end))
                       , ([ interpT τ ]?∙ end))
                       , ([ F' ]?∙ ([ sess (interpEff G) ]!∙ end))

            en = restrict {Σ = Σ1} el (th (th (th here))) (th here) {refl}
       in en

-- Get operation
embedInterm {Γ} {G = g} (const {τ = τ} Get) = 
       let esB = _<->∙_ {Γ = map interpT (Γ , τ)} {S = interpEff g} {T = end} here (nil {n = 1}) 
           e0 = (inr here) !< var {Γ = map interpT (Γ , τ)} {Σ = Em , end} here >∙ esB
           e1 = (there here) ?[-]∙ e0
           S = [ interpT τ ]?∙ (interpEff g)
           e2 = _◁_∙_ {Si = ("get" , S) ∷ []} here here e1
           esA = (there (there here)) [ here ]∙ e2
       in esA

-- Unit constant
embedInterm {Γ} {F = .[]} {G} unit rewrite right-unit-list {e = G} = 
      let esB = _<->∙_ {Γ = map interpT Γ} {S = interpEff G} {T = end} here (nil {n = 1}) 
          e = (inr here) !< unit {Σ = Em , end} >∙ esB
          esA = (there (there here)) [ there here ]∙ e
      in esA

-- Zero constant
embedInterm {Γ} {F = .[]} {G} nzero rewrite right-unit-list {e = G} = 
      let esB = _<->∙_ {Γ = map interpT Γ} {S = interpEff G} {T = end} here (nil {n = 1}) 
          e = (inr here) !< nzero {Σ = Em , end} >∙ esB
          esA = (there (there here)) [ there here ]∙ e
      in esA

-- Successor operation
embedInterm {Γ} {G = G} (nsucc e) = 
      let esB = _<->∙_ {Γ = map interpT Γ} {S = interpEff G} {T = end} here (nil {n = 1}) 
          e =  weakenE {S = ([ nat ]!∙ end)} {T = [ sess (interpEff G) ]!∙ end} 
                   (embedPure (nsucc e))
          e' = weakenE {S = ([ nat ]!∙ end)} {T = interpEff G} e
          esA = (there (there here)) [ there here ]∙ e'
      in esA

{- Top-level embedding -}
embed : forall {Γ τ F}
               -> (e : stEff , Γ !- τ , F)
               -> (map interpT Γ) * ((Em , [ interpT τ ]!∙ end) , interpEff F) |- proc
embed {Γ} {τ} {F} e = 
          let p = cong-coerce (\f -> map interpT Γ * ((Em , ([ interpT τ ]!∙ end)) , ([ sess (interpEff f) ]?∙ ([ sess end ]!∙ end))) |- proc) ((Effect.right-unit stEff) {e = F}) (embedInterm {G = []} e) 
              j0 = nil {n = 2}
              j1 = here [ here ]∙ j0
              j2 = _<->∙_ {S = interpEff F} here j1
              e0 = par p j2
              e1 = restrict e0 (there (there here)) (there here) {refl}
          in e1

