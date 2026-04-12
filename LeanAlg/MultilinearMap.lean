

import Mathlib

--noncomputable section

open MultilinearMap

open SymmetricPower

open PiTensorProduct

open Equiv

universe u u' u₁ u₂ u₃ v w w'


variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
  (N : Type w) [AddCommGroup N] [Module R N]
  (P : Type w') [AddCommGroup P] [Module R P]
  (ι : Type u') (ι' : Type u₁) (ι'' : Type u₂)

  
example (m : M) : (Module.Dual R M) →ₗ[R] R := 
  Module.Dual.eval R M m
  
example (m : M) (φ : Module.Dual R M) : R := 
  Module.Dual.eval R M m φ


open BigOperators

example [Fintype ι] (φ : Module.Dual R M) : (ι → M) → R := by
  intro f
  exact ∏ i, φ (f i)

example [Fintype ι] (m : M) : (ι → Module.Dual R M) → R := by
  intro φ
  exact ∏ i, (φ i) m



example [Fintype ι] [DecidableEq ι] 
    (m : M) : MultilinearMap R (fun (i:ι) => (Module.Dual R M)) R := by
  apply MultilinearMap.mk
  
  
