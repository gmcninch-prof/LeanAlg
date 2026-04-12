

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


/-- An symmetric map from `ι → M` to `N`, denoted `M [Σ^ι]→ₗ[R] N`,
is a multilinear map that stays the same when its arguments are permuted. -/
structure SymmetricMap extends MultilinearMap R (fun _ : ι => M) N where
  /-- The map is symmetric: if the arguments of `v` are permuted, the result does not change. -/
  map_perm_apply' (v : ι → M) (e : Perm ι) : (toFun fun i ↦ v (e i)) = toFun v


@[inherit_doc]
notation M:arg " [Σ^" ι "]→ₗ[" R "] " N:arg => SymmetricMap R M N ι


namespace SymmetricMap

variable {R M N P ι} (f f₁ f₂ g g₁ g₂ : M [Σ^ι]→ₗ[R] N) (v x y : ι → M)

instance : FunLike (M [Σ^ι]→ₗ[R] N) (ι → M) N where
  coe f := f.toFun
  coe_injective' f g h := by
    rcases f with ⟨⟨_, _, _⟩, _⟩
    rcases g with ⟨⟨_, _, _⟩, _⟩
    congr



--example : Module R (SymmetricMap R M N ι) := inferInstance


@[inherit_doc]
notation M:arg " [Σ^" ι "]→ₗ[" R "] " N:arg => SymmetricMap R M N ι


def SymmUMP (R M N ι : Type) [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Fintype ι] : 
  (SymmetricPower R ι M →ₗ[R] N) ≃ₗ[R] MultilinearMap R (fun (i:ι) => M) N := by sorry
  

structure form (k V ι : Type) [Field k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V]
    [Fintype ι] where
  carrier : SymmetricPower k ι (Module.Dual k V)
  eval : V → k
  -- properties of eval


