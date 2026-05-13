
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Congruence.Defs
import Mathlib.LinearAlgebra.Quotient.Basic

variable (R : Type) [CommRing R]

variable (M N : Type) [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

variable (p : Submodule R M)

example : M → M → Prop := Submodule.quotientRel p

example : M →ₗ[R] (M ⧸ p) := by exact p.mkQ

example (φ : (M ⧸ p) →ₗ[R] N) : {ψ:M →ₗ[R] N // (p ≤ LinearMap.ker ψ) } := 
  ⟨φ ∘ₗ p.mkQ, by 
    intro x hx
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply] 
    suffices h : Submodule.Quotient.mk (p:=p) x = 0 by
      rw [h]
      simp
    simp only [Submodule.Quotient.mk_eq_zero]
    exact hx
  ⟩

example (φ : (M ⧸ p) →ₗ[R] N) : {ψ : M →ₗ[R] N // p ≤ LinearMap.ker ψ} :=
  ⟨φ ∘ₗ p.mkQ, by
    rw [LinearMap.ker_comp]
    intro x hx
    simp only [Submodule.mem_comap, Submodule.mkQ_apply, LinearMap.mem_ker] 
    rw [ (Submodule.Quotient.mk_eq_zero p).mpr hx ]            
    simp only [map_zero]
    ⟩


