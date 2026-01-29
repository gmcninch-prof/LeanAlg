

import Mathlib

--noncomputable section

open SymmetricPower

open PiTensorProduct

variable {k : Type} [Field k]

variable {V : Type} [AddCommGroup V] [Module k V] 

variable (ι : Type) [Fintype ι] [DecidableEq ι]

def SymmMultilinear (R M N ι : Type) [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Fintype ι] : 
  Submodule R (MultilinearMap R (fun (i:ι) => M) N) := by sorry


def SymmUMP (R M N ι : Type) [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Fintype ι] : 
  (SymmetricPower R ι M →ₗ[R] N) ≃ₗ[R] MultilinearMap R (fun (i:ι) => M) N := by sorry
  

structure form (k V ι : Type) [Field k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V]
    [Fintype ι] where
  carrier : SymmetricPower k ι (Module.Dual k V)
  eval : V → k
  -- properties of eval

example : PiTensorProduct k (fun (i:iota) => V) -> V := sorry
