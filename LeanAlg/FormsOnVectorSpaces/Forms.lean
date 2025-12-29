import Mathlib

noncomputable section

open SymmetricPower

variable {k : Type} [Field k]

variable {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

variable (ι : Type) [Fintype ι] [DecidableEq ι]

def form (k V ι : Type) [Field k] [AddCommGroup V] [Module k V] :=
  SymmetricPower k ι (Module.Dual k V)

#check SymmetricPower k ι (Module.Dual k V)

example (f : ι -> Module.Dual k V) : form k V ι := by
  exact ⨂ₛ[k] i, f i

--def eval (phi : )

-- def eval (phi : form k V ι) (v : V) : k :=
--   match phi with
--   |
