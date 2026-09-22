import Mathlib

/- foo bar -/

theorem modus_ponens {p q : Prop} : (f: p → q) → (h : p)  → q :=
  fun f h => f h

theorem modus_ponens' {p q : Prop} : (f: p → q) → (h : p)  → q := by
  intro f h 
  exact f h

example {p q : Prop} (hp : p) (hq : q) : p ∧ q :=
  And.intro hp hq

#check And.intro

variable (p q : Prop)
example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq

variable (x y : ℝ)


example {p q : Prop} (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp
  · exact hq

#check absurd

example : ¬ (1 = 0) := by norm_num

example : ¬ (1 = 0) := by
  intro h        -- h : 1 = 0, goal is now False
  
  exact absurd h (by norm_num)


example (a b : ℝ) (h : a = b) (k : a ≠ b) : 1 = 0 :=
  absurd h k 

#check False.elim

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  have ⟨h₀, h₁⟩ := h
  contrapose! h₁
  exact le_antisymm h₀ h₁


