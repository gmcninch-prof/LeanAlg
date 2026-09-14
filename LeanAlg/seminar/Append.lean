import Mathlib.Tactic

/-! module docstring
-/

def a : List Nat :=  [ 1 , 2 , 3 ] 


def b : List String := [ "a", "bc" ]

def c : List Nat := [500, 100000]

#eval a.length
#eval b.length



def append {α : Type} (xs ys : List α) : List α :=
  match xs with
  | []      => ys
  | z :: zs => z :: append zs ys

  
#eval append a c

#eval append b b 

-- a theorem, and its proof

theorem append_length {α : Type} (xs ys : List α) :
    (append xs ys).length = xs.length + ys.length := by
  induction xs with
  | nil => simp [append]
  | cons z zs ih => 
      simp only [append, List.length_cons]
      rw [ih]
      ring
      


      

theorem append_assoc {α : Type} (xs ys zs : List α) :
    append (append xs ys) zs = append xs (append ys zs) := by
  induction xs with
  | nil => simp only [append]
  | cons x xs ih => simp only [append, ih]

theorem append_assoc' {α : Type} (xs ys zs : List α) :
    append (append xs ys) zs = append xs (append ys zs) := by
  induction xs with
  | nil => rw [ append, append ]
  | cons x xs ih => simp only [ ih, append ]
