import Mathlib.Tactic

-- Let's do some basic tactics exercises.

section rw

/-
In this section, only use the `rw` tactic.
You will also need the following functions: -/
#check mul_comm
#check mul_assoc

example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [← mul_assoc]

example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]
  rw [mul_assoc]
  rw [mul_comm c a]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc]
  rw [mul_comm a b]
  rw [mul_assoc]

example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_comm a b]
  rw [mul_assoc]
  rw [mul_comm a c]
  rw [← mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [← mul_assoc]
  rw [mul_comm a b]
  rw [mul_assoc]
  rw [mul_comm a c]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc]
  rw [mul_comm a b]
  rw [mul_assoc]

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [← mul_assoc]
  rw [h]
  rw [h']
  rw [mul_assoc]

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a b c]
  rw [h]
  rw [← mul_assoc]

-- For this next exercise, you should also need:
#check sub_self

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp]
  rw [hyp']
  rw [mul_comm a b]
  rw [sub_self]

end rw

section logic

/-
For the following exercises, use the tactics:
- `intro`
- `exact`
- `constructor`
- `left`
- `right`
- `apply`
- `obtain`
- `rcases`
- `rw`
-/

example (P Q R S : Prop) (h : P → R) (h' : Q → S) : P ∧ Q → R ∧ S := by
  intro k
  obtain ⟨kP, kQ⟩ := k
  constructor
  · exact h kP
  · exact h' kQ


example (α : Type) (P Q : α → Prop) : (∃ x, P x ∧ Q x) → ∃ x, Q x ∧ P x := by
  intro ⟨h,hP,hQ⟩
  use h

-- For the next exercise you also need the function
#check le_trans

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  · apply h₀
  · apply h₁

-- For the next exercise, you can also use `ring`.
-- You will also need the following:
#check add_zero

example (a b : ℝ) : a = b ↔ b - a = 0 := by
 constructor
 · intro h
   rw[h]
   ring
 · intro h
   rw[← add_zero a]
   rw[← h]
   ring

example (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
 constructor
 · intro h
   obtain ⟨hP, hQ|hR⟩ := h
   · left
     constructor
     · exact hP
     · exact hQ
   · right
     constructor
     · exact hP
     · exact hR
 · intro h
   rcases h with hPQ | hPR
   · obtain ⟨hP, hQ⟩ := hPQ
     constructor
     · exact hP
     · left
       exact hQ
   · obtain ⟨hP, hR⟩ := hPR
     constructor
     · exact hP
     · right
       exact hR

example (α : Type) (P Q : α → Prop) : (∀ x, P x ∧ Q x) ↔ ((∀ x, Q x) ∧ (∀ x, P x)) := by
 constructor
 · intro h
   constructor
   · intro x
     obtain ⟨Px,Qx⟩ := h x
     use Qx
   · intro x
     obtain ⟨Px,Qx⟩ := h x
     use Px
 · intro h
   intro x
   obtain ⟨hQ, hP⟩ := h
   constructor
   · exact hP x
   · exact hQ x

end logic
