import Mathlib.Tactic

section review


/-
Here is what we saw last time:

1. Lean can do standard functional programming.
-/

#check [1,2,3]

#check "Hello World!"

/-
2. We will use it exclusively for mathematics and theorem proving.
   This requires translating statments and their proofs into types and terms.
   We have the type `Prop` for propositions.
    We have the type `Type` for types i.e. our *sets*.
    We have the type `Type n` for larger types.

-/

#check ℕ

#check Prop
#check Type 0
#check Type 1
#check Type*



#check (ULift : Type → Type 1)
#check ULift

-- Functions value in `Type` are structured or indexed sets.
#check ℝ → Type

-- Formulas are `functions` valued in `Prop`.
#check ℕ → Prop

-- Identities are an example of propositions.
#check 2 + 3 = 6
#check (fun x y : Nat => x = y)

-- 3. The goal is to use this perspective to define and prove mathematics.
end review


section evennumber
/-
Here is a mathematical statement:
For all natural numbers `m` and `n`, if `n` is even, then `m * n` is even.
-/

-- To express this we use the function `Even`:
#check Even
#print Even


example : ∀ m n : Nat, Even n → Even (m * n) := sorry

/-
A proof is a function.
Domain: A tuple `(m,n, ⟨k, hk⟩  : Even n)`
Codomain: `⟨l, hl⟩ : Even (m * n)`

Naively, we should have `l = m * k` and `hl` should be the combination of `mul_add m k k` and `m * hk`.
Making this naive proof precise is tedious.
-/

set_option linter.unusedVariables false
example : ∀ m n : Nat, Even n → Even (m * n) :=
  fun m n ⟨k, hk⟩ ↦
    ⟨m * k, Eq.trans (congrArg (fun l => m * l) hk) (mul_add m k k)⟩

set_option linter.unusedVariables true

-- Let's try to use tactics.
-- There are many ways we can do this!

example : ∀ m n : Nat, Even n → Even (m * n) := by
  -- Say `m` and `n` are natural numbers, and assume `n = 2 * k`.
  intro m n ⟨k, hk⟩
  -- We need to prove `m * n` is twice a natural number. Let's show it's twice `m * k`.
  use m * k
  -- Substitute for `n`,
  rw [hk]
  -- and now it's obvious.
  ring

example : ∀ m n : Nat, Even n → Even (m * n) :=
  fun m n ⟨k, hk⟩ ↦
    ⟨m * k, by rw [hk, mul_add]⟩


example : ∀ m n : Nat, Even n → Even (m * n) := by
  rintro m n ⟨k, hk⟩; use m * k; rw [hk]; ring

example : ∀ m n : Nat, Even n → Even (m * n) := by
  intros; simp [*, parity_simps]

end evennumber

section tactics
/-

What we want are tactics!
Tactics are built-in functions that allow step-wise manipulation of the goal.
Here are the tactics we will (have) look at today:
* `rfl`
* `rw`
* `intro`
* `exact`
* `apply`
* `have`
* `ring`
-/

-- `rfl` is the reflexivity tactic. It only works when things are literally equal.
example : (2 * 3) + 4 = 10 := by
  rfl

-- Usually we don't write `rfl`, cause it is applied automatically.
-- So `rfl` will not be very relevant for us.

-- `rw` is the rewrite tactic. It replaces one term with another *equal* term.

example {n} (hn : n = 2) : n + 3 = 7 - 2 := by
  rw [hn]

-- To get 2 + 3 = 7 -2 a `rfl` is applied automatically.

-- Very important: `rw` has direction.

example {n} (hn : 2 = n) : n + 3 = 7 - 2 := by
  rw [← hn]

-- We use `←` to rewrite in the other direction.

-- We can also rewrite in the assumption with `at`.

example {n m k} (hn : n = m  + 2 * k)  (hm : m = 3 * k) :  n = 5 * k := by
  rw [hm] at hn
  rw [← add_mul] at hn
  rw [hn]

-- `intro` is the introduction tactic. It introduces a variable into the context.
-- We use it when we have an implication `→` or  universal quantifier `∀`.

example {n} : n = 2 → n + 3 = 5 := by
  intro hn
  rw [hn]

-- `exact` is the exact tactic. It closes the goal with an explicit term.

example (P Q : Prop) (h : P) (k : P → Q): Q := by
  exact k h

-- Note in this case `exact` is redundant. However, it is useful as part of larger proofs.

-- `apply` is the application tactic. It applies a function to the goal.
-- It is a *backwards* tactic, that reduces the goal.

example (P R Q : Prop) (h : P) (k : P → Q) (l : Q → R): R := by
  apply l
  apply k
  exact h

-- Note, again here we can do things more directly.

example (P R Q : Prop) (h : P) (k : P → Q) (l : Q → R): R := l (k h)

-- But this won't be the case later on.

-- `have` is the have tactic. It introduces a new assumption into the context.
-- It is alsoa  *backwards* tactic.

example (P R Q : Prop) (h : P) (k : P → Q) (l : Q → R): R := by
  have q := k h
  have r := l q
  exact r

-- `ring` is the ring tactic. It simplifies computational expressions in rings.

example (a b c : ℝ) : a * (b - c) = b * a - a * c := by
  ring

end tactics

section algebra

-- In sections we can define variables, which are valid throughout the section.
variable (a b c : ℝ)

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc a b c
#check mul_comm a
#check mul_comm

example (ha : a = b * c) : b * a * c = a * a := by
  rw [mul_comm]
  rw [← mul_assoc]
  rw [mul_comm c b]
  rw [ha]

-- Checkout exercises for more practice with `rw`.

end algebra


section more_logic

/-
We saw tactics for basic propositions.
Of course, most propositions involve more logic.
Let's see how tactics appear there.
-/

-- As we saw, we use `intro` to prove implications.

example (a b : ℝ) : a > 0 → b > 0 → a + b > 0 := by
  intro ha hb
  exact add_pos ha hb

example (P Q R : Prop) : (P → Q) → (P → Q → R) → P → R := by
  intros ha hb hc
  exact hb hc (ha hc)

-- For universal quantifiers we also apply  `intro`

example : ∀ a b : ℝ, a + b = b + a := by
  intro a b
  rw [add_comm]

-- To use a universal quantifier, we plug it in.

example (P : ℝ → Prop) (h : ∀ x, P x): P 2 := by
  exact h 2

/-
From the perspective of the system, ∀ is also just a function, however,
the codomain of the value of the function depends on the input.
Here the codomain of an input pair (a,b) is inside the type a + b = b + a
-/


-- If we have an *if and only if*, we use `constructor`
-- to decompose and then prove it.

example (a b : ℝ) : a = b ↔ b = a := by
  constructor
  · intro h
    rw [h]
  · intro h
    rw [h]

/-
To prove a conjunction i.e. *and* we use the `constructor` tactic.
To use a conjunction, we use .1 or .2
We can also use the `obtain` tactic to split the assumption.
-/

example (P Q : Prop) : P ∧ Q → Q := by
  intro h
  obtain ⟨hP, hQ⟩ := h
  exact hQ

example (P Q : Prop) : P ∧ Q → Q := by
  intro h
  exact h.2

example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  constructor
  · exact h.2
  · exact h.1


/-
To prove disjunction i.e. *or* we use the `left` or `right` tactic.
Depending on which side we want to prove.
-/

example (P Q : Prop) : P → P ∨ Q := by
  intro h
  left
  exact h

/-
On the other side, if we want to assume a disjunction, then we have to be more careful.
Here we use `rcases` to separate the cases.
-/

example (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  rcases h with hP | hQ
  · right
    exact hP
  · left
    exact hQ

/-
To prove an existential quantifier, we use `use` and then provide a witness.
If we assume extensional quantifiers, we can use `obtain` to split the assumption.
-/

example (P : ℝ → Prop) (h : ∀ x, P x) : ∃ x, P x := by
  use 2
  exact h 2

-- The `use` tactic automatically tries to use available assumptions.

example (P : ℝ → Prop) (h : ∀ x, P x) : ∃ x, P x := by
  have h2 : P 2 := h 2
  use 2

example (P Q : ℝ → Prop) (h : ∃ x, P x ∧ Q x) : ∃ x, P x := by
  obtain ⟨x, hP, hQ⟩ := h
  use x

end more_logic

section tricks

/-
We now saw some basic tactics.

If we know the steps of a proof and the relevant lemmas, theorems, ...
then tactics are very powerful.

What if we don't even know the relevant input?

Here are some tricks for that:

* Press `F12` on relevant definition to go to source file
* `#loogle`
* `#moogle`
* `#check`
* `unfold`
* `simp?`
-/

-- Pressing `F12` on a definition is a good way to learn definitions.

#check ℕ

-- Moogle and loogle search the internet for suggestions (Empfehlungen, Vorschläge).
#moogle "The sum of two even numbers is even."

#loogle "Existential"

/-
One can also directly check the relevant websites:
https://loogle.lean-lang.org/
https://www.moogle.ai/
-/


-- `#check` similarly allows us to understand definitions.

-- Inside proofs we can also ue the `unfold` tactic, to better understand definitions.

example (a b : ℕ ) : Even a → Even b → Even (a + b) := by
  intro ha hb
  -- Let's say I don't know what `Even` means.
  unfold Even
  unfold Even at ha
  unfold Even at hb
  -- Now I can see very explicitly what `Even` means and can continue.
  obtain ⟨k, hk⟩ := ha
  obtain ⟨l, hl⟩ := hb
  use k + l
  rw [hk, hl]
  ring

/-
`simp?`,  is a tactic that tries to suggest simplifications.
More on this next time!
-/


end tricks
