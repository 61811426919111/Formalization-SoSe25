/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Set.Basic

/-!
# Inclusion-exclusion principle

This file proves several variants of the inclusion-exclusion principle.

The inclusion-exclusion principle says that the sum/integral of a function over a finite union of
sets can be calculated as the alternating sum over `n > 0` of the sum/integral of the function over
the intersection of `n` of the sets.

By taking complements, it also says that the sum/integral of a function over a finite intersection
of complements of sets can be calculated as the alternating (wechselnd) sum over `n ≥ 0` of the
sum/integral of the function over the intersection of `n` of the sets.

By taking the function to be constant `1`, we instead get a result about the cardinality/measure of
the sets.

## Main declarations

Per the above explanation, this file contains the following variants of inclusion-exclusion:
* `Finset.inclusion_exclusion_sum_biUnion`: Sum of a function over a finite (endlich, begrenzt)
union of sets
* `Finset.inclusion_exclusion_card_biUnion`: Cardinality of a finite union of sets
* `Finset.inclusion_exclusion_sum_inf_compl`: Sum of a function over a finite intersection of
  complements of sets
* `Finset.inclusion_exclusion_card_inf_compl`: Cardinality of a finite intersection of
  complements of sets

## TODO

* Use (a slight variant of) `Finset.prod_indicator_biUnion_sub_indicator` to prove the integral
  version of inclusion-exclusion.
* Prove that truncating (abbrechend) the series alternatively gives an upper/lower bound to the
true value.
-/

assert_not_exists Field

namespace Finset
variable {ι α G : Type*} [DecidableEq α] [AddCommGroup G] {s : Finset ι}

lemma prod_indicator_biUnion_sub_indicator (hs : s.Nonempty) (S : ι → Finset α) (a : α) :
    ∏ i ∈ s, (Set.indicator (s.biUnion S) 1 a - Set.indicator (S i) 1 a) = (0 : ℤ) := by
  by_cases ha : a ∈ s.biUnion S
  · obtain ⟨i, hi, ha⟩ := mem_biUnion.1 ha
    exact prod_eq_zero hi <| by simp [*, -coe_biUnion]
  · obtain ⟨i, hi⟩ := hs
    have ha : a ∉ S i := fun h ↦ ha <| subset_biUnion_of_mem _ hi h
    exact prod_eq_zero hi <| by simp [*, -coe_biUnion]

/-- **Inclusion-exclusion principle** for the sum of a function over a union.

The sum of a function `f` over the union of the `S i` over `i ∈ s` is the alternating sum of the
sums of `f` over the intersections of the `S i`. -/

theorem inclusion_exclusion_sum_biUnion (s : Finset ι) (S : ι → Finset α) (f : α → G) :
    ∑ a ∈ s.biUnion S, f a = ∑ t : s.powerset.filter (·.Nonempty),
      (-1) ^ (#t.1 + 1) • ∑ a ∈ t.1.inf' (mem_filter.1 t.2).2 S, f a := by
  classical
  rw [← sub_eq_zero]
  calc
    ∑ a ∈ s.biUnion S, f a - ∑ t : s.powerset.filter (·.Nonempty),
      (-1) ^ (#t.1 + 1) • ∑ a ∈ t.1.inf' (mem_filter.1 t.2).2 S, f a
      = ∑ t : s.powerset.filter (·.Nonempty),
          (-1) ^ #t.1 • ∑ a ∈ t.1.inf' (mem_filter.1 t.2).2 S, f a +
          ∑ t ∈ s.powerset.filter (¬ ·.Nonempty), (-1) ^ #t • ∑ a ∈ s.biUnion S, f a := by
      simp [sub_eq_neg_add, ← sum_neg_distrib, filter_eq', pow_succ]
    _ = ∑ t ∈ s.powerset, (-1) ^ #t •
          if ht : t.Nonempty then ∑ a ∈ t.inf' ht S, f a else ∑ a ∈ s.biUnion S, f a := by
      rw [← sum_attach (filter ..)]; simp [sum_dite]
    _ = ∑ a ∈ s.biUnion S, (∏ i ∈ s, (1 - Set.indicator (S i) 1 a : ℤ)) • f a := by
      simp only [Int.reduceNeg, prod_sub, sum_comm (s := s.biUnion S), sum_smul, mul_assoc]
      congr! with t
      split_ifs with ht
      · obtain ⟨i, hi⟩ := ht
        simp only [prod_const_one, prod_indicator_apply]
        simp only [smul_sum, Set.indicator, Set.mem_iInter, mem_coe, Pi.one_apply, mul_ite, mul_one,
          mul_zero, ite_smul, zero_smul, sum_ite, not_forall, sum_const_zero, add_zero]
        congr
        aesop
      · obtain rfl := not_nonempty_iff_eq_empty.1 ht
        simp
    _ = ∑ a ∈ s.biUnion S, (∏ i ∈ s,
          (Set.indicator (s.biUnion S) 1 a - Set.indicator (S i) 1 a) : ℤ) • f a := by
      congr! with t; rw [Set.indicator_of_mem ‹_›, Pi.one_apply]
    _ = 0 := by
      obtain rfl | hs := s.eq_empty_or_nonempty <;>
        simp [-coe_biUnion, prod_indicator_biUnion_sub_indicator, *]


/- trunkierte Version -/
open BigOperators
open Finset

lemma sub_nonneg_ge  {γ : Type u} [AddGroup γ] [LE γ] [AddRightMono γ] {d e : γ} :
d ≥ e ↔ d-e ≥ 0 := by simp

/- Tipps and To-Do

Idealerweise gibt es (oder du kannst beweisen) das wenn S eine Menge ist und P und Q zwei Propositionen
für S sind, und P impliziert Q dann ist S.filter P eine Teilmenge von S.filter Q.
In unserem Falle sollte die Implikation eigentlich klar sein, es ist ein Fall von (A und B) impliziert A,
was immer stimmt.

-/

theorem subset {α : Type*} (p q : α → Prop) [DecidablePred p] [DecidablePred q] (s : Finset α) (h: ∀ x, p x → q x) :
s.filter p ⊆ s.filter q := by
intro x hx
simp at hx
sorry

variable {ι α G : Type*} [DecidableEq α]
  [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G] (r k : ℕ) (evenk : 2 ∣ k) (oddr : ¬ 2 ∣ r)

theorem incl_excl_sum_biUnion_trunk_even (s : Finset ι) (S : ι → Finset α) (f : α → G) (hf : ∀ a, f a ≥ 0):
   ∑ a ∈ s.biUnion S, f a ≥ ∑ ⟨t, tcond⟩ : s.powerset.filter (fun t => t.Nonempty ∧ Finset.card t ≤ k),
      (-1) ^ (#t + 1) • ∑ a ∈ t.inf' (mem_filter.1 tcond).2.1 S, f a := by
  classical
  rw [sub_nonneg_ge]
  calc
   ∑ a ∈ s.biUnion S, f a -
      ∑ ⟨t, tcond⟩ : s.powerset.filter (fun t => t.Nonempty ∧ Finset.card t ≤ k),
      (-1) ^ (#t + 1) • ∑ a ∈ t.inf' (mem_filter.1 tcond).2.1 S, f a =
      ∑ t : s.powerset.filter (·.Nonempty),
      (-1) ^ (#t.1 + 1) • ∑ a ∈ t.1.inf' (mem_filter.1 t.2).2 S, f a -
      ∑ ⟨t, tcond⟩ : s.powerset.filter (fun t => t.Nonempty ∧ Finset.card t ≤ k),
      (-1) ^ (#t + 1) • ∑ a ∈ t.inf' (mem_filter.1 tcond).2.1 S, f a := by rw [inclusion_exclusion_sum_biUnion]
  _=  ∑ t : s.powerset.filter (·.Nonempty),
      (-1) ^ (#t.1 + 1) • ∑ a ∈ t.1.inf' (mem_filter.1 t.2).2 S, f a +
      ∑ ⟨t, tcond⟩ : s.powerset.filter (fun t => t.Nonempty ∧ Finset.card t ≤ k),
      (-1) ^ #t • ∑ a ∈ t.inf' (mem_filter.1 tcond).2.1 S, f a := by simp [pow_succ]
  _=  - ∑ t : s.powerset.filter (·.Nonempty),
      (-1) ^ #t.1 • ∑ a ∈ t.1.inf' (mem_filter.1 t.2).2 S, f a +
      ∑ ⟨t, tcond⟩ : s.powerset.filter (fun t => t.Nonempty ∧ Finset.card t ≤ k),
      (-1) ^ #t • ∑ a ∈ t.inf' (mem_filter.1 tcond).2.1 S, f a  := by simp [pow_succ]
  _=  ∑ ⟨t, tcond⟩ : s.powerset.filter (fun t => t.Nonempty ∧ Finset.card t ≤ k),
      (-1) ^ #t • ∑ a ∈ t.inf' (mem_filter.1 tcond).2.1 S, f a -
      ∑ t : s.powerset.filter (·.Nonempty),
      (-1) ^ #t.1 • ∑ a ∈ t.1.inf' (mem_filter.1 t.2).2 S, f a := by simp [← sub_eq_neg_add]
  _=  ∑ t ∈ s.powerset, (-1) ^ #t •
          if ht : fun t => t.Nonempty ∧ Finset.card t ≤ k then ∑ a ∈ t.inf' ht S, f a - f a
          else ∑ a ∈ t.1.inf' (mem_filter.1 t.2).2 S, - f a := by
      rw [← sum_attach (filter ..)]; simp [sum_dite]


theorem incl_excl_sum_biUnion_trunk_odd (s : Finset ι) (S : ι → Finset α) (f : α → G):
   ∑ a ∈ s.biUnion S, f a ≤ ∑ ⟨t, tcond⟩ : s.powerset.filter (fun t => t.Nonempty ∧ Finset.card t ≤ r),
      (-1) ^ (#t + 1) • ∑ a ∈ t.inf' (mem_filter.1 tcond).2.1 S, f a := by
  classical
  rw [← sub_nonneg]
  calc
    (∑ ⟨t, tcond⟩ : s.powerset.filter (fun t => t.Nonempty ∧ Finset.card t ≤ r),
      (-1) ^ (#t + 1) • ∑ a ∈ t.inf' (mem_filter.1 tcond).2.1 S, f a) - ∑ a ∈ s.biUnion S, f a
      = sorry


/-- **Inclusion-exclusion principle** for the cardinality of a union.

The cardinality of the union of the `S i` over `i ∈ s` is the alternating sum of the cardinalities
of the intersections of the `S i`. -/
theorem inclusion_exclusion_card_biUnion (s : Finset ι) (S : ι → Finset α) :
    #(s.biUnion S) = ∑ t : s.powerset.filter (·.Nonempty),
      (-1 : ℤ) ^ (#t.1 + 1) * #(t.1.inf' (mem_filter.1 t.2).2 S) := by
  simpa using inclusion_exclusion_sum_biUnion (G := ℤ) s S (f := 1)

variable [Fintype α]


theorem Finset.sum_attach {ι : Type u_1} {M : Type u_4} [AddCommMonoid M] (s : Finset ι) (f : ι → M) :
∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x := by sorry



end Finset
