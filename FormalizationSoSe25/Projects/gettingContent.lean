/- to get the content of Beweisvorlage -/

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.BigOperators

-- assert_not_exists Field

namespace Finset
variable {ι α G : Type*} [DecidableEq α] [AddCommGroup G] {s : Finset ι}

lemma prod_indicator_biUnion_sub_indicator (hs : s.Nonempty) (S : ι → Finset α) (a : α) :
/-
hs -> Annahme, dass Menge s nicht leer ist
S -> Funktion, die jedem Element i vom Typ ι eine endliche Menge (Finset α) zuordnet
-> man hat eine Familie von endlichen Mengen, die durch S beschrieben wird
a : α -> a ist ein Element der Menge α, auf die sich die Indikatorfunktionen beziehen
-/
    ∏ i ∈ s, (Set.indicator (s.biUnion S) 1 a - Set.indicator (S i) 1 a) = (0 : ℤ) := by
    /-
    ∏ i ∈ s -> Das ist das Produkt über alle i in der Menge s
    Set.indicator (s.biUNion S) 1 a -> Indikatorfunktion, ist 1 wenn a in s.biUnion S ist und 0 sonst
    s.biUnion S -> Vereinigung aller Mengen S i
    S i -> Menge die i durch die Funktion S zugeordnet wird
    Set.indicator (S i) 1 a -> Indikatorfunktion, ist 1 wenn a in S i ist und 0 sonst
    -/
  by_cases ha : a ∈ s.biUnion S
  /-
  Fallunterscheidung:
  Fall 1 ha ist wahr, d.h. a ist in der Vereinigung s.biUnion S
  Fall 2: ha ist falsch, d.h. a ist nicht in der Vereinigun s.biUnion S
  -/
  · obtain ⟨i, hi, ha⟩ := mem_biUnion.1 ha
    /-
    i ist von Typ ι
    hi: i ∈ s
    ha: a ∈ S i
    -/
    exact prod_eq_zero hi <| by simp [*, -coe_biUnion]
    /-
    Finset.prod_eq_zero:  (hi : i ∈ s) (h : f i = 0) : ∏ j ∈ s, f j = 0
    "<|"" -> Pipe-Operator wie in R: f <| g <| x means f(g(x))
    simp[*] -> rewrite with all hypothesis
    Finset.coe_biUnion: ↑(s.biUnion t) = ⋃ x ∈ ↑s, ↑(t x)
    -/
  · obtain ⟨i, hi⟩ := hs
    /-
    i : ι -> i ist vom Typ ι
    hi : i ∈ s
    -/
    have ha : a ∉ S i := fun h ↦ ha <| subset_biUnion_of_mem _ hi h
    /-
    Finset.subset_biUnion_of_mem:
    {s : Finset α} [DecidableEq β] (u : α → Finset β) {x : α} (xs : x ∈ s) :
    u x ⊆ s.biUnion u
    -/
    exact prod_eq_zero hi <| by simp [*, -coe_biUnion]

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
