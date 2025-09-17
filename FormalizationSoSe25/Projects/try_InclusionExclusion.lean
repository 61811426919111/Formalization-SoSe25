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

/- oben: Gleichheit der Gleichung, die ich in die trunkierte Version in Form von Ungleichungen
umwandeln soll, Beweis dient als Vorlage für meinen Beweis-/


/- mein Projekt: trunkierte Version -/
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

-- das bräuchte ich vermutlich um die Summen zusammenziehen zu können
lemma subset {α : Type*} (p q : α → Prop) [DecidablePred p] [DecidablePred q] (s : Finset α) (h: ∀ x, p x → q x) :
s.filter p ⊆ s.filter q := by
  intro x
  simp
  intro hx hp
  constructor
  · exact hx
  · exact h x hp

/- bräuchte vermutlich eher, dass sich s.filter q disjunkt in s.filter p und s.filter q ∧ ¬p zerlegen lässt,
aber das bekomme ich nicht vernünftig aufgeschrieben, sodass Lean mich versteht.
-/

lemma disjunct_subsets {α : Type*} (p q : α → Prop) [DecidablePred p] [DecidablePred q] (s : Finset α) (h: ∀ x, p x → q x) :
  s.filter q = s.filter p ⊔ s.filter (fun x => q x ∧ ¬ p x) := by sorry

variable {ι α G : Type*} [DecidableEq α]
  [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]

lemma sum_function (s t : Finset ι) (S : ι → Finset α) (f : α → G) (hf: ∀ a, f a ≥ 0) (k : ℕ) (hst : t ⊆ s):
∑ a ∈ s.biUnion S, f a ≥ ∑ a ∈ t.biUnion S, f a := by
  sorry
/- das gilt weil die Menge, aus denen die a kommen bei t=k+1 in der Menge von t=k enthalten ist.
t=k enthält also alle a, die auch in t=k+1 sind, aber sie kann auch noch mehr a enthalten.
da für t=k+1 f a in beiden Mengen gleich ist und f eine nichtnegative Funktion, kann durch einen größeren Wertebereich
(also bei t=k -> dann ist der Wertebereich größer als bei t=k+1) die Summe über alle Funktionswerte nur größer werden
oder gleich bleiben.
-> weiß nur noch nicht wie ich das in lean beweisen soll/kann. -/


/-
Alternative Idee: A_k erstmal definieren und dann zeigen dass f(A_k) ≥ f(A_{k+1}) für alle k.
-/


/-
vgl. lecture 4 Definitionen für Sets, habe versucht sie für Finsets anzupassen
-/

/-- Class for the `sInf` operator -/
class InfFinset (α : Type*) where
  /-- Infimum of a set -/
  fsInf : Finset α → α

export InfFinset (fsInf)

/-- Indexed infimum -/
def fsiInf [InfFinset α] (s : ι → α) : α :=
  fsInf (range s)

/-- begrenzter Schnitt-/
def A_k (A : Finset α) (s : ι → Finset α) (k : ℕ) (t : Finset ι) (ht : t.card = k) (knneg: 0 < k): Finset α :=
  {a ∈ A| ∀ i ∈ t, a ∈ s i}



lemma sum_int_function (s : Finset ι) (S : ι → Finset α) (f : α → G) (hf: ∀ a, f a ≥ 0) (k : ℕ) (evenk: 2 ∣ k):
∑ ⟨t, tcond⟩ : s.powerset.filter (fun t => t.Nonempty ∧ Finset.card t = k+1),
      (-1) ^ (#t +1) • ∑ a ∈ t.inf' (mem_filter.1 tcond).2.1 S, f a ≥
    ∑ ⟨t, tcond⟩ : s.powerset.filter (fun t => t.Nonempty ∧ Finset.card t > k+1),
        (-1) ^ (#t +1) • ∑ a ∈ t.inf' (mem_filter.1 tcond).2.1 S, f a := by sorry

/-
das Lemma ist glaube ich noch nicht richtig formuliert, eigentlich sollte es nur um die f a gehen, aber ich weiß
nicht wie ich das in der Summe schreibe, wenn ich kein t zur Verfügung habe.
-/

lemma nat_ge (n m: ℕ) : n > m ↔ n ≥ m + 1 := by
  constructor
  · intro h
    simp
    exact h
  · intro h
    simp
    exact h

theorem Finset.sum_nonneg {ι : Type u_1} {N : Type u_5} [AddCommMonoid N] [PartialOrder N]
[IsOrderedAddMonoid N] {f : ι → N} {s : Finset ι} (h : ∀ i ∈ s, 0 ≤ f i) :
0 ≤ ∑ i ∈ s, f i := by sorry
--> ist schon bewiesen und kann ich verwenden, hier nur damit ich Bedeutung nachlesen kann

theorem Finset.sum_attach {ι : Type u_1} {M : Type u_4} [AddCommMonoid M] (s : Finset ι) (f : ι → M) :
∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x := by sorry
--> this is a proven theorem I can already use, but only write it down here so I don't forget what it means

variable (evenk : 2 ∣ k) (oddr : ¬ 2 ∣ r) (r k : ℕ)

-- die erste Ungleichung die gezeigt werden soll, gerader Fall der trunkierten Version
theorem incl_excl_sum_biUnion_trunk_even (s : Finset ι) (S : ι → Finset α) (f : α → G) (hf : ∀ a, f a ≥ 0) (evenk : 2 ∣ k) :
   ∑ a ∈ s.biUnion S, f a ≥ ∑ ⟨t, tcond⟩ : s.powerset.filter (fun t => t.Nonempty ∧ Finset.card t ≤ k), -- hier vllt besser = statt kleinergleich
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
  _=  ∑ ⟨t, tcond⟩ : s.powerset.filter (fun t => t.Nonempty ∧ Finset.card t ≤ k),
      (-1) ^ #t • ∑ a ∈ t.inf' (mem_filter.1 tcond).2.1 S, f a -
      (∑ ⟨t, tcond⟩ : s.powerset.filter (fun t => t.Nonempty ∧ Finset.card t ≤ k),
      (-1) ^ #t • ∑ a ∈ t.inf' (mem_filter.1 tcond).2.1 S, f a +
      ∑ ⟨t, tcond⟩ : s.powerset.filter (fun t => t.Nonempty ∧ Finset.card t > k),
      (-1) ^ #t • ∑ a ∈ t.inf' (mem_filter.1 tcond).2.1 S, f a) := by sorry
  _=  ∑ ⟨t, tcond⟩ : s.powerset.filter (fun t => t.Nonempty ∧ Finset.card t ≤ k),
      (-1) ^ #t • ∑ a ∈ t.inf' (mem_filter.1 tcond).2.1 S, (f a - f a) -
      ∑ ⟨t, tcond⟩ : s.powerset.filter (fun t => t.Nonempty ∧ Finset.card t > k),
      (-1) ^ #t • ∑ a ∈ t.inf' (mem_filter.1 tcond).2.1 S, f a := by simp [sub_eq_neg_add]
  _=  - ∑ ⟨t, tcond⟩ : s.powerset.filter (fun t => t.Nonempty ∧ Finset.card t > k),
      (-1) ^ #t • ∑ a ∈ t.inf' (mem_filter.1 tcond).2.1 S, f a := by simp
  _=  ∑ ⟨t, tcond⟩ : s.powerset.filter (fun t => t.Nonempty ∧ Finset.card t > k),
      (-1) ^ (#t +1) • ∑ a ∈ t.inf' (mem_filter.1 tcond).2.1 S, f a := by simp [pow_succ]
  _=  ∑ ⟨t, tcond⟩ : s.powerset.filter (fun t => t.Nonempty ∧ Finset.card t ≥ k+1),
      (-1) ^ (#t +1) • ∑ a ∈ t.inf' (mem_filter.1 tcond).2.1 S, f a := by exact rfl
  _=  ∑ ⟨t, tcond⟩ : s.powerset.filter (fun t => t.Nonempty ∧ Finset.card t = k+1),
      (-1) ^ (#t +1) • ∑ a ∈ t.inf' (mem_filter.1 tcond).2.1 S, f a +
      ∑ ⟨t, tcond⟩ : s.powerset.filter (fun t => t.Nonempty ∧ Finset.card t > k+1),
      (-1) ^ (#t +1) • ∑ a ∈ t.inf' (mem_filter.1 tcond).2.1 S, f a := by sorry
  _≥ 0 := by sorry

/-
da erste Summe größer zweite Summe ist Differenz (da zweite Summe durch (-1) ein negatives Vorzeichen bekommt)
beider positiv
das wollte ich mit dem obigen Lemma zeigen, aber das ist noch nicht 100%ig passend formuliert.
-/

/-.
erster Weg: komme aber im zweiten Fall nicht weiter:
    apply Finset.sum_nonneg
    intro t tcond
    simp only [Int.reduceNeg]
    refine zsmul_nonneg ?_ ?_
    · apply Finset.sum_nonneg
      intro a ha
      exact hf a
    · refine Even.pow_nonneg ?_ (-1)
      obtain ⟨x, hxk⟩ := t
-> da ich evenk nicht anwenden kann. Denke die Fallunterscheidung ist nicht hilfreich.

zweiter Versuch - Plan: versuche erst zu zeigen dass das kleinstmögliche t, dass die Bedingung t>k erfüllt, die größte
Summe der ausgewerteten Funktion hat, also das Vorzeichen entscheidet.
Dann das kleinste t>k bestimmen (da k in ℕ muss auch t in ℕ sein), also t=k+1, und damit die alternierende Summe
auswerten mit dem Hinweis, dass k gerade ist, also ist k+1 +1 auch gerade und das Vorzeichen der Summe ist positiv.
-/

/-
zweite Ungleichung, vermutlich analog zur ersten lösbar, sobald ich die erste gelöst habe
trunkierte Version im ungeraden Fall
-/
theorem incl_excl_sum_biUnion_trunk_odd (s : Finset ι) (S : ι → Finset α) (f : α → G) (hf: ∀ a, f a ≥ 0) ():
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

theorem incl_excl_card_biUnion_trunk_even (s : Finset ι) (S : ι → Finset α) (k : ℕ):
    (#(s.biUnion S) : ℤ) ≥ ∑ ⟨t, tcond⟩ : s.powerset.filter (fun t => t.Nonempty ∧ Finset.card t ≤ k),
      (-1 : ℤ) ^ (#t + 1) * #(t.inf' (mem_filter.1 tcond).2.1 S) := by
  simpa using incl_excl_sum_biUnion_trunk_even (G := ℤ) s S (f := 1) k

theorem incl_excl_card_biUnion_trunk_odd (s : Finset ι) (S : ι → Finset α) (r : ℕ):
    (#(s.biUnion S) : ℤ) ≤ ∑ ⟨t, tcond⟩ : s.powerset.filter (fun t => t.Nonempty ∧ Finset.card t ≤ r),
      (-1 : ℤ) ^ (#t + 1) * #(t.inf' (mem_filter.1 tcond).2.1 S) := by
  simpa using incl_excl_card_biUnion_trunk_odd (G := ℤ) s S (f := 1) r

/-
hier bei den Kardinalitäten weiß ich nicht weiter. Iwie stimmt mein Syntax noch nicht,
theoretisch muss ich nämlich nur die ungleichungen anwenden, aber Lean versteh noch nicht wie ich das meine.
-/


variable [Fintype α]





end Finset

/-
Tipps von Nima:
(1) Eine einfache Methode die manchmal funktioniert sind die Fragezeichen Taktiken,
also man kann die Taktiken 'exact?', 'apply?' und 'simp?' und das sucht in Mathlib und macht
manchmal gute Vorschläge.

(2) Wie du erwähnt hast, gibt es die zwei Webseiten <https://www.moogle.ai/> und
<https://loogle.lean-lang.org/> die sozusagen Databases sind für Lean. Ich benutze die zwei auch
nicht so oft, aber anscheinend hilft es vielen weiter. In <https://www.moogle.ai/> kann man Sätze
(auf Englisch) eingeben und es versucht mit einer KI Methode passende Sätze in Mathlib zu finden.
In <https://loogle.lean-lang.org/> musst du die richtigen Lean Namen eingeben, was schwieriger sein
kann. Ist wahrscheinlich ein Versuch Wert.

(3) Wenn du VS Code benutzt kannst du (glaube ich) Github Copilot auf deinem Computer freischalten,
das versucht automatisch Vorschläge zu machen wenn du etwas schreibst. Ist nicht immer richtig,
kann aber weiterhelfen. Das nutze ich sehr oft, und manchmal hat es mir wirklich weitergeholfen.

(4) Eine direktere KI Methode (die du wahrscheinlich schon versucht hast ist), ist einfach direkt
ChatGPT zu fragen. 'Ich will dieses Ergebnis in Lean' und dann kann man es direkt beschreiben.

(5) Manchmal hilft es Ergebnis das man will als Satz in Lean aufzuschreiben also

lemma test : 'das Ding das wir wollen' := by sorry

Dann benutzt man es wo man will und versucht später diese Lücken zu füllen.

(6) Es kann helfen Schritt (5) mit Schritt (1), (3) oder (4) zu kombinieren. Also man schreibt
explizit in Lean was man will (so wie in (5) beschrieben) und dann kann man die Fragezeichen
Taktiken (simp? oder apply?), oder KI in Github Copilot direkt, oder auf einer Webseite fragen
ob es einen Beweis dazu gibt.

Im Endeffekt muss man leider ein bisschen rumprobieren, und für verschiedene Menschen funktionieren
verschiedene Optionen besser.

Zum Beispiel, für deine Frage über nicht-negative habe ich genau ChatGPT gefragt. Nämlich:

'I want a proof that if f i are bigger equal the identity, then so is the sum. Is there a term
in Mathlib for this?'
Die Antwort war:
'Finset.sum_nonneg.{u_1, u_5} {ι : Type u_1} {N : Type u_5} [AddCommMonoid N] [PartialOrder N]
[IsOrderedAddMonoid N] {f : ι → N} {s : Finset ι} (h : ∀ i ∈ s, 0 ≤ f i) : 0 ≤ ∑ i ∈ s, f i'

Also ist der Vorschlag Finset.sum_nonneg was (glaube ich) die gewünschte Antwort ist?
-/
