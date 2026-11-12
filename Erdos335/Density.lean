/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Count
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
# Ordinary density and periodic examples

This module adapts the elementary density and periodic-set lemmas from
AItoBit/formal-conjectures, commit 76e184a85c6134ab86f4b9d7e57d7f3c85a49d32,
FormalConjectures/ErdosProblems/335.lean (PR 6866).
The source is preserved in ../public_sources/deepmind335_pr.lean.
Only the independently checked elementary portion is included here.
The unrestricted classification and the source's unproved declarations are excluded.
-/

set_option autoImplicit false

open Filter Topology
open scoped Pointwise

namespace Erdos335

/-- `count A N = |A ∩ {1, …, N}|`. -/
noncomputable def count (A : Set ℕ) (N : ℕ) : ℕ := by
  classical exact ((Finset.Icc 1 N).filter (· ∈ A)).card

/-- `A` has natural density `δ`: `|A ∩ [N]| / N → δ` as `N → ∞` (the limit exists). -/
def HasDensity (A : Set ℕ) (δ : ℝ) : Prop :=
  Tendsto (fun N : ℕ => (count A N : ℝ) / N) atTop (𝓝 δ)

/-- Density along a sequence `Ns → ∞`: `d_N(A) = lim_s |A ∩ [N_s]| / N_s` exists and is `δ`. -/
def HasDensityAlong (Ns : ℕ → ℕ) (A : Set ℕ) (δ : ℝ) : Prop :=
  Tendsto (fun s : ℕ => (count A (Ns s) : ℝ) / (Ns s)) atTop (𝓝 δ)

/-- The pairs that Erdős Problem #335 asks to characterise: `A, B ⊆ {1,2,…}`, both with
positive (existing) density, such that `A + B` has density `d(A) + d(B)`. -/
def IsErdos335Pair (A B : Set ℕ) : Prop :=
  A ⊆ Set.Ioi 0 ∧ B ⊆ Set.Ioi 0 ∧
    ∃ dA dB : ℝ, 0 < dA ∧ 0 < dB ∧ HasDensity A dA ∧ HasDensity B dB ∧
      HasDensity (A + B) (dA + dB)

/-- The periodic set `{n ≥ 1 : n mod m ∈ X}`. -/
def periodicSet {m : ℕ} (X : Finset (ZMod m)) : Set ℕ := {n | 0 < n ∧ (n : ZMod m) ∈ X}

theorem count_zero (A : Set ℕ) : count A 0 = 0 := by
  classical
  simp [count]

theorem count_succ (A : Set ℕ) (N : ℕ) :
    count A (N + 1) = count A N + (by classical exact if N + 1 ∈ A then 1 else 0) := by
  classical
  unfold count
  rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega), Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · convert (add_zero _).symm

/-- A density statement from a uniformly bounded error term. -/
theorem tendsto_div_of_bounded (f : ℕ → ℝ) (δ C : ℝ) (h : ∀ N, |f N - δ * N| ≤ C) :
    Tendsto (fun N : ℕ => f N / N) atTop (𝓝 δ) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (tendsto_const_div_atTop_nhds_zero_nat C)
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.norm_eq_abs, show f N / N - δ = (f N - δ * N) / N by field_simp, abs_div,
    abs_of_pos hN']
  exact div_le_div_of_nonneg_right (h N) hN'.le

/-- Counting functions of sets agreeing above `K` differ by at most `K`. -/
theorem count_le_count_add (A B : Set ℕ) (K : ℕ) (h : ∀ n, K < n → n ∈ A → n ∈ B) (N : ℕ) :
    count A N ≤ count B N + K := by
  classical
  unfold count
  calc ((Finset.Icc 1 N).filter (· ∈ A)).card
      ≤ ((Finset.Icc 1 N).filter (· ∈ B) ∪ Finset.Icc 1 K).card := by
        apply Finset.card_le_card
        intro n hn
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union] at hn ⊢
        by_cases hK : K < n
        · exact Or.inl ⟨hn.1, h n hK hn.2⟩
        · exact Or.inr ⟨hn.1.1, by omega⟩
    _ ≤ _ := by
        refine (Finset.card_union_le _ _).trans ?_
        simp

/-- If two sets agree above `K` and one has density `δ`, so does the other. -/
theorem HasDensity.of_eventually_eq {A B : Set ℕ} {δ : ℝ} (K : ℕ)
    (h : ∀ n, K < n → (n ∈ A ↔ n ∈ B)) (hA : HasDensity A δ) : HasDensity B δ := by
  unfold HasDensity at *
  have hdiff : Tendsto (fun N : ℕ => ((count B N : ℝ) - count A N) / N) atTop (𝓝 0) := by
    have := tendsto_div_of_bounded (fun N => (count B N : ℝ) - count A N) 0 K
      (fun N => by
        have h1 := count_le_count_add A B K (fun n hn => (h n hn).1) N
        have h2 := count_le_count_add B A K (fun n hn => (h n hn).2) N
        rw [zero_mul, sub_zero, abs_le]
        constructor
        · have : (count A N : ℝ) ≤ count B N + K := by exact_mod_cast h1
          linarith
        · have : (count B N : ℝ) ≤ count A N + K := by exact_mod_cast h2
          linarith)
    simpa using this
  have := hA.add hdiff
  rw [add_zero] at this
  refine this.congr fun N => ?_
  rw [← add_div]
  ring_nf

/-- In `[0, m)`, exactly `|X|` integers have residue in `X`. -/
theorem nat_count_period {m : ℕ} [NeZero m] (X : Finset (ZMod m)) :
    Nat.count (fun n : ℕ => (n : ZMod m) ∈ X) m = X.card := by
  rw [Nat.count_eq_card_filter_range]
  refine Finset.card_bij (fun n _ => (n : ZMod m)) ?_ ?_ ?_
  · intro n hn
    exact (Finset.mem_filter.1 hn).2
  · intro a ha b hb hab
    have ha' := Finset.mem_range.1 (Finset.mem_filter.1 ha).1
    have hb' := Finset.mem_range.1 (Finset.mem_filter.1 hb).1
    have := congrArg ZMod.val hab
    rwa [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] at this
  · intro x hx
    refine ⟨x.val, Finset.mem_filter.2 ⟨Finset.mem_range.2 (ZMod.val_lt x), ?_⟩, ?_⟩
    · simpa using hx
    · simp

theorem nat_count_periodic {m : ℕ} [NeZero m] (X : Finset (ZMod m)) (q r : ℕ) :
    Nat.count (fun n : ℕ => (n : ZMod m) ∈ X) (m * q + r) =
      q * X.card + Nat.count (fun n : ℕ => (n : ZMod m) ∈ X) r := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show m * (q + 1) + r = m + (m * q + r) by ring, Nat.count_add, nat_count_period]
    have hshift : Nat.count (fun k : ℕ => ((m + k : ℕ) : ZMod m) ∈ X) (m * q + r) =
        Nat.count (fun k : ℕ => (k : ZMod m) ∈ X) (m * q + r) := by
      simp
    rw [hshift, ih]
    ring

theorem count_periodicSet_add {m : ℕ} (X : Finset (ZMod m)) (N : ℕ) :
    count (periodicSet X) N + (if ((0 : ℕ) : ZMod m) ∈ X then 1 else 0) =
      Nat.count (fun n : ℕ => (n : ZMod m) ∈ X) (N + 1) := by
  classical
  induction N with
  | zero => simp [count_zero, Nat.count_succ]
  | succ N ih =>
    rw [count_succ, Nat.count_succ, ← ih]
    simp only [periodicSet, Set.mem_ofPred_eq, Nat.succ_pos, true_and]
    split_ifs <;> omega

/-- An exact quotient-and-remainder expression for the periodic counting function. -/
theorem count_periodicSet_div_mod {m : ℕ} [NeZero m] (X : Finset (ZMod m)) (N : ℕ) :
    (count (periodicSet X) N : ℝ) +
      ((if ((0 : ℕ) : ZMod m) ∈ X then 1 else 0 : ℕ) : ℝ) =
      ((N + 1) / m : ℕ) * (X.card : ℝ) +
        (Nat.count (fun n : ℕ => (n : ZMod m) ∈ X) ((N + 1) % m) : ℝ) := by
  have key := count_periodicSet_add X N
  have hc := nat_count_periodic X ((N + 1) / m) ((N + 1) % m)
  rw [Nat.div_add_mod] at hc
  rw [hc] at key
  exact_mod_cast key

/-- `{n ≥ 1 : n mod m ∈ X}` has density `|X| / m`. -/
theorem hasDensity_periodicSet {m : ℕ} [NeZero m] (X : Finset (ZMod m)) :
    HasDensity (periodicSet X) (X.card / m) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hXm : (X.card : ℝ) ≤ m := by
    have := Finset.card_le_univ X
    rw [ZMod.card] at this
    exact_mod_cast this
  refine tendsto_div_of_bounded _ _ (m + 2) fun N => ?_
  set M := N + 1 with hM
  have hdiv := Nat.div_add_mod M m
  have hr : M % m < m := Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne m))
  have hcr : Nat.count (fun n : ℕ => (n : ZMod m) ∈ X) (M % m) ≤ M % m := Nat.count_le _
  set q := M / m
  set r := M % m
  have hq : (M : ℝ) = m * q + r := by exact_mod_cast hdiv.symm
  have hite : ((if ((0 : ℕ) : ZMod m) ∈ X then 1 else 0 : ℕ) : ℝ) ≤ 1 := by
    split_ifs <;> simp
  have hite0 : (0 : ℝ) ≤ ((if ((0 : ℕ) : ZMod m) ∈ X then 1 else 0 : ℕ) : ℝ) := by positivity
  have key' := count_periodicSet_div_mod X N
  change (count (periodicSet X) N : ℝ) +
    ((if ((0 : ℕ) : ZMod m) ∈ X then 1 else 0 : ℕ) : ℝ) =
      (q : ℝ) * X.card + Nat.count (fun n : ℕ => (n : ZMod m) ∈ X) r at key'
  have hcr' : (Nat.count (fun n : ℕ => (n : ZMod m) ∈ X) r : ℝ) ≤ r := by exact_mod_cast hcr
  have hr' : (r : ℝ) < m := by exact_mod_cast hr
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hN : (N : ℝ) = m * q + r - 1 := by rw [← hq, hM]; push_cast; ring
  have hexp : (X.card : ℝ) / m * N = q * X.card + (r - 1) * X.card / m := by
    rw [hN]; field_simp; ring
  have hX0 : (0 : ℝ) ≤ X.card := by positivity
  have hb1 : ((r : ℝ) - 1) * X.card / m ≤ r := by
    rw [div_le_iff₀ hm]; nlinarith
  have hb2 : -1 ≤ ((r : ℝ) - 1) * X.card / m := by
    rw [le_div_iff₀ hm]; nlinarith
  have hcnt0 : (0 : ℝ) ≤ (Nat.count (fun n : ℕ => (n : ZMod m) ∈ X) r : ℝ) := by positivity
  rw [hexp, abs_le]
  constructor <;> linarith

/-- Above `m`, the sumset of two periodic sets is the periodic set of the sumset. -/
theorem mem_periodicSet_add_iff {m : ℕ} [NeZero m] (X Y : Finset (ZMod m)) (n : ℕ)
    (hn : m < n) : n ∈ periodicSet X + periodicSet Y ↔ n ∈ periodicSet (X + Y) := by
  constructor
  · rintro ⟨a, ⟨ha0, ha⟩, b, ⟨hb0, hb⟩, rfl⟩
    refine ⟨by omega, ?_⟩
    push_cast
    exact Finset.add_mem_add ha hb
  · rintro ⟨-, hn'⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_add.1 hn'
    set b : ℕ := if y.val = 0 then m else y.val with hbdef
    have hb1 : 0 < b := by
      rw [hbdef]; split_ifs with h
      · exact Nat.pos_of_ne_zero (NeZero.ne m)
      · exact Nat.pos_of_ne_zero h
    have hbm : b ≤ m := by
      rw [hbdef]; split_ifs
      · exact le_rfl
      · exact (ZMod.val_lt y).le
    have hby : (b : ZMod m) = y := by
      rw [hbdef]; split_ifs with h
      · rw [ZMod.natCast_self]; exact ((ZMod.val_eq_zero y).1 h).symm
      · simp
    refine ⟨n - b, ⟨by omega, ?_⟩, b, ⟨hb1, by rwa [hby]⟩, by show n - b + b = n; omega⟩
    rw [Nat.cast_sub (by omega), hby, ← hxy]
    simpa using hx

/-- **Rotations on `ℤ/mℤ` give solutions.** If `X, Y ⊆ ℤ/mℤ` are nonempty and
`|X + Y| = |X| + |Y|`, then `A = {n ≥ 1 : n mod m ∈ X}` and `B = {n ≥ 1 : n mod m ∈ Y}`
have positive densities `|X|/m`, `|Y|/m`, and `d(A + B) = d(A) + d(B)`. -/
theorem periodicSet_isErdos335Pair {m : ℕ} [NeZero m] (X Y : Finset (ZMod m))
    (hX : X.Nonempty) (hY : Y.Nonempty) (hcard : (X + Y).card = X.card + Y.card) :
    IsErdos335Pair (periodicSet X) (periodicSet Y) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  refine ⟨fun n hn => hn.1, fun n hn => hn.1, X.card / m, Y.card / m,
    div_pos (by exact_mod_cast hX.card_pos) hm, div_pos (by exact_mod_cast hY.card_pos) hm,
    hasDensity_periodicSet X, hasDensity_periodicSet Y, ?_⟩
  have h := hasDensity_periodicSet (X + Y)
  rw [hcard, Nat.cast_add, add_div] at h
  exact h.of_eventually_eq m fun n hn => (mem_periodicSet_add_iff X Y n hn).symm


end Erdos335
