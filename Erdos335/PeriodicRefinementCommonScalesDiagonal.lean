import Erdos335.PositiveIntermediateScales
import Erdos335.ReciprocalScaleRatios
import Mathlib.Order.Filter.Finite

/-! Private uncompiled draft of a diagonal through nested scale intervals. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Filter Topology Finset

noncomputable section

namespace Erdos335.IntermediateScale

def refinementIndex (ρ : ℕ → ℕ → ℕ) (j : ℕ) : ℕ → ℕ → ℕ
  | 0 => id
  | d + 1 => fun n => refinementIndex ρ j d (ρ (j + d) n)

theorem refinementIndex_strictMono (ρ : ℕ → ℕ → ℕ)
    (hρ : ∀ j, StrictMono (ρ j)) (j d : ℕ) :
    StrictMono (refinementIndex ρ j d) := by
  induction d with
  | zero => exact strictMono_id
  | succ d ih => exact ih.comp (hρ (j + d))

theorem refinementIndex_factor (τ ρ : ℕ → ℕ → ℕ)
    (hstep : ∀ j, τ (j + 1) = τ j ∘ ρ j) (j d : ℕ) :
    τ (j + d) = τ j ∘ refinementIndex ρ j d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [Nat.add_succ, hstep, ih]
      rfl

private theorem nat_le_strictMono_value (f : ℕ → ℕ) (hf : StrictMono f) (n : ℕ) : n ≤ f n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      have hnext := hf (Nat.lt_succ_self n)
      exact Nat.succ_le_of_lt (ih.trans_lt hnext)

theorem exists_nested_interval_diagonal
    (N : ℕ → ℕ) (τ ρ : ℕ → ℕ → ℕ)
    (hτ : ∀ j, StrictMono (τ j)) (hρ : ∀ j, StrictMono (ρ j))
    (hstep : ∀ j, τ (j + 1) = τ j ∘ ρ j)
    (A B : ℕ → ℕ → ℕ)
    (hApos : ∀ j n, 0 < A j n) (hBpos : ∀ j n, 0 < B j n)
    (hA : ∀ j, Tendsto (A j) atTop atTop)
    (hAB : ∀ j, Tendsto (fun n => (A j n : ℝ) / B j n) atTop (𝓝 0))
    (hAlink : ∀ j, ∀ᶠ n in atTop, A j (ρ j n) ≤ A (j + 1) n)
    (hBlink : ∀ j, ∀ᶠ n in atTop, B (j + 1) n ≤ B j (ρ j n))
    (hBinside : ∀ j, ∀ᶠ n in atTop, B j n ≤ N (τ j n)) :
    ∃ (κ L V H : ℕ → ℕ), StrictMono κ ∧
      (∀ n, 0 < L n ∧ 0 < V n ∧ 0 < H n) ∧
      Tendsto L atTop atTop ∧ Tendsto H atTop atTop ∧
      Tendsto (fun n => (L n : ℝ) / H n) atTop (𝓝 0) ∧
      Tendsto (fun n => (H n : ℝ) / V n) atTop (𝓝 0) ∧
      Tendsto (fun n => (H n : ℝ) / N (κ n)) atTop (𝓝 0) ∧
      ∀ j, ∃ σ : ℕ → ℕ, StrictMono σ ∧ τ j ∘ σ =ᶠ[atTop] κ ∧
        Tendsto (fun n => (A j (σ n) : ℝ) / L n) atTop (𝓝 0) ∧
        Tendsto (fun n => (V n : ℝ) / B j (σ n)) atTop (𝓝 0) := by
  classical
  have lower_compare (j d : ℕ) :
      ∀ᶠ n in atTop, A j (refinementIndex ρ j d n) ≤ A (j + d) n := by
    induction d with
    | zero => exact Eventually.of_forall fun _ => le_rfl
    | succ d ih =>
        filter_upwards [(hρ (j + d)).tendsto_atTop.eventually ih, hAlink (j + d)] with n hn hm
        simpa only [refinementIndex, Nat.add_succ] using hn.trans hm
  have upper_compare (j d : ℕ) :
      ∀ᶠ n in atTop, B (j + d) n ≤ B j (refinementIndex ρ j d n) := by
    induction d with
    | zero => exact Eventually.of_forall fun _ => le_rfl
    | succ d ih =>
        filter_upwards [(hρ (j + d)).tendsto_atTop.eventually ih, hBlink (j + d)] with n hn hm
        simpa only [refinementIndex, Nat.add_succ] using hm.trans hn
  let small := fun j => positiveIntermediateScale (A j) (B j) (1 / 4) 0
  let middle := fun j => positiveIntermediateScale (A j) (B j) (1 / 2) 0
  let large := fun j => positiveIntermediateScale (A j) (B j) (3 / 4) 0
  have hBA (j : ℕ) : Tendsto (fun n => (B j n : ℝ) / A j n) atTop atTop :=
    reciprocal_scale_ratio_tendsto_atTop (A j) (B j) (hApos j) (hBpos j) (hAB j)
  have hB (j : ℕ) : Tendsto (B j) atTop atTop :=
    scale_tendsto_atTop_of_smaller (A j) (B j) (hA j) (hBpos j) (hAB j)
  have hsmall (j : ℕ) : Tendsto (small j) atTop atTop :=
    positiveIntermediateScale_atTop (A j) (B j) (hA j) (hBA j) _ _ (by norm_num)
  have hAsmall (j : ℕ) : Tendsto (fun n => (A j n : ℝ) / small j n) atTop (𝓝 0) :=
    positiveIntermediateScale_lower_ratio (A j) (B j) (hA j) (hBA j) _ _ (by norm_num)
  have hsmallMiddle (j : ℕ) : Tendsto (fun n => (small j n : ℝ) / middle j n) atTop (𝓝 0) :=
    positiveIntermediateScale_lexicographic_ratio (A j) (B j) (hA j) (hBA j)
      _ _ _ _ (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hmiddleLarge (j : ℕ) : Tendsto (fun n => (middle j n : ℝ) / large j n) atTop (𝓝 0) :=
    positiveIntermediateScale_lexicographic_ratio (A j) (B j) (hA j) (hBA j)
      _ _ _ _ (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hlargeB (j : ℕ) : Tendsto (fun n => (large j n : ℝ) / B j n) atTop (𝓝 0) :=
    positiveIntermediateScale_ambient_ratio (A j) (B j) (B j) (hA j) (hB j) (hBA j)
      (Eventually.of_forall fun _ => le_rfl) _ _ (by norm_num) (by norm_num)
  have hmiddleN (j : ℕ) :
      Tendsto (fun n => (middle j n : ℝ) / N (τ j n)) atTop (𝓝 0) :=
    positiveIntermediateScale_ambient_ratio (A j) (B j) (N ∘ τ j) (hA j) (hB j) (hBA j)
      (hBinside j) _ _ (by norm_num) (by norm_num)
  have hOldSmall (j k : ℕ) (hjk : j ≤ k) :
      Tendsto (fun n => (A j (refinementIndex ρ j (k - j) n) : ℝ) / small k n)
        atTop (𝓝 0) := by
    have hc := lower_compare j (k - j)
    rw [Nat.add_sub_of_le hjk] at hc
    apply squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ (hAsmall k)
    exact hc.mono fun n hn => div_le_div_of_nonneg_right (by exact_mod_cast hn) (by positivity)
  have hLargeOld (j k : ℕ) (hjk : j ≤ k) :
      Tendsto (fun n => (large k n : ℝ) / B j (refinementIndex ρ j (k - j) n))
        atTop (𝓝 0) := by
    have hc := upper_compare j (k - j)
    rw [Nat.add_sub_of_le hjk] at hc
    apply squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ (hlargeB k)
    filter_upwards [hc] with n hn
    exact div_le_div_of_nonneg_left (by positivity)
      (by exact_mod_cast hBpos k n) (by exact_mod_cast hn)
  let ε := fun k : ℕ => (1 : ℝ) / ((k + 1 : ℕ) : ℝ)
  let Q := fun k n : ℕ =>
    k + 1 ≤ small k n ∧
    (small k n : ℝ) / middle k n ≤ ε k ∧
    (middle k n : ℝ) / large k n ≤ ε k ∧
    (middle k n : ℝ) / N (τ k n) ≤ ε k ∧
    ∀ j ≤ k, (A j (refinementIndex ρ j (k - j) n) : ℝ) / small k n ≤ ε k ∧
      (large k n : ℝ) / B j (refinementIndex ρ j (k - j) n) ≤ ε k
  have hQ (k : ℕ) : ∀ᶠ n in atTop, Q k n := by
    have hε : 0 < ε k := by dsimp only [ε]; positivity
    have hold : ∀ᶠ n in atTop, ∀ j ∈ range (k + 1),
        (A j (refinementIndex ρ j (k - j) n) : ℝ) / small k n ≤ ε k ∧
        (large k n : ℝ) / B j (refinementIndex ρ j (k - j) n) ≤ ε k := by
      apply (eventually_all_finset (range (k + 1))).mpr
      intro j hj
      have hjk : j ≤ k := by have := mem_range.mp hj; omega
      filter_upwards [(hOldSmall j k hjk).eventually (eventually_lt_nhds hε),
        (hLargeOld j k hjk).eventually (eventually_lt_nhds hε)] with n hn hm
      exact ⟨hn.le, hm.le⟩
    filter_upwards [(hsmall k).eventually (eventually_ge_atTop (k + 1)),
      (hsmallMiddle k).eventually (eventually_lt_nhds hε),
      (hmiddleLarge k).eventually (eventually_lt_nhds hε),
      (hmiddleN k).eventually (eventually_lt_nhds hε), hold] with n hn hsm hml hmn ho
    exact ⟨hn, hsm.le, hml.le, hmn.le, fun j hj => ho j (mem_range.mpr (by omega))⟩
  have hchoose : ∀ k b : ℕ, ∃ n, b ≤ n ∧ k ≤ n ∧ Q k n := by
    intro k b
    obtain ⟨n, hn, hb⟩ := ((hQ k).and (eventually_ge_atTop (max b k))).exists
    exact ⟨n, (le_max_left _ _).trans hb, (le_max_right _ _).trans hb, hn⟩
  choose pick hpick using hchoose
  let selected : ℕ → ℕ := Nat.rec (pick 0 0) (fun k previous => pick (k + 1) (τ k previous + 1))
  have hselected (k : ℕ) : k ≤ selected k ∧ Q k (selected k) := by
    cases k with
    | zero => exact ⟨(hpick 0 0).2.1, (hpick 0 0).2.2⟩
    | succ k => exact ⟨(hpick (k + 1) (τ k (selected k) + 1)).2.1,
        (hpick (k + 1) (τ k (selected k) + 1)).2.2⟩
  let κ := fun k => τ k (selected k)
  have hκ : StrictMono κ := by
    apply strictMono_nat_of_lt_succ
    intro k
    have hp : τ k (selected k) + 1 ≤ selected (k + 1) :=
      (hpick (k + 1) (τ k (selected k) + 1)).1
    have hs := nat_le_strictMono_value (τ (k + 1)) (hτ (k + 1)) (selected (k + 1))
    dsimp only [κ]
    omega
  let L := fun k => small k (selected k)
  let H := fun k => middle k (selected k)
  let V := fun k => large k (selected k)
  have hpos : ∀ n, 0 < L n ∧ 0 < V n ∧ 0 < H n := by
    intro n
    exact ⟨positiveIntermediateScale_pos _ _ _ _ _, positiveIntermediateScale_pos _ _ _ _ _,
      positiveIntermediateScale_pos _ _ _ _ _⟩
  have hεlim : Tendsto ε atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat 1).comp (tendsto_add_atTop_nat 1)
  have hL : Tendsto L atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [eventually_ge_atTop k] with n hn
    exact hn.trans ((Nat.le_succ n).trans ((hselected n).2.1))
  have hLH : Tendsto (fun n => (L n : ℝ) / H n) atTop (𝓝 0) :=
    squeeze_zero (fun _ => by positivity) (fun n => (hselected n).2.2.1) hεlim
  have hHV : Tendsto (fun n => (H n : ℝ) / V n) atTop (𝓝 0) :=
    squeeze_zero (fun _ => by positivity) (fun n => (hselected n).2.2.2.1) hεlim
  have hHN : Tendsto (fun n => (H n : ℝ) / N (κ n)) atTop (𝓝 0) :=
    squeeze_zero (fun _ => by positivity) (fun n => (hselected n).2.2.2.2.1) hεlim
  refine ⟨κ, L, V, H, hκ, hpos, hL,
    scale_tendsto_atTop_of_smaller L H hL (fun n => (hpos n).2.2) hLH,
    hLH, hHV, hHN, ?_⟩
  intro j
  let σ := fun n => if j ≤ n then refinementIndex ρ j (n - j) (selected n) else n
  have hmap (n : ℕ) (hn : j ≤ n) : τ j (σ n) = κ n := by
    have hf := refinementIndex_factor τ ρ hstep j (n - j)
    rw [Nat.add_sub_of_le hn] at hf
    dsimp only [σ]
    rw [if_pos hn]
    exact (congrFun hf (selected n)).symm
  have hσ : StrictMono σ := by
    apply strictMono_nat_of_lt_succ
    intro n
    by_cases hn : j ≤ n
    · have hn' : j ≤ n + 1 := by omega
      have hm : τ j (σ n) < τ j (σ (n + 1)) := by rw [hmap n hn, hmap (n + 1) hn']; exact hκ (Nat.lt_succ_self n)
      by_contra hnot
      exact not_le_of_gt hm ((hτ j).monotone (not_lt.mp hnot))
    · by_cases hn' : j ≤ n + 1
      · have hj : j = n + 1 := by omega
        subst j
        simpa only [σ, if_neg (by omega : ¬ (n + 1 ≤ n)), if_pos (le_refl (n + 1)),
          Nat.sub_self, refinementIndex, id_eq] using (Nat.lt_succ_self n).trans_le (hselected (n + 1)).1
      · simp only [σ, if_neg hn, if_neg hn']
        exact Nat.lt_succ_self n
  refine ⟨σ, hσ, ?_, ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop j] with n hn
    exact hmap n hn
  · apply squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ hεlim
    filter_upwards [eventually_ge_atTop j] with n hn
    simpa only [σ, if_pos hn] using ((hselected n).2.2.2.2.2 j hn).1
  · apply squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ hεlim
    filter_upwards [eventually_ge_atTop j] with n hn
    simpa only [σ, if_pos hn] using ((hselected n).2.2.2.2.2 j hn).2

end Erdos335.IntermediateScale

end
