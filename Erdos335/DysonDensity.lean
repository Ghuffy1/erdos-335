import Erdos335.LowerDensity
import Erdos335.DysonTransform
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Density invariants and the unbounded-gap case of Dyson's method

The joint lower density is necessary here because the derived inputs need not
have individual ordinary densities. The final theorem is the unbounded-gap
case in Kneser's reduction (equation (18) in the original proof).
-/

set_option autoImplicit false

open Filter Topology
open scoped Pointwise

namespace Erdos335

noncomputable def jointLowerDensity (A B : Set ℕ) : ℝ :=
  liminf (fun N : ℕ => ((count A N : ℝ) + count B N) / N) atTop

theorem jointCount_bounded_below (A B : Set ℕ) :
    IsBoundedUnder (· ≥ ·) atTop
      (fun N : ℕ => ((count A N : ℝ) + count B N) / N) := by
  refine ⟨0, ?_⟩
  change ∀ᶠ N : ℕ in atTop, 0 ≤ ((count A N : ℝ) + count B N) / N
  exact Eventually.of_forall fun N => by positivity

theorem jointCount_bounded_above (A B : Set ℕ) :
    IsBoundedUnder (· ≤ ·) atTop
      (fun N : ℕ => ((count A N : ℝ) + count B N) / N) := by
  refine ⟨2, ?_⟩
  change ∀ᶠ N : ℕ in atTop, ((count A N : ℝ) + count B N) / N ≤ 2
  apply Eventually.of_forall
  intro N
  rw [add_div]
  linarith [count_ratio_le_one A N, count_ratio_le_one B N]

theorem jointLowerDensity_eq_of_hasDensity {A B : Set ℕ} {a b : ℝ}
    (hA : HasDensity A a) (hB : HasDensity B b) : jointLowerDensity A B = a + b := by
  have h := hA.add hB
  simpa only [jointLowerDensity, ← add_div] using h.liminf_eq

theorem liminf_add_of_tendsto_zero {e f : ℕ → ℝ}
    (he : Tendsto e atTop (𝓝 0))
    (hflo : IsBoundedUnder (· ≥ ·) atTop f)
    (hfhi : IsBoundedUnder (· ≤ ·) atTop f) :
    liminf (e + f) atTop = liminf f atTop := by
  apply le_antisymm
  · have h := liminf_add_le he.isBoundedUnder_ge he.isBoundedUnder_le hflo
      hfhi.isCobounded_flip
    simpa only [he.limsup_eq, zero_add] using h
  · have h := le_liminf_add he.isBoundedUnder_ge he.isBoundedUnder_le hflo
      hfhi.isCobounded_flip
    simpa only [he.liminf_eq, zero_add] using h

theorem DysonDerived.jointLowerDensity_eq {A B C D : Set ℕ}
    (h : DysonDerived A B C D) : jointLowerDensity C D = jointLowerDensity A B := by
  have hz := h.count_difference_tendsto
  have hlim := liminf_add_of_tendsto_zero hz
    (jointCount_bounded_below A B) (jointCount_bounded_above A B)
  unfold jointLowerDensity
  change _ = liminf (fun N : ℕ => ((count A N : ℝ) + count B N) / N) atTop at hlim
  rw [← hlim]
  apply liminf_congr
  apply Eventually.of_forall
  intro N
  simp only [Pi.add_apply]
  ring

theorem jointLowerDensity_le_upperDensity_add_lowerDensity (A B : Set ℕ) :
    jointLowerDensity A B ≤ upperDensity B + lowerDensity A := by
  have h := liminf_add_le (count_ratio_bounded_below B) (count_ratio_bounded_above B)
    (count_ratio_bounded_below A) (count_ratio_bounded_above A).isCobounded_flip
  unfold jointLowerDensity upperDensity lowerDensity
  convert h using 1
  apply liminf_congr
  apply Eventually.of_forall
  intro N
  simp only [Pi.add_apply]
  ring

def Separated (B : Set ℕ) (f : ℕ) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B, a < b → f ≤ b - a

theorem count_le_div_add_one_of_separated {B : Set ℕ} {f : ℕ}
    (hf : 0 < f) (hB : Separated B f) (N : ℕ) : count B N ≤ N / f + 1 := by
  classical
  let T := (Finset.Icc 1 N).filter (· ∈ B)
  have hinj : Set.InjOn (fun n : ℕ => n / f) (T : Set ℕ) := by
    intro a ha b hb hab
    have haB := (Finset.mem_filter.mp ha).2
    have hbB := (Finset.mem_filter.mp hb).2
    have haMod := Nat.mod_lt a hf
    have hbMod := Nat.mod_lt b hf
    have haRep := Nat.div_add_mod a f
    have hbRep := Nat.div_add_mod b f
    change a / f = b / f at hab
    rw [hab] at haRep
    rcases lt_trichotomy a b with hlt | heq | hgt
    · have h := hB a haB b hbB hlt
      omega
    · exact heq
    · have h := hB b hbB a haB hgt
      omega
  have hsub : T.image (fun n => n / f) ⊆ Finset.range (N / f + 1) := by
    intro n hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
    have haN := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).2
    have h : a / f ≤ N / f := Nat.div_le_div_right haN
    exact Finset.mem_range.mpr (by omega)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at hcard
  exact hcard

theorem upperDensity_le_inv_of_separated {B : Set ℕ} {f : ℕ}
    (hf : 0 < f) (hB : Separated B f) : upperDensity B ≤ 1 / (f : ℝ) := by
  have hbound : ∀ N : ℕ, (count B N : ℝ) / N ≤ 1 / (f : ℝ) + 1 / (N : ℝ) := by
    intro N
    rcases eq_or_ne N 0 with rfl | hN
    · simp only [Nat.cast_zero, div_zero, add_zero]
      positivity
    have hcard := count_le_div_add_one_of_separated hf hB N
    have hdiv := Nat.div_mul_le_self N f
    have hNat : count B N * f ≤ N + f := by nlinarith
    have hReal : (count B N : ℝ) * f ≤ N + f := by exact_mod_cast hNat
    have hfR : (0 : ℝ) < f := by exact_mod_cast hf
    have hNR : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    apply (div_le_iff₀ hNR).mpr
    apply (le_of_mul_le_mul_right ?_ hfR)
    calc
      (count B N : ℝ) * f ≤ N + f := hReal
      _ = (1 / (f : ℝ) + 1 / (N : ℝ)) * N * f := by field_simp
  have hlo := count_ratio_bounded_below B
  have hhi : IsBoundedUnder (· ≤ ·) atTop
      (fun N : ℕ => 1 / (f : ℝ) + 1 / (N : ℝ)) := by
    exact ((tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat 1)) :
      Tendsto (fun N : ℕ => 1 / (f : ℝ) + 1 / (N : ℝ)) atTop
        (𝓝 (1 / (f : ℝ) + 0))).isBoundedUnder_le
  have h := limsup_le_limsup (Eventually.of_forall hbound) hlo.isCobounded_flip hhi
  have ht := (tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat 1) :
    Tendsto (fun N : ℕ => 1 / (f : ℝ) + 1 / (N : ℝ)) atTop
      (𝓝 (1 / (f : ℝ) + 0)))
  simpa only [upperDensity, ht.limsup_eq, add_zero] using h

theorem DysonDerived.lowerDensity_sum_ge_of_separated {A B C D : Set ℕ} {f : ℕ}
    (h : DysonDerived A B C D) (hA : 0 ∈ A) (hB : 0 ∈ B)
    (hf : 0 < f) (hD : Separated D f) :
    jointLowerDensity A B - 1 / (f : ℝ) ≤ lowerDensity (A + B) := by
  have hzero := (h.zero_mem hA hB).2
  have hCS : C ⊆ A + B := by
    intro c hc
    exact h.sum_subset ⟨c, hc, 0, hzero, by simp⟩
  have hmass := jointLowerDensity_le_upperDensity_add_lowerDensity C D
  rw [h.jointLowerDensity_eq] at hmass
  have hlow := lowerDensity_mono hCS
  have hupp := upperDensity_le_inv_of_separated hf hD
  linarith

theorem lowerDensity_sum_ge_of_unbounded_dyson_gaps (A B : Set ℕ)
    (hA : 0 ∈ A) (hB : 0 ∈ B)
    (hgap : ∀ f : ℕ, 0 < f → ∃ C D : Set ℕ, DysonDerived A B C D ∧ Separated D f) :
    jointLowerDensity A B ≤ lowerDensity (A + B) := by
  have hlim := (tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat 1) :
    Tendsto (fun N : ℕ => jointLowerDensity A B - 1 / (N : ℝ)) atTop
      (𝓝 (jointLowerDensity A B - 0)))
  apply le_of_tendsto (by simpa only [sub_zero] using hlim)
  filter_upwards [eventually_ge_atTop 1] with N hN
  obtain ⟨C, D, h, hsep⟩ := hgap N (by omega)
  exact h.lowerDensity_sum_ge_of_separated hA hB (by omega) hsep

end Erdos335
