import Erdos335.AEIntervalFromTranslation
import Erdos335.PeriodicCutoffLoss
import Erdos335.UnitIntervalCutoffDerivative

/-!
# Interval structure for a periodic indicator with sharp translation loss
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology MeasureTheory

namespace Erdos335.Loeb

theorem periodic_indicator_ae_interval_of_translation_bound
    (S : Set ℝ) (hS : MeasurableSet S)
    (hperiod : Function.Periodic (S.indicator (fun _ => (1 : ℝ))) 1)
    (hzero : 0 ∉ S)
    (hderiv : HasDerivAt (fun y => ∫ x in 0..y, S.indicator (fun _ => (1 : ℝ)) x) 0 0)
    (hpositive : 0 < volume (S ∩ Ioo (0 : ℝ) 1))
    (t m : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 0))
    (htpos : ∀ n, 0 < t n) (htone : ∀ n, t n < 1) (hm : Tendsto m atTop (𝓝 1))
    (hloss : ∀ n, (∫ x in 0..1,
      max (S.indicator (fun _ => (1 : ℝ)) x -
        S.indicator (fun _ => (1 : ℝ)) (x + t n)) 0) ≤ m n * t n) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧ S ∩ Ioo 0 1 =ᵐ[volume] Ioo a b := by
  let f : ℝ → ℝ := S.indicator fun _ => 1
  let T : Set ℝ := S ∩ Ioo 0 1
  have hf : LocallyIntegrable f volume := (locallyIntegrable_const (1 : ℝ)).indicator hS
  have hnonneg (x : ℝ) : 0 ≤ f x := by by_cases hx : x ∈ S <;> simp [f, hx]
  have hfzero : f 0 = 0 := indicator_of_notMem hzero _
  have hcut : (Ioo (0 : ℝ) 1).indicator f = T.indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hxS : x ∈ S <;> by_cases hxI : x ∈ Ioo (0 : ℝ) 1 <;> simp [f, T, hxS, hxI]
  have hboundary : HasDerivAt (fun y => ∫ x in 0..y, T.indicator (fun _ => (1 : ℝ)) x) 0 1 := by
    have h := periodic_unit_cutoff_derivative_zero f hf hperiod hfzero hderiv
    rwa [hcut] at h
  let q (n : ℕ) : ℝ := (∫ x in 0..t n, f x) / t n
  have hright : Tendsto t atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall htpos⟩
  have hq : Tendsto q atTop (𝓝 0) := by
    have h := hderiv.tendsto_slope_zero_right.comp hright
    simpa only [q, f, Function.comp_def, zero_add, intervalIntegral.integral_same,
      sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using h
  let M (n : ℕ) : ℝ := m n + q n
  have hM : Tendsto M atTop (𝓝 1) := by simpa only [add_zero] using hm.add hq
  apply ae_interval_of_sharp_translation_bound T (hS.inter measurableSet_Ioo)
    inter_subset_right hpositive hboundary t M ht htpos hM
  intro n
  rw [← hcut]
  calc
    (∫ x in 0..1, max ((Ioo (0 : ℝ) 1).indicator f x -
        (Ioo (0 : ℝ) 1).indicator f (x + t n)) 0) ≤
        (∫ x in 0..1, max (f x - f (x + t n)) 0) + ∫ x in 0..t n, f x :=
      periodic_cutoff_translation_loss_le f hf hperiod hnonneg (t n) (htpos n) (htone n)
    _ ≤ m n * t n + ∫ x in 0..t n, f x := add_le_add (hloss n) le_rfl
    _ = M n * t n := by
      dsimp [M, q]
      rw [add_mul, div_mul_cancel₀ _ (htpos n).ne']

end Erdos335.Loeb
