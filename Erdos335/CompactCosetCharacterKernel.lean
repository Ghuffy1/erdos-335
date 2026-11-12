import Erdos335.CompactOpenSubgroupKernel
import Erdos335.TranslatedCompactPairs

/-!
# The finite-kernel criterion for inputs in translated connected cosets
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

namespace Erdos335.Loeb

theorem finite_character_kernel_on_connected_cosets
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure]
    (H : OpenAddSubgroup G) [ConnectedSpace H] (a b : G)
    (S : Set G) (hSm : MeasurableSet S) (hSH : S ⊆ (a + b) +ᵥ (H : Set G))
    (hperiod : ∀ t : G, t +ᵥ S =ᵐ[μ] S → t = 0)
    (A B : ℕ → Set G)
    (hAH : ∀ n, A n ⊆ a +ᵥ (H : Set G)) (hBH : ∀ n, B n ⊆ b +ᵥ (H : Set G))
    (hBm : ∀ n, MeasurableSet (B n)) (hBpos : ∀ n, 0 < μ (B n))
    (hsum : ∀ n, A n + B n =ᵐ[μ] S)
    (hmass : ∀ n, μ S = μ (A n) + μ (B n))
    (hlocal : ∀ V ∈ 𝓝 (0 : G), ∀ᶠ n in atTop, B n - B n ⊆ V)
    (χ : H →+ AddCircle (1 : ℝ)) (hχ : Continuous χ) (hχne : χ ≠ 0) :
    Finite χ.ker := by
  let T : Set G := -(a + b) +ᵥ S
  let P (n : ℕ) : Set G := -a +ᵥ A n
  let Q (n : ℕ) : Set G := -b +ᵥ B n
  have shift_measure (E : Set G) (c : G) : μ (c +ᵥ E) = μ E := by
    rw [vadd_set_eq_neg_preimage, measure_preimage_add]
  have shift_measurable (E : Set G) (hE : MeasurableSet E) (c : G) :
      MeasurableSet (c +ᵥ E) := by
    rw [vadd_set_eq_neg_preimage]
    exact hE.preimage (measurable_const.add measurable_id)
  have shift_subset (E : Set G) (c : G) (hE : E ⊆ c +ᵥ (H : Set G)) :
      -c +ᵥ E ⊆ H := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨h, hh, rfl⟩ := hE hy
    simpa only [vadd_eq_add, neg_add_cancel_left] using hh
  have hTperiod (t : G) (ht : t +ᵥ T =ᵐ[μ] T) : t = 0 :=
    hperiod t ((ae_period_translate_iff μ S (-(a + b)) t).mp ht)
  have hsumT (n : ℕ) : P n + Q n =ᵐ[μ] T := by
    change (-a +ᵥ A n) + (-b +ᵥ B n) =ᵐ[μ] -(a + b) +ᵥ S
    rw [translate_pair_sum]
    simpa only [neg_add] using (vadd_set_ae_eq (-(a + b))).mpr (hsum n)
  have hmassT (n : ℕ) : μ T = μ (P n) + μ (Q n) := by
    change μ (-(a + b) +ᵥ S) = μ (-a +ᵥ A n) + μ (-b +ᵥ B n)
    simp only [shift_measure]
    exact hmass n
  have hlocalQ : ∀ V ∈ 𝓝 (0 : G), ∀ᶠ n in atTop, Q n - Q n ⊆ V := by
    intro V hV
    simpa only [Q, translate_set_difference] using hlocal V hV
  exact finite_character_kernel_on_connected_open_subgroup μ H T
    (shift_measurable S hSm _) (shift_subset S (a + b) hSH) hTperiod P Q
    (fun n => shift_subset (A n) a (hAH n)) (fun n => shift_subset (B n) b (hBH n))
    (fun n => shift_measurable (B n) (hBm n) _) (fun n => by
      change 0 < μ (-b +ᵥ B n)
      rw [shift_measure]
      exact hBpos n) hsumT hmassT hlocalQ χ hχ hχne

end Erdos335.Loeb
