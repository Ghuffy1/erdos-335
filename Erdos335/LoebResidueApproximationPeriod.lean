import Erdos335.LoebPeriodicCoverCore
import Erdos335.LoebWindowMaskBounds

/-!
# A finite mask from a fixed integer period and arbitrarily close residue covers
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance residueApproximationPeriodLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_periodic_mask_of_residue_approximation
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (S : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) (hSm : MeasurableSet S)
    (a : ℝ) (hmass : (loebMeasure U hU S).toReal = a)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ (k : ℕ+) (R : Finset (ZMod (k : ℕ))),
      S ≤ᵐ[loebMeasure U hU] (finiteQuotient U (fun n => naturalCyclicProjection (q n) k)) ⁻¹' (R : Set _) ∧
        (R.card : ℝ) / (k : ℕ) ≤ a + ε)
    (t : ℕ+)
    (hperiod : productProjection (U : Filter ℕ) (fun n => ((t : ℕ) : ZMod (q n : ℕ))) +ᵥ S
      =ᵐ[loebMeasure U hU] S) :
    ∃ R : Finset (ZMod (t : ℕ)), S =ᵐ[loebMeasure U hU]
      (finiteQuotient U (fun n => naturalCyclicProjection (q n) t)) ⁻¹' (R : Set _) := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ : Measure G := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let f := finiteQuotient U (fun n => naturalCyclicProjection (q n) t)
  have hnear (ε : ℝ) (hε : 0 < ε) : ∃ R : Finset (ZMod (t : ℕ)),
      S ≤ᵐ[μ] f ⁻¹' (R : Set _) ∧ (R.card : ℝ) / (t : ℕ) ≤ a + ε := by
    obtain ⟨k, R, hSR, hRmass⟩ := happrox ε hε
    let L := k * t
    have hkL : (k : ℕ) ∣ (L : ℕ) := ⟨t, rfl⟩
    have htL : (t : ℕ) ∣ (L : ℕ) := ⟨k, Nat.mul_comm _ _⟩
    let R' := Finset.univ.filter (fun r : ZMod (L : ℕ) => naturalCyclicProjection L k r ∈ R)
    have hRset : (R' : Set (ZMod (L : ℕ))) = (naturalCyclicProjection L k) ⁻¹' (R : Set _) := by
      ext r
      simp [R']
    have hpre : (finiteQuotient U (fun n => naturalCyclicProjection (q n) L)) ⁻¹' (R' : Set _) =
        (finiteQuotient U (fun n => naturalCyclicProjection (q n) k)) ⁻¹' (R : Set _) := by
      rw [hRset, ← natural_quotient_preimage_composition U q L k (hdiv L) hkL]
    obtain ⟨T, hST, hTsub⟩ := loeb_integer_period_cover_core U hU q L t htL (hdiv L) S hperiod R'
      (by rwa [hpre])
    rw [hpre] at hTsub
    refine ⟨T, hST, ?_⟩
    have hle := ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hTsub)
    rw [loebMeasure_naturalCyclicProjection_preimage U hU q t (hdiv t),
      loebMeasure_naturalCyclicProjection_preimage U hU q k (hdiv k),
      ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
      ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast] at hle
    exact hle.trans hRmass
  let F := fun n : ℕ => ∃ R : Finset (ZMod (t : ℕ)), R.card = n ∧ S ≤ᵐ[μ] f ⁻¹' (R : Set _)
  have hex : ∃ n, F n := by
    refine ⟨Finset.univ.card, Finset.univ, rfl, ?_⟩
    exact Filter.Eventually.of_forall fun x hx => by simp
  obtain ⟨R₀, hR₀card, hR₀⟩ := Nat.find_spec hex
  have hmin (R : Finset (ZMod (t : ℕ))) (hR : S ≤ᵐ[μ] f ⁻¹' (R : Set _)) : R₀.card ≤ R.card := by
    rw [hR₀card]
    exact Nat.find_min' hex ⟨R, rfl, hR⟩
  have hupper : (R₀.card : ℝ) / (t : ℕ) ≤ a := by
    by_contra hn
    have hε : 0 < ((R₀.card : ℝ) / (t : ℕ) - a) / 2 := by linarith
    obtain ⟨T, hST, hT⟩ := hnear _ hε
    have hratio : (R₀.card : ℝ) / (t : ℕ) ≤ (T.card : ℝ) / (t : ℕ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hmin T hST) (by positivity)
    linarith
  have hmassCover : μ (f ⁻¹' (R₀ : Set _)) = μ S := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top μ _)).mp
    have hlo := ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hR₀)
    rw [loebMeasure_naturalCyclicProjection_preimage U hU q t (hdiv t),
      ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast, hmass] at hlo ⊢
    exact le_antisymm hupper hlo
  exact ⟨R₀, ae_eq_of_ae_subset_of_measure_ge hR₀ hmassCover.le hSm.nullMeasurableSet (measure_ne_top μ _)⟩

end Erdos335.Loeb

end
