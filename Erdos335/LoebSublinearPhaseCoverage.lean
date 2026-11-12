import Erdos335.LoebSublinearWindowTranslations
import Erdos335.LoebPrefixAgreement
import Erdos335.LoebTranslationStructure
import Erdos335.StabilizerPullback

/-!
# Full output from sublinear actual translates with arbitrary phases
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance phaseCoverageLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_full_of_all_phase_translates
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ AddCircle (1 : ℝ))
    (P C : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (J : Set (AddCircle (1 : ℝ))) (hJ : (interior J).Nonempty)
    (hmodel : P =ᵐ[loebMeasure U hU] φ ⁻¹' J)
    (hphase : ∀ z : AddCircle (1 : ℝ),
      ∃ t : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)),
        φ t = z ∧ t +ᵥ P ≤ᵐ[loebMeasure U hU] C) :
    C =ᵐ[loebMeasure U hU] univ := by
  classical
  obtain ⟨F, hF⟩ := compact_covered_by_add_left_translates
    (isCompact_univ : IsCompact (univ : Set (AddCircle (1 : ℝ)))) hJ
  have hlocal (g : AddCircle (1 : ℝ)) :
      φ ⁻¹' ((-g) +ᵥ J) ≤ᵐ[loebMeasure U hU] C := by
    obtain ⟨t, ht, hsub⟩ := hphase (-g)
    have heq := loeb_vadd_congr_ae U hU P (φ ⁻¹' J) t hmodel
    rw [← preimage_vadd_addHom, ht] at heq
    exact heq.symm.le.trans hsub
  have hall : ∀ g : (F : Set (AddCircle (1 : ℝ))),
      ∀ᵐ x ∂loebMeasure U hU, φ x ∈ (-g.val) +ᵥ J → x ∈ C := by
    intro g
    exact hlocal g.val
  filter_upwards [ae_all_iff.mpr hall] with x hx
  have hmem := hF (mem_univ (φ x))
  obtain ⟨g, hg, hgx⟩ := mem_iUnion₂.mp hmem
  have hgin : φ x ∈ (-g) +ᵥ J := by
    rw [vadd_set_eq_neg_preimage]
    simpa only [mem_preimage, neg_neg] using hgx
  have hCx := hx ⟨g, hg⟩ hgin
  exact propext ⟨fun _ => trivial, fun _ => hCx⟩

theorem sum_density_one_of_sublinear_phase_surjectivity
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (A B : Set ℕ) (c : ℝ) (hC : HasDensity (A + B) c)
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ AddCircle (1 : ℝ))
    (J : Set (AddCircle (1 : ℝ))) (hJ : (interior J).Nonempty)
    (hmodel : internalSet U
      (fun n => (cyclicWindow B 0 (q n : ℕ) : Set (ZMod (q n : ℕ))))
        =ᵐ[loebMeasure U hU] φ ⁻¹' J)
    (hphase : ∀ z : AddCircle (1 : ℝ), ∃ u : ℕ → ℕ,
      (∀ᶠ n in U, u n ∈ A) ∧
      Tendsto (fun n => (u n : ℝ) / (q n : ℕ)) (U : Filter ℕ) (𝓝 0) ∧
      φ (productProjection (U : Filter ℕ) (fun n => (u n : ZMod (q n : ℕ)))) = z) :
    c = 1 := by
  letI : IsProbabilityMeasure (loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU) :=
    isProbabilityMeasure_loebMeasure U hU
  have hfull := loeb_full_of_all_phase_translates U hU q φ
    (internalSet U (fun n => (cyclicWindow B 0 (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (internalSet U (fun n => (cyclicWindow (A + B) 0 (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    J hJ hmodel (by
      intro z
      obtain ⟨u, hu, hsmall, hz⟩ := hphase z
      exact ⟨_, hz, actual_sublinear_translate_subset_sum_window U hU q A B (fun _ => 0) u hu hsmall⟩)
  have hmass := loeb_zero_window_mass_of_density U hU q hq (A + B) c hC
  rw [measure_congr hfull, measure_univ, ENNReal.toReal_one] at hmass
  exact hmass.symm

end Erdos335.Loeb

end
