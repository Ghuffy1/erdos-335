import Erdos335.LoebWindowProfiles
import Erdos335.LoebResidueMaskProfiles
import Erdos335.PeriodicOutput

/-!
# Prefix models of ordinary periodic templates
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance periodicPrefixLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem periodic_template_residue_density
    (A : Set ℕ) (h : ℕ+) (R : Finset (ZMod (h : ℕ)))
    (hAR : DensityEquivalent A (periodicSet R)) (r : ZMod (h : ℕ)) :
    HasDensity (residueFiber A r) (if r ∈ R then (1 : ℝ) / (h : ℕ) else 0) := by
  classical
  by_cases hr : r ∈ R
  · rw [if_pos hr]
    have hsmall : Negligible (periodicSet ({r} : Finset (ZMod (h : ℕ))) \ residueFiber A r) := by
      apply hAR.2.mono
      rintro n ⟨hn, hout⟩
      have hnr : (n : ZMod (h : ℕ)) = r := by simpa only [Finset.mem_singleton] using hn.2
      refine ⟨⟨hn.1, hnr ▸ hr⟩, ?_⟩
      intro hnA
      exact hout ⟨hnA, hn⟩
    have hreverse : Negligible (residueFiber A r \ periodicSet ({r} : Finset (ZMod (h : ℕ)))) := by
      apply (show Negligible (∅ : Set ℕ) from hasDensity_empty).mono
      rintro n ⟨hn, hout⟩
      exact False.elim (hout hn.2)
    have heq : DensityEquivalent (periodicSet ({r} : Finset (ZMod (h : ℕ)))) (residueFiber A r) :=
      ⟨hsmall, hreverse⟩
    simpa only [Finset.card_singleton, Nat.cast_one] using heq.hasDensity (hasDensity_periodicSet {r})
  · rw [if_neg hr]
    apply hAR.1.mono
    rintro n ⟨hnA, hn⟩
    refine ⟨hnA, ?_⟩
    intro hnR
    have hnr : (n : ZMod (h : ℕ)) = r := by simpa only [Finset.mem_singleton] using hn.2
    exact hr (hnr ▸ hnR.2)

theorem loeb_prefix_residue_measure_of_density
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A : Set ℕ) (hA : A ⊆ Set.Ioi 0) (r : ZMod (h : ℕ)) (a : ℝ)
    (hdA : HasDensity (residueFiber A r) a) :
    (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A 0 (q n : ℕ) : Set (ZMod (q n : ℕ)))) ∩
        (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' {r})).toReal = a := by
  have hset : {n : ℕ | n ∈ A ∧ ((n - 0 : ℕ) : ZMod (h : ℕ)) = r} = residueFiber A r := by
    ext n
    constructor
    · rintro ⟨hn, hr⟩
      exact ⟨hn, hA hn, by simpa only [Nat.sub_zero, Finset.mem_singleton] using hr⟩
    · rintro ⟨hn, _, hr⟩
      exact ⟨hn, by simpa only [Nat.sub_zero, Finset.mem_singleton] using hr⟩
  have hp := loeb_window_residue_measure_tendsto U hU q h hd (fun _ => A) (fun _ => 0) r
  simp only [hset] at hp
  have hd := ((hasDensity_iff_prefixCount _ _).mp hdA).comp hq
  have hcounts : Tendsto (fun n => ((cyclicWindow (residueFiber A r) 0 (q n : ℕ)).card : ℝ) /
      (q n : ℕ)) atTop (𝓝 a) := by
    simpa only [Function.comp_def, cyclicWindow_card_eq_prefixCount, tailShift, add_zero, setOf_mem_eq] using hd
  exact tendsto_nhds_unique hp (hcounts.mono_left hU)

theorem loeb_prefix_mask_of_density_equivalence
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A : Set ℕ) (hA : A ⊆ Set.Ioi 0) (R : Finset (ZMod (h : ℕ)))
    (hAR : DensityEquivalent A (periodicSet R)) :
    internalSet U (fun n => (cyclicWindow A 0 (q n : ℕ) : Set (ZMod (q n : ℕ))))
      =ᵐ[loebMeasure U hU]
        (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' (R : Set _) := by
  apply loeb_ae_eq_residue_mask_of_profile U hU q h hd _ (measurable_internalSet U _) R
  intro r
  exact loeb_prefix_residue_measure_of_density U hU q hq h hd A hA r _
    (periodic_template_residue_density A h R hAR r)

end Erdos335.Loeb

end
