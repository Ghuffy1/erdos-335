import Erdos335.FiniteTranslationCore
import Erdos335.NaturalKernelGenerators
import Erdos335.LoebIntegerPeriods

/-!
# Refining a finite cover using one fixed integer translation period
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance periodicCoverCoreLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_integer_period_cover_core
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (L t : ℕ+) (htL : (t : ℕ) ∣ (L : ℕ))
    (hd : ∀ᶠ n in U, (L : ℕ) ∣ (q n : ℕ))
    (S : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hperiod : productProjection (U : Filter ℕ) (fun n => ((t : ℕ) : ZMod (q n : ℕ))) +ᵥ S
      =ᵐ[loebMeasure U hU] S)
    (R : Finset (ZMod (L : ℕ)))
    (hcover : S ≤ᵐ[loebMeasure U hU]
      (finiteQuotient U (fun n => naturalCyclicProjection (q n) L)) ⁻¹' (R : Set _)) :
    ∃ T : Finset (ZMod (t : ℕ)),
      S ≤ᵐ[loebMeasure U hU] (finiteQuotient U (fun n => naturalCyclicProjection (q n) t)) ⁻¹' (T : Set _) ∧
      (finiteQuotient U (fun n => naturalCyclicProjection (q n) t)) ⁻¹' (T : Set _) ⊆
        (finiteQuotient U (fun n => naturalCyclicProjection (q n) L)) ⁻¹' (R : Set _) := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let g := finiteQuotient U (fun n => naturalCyclicProjection (q n) L)
  let f := finiteQuotient U (fun n => naturalCyclicProjection (q n) t)
  let π := naturalCyclicProjection L t
  let C := kernelCore π R
  let T := C.image π
  have hfor (z : ZMod (L : ℕ)) : ∀ᵐ x ∂loebMeasure U hU,
      x ∈ S → z ∈ π.ker → g x + z ∈ R := by
    by_cases hz : z ∈ π.ker
    · obtain ⟨n, hn⟩ := (naturalCyclicProjection_zero_iff_multiple L t htL z).mp hz
      let v : G := productProjection (U : Filter ℕ) (fun s => ((n * (t : ℕ) : ℕ) : ZMod (q s : ℕ)))
      have hp := loeb_period_nsmul U hU q S
        (productProjection (U : Filter ℕ) (fun s => ((t : ℕ) : ZMod (q s : ℕ)))) hperiod n
      rw [← productProjection_nat_mul U q n (t : ℕ)] at hp
      have hmem := loeb_translate_membership_ae U hU q S _ v (hp.le.trans hcover)
      have hv : g v = z := (finiteQuotient_natCast_of_eventually U q L
        (fun s => naturalCyclicProjection (q s) L)
        (hd.mono fun s hs k => naturalCyclicProjection_natCast (q s) L hs k) (n * (t : ℕ))).trans hn
      filter_upwards [hmem] with x hx hxS _
      have he := hx hxS
      change g (v + x) ∈ R at he
      rw [map_add, hv, add_comm] at he
      exact he
    · exact Filter.Eventually.of_forall fun _ _ h => (hz h).elim
  have hCore : S ≤ᵐ[loebMeasure U hU] g ⁻¹' (C : Set _) := by
    filter_upwards [ae_all_iff.mpr hfor] with x hx hxS
    exact (mem_kernelCore π R (g x)).mpr fun z hz => hx z hxS hz
  have hpull : f ⁻¹' (T : Set _) = g ⁻¹' (C : Set _) := by
    ext x
    have heq := congrArg (fun k => k x) (finiteQuotient_natural_refinement U q L t hd htL)
    change f x ∈ T ↔ g x ∈ C
    rw [← heq]
    exact Iff.of_eq (congrArg (fun V : Set (ZMod (L : ℕ)) => g x ∈ V) (kernelCore_preimage_image π R))
  refine ⟨T, ?_, ?_⟩
  · rw [hpull]
    exact hCore
  · rw [hpull]
    exact preimage_mono (kernelCore_subset π R)

end Erdos335.Loeb

end
