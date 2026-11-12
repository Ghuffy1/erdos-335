import Erdos335.CyclicModelConstruction
import Erdos335.LoebCyclicModelMeasures
import Erdos335.LoebCyclicModelContainment
import Erdos335.CyclicWindowDensityGeneral
import Erdos335.CyclicWindowLiteralLift

/-!
# Internal models retaining literal prefix elements
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.IntermediateScale

local instance cyclicConstructionLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := Loeb.loebMeasurableSpace U

theorem exists_intermediate_loeb_models
    (N : ℕ → ℕ) [∀ s, NeZero (N s)]
    (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (hprev : Tendsto (fun s => (N (s - 1) : ℝ) / N s) atTop (𝓝 0))
    (lower upper : ℕ → ℕ)
    (hlower : Tendsto lower atTop atTop) (hupper : Tendsto upper atTop atTop)
    (hgap : Tendsto (fun s => (upper s : ℝ) / lower s) atTop atTop)
    (hupperN : ∀ᶠ s in atTop, upper s ≤ N s)
    (Aset Bset : Set ℕ) (a b c : ℝ) (hB : HasDensity Bset b)
    (hAerror : Tendsto (fun s => prefixError Aset a (N s) / lower s) atTop (𝓝 0))
    (hCerror : Tendsto (fun s => prefixError (Aset + Bset) c (N s) / lower s) atTop (𝓝 0))
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
    ∃ (τ : ℕ → ℕ) (q : ℕ → ℕ+) (start : ℕ → ℕ)
      (D : ∀ s, Finset (ZMod (q s : ℕ))) (E : ℕ → Finset ℕ),
      StrictMono τ ∧ Tendsto (fun s => (q s : ℕ)) atTop atTop ∧
      Tendsto (fun s => ((q s : ℕ) : ℝ) / N (τ s)) atTop (𝓝 0) ∧
      Tendsto (fun s => (lower (τ s) : ℝ) / (q s : ℕ)) atTop (𝓝 0) ∧
      (∀ M : ℕ, 0 < M → ∀ᶠ s in atTop, M ∣ (q s : ℕ)) ∧
      (∀ᶠ s in atTop, start s + (q s : ℕ) ≤ N (τ s)) ∧
      (∀ s, D s ⊆ cyclicWindow Aset (start s) (q s : ℕ)) ∧
      (∀ s, (E s : Set ℕ) ⊆ Bset) ∧
      (∀ v ∈ Bset, ∀ᶠ s in atTop, v ∈ E s) ∧
      (Loeb.loebMeasure U hU
        (Loeb.internalSet U (fun s => (D s : Set (ZMod (q s : ℕ)))))).toReal = a ∧
      (Loeb.loebMeasure U hU
        (Loeb.internalSet U (fun s => ((↑) : ℕ → ZMod (q s : ℕ)) '' (E s : Set ℕ)))).toReal = b ∧
      (Loeb.loebMeasure U hU
        (Loeb.internalSet U (fun s => (D s : Set (ZMod (q s : ℕ)))) +
          Loeb.internalSet U (fun s => ((↑) : ℕ → ZMod (q s : ℕ)) '' (E s : Set ℕ)))).toReal ≤ c ∧
      (Loeb.internalSet U (fun s => (D s : Set (ZMod (q s : ℕ)))) =ᵐ[Loeb.loebMeasure U hU]
        Loeb.internalSet U (fun s => (cyclicWindow Aset (start s) (q s : ℕ) : Set (ZMod (q s : ℕ))))) ∧
      (Loeb.internalSet U (fun s => ((↑) : ℕ → ZMod (q s : ℕ)) '' (E s : Set ℕ)) =ᵐ[Loeb.loebMeasure U hU]
        Loeb.internalSet U (fun s => (cyclicWindow Bset 0 (q s : ℕ) : Set (ZMod (q s : ℕ))))) ∧
      (Loeb.loebMeasure U hU (Loeb.internalSet U
        (fun s => (cyclicWindow (Aset + Bset) (start s) (q s : ℕ) : Set (ZMod (q s : ℕ)))))).toReal = c ∧
      (Loeb.internalSet U (fun s => (D s : Set (ZMod (q s : ℕ)))) +
          Loeb.internalSet U (fun s => ((↑) : ℕ → ZMod (q s : ℕ)) '' (E s : Set ℕ)) ≤ᵐ[Loeb.loebMeasure U hU]
        Loeb.internalSet U (fun s => (cyclicWindow (Aset + Bset) (start s) (q s : ℕ) :
          Set (ZMod (q s : ℕ))))) := by
  classical
  obtain ⟨τ, q, start, D, P, hτ, hq, hqN, hloq, hdiv, hinside, hsub,
    hexhaust, hD, hP, hC, hspill⟩ :=
    exists_intermediate_cyclic_models N hN hmono hprev lower upper hlower hupper hgap
      hupperN Aset Bset a b c hB hAerror hCerror U hU
  let E (s : ℕ) : Finset ℕ := cyclicLift (P s)
  have himage (s : ℕ) :
      ((↑) : ℕ → ZMod (q s : ℕ)) '' (E s : Set ℕ) = (P s : Set (ZMod (q s : ℕ))) := by
    rw [← Finset.coe_image]
    exact congrArg (fun S : Finset (ZMod (q s : ℕ)) => (S : Set (ZMod (q s : ℕ))))
      (cyclicLift_image (P s))
  have hAerrorq : Tendsto (fun s => prefixError Aset a (N (τ s)) / (q s : ℕ)) atTop (𝓝 0) := by
    have ht := (hAerror.comp hτ.tendsto_atTop).mul hloq
    simp only [mul_zero] at ht
    apply ht.congr'
    filter_upwards [(hlower.comp hτ.tendsto_atTop).eventually (eventually_gt_atTop 0)] with s hs
    have hl : (lower (τ s) : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
    dsimp only [Function.comp_def]
    field_simp
  have hAwindow := cyclic_window_density_of_general_prefix_error Aset a
    (N ∘ τ) (fun s => (q s : ℕ)) start hq hinside hAerrorq
  have hBwindow : Tendsto (fun s => ((cyclicWindow Bset 0 (q s : ℕ)).card : ℝ) / (q s : ℕ))
      atTop (𝓝 b) := by
    have hb := ((hasDensity_iff_prefixCount Bset b).mp hB).comp hq
    have hzero : tailShift Bset 0 = Bset := by ext n; simp [tailShift]
    simpa only [Function.comp_def, cyclicWindow_card_eq_prefixCount, hzero] using hb
  refine ⟨τ, q, start, D, E, hτ, hq, hqN, hloq, hdiv, hinside,
    (fun s => (hsub s).1), (fun s => cyclicLift_subset Bset (P s) (hsub s).2),
    cyclicLift_exhaustion Bset (fun s => (q s : ℕ)) hq P hexhaust, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Loeb.loeb_finset_measure_eq U hU q D a hD
  · simpa only [himage] using Loeb.loeb_finset_measure_eq U hU q P b hP
  · simpa only [himage] using
      Loeb.loeb_cyclic_sum_measure_le U hU q D P
        (fun s => cyclicWindow (Aset + Bset) (start s) (q s : ℕ)) c hC hspill
  · exact Loeb.loeb_finset_ae_eq_of_same_density U hU q D
      (fun s => cyclicWindow Aset (start s) (q s : ℕ)) a (fun s => (hsub s).1) hD hAwindow
  · simpa only [himage] using Loeb.loeb_finset_ae_eq_of_same_density U hU q P
      (fun s => cyclicWindow Bset 0 (q s : ℕ)) b (fun s => (hsub s).2) hP hBwindow
  · exact Loeb.loeb_finset_measure_eq U hU q
      (fun s => cyclicWindow (Aset + Bset) (start s) (q s : ℕ)) c hC
  · simpa only [himage] using Loeb.loeb_cyclic_sum_ae_subset U hU q D P
      (fun s => cyclicWindow (Aset + Bset) (start s) (q s : ℕ)) hspill

end Erdos335.IntermediateScale

end
