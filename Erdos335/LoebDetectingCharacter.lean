import Erdos335.LoebCompactPeriodCharacter

/-!
# Characters detecting a specified non-period of a compact model
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise ComplexConjugate

noncomputable section

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]

local instance detectingCharacterLoebSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
local instance detectingCharacterCircleSpace : MeasurableSpace (Additive Circle) :=
    borel (Additive Circle)
local instance detectingCharacterCircleBorel : BorelSpace (Additive Circle) := ⟨rfl⟩

theorem exists_internal_character_detecting_nonperiod
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (F : ℕ → ∀ n, X n →+ Additive Circle)
    [CompactSpace (countableUltralimitHom U F).range]
    (S : Set (countableUltralimitHom U F).range) (hS : MeasurableSet S)
    (t : (countableUltralimitHom U F).range)
    (ht : ¬ t +ᵥ S =ᵐ[Measure.map (countableUltralimitHom U F).rangeRestrict
      (loebMeasure U hU)] S) :
    ∃ p ∈ internalCharacterFunctions U F, p t ≠ 1 ∧
      (∫ x, S.indicator (fun _ => (1 : ℂ)) x * conj (p x)
        ∂Measure.map (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU)) ≠ 0 ∧
      ∀ s, s +ᵥ S =ᵐ[Measure.map (countableUltralimitHom U F).rangeRestrict
        (loebMeasure U hU)] S → p s = 1 := by
  classical
  letI : MetricSpace (ℕ → Additive Circle) := PiCountable.metricSpace
  let K := (countableUltralimitHom U F).range
  let φ := (countableUltralimitHom U F).rangeRestrict
  let μ := loebMeasure (X := X) U hU
  let ν := Measure.map φ μ
  have hφ : Measurable φ := (measurable_countableUltralimitHom U F).subtype_mk
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have : IsProbabilityMeasure ν := ⟨by
    change Measure.map φ μ univ = 1
    rw [Measure.map_apply hφ MeasurableSet.univ]
    simp⟩
  have : ν.IsAddHaarMeasure := countableUltralimitHom_haar U hU F
  let f : K → ℂ := S.indicator fun _ => 1
  let g : K → ℂ := fun x => f (t + x)
  have hfm : Measurable f := measurable_const.indicator hS
  have hgm : Measurable g := hfm.comp (measurable_const.add measurable_id)
  have hfbound (x : K) : ‖f x‖ ≤ 1 := by
    by_cases hx : x ∈ S <;> simp [f, hx]
  have hf : MemLp f 2 ν := MemLp.of_bound hfm.aestronglyMeasurable 1 (ae_of_all ν hfbound)
  have hg : MemLp g 2 ν := MemLp.of_bound hgm.aestronglyMeasurable 1
    (ae_of_all ν fun x => hfbound (t + x))
  have hexists : ∃ p ∈ internalCharacterFunctions U F, p t ≠ 1 ∧
      (∫ x, f x * conj (p x) ∂ν) ≠ 0 := by
    by_contra hn
    have hgf : g =ᵐ[ν] f := by
      apply ae_eq_of_separating_multiplicative_integrals ν (internalCharacterFunctions U F)
        (one_mem_internalCharacterFunctions U F)
        (fun p hp q hq => mul_mem_internalCharacterFunctions U F p q hp hq)
        (star_mem_internalCharacterFunctions U F) (internalCharacterFunctions_separate U F)
        g f hg hf
      intro p hp
      obtain ⟨χ, hχ⟩ := internalCharacterFunctions_addChar U F p hp
      have htranslate : (∫ x, g x * conj (p x) ∂ν) =
          p t * ∫ x, f x * conj (p x) ∂ν := by
        simpa only [g, hχ] using integral_translate_character ν χ f t
      rw [htranslate]
      by_cases hc : (∫ x, f x * conj (p x) ∂ν) = 0
      · simp [hc]
      · have hpt : p t = 1 := by
          by_contra hpt
          exact hn ⟨p, hp, hpt, hc⟩
        rw [hpt, one_mul]
    have hneg : -t +ᵥ S =ᵐ[ν] S := by
      rw [vadd_set_eq_neg_preimage]
      filter_upwards [hgf] with x hx
      change (-(-t) + x ∈ S) = (x ∈ S)
      simp only [neg_neg]
      apply propext
      constructor
      · intro hs
        have hx' : (1 : ℂ) = f x := by simpa only [g, f, indicator_of_mem hs] using hx
        by_contra hxs
        simp [f, hxs] at hx'
      · intro hs
        have hx' : g x = (1 : ℂ) := by simpa only [f, indicator_of_mem hs] using hx
        by_contra hxs
        simp [g, f, hxs] at hx'
    have hmem : -t ∈ AddAction.aestabilizer K ν S := hneg
    have htmem : t ∈ AddAction.aestabilizer K ν S := by
      simpa only [neg_neg] using (AddAction.aestabilizer K ν S).neg_mem hmem
    exact ht htmem
  obtain ⟨p, hp, hpt, hcoeff⟩ := hexists
  obtain ⟨χ, hχ⟩ := internalCharacterFunctions_addChar U F p hp
  have hcoeffχ : (∫ x, S.indicator (fun _ => (1 : ℂ)) x * conj (χ x : ℂ) ∂ν) ≠ 0 := by
    simpa only [f, hχ] using hcoeff
  refine ⟨p, hp, hpt, hcoeff, ?_⟩
  intro s hs
  exact (hχ s).symm.trans (congrArg (fun z : Circle => (z : ℂ))
    (fourier_character_trivial_on_ae_stabilizer ν χ S hcoeffχ s hs))

end Erdos335.Loeb

end
