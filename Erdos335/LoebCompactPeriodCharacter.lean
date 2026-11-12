import Erdos335.LoebInternalCharacters
import Erdos335.CompactFourierUniqueness
import Erdos335.CompactFourierPeriods
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# A nontrivial character trivial on the essential stabilizer
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise ComplexConjugate

noncomputable section

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]

local instance compactPeriodCharacterLoebSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
local instance compactPeriodCharacterCircleSpace : MeasurableSpace (Additive Circle) :=
    borel (Additive Circle)
local instance compactPeriodCharacterCircleBorel : BorelSpace (Additive Circle) := ⟨rfl⟩

theorem exists_nontrivial_internal_period_character
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (F : ℕ → ∀ n, X n →+ Additive Circle)
    [CompactSpace (countableUltralimitHom U F).range]
    (S : Set (countableUltralimitHom U F).range) (hS : MeasurableSet S)
    (hSpos : 0 < Measure.map (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU) S)
    (hSlt : Measure.map (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU) S < 1) :
    ∃ p ∈ internalCharacterFunctions U F, p ≠ 1 ∧
      (∫ x, S.indicator (fun _ => (1 : ℂ)) x * conj (p x)
        ∂Measure.map (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU)) ≠ 0 ∧
      ∀ t, t +ᵥ S =ᵐ[Measure.map (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU)] S →
        p t = 1 := by
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
  have : Measure.IsAddHaarMeasure ν := countableUltralimitHom_haar U hU F
  let f : K → ℂ := S.indicator fun _ => 1
  have hexists : ∃ p ∈ internalCharacterFunctions U F, p ≠ 1 ∧
      (∫ x, f x * conj (p x) ∂ν) ≠ 0 := by
    by_contra hn
    have hzero (p : C(K, ℂ)) (hp : p ∈ internalCharacterFunctions U F) (hne : p ≠ 1) :
        (∫ x, f x * conj (p x) ∂ν) = 0 := by
      by_contra hc
      exact hn ⟨p, hp, hne, hc⟩
    let c : ℂ := ∫ x, f x ∂ν
    have hf : MemLp f 2 ν := by
      apply MemLp.of_bound (measurable_const.indicator hS).aestronglyMeasurable 1
      exact ae_of_all ν fun x => by by_cases hx : x ∈ S <;> simp [f, hx]
    have hg : MemLp (fun _ : K => c) 2 ν := memLp_const c
    have hfc : f =ᵐ[ν] fun _ => c := by
      apply ae_eq_of_separating_multiplicative_integrals ν (internalCharacterFunctions U F)
        (one_mem_internalCharacterFunctions U F)
        (fun p hp q hq => mul_mem_internalCharacterFunctions U F p q hp hq)
        (star_mem_internalCharacterFunctions U F) (internalCharacterFunctions_separate U F)
        f (fun _ => c) hf hg
      intro p hp
      by_cases hpone : p = 1
      · simp [hpone, c]
      · have hmean : (∫ x, conj (p x) ∂ν) = 0 := by
          by_contra hc
          obtain ⟨χ, hχ⟩ := internalCharacterFunctions_addChar U F p hp
          have hcoeff : (∫ x, (1 : ℂ) * conj (χ x : ℂ) ∂ν) ≠ 0 := by
            simpa only [one_mul, hχ] using hc
          apply hpone
          ext t
          have ht := character_eq_one_of_period_and_nonzero_coefficient ν χ
            (fun _ => (1 : ℂ)) t Filter.EventuallyEq.rfl hcoeff
          exact (hχ t).symm.trans (congrArg (fun z : Circle => (z : ℂ)) ht)
        rw [hzero p hp hpone, integral_const_mul, hmean, mul_zero]
    obtain ⟨x, hx⟩ := hfc.exists
    have hc : c = 0 ∨ c = 1 := by
      by_cases hs : x ∈ S
      · right
        simpa only [f, Set.indicator_of_mem hs] using hx.symm
      · left
        simpa only [f, Set.indicator_of_notMem hs] using hx.symm
    rcases hc with hc | hc
    · have hnull : S ≤ᵐ[ν] (∅ : Set K) := by
        filter_upwards [hfc] with x hx
        intro hs
        simp [f, hs, hc] at hx
      have hm : ν S = 0 := by simpa using ae_le_set.mp hnull
      exact hSpos.ne' hm
    · have hfull : S =ᵐ[ν] (univ : Set K) := by
        filter_upwards [hfc] with x hx
        have hs : x ∈ S := by
          by_contra hnS
          simp [f, hnS, hc] at hx
        simp [hs]
      have hm : ν S = 1 := by simpa using measure_congr hfull
      exact (ne_of_lt hSlt) hm
  obtain ⟨p, hp, hne, hcoeff⟩ := hexists
  obtain ⟨χ, hχ⟩ := internalCharacterFunctions_addChar U F p hp
  have hcoeffχ : (∫ x, S.indicator (fun _ => (1 : ℂ)) x * conj (χ x : ℂ) ∂ν) ≠ 0 := by
    simpa only [f, hχ] using hcoeff
  refine ⟨p, hp, hne, hcoeff, ?_⟩
  intro t ht
  exact (hχ t).symm.trans (congrArg (fun z : Circle => (z : ℂ))
    (fourier_character_trivial_on_ae_stabilizer ν χ S hcoeffχ t ht))

end Erdos335.Loeb

end
