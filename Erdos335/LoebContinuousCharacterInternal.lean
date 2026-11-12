import Erdos335.LoebInternalCharacters
import Erdos335.CompactFourierUniqueness
import Erdos335.CompactFourierPeriods
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Continuous characters on a countable compact factor are internal
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]

local instance continuousCharacterLoebSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
local instance continuousCharacterCircleSpace : MeasurableSpace (Additive Circle) := borel (Additive Circle)
local instance continuousCharacterCircleBorel : BorelSpace (Additive Circle) := ⟨rfl⟩

theorem continuous_character_on_countable_factor_internal
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (F : ℕ → ∀ n, X n →+ Additive Circle)
    [CompactSpace (countableUltralimitHom U F).range]
    (χ : (countableUltralimitHom U F).range →+ Additive Circle) (hχ : Continuous χ) :
    ∃ ψ : ∀ n, X n →+ Additive Circle,
      χ.comp (countableUltralimitHom U F).rangeRestrict = ultralimitAddHom U ψ := by
  letI : MetricSpace (ℕ → Additive Circle) := PiCountable.metricSpace
  let K := (countableUltralimitHom U F).range
  let π := (countableUltralimitHom U F).rangeRestrict
  let μ := loebMeasure (X := X) U hU
  let ν := Measure.map π μ
  have hπ : Measurable π := (measurable_countableUltralimitHom U F).subtype_mk
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have : IsProbabilityMeasure ν := ⟨by
    rw [Measure.map_apply hπ MeasurableSet.univ]
    simp⟩
  have : ν.IsAddHaarMeasure := countableUltralimitHom_haar U hU F
  let f : K → ℂ := fun x => ((χ x).toMul : ℂ)
  have hfcontinuous : Continuous f := continuous_subtype_val.comp hχ
  have hfnorm (x : K) : ‖f x‖ = 1 := Circle.norm_coe _
  have hf : MemLp f 2 ν := MemLp.of_bound hfcontinuous.aestronglyMeasurable 1
    (ae_of_all ν fun x => (hfnorm x).le)
  have hexists : ∃ p ∈ internalCharacterFunctions U F,
      (∫ x, f x * conj (p x) ∂ν) ≠ 0 := by
    by_contra hn
    have hzero (p : C(K, ℂ)) (hp : p ∈ internalCharacterFunctions U F) :
        (∫ x, f x * conj (p x) ∂ν) = 0 := by
      by_contra hc
      exact hn ⟨p, hp, hc⟩
    have hfeq : f =ᵐ[ν] fun _ => (0 : ℂ) := by
      apply ae_eq_of_separating_multiplicative_integrals ν (internalCharacterFunctions U F)
        (one_mem_internalCharacterFunctions U F)
        (fun p hp q hq => mul_mem_internalCharacterFunctions U F p q hp hq)
        (star_mem_internalCharacterFunctions U F) (internalCharacterFunctions_separate U F)
        f (fun _ => 0) hf (memLp_const 0)
      intro p hp
      simpa only [zero_mul, integral_zero] using hzero p hp
    obtain ⟨x, hx⟩ := hfeq.exists
    have hxnorm := hfnorm x
    rw [hx, norm_zero] at hxnorm
    exact zero_ne_one hxnorm
  obtain ⟨p, hp, hcoeff⟩ := hexists
  obtain ⟨γ, hγ⟩ := internalCharacterFunctions_addChar U F p hp
  have hfadd (t x : K) : f (t + x) = f t * f x := by
    change ((χ (t + x)).toMul : ℂ) = ((χ t).toMul : ℂ) * ((χ x).toMul : ℂ)
    rw [map_add]
    rfl
  have hpeq (t : K) : f t = p t := by
    have htranslate := integral_translate_character ν γ f t
    have hleft : (∫ x, f (t + x) * conj (γ x : ℂ) ∂ν) =
        f t * ∫ x, f x * conj (p x) ∂ν := by
      simp_rw [hfadd, mul_assoc, hγ]
      exact integral_const_mul _ _
    rw [hleft, hγ] at htranslate
    have hcoeff' : (∫ x, f x * conj (γ x : ℂ) ∂ν) = ∫ x, f x * conj (p x) ∂ν := by
      simp only [hγ]
    rw [hcoeff'] at htranslate
    exact mul_right_cancel₀ hcoeff htranslate
  obtain ⟨ψ, hψ⟩ := hp
  refine ⟨fun n => (ψ n).toAddMonoidHom, ?_⟩
  ext x
  have heq : ((χ (π x)).toMul : ℂ) =
      ((ultralimitAddHom U (fun n => (ψ n).toAddMonoidHom) x).toMul : ℂ) :=
    (hpeq (π x)).trans (hψ x)
  exact heq

end Erdos335.Loeb

end
