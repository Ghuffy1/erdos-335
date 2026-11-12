import Erdos335.CompactCharacterDensity

/-!
# Uniqueness from continuous Fourier tests

Equality against a separating multiplicative family determines a
square-integrable function almost everywhere.
-/

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped ENNReal ComplexConjugate

namespace Erdos335.Loeb

theorem inner_continuous_test_toLp
    {G : Type*} [TopologicalSpace G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsFiniteMeasure μ]
    (ψ : C(G, ℂ)) (f : G → ℂ) (hf : MemLp f 2 μ) :
    inner ℂ (ContinuousMap.toLp 2 μ ℂ ψ) (hf.toLp f) =
      ∫ x, f x * conj (ψ x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ ψ, hf.coeFn_toLp] with x hψ hfx
  simp only [RCLike.inner_apply, hψ, hfx, mul_comm]

theorem ae_eq_of_separating_multiplicative_integrals
    {G : Type*} [TopologicalSpace G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.WeaklyRegular] [IsFiniteMeasure μ]
    (S : Set C(G, ℂ)) (hone : (1 : C(G, ℂ)) ∈ S)
    (hmul : ∀ f ∈ S, ∀ g ∈ S, f * g ∈ S)
    (hstar : ∀ f ∈ S, star f ∈ S)
    (hsep : ∀ x y : G, x ≠ y → ∃ f ∈ S, f x ≠ f y)
    (f g : G → ℂ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hcoeff : ∀ ψ ∈ S, (∫ x, f x * conj (ψ x) ∂μ) = ∫ x, g x * conj (ψ x) ∂μ) :
    f =ᵐ[μ] g := by
  have heq : hf.toLp f = hg.toLp g := by
    apply separating_multiplicative_L2_ext μ S hone hmul hstar hsep
    intro ψ hψ
    simpa only [inner_continuous_test_toLp] using hcoeff ψ hψ
  calc
    f =ᵐ[μ] hf.toLp f := hf.coeFn_toLp.symm
    _ =ᵐ[μ] hg.toLp g := EventuallyEq.of_eq (congrArg (fun z : Lp ℂ 2 μ => (z : G → ℂ)) heq)
    _ =ᵐ[μ] g := hg.coeFn_toLp

end Erdos335.Loeb
