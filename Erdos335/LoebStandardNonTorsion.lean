import Erdos335.CircleCharacterDrift
import Erdos335.UltrafilterIntegerDrift
import Erdos335.LoebCharacterTorsion
import Erdos335.LoebUnboundedDriftPhases
import Erdos335.LoebBoundedDriftExclusion
import Erdos335.CircleDriftSeparation
import Erdos335.LoebSublinearPhaseCoverage

/-!
# Non-torsion of the standard character in an actual prefix model

Privately checked supporting development.
Positive ordinary density on the actual multiples of every fixed modulus
is retained explicitly on both inputs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance standardNonTorsionLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem standard_character_non_torsion_of_prefix_model
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (hdiv : ∀ ell : ℕ+, ∀ᶠ n in U, (ell : ℕ) ∣ (q n : ℕ))
    (A B : Set ℕ) (c : ℝ) (hC : HasDensity (A + B) c) (hc : c < 1)
    (hAdensity : ∀ ell : ℕ+, ∃ ρ : ℝ, 0 < ρ ∧
      HasDensity (A ∩ {u : ℕ | (ell : ℕ) ∣ u}) ρ)
    (hBdensity : ∀ ell : ℕ+, ∃ ρ : ℝ, 0 < ρ ∧
      HasDensity (B ∩ {u : ℕ | (ell : ℕ) ∣ u}) ρ)
    (χ : ∀ n, ZMod (q n : ℕ) →+ AddCircle (1 : ℝ))
    (hsurj : Function.Surjective (ultralimitAddHom U χ))
    (J : Set (AddCircle (1 : ℝ))) (hJclosed : IsClosed J) (hJnonempty : J.Nonempty)
    (hJproper : J ≠ univ) (hJinterior : (interior J).Nonempty)
    (hmodel : internalSet U
      (fun n => (cyclicWindow B 0 (q n : ℕ) : Set (ZMod (q n : ℕ))))
        =ᵐ[loebMeasure U hU] (ultralimitAddHom U χ) ⁻¹' J) :
    addOrderOf (ultralimitAddHom U χ (productProjection (U : Filter ℕ)
      (fun n => (1 : ZMod (q n : ℕ))))) = 0 := by
  classical
  let z := ultralimitAddHom U χ (productProjection (U : Filter ℕ)
    (fun n => (1 : ZMod (q n : ℕ))))
  change addOrderOf z = 0
  by_contra horder
  let ell : ℕ+ := ⟨addOrderOf z, Nat.pos_of_ne_zero horder⟩
  have hell : (ell : ℕ) • z = 0 := addOrderOf_nsmul_eq_zero z
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective z
  have hrkill : (ell : ℕ) • (r : AddCircle (1 : ℝ)) = 0 := by
    rw [hr]
    exact hell
  have hlimit : Tendsto (fun n => χ n 1) (U : Filter ℕ) (𝓝 (r : AddCircle (1 : ℝ))) := by
    have h := tendsto_ultralimitFunction U (fun n => χ n)
      (fun n => (1 : ZMod (q n : ℕ)))
    change Tendsto (fun n => χ n 1) (U : Filter ℕ) (𝓝 z) at h
    simpa only [hr] using h
  obtain ⟨ε, hε, hχ⟩ := exists_circle_lifts_tendsto_zero (U : Filter ℕ)
    (fun n => χ n 1) r hlimit
  have hintegral : ∀ᶠ n in U, ∃ k : ℤ, (k : ℝ) = (q n : ℕ) * ε n := by
    filter_upwards [hdiv ell] with n hn
    have hqkill : (q n : ℕ) • (r : AddCircle (1 : ℝ)) = 0 := by
      obtain ⟨k, hk⟩ := hn
      calc
        (q n : ℕ) • (r : AddCircle (1 : ℝ)) = k • ((ell : ℕ) • (r : AddCircle (1 : ℝ))) := by
          simp only [hk, mul_nsmul, smul_comm (ell : ℕ) k]
        _ = 0 := by rw [hrkill, smul_zero]
    exact cyclic_character_integral_drift (q n) (χ n) r (ε n) hqkill (hχ n)
  let d : ℕ → ℤ := fun n =>
    if h : ∃ k : ℤ, (k : ℝ) = (q n : ℕ) * ε n then h.choose else 0
  have hd : ∀ᶠ n in U, (d n : ℝ) = (q n : ℕ) * ε n := by
    filter_upwards [hintegral] with n hn
    simpa only [d, dif_pos hn] using hn.choose_spec
  have hcharacter (n a : ℕ) (ha : (ell : ℕ) ∣ a) :
      χ n (a : ZMod (q n : ℕ)) = ((ε n * (a : ℝ) : ℝ) : AddCircle (1 : ℝ)) := by
    have hgenerator : χ n (a : ZMod (q n : ℕ)) = a • χ n 1 := by
      rw [← map_nsmul]
      congr 1
      simp only [nsmul_eq_mul, mul_one]
    have hakill : a • (r : AddCircle (1 : ℝ)) = 0 := by
      obtain ⟨k, hk⟩ := ha
      calc
        a • (r : AddCircle (1 : ℝ)) = k • ((ell : ℕ) • (r : AddCircle (1 : ℝ))) := by
          simp only [hk, mul_nsmul, smul_comm (ell : ℕ) k]
        _ = 0 := by rw [hrkill, smul_zero]
    rw [hgenerator, hχ n, AddCircle.coe_add, smul_add, hakill, zero_add,
      Proposed.nsmul_coe_real]
    congr 1
    ring
  rcases integer_drift_constant_or_diverges U d with ⟨k, hfixed⟩ | hdiverges
  · have hrelation : ∀ᶠ n in U, (q n : ℕ) * ε n = (k : ℝ) := by
      filter_upwards [hd, hfixed] with n hn hkn
      rw [hkn] at hn
      exact hn.symm
    by_cases hk : k = 0
    · have hfixedTorsion : ∀ᶠ n in U, (ell : ℕ) • χ n 1 = 0 := by
        filter_upwards [hrelation] with n hn
        have hqne : ((q n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (q n).ne_zero
        have hεzero : ε n = 0 := by
          rw [hk, Int.cast_zero] at hn
          exact (mul_eq_zero.mp hn).resolve_left hqne
        rw [hχ n, hεzero, add_zero]
        exact hrkill
      exact loeb_character_not_eventually_fixed_torsion U q χ hsurj ell hfixedTorsion
    · obtain ⟨ρ, hρ, hBρ⟩ := hBdensity ell
      obtain ⟨u, α, β, v, η, hu, huα, hαβ, hβv, hv, hη, hsep⟩ :=
        exists_circle_drift_separated_interval k hk J hJclosed hJnonempty hJproper
      have hboundedCharacter : ∀ᶠ n in U, ∀ a ∈ B,
          (ell : ℕ) ∣ a → a < (q n : ℕ) → χ n (a : ZMod (q n : ℕ)) =
            (((k : ℝ) * (a : ℝ) / (q n : ℕ) : ℝ) : AddCircle (1 : ℝ)) := by
        filter_upwards [hrelation] with n hn a _ ha _
        have hqne : ((q n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (q n).ne_zero
        have heq : ε n = (k : ℝ) / (q n : ℕ) := by
          apply (eq_div_iff hqne).mpr
          simpa only [mul_comm] using hn
        rw [hcharacter n a ha, heq]
        congr 1
        ring
      exact loeb_bounded_drift_exclusion_of_separated_interval U hU q hq ell B ρ hρ hBρ
        χ k J hmodel hboundedCharacter u α β v η hu huα hαβ hβv hv hη hsep
  · have hcast : Tendsto (fun n => ((d n).natAbs : ℝ)) (U : Filter ℕ) atTop :=
      tendsto_natCast_atTop_atTop.comp hdiverges
    have habs (n : ℕ) : ((d n).natAbs : ℝ) = |(d n : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    have hlarge : Tendsto (fun n => |ε n * (q n : ℕ)|) (U : Filter ℕ) atTop := by
      apply (tendsto_congr' ?_).mp hcast
      filter_upwards [hd] with n hn
      rw [habs n, hn, mul_comm]
    obtain ⟨ρ, hρ, hAρ⟩ := hAdensity ell
    have hphases := exists_sublinear_character_phase_of_unbounded_drift U q ell A ρ
      hAρ hρ χ r hrkill ε hε (Eventually.of_forall hχ) hlarge
    have hcOne := sum_density_one_of_sublinear_phase_surjectivity U hU q hq A B c hC
      (ultralimitAddHom U χ) J hJinterior hmodel hphases
    exact (ne_of_lt hc) hcOne

end Erdos335.Loeb

end
