import Erdos335.PositiveDensityScaleSelection
import Erdos335.CircleCharacterDrift
import Erdos335.LoebCompactHom

/-!
# Actual sublinear translates for an unbounded rational drift

Privately checked supporting development.
The input density concerns the actual elements divisible by the fixed modulus.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology

noncomputable section

namespace Erdos335.Loeb

private theorem select_sublinear_drift_multiple
    (U : Ultrafilter ℕ) (q : ℕ → ℕ+) (ell : ℕ+)
    (A : Set ℕ) (ρ : ℝ)
    (hA : HasDensity {u | u ∈ A ∧ (ell : ℕ) ∣ u} ρ) (hρ : 0 < ρ)
    (ε : ℕ → ℝ) (σ : ℝ) (hε : Tendsto ε (U : Filter ℕ) (𝓝 0))
    (hpositive : ∀ᶠ n in U, 0 < σ * ε n)
    (hlarge : Tendsto (fun n => (σ * ε n) * (q n : ℕ)) (U : Filter ℕ) atTop)
    (t : ℝ) (ht : 0 < t) :
    ∃ u : ℕ → ℕ,
      (∀ n, u n ∈ A ∧ (ell : ℕ) ∣ u n) ∧
      Tendsto (fun n => (u n : ℝ) / (q n : ℕ)) (U : Filter ℕ) (𝓝 0) ∧
      Tendsto (fun n => (σ * ε n) * (u n : ℝ)) (U : Filter ℕ) (𝓝 t) := by
  let η : ℕ → ℝ := fun n => σ * ε n
  let H : ℕ → ℝ := fun n => (η n)⁻¹
  have hη : Tendsto η (U : Filter ℕ) (𝓝 0) := by
    simpa only [η, mul_zero] using (tendsto_const_nhds (x := σ)).mul hε
  have hηpos : ∀ᶠ n in U, η n ∈ Ioi (0 : ℝ) := hpositive
  have hηwithin : Tendsto η (U : Filter ℕ) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hη, hηpos⟩
  have hH : Tendsto H (U : Filter ℕ) atTop :=
    tendsto_inv_nhdsGT_zero.comp hηwithin
  obtain ⟨u, hu, _, hratio, _⟩ := exists_positive_density_scale_selection
    (U : Filter ℕ) {u | u ∈ A ∧ (ell : ℕ) ∣ u} ρ hA hρ H hH t ht
  have hHq : Tendsto (fun n => H n / (q n : ℕ)) (U : Filter ℕ) (𝓝 0) := by
    have hinv := hlarge.inv_tendsto_atTop
    convert hinv using 1
    ext n
    change (σ * ε n)⁻¹ / (q n : ℕ) = ((σ * ε n) * (q n : ℕ))⁻¹
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hsmallProduct : Tendsto (fun n => ((u n : ℝ) / H n) * (H n / (q n : ℕ)))
      (U : Filter ℕ) (𝓝 0) := by
    simpa only [mul_zero] using hratio.mul hHq
  have hcancel :
      (fun n => ((u n : ℝ) / H n) * (H n / (q n : ℕ))) =ᶠ[U]
        (fun n => (u n : ℝ) / (q n : ℕ)) := by
    filter_upwards [hpositive] with n hn
    have hHne : H n ≠ 0 := inv_ne_zero (ne_of_gt hn)
    exact div_mul_div_cancel₀ hHne
  have hsmall : Tendsto (fun n => (u n : ℝ) / (q n : ℕ)) (U : Filter ℕ) (𝓝 0) :=
    (tendsto_congr' hcancel).mp hsmallProduct
  have hphase : Tendsto (fun n => (σ * ε n) * (u n : ℝ)) (U : Filter ℕ) (𝓝 t) := by
    convert hratio using 1
    ext n
    simp only [H, η, div_eq_mul_inv, inv_inv]
    ring
  exact ⟨u, hu, hsmall, hphase⟩

private theorem exists_positive_circle_lift (z : AddCircle (1 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ (t : AddCircle (1 : ℝ)) = z := by
  letI : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let v := AddCircle.equivIoc (1 : ℝ) 0 z
  exact ⟨v.val, v.property.1, AddCircle.coe_equivIoc⟩

theorem exists_sublinear_character_phase_of_unbounded_drift
    (U : Ultrafilter ℕ) (q : ℕ → ℕ+) (ell : ℕ+)
    (A : Set ℕ) (ρ : ℝ)
    (hA : HasDensity {u | u ∈ A ∧ (ell : ℕ) ∣ u} ρ) (hρ : 0 < ρ)
    (χ : ∀ n, ZMod (q n : ℕ) →+ AddCircle (1 : ℝ))
    (r : ℝ) (hr : (ell : ℕ) • (r : AddCircle (1 : ℝ)) = 0)
    (ε : ℕ → ℝ) (hε : Tendsto ε (U : Filter ℕ) (𝓝 0))
    (hχ : ∀ᶠ n in U, χ n 1 = ((r + ε n : ℝ) : AddCircle (1 : ℝ)))
    (hlarge : Tendsto (fun n => |ε n * (q n : ℕ)|) (U : Filter ℕ) atTop) :
    ∀ z : AddCircle (1 : ℝ), ∃ u : ℕ → ℕ,
      (∀ᶠ n in U, u n ∈ A) ∧
      Tendsto (fun n => (u n : ℝ) / (q n : ℕ)) (U : Filter ℕ) (𝓝 0) ∧
      ultralimitAddHom U χ (productProjection (U : Filter ℕ)
        (fun n => (u n : ZMod (q n : ℕ)))) = z := by
  have hnonzero : ∀ᶠ n in U, ε n ≠ 0 := by
    filter_upwards [hlarge.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hzero
    simpa only [hzero, zero_mul, abs_zero, lt_self_iff_false] using hn
  have hsign : (∀ᶠ n in U, 0 < ε n) ∨ ∀ᶠ n in U, ε n < 0 := by
    apply Ultrafilter.eventually_or.mp
    exact hnonzero.mono fun n hn => lt_or_gt_of_ne hn.symm
  have hmake (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
      (hpositive : ∀ᶠ n in U, 0 < σ * ε n)
      (hlargeσ : Tendsto (fun n => (σ * ε n) * (q n : ℕ)) (U : Filter ℕ) atTop)
      (z : AddCircle (1 : ℝ)) :
      ∃ u : ℕ → ℕ, (∀ᶠ n in U, u n ∈ A) ∧
        Tendsto (fun n => (u n : ℝ) / (q n : ℕ)) (U : Filter ℕ) (𝓝 0) ∧
        ultralimitAddHom U χ (productProjection (U : Filter ℕ)
          (fun n => (u n : ZMod (q n : ℕ)))) = z := by
    have hσsq : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
    have hlift : ∃ t : ℝ, 0 < t ∧ ((σ * t : ℝ) : AddCircle (1 : ℝ)) = z := by
      rcases hσ with rfl | rfl
      · obtain ⟨t, ht, htz⟩ := exists_positive_circle_lift z
        exact ⟨t, ht, by simpa only [one_mul] using htz⟩
      · obtain ⟨t, ht, htz⟩ := exists_positive_circle_lift (-z)
        refine ⟨t, ht, ?_⟩
        rw [neg_one_mul, AddCircle.coe_neg, htz, neg_neg]
    obtain ⟨t, ht, htz⟩ := hlift
    obtain ⟨u, hu, hsmall, hphaseσ⟩ := select_sublinear_drift_multiple U q ell A ρ hA hρ
      ε σ hε hpositive hlargeσ t ht
    have hrealPhase : Tendsto (fun n => ε n * (u n : ℝ)) (U : Filter ℕ) (𝓝 (σ * t)) := by
      have hm := (tendsto_const_nhds (x := σ)).mul hphaseσ
      convert hm using 1
      ext n
      simp only [← mul_assoc, hσsq, one_mul]
    have hchar (n : ℕ) (hnχ : χ n 1 = ((r + ε n : ℝ) : AddCircle (1 : ℝ))) :
        χ n (u n : ZMod (q n : ℕ)) = ((ε n * (u n : ℝ) : ℝ) : AddCircle (1 : ℝ)) := by
      have hgenerator : χ n (u n : ZMod (q n : ℕ)) = (u n) • χ n 1 := by
        rw [← map_nsmul]
        congr 1
        simp only [nsmul_eq_mul, mul_one]
      have hkill : (u n) • (r : AddCircle (1 : ℝ)) = 0 := by
        obtain ⟨k, hk⟩ := (hu n).2
        calc
          (u n) • (r : AddCircle (1 : ℝ)) = k • ((ell : ℕ) • (r : AddCircle (1 : ℝ))) := by
            simp only [hk, mul_nsmul, smul_comm (ell : ℕ) k]
          _ = 0 := by rw [hr, smul_zero]
      rw [hgenerator, hnχ, AddCircle.coe_add, smul_add, hkill, zero_add,
        Proposed.nsmul_coe_real]
      congr 1
      ring
    have hcirclePhase : Tendsto (fun n => χ n (u n : ZMod (q n : ℕ)))
        (U : Filter ℕ) (𝓝 z) := by
      have hc : Tendsto (fun n => ((ε n * (u n : ℝ) : ℝ) : AddCircle (1 : ℝ)))
          (U : Filter ℕ) (𝓝 ((σ * t : ℝ) : AddCircle (1 : ℝ))) :=
        (AddCircle.continuous_mk' (1 : ℝ)).continuousAt.tendsto.comp hrealPhase
      rw [htz] at hc
      exact hc.congr' (hχ.mono fun n hn => (hchar n hn).symm)
    have hmodelPhase := tendsto_ultralimitFunction U (fun n => χ n)
      (fun n => (u n : ZMod (q n : ℕ)))
    refine ⟨u, Eventually.of_forall fun n => (hu n).1, hsmall, ?_⟩
    exact tendsto_nhds_unique hmodelPhase hcirclePhase
  intro z
  rcases hsign with hpos | hneg
  · have hpositive : ∀ᶠ n in U, 0 < (1 : ℝ) * ε n := by simpa only [one_mul] using hpos
    have hlargeσ : Tendsto (fun n => ((1 : ℝ) * ε n) * (q n : ℕ))
        (U : Filter ℕ) atTop := by
      apply (tendsto_congr' ?_).mp hlarge
      filter_upwards [hpos] with n hn
      rw [abs_of_pos (mul_pos hn (by exact_mod_cast (q n).pos)), one_mul]
    exact hmake 1 (Or.inl rfl) hpositive hlargeσ z
  · have hpositive : ∀ᶠ n in U, 0 < (-1 : ℝ) * ε n := by
      filter_upwards [hneg] with n hn
      nlinarith
    have hlargeσ : Tendsto (fun n => ((-1 : ℝ) * ε n) * (q n : ℕ))
        (U : Filter ℕ) atTop := by
      apply (tendsto_congr' ?_).mp hlarge
      filter_upwards [hneg] with n hn
      rw [abs_of_neg (mul_neg_of_neg_of_pos hn (by exact_mod_cast (q n).pos))]
      ring
    exact hmake (-1) (Or.inr rfl) hpositive hlargeσ z

end Erdos335.Loeb

end
