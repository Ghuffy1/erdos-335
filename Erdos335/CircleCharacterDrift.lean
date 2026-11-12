import Erdos335.ArcDensity
import Erdos335.LoebCompactHom
import Mathlib.Analysis.Normed.Group.AddCircle

/-!
# Real lifts of convergent circle characters and their integral drift
-/

set_option autoImplicit false

open Filter Set Topology

noncomputable section

namespace Erdos335.Loeb

theorem exists_circle_lifts_tendsto_zero
    {ι : Type*} (L : Filter ι) (f : ι → AddCircle (1 : ℝ)) (r : ℝ)
    (hf : Tendsto f L (𝓝 (r : AddCircle (1 : ℝ)))) :
    ∃ ε : ι → ℝ, Tendsto ε L (𝓝 0) ∧
      ∀ i, f i = ((r + ε i : ℝ) : AddCircle (1 : ℝ)) := by
  classical
  choose a ha using fun i => QuotientAddGroup.mk_surjective (f i - (r : AddCircle (1 : ℝ)))
  let ε : ι → ℝ := fun i => a i - round (a i)
  have hεcoe (i : ι) : (ε i : AddCircle (1 : ℝ)) = (a i : AddCircle (1 : ℝ)) := by
    apply NumStability.coe_eq_coe_iff_exists_int_sub_eq.mpr
    refine ⟨-round (a i), ?_⟩
    dsimp only [ε]
    simp only [Int.cast_neg]
    ring
  have habs (i : ι) : |ε i| = ‖f i - (r : AddCircle (1 : ℝ))‖ := by
    rw [← ha i]
    simp only [ε, AddCircle.norm_eq, inv_one, one_mul, mul_one]
  have habslim : Tendsto (fun i => |ε i|) L (𝓝 0) := by
    have hsub : Tendsto (fun i => f i - (r : AddCircle (1 : ℝ))) L (𝓝 0) := by
      simpa only [sub_self] using hf.sub
        (tendsto_const_nhds : Tendsto (fun _ : ι => (r : AddCircle (1 : ℝ))) L (𝓝 (r : AddCircle (1 : ℝ))))
    simpa only [norm_zero, ← habs] using hsub.norm
  have hlim : Tendsto ε L (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Real.norm_eq_abs] using habslim
  refine ⟨ε, hlim, ?_⟩
  intro i
  rw [AddCircle.coe_add, hεcoe, ha i]
  abel

theorem cyclic_character_integral_drift
    (q : ℕ+) (χ : ZMod (q : ℕ) →+ AddCircle (1 : ℝ)) (r ε : ℝ)
    (hr : (q : ℕ) • (r : AddCircle (1 : ℝ)) = 0)
    (hχ : χ 1 = ((r + ε : ℝ) : AddCircle (1 : ℝ))) :
    ∃ d : ℤ, (d : ℝ) = (q : ℕ) * ε := by
  have hzero : (q : ℕ) • χ 1 = 0 := by
    rw [← map_nsmul]
    simp only [nsmul_eq_mul, mul_one, ZMod.natCast_self, map_zero]
  rw [hχ, AddCircle.coe_add, smul_add, hr, zero_add, Proposed.nsmul_coe_real] at hzero
  obtain ⟨d, hd⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero
  exact ⟨d, by simpa only [zsmul_eq_mul, mul_one] using hd⟩

end Erdos335.Loeb

end
