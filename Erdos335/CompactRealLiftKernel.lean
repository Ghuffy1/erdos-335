import Erdos335.CompactRealCoverLift
import Mathlib.GroupTheory.OrderOfElement

/-!
# The period of a lifted real homomorphism
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

namespace Erdos335.Loeb

theorem exists_positive_integer_period_of_real_lift
    {G : Type*} [AddCommGroup G]
    (φ : G →+ AddCircle (1 : ℝ)) [Finite φ.ker]
    (f : ℝ →+ G) (hlift : ∀ x : ℝ, φ (f x) = (x : AddCircle (1 : ℝ))) :
    ∃ n : ℕ, 0 < n ∧ f.ker = AddSubgroup.zmultiples (n : ℝ) := by
  let g : φ.ker := ⟨f 1, by
    change φ (f 1) = 0
    rw [hlift]
    exact AddCircle.coe_period (1 : ℝ)⟩
  let n : ℕ := addOrderOf g
  refine ⟨n, addOrderOf_pos g, ?_⟩
  have hfint (k : ℤ) : f (k : ℝ) = k • (g : G) := by
    change f (k : ℝ) = k • f 1
    rw [← map_zsmul]
    congr 1
    simp
  ext x
  constructor
  · intro hx
    have hxzero : f x = 0 := hx
    have hcircle : (x : AddCircle (1 : ℝ)) = 0 := by rw [← hlift, hxzero, map_zero]
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hcircle
    have hkx : (k : ℝ) = x := by simpa using hk
    have hkg : k • g = 0 := by
      apply Subtype.ext
      change k • (g : G) = 0
      rw [← hfint, hkx, hxzero]
    have hdiv : (n : ℤ) ∣ k := addOrderOf_dvd_iff_zsmul_eq_zero.mpr hkg
    obtain ⟨m, hm⟩ := hdiv
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨m, ?_⟩
    rw [← hkx, hm]
    push_cast
    simp [zsmul_eq_mul, mul_comm]
  · intro hx
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    change f x = 0
    rw [← hk, map_zsmul]
    have hn : f (n : ℝ) = 0 := by
      have hng : n • g = 0 := addOrderOf_nsmul_eq_zero g
      have hcoe : n • (g : G) = 0 := congrArg (fun z : φ.ker => (z : G)) hng
      have hf := hfint (n : ℤ)
      simpa only [Int.cast_natCast, natCast_zsmul] using hf.trans (by simpa using hcoe)
    rw [hn, smul_zero]

end Erdos335.Loeb
