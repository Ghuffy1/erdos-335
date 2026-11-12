import Erdos335.LoebCompactHom
import Erdos335.ArcDensity
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Real.Irrational

/-!
# Fixed torsion in surjective ultralimit characters

Privately checked supporting development.
Exact eventual annihilation of the coordinate generators would annihilate
the whole ultralimit image. Surjectivity rules this out for every positive
annihilator and forces the coordinate generator orders to tend to infinity.
-/

set_option autoImplicit false

open Filter Set Topology

namespace Erdos335.Loeb

private theorem zmod_hom_nsmul_eq_zero_of_generator
    {E : Type*} [AddCommGroup E] (q : ℕ+) (χ : ZMod (q : ℕ) →+ E)
    (m : ℕ) (hm : m • χ 1 = 0) (x : ZMod (q : ℕ)) :
    m • χ x = 0 := by
  have hx : x.val • (1 : ZMod (q : ℕ)) = x := by
    simpa only [nsmul_eq_mul, mul_one] using ZMod.natCast_zmod_val x
  calc
    m • χ x = m • χ (x.val • (1 : ZMod (q : ℕ))) :=
      congrArg (fun y => m • χ y) hx.symm
    _ = m • (x.val • χ 1) := by rw [map_nsmul]
    _ = x.val • (m • χ 1) := smul_comm m x.val (χ 1)
    _ = 0 := by rw [hm, smul_zero]

theorem ultralimit_character_nsmul_eq_zero_of_eventually
    (U : Ultrafilter ℕ) (q : ℕ → ℕ+)
    (χ : ∀ n, ZMod (q n : ℕ) →+ AddCircle (1 : ℝ))
    (m : ℕ) (hm : ∀ᶠ n in U, m • χ n 1 = 0)
    (x : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) :
    m • ultralimitAddHom U χ x = 0 := by
  induction x using Quotient.inductionOn with
  | h a =>
      have hlimit : Tendsto (fun n => m • χ n (a n)) (U : Filter ℕ)
          (𝓝 (m • ultralimitAddHom U χ
            (a : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))) := by
        exact (tendsto_ultralimitFunction U (fun n => χ n) a).nsmul m
      have heq : (fun n => m • χ n (a n)) =ᶠ[(U : Filter ℕ)]
          (fun _ => (0 : AddCircle (1 : ℝ))) :=
        hm.mono fun n hn => zmod_hom_nsmul_eq_zero_of_generator
          (q n) (χ n) m hn (a n)
      have hzero : Tendsto (fun n => m • χ n (a n)) (U : Filter ℕ)
          (𝓝 (0 : AddCircle (1 : ℝ))) :=
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : AddCircle (1 : ℝ)))
          (U : Filter ℕ) (𝓝 0)).congr' heq.symm
      exact tendsto_nhds_unique hlimit hzero

theorem loeb_character_not_eventually_fixed_torsion
    (U : Ultrafilter ℕ) (q : ℕ → ℕ+)
    (χ : ∀ n, ZMod (q n : ℕ) →+ AddCircle (1 : ℝ))
    (hsurj : Function.Surjective (ultralimitAddHom U χ)) (ell : ℕ+) :
    ¬ ∀ᶠ n in U, (ell : ℕ) • χ n 1 = 0 := by
  intro hkill
  obtain ⟨x, hx⟩ := hsurj ((Real.sqrt 2 : ℝ) : AddCircle (1 : ℝ))
  have hzero := ultralimit_character_nsmul_eq_zero_of_eventually U q χ
    (ell : ℕ) hkill x
  rw [hx] at hzero
  have hdvd : addOrderOf ((Real.sqrt 2 : ℝ) : AddCircle (1 : ℝ)) ∣ (ell : ℕ) :=
    (addOrderOf_dvd_iff_nsmul_eq_zero).mpr hzero
  rw [Erdos335.Proposed.irrational_addOrder irrational_sqrt_two] at hdvd
  exact ell.ne_zero (by simpa using hdvd)

theorem loeb_character_eventually_not_fixed_torsion
    (U : Ultrafilter ℕ) (q : ℕ → ℕ+)
    (χ : ∀ n, ZMod (q n : ℕ) →+ AddCircle (1 : ℝ))
    (hsurj : Function.Surjective (ultralimitAddHom U χ)) (ell : ℕ+) :
    ∀ᶠ n in U, (ell : ℕ) • χ n 1 ≠ 0 :=
  Ultrafilter.eventually_not.mpr
    (loeb_character_not_eventually_fixed_torsion U q χ hsurj ell)

theorem loeb_character_addOrder_tendsto_atTop
    (U : Ultrafilter ℕ) (q : ℕ → ℕ+)
    (χ : ∀ n, ZMod (q n : ℕ) →+ AddCircle (1 : ℝ))
    (hsurj : Function.Surjective (ultralimitAddHom U χ)) :
    Tendsto (fun n => addOrderOf (χ n 1)) (U : Filter ℕ) atTop := by
  apply tendsto_atTop.mpr
  intro K
  let ell : ℕ+ := ⟨Nat.factorial (K + 1), Nat.factorial_pos _⟩
  filter_upwards [loeb_character_eventually_not_fixed_torsion U q χ hsurj ell]
    with n hn
  have hfinite : IsOfFinAddOrder (χ n 1) :=
    (χ n).isOfFinAddOrder
      (isOfFinAddOrder_of_finite (1 : ZMod (q n : ℕ)))
  have hpositive : 0 < addOrderOf (χ n 1) := hfinite.addOrderOf_pos
  by_contra hsmall
  have hle : addOrderOf (χ n 1) ≤ K + 1 := by omega
  have hdvd : addOrderOf (χ n 1) ∣ (ell : ℕ) := by
    change addOrderOf (χ n 1) ∣ Nat.factorial (K + 1)
    exact Nat.dvd_factorial hpositive hle
  exact hn ((addOrderOf_dvd_iff_nsmul_eq_zero).mp hdvd)

end Erdos335.Loeb
