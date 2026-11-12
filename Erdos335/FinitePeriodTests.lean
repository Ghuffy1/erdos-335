import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
# Selecting a common period from finitely many candidates

If every finite collection of summand pairs has a period from one finite
family, one member of that family is a period of the entire sumset.
-/

set_option autoImplicit false

open Set
open scoped Pointwise

namespace Erdos335.Loeb

theorem exists_common_period_of_finite_tests
    {G I : Type*} [AddCommGroup G] [Fintype I]
    (A B : Set G) (H : I → AddSubgroup G)
    (htest : ∀ S T : Finset G, (↑S : Set G) ⊆ A → (↑T : Set G) ⊆ B →
      ∃ i, ∀ a ∈ S, ∀ b ∈ T, ∀ h ∈ H i, a + b + h ∈ A + B) :
    ∃ i, A + B + (H i : Set G) = A + B := by
  classical
  by_contra hnone
  have hbad (i : I) : ∃ a ∈ A, ∃ b ∈ B, ∃ h ∈ H i, a + b + h ∉ A + B := by
    by_contra hn
    push_neg at hn
    apply hnone
    refine ⟨i, le_antisymm ?_ ?_⟩
    · rintro z ⟨c, ⟨a, ha, b, hb, rfl⟩, h, hh, rfl⟩
      exact hn a ha b hb h hh
    · intro c hc
      exact ⟨c, hc, 0, (H i).zero_mem, add_zero c⟩
  choose a ha b hb h hh hnot using hbad
  let S := Finset.univ.image a
  let T := Finset.univ.image b
  have hSA : (↑S : Set G) ⊆ A := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact ha i
  have hTB : (↑T : Set G) ⊆ B := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hb i
  obtain ⟨i, hi⟩ := htest S T hSA hTB
  exact hnot i (hi (a i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    (b i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩) (h i) (hh i))

theorem exists_reciprocal_modulus_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ D : ℕ, ∀ h : ℕ+, δ ≤ (((h : ℕ) : ℝ))⁻¹ → (h : ℕ) ≤ D := by
  obtain ⟨D, hD⟩ := exists_nat_gt (1 / δ)
  refine ⟨D, fun h hh => ?_⟩
  have hpos : (0 : ℝ) < (h : ℕ) := by exact_mod_cast h.pos
  have hmul : δ * (h : ℕ) ≤ 1 := by
    have hb := mul_le_mul_of_nonneg_right hh hpos.le
    simpa only [inv_mul_cancel₀ hpos.ne'] using hb
  have hDmul : (1 : ℝ) < (D : ℝ) * δ := (div_lt_iff₀ hδ).mp hD
  by_contra hgt
  have hle : (D : ℝ) ≤ (h : ℕ) := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hgt))
  nlinarith

end Erdos335.Loeb
