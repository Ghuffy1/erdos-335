import Erdos335.CircleCellPolynomials

/-!
# Error bounds for finite products of polynomial approximants
-/

set_option autoImplicit false

open Finset
open scoped BigOperators Classical

namespace Erdos335.IntermediateScale

theorem norm_prod_le_two_pow {I : Type*} (S : Finset I) (f : I → ℂ)
    (hf : ∀ i ∈ S, ‖f i‖ ≤ 2) : ‖∏ i ∈ S, f i‖ ≤ 2 ^ S.card := by
  rw [norm_prod]
  calc
    _ ≤ ∏ _i ∈ S, (2 : ℝ) := prod_le_prod₀ (fun _ _ => norm_nonneg _) hf
    _ = _ := by simp

theorem norm_prod_approximation {I : Type*} (S : Finset I) (f g : I → ℂ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hf : ∀ i ∈ S, ‖f i‖ ≤ 1) (hg : ∀ i ∈ S, ‖g i‖ ≤ 2)
    (herr : ∀ i ∈ S, ‖f i - g i‖ ≤ ε) :
    ‖(∏ i ∈ S, f i) - ∏ i ∈ S, g i‖ ≤ S.card * ε * 2 ^ S.card := by
  revert hf hg herr
  induction S using Finset.induction_on with
  | empty => intro hf hg herr; simp
  | @insert a S ha ih =>
    intro hf hg herr
    have hfS := fun i hi => hf i (mem_insert_of_mem hi)
    have hgS := fun i hi => hg i (mem_insert_of_mem hi)
    have heS := fun i hi => herr i (mem_insert_of_mem hi)
    have hstep := ih hfS hgS heS
    have hprod := norm_prod_le_two_pow S g hgS
    have hfa := hf a (mem_insert_self _ _)
    have herra := herr a (mem_insert_self _ _)
    rw [prod_insert ha, prod_insert ha, card_insert_of_notMem ha]
    have heq : f a * (∏ i ∈ S, f i) - g a * (∏ i ∈ S, g i) =
        f a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i) + (f a - g a) * ∏ i ∈ S, g i := by ring
    rw [heq]
    calc
      _ ≤ ‖f a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i)‖ +
          ‖(f a - g a) * ∏ i ∈ S, g i‖ := norm_add_le _ _
      _ = ‖f a‖ * ‖(∏ i ∈ S, f i) - ∏ i ∈ S, g i‖ +
          ‖f a - g a‖ * ‖∏ i ∈ S, g i‖ := by rw [norm_mul, norm_mul]
      _ ≤ 1 * (S.card * ε * 2 ^ S.card) + ε * 2 ^ S.card := by
        gcongr
      _ ≤ ((S.card + 1 : ℕ) : ℝ) * ε * 2 ^ (S.card + 1) := by
        rw [pow_succ]
        push_cast
        have hnonneg : 0 ≤ ((S.card : ℝ) + 1) * ε * 2 ^ S.card := by positivity
        nlinarith

end Erdos335.IntermediateScale
