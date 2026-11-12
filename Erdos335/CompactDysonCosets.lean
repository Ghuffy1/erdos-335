import Erdos335.CompactDysonTransform

/-!
# Recovering original cosets from a Dyson sequence
-/

set_option autoImplicit false

open Set
open scoped Pointwise

namespace Erdos335.Loeb

theorem dyson_chain_coset_ancestry
    {G : Type*} [AddCommGroup G]
    (H : AddSubgroup G) (C D : ℕ → Set G) (e : ℕ → G)
    (hstep : ∀ n, C (n + 1) = dysonGroupLeft (C n) (D n) (e n))
    (n : ℕ) (a b : G) (hC : C n ⊆ a +ᵥ (H : Set G)) (hD : D n ⊆ b +ᵥ (H : Set G)) :
    ∃ a₀ b₀ : G, C 0 ⊆ a₀ +ᵥ (H : Set G) ∧ D 0 ⊆ b₀ +ᵥ (H : Set G) := by
  induction n generalizing a b with
  | zero => exact ⟨a, b, hC, hD⟩
  | succ n ih =>
    have hCprev : C n ⊆ a +ᵥ (H : Set G) := by
      apply Subset.trans _ hC
      rw [hstep n]
      exact subset_union_left
    have hDprev : D n ⊆ (a - e n) +ᵥ (H : Set G) := by
      intro x hx
      have hxnext : e n + x ∈ C (n + 1) := by
        rw [hstep n]
        exact Or.inr ⟨x, hx, rfl⟩
      obtain ⟨k, hk, hka⟩ := hC hxnext
      refine ⟨k, hk, ?_⟩
      change a + k = e n + x at hka
      change (a - e n) + k = x
      calc
        (a - e n) + k = (a + k) - e n := by abel
        _ = x := by rw [hka]; simp
    exact ih a (a - e n) hCprev hDprev

end Erdos335.Loeb
