import Erdos335.CompactDysonTransform

/-!
# Coset containment along a nonempty Dyson sequence
-/

set_option autoImplicit false

open Set
open scoped Pointwise

namespace Erdos335.Loeb

theorem dysonGroup_preserves_cosets
    {G : Type*} [AddCommGroup G] (H : AddSubgroup G)
    (A B : Set G) (a b e : G)
    (hA : A ⊆ a +ᵥ (H : Set G)) (hB : B ⊆ b +ᵥ (H : Set G))
    (hR : (dysonGroupRight A B e).Nonempty) :
    dysonGroupLeft A B e ⊆ a +ᵥ (H : Set G) ∧
      dysonGroupRight A B e ⊆ b +ᵥ (H : Set G) := by
  obtain ⟨r, hrB, hrA⟩ := hR
  obtain ⟨u, hu, hru⟩ := hB hrB
  obtain ⟨v, hv, hrv⟩ := hA hrA
  constructor
  · intro x hx
    rcases hx with hxA | ⟨y, hy, rfl⟩
    · exact hA hxA
    · obtain ⟨w, hw, hyw⟩ := hB hy
      refine ⟨v - u + w, H.add_mem (H.sub_mem hv hu) hw, ?_⟩
      change a + v = e + r at hrv
      change b + u = r at hru
      change b + w = y at hyw
      change a + (v - u + w) = e + y
      calc
        a + (v - u + w) = (a + v) - (b + u) + (b + w) := by abel
        _ = e + y := by rw [hrv, hru, hyw]; abel
  · exact fun x hx => hB hx.1

theorem dyson_chain_preserves_cosets
    {G : Type*} [AddCommGroup G] (H : AddSubgroup G)
    (A B : ℕ → Set G) (e : ℕ → G) (a b : G)
    (hA : A 0 ⊆ a +ᵥ (H : Set G)) (hB : B 0 ⊆ b +ᵥ (H : Set G))
    (hleft : ∀ n, A (n + 1) = dysonGroupLeft (A n) (B n) (e n))
    (hright : ∀ n, B (n + 1) = dysonGroupRight (A n) (B n) (e n))
    (hBne : ∀ n, (B n).Nonempty) :
    ∀ n, A n ⊆ a +ᵥ (H : Set G) ∧ B n ⊆ b +ᵥ (H : Set G) := by
  intro n
  induction n with
  | zero => exact ⟨hA, hB⟩
  | succ n ih =>
    rw [hleft n, hright n]
    exact dysonGroup_preserves_cosets H (A n) (B n) a b (e n) ih.1 ih.2
      (hright n ▸ hBne (n + 1))

end Erdos335.Loeb
