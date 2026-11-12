import Erdos335.PeriodicSummandClassification
import Erdos335.RegularSummandGlobal
import Erdos335.Sufficiency

/-!
# The proposed classification for pairs with a regular input

The unrestricted FullSolution proposition remains a separate obligation.
-/

set_option autoImplicit false

open Filter Set Topology
open scoped Pointwise

namespace Erdos335.Proposed

theorem SingletonBranch.swap {A B : Set ℕ} (h : SingletonBranch A B) : SingletonBranch B A := by
  obtain ⟨f, x, hxpos, hxlt, hcase⟩ := h
  exact ⟨f.swap, x, hxpos, hxlt, hcase.symm⟩

theorem MaskBranch.swap {A B : Set ℕ} {s : ℝ} (h : MaskBranch A B s) : MaskBranch B A s := by
  obtain ⟨hdC, q, FA, FB, hAq, hBq, hFA, hFB, hcover⟩ :=
    (maskBranch_iff_common_period_finite_translate_cover A B s).mp h
  apply (maskBranch_iff_common_period_finite_translate_cover B A s).mpr
  refine ⟨by simpa only [add_comm B A] using hdC, q, FB, FA, hBq, hAq, hFB, hFA, ?_⟩
  simpa only [finiteTranslateCover, add_comm B A, Set.union_comm] using hcover

theorem regular_summand_strict_classification
    (A B : Set ℕ) (a b : ℝ) (hA : A ⊆ Set.Ioi 0) (hB : B ⊆ Set.Ioi 0)
    (ha : 0 < a) (hb : 0 < b) (hdA : HasDensity A a) (hdB : HasDensity B b)
    (hdC : HasDensity (A + B) (a + b)) (hgap : a + b < gamma A B)
    (happroxA : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ+,
      ((residues (k : ℕ) A).card : ℝ) / (k : ℕ) ≤ a + ε) :
    SingletonBranch A B ∨ MaskBranch A B (a + b) := by
  rcases exists_periodic_summand_of_regular_capacity A B a b hA hB ha hb hdA hdB hdC hgap happroxA with
    ⟨h, P, hAP⟩ | ⟨h, Q, hBQ⟩
  · exact periodic_summand_classified A B a b hA hB ha hb hdA hdB hdC hgap h P hAP
  · have hgamma : gamma B A = gamma A B := by
      unfold gamma modularCapacity
      congr 1
      funext m
      rw [add_comm]
    have hC : HasDensity (B + A) (b + a) := by simpa only [add_comm] using hdC
    have hgap' : b + a < gamma B A := by simpa only [hgamma, add_comm b a] using hgap
    rcases periodic_summand_classified B A b a hB hA hb ha hdB hdA hC hgap' h Q hBQ with hs | hm
    · exact Or.inl hs.swap
    · exact Or.inr (by simpa only [add_comm b a] using hm.swap)

theorem classification_iff_of_regular_capacity
    (A B : Set ℕ) (a b : ℝ) (hA : A ⊆ Set.Ioi 0) (hB : B ⊆ Set.Ioi 0)
    (ha : 0 < a) (hb : 0 < b) (hdA : HasDensity A a) (hdB : HasDensity B b)
    (happroxA : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ+,
      ((residues (k : ℕ) A).card : ℝ) / (k : ℕ) ≤ a + ε) :
    HasDensity (A + B) (a + b) ↔ Classified A B (a + b) := by
  constructor
  · intro hdC
    have hle := density_sum_le_gamma hA hB hdC
    rcases eq_or_lt_of_le hle with heq | hlt
    · exact Or.inl heq.symm
    · rcases regular_summand_strict_classification A B a b hA hB ha hb hdA hdB hdC hlt happroxA with hs | hm
      · exact Or.inr ⟨hlt, Or.inr (Or.inl hs)⟩
      · exact Or.inr ⟨hlt, Or.inr (Or.inr hm)⟩
  · intro hc
    exact hc.hasDensity hA hB hdA hdB

end Erdos335.Proposed
