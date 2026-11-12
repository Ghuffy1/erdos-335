import Erdos335.NaturalIntermediateScales
import Mathlib.Data.Prod.Lex

/-!
# Positive integer block lengths in a lexicographically separated scale family
-/

set_option autoImplicit false

open Filter Topology Set

namespace Erdos335.IntermediateScale

noncomputable def positiveIntermediateScale (lower upper : ℕ → ℕ) (a b : ℝ) (s : ℕ) : ℕ :=
  max 1 (naturalIntermediateScale lower upper a b s)

theorem positiveIntermediateScale_pos (lower upper : ℕ → ℕ) (a b : ℝ) (s : ℕ) :
    0 < positiveIntermediateScale lower upper a b s :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

theorem positiveIntermediateScale_eventually_eq (lower upper : ℕ → ℕ)
    (hlower : Tendsto lower atTop atTop)
    (hgap : Tendsto (fun s => (upper s : ℝ) / lower s) atTop atTop)
    (a b : ℝ) (ha : 0 < a) :
    positiveIntermediateScale lower upper a b =ᶠ[atTop] naturalIntermediateScale lower upper a b := by
  filter_upwards [(naturalIntermediateScale_atTop lower upper hlower hgap a b ha).eventually
    (eventually_ge_atTop 1)] with s hs
  exact max_eq_right hs

theorem positiveIntermediateScale_atTop (lower upper : ℕ → ℕ)
    (hlower : Tendsto lower atTop atTop)
    (hgap : Tendsto (fun s => (upper s : ℝ) / lower s) atTop atTop)
    (a b : ℝ) (ha : 0 < a) :
    Tendsto (positiveIntermediateScale lower upper a b) atTop atTop :=
  (naturalIntermediateScale_atTop lower upper hlower hgap a b ha).congr'
    (positiveIntermediateScale_eventually_eq lower upper hlower hgap a b ha).symm

theorem positiveIntermediateScale_lower_ratio (lower upper : ℕ → ℕ)
    (hlower : Tendsto lower atTop atTop)
    (hgap : Tendsto (fun s => (upper s : ℝ) / lower s) atTop atTop)
    (a b : ℝ) (ha : 0 < a) :
    Tendsto (fun s => (lower s : ℝ) / positiveIntermediateScale lower upper a b s) atTop (𝓝 0) := by
  apply (naturalIntermediateScale_lower_ratio lower upper hlower hgap a b ha).congr'
  filter_upwards [positiveIntermediateScale_eventually_eq lower upper hlower hgap a b ha] with s hs
  rw [hs]

theorem positiveIntermediateScale_ambient_ratio (lower upper N : ℕ → ℕ)
    (hlower : Tendsto lower atTop atTop) (hupper : Tendsto upper atTop atTop)
    (hgap : Tendsto (fun s => (upper s : ℝ) / lower s) atTop atTop)
    (hupperN : ∀ᶠ s in atTop, upper s ≤ N s)
    (a b : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    Tendsto (fun s => (positiveIntermediateScale lower upper a b s : ℝ) / N s) atTop (𝓝 0) := by
  have hr : Tendsto (fun s => (positiveIntermediateScale lower upper a b s : ℝ) / upper s)
      atTop (𝓝 0) := by
    apply (naturalIntermediateScale_upper_ratio lower upper hlower hupper hgap a b ha ha1).congr'
    filter_upwards [positiveIntermediateScale_eventually_eq lower upper hlower hgap a b ha] with s hs
    rw [hs]
  apply squeeze_zero' (Eventually.of_forall fun s => by positivity) ?_ hr
  filter_upwards [hupperN, hupper.eventually (eventually_gt_atTop 0)] with s hs hu
  have huR : (0 : ℝ) < upper s := by exact_mod_cast hu
  have hsR : (upper s : ℝ) ≤ N s := by exact_mod_cast hs
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) huR hsR

theorem positiveIntermediateScale_lexicographic_ratio (lower upper : ℕ → ℕ)
    (hlower : Tendsto lower atTop atTop)
    (hgap : Tendsto (fun s => (upper s : ℝ) / lower s) atTop atTop)
    (a b a' b' : ℝ) (ha : 0 < a) (ha' : 0 < a')
    (horder : a < a' ∨ (a = a' ∧ b < b')) :
    Tendsto (fun s => (positiveIntermediateScale lower upper a b s : ℝ) /
      positiveIntermediateScale lower upper a' b' s) atTop (𝓝 0) := by
  apply (naturalIntermediateScale_lexicographic_ratio lower upper hlower hgap a b a' b'
    ha ha' horder).congr'
  filter_upwards [positiveIntermediateScale_eventually_eq lower upper hlower hgap a b ha,
    positiveIntermediateScale_eventually_eq lower upper hlower hgap a' b' ha'] with s hs ht
  rw [hs, ht]

abbrev BlockScaleParameter := Icc (0 : ℝ) 1 ×ₗ Icc (0 : ℝ) 1

noncomputable def blockScaleExponent (p : BlockScaleParameter) : ℝ := ((ofLex p).1.val + 1) / 3

noncomputable def blockScaleFamily (lower upper : ℕ → ℕ) (p : BlockScaleParameter) : ℕ → ℕ :=
  positiveIntermediateScale lower upper (blockScaleExponent p) (ofLex p).2.val

theorem blockScaleExponent_mem (p : BlockScaleParameter) : blockScaleExponent p ∈ Ioo (0 : ℝ) 1 := by
  have hp := (ofLex p).1.property
  dsimp [blockScaleExponent]
  constructor <;> linarith [hp.1, hp.2]

theorem blockScaleFamily_pos (lower upper : ℕ → ℕ) (p : BlockScaleParameter) (s : ℕ) :
    0 < blockScaleFamily lower upper p s := positiveIntermediateScale_pos lower upper _ _ s

theorem blockScaleFamily_ambient_ratio (lower upper N : ℕ → ℕ)
    (hlower : Tendsto lower atTop atTop) (hupper : Tendsto upper atTop atTop)
    (hgap : Tendsto (fun s => (upper s : ℝ) / lower s) atTop atTop)
    (hupperN : ∀ᶠ s in atTop, upper s ≤ N s) (p : BlockScaleParameter) :
    Tendsto (fun s => (blockScaleFamily lower upper p s : ℝ) / N s) atTop (𝓝 0) :=
  positiveIntermediateScale_ambient_ratio lower upper N hlower hupper hgap hupperN _ _
    (blockScaleExponent_mem p).1 (blockScaleExponent_mem p).2

theorem blockScaleFamily_separated (lower upper : ℕ → ℕ)
    (hlower : Tendsto lower atTop atTop)
    (hgap : Tendsto (fun s => (upper s : ℝ) / lower s) atTop atTop)
    (p q : BlockScaleParameter) (hpq : p < q) :
    Tendsto (fun s => (blockScaleFamily lower upper p s : ℝ) /
      blockScaleFamily lower upper q s) atTop (𝓝 0) := by
  apply positiveIntermediateScale_lexicographic_ratio lower upper hlower hgap _ _ _ _
    (blockScaleExponent_mem p).1 (blockScaleExponent_mem q).1
  rcases Prod.Lex.lt_iff.mp hpq with hlt | ⟨heq, hlt⟩
  · left
    change (ofLex p).1.val < (ofLex q).1.val at hlt
    dsimp [blockScaleExponent]
    linarith
  · right
    exact ⟨by simp only [blockScaleExponent, heq], hlt⟩

end Erdos335.IntermediateScale
