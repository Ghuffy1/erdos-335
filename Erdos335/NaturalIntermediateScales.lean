import Erdos335.IntermediateScaleFamily

/-!
# Integer-valued lexicographic scale families
-/

set_option autoImplicit false

open Filter Topology

namespace Erdos335.IntermediateScale

noncomputable def naturalIntermediateScale (lower upper : ℕ → ℕ) (a b : ℝ) (n : ℕ) : ℕ :=
  ⌊intermediateScale (fun n => (lower n : ℝ)) (fun n => (upper n : ℝ)) a b n⌋₊

theorem naturalIntermediateScale_atTop (lower upper : ℕ → ℕ)
    (hlower : Tendsto lower atTop atTop)
    (hgap : Tendsto (fun n => (upper n : ℝ) / lower n) atTop atTop)
    (a b : ℝ) (ha : 0 < a) :
    Tendsto (naturalIntermediateScale lower upper a b) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp (intermediateScale_atTop _ _
    ((hlower.eventually (eventually_ge_atTop 1)).mono (fun _ hn => by exact_mod_cast hn))
    hgap a b ha)

theorem naturalIntermediateScale_lower_ratio (lower upper : ℕ → ℕ)
    (hlower : Tendsto lower atTop atTop)
    (hgap : Tendsto (fun n => (upper n : ℝ) / lower n) atTop atTop)
    (a b : ℝ) (ha : 0 < a) :
    Tendsto (fun n => (lower n : ℝ) / naturalIntermediateScale lower upper a b n)
      atTop (𝓝 0) := by
  have hlo : ∀ᶠ n in atTop, 1 ≤ (lower n : ℝ) :=
    (hlower.eventually (eventually_ge_atTop 1)).mono fun _ hn => by exact_mod_cast hn
  have hp : ∀ᶠ n in atTop, 0 < (lower n : ℝ) := hlo.mono fun _ hn => lt_of_lt_of_le zero_lt_one hn
  have hS := intermediateScale_atTop (fun n => (lower n : ℝ)) (fun n => (upper n : ℝ)) hlo hgap a b ha
  have hr := tendsto_inv_atTop_zero.comp
    (intermediateScale_div_lower_atTop (fun n => (lower n : ℝ)) (fun n => (upper n : ℝ)) hp hgap a b ha)
  have hratio : Tendsto (fun n => (lower n : ℝ) /
      intermediateScale (fun n => (lower n : ℝ)) (fun n => (upper n : ℝ)) a b n)
      atTop (𝓝 0) := by simpa only [Function.comp_def, inv_div] using hr
  have hround := floor_preserves_vanishing_ratio (fun n => (lower n : ℝ))
    (intermediateScale (fun n => (lower n : ℝ)) (fun n => (upper n : ℝ)) a b)
    (tendsto_natCast_atTop_atTop.comp hlower) hS hratio
  simpa only [naturalIntermediateScale, Nat.floor_natCast] using hround

theorem naturalIntermediateScale_upper_ratio (lower upper : ℕ → ℕ)
    (hlower : Tendsto lower atTop atTop) (hupper : Tendsto upper atTop atTop)
    (hgap : Tendsto (fun n => (upper n : ℝ) / lower n) atTop atTop)
    (a b : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    Tendsto (fun n => (naturalIntermediateScale lower upper a b n : ℝ) / upper n)
      atTop (𝓝 0) := by
  have hlo : ∀ᶠ n in atTop, 1 ≤ (lower n : ℝ) :=
    (hlower.eventually (eventually_ge_atTop 1)).mono fun _ hn => by exact_mod_cast hn
  have hp : ∀ᶠ n in atTop, 0 < (lower n : ℝ) := hlo.mono fun _ hn => lt_of_lt_of_le zero_lt_one hn
  have hS := intermediateScale_atTop (fun n => (lower n : ℝ)) (fun n => (upper n : ℝ)) hlo hgap a b ha
  have hr := intermediateScale_div_upper_zero (fun n => (lower n : ℝ))
    (fun n => (upper n : ℝ)) hp hgap a b ha1
  have hround := floor_preserves_vanishing_ratio
    (intermediateScale (fun n => (lower n : ℝ)) (fun n => (upper n : ℝ)) a b)
    (fun n => (upper n : ℝ)) hS (tendsto_natCast_atTop_atTop.comp hupper) hr
  simpa only [naturalIntermediateScale, Nat.floor_natCast] using hround

theorem naturalIntermediateScale_lexicographic_ratio (lower upper : ℕ → ℕ)
    (hlower : Tendsto lower atTop atTop)
    (hgap : Tendsto (fun n => (upper n : ℝ) / lower n) atTop atTop)
    (a b a' b' : ℝ) (ha : 0 < a) (ha' : 0 < a')
    (horder : a < a' ∨ (a = a' ∧ b < b')) :
    Tendsto (fun n => (naturalIntermediateScale lower upper a b n : ℝ) /
      naturalIntermediateScale lower upper a' b' n) atTop (𝓝 0) := by
  have hlo : ∀ᶠ n in atTop, 1 ≤ (lower n : ℝ) :=
    (hlower.eventually (eventually_ge_atTop 1)).mono fun _ hn => by exact_mod_cast hn
  have hp : ∀ᶠ n in atTop, 0 < (lower n : ℝ) := hlo.mono fun _ hn => lt_of_lt_of_le zero_lt_one hn
  exact floor_preserves_vanishing_ratio _ _
    (intermediateScale_atTop _ _ hlo hgap a b ha)
    (intermediateScale_atTop _ _ hlo hgap a' b' ha')
    (intermediateScale_ratio_zero _ _ hp hgap a b a' b' horder)

end Erdos335.IntermediateScale
