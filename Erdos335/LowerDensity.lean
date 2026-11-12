import Erdos335.PeriodicOutput
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Lower and upper ordinary densities

These definitions use the same positive-integer counting function as
`HasDensity`. In particular, the value at zero has no effect on the limits.
-/

set_option autoImplicit false

open Filter Topology
open scoped Pointwise

namespace Erdos335

noncomputable def lowerDensity (A : Set ℕ) : ℝ :=
  liminf (fun N : ℕ => (count A N : ℝ) / N) atTop

noncomputable def upperDensity (A : Set ℕ) : ℝ :=
  limsup (fun N : ℕ => (count A N : ℝ) / N) atTop

theorem count_ratio_nonneg (A : Set ℕ) (N : ℕ) : 0 ≤ (count A N : ℝ) / N := by
  positivity

theorem count_ratio_le_one (A : Set ℕ) (N : ℕ) : (count A N : ℝ) / N ≤ 1 := by
  rcases N with _ | N
  · simp
  · apply (div_le_one (by positivity)).mpr
    exact_mod_cast count_le A (N + 1)

theorem count_ratio_bounded_below (A : Set ℕ) :
    IsBoundedUnder (· ≥ ·) atTop (fun N : ℕ => (count A N : ℝ) / N) := by
  refine ⟨0, ?_⟩
  change ∀ᶠ N : ℕ in atTop, 0 ≤ (count A N : ℝ) / N
  exact Eventually.of_forall (count_ratio_nonneg A)

theorem count_ratio_bounded_above (A : Set ℕ) :
    IsBoundedUnder (· ≤ ·) atTop (fun N : ℕ => (count A N : ℝ) / N) := by
  refine ⟨1, ?_⟩
  change ∀ᶠ N : ℕ in atTop, (count A N : ℝ) / N ≤ 1
  exact Eventually.of_forall (count_ratio_le_one A)

theorem lowerDensity_nonneg (A : Set ℕ) : 0 ≤ lowerDensity A := by
  exact le_liminf_of_le (count_ratio_bounded_above A).isCobounded_flip
    (Eventually.of_forall (count_ratio_nonneg A))

theorem upperDensity_le_one (A : Set ℕ) : upperDensity A ≤ 1 := by
  exact limsup_le_of_le (count_ratio_bounded_below A).isCobounded_flip
    (Eventually.of_forall (count_ratio_le_one A))

theorem lowerDensity_le_upperDensity (A : Set ℕ) : lowerDensity A ≤ upperDensity A :=
  liminf_le_limsup (count_ratio_bounded_above A) (count_ratio_bounded_below A)

theorem lowerDensity_mono {A B : Set ℕ} (hAB : A ⊆ B) : lowerDensity A ≤ lowerDensity B := by
  exact liminf_le_liminf (Eventually.of_forall fun N =>
    div_le_div_of_nonneg_right (by exact_mod_cast count_mono hAB N) (Nat.cast_nonneg N))
    (count_ratio_bounded_below A) (count_ratio_bounded_above B).isCobounded_flip

theorem upperDensity_mono {A B : Set ℕ} (hAB : A ⊆ B) : upperDensity A ≤ upperDensity B := by
  exact limsup_le_limsup (Eventually.of_forall fun N =>
    div_le_div_of_nonneg_right (by exact_mod_cast count_mono hAB N) (Nat.cast_nonneg N))
    (count_ratio_bounded_below A).isCobounded_flip (count_ratio_bounded_above B)

theorem HasDensity.lowerDensity_eq {A : Set ℕ} {d : ℝ} (hA : HasDensity A d) :
    lowerDensity A = d := hA.liminf_eq

theorem HasDensity.upperDensity_eq {A : Set ℕ} {d : ℝ} (hA : HasDensity A d) :
    upperDensity A = d := hA.limsup_eq

theorem hasDensity_of_lowerDensity_ge_upperDensity_le {A : Set ℕ} {d : ℝ}
    (hl : d ≤ lowerDensity A) (hu : upperDensity A ≤ d) : HasDensity A d := by
  apply tendsto_order.mpr
  constructor
  · intro x hx
    exact eventually_lt_of_lt_liminf (hx.trans_le hl) (count_ratio_bounded_below A)
  · intro x hx
    exact eventually_lt_of_limsup_lt (hu.trans_lt hx) (count_ratio_bounded_above A)

theorem hasDensity_iff_lowerDensity_eq_upperDensity_eq (A : Set ℕ) (d : ℝ) :
    HasDensity A d ↔ lowerDensity A = d ∧ upperDensity A = d := by
  constructor
  · intro h
    exact ⟨h.lowerDensity_eq, h.upperDensity_eq⟩
  · rintro ⟨hl, hu⟩
    exact hasDensity_of_lowerDensity_ge_upperDensity_le hl.ge hu.le

theorem upperDensity_sum_le_gamma {A B : Set ℕ}
    (hA : A ⊆ Set.Ioi 0) (hB : B ⊆ Set.Ioi 0) : upperDensity (A + B) ≤ gamma A B := by
  have hCpos : A + B ⊆ Set.Ioi 0 := by
    rintro n ⟨a, ha, b, hb, rfl⟩
    have ha0 : 0 < a := hA ha
    have hb0 : 0 < b := hB hb
    change 0 < a + b
    omega
  apply le_ciInf
  intro q
  have h := upperDensity_mono (subset_periodic_residues (q : ℕ) (A + B) hCpos)
  rw [(hasDensity_periodicSet (residues (q : ℕ) (A + B))).upperDensity_eq] at h
  simpa only [residues_add, modularCapacity] using h

theorem density_sum_of_lowerDensity_ge_gamma {A B : Set ℕ}
    (hA : A ⊆ Set.Ioi 0) (hB : B ⊆ Set.Ioi 0)
    (h : gamma A B ≤ lowerDensity (A + B)) : HasDensity (A + B) (gamma A B) :=
  hasDensity_of_lowerDensity_ge_upperDensity_le h (upperDensity_sum_le_gamma hA hB)

end Erdos335
