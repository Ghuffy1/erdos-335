import Erdos335.Bohr
import Erdos335.DensitySubsetPeriods
import Mathlib.NumberTheory.FrobeniusNumber

/-!
# Minimum normalization and gcd periods for sparse terminal sums

Private proof development. Verification status is recorded separately.
All densities are ordinary densities. The sets may contain zero.
-/

set_option autoImplicit false

open Filter Set Topology
open scoped Pointwise

noncomputable section

namespace Erdos335.Proposed

@[simp] theorem sparse_shift_zero (V : Set ℕ) : shift V 0 = V := by
  ext n
  simp [shift]

theorem sparse_period_add (V : Set ℕ) (s t : ℕ)
    (hs : DensityEquivalent (shift V s) V)
    (ht : DensityEquivalent (shift V t) V) :
    DensityEquivalent (shift V (s + t)) V := by
  rw [← shift_shift_eq]
  exact (hs.shift t).trans ht

theorem sparse_period_mul (V : Set ℕ) (g : ℕ)
    (hg : DensityEquivalent (shift V g) V) (n : ℕ) :
    DensityEquivalent (shift V (g * n)) V := by
  induction n with
  | zero => simpa only [Nat.mul_zero, sparse_shift_zero] using DensityEquivalent.refl V
  | succ n ih =>
      rw [Nat.mul_succ]
      exact sparse_period_add V (g * n) g ih hg

theorem sparse_period_setGcd (D V : Set ℕ)
    (hD : ∀ d ∈ D, DensityEquivalent (shift V d) V) :
    DensityEquivalent (shift V (Nat.setGcd D)) V := by
  let P : AddSubmonoid ℕ := {
    carrier := {d | DensityEquivalent (shift V d) V}
    zero_mem' := by
      change DensityEquivalent (shift V 0) V
      simpa only [sparse_shift_zero] using DensityEquivalent.refl V
    add_mem' := fun hs ht => sparse_period_add V _ _ hs ht
  }
  have hclosure : AddSubmonoid.closure D ≤ P := AddSubmonoid.closure_le.mpr hD
  by_cases hz : Nat.setGcd D = 0
  · simpa only [hz, sparse_shift_zero] using DensityEquivalent.refl V
  have hg : 0 < Nat.setGcd D := Nat.pos_of_ne_zero hz
  obtain ⟨N, hN⟩ := Nat.exists_mem_closure_of_ge D
  let n := Nat.setGcd D * (N + 1)
  have hn : N ≤ n := by dsimp only [n]; nlinarith
  have hn' : N ≤ n + Nat.setGcd D := hn.trans (Nat.le_add_right _ _)
  have hp : DensityEquivalent (shift V n) V :=
    hclosure (hN n hn ⟨N + 1, rfl⟩)
  have hp' : DensityEquivalent (shift V (n + Nat.setGcd D)) V :=
    hclosure (hN (n + Nat.setGcd D) hn' ⟨N + 2, by dsimp only [n]; ring⟩)
  simpa only [Nat.add_sub_cancel_left] using
    period_of_equal_translates V n (n + Nat.setGcd D) (Nat.le_add_right _ _)
      (hp.trans hp'.symm)

theorem sparse_subset_sum (D V : Set ℕ) (hzero : 0 ∈ D) : V ⊆ D + V := by
  intro v hv
  exact ⟨0, hzero, v, hv, zero_add v⟩

theorem sparse_sum_density_iff_negligible (D V : Set ℕ) (x : ℝ)
    (hzero : 0 ∈ D) (hV : HasDensity V x) :
    HasDensity (D + V) x ↔ Negligible ((D + V) \ V) := by
  constructor
  · intro hsum
    exact (densityEquivalent_of_subset_same_density V (D + V) x
      (sparse_subset_sum D V hzero) hV hsum).2
  · intro hmissing
    have hcontained : Negligible (V \ (D + V)) := by
      rw [Set.sdiff_eq_empty.mpr (sparse_subset_sum D V hzero)]
      exact hasDensity_empty
    exact (show DensityEquivalent V (D + V) from ⟨hcontained, hmissing⟩).hasDensity hV

theorem sparse_sum_periods (D V : Set ℕ) (x : ℝ)
    (hzero : 0 ∈ D) (hV : HasDensity V x) (hsum : HasDensity (D + V) x) :
    ∀ d ∈ D, DensityEquivalent (shift V d) V := by
  have hbase := densityEquivalent_of_subset_same_density V (D + V) x
    (sparse_subset_sum D V hzero) hV hsum
  intro d hd
  have hshift := densityEquivalent_of_subset_same_density (shift V d) (D + V) x
    (shift_subset_sum hd) (hV.shift d) hsum
  exact hshift.trans hbase.symm

theorem sparse_sum_setGcd_period (D V : Set ℕ) (x : ℝ)
    (hzero : 0 ∈ D) (hV : HasDensity V x) (hsum : HasDensity (D + V) x) :
    DensityEquivalent (shift V (Nat.setGcd D)) V :=
  sparse_period_setGcd D V (sparse_sum_periods D V x hzero hV hsum)

theorem sparse_finite_sum_density_of_setGcd_period
    (D V : Set ℕ) (x : ℝ) (hD : D.Finite) (hzero : 0 ∈ D)
    (hV : HasDensity V x)
    (hperiod : DensityEquivalent (shift V (Nat.setGcd D)) V) :
    HasDensity (D + V) x := by
  classical
  have hshift (d : ℕ) (hd : d ∈ D) : DensityEquivalent (shift V d) V := by
    obtain ⟨n, hn⟩ := Nat.setGcd_dvd_of_mem hd
    rw [hn]
    exact sparse_period_mul V (Nat.setGcd D) hperiod n
  have hmissing : Negligible ((D + V) \ V) := by
    apply (negligible_finiteUnion hD.toFinset (fun d => shift V d \ V)
      (fun d hd => (hshift d (hD.mem_toFinset.mp hd)).1)).mono
    rintro n ⟨⟨d, hd, v, hv, rfl⟩, hnV⟩
    exact ⟨d, hD.mem_toFinset.mpr hd, ⟨⟨v, hv, Nat.add_comm v d⟩, hnV⟩⟩
  exact (sparse_sum_density_iff_negligible D V x hzero hV).mpr hmissing

theorem sparse_finite_sum_density_iff_setGcd_period
    (D V : Set ℕ) (x : ℝ) (hD : D.Finite) (hzero : 0 ∈ D)
    (hV : HasDensity V x) :
    HasDensity (D + V) x ↔ DensityEquivalent (shift V (Nat.setGcd D)) V :=
  ⟨sparse_sum_setGcd_period D V x hzero hV,
    sparse_finite_sum_density_of_setGcd_period D V x hD hzero hV⟩

theorem sparse_minimum_exists (U : Set ℕ) (hU : U.Nonempty) :
    ∃ u₀, IsLeast U u₀ := by
  classical
  exact ⟨Nat.find hU, Nat.find_spec hU, fun u hu => Nat.find_min' hU hu⟩

theorem sparse_normalized_zero (U : Set ℕ) (u₀ : ℕ) (hu₀ : IsLeast U u₀) :
    0 ∈ tailShift U u₀ := by
  simpa only [tailShift, Set.mem_setOf_eq, zero_add] using hu₀.1

theorem sparse_restore_minimum (U : Set ℕ) (u₀ : ℕ) (hu₀ : IsLeast U u₀) :
    shift (tailShift U u₀) u₀ = U := by
  rw [shift_tailShift]
  exact Set.inter_eq_left.mpr (fun u hu => hu₀.2 hu)

theorem sparse_normalized_sum (U V : Set ℕ) (u₀ : ℕ) (hu₀ : IsLeast U u₀) :
    shift (tailShift U u₀ + V) u₀ = U + V := by
  calc
    shift (tailShift U u₀ + V) u₀ = shift (tailShift U u₀) u₀ + shift V 0 := by
      simpa only [Nat.add_zero] using shift_add (tailShift U u₀) V u₀ 0
    _ = U + V := by rw [sparse_restore_minimum U u₀ hu₀, sparse_shift_zero]

theorem sparse_normalized_density_iff (U V : Set ℕ) (u₀ : ℕ) (x : ℝ)
    (hu₀ : IsLeast U u₀) :
    HasDensity (tailShift U u₀ + V) x ↔ HasDensity (U + V) x := by
  rw [← sparse_normalized_sum U V u₀ hu₀]
  exact (hasDensity_shift_iff _ u₀ x).symm

theorem sparse_normalized_finite (U : Set ℕ) (u₀ : ℕ)
    (hu₀ : IsLeast U u₀) (hU : U.Finite) : (tailShift U u₀).Finite := by
  apply (hU.image (fun u => u - u₀)).subset
  intro d hd
  refine ⟨d + u₀, hd, ?_⟩
  exact Nat.add_sub_cancel d u₀

theorem sparse_normalized_setGcd_pos (U : Set ℕ) (u₀ : ℕ)
    (hu₀ : IsLeast U u₀) (hnonsingle : U ≠ {u₀}) :
    0 < Nat.setGcd (tailShift U u₀) := by
  apply Nat.pos_of_ne_zero
  intro hz
  have hD := Nat.setGcd_eq_zero_iff.mp hz
  apply hnonsingle
  ext u
  constructor
  · intro hu
    have hle := hu₀.2 hu
    have hd : u - u₀ ∈ tailShift U u₀ := by
      simpa only [tailShift, Set.mem_setOf_eq, Nat.sub_add_cancel hle] using hu
    have heq : u - u₀ = 0 := Set.mem_singleton_iff.mp (hD hd)
    exact Set.mem_singleton_iff.mpr (by omega)
  · intro hu
    simpa only [Set.mem_singleton_iff.mp hu] using hu₀.1

end Erdos335.Proposed

end
