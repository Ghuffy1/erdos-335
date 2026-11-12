import Erdos335.PackedIntervals
import Erdos335.LongIntervalEstimate

/-!
# The periodic subset in a stabilized deficient family

Packing occupied residues preserves the joint density up to a fixed factor.
Long intervals force a cofinite packed sum. Unpacking supplies the periodic
subset through zero needed in Kneser's reduction.
-/

set_option autoImplicit false

open Filter Topology
open scoped Pointwise

namespace Erdos335

theorem exists_periodic_derived_sum (A B : Set ℕ) (q g : ℕ+)
    (hA0 : 0 ∈ A) (hB0 : 0 ∈ B) (hg : (g : ℕ) = Nat.setGcd B)
    (hgap : lowerDensity (A + B) < jointLowerDensity A B)
    (hstable : ∀ C D : Set ℕ, DysonDerived A B C D →
      HasGap D q ∧ Nat.setGcd D = Nat.setGcd B ∧
        residues (q : ℕ) D = residues (q : ℕ) B) :
    ∃ C D : Set ℕ, DysonDerived A B C D ∧
      ∃ K : ℕ, ∀ n : ℕ, K ≤ n →
        (n ∈ C + D ↔ (n : ZMod (g : ℕ)) ∈ residues (g : ℕ) A) := by
  classical
  let S := residues (g : ℕ) A
  have hS : S.Nonempty := ⟨0, mem_residues.mpr ⟨0, hA0, by simp⟩⟩
  obtain ⟨h, hh, label, hinj, hsurj⟩ := exists_residue_label g S hS
  let t : ℝ := (g : ℕ) / (h : ℕ)
  have ht : 0 < t := div_pos (by exact_mod_cast g.pos) (by exact_mod_cast h.pos)
  have hBdiv : ∀ b ∈ B, (g : ℕ) ∣ b := fun b hb => hg ▸ Nat.setGcd_dvd_of_mem hb
  have hcarrier : ∀ C D : Set ℕ, DysonDerived A B C D →
      ∀ c ∈ C, (c : ZMod (g : ℕ)) ∈ S := by
    intro C D hCD c hc
    change (c : ZMod (g : ℕ)) ∈ residues (g : ℕ) A
    rw [← hCD.residues_left_of_dvd g hBdiv]
    exact mem_residues.mpr ⟨c, hc, rfl⟩
  have hdiv : ∀ C D : Set ℕ, DysonDerived A B C D → ∀ d ∈ D, (g : ℕ) ∣ d := by
    intro C D hCD d hd
    exact hBdiv d (hCD.right_subset hd)
  have hjoint : ∀ C D : Set ℕ, DysonDerived A B C D →
      jointLowerDensity (packedSet g h label C) (packedSet g h (fun _ => 0) D) =
        t * jointLowerDensity A B := by
    intro C D hCD
    rw [jointLowerDensity_packed g h label S C D (hcarrier C D hCD) hinj (hdiv C D hCD),
      hCD.jointLowerDensity_eq]
  have houtput : ∀ C D : Set ℕ, DysonDerived A B C D →
      lowerDensity (packedSet g h label C + packedSet g h (fun _ => 0) D) ≤
        t * lowerDensity (A + B) := by
    intro C D hCD
    rw [lowerDensity_packed_sum g h label S C D (hcarrier C D hCD) hinj (hdiv C D hCD)]
    exact mul_le_mul_of_nonneg_left (lowerDensity_mono hCD.sum_subset) ht.le
  have hlarge : 1 < t * jointLowerDensity A B := by
    by_contra hbad
    have hs : t * jointLowerDensity A B ≤ 1 := le_of_not_gt hbad
    have hgap' := mul_lt_mul_of_pos_left hgap ht
    obtain ⟨δ, hδlo, hδhi⟩ := exists_between hgap'
    have hδpos : 0 < δ := (mul_nonneg ht.le (lowerDensity_nonneg (A + B))).trans_lt hδlo
    obtain ⟨γ, hδγ, hγhi⟩ := exists_between hδhi
    have hdiff : 0 < γ - δ := sub_pos.mpr hδγ
    obtain ⟨k, hk⟩ := exists_nat_gt (δ / (γ - δ) + 1)
    have hfrac0 : 0 ≤ δ / (γ - δ) := div_nonneg hδpos.le hdiff.le
    have hkR : (0 : ℝ) < k := by linarith
    have hkpos : 0 < k := by exact_mod_cast hkR
    have hfrac : δ / (γ - δ) < (k : ℝ) := by linarith
    have hmul := (div_lt_iff₀ hdiff).mp hfrac
    have hweight : ((k : ℝ) + 1) * δ ≤ k * γ := by nlinarith
    obtain ⟨C, D, u, hCD, hblock⟩ :=
      exists_dysonDerived_packed_intervals A B q g h hg hstable label hsurj k
    have hD0 := zero_mem_packed_multiples g h (hCD.zero_mem hA0 hB0).2
    have hγdensity : γ < jointLowerDensity (packedSet g h label C)
        (packedSet g h (fun _ => 0) D) := by rw [hjoint C D hCD]; exact hγhi
    have hl := lowerDensity_sum_ge_of_interval _ _ u hkpos hblock hD0
      (hδpos.trans hδγ) hγdensity hδγ.le (hδhi.trans_le hs).le hweight
    exact hδlo.not_ge (hl.trans (houtput C D hCD))
  obtain ⟨γ, hγ, hγs⟩ := exists_between hlarge
  have hdiff : 0 < γ - 1 := by linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / (γ - 1) + 1)
  have hfrac0 : 0 ≤ 1 / (γ - 1) := by positivity
  have hkR : (0 : ℝ) < k := by linarith
  have hkpos : 0 < k := by exact_mod_cast hkR
  have hfrac : 1 / (γ - 1) < (k : ℝ) := by linarith
  have hmul := (div_lt_iff₀ hdiff).mp hfrac
  have hweight : (k : ℝ) + 1 ≤ k * γ := by nlinarith
  obtain ⟨C, D, u, hCD, hblock⟩ :=
    exists_dysonDerived_packed_intervals A B q g h hg hstable label hsurj k
  have hD0 := zero_mem_packed_multiples g h (hCD.zero_mem hA0 hB0).2
  have hγdensity : γ < jointLowerDensity (packedSet g h label C)
      (packedSet g h (fun _ => 0) D) := by rw [hjoint C D hCD]; exact hγs
  have hfull := cofinite_sum_of_interval _ _ u hkpos hblock hD0 hγ hγdensity hweight
  exact ⟨C, D, hCD,
    cofinite_packed_sum_reflect g h label S C D (hcarrier C D hCD) hinj (hdiv C D hCD) hfull⟩

theorem stable_periodic_subset_through_zero (A B : Set ℕ) (q : ℕ+)
    (hA0 : 0 ∈ A) (hB0 : 0 ∈ B) (hg : 0 < Nat.setGcd B)
    (hgap : lowerDensity (A + B) < jointLowerDensity A B)
    (hstable : ∀ C D : Set ℕ, DysonDerived A B C D →
      HasGap D q ∧ Nat.setGcd D = Nat.setGcd B ∧
        residues (q : ℕ) D = residues (q : ℕ) B) :
    ∃ (P : Set ℕ) (g : ℕ+), P ⊆ A + B ∧ 0 ∈ P ∧
      (∀ᶠ n : ℕ in atTop, n ∈ P ↔ n ∈ periodicSet (residues (g : ℕ) P)) ∧
      jointLowerDensity A B - 1 / (g : ℕ) ≤ lowerDensity P := by
  classical
  let g : ℕ+ := ⟨Nat.setGcd B, hg⟩
  obtain ⟨C, D, hCD, K, hK⟩ := exists_periodic_derived_sum A B q g hA0 hB0 rfl hgap hstable
  have hD0 := (hCD.zero_mem hA0 hB0).2
  have hdiv : ∀ d ∈ D, (g : ℕ) ∣ d := fun d hd => Nat.setGcd_dvd_of_mem (hCD.right_subset hd)
  have hDres : residues (g : ℕ) D = {0} := by
    ext r
    constructor
    · intro hr
      obtain ⟨d, hd, rfl⟩ := mem_residues.mp hr
      obtain ⟨k, rfl⟩ := hdiv d hd
      simp
    · intro hr
      have hr0 : r = 0 := Finset.mem_singleton.mp hr
      subst r
      exact mem_residues.mpr ⟨0, hD0, by simp⟩
  have hres : residues (g : ℕ) (C + D) = residues (g : ℕ) A := by
    rw [residues_add, hDres]
    rw [hCD.residues_left_of_dvd g (fun b hb => Nat.setGcd_dvd_of_mem hb)]
    ext r
    constructor
    · intro hr
      obtain ⟨x, hx, y, hy, heq⟩ := Finset.mem_add.mp hr
      have hy0 : y = 0 := Finset.mem_singleton.mp hy
      have hxr : x = r := by simpa only [hy0, add_zero] using heq
      exact hxr ▸ hx
    · intro hr
      exact Finset.mem_add.mpr ⟨r, hr, 0, by simp, by simp⟩
  have hperiod : ∀ᶠ n : ℕ in atTop,
      n ∈ C + D ↔ n ∈ periodicSet (residues (g : ℕ) (C + D)) := by
    filter_upwards [eventually_ge_atTop K, eventually_ge_atTop 1] with n hn hn1
    rw [hK n hn, hres]
    simp only [periodicSet, Set.mem_ofPred_eq, and_iff_right (by omega : 0 < n)]
  have hsep : Separated D (g : ℕ) := by
    intro d hd e he hde
    exact Nat.le_of_dvd (Nat.sub_pos_of_lt hde) (Nat.dvd_sub (hdiv e he) (hdiv d hd))
  have hupper := upperDensity_le_inv_of_separated g.pos hsep
  have hjoint := jointLowerDensity_le_upperDensity_add_lowerDensity C D
  rw [hCD.jointLowerDensity_eq] at hjoint
  have hCsub : C ⊆ C + D := fun c hc => ⟨c, hc, 0, hD0, by simp⟩
  have hClower := lowerDensity_mono hCsub
  refine ⟨C + D, g, hCD.sum_subset, ?_, hperiod, ?_⟩
  · exact ⟨0, (hCD.zero_mem hA0 hB0).1, 0, hD0, by simp⟩
  · linarith

end Erdos335
