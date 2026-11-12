import Erdos335.DysonStabilization

/-!
# Finite translates in a stabilized Dyson family

The right-input residue classes remain available after each transform. This
lets a word in those classes act on any fixed finite part of the left input.
-/

set_option autoImplicit false

open Filter Topology
open scoped Pointwise

namespace Erdos335

theorem exists_dysonDerived_translate_of_residue_word
    (C D : Set ℕ) (q : ℕ+)
    (hstable : ∀ E F : Set ℕ, DysonDerived C D E F →
      residues (q : ℕ) F = residues (q : ℕ) D)
    (L : List (ZMod (q : ℕ))) (hL : ∀ r ∈ L, r ∈ residues (q : ℕ) D)
    (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ C) :
    ∃ (E F : Set ℕ) (z : ℕ), DysonDerived C D E F ∧
      (z : ZMod (q : ℕ)) = L.sum ∧ ∀ a ∈ S, a + z ∈ E := by
  classical
  induction L generalizing C D S with
  | nil =>
      exact ⟨C, D, 0, DysonDerived.refl, by simp, fun a ha => by simpa using hS ha⟩
  | cons r L ih =>
      obtain ⟨X, Y, hXY, hcover⟩ := exists_dysonDerived_cover_finite C D S hS
      have hr : r ∈ residues (q : ℕ) Y := by
        rw [hstable X Y hXY]
        exact hL r (by simp)
      obtain ⟨b, hb, hbr⟩ := mem_residues.mp hr
      let T := S.image (fun a => a + b)
      have hT : (T : Set ℕ) ⊆ X := by
        intro x hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
        have h := hcover a ha ⟨b, hb, rfl⟩
        simpa only [Nat.add_comm b a] using h
      have hstable' : ∀ E F : Set ℕ, DysonDerived X Y E F →
          residues (q : ℕ) F = residues (q : ℕ) Y := by
        intro E F hEF
        exact (hstable E F (hXY.trans hEF)).trans (hstable X Y hXY).symm
      have hL' : ∀ t ∈ L, t ∈ residues (q : ℕ) Y := by
        intro t ht
        rw [hstable X Y hXY]
        exact hL t (by simp [ht])
      obtain ⟨E, F, z, hEF, hz, htranslate⟩ := ih X Y hstable' hL' T hT
      refine ⟨E, F, b + z, hXY.trans hEF, ?_, ?_⟩
      · simp only [Nat.cast_add, List.sum_cons, hbr, hz]
      · intro a ha
        have h := htranslate (a + b) (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
        simpa only [Nat.add_assoc] using h

theorem residue_word_of_mem_closure (D : Set ℕ) (q : ℕ+) {n : ℕ}
    (hn : n ∈ AddSubmonoid.closure D) :
    ∃ L : List (ZMod (q : ℕ)),
      (∀ r ∈ L, r ∈ residues (q : ℕ) D) ∧ L.sum = (n : ZMod (q : ℕ)) := by
  classical
  induction hn using AddSubmonoid.closure_induction with
  | mem x hx =>
      exact ⟨[(x : ZMod (q : ℕ))], by
        simpa using (mem_residues.mpr ⟨x, hx, rfl⟩ :
          (x : ZMod (q : ℕ)) ∈ residues (q : ℕ) D), by simp⟩
  | zero => exact ⟨[], by simp, by simp⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨L, hL, hLs⟩ := ihx
      obtain ⟨M, hM, hMs⟩ := ihy
      refine ⟨L ++ M, ?_, ?_⟩
      · intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact hL r hr
        · exact hM r hr
      · simp only [List.sum_append, hLs, hMs, Nat.cast_add]

theorem exists_residue_word_setGcd (D : Set ℕ) (q : ℕ+)
    (hg : 0 < Nat.setGcd D) :
    ∃ L : List (ZMod (q : ℕ)),
      (∀ r ∈ L, r ∈ residues (q : ℕ) D) ∧ L.sum = (Nat.setGcd D : ZMod (q : ℕ)) := by
  obtain ⟨K, hK⟩ := Nat.exists_mem_closure_of_ge D
  let n := Nat.setGcd D * ((q : ℕ) * (K + 1) + 1)
  have hq := q.pos
  have hnK : K ≤ n := by
    dsimp [n]
    have hqK := Nat.mul_le_mul_right (K + 1) (show 1 ≤ (q : ℕ) by omega)
    have hgK := Nat.mul_le_mul_right ((q : ℕ) * (K + 1) + 1)
      (show 1 ≤ Nat.setGcd D by omega)
    simp only [one_mul] at hqK hgK
    omega
  have hn : n ∈ AddSubmonoid.closure D := hK n hnK (by dsimp [n]; exact dvd_mul_right _ _)
  obtain ⟨L, hL, hsum⟩ := residue_word_of_mem_closure D q hn
  refine ⟨L, hL, ?_⟩
  simpa [n] using hsum

/-- Kneser's finite two-translate step, with the stable residue and gap data
obtained in `DysonStabilization`. -/
theorem exists_dysonDerived_two_translates (C D : Set ℕ) (q : ℕ+)
    (hg : 0 < Nat.setGcd D)
    (hstable : ∀ E F : Set ℕ, DysonDerived C D E F →
      HasGap F q ∧ residues (q : ℕ) F = residues (q : ℕ) D)
    (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ C) :
    ∃ (E F : Set ℕ) (z : ℕ), DysonDerived C D E F ∧
      ∀ a ∈ S, a + z ∈ E ∧ a + z + Nat.setGcd D ∈ E := by
  classical
  let g := Nat.setGcd D
  let P : ℕ → Prop := fun d => 0 < d ∧ (d : ZMod (q : ℕ)) = (g : ZMod (q : ℕ)) ∧
    ∃ (E F : Set ℕ) (z : ℕ), DysonDerived C D E F ∧
      ∀ a ∈ S, a + z ∈ E ∧ a + z + d ∈ E
  have hqg : g ≤ (q : ℕ) := by
    obtain ⟨x, hx, y, hy, hxy, hdiff⟩ := (hstable C D DysonDerived.refl).1
    have hdiv : g ∣ y - x := Nat.dvd_sub (Nat.setGcd_dvd_of_mem hy) (Nat.setGcd_dvd_of_mem hx)
    rw [hdiff] at hdiv
    exact Nat.le_of_dvd q.pos hdiv
  have hex : ∃ d : ℕ, P d := by
    obtain ⟨L, hL, hsum⟩ := exists_residue_word_setGcd D q hg
    obtain ⟨E, F, z, hEF, hz, htranslate⟩ :=
      exists_dysonDerived_translate_of_residue_word C D q
        (fun E F h => (hstable E F h).2) L hL S hS
    let T := S ∪ S.image (fun a => a + z)
    have hT : (T : Set ℕ) ⊆ E := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hEF.left_subset (hS hx)
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
        exact htranslate a ha
    obtain ⟨U, V, hUV, hcover⟩ := exists_dysonDerived_cover_finite E F T hT
    have hCV := hEF.trans hUV
    obtain ⟨x, hx, y, hy, hxy, hdiff⟩ := (hstable U V hCV).1
    have hyeq : y = x + (q : ℕ) := by omega
    refine ⟨z + (q : ℕ), by omega, ?_, U, V, x, hCV, ?_⟩
    · simpa only [Nat.cast_add, ZMod.natCast_self, add_zero, g] using hz.trans hsum
    · intro a ha
      constructor
      · have h := hcover a (Finset.mem_union_left _ ha) ⟨x, hx, rfl⟩
        convert h using 1
        dsimp only
        omega
      · have h := hcover (a + z)
          (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)) ⟨y, hy, rfl⟩
        convert h using 1
        dsimp only
        omega
  let d := Nat.find hex
  obtain ⟨hdpos, hdmod, E, F, z, hEF, hpair⟩ := Nat.find_spec hex
  have hdq : d ≤ (q : ℕ) := by
    by_contra hlarge
    have hqd : (q : ℕ) < d := by omega
    let T := (S.image (fun a => a + z)) ∪ S.image (fun a => a + z + d)
    have hT : (T : Set ℕ) ⊆ E := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
        exact (hpair a ha).1
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
        exact (hpair a ha).2
    obtain ⟨U, V, hUV, hcover⟩ := exists_dysonDerived_cover_finite E F T hT
    have hCV := hEF.trans hUV
    obtain ⟨x, hx, y, hy, hxy, hdiff⟩ := (hstable U V hCV).1
    have hyeq : y = x + (q : ℕ) := by omega
    have hsmall : P (d - (q : ℕ)) := by
      refine ⟨by omega, ?_, U, V, z + x + (q : ℕ), hCV, ?_⟩
      · rw [Nat.cast_sub hqd.le, ZMod.natCast_self, sub_zero]
        exact hdmod
      · intro a ha
        constructor
        · have h := hcover (a + z)
            (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)) ⟨y, hy, rfl⟩
          convert h using 1
          dsimp only
          omega
        · have h := hcover (a + z + d)
            (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)) ⟨x, hx, rfl⟩
          convert h using 1
          dsimp only
          omega
    exact Nat.find_min hex (by dsimp [d]; omega) hsmall
  have heq : d = g := by
    have hmod := (ZMod.natCast_eq_natCast_iff d g (q : ℕ)).mp hdmod
    change d % (q : ℕ) = g % (q : ℕ) at hmod
    by_cases hd : d = (q : ℕ)
    · by_cases hgq : g = (q : ℕ)
      · omega
      · rw [hd, Nat.mod_self, Nat.mod_eq_of_lt (by omega : g < (q : ℕ))] at hmod
        omega
    · by_cases hgq : g = (q : ℕ)
      · rw [hgq, Nat.mod_self, Nat.mod_eq_of_lt (by omega : d < (q : ℕ))] at hmod
        omega
      · rwa [Nat.mod_eq_of_lt (by omega : d < (q : ℕ)),
          Nat.mod_eq_of_lt (by omega : g < (q : ℕ))] at hmod
  refine ⟨E, F, z, hEF, ?_⟩
  have hdg : Nat.find hex = Nat.setGcd D := heq
  intro a ha
  simpa only [hdg] using hpair a ha

theorem exists_dysonDerived_progressions (C D : Set ℕ) (q : ℕ+)
    (hg : 0 < Nat.setGcd D)
    (hstable : ∀ E F : Set ℕ, DysonDerived C D E F →
      HasGap F q ∧ Nat.setGcd F = Nat.setGcd D ∧
        residues (q : ℕ) F = residues (q : ℕ) D)
    (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ C) (k : ℕ) :
    ∃ (E F : Set ℕ) (z : ℕ), DysonDerived C D E F ∧
      ∀ a ∈ S, ∀ i ≤ k, a + z + i * Nat.setGcd D ∈ E := by
  classical
  induction k with
  | zero =>
      refine ⟨C, D, 0, DysonDerived.refl, ?_⟩
      intro a ha i hi
      have hi0 : i = 0 := by omega
      simpa only [hi0, zero_mul, add_zero] using hS ha
  | succ k ih =>
      obtain ⟨E, F, z, hEF, hprogression⟩ := ih
      let T := S.biUnion fun a => (Finset.range (k + 1)).image
        (fun i => a + z + i * Nat.setGcd D)
      have hT : (T : Set ℕ) ⊆ E := by
        intro x hx
        obtain ⟨a, ha, hx⟩ := Finset.mem_biUnion.mp hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        exact hprogression a ha i (by have := Finset.mem_range.mp hi; omega)
      have hgF : 0 < Nat.setGcd F := by rw [(hstable E F hEF).2.1]; exact hg
      have hstableF : ∀ G H : Set ℕ, DysonDerived E F G H →
          HasGap H q ∧ residues (q : ℕ) H = residues (q : ℕ) F := by
        intro G H hGH
        have hH := hstable G H (hEF.trans hGH)
        exact ⟨hH.1, hH.2.2.trans (hstable E F hEF).2.2.symm⟩
      obtain ⟨G, H, w, hGH, htwo⟩ := exists_dysonDerived_two_translates E F q hgF hstableF T hT
      refine ⟨G, H, z + w, hEF.trans hGH, ?_⟩
      intro a ha i hi
      have hmem : ∀ j ≤ k, a + z + j * Nat.setGcd D ∈ T := by
        intro j hj
        exact Finset.mem_biUnion.mpr ⟨a, ha,
          Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩⟩
      by_cases hik : i ≤ k
      · have h := (htwo _ (hmem i hik)).1
        convert h using 1
        omega
      · have hik' : i = k + 1 := by omega
        have h := (htwo _ (hmem k le_rfl)).2
        rw [(hstable E F hEF).2.1] at h
        rw [hik']
        convert h using 1
        ring

theorem exists_dysonDerived_long_progressions (A B : Set ℕ)
    (hA : 0 ∈ A) (hB : 0 ∈ B)
    (hgap : lowerDensity (A + B) < jointLowerDensity A B) :
    ∃ C D : Set ℕ, DysonDerived A B C D ∧ 0 < Nat.setGcd D ∧
      ∀ k : ℕ, ∃ (E F : Set ℕ) (z : ℕ), DysonDerived C D E F ∧
        ∀ i ≤ k, z + i * Nat.setGcd D ∈ E := by
  obtain ⟨C, D, q, hCD, hsep, hstable⟩ :=
    exists_dysonDerived_stable_residues A B hA hB hgap
  obtain ⟨x, hx, y, hy, hxy, hdiff⟩ := (hstable C D DysonDerived.refl).1
  have hpair : ∃ x ∈ D, ∃ y ∈ D, x < y ∧ y - x ≤ (q : ℕ) :=
    ⟨x, hx, y, hy, hxy, hdiff.le⟩
  have hg := (setGcd_bounds_of_close_pair D q hpair).1
  refine ⟨C, D, hCD, hg, ?_⟩
  intro k
  have hzero := (hCD.zero_mem hA hB).1
  have hS : (({0} : Finset ℕ) : Set ℕ) ⊆ C := by simpa using hzero
  obtain ⟨E, F, z, hEF, hprog⟩ := exists_dysonDerived_progressions C D q hg hstable {0} hS k
  refine ⟨E, F, z, hEF, ?_⟩
  intro i hi
  simpa only [zero_add] using hprog 0 (by simp) i hi

end Erdos335
