import Erdos335.Density

/-!
# Literal residue supports

Finite or density-zero exceptional elements are retained in these definitions.
The residue-support identity and the escaping-sum identity are exact set identities.
-/

set_option autoImplicit false

open Filter Topology
open scoped Pointwise

namespace Erdos335

noncomputable def residues (q : ℕ) [NeZero q] (A : Set ℕ) : Finset (ZMod q) := by
  classical
  exact Finset.univ.filter (fun r => ∃ a ∈ A, (a : ZMod q) = r)

@[simp] theorem mem_residues {q : ℕ} [NeZero q] {A : Set ℕ} {r : ZMod q} :
    r ∈ residues q A ↔ ∃ a ∈ A, (a : ZMod q) = r := by
  classical
  simp [residues]

theorem residues_add (q : ℕ) [NeZero q] (A B : Set ℕ) :
    residues q (A + B) = residues q A + residues q B := by
  classical
  ext r
  constructor
  · rintro h
    obtain ⟨n, hn, rfl⟩ := mem_residues.mp h
    obtain ⟨a, ha, b, hb, rfl⟩ := hn
    exact Finset.mem_add.mpr ⟨(a : ZMod q), mem_residues.mpr ⟨a, ha, rfl⟩,
      (b : ZMod q), mem_residues.mpr ⟨b, hb, rfl⟩, by simp⟩
  · intro h
    obtain ⟨rA, hrA, rB, hrB, rfl⟩ := Finset.mem_add.mp h
    obtain ⟨a, ha, rfl⟩ := mem_residues.mp hrA
    obtain ⟨b, hb, rfl⟩ := mem_residues.mp hrB
    exact mem_residues.mpr ⟨a + b, ⟨a, ha, b, hb, rfl⟩, by simp⟩

theorem subset_periodic_residues (q : ℕ) [NeZero q] (A : Set ℕ)
    (hA : A ⊆ Set.Ioi 0) : A ⊆ periodicSet (residues q A) := by
  intro n hn
  exact ⟨hA hn, mem_residues.mpr ⟨n, hn, rfl⟩⟩

noncomputable def baseline {q : ℕ} [NeZero q] (A B : Set ℕ) (S T : Finset (ZMod q)) :
    Finset (ZMod q) := (residues q A + T) ∪ (S + residues q B)

/-- Every escaping sum uses exceptional elements on both input sides. -/
theorem escaping_sum_eq (q : ℕ) [NeZero q] (A B : Set ℕ)
    (hA : A ⊆ Set.Ioi 0) (hB : B ⊆ Set.Ioi 0) (S T : Finset (ZMod q)) :
    (A + B) \ periodicSet (baseline A B S T) =
      ((A \ periodicSet S) + (B \ periodicSet T)) \
        periodicSet (baseline A B S T) := by
  classical
  ext n
  constructor
  · rintro ⟨⟨a, ha, b, hb, rfl⟩, hn⟩
    have hna : a ∉ periodicSet S := by
      intro haS
      apply hn
      refine ⟨?_, ?_⟩
      · change 0 < a + b
        have ha0 : 0 < a := hA ha
        have hb0 : 0 < b := hB hb
        omega
      · apply Finset.mem_union_right
        have hbr : (b : ZMod q) ∈ residues q B := mem_residues.mpr ⟨b, hb, rfl⟩
        simpa only [Nat.cast_add] using Finset.add_mem_add haS.2 hbr
    have hnb : b ∉ periodicSet T := by
      intro hbT
      apply hn
      refine ⟨?_, ?_⟩
      · change 0 < a + b
        have ha0 : 0 < a := hA ha
        have hb0 : 0 < b := hB hb
        omega
      · apply Finset.mem_union_left
        have har : (a : ZMod q) ∈ residues q A := mem_residues.mpr ⟨a, ha, rfl⟩
        simpa only [Nat.cast_add] using Finset.add_mem_add har hbT.2
    exact ⟨⟨a, ⟨ha, hna⟩, b, ⟨hb, hnb⟩, rfl⟩, hn⟩
  · rintro ⟨⟨a, ha, b, hb, rfl⟩, hn⟩
    exact ⟨⟨a, ha.1, b, hb.1, rfl⟩, hn⟩

theorem count_mono {A B : Set ℕ} (hAB : A ⊆ B) (N : ℕ) : count A N ≤ count B N := by
  classical
  apply Finset.card_le_card
  intro n hn
  exact Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hn).1, hAB (Finset.mem_filter.mp hn).2⟩

theorem count_le (A : Set ℕ) (N : ℕ) : count A N ≤ N := by
  classical
  calc
    count A N ≤ (Finset.Icc 1 N).card := Finset.card_filter_le _ _
    _ = N := by simp

theorem HasDensity.unique {A : Set ℕ} {a b : ℝ}
    (ha : HasDensity A a) (hb : HasDensity A b) : a = b :=
  tendsto_nhds_unique ha hb

theorem HasDensity.nonneg {A : Set ℕ} {a : ℝ} (ha : HasDensity A a) : 0 ≤ a := by
  exact ge_of_tendsto' ha (fun N => by positivity)

theorem HasDensity.le_one {A : Set ℕ} {a : ℝ} (ha : HasDensity A a) : a ≤ 1 := by
  apply le_of_tendsto ha
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  exact (div_le_one hNr).mpr (by exact_mod_cast count_le A N)

theorem HasDensity.mono {A B : Set ℕ} {a b : ℝ}
    (ha : HasDensity A a) (hb : HasDensity B b) (hAB : A ⊆ B) : a ≤ b := by
  exact le_of_tendsto_of_tendsto' ha hb (fun N =>
    div_le_div_of_nonneg_right (by exact_mod_cast count_mono hAB N) (Nat.cast_nonneg N))

/-- Any actual density is bounded by every literal residue cover. -/
theorem HasDensity.le_residue_cover {A : Set ℕ} {a : ℝ} (ha : HasDensity A a)
    (hA : A ⊆ Set.Ioi 0) (q : ℕ) [NeZero q] :
    a ≤ (residues q A).card / (q : ℝ) :=
  ha.mono (hasDensity_periodicSet (residues q A)) (subset_periodic_residues q A hA)

noncomputable def modularCapacity (A B : Set ℕ) (q : ℕ+) : ℝ :=
  ((residues (q : ℕ) A + residues (q : ℕ) B).card : ℝ) / (q : ℕ)

noncomputable def gamma (A B : Set ℕ) : ℝ := ⨅ q : ℕ+, modularCapacity A B q

theorem modularCapacity_nonneg (A B : Set ℕ) (q : ℕ+) :
    0 ≤ modularCapacity A B q := by
  unfold modularCapacity
  positivity

theorem density_sum_le_gamma {A B : Set ℕ} {s : ℝ}
    (hA : A ⊆ Set.Ioi 0) (hB : B ⊆ Set.Ioi 0) (hC : HasDensity (A + B) s) :
    s ≤ gamma A B := by
  apply le_ciInf
  intro q
  have hpositive : A + B ⊆ Set.Ioi 0 := by
    rintro n ⟨a, ha, b, hb, rfl⟩
    have ha0 : 0 < a := hA ha
    have hb0 : 0 < b := hB hb
    change 0 < a + b
    omega
  simpa only [modularCapacity, residues_add] using
    hC.le_residue_cover hpositive (q : ℕ)

/-- The entire gamma-below-density exclusion branch is unconditional. -/
theorem no_density_equality_of_gamma_lt {A B : Set ℕ} {a b : ℝ}
    (hA : A ⊆ Set.Ioi 0) (hB : B ⊆ Set.Ioi 0)
    (hgap : gamma A B < a + b) : ¬HasDensity (A + B) (a + b) := by
  intro hC
  exact (not_lt_of_ge (density_sum_le_gamma hA hB hC)) hgap

theorem no_density_equality_of_one_lt {A B : Set ℕ} {a b : ℝ}
    (hgap : 1 < a + b) : ¬HasDensity (A + B) (a + b) := by
  intro hC
  exact (not_lt_of_ge hC.le_one) hgap

end Erdos335
