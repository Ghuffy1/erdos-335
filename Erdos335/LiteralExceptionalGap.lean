import Erdos335.FiniteExceptionalCapacity
import Erdos335.ResidueCapacityRefinement
import Erdos335.PeriodicOutput

/-!
# A literal capacity comparison for one exceptional output residue
-/

set_option autoImplicit false

open Set
open scoped Pointwise Classical

namespace Erdos335

theorem input_gap_le_output_gap_of_full_background
    (A B : Set ℕ) (a b δ : ℝ) (h : ℕ+) (i j : ZMod (h : ℕ))
    (hi : i ∈ residues (h : ℕ) A) (hj : j ∈ residues (h : ℕ) B)
    (hcard : (residues (h : ℕ) A + residues (h : ℕ) B).card + 1 =
      (residues (h : ℕ) A).card + (residues (h : ℕ) B).card)
    (ha : a = (((residues (h : ℕ) A).card : ℝ) - 1) / (h : ℕ))
    (hfull : ∀ n : ℕ+, (h : ℕ) ∣ (n : ℕ) → ∀ r : ZMod (n : ℕ),
      Loeb.naturalCyclicProjection n h r ∈
        (residues (h : ℕ) A + residues (h : ℕ) B).erase (i + j) → r ∈ residues (n : ℕ) (A + B))
    (hcapacity : ∀ n : ℕ+, b + δ ≤ ((residues (n : ℕ) B).card : ℝ) / (n : ℕ)) :
    a + b + δ ≤ gamma A B := by
  obtain ⟨a₀, ha₀, hai⟩ := mem_residues.mp hi
  let R := residues (h : ℕ) A + residues (h : ℕ) B
  let T := residues (h : ℕ) B
  have hu : i + j ∈ R := Finset.add_mem_add hi hj
  have hRerase : (((R.erase (i + j)).card : ℝ)) + 1 = R.card := by
    exact_mod_cast Finset.card_erase_add_one hu
  have hTerase : (((T.erase j).card : ℝ)) + 1 = T.card := by
    exact_mod_cast Finset.card_erase_add_one hj
  have hcardReal : (R.card : ℝ) + 1 = (residues (h : ℕ) A).card + T.card := by
    exact_mod_cast hcard
  have hmass : (((R.erase (i + j)).card : ℝ)) / (h : ℕ) =
      a + (((T.erase j).card : ℝ)) / (h : ℕ) := by
    rw [ha, ← add_div]
    congr 1
    linarith
  have at_multiple (n : ℕ+) (hn : (h : ℕ) ∣ (n : ℕ)) :
      a + b + δ ≤ ((residues (n : ℕ) (A + B)).card : ℝ) / (n : ℕ) := by
    let φ := Loeb.naturalCyclicProjection n h
    have hφa : φ (a₀ : ZMod (n : ℕ)) = i :=
      (Loeb.naturalCyclicProjection_natCast n h hn a₀).trans hai
    have hbound := exceptional_fiber_card_bound φ (residues (n : ℕ) B)
      (residues (n : ℕ) (A + B)) R T (a₀ : ZMod (n : ℕ)) j
      (fun r hr => by
        obtain ⟨v, hv, rfl⟩ := mem_residues.mp hr
        rw [Loeb.naturalCyclicProjection_natCast n h hn]
        exact mem_residues.mpr ⟨v, hv, rfl⟩)
      (fun r hr => hfull n hn r (by simpa only [hφa] using hr))
      (fun r hr => by
        rw [residues_add]
        exact Finset.add_mem_add (mem_residues.mpr ⟨a₀, ha₀, rfl⟩) hr)
    rw [hφa] at hbound
    have hboundReal : ((residues (n : ℕ) B).card : ℝ) +
        (Finset.univ.filter (fun r : ZMod (n : ℕ) => φ r ∈ R.erase (i + j))).card ≤
        (residues (n : ℕ) (A + B)).card +
        (Finset.univ.filter (fun r : ZMod (n : ℕ) => φ r ∈ T.erase j)).card := by
      exact_mod_cast hbound
    have hdivided := div_le_div_of_nonneg_right hboundReal (by positivity : (0 : ℝ) ≤ (n : ℕ))
    rw [add_div, add_div, natural_preimage_capacity n h hn,
      natural_preimage_capacity n h hn, hmass] at hdivided
    linarith [hcapacity n]
  apply le_ciInf
  intro k
  have hlower := (at_multiple (h * k) ⟨k, rfl⟩).trans
    (residue_capacity_mono_of_dvd (A + B) k (h * k) ⟨h, Nat.mul_comm _ _⟩)
  simpa only [modularCapacity, residues_add] using hlower

end Erdos335
