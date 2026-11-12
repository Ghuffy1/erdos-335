import Erdos335.NaturalQuotientRefinement
import Erdos335.CyclicQuotients

/-!
# Residue-cover capacities under divisibility refinement
-/

set_option autoImplicit false

open Set

namespace Erdos335

theorem residue_capacity_mono_of_dvd (A : Set ℕ) (h q : ℕ+)
    (hd : (h : ℕ) ∣ (q : ℕ)) :
    ((residues (q : ℕ) A).card : ℝ) / (q : ℕ) ≤
      ((residues (h : ℕ) A).card : ℝ) / (h : ℕ) := by
  let π := Loeb.naturalCyclicProjection q h
  have himage := residues_image_of_natCast q h π
    (fun n => Loeb.naturalCyclicProjection_natCast q h hd n) A
  have hsub : periodicSet (residues (q : ℕ) A) ⊆ periodicSet (residues (h : ℕ) A) := by
    rintro n ⟨hn, hr⟩
    refine ⟨hn, ?_⟩
    rw [← himage]
    exact Finset.mem_image.mpr ⟨(n : ZMod (q : ℕ)), hr,
      Loeb.naturalCyclicProjection_natCast q h hd n⟩
  exact (hasDensity_periodicSet (residues (q : ℕ) A)).mono
    (hasDensity_periodicSet (residues (h : ℕ) A)) hsub

theorem residue_capacity_approximants_at_multiples (A : Set ℕ) (a : ℝ)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ q : ℕ+, ((residues (q : ℕ) A).card : ℝ) / (q : ℕ) ≤ a + ε)
    (m : ℕ+) (ε : ℝ) (hε : 0 < ε) :
    ∃ q : ℕ+, (m : ℕ) ∣ (q : ℕ) ∧ ((residues (q : ℕ) A).card : ℝ) / (q : ℕ) ≤ a + ε := by
  obtain ⟨q, hq⟩ := happrox ε hε
  refine ⟨m * q, ⟨q, rfl⟩, ?_⟩
  exact (residue_capacity_mono_of_dvd A q (m * q) ⟨m, Nat.mul_comm _ _⟩).trans hq

theorem residue_capacity_ge_of_full_coarse_fiber (A : Set ℕ) (m h : ℕ+)
    (hmh : (m : ℕ) ∣ (h : ℕ)) (r : ZMod (m : ℕ))
    (hfull : (Loeb.naturalCyclicProjection h m) ⁻¹' {r} ⊆ (residues (h : ℕ) A : Set _)) :
    (1 : ℝ) / (m : ℕ) ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ) := by
  have hsub : periodicSet ({r} : Finset (ZMod (m : ℕ))) ⊆ periodicSet (residues (h : ℕ) A) := by
    rintro n ⟨hn, hr⟩
    refine ⟨hn, hfull ?_⟩
    change Loeb.naturalCyclicProjection h m (n : ZMod (h : ℕ)) = r
    rw [Loeb.naturalCyclicProjection_natCast h m hmh]
    simpa only [Finset.mem_singleton] using hr
  have hd := (hasDensity_periodicSet ({r} : Finset (ZMod (m : ℕ)))).mono
    (hasDensity_periodicSet (residues (h : ℕ) A)) hsub
  simpa only [Finset.card_singleton, Nat.cast_one] using hd

end Erdos335
