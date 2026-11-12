import Erdos335.ResidueCapacityRefinement

/-!
# Lower residue-capacity bounds from a full coarse mask
-/

set_option autoImplicit false

open Set

namespace Erdos335

theorem residue_capacity_ge_of_full_coarse_mask (A : Set ℕ) (m h : ℕ+)
    (hmh : (m : ℕ) ∣ (h : ℕ)) (R : Finset (ZMod (m : ℕ)))
    (hfull : (Loeb.naturalCyclicProjection h m) ⁻¹' (R : Set _) ⊆ (residues (h : ℕ) A : Set _)) :
    (R.card : ℝ) / (m : ℕ) ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ) := by
  have hsub : periodicSet R ⊆ periodicSet (residues (h : ℕ) A) := by
    rintro n ⟨hn, hr⟩
    refine ⟨hn, hfull ?_⟩
    change Loeb.naturalCyclicProjection h m (n : ZMod (h : ℕ)) ∈ R
    rwa [Loeb.naturalCyclicProjection_natCast h m hmh]
  exact (hasDensity_periodicSet R).mono (hasDensity_periodicSet (residues (h : ℕ) A)) hsub

end Erdos335
