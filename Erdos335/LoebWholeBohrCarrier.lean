import Erdos335.LoebProfileCapacity
import Erdos335.LoebBohrPairProfiles

/-!
# Literal support of a whole Bohr prefix model
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance wholeBohrCarrierLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem whole_bohr_prefix_carrier
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (W : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (B : Set ℕ) (E : ℕ → Set ℕ) (hB : B.Nonempty)
    (hEsub : ∀ᶠ n in U, E n ⊆ B) (hexhaust : ∀ v ∈ B, ∀ᶠ n in U, v ∈ E n)
    (d : InternalBohrPairData U hU q W
      (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n))) :
    residues (d.modulus : ℕ) B = {finiteQuotient U d.residue d.right_anchor} := by
  classical
  let P := internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
  let φ := finiteQuotient U d.residue
  have himage : φ '' P = (residues (d.modulus : ℕ) B : Set _) :=
    finiteQuotient_image_of_literal_exhaustion U q B E hEsub hexhaust d.modulus d.residue
      (d.natural_residue.mono fun n hn => hn.2)
  have hsub : ∀ r ∈ residues (d.modulus : ℕ) B, r = φ d.right_anchor := by
    intro r hr
    have hr' : r ∈ φ '' P := by rw [himage]; exact hr
    obtain ⟨x, hx, hxr⟩ := hr'
    obtain ⟨k, hk, hkx⟩ := (d.right_containment hx).1
    change φ k = 0 at hk
    change d.right_anchor + k = x at hkx
    change φ x = r at hxr
    rw [← hkx, map_add, hk, add_zero] at hxr
    exact hxr.symm
  obtain ⟨v, hv⟩ := hB
  have hvR : (v : ZMod (d.modulus : ℕ)) ∈ residues (d.modulus : ℕ) B :=
    mem_residues.mpr ⟨v, hv, rfl⟩
  apply Finset.Subset.antisymm
  · intro r hr
    exact Finset.mem_singleton.mpr (hsub r hr)
  · intro r hr
    have hr' : r = φ d.right_anchor := Finset.mem_singleton.mp hr
    rw [hr', ← hsub (v : ZMod (d.modulus : ℕ)) hvR]
    exact hvR

end Erdos335.Loeb

end
