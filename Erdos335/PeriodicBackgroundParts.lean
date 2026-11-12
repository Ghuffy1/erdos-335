import Erdos335.DensitySubsetPeriods

/-!
# Extending an exceptional-fiber period across full periodic backgrounds
-/

set_option autoImplicit false

open Filter Set Topology
open scoped Pointwise

namespace Erdos335

theorem equivalent_periodic_background_and_fiber
    (A : Set ℕ) (q : ℕ+) (i : ZMod (q : ℕ)) (hA : A ⊆ Set.Ioi 0)
    (hbackground : ∀ r ∈ residues (q : ℕ) A, r ≠ i →
      Negligible (periodicSet ({r} : Finset (ZMod (q : ℕ))) \ A)) :
    DensityEquivalent A (periodicSet ((residues (q : ℕ) A).erase i) ∪ residueFiber A i) := by
  classical
  let R := (residues (q : ℕ) A).erase i
  have hholes : Negligible (periodicSet R \ A) := by
    apply negligible_periodic_diff_of_singletons
    intro r hr
    exact hbackground r (Finset.mem_erase.mp hr).2 (Finset.mem_erase.mp hr).1
  have hsub : A ⊆ periodicSet R ∪ residueFiber A i := by
    intro n hn
    by_cases hni : (n : ZMod (q : ℕ)) = i
    · exact Or.inr ⟨hn, hA hn, by simpa only [Finset.mem_singleton] using hni⟩
    · exact Or.inl ⟨hA hn, Finset.mem_erase.mpr ⟨hni, mem_residues.mpr ⟨n, hn, rfl⟩⟩⟩
  constructor
  · apply (show Negligible (∅ : Set ℕ) from hasDensity_empty).mono
    rintro n ⟨hn, hout⟩
    exact False.elim (hout (hsub hn))
  · apply hholes.mono
    rintro n ⟨hn | hn, hout⟩
    · exact ⟨hn, hout⟩
    · exact False.elim (hout hn.1)

theorem periodic_mask_shift_of_dvd
    (q : ℕ+) (R : Finset (ZMod (q : ℕ))) (t : ℕ) (hqt : (q : ℕ) ∣ t) :
    DensityEquivalent (shift (periodicSet R) t) (periodicSet R) := by
  have hcast : (t : ZMod (q : ℕ)) = 0 := (ZMod.natCast_eq_zero_iff t (q : ℕ)).mpr hqt
  have hzero : ({0} : Finset (ZMod (q : ℕ))) + R = R := by
    ext r
    constructor
    · intro hr
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp hr
      have ha0 : a = 0 := Finset.mem_singleton.mp ha
      have hbr : b = r := by simpa only [ha0, zero_add] using hab
      exact hbr ▸ hb
    · intro hr
      simpa only [zero_add] using Finset.add_mem_add (Finset.mem_singleton_self 0) hr
  simpa only [hcast, hzero] using shift_periodic_equiv R t

theorem period_from_exceptional_fiber
    (A : Set ℕ) (q : ℕ+) (i : ZMod (q : ℕ)) (hA : A ⊆ Set.Ioi 0)
    (hbackground : ∀ r ∈ residues (q : ℕ) A, r ≠ i →
      Negligible (periodicSet ({r} : Finset (ZMod (q : ℕ))) \ A))
    (t : ℕ) (hqt : (q : ℕ) ∣ t)
    (hactive : DensityEquivalent (shift (residueFiber A i) t) (residueFiber A i)) :
    DensityEquivalent (shift A t) A := by
  let R := (residues (q : ℕ) A).erase i
  have heq := equivalent_periodic_background_and_fiber A q i hA hbackground
  have hsplit : shift (periodicSet R ∪ residueFiber A i) t =
      shift (periodicSet R) t ∪ shift (residueFiber A i) t := by
    exact Set.image_union _ _ _
  have hperiod := (periodic_mask_shift_of_dvd q R t hqt).union hactive
  have hperiod' : DensityEquivalent (shift (periodicSet R ∪ residueFiber A i) t)
      (periodicSet R ∪ residueFiber A i) := by
    rw [hsplit]
    exact hperiod
  exact (heq.shift t).trans (hperiod'.trans heq.symm)

end Erdos335
