import Erdos335.NullFramePeriods

/-!
# Finite literal translates cover a null-active frame in density
-/

set_option autoImplicit false

open Filter Set Topology
open scoped Pointwise

namespace Erdos335.Proposed

theorem missing_fiber_of_full_shift
    (A C : Set ℕ) (q : ℕ+) (r : ZMod (q : ℕ)) (b : ℕ)
    (hfull : DensityEquivalent (residueFiber A r) (periodicSet ({r} : Finset (ZMod (q : ℕ)))))
    (hsub : shift A b ⊆ C) :
    Negligible (periodicSet ({r + (b : ZMod (q : ℕ))} : Finset (ZMod (q : ℕ))) \ C) := by
  have heq := (hfull.shift b).trans (shift_periodic_equiv ({r} : Finset (ZMod (q : ℕ))) b)
  have hsmall : Negligible (periodicSet ({r + (b : ZMod (q : ℕ))} : Finset (ZMod (q : ℕ))) \
      shift (residueFiber A r) b) := by
    simpa only [Finset.singleton_add_singleton, add_comm] using heq.2
  apply hsmall.mono
  rintro n ⟨hn, hout⟩
  refine ⟨hn, ?_⟩
  rintro ⟨a, ha, rfl⟩
  exact hout (hsub ⟨a, ha.1, rfl⟩)

theorem FiniteFrame.null_left_finite_translate_coverage
    {A B : Set ℕ} (f : FiniteFrame A B)
    (hA : A ⊆ Set.Ioi 0) (hB : B ⊆ Set.Ioi 0) (a b x : ℝ)
    (hdA : HasDensity A a) (hdB : HasDensity B b) (hdC : HasDensity (A + B) (a + b))
    (hzero : HasDensity (residueSection A f.modulus f.activeA) 0)
    (hactive : HasDensity (residueSection B f.modulus f.activeB) x) :
    ∃ FA FB : Finset ℕ, (FA : Set ℕ) ⊆ A ∧ (FB : Set ℕ) ⊆ B ∧
      Negligible ((A + B) \ finiteTranslateCover A B FA FB) := by
  classical
  let q := f.modulus
  obtain ⟨FA, hFA, hrepA⟩ := exists_finite_residue_representatives A q
  obtain ⟨FB, hFB, hrepB⟩ := exists_finite_residue_representatives B q
  let C := finiteTranslateCover A B FA FB
  have leftShift (v : ℕ) (hv : v ∈ FB) : shift A v ⊆ C := by
    intro n hn
    exact Or.inl ⟨v, hv, hn⟩
  have rightShift (u : ℕ) (hu : u ∈ FA) : shift B u ⊆ C := by
    intro n hn
    exact Or.inr ⟨u, hu, hn⟩
  have hsmall (w : ZMod (q : ℕ)) (hw : w ∈ residues (q : ℕ) (A + B)) :
      Negligible (residueFiber (A + B) w \ C) := by
    by_cases hactivew : w = f.activeA + f.activeB
    · obtain ⟨u, huFA, hur⟩ := hrepA f.activeA f.activeA_mem
      have hu : u ∈ residueFiber A f.activeA :=
        ⟨hFA huFA, hA (hFA huFA), by simpa only [Finset.mem_singleton] using hur⟩
      have heq := f.null_left_translate_coverage hA hB a b x hdA hdB hdC hzero hactive u hu
      apply heq.2.mono
      rintro n ⟨hn, hout⟩
      refine ⟨by simpa only [hactivew] using hn, ?_⟩
      rintro ⟨v, hv, rfl⟩
      exact hout (rightShift u huFA ⟨v, hv.1, rfl⟩)
    · rw [residues_add] at hw
      obtain ⟨r, hr, t, ht, rfl⟩ := Finset.mem_add.mp hw
      by_cases hri : r = f.activeA
      · have htj : t ≠ f.activeB := by
          intro heq
          exact hactivew (by rw [hri, heq])
        obtain ⟨u, huFA, hur⟩ := hrepA r hr
        have hs := missing_fiber_of_full_shift B C q t u
          (full_residueFiber hB (f.backgroundB t ht htj)) (rightShift u huFA)
        apply hs.mono
        rintro n ⟨hn, hout⟩
        refine ⟨?_, hout⟩
        simpa only [hur, add_comm] using hn.2
      · obtain ⟨v, hvFB, hvt⟩ := hrepB t ht
        have hs := missing_fiber_of_full_shift A C q r v
          (full_residueFiber hA (f.backgroundA r hr hri)) (leftShift v hvFB)
        apply hs.mono
        rintro n ⟨hn, hout⟩
        refine ⟨?_, hout⟩
        simpa only [hvt] using hn.2
  refine ⟨FA, FB, hFA, hFB, ?_⟩
  apply (negligible_finiteUnion (residues (q : ℕ) (A + B))
    (fun w => residueFiber (A + B) w \ C) hsmall).mono
  rintro n ⟨hn, hout⟩
  exact ⟨(n : ZMod (q : ℕ)), mem_residues.mpr ⟨n, hn, rfl⟩,
    ⟨⟨hn, sumset_positive hA hB hn, by simp⟩, hout⟩⟩

end Erdos335.Proposed
