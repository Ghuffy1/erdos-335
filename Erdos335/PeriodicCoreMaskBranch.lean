import Erdos335.NullFrameCoverage
import Erdos335.LoebPeriodicPrefix
import Erdos335.PeriodicBackgroundParts

/-!
# The sparse-transition branch for ordinary periodic input cores
-/

set_option autoImplicit false

open Filter Set Topology
open scoped Pointwise

namespace Erdos335.Proposed

theorem periodic_inputs_maskBranch
    (A B : Set ℕ) (a b : ℝ) (hA : A ⊆ Set.Ioi 0) (hB : B ⊆ Set.Ioi 0)
    (hdA : HasDensity A a) (hdB : HasDensity B b) (hdC : HasDensity (A + B) (a + b))
    (q : ℕ+) (P Q : Finset (ZMod (q : ℕ))) (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hAP : DensityEquivalent A (periodicSet P)) (hBQ : DensityEquivalent B (periodicSet Q)) :
    MaskBranch A B (a + b) := by
  classical
  have hAD : a = (P.card : ℝ) / (q : ℕ) := hdA.unique (hAP.symm.hasDensity (hasDensity_periodicSet P))
  have hBD : b = (Q.card : ℝ) / (q : ℕ) := hdB.unique (hBQ.symm.hasDensity (hasDensity_periodicSet Q))
  have hcriterion := (periodic_inputs_criterion A B P Q hA hB hP hQ hAP hBQ).mp
    (by simpa only [← hAD, ← hBD] using hdC)
  obtain ⟨FA, hFA, hrepA⟩ := exists_finite_residue_representatives A q
  obtain ⟨FB, hFB, hrepB⟩ := exists_finite_residue_representatives B q
  let C := finiteTranslateCover A B FA FB
  have full_fiber (V : Set ℕ) (R : Finset (ZMod (q : ℕ)))
      (hVR : DensityEquivalent V (periodicSet R)) (r : ZMod (q : ℕ)) (hr : r ∈ R) :
      DensityEquivalent (residueFiber V r) (periodicSet ({r} : Finset (ZMod (q : ℕ)))) := by
    have hd := Loeb.periodic_template_residue_density V q R hVR r
    rw [if_pos hr] at hd
    apply densityEquivalent_of_subset_same_density _ _ ((1 : ℝ) / (q : ℕ))
      (fun n hn => hn.2) hd
    simpa only [Finset.card_singleton, Nat.cast_one] using hasDensity_periodicSet ({r} : Finset (ZMod (q : ℕ)))
  have hmissing : Negligible (periodicSet (baseline A B P Q) \ C) := by
    apply negligible_periodic_diff_of_singletons
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨r, hr, t, ht, rfl⟩ := Finset.mem_add.mp hw
      obtain ⟨u, huFA, hur⟩ := hrepA r hr
      have hs := missing_fiber_of_full_shift B C q t u (full_fiber B Q hBQ t ht)
        (fun n hn => Or.inr ⟨u, huFA, hn⟩)
      simpa only [hur, add_comm] using hs
    · obtain ⟨r, hr, t, ht, rfl⟩ := Finset.mem_add.mp hw
      obtain ⟨v, hvFB, hvt⟩ := hrepB t ht
      have hs := missing_fiber_of_full_shift A C q r v (full_fiber A P hAP r hr)
        (fun n hn => Or.inl ⟨v, hvFB, hn⟩)
      simpa only [hvt] using hs
  have hcover : Negligible ((A + B) \ C) := by
    apply (hcriterion.2.union hmissing).mono
    rintro n ⟨hn, hout⟩
    by_cases hnU : n ∈ periodicSet (baseline A B P Q)
    · exact Or.inr ⟨hnU, hout⟩
    · exact Or.inl ⟨hn, hnU⟩
  have hAq : DensityEquivalent (shift A (q : ℕ)) A :=
    (hAP.shift q).trans ((periodic_mask_shift_of_dvd q P q dvd_rfl).trans hAP.symm)
  have hBq : DensityEquivalent (shift B (q : ℕ)) B :=
    (hBQ.shift q).trans ((periodic_mask_shift_of_dvd q Q q dvd_rfl).trans hBQ.symm)
  exact (maskBranch_iff_common_period_finite_translate_cover A B (a + b)).mpr
    ⟨hdC, q, FA, FB, hAq, hBq, hFA, hFB, hcover⟩

theorem periodic_summand_saturated_maskBranch
    (A B : Set ℕ) (a b : ℝ) (hA : A ⊆ Set.Ioi 0) (hB : B ⊆ Set.Ioi 0)
    (ha : 0 < a) (hb : 0 < b) (hdA : HasDensity A a) (hdB : HasDensity B b)
    (hdC : HasDensity (A + B) (a + b)) (hgap : a + b < gamma A B)
    (m : ℕ+) (P : Finset (ZMod (m : ℕ))) (hAP : DensityEquivalent A (periodicSet P))
    (heq : ((residues (m : ℕ) B + P).card : ℝ) / (m : ℕ) = a + b) :
    MaskBranch A B (a + b) := by
  let U := residues (m : ℕ) B + P
  change (U.card : ℝ) / (m : ℕ) = a + b at heq
  have hholes : Negligible (periodicSet U \ (A + B)) := by
    apply negligible_periodic_diff_of_singletons
    intro w hw
    have hh := missing_left_baseline_singleton (A := B) (B := A) hAP hw
    simpa only [add_comm B A] using hh
  have hout : Negligible ((A + B) \ periodicSet U) := by
    change HasDensity ((A + B) \ periodicSet U) 0
    have hd := hdC.sdiff_of_negligible_reverse (hasDensity_periodicSet U) hholes
    simpa only [heq, sub_self] using hd
  obtain ⟨S, T, hS, hT, hAS, hBT, _, _⟩ := periodic_output_forces_periodic_inputs A B U a b
    hA hB ha hb hdA hdB hdC ⟨hout, hholes⟩ hgap
  exact periodic_inputs_maskBranch A B a b hA hB hdA hdB hdC m S T hS hT hAS hBT

end Erdos335.Proposed
