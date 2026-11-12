import Erdos335.PeriodicRefinementPrefixProfilesCompact
import Erdos335.PeriodicRefinementAssembly
import Erdos335.PeriodicRefinementMacroAssemblyLabels

/-!
# Recovering a periodic summand from its ordinary prefix-mask limit
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology
open Erdos335.PeriodicRefinementMacroAssembly
open scoped Pointwise BigOperators

noncomputable section

namespace Erdos335.PeriodicRefinement

theorem negligible_of_zero_residue_prefix_limits
    (A : Set ℕ) (M : ℕ+)
    (hlim : ∀ r, Tendsto (fun n => normalizedResiduePrefix A M n r) atTop (𝓝 0)) :
    Negligible A := by
  have hMr : ((M : ℕ) : ℝ) ≠ 0 := by exact_mod_cast M.ne_zero
  have hfiber (r : ZMod (M : ℕ)) : Negligible (literalResidue A M r) := by
    apply (hasDensity_iff_prefixCount _ _).mpr
    have hh := (hlim r).div_const ((M : ℕ) : ℝ)
    simp only [zero_div] at hh
    apply hh.congr
    intro n
    dsimp only [normalizedResiduePrefix]
    field_simp [hMr]
  have hunion : A = finiteUnion Finset.univ (literalResidue A M) := by
    ext n
    constructor
    · intro hn
      exact ⟨(n : ZMod (M : ℕ)), Finset.mem_univ _, hn, rfl⟩
    · rintro ⟨r, _, hn, _⟩
      exact hn
  rw [hunion]
  exact negligible_finiteUnion Finset.univ (literalResidue A M) (fun r _ => hfiber r)

theorem periodic_of_residue_prefix_mask
    (A : Set ℕ) (M : ℕ+) (a : ℝ) (hApos : A ⊆ Ioi 0) (hA : HasDensity A a)
    (P : Finset (ZMod (M : ℕ)))
    (hlim : Tendsto (normalizedResiduePrefix A M) atTop (𝓝 (maskVector P))) :
    DensityEquivalent A (periodicSet P) := by
  classical
  have hcoordinate (r : ZMod (M : ℕ)) :
      Tendsto (fun n => normalizedResiduePrefix A M n r) atTop (𝓝 (maskVector P r)) :=
    (continuous_apply r).tendsto (maskVector P) |>.comp hlim
  have hmass := normalized_residue_prefix_limit_mass A M a hA id tendsto_id
    (maskVector P) hcoordinate
  have hsum : (∑ r, maskVector P r) = (P.card : ℝ) := by
    simp [maskVector]
  rw [hsum] at hmass
  have ha : a = (P.card : ℝ) / (M : ℕ) := by
    apply (eq_div_iff (by exact_mod_cast M.ne_zero)).mpr
    simpa only [mul_comm] using hmass.symm
  have hout : Negligible (A \ periodicSet P) := by
    apply negligible_of_zero_residue_prefix_limits _ M
    intro r
    by_cases hr : r ∈ P
    · have he : literalResidue (A \ periodicSet P) M r = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro n ⟨⟨hnA, hnP⟩, hnr⟩
        exact hnP ⟨hApos hnA, by simpa only [hnr] using hr⟩
      simpa [normalizedResiduePrefix, he, prefixCount] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · have he : literalResidue (A \ periodicSet P) M r = literalResidue A M r := by
        ext n
        constructor
        · rintro ⟨⟨hnA, _⟩, hnr⟩
          exact ⟨hnA, hnr⟩
        · rintro ⟨hnA, hnr⟩
          refine ⟨⟨hnA, ?_⟩, hnr⟩
          intro hnP
          exact hr (by simpa only [hnr] using hnP.2)
      simpa only [normalizedResiduePrefix, he, maskVector, if_neg hr] using hcoordinate r
  refine ⟨hout, ?_⟩
  change HasDensity (periodicSet P \ A) 0
  have hmissing := (hasDensity_periodicSet P).sdiff_of_negligible_reverse hA hout
  simpa only [ha, sub_self] using hmissing

end Erdos335.PeriodicRefinement

end
