import Erdos335.PrincipalFrequencies
import Erdos335.FiniteExceptionalDensity

/-!
# Exceptional windows for bounded integer combinations of frequencies
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators Classical

namespace Erdos335.IntermediateScale

abbrev BoundedFrequencyWeights (d C : ℕ) := Fin d → ↥(Finset.Icc (-(C : ℤ)) (C : ℤ))

noncomputable def frequencyCombination {d : ℕ} (α : ℕ → Fin d → ℝ) (w : Fin d → ℤ) (n : ℕ) : ℝ :=
  ∑ i, (w i : ℝ) * α n i

noncomputable def badFrequencyCombinationWindows {d : ℕ}
    (N W C : ℕ) (α : ℕ → Fin d → ℝ) : Finset ℕ :=
  (range N).filter fun n => ∃ w : BoundedFrequencyWeights d C,
    1 / ((C : ℝ) * W) < circleFrequencyDistance (frequencyCombination α (fun i => (w i).val) n) ∧
      circleFrequencyDistance (frequencyCombination α (fun i => (w i).val) n) < (C : ℝ) / W

theorem badFrequencyCombinationWindows_density_tendsto_zero
    {d : ℕ} (N W : ℕ → ℕ) (C : ℕ) (α : ℕ → Fin d → ℝ)
    (h : ∀ w : BoundedFrequencyWeights d C,
      Tendsto (fun s => frequencyBandDensity (N s) (W s) C
        (fun n => circleFrequencyDistance (frequencyCombination α (fun i => (w i).val) n)))
        atTop (𝓝 0)) :
    Tendsto (fun s => ((badFrequencyCombinationWindows (N s) (W s) C α).card : ℝ) / N s)
      atTop (𝓝 0) := by
  let E := fun (w : BoundedFrequencyWeights d C) (s : ℕ) => (range (N s)).filter fun n =>
    1 / ((C : ℝ) * W s) < circleFrequencyDistance (frequencyCombination α (fun i => (w i).val) n) ∧
      circleFrequencyDistance (frequencyCombination α (fun i => (w i).val) n) < (C : ℝ) / W s
  have heq (s : ℕ) : badFrequencyCombinationWindows (N s) (W s) C α = univ.biUnion (fun w => E w s) := by
    ext n
    constructor
    · intro hn
      obtain ⟨hnN, w, hw⟩ := mem_filter.mp hn
      exact mem_biUnion.mpr ⟨w, mem_univ w, mem_filter.mpr ⟨hnN, hw⟩⟩
    · intro hn
      obtain ⟨w, _hw, hn⟩ := mem_biUnion.mp hn
      obtain ⟨hnN, hw⟩ := mem_filter.mp hn
      exact mem_filter.mpr ⟨hnN, w, hw⟩
  have hE (w : BoundedFrequencyWeights d C) : Tendsto (fun s => ((E w s).card : ℝ) / N s) atTop (𝓝 0) := by
    have hd (n : ℕ) : |circleFrequencyDistance (frequencyCombination α (fun i => (w i).val) n)| =
        circleFrequencyDistance (frequencyCombination α (fun i => (w i).val) n) :=
      abs_of_nonneg (circleFrequencyDistance_mem _).1
    simpa only [frequencyBandDensity, E, hd] using h w
  simpa only [heq] using finite_union_density_tendsto_zero N E hE

theorem boundedFrequencyWeights_represent {d C : ℕ} (w : Fin d → ℤ)
    (hw : ∀ i, |w i| ≤ (C : ℤ)) :
    ∃ v : BoundedFrequencyWeights d C, ∀ i, (v i).val = w i := by
  exact ⟨fun i => ⟨w i, Finset.mem_Icc.mpr (abs_le.mp (hw i))⟩, fun _ => rfl⟩

end Erdos335.IntermediateScale
