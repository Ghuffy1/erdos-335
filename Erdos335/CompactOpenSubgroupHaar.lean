import Erdos335.CompactHaarProbability
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Normalized Haar measure on an open subgroup
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Topology

noncomputable section

namespace Erdos335.Loeb

theorem exists_normalized_open_subgroup_measure
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [MeasurableAdd₂ G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure]
    (H : OpenAddSubgroup G) :
    ∃ ν : Measure H, IsProbabilityMeasure ν ∧ ν.IsAddHaarMeasure ∧
      ∀ S : Set H, μ ((Subtype.val : H → G) '' S) = μ (H : Set G) * ν S := by
  have hEmb : IsOpenEmbedding (H.toAddSubgroup.subtype : H → G) :=
    H.isOpen.isOpenEmbedding_subtypeVal
  have : MeasurableAdd₂ H := ⟨by
    exact ((measurable_subtype_coe.comp measurable_fst).add
      (measurable_subtype_coe.comp measurable_snd)).subtype_mk⟩
  let η : Measure H := μ.comap H.toAddSubgroup.subtype
  have : η.IsAddHaarMeasure := Measure.IsAddHaarMeasure.comap μ (mH := inferInstance) hEmb
  have hηuniv : η univ = μ (H : Set G) := by
    change μ.comap H.toAddSubgroup.subtype univ = μ (H : Set G)
    rw [hEmb.measurableEmbedding.comap_apply μ]
    congr 1
    ext x
    simp
  have hHpos : 0 < μ (H : Set G) := H.isOpen.measure_pos μ ⟨0, H.zero_mem⟩
  have hηne : η ≠ 0 := by
    intro hz
    have : μ (H : Set G) = 0 := by rw [← hηuniv, hz]; simp
    exact hHpos.ne' this
  have : NeZero η := ⟨hηne⟩
  let ν : Measure H := (η univ)⁻¹ • η
  have : IsProbabilityMeasure ν := inferInstance
  have hνhaar : ν.IsAddHaarMeasure := Measure.IsAddHaarMeasure.smul
    (μ := η) (ENNReal.inv_ne_zero.mpr (measure_ne_top η _))
      (ENNReal.inv_ne_top.mpr (hηuniv ▸ hHpos.ne'))
  refine ⟨ν, inferInstance, hνhaar, ?_⟩
  intro S
  have hS : η S = μ ((Subtype.val : H → G) '' S) :=
    hEmb.measurableEmbedding.comap_apply μ S
  rw [← hS]
  change η S = μ (H : Set G) * ((η univ)⁻¹ * η S)
  rw [hηuniv, ← mul_assoc, ENNReal.mul_inv_cancel hHpos.ne' (measure_ne_top μ _), one_mul]

end Erdos335.Loeb

end
