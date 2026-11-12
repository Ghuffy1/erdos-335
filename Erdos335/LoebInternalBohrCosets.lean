import Erdos335.BohrCosetPullback
import Erdos335.LoebCircleCharacterInternal
import Erdos335.LoebPositiveSubgroups
import Erdos335.LoebHaar

/-!
# Internal character and natural residue descriptions of circle cosets
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance internalBohrCosetLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U
local instance internalBohrCosetCircleSpace : MeasurableSpace (Additive Circle) := borel (Additive Circle)
local instance internalBohrCosetCircleBorel : BorelSpace (Additive Circle) := ⟨rfl⟩

theorem exists_internal_character_for_open_circle_cosets
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (F : ℕ → ∀ n, ZMod (q n : ℕ) →+ Additive Circle)
    [CompactSpace (countableUltralimitHom U F).range]
    {L : Type*} [AddCommGroup L] [TopologicalSpace L] [IsTopologicalAddGroup L]
    [CompactSpace L] [T2Space L] [MeasurableSpace L] [BorelSpace L]
    (ψ : (countableUltralimitHom U F).range →+ L)
    (hψ : Continuous ψ) (hψsurj : Function.Surjective ψ)
    (H : OpenAddSubgroup L) (e : H ≃+ AddCircle (1 : ℝ)) (he : Continuous e) :
    ∃ m : ℕ+, ∃ p : ∀ n, ZMod (q n : ℕ) →+ ZMod (m : ℕ),
      (∀ᶠ n in U, Function.Surjective (p n) ∧
        ∀ k : ℕ, p n (k : ZMod (q n : ℕ)) = (k : ZMod (m : ℕ))) ∧
      ∃ γ : L →+ AddCircle (1 : ℝ), Continuous γ ∧ Function.Surjective γ ∧
        γ.comp H.toAddSubgroup.subtype = e.toAddMonoidHom ∧
      ∃ ρ : ∀ n, ZMod (q n : ℕ) →+ AddCircle (1 : ℝ),
        γ.comp (ψ.comp (countableUltralimitHom U F).rangeRestrict) = ultralimitAddHom U ρ ∧
        (finiteQuotient U p).ker = H.toAddSubgroup.comap (ψ.comp (countableUltralimitHom U F).rangeRestrict) ∧
        ∀ a : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)), ∀ S : Set (AddCircle (1 : ℝ)),
          (ψ.comp (countableUltralimitHom U F).rangeRestrict) ⁻¹'
              ((ψ.comp (countableUltralimitHom U F).rangeRestrict) a +ᵥ
                ((Subtype.val : H → L) '' (e ⁻¹' S))) =
            (a +ᵥ ((finiteQuotient U p).ker : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))) ∩
              (ultralimitAddHom U ρ) ⁻¹'
                (γ ((ψ.comp (countableUltralimitHom U F).rangeRestrict) a) +ᵥ S) := by
  obtain ⟨γ, hγ, hγsurj, hγrestrict⟩ :=
    exists_surjective_continuous_circle_character_extension H e.toAddMonoidHom he e.surjective
  obtain ⟨ρ, hρ⟩ := unitCircle_character_on_countable_factor_internal U hU F
    (γ.comp ψ) (hγ.comp hψ)
  let θ := ψ.comp (countableUltralimitHom U F).rangeRestrict
  have hθ : Measurable θ := hψ.measurable.comp (measurable_countableUltralimitHom U F).subtype_mk
  have hθsurj : Function.Surjective θ := hψsurj.comp (countableUltralimitHom U F).rangeRestrict_surjective
  have hρ' : γ.comp θ = ultralimitAddHom U ρ := hρ
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let ν := Measure.map θ μ
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have : IsProbabilityMeasure ν := ⟨by
    rw [Measure.map_apply hθ MeasurableSet.univ]
    simp⟩
  have : ν.IsAddHaarMeasure := loebMeasure_map_hom_isAddHaarMeasure U hU θ hθ hθsurj
  let J := H.toAddSubgroup.comap θ
  have hJm : MeasurableSet (J : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) :=
    H.isOpen.measurableSet.preimage hθ
  have hJpos : 0 < μ (J : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) := by
    change 0 < μ (θ ⁻¹' (H : Set L))
    rw [← Measure.map_apply hθ H.isOpen.measurableSet]
    exact H.isOpen.measure_pos ν ⟨0, H.zero_mem⟩
  obtain ⟨m, p, hpnat, hker, _⟩ :=
    positive_measurable_subgroup_is_natural_finite_kernel U hU q J hJm hJpos
  refine ⟨m, p, hpnat, γ, hγ, hγsurj, hγrestrict, ρ, hρ', hker, ?_⟩
  intro a S
  have h := preimage_subgroup_character_coset θ H.toAddSubgroup e.toAddMonoidHom γ hγrestrict a S
  have hk : (finiteQuotient U p).ker = H.toAddSubgroup.comap θ := hker
  rw [← hk, hρ'] at h
  exact h

end Erdos335.Loeb

end
