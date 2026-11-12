import Erdos335.LoebContinuousCharacterInternal
import Erdos335.CompactCircleEquiv

/-!
# Internal representatives for unit-circle characters
-/

set_option autoImplicit false

open Set Filter

noncomputable section

namespace Erdos335.Loeb

theorem unitCircle_character_on_countable_factor_internal
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (F : ℕ → ∀ n, X n →+ Additive Circle)
    [CompactSpace (countableUltralimitHom U F).range]
    (χ : (countableUltralimitHom U F).range →+ AddCircle (1 : ℝ)) (hχ : Continuous χ) :
    ∃ ψ : ∀ n, X n →+ AddCircle (1 : ℝ),
      χ.comp (countableUltralimitHom U F).rangeRestrict = ultralimitAddHom U ψ := by
  obtain ⟨e, he, hesymm⟩ := exists_unitCircle_addEquiv
  obtain ⟨ψ, hψ⟩ := continuous_character_on_countable_factor_internal U hU F
    (e.toAddMonoidHom.comp χ) (he.comp hχ)
  let g := fun n => e.symm.toAddMonoidHom.comp (ψ n)
  refine ⟨g, ?_⟩
  apply DFunLike.ext
  intro x
  have hv : e (χ ((countableUltralimitHom U F).rangeRestrict x)) =
      ultralimitAddHom U ψ x := DFunLike.congr_fun hψ x
  have hu : ultralimitAddHom U g x = e.symm (ultralimitAddHom U ψ x) :=
    congrFun (ultralimitFunction_comp_continuous U (fun n => ψ n) e.symm hesymm) x
  change χ ((countableUltralimitHom U F).rangeRestrict x) = ultralimitAddHom U g x
  rw [hu, ← hv, e.symm_apply_apply]

end Erdos335.Loeb

end
