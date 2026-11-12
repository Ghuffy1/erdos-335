import Erdos335.LoebHomOperations
import Erdos335.LoebCountableFactor
import Erdos335.CompactCharacterDensity
import Mathlib.Analysis.Complex.Circle

/-!
# Internal characters on a countable compact factor

Internal characters that descend to the factor form a separating family
closed under multiplication and conjugation. Their linear span is dense.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)]

def internalCharacterFunctions (U : Ultrafilter ℕ)
    (F : ℕ → ∀ n, X n →+ Additive Circle) :
    Set C((countableUltralimitHom U F).range, ℂ) :=
  {p | ∃ χ : ∀ n, AddChar (X n) Circle,
    ∀ x, p ((countableUltralimitHom U F).rangeRestrict x) =
      ((ultralimitAddHom U (fun n => (χ n).toAddMonoidHom) x).toMul : ℂ)}

theorem one_mem_internalCharacterFunctions (U : Ultrafilter ℕ)
    (F : ℕ → ∀ n, X n →+ Additive Circle) :
    (1 : C((countableUltralimitHom U F).range, ℂ)) ∈ internalCharacterFunctions U F := by
  refine ⟨fun _ => 0, ?_⟩
  intro x
  change (1 : ℂ) = ((ultralimitAddHom U (fun n => (0 : X n →+ Additive Circle)) x).toMul : ℂ)
  rw [ultralimitAddHom_zero_family]
  rfl

theorem mul_mem_internalCharacterFunctions (U : Ultrafilter ℕ)
    (F : ℕ → ∀ n, X n →+ Additive Circle)
    (p q : C((countableUltralimitHom U F).range, ℂ))
    (hp : p ∈ internalCharacterFunctions U F) (hq : q ∈ internalCharacterFunctions U F) :
    p * q ∈ internalCharacterFunctions U F := by
  obtain ⟨χ, hχ⟩ := hp
  obtain ⟨ψ, hψ⟩ := hq
  refine ⟨fun n => χ n + ψ n, ?_⟩
  intro x
  change p ((countableUltralimitHom U F).rangeRestrict x) *
      q ((countableUltralimitHom U F).rangeRestrict x) = _
  rw [hχ x, hψ x]
  change _ = ((ultralimitAddHom U (fun n => (χ n).toAddMonoidHom + (ψ n).toAddMonoidHom) x).toMul : ℂ)
  rw [ultralimitAddHom_add_family]
  rfl

theorem star_mem_internalCharacterFunctions (U : Ultrafilter ℕ)
    (F : ℕ → ∀ n, X n →+ Additive Circle)
    (p : C((countableUltralimitHom U F).range, ℂ))
    (hp : p ∈ internalCharacterFunctions U F) : star p ∈ internalCharacterFunctions U F := by
  obtain ⟨χ, hχ⟩ := hp
  refine ⟨fun n => AddChar.toAddMonoidHomEquiv.symm (-(χ n).toAddMonoidHom), ?_⟩
  intro x
  change star (p ((countableUltralimitHom U F).rangeRestrict x)) = _
  rw [hχ x]
  change _ = ((ultralimitAddHom U (fun n => -(χ n).toAddMonoidHom) x).toMul : ℂ)
  rw [ultralimitAddHom_neg_family]
  exact (Circle.coe_inv_eq_conj _).symm

theorem coordinate_mem_internalCharacterFunctions (U : Ultrafilter ℕ)
    (F : ℕ → ∀ n, X n →+ Additive Circle) (k : ℕ) :
    (⟨(fun y => ((y : ℕ → Additive Circle) k).toMul),
      continuous_subtype_val.comp (continuous_countable_factor_coordinate U F k)⟩ :
        C((countableUltralimitHom U F).range, ℂ)) ∈ internalCharacterFunctions U F := by
  refine ⟨fun n => AddChar.toAddMonoidHomEquiv.symm (F k n), ?_⟩
  intro x
  change ((countableUltralimitHom U F x k).toMul : ℂ) = _
  rw [countableUltralimitHom_apply]
  rfl

theorem internalCharacterFunctions_separate (U : Ultrafilter ℕ)
    (F : ℕ → ∀ n, X n →+ Additive Circle)
    (x y : (countableUltralimitHom U F).range) (hxy : x ≠ y) :
    ∃ p ∈ internalCharacterFunctions U F, p x ≠ p y := by
  have hval : (x : ℕ → Additive Circle) ≠ (y : ℕ → Additive Circle) := by
    intro h
    exact hxy (Subtype.ext h)
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hval
  refine ⟨⟨(fun y => ((y : ℕ → Additive Circle) k).toMul),
    continuous_subtype_val.comp (continuous_countable_factor_coordinate U F k)⟩,
    coordinate_mem_internalCharacterFunctions U F k, ?_⟩
  intro h
  apply hk
  exact Subtype.ext h

theorem internalCharacterFunctions_span_dense (U : Ultrafilter ℕ)
    (F : ℕ → ∀ n, X n →+ Additive Circle)
    [CompactSpace (countableUltralimitHom U F).range] :
    (Submodule.span ℂ (internalCharacterFunctions U F)).topologicalClosure = ⊤ :=
  separating_multiplicative_span_dense (internalCharacterFunctions U F)
    (one_mem_internalCharacterFunctions U F)
    (fun p hp q hq => mul_mem_internalCharacterFunctions U F p q hp hq)
    (star_mem_internalCharacterFunctions U F) (internalCharacterFunctions_separate U F)

theorem internalCharacterFunctions_norm (U : Ultrafilter ℕ)
    (F : ℕ → ∀ n, X n →+ Additive Circle)
    (p : C((countableUltralimitHom U F).range, ℂ))
    (hp : p ∈ internalCharacterFunctions U F)
    (y : (countableUltralimitHom U F).range) : ‖p y‖ = 1 := by
  obtain ⟨χ, hχ⟩ := hp
  obtain ⟨y, x, rfl⟩ := y
  change ‖p ((countableUltralimitHom U F).rangeRestrict x)‖ = 1
  rw [hχ x]
  exact Circle.norm_coe _

theorem internalCharacterFunctions_map_add (U : Ultrafilter ℕ)
    (F : ℕ → ∀ n, X n →+ Additive Circle)
    (p : C((countableUltralimitHom U F).range, ℂ))
    (hp : p ∈ internalCharacterFunctions U F)
    (y z : (countableUltralimitHom U F).range) : p (y + z) = p y * p z := by
  obtain ⟨χ, hχ⟩ := hp
  obtain ⟨y, x, rfl⟩ := y
  obtain ⟨z, t, rfl⟩ := z
  change p ((countableUltralimitHom U F).rangeRestrict x +
    (countableUltralimitHom U F).rangeRestrict t) =
      p ((countableUltralimitHom U F).rangeRestrict x) *
        p ((countableUltralimitHom U F).rangeRestrict t)
  rw [← map_add, hχ (x + t), hχ x, hχ t, map_add]
  rfl

theorem internalCharacterFunctions_map_zero (U : Ultrafilter ℕ)
    (F : ℕ → ∀ n, X n →+ Additive Circle)
    (p : C((countableUltralimitHom U F).range, ℂ))
    (hp : p ∈ internalCharacterFunctions U F) : p 0 = 1 := by
  obtain ⟨χ, hχ⟩ := hp
  simpa using hχ 0

theorem internalCharacterFunctions_addChar (U : Ultrafilter ℕ)
    (F : ℕ → ∀ n, X n →+ Additive Circle)
    (p : C((countableUltralimitHom U F).range, ℂ))
    (hp : p ∈ internalCharacterFunctions U F) :
    ∃ χ : AddChar (countableUltralimitHom U F).range Circle,
      ∀ y, (χ y : ℂ) = p y := by
  let c : (countableUltralimitHom U F).range → Circle := fun y =>
    ⟨p y, mem_sphere_zero_iff_norm.mpr (internalCharacterFunctions_norm U F p hp y)⟩
  let χ : AddChar (countableUltralimitHom U F).range Circle := {
    toFun := c
    map_zero_eq_one' := Subtype.ext (internalCharacterFunctions_map_zero U F p hp)
    map_add_eq_mul' := fun y z => Subtype.ext (internalCharacterFunctions_map_add U F p hp y z)
  }
  exact ⟨χ, fun _ => rfl⟩

end Erdos335.Loeb
