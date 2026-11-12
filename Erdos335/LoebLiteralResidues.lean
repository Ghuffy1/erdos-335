import Erdos335.LoebFiniteQuotientMeasure
import Erdos335.Residues

/-!
# Literal residues retained by internal integer models

An internal model built from subsets of an integer set and containing
each fixed integer eventually has exactly its literal finite residues.
The finite quotient saturation consequently has the exact residue-cover
measure, including residues represented only by sparse or finite pieces.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance literalResiduesLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem addHom_saturation_eq_preimage_image {G F : Type*} [AddCommGroup G] [AddCommGroup F]
    (φ : G →+ F) (A : Set G) : A + (φ.ker : Set G) = φ ⁻¹' (φ '' A) := by
  ext x
  constructor
  · rintro ⟨a, ha, k, hk, rfl⟩
    refine ⟨a, ha, ?_⟩
    rw [map_add, show φ k = 0 from hk, add_zero]
  · rintro ⟨a, ha, hax⟩
    refine ⟨a, ha, x - a, ?_, by abel⟩
    change φ (x - a) = 0
    rw [map_sub, ← hax, sub_self]

theorem finiteQuotient_image_of_literal_exhaustion
    (U : Ultrafilter ℕ) (q : ℕ → ℕ+) (A : Set ℕ) (E : ℕ → Set ℕ)
    (hEA : ∀ᶠ n in U, E n ⊆ A)
    (hexhaust : ∀ a ∈ A, ∀ᶠ n in U, a ∈ E n)
    (h : ℕ+) (p : ∀ n, ZMod (q n : ℕ) →+ ZMod (h : ℕ))
    (hp : ∀ᶠ n in U, ∀ a : ℕ, p n (a : ZMod (q n : ℕ)) = (a : ZMod (h : ℕ))) :
    (finiteQuotient U p) '' (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)) =
      (residues (h : ℕ) A : Set (ZMod (h : ℕ))) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    induction x using Quotient.inductionOn with
    | h f =>
      change ∀ᶠ n in U, f n ∈ ((↑) : ℕ → ZMod (q n : ℕ)) '' E n at hx
      obtain ⟨n, hn, hEA', hp', hf⟩ := Filter.nonempty_of_mem
        (hx.and (hEA.and (hp.and (eventually_eq_finiteValue U (fun n => p n (f n))))))
      obtain ⟨a, ha, haf⟩ := hn
      apply mem_residues.mpr
      refine ⟨a, hEA' ha, ?_⟩
      change (a : ZMod (h : ℕ)) = finiteValue U (fun n => p n (f n))
      calc
        (a : ZMod (h : ℕ)) = p n (a : ZMod (q n : ℕ)) := (hp' a).symm
        _ = p n (f n) := congrArg (p n) haf
        _ = _ := hf
  · intro hy
    obtain ⟨a, ha, hay⟩ := mem_residues.mp hy
    refine ⟨productProjection (U : Filter ℕ) (fun n => (a : ZMod (q n : ℕ))), ?_, ?_⟩
    · change ∀ᶠ n in U, (a : ZMod (q n : ℕ)) ∈ ((↑) : ℕ → ZMod (q n : ℕ)) '' E n
      exact (hexhaust a ha).mono (fun n hn => ⟨a, hn, rfl⟩)
    · exact (finiteQuotient_natCast_of_eventually U q h p hp a).trans hay

theorem loeb_literal_exhaustion_saturation_measure
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A : Set ℕ) (E : ℕ → Set ℕ)
    (hEA : ∀ᶠ n in U, E n ⊆ A)
    (hexhaust : ∀ a ∈ A, ∀ᶠ n in U, a ∈ E n)
    (h : ℕ+) (p : ∀ n, ZMod (q n : ℕ) →+ ZMod (h : ℕ))
    (hp : ∀ᶠ n in U, Function.Surjective (p n) ∧
      ∀ a : ℕ, p n (a : ZMod (q n : ℕ)) = (a : ZMod (h : ℕ))) :
    loebMeasure U hU
      ((internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)) +
        ((finiteQuotient U p).ker : Set _)) =
      ((residues (h : ℕ) A).card : ℝ≥0∞) / (h : ℕ) := by
  rw [addHom_saturation_eq_preimage_image,
    finiteQuotient_image_of_literal_exhaustion U q A E hEA hexhaust h p (hp.mono fun _ hn => hn.2),
    loebMeasure_finiteQuotient_preimage U hU q p (hp.mono fun _ hn => hn.1)]
  simp

end Erdos335.Loeb

end
