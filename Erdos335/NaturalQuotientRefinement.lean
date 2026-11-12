import Erdos335.NaturalCyclicProjection

/-!
# Compatibility of natural residue maps under quotient refinement
-/

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace Erdos335.Loeb

theorem naturalCyclicProjection_comp (q h k : ℕ+)
    (hhq : (h : ℕ) ∣ (q : ℕ)) (hkh : (k : ℕ) ∣ (h : ℕ)) :
    (naturalCyclicProjection h k).comp (naturalCyclicProjection q h) = naturalCyclicProjection q k := by
  ext x
  rw [← ZMod.natCast_zmod_val x]
  change naturalCyclicProjection h k (naturalCyclicProjection q h (x.val : ZMod (q : ℕ))) = _
  rw [naturalCyclicProjection_natCast q h hhq,
    naturalCyclicProjection_natCast h k hkh,
    naturalCyclicProjection_natCast q k (dvd_trans hkh hhq)]

theorem finiteQuotient_natural_refinement
    (U : Ultrafilter ℕ) (q : ℕ → ℕ+) (h k : ℕ+)
    (hhq : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (hkh : (k : ℕ) ∣ (h : ℕ)) :
    (naturalCyclicProjection h k).comp (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) =
      finiteQuotient U (fun n => naturalCyclicProjection (q n) k) := by
  rw [← finiteQuotient_comp]
  apply finiteQuotient_eq_of_eventually_natural
  · exact hhq.mono fun n hn t => by
      change naturalCyclicProjection h k (naturalCyclicProjection (q n) h (t : ZMod (q n : ℕ))) = _
      rw [naturalCyclicProjection_natCast (q n) h hn,
        naturalCyclicProjection_natCast h k hkh]
  · exact hhq.mono fun n hn t => naturalCyclicProjection_natCast (q n) k (dvd_trans hkh hn) t

theorem natural_quotient_preimage_composition
    (U : Ultrafilter ℕ) (q : ℕ → ℕ+) (h k : ℕ+)
    (hhq : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (hkh : (k : ℕ) ∣ (h : ℕ))
    (S : Set (ZMod (k : ℕ))) :
    (finiteQuotient U (fun n => naturalCyclicProjection (q n) k)) ⁻¹' S =
      (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹'
        ((naturalCyclicProjection h k) ⁻¹' S) := by
  have heq := finiteQuotient_natural_refinement U q h k hhq hkh
  ext x
  exact Iff.of_eq (congrArg (fun f => f x ∈ S) heq.symm)

end Erdos335.Loeb

end
