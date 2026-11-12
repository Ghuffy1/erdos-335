import Erdos335.LoebTranslationStructure

/-!
# Integer multiples of a Loeb translation period
-/

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance integerPeriodsLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_period_nsmul
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (S : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (t : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
    (ht : t +ᵥ S =ᵐ[loebMeasure U hU] S) (n : ℕ) :
    (n • t) +ᵥ S =ᵐ[loebMeasure U hU] S := by
  induction n with
  | zero =>
    rw [zero_nsmul, zero_vadd]
  | succ n ih =>
    have heq : ((n + 1) • t) +ᵥ S = t +ᵥ ((n • t) +ᵥ S) := by
      rw [vadd_vadd, add_nsmul, one_nsmul, add_comm (n • t) t]
    rw [heq]
    exact (loeb_vadd_congr_ae U hU _ _ t ih).trans ht

theorem loeb_translate_membership_ae
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (S T : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (t : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
    (hST : t +ᵥ S ≤ᵐ[loebMeasure U hU] T) :
    ∀ᵐ x ∂loebMeasure U hU, x ∈ S → t + x ∈ T := by
  have hmap : t +ᵥ S ≤ᵐ[Measure.map (fun x => t + x) (loebMeasure U hU)] T := by
    rw [loebMeasure_map_add_left U hU t]
    exact hST
  have hp := ae_of_ae_map (measurable_add_left U hU t).aemeasurable hmap
  filter_upwards [hp] with x hx hxS
  exact hx ⟨x, hxS, rfl⟩

theorem productProjection_nat_mul
    (U : Ultrafilter ℕ) (q : ℕ → ℕ+) (n t : ℕ) :
    productProjection (U : Filter ℕ) (fun s => ((n * t : ℕ) : ZMod (q s : ℕ))) =
      n • productProjection (U : Filter ℕ) (fun s => (t : ZMod (q s : ℕ))) := by
  change productProjection (U : Filter ℕ) (fun s => ((n * t : ℕ) : ZMod (q s : ℕ))) =
    productProjection (U : Filter ℕ) (fun s => n • (t : ZMod (q s : ℕ)))
  congr 1
  funext s
  simp only [Nat.cast_mul, nsmul_eq_mul]

end Erdos335.Loeb

end
