import Erdos335.LoebTranslationStructure
import Erdos335.LoebDifferenceDeficit

/-!
# Complements and negation of translation periods
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise

noncomputable section

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]

local instance aePeriodOperationsLoebSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U

theorem loeb_neg_congr_ae
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (S T : Set ((U : Filter ℕ).Product X)) (h : S =ᵐ[loebMeasure U hU] T) :
    -S =ᵐ[loebMeasure U hU] -T := by
  have hpre := (loebMeasurePreserving_sub_left U hU (0 : (U : Filter ℕ).Product X)).quasiMeasurePreserving.ae h
  filter_upwards [hpre] with x hx
  simpa only [Set.mem_neg, zero_sub] using hx

theorem loeb_ae_period_compl
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (S : Set ((U : Filter ℕ).Product X)) (t : (U : Filter ℕ).Product X)
    (h : t +ᵥ Sᶜ =ᵐ[loebMeasure U hU] Sᶜ) :
    t +ᵥ S =ᵐ[loebMeasure U hU] S := by
  rw [vadd_set_compl] at h
  filter_upwards [h] with x hx
  change ((x ∉ t +ᵥ S) = (x ∉ S)) at hx
  exact propext (not_iff_not.mp (Iff.of_eq hx))

theorem loeb_ae_period_of_neg
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (S : Set ((U : Filter ℕ).Product X)) (t : (U : Filter ℕ).Product X)
    (h : (-t) +ᵥ (-S) =ᵐ[loebMeasure U hU] -S) :
    t +ᵥ S =ᵐ[loebMeasure U hU] S := by
  have hn := loeb_neg_congr_ae U hU ((-t) +ᵥ (-S)) (-S) h
  have hset : -((-t) +ᵥ (-S)) = t +ᵥ S := by
    ext x
    simp [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, add_comm]
  simpa only [hset, neg_neg] using hn

end Erdos335.Loeb

end
