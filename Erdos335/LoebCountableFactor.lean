import Erdos335.LoebHaar
import Mathlib.Topology.MetricSpace.PiNat

/-!
# A compact factor for countably many coordinate homomorphisms

Countably many compact-valued internal homomorphisms factor simultaneously
through one compact metrizable group. The induced probability measure on
this factor is Haar measure.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace Erdos335.Loeb

attribute [local instance] PiCountable.metricSpace

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)]
  {E : Type*} [AddCommGroup E] [MetricSpace E] [CompactSpace E]
  [IsTopologicalAddGroup E]

noncomputable def countableUltralimitHom (U : Ultrafilter ℕ)
    (f : ℕ → ∀ n, X n →+ E) : (U : Filter ℕ).Product X →+ (ℕ → E) :=
  ultralimitAddHom U (fun n => AddMonoidHom.pi (fun k => f k n))

theorem countableUltralimitHom_apply (U : Ultrafilter ℕ)
    (f : ℕ → ∀ n, X n →+ E) (x : (U : Filter ℕ).Product X) (k : ℕ) :
    countableUltralimitHom U f x k = ultralimitAddHom U (f k) x := by
  induction x using Quotient.inductionOn with
  | h a =>
    have hlim := tendsto_ultralimitFunction U
      (fun n => (AddMonoidHom.pi (fun k => f k n) : X n →+ (ℕ → E))) a
    have hcomponent := (continuous_apply k).tendsto
      (ultralimitFunction U (fun n => AddMonoidHom.pi (fun k => f k n)) a)
    exact tendsto_nhds_unique (hcomponent.comp hlim)
      (tendsto_ultralimitFunction U (fun n => f k n) a)

theorem isCompact_range_countableUltralimitHom
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f : ℕ → ∀ n, X n →+ E) :
    IsCompact ((countableUltralimitHom U f).range : Set (ℕ → E)) :=
  isCompact_range_ultralimitAddHom U hU _

theorem measurable_countableUltralimitHom
    [∀ n, Finite (X n)] [MeasurableSpace E] [BorelSpace E]
    (U : Ultrafilter ℕ) (f : ℕ → ∀ n, X n →+ E) :
    @Measurable ((U : Filter ℕ).Product X) (ℕ → E)
      (loebMeasurableSpace U) _ (countableUltralimitHom U f) :=
  measurable_ultralimitAddHom U _

theorem countableUltralimitHom_haar
    [∀ n, Finite (X n)] [MeasurableSpace E] [BorelSpace E]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f : ℕ → ∀ n, X n →+ E) :
    Measure.IsAddHaarMeasure
      (@Measure.map _ _ (loebMeasurableSpace U) _
        (countableUltralimitHom U f).rangeRestrict (loebMeasure U hU)) :=
  loebMeasure_compact_factor_isAddHaarMeasure U hU _

theorem continuous_countable_factor_coordinate
    (U : Ultrafilter ℕ) (f : ℕ → ∀ n, X n →+ E) (k : ℕ) :
    Continuous (fun y : (countableUltralimitHom U f).range => (y : ℕ → E) k) :=
  (continuous_apply k).comp continuous_subtype_val

end Erdos335.Loeb
