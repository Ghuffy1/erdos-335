import Erdos335.LoebCompactRange
import Erdos335.LoebGroup
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Compact group factors of a finite-group ultraproduct

Coordinate homomorphisms into a compact metric group induce a homomorphism
on the ultraproduct. Countable saturation makes its image compact.
-/

set_option autoImplicit false

open Filter Set Topology

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)]
  {E : Type*} [AddCommGroup E] [MetricSpace E] [CompactSpace E]
  [IsTopologicalAddGroup E]

noncomputable def ultralimitAddHom (U : Ultrafilter ℕ) (f : ∀ n, X n →+ E) :
    (U : Filter ℕ).Product X →+ E where
  toFun := ultralimitFunction U (fun n => f n)
  map_zero' := by
    apply tendsto_nhds_unique
      (tendsto_ultralimitFunction U (fun n => f n) (fun _ => 0))
    simpa only [map_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : E)) (U : Filter ℕ) (𝓝 0))
  map_add' x y := by
    induction x using Quotient.inductionOn with
    | h a =>
      induction y using Quotient.inductionOn with
      | h b =>
        change (U.map (fun n => f n (a n + b n))).lim =
          (U.map (fun n => f n (a n))).lim + (U.map (fun n => f n (b n))).lim
        have ha : Tendsto (fun n => f n (a n)) (U : Filter ℕ)
            (𝓝 (U.map (fun n => f n (a n))).lim) := (U.map _).le_nhds_lim
        have hb : Tendsto (fun n => f n (b n)) (U : Filter ℕ)
            (𝓝 (U.map (fun n => f n (b n))).lim) := (U.map _).le_nhds_lim
        apply tendsto_nhds_unique
          ((U.map (fun n => f n (a n + b n))).le_nhds_lim)
        simpa only [map_add] using ha.add hb

theorem isClosed_range_ultralimitAddHom
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (f : ∀ n, X n →+ E) :
    IsClosed ((ultralimitAddHom U f).range : Set E) :=
  isClosed_range_ultralimitFunction U hU (fun n => f n)

theorem isCompact_range_ultralimitAddHom
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (f : ∀ n, X n →+ E) :
    IsCompact ((ultralimitAddHom U f).range : Set E) :=
  (isClosed_range_ultralimitAddHom U hU f).isCompact

theorem measurable_ultralimitAddHom
    [∀ n, Finite (X n)] [MeasurableSpace E] [BorelSpace E]
    (U : Ultrafilter ℕ) (f : ∀ n, X n →+ E) :
    @Measurable ((U : Filter ℕ).Product X) E (loebMeasurableSpace U) _
      (ultralimitAddHom U f) :=
  measurable_ultralimitFunction U (fun n => f n)

theorem measurable_rangeRestrict_ultralimitAddHom
    [∀ n, Finite (X n)] [MeasurableSpace E] [BorelSpace E]
    (U : Ultrafilter ℕ) (f : ∀ n, X n →+ E) :
    @Measurable ((U : Filter ℕ).Product X) (ultralimitAddHom U f).range
      (loebMeasurableSpace U) _ (ultralimitAddHom U f).rangeRestrict :=
  (measurable_ultralimitAddHom U f).subtype_mk

end Erdos335.Loeb
