import Erdos335.LoebSpectralApproximation
import Erdos335.LoebCountableFactor

/-!
# A common compact factor for convolution approximations

The finite-rank approximants at every accuracy use one countable family of
internal characters. Their joint compact factor carries Haar probability,
and the convolution is approximated in mean square by continuous functions
on this same factor.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped BigOperators

noncomputable section

namespace Erdos335.Loeb

local instance : MeasurableSpace (Additive Circle) := borel (Additive Circle)
local instance : BorelSpace (Additive Circle) := ⟨rfl⟩

theorem exists_compact_convolution_approximations
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f g : ∀ n, X n → ℂ) (hf : ∀ n x, ‖f n x‖ ≤ 1) (hg : ∀ n x, ‖g n x‖ ≤ 1) :
    ∃ F : ℕ → ∀ n, X n →+ Additive Circle,
      ∃ P : ℕ → (countableUltralimitHom U F).range → ℂ,
        (∀ k, Continuous (P k)) ∧
        IsCompact ((countableUltralimitHom U F).range : Set (ℕ → Additive Circle)) ∧
        Measure.IsAddHaarMeasure
          (@Measure.map _ _ (loebMeasurableSpace U) _
            (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU)) ∧
        ∀ k : ℕ, (∫ x, ‖(∫ t, boundedComplexFunction U f 1 hf t *
          boundedComplexFunction U g 1 hg (x - t) ∂loebMeasure U hU) -
            P k ((countableUltralimitHom U F).rangeRestrict x)‖ ^ 2
              ∂loebMeasure U hU) ≤ (1 / (k + 1 : ℝ)) ^ 2 := by
  classical
  let M (k : ℕ) : ℕ := (k + 1) ^ 2
  have hM (k : ℕ) : 1 / (1 / (k + 1 : ℝ)) ^ 2 ≤ (M k : ℝ) := by
    simp [M, one_div]
  have hε (k : ℕ) : 0 < 1 / (k + 1 : ℝ) := by positivity
  choose χ c hc herr using fun k : ℕ =>
    exists_loeb_convolution_polynomial U hU f g hf hg (1 / (k + 1 : ℝ)) (hε k) (M k) (hM k)
  let J := Σ k : ℕ, Fin (M k)
  let F (i n : ℕ) : X n →+ Additive Circle :=
    match Encodable.decode (α := J) i with
    | none => 0
    | some j => (χ j.1 n j.2).toAddMonoidHom
  have hF (k : ℕ) (j : Fin (M k)) :
      F (Encodable.encode (⟨k, j⟩ : J)) = fun n => (χ k n j).toAddMonoidHom := by
    funext n
    simp only [F, Encodable.encodek]
  let π := countableUltralimitHom U F
  let P (k : ℕ) (y : π.range) : ℂ :=
    ∑ j : Fin (M k), c k j *
      (((y : ℕ → Additive Circle) (Encodable.encode (⟨k, j⟩ : J))).toMul : ℂ)
  have hval : Continuous (fun z : Additive Circle => (z.toMul : ℂ)) := continuous_subtype_val
  have hP (k : ℕ) : Continuous (P k) := by
    apply continuous_finsetSum
    intro j _
    exact continuous_const.mul
      (hval.comp ((continuous_apply (Encodable.encode (⟨k, j⟩ : J))).comp continuous_subtype_val))
  have hPeq (k : ℕ) (x : (U : Filter ℕ).Product X) :
      P k ((countableUltralimitHom U F).rangeRestrict x) = ∑ j : Fin (M k), c k j *
        ((ultralimitAddHom U (fun n => (χ k n j).toAddMonoidHom) x).toMul : ℂ) := by
    apply Finset.sum_congr rfl
    intro j _
    change c k j * ((countableUltralimitHom U F x (Encodable.encode (⟨k, j⟩ : J))).toMul : ℂ) = _
    rw [countableUltralimitHom_apply, hF]
  refine ⟨F, P, hP, isCompact_range_countableUltralimitHom U hU F,
    countableUltralimitHom_haar U hU F, ?_⟩
  intro k
  simpa only [hPeq] using herr k

end Erdos335.Loeb

end
