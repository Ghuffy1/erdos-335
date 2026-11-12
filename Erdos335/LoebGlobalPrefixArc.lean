import Erdos335.LoebStandardNonTorsion
import Erdos335.LoebStandardCharacterArc
import Erdos335.CircleArcModels

/-!
# A global irrational arc from an actual prefix Bohr model

Privately checked supporting development.
The standard character's non-torsion is proved from the retained global
density hypotheses through LoebStandardNonTorsion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance globalPrefixArcLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem short_circle_arc_properties
    (x : AddCircle (1 : ℝ)) (y : ℝ) (hy : 0 < y) (hyone : y < 1) :
    let J := x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 y)
    IsClosed J ∧ J.Nonempty ∧ J ≠ univ ∧ (interior J).Nonempty := by
  letI : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  letI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
    ⟨by simpa using AddCircle.measure_univ (1 : ℝ)⟩
  let J := x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 y)
  let O := x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Ioo 0 y)
  have hclosed : IsClosed J := by
    change IsClosed (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 y))
    rw [vadd_set_eq_neg_preimage]
    exact ((isCompact_Icc.image (AddCircle.continuous_mk' (1 : ℝ))).isClosed).preimage
      (continuous_const.add continuous_id)
  have hnonempty : J.Nonempty := by
    refine ⟨x + 0, ?_⟩
    exact ⟨(0 : AddCircle (1 : ℝ)), ⟨(0 : ℝ), ⟨le_rfl, hy.le⟩, rfl⟩, rfl⟩
  have hproper : J ≠ univ := by
    intro hfull
    have hvol : (volume J).toReal = y := by
      change (volume (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 y))).toReal = y
      rw [volume_unitCircle_normalized_closedArc x y hyone.le,
        ENNReal.toReal_ofReal hy.le]
    rw [hfull, measure_univ, ENNReal.toReal_one] at hvol
    exact (ne_of_lt hyone) hvol.symm
  have hopen : IsOpen O := by
    change IsOpen (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Ioo 0 y))
    rw [vadd_set_eq_neg_preimage]
    exact (QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo).preimage
      (continuous_const.add continuous_id)
  have hsub : O ⊆ J := by
    rintro z ⟨v, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨(t : AddCircle (1 : ℝ)), ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩, rfl⟩
  have hmid : x + ((y / 2 : ℝ) : AddCircle (1 : ℝ)) ∈ O := by
    refine ⟨((y / 2 : ℝ) : AddCircle (1 : ℝ)), ⟨y / 2, ?_, rfl⟩, rfl⟩
    constructor <;> linarith
  have hinside : O ⊆ interior J := by
    calc
      O = interior O := hopen.interior_eq.symm
      _ ⊆ interior J := interior_mono hsub
  exact ⟨hclosed, hnonempty, hproper, ⟨_, hinside hmid⟩⟩

theorem global_prefix_irrational_arc
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (hdiv : ∀ ell : ℕ+, ∀ᶠ n in U, (ell : ℕ) ∣ (q n : ℕ))
    (A B : Set ℕ) (c y : ℝ) (hC : HasDensity (A + B) c) (hc : c < 1)
    (hBpos : B ⊆ Ioi 0) (hB : HasDensity B y) (hy : 0 < y) (hyone : y < 1)
    (hAdensity : ∀ ell : ℕ+, ∃ ρ : ℝ, 0 < ρ ∧
      HasDensity (A ∩ {u : ℕ | (ell : ℕ) ∣ u}) ρ)
    (hBdensity : ∀ ell : ℕ+, ∃ ρ : ℝ, 0 < ρ ∧
      HasDensity (B ∩ {u : ℕ | (ell : ℕ) ∣ u}) ρ)
    (χ : ∀ n, ZMod (q n : ℕ) →+ AddCircle (1 : ℝ))
    (hsurj : Function.Surjective (ultralimitAddHom U χ))
    (E : ℕ → Set ℕ) (hexhaust : ∀ n ∈ B, ∀ᶠ i in U, n ∈ E i)
    (x : AddCircle (1 : ℝ))
    (hcontain : internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n) ⊆
      (ultralimitAddHom U χ) ⁻¹' (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 y)))
    (hprefix : internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
      =ᵐ[loebMeasure U hU] internalSet U
        (fun n => (cyclicWindow B 0 (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (hmodel : internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
      =ᵐ[loebMeasure U hU]
        (ultralimitAddHom U χ) ⁻¹' (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 y))) :
    ∃ θ start : ℝ, Irrational θ ∧ B ⊆ Proposed.closedArcPullback θ start y ∧
      HasDensity (Proposed.closedArcPullback θ start y \ B) 0 := by
  obtain ⟨hJclosed, hJnonempty, hJproper, hJinterior⟩ := short_circle_arc_properties x y hy hyone
  have hactual := hprefix.symm.trans hmodel
  have horder := standard_character_non_torsion_of_prefix_model U hU q hq hdiv A B c hC hc
    hAdensity hBdensity χ hsurj
    (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 y))
    hJclosed hJnonempty hJproper hJinterior hactual
  exact prefix_arc_of_non_torsion_character U q χ B E y hBpos hB hy hyone hexhaust x hcontain horder

end Erdos335.Loeb

end
