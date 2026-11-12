import Erdos335.LoebStrictBackgroundPair
import Erdos335.LoebFinitePeriodIntersection
import Erdos335.LoebEnvelopeStabilizer

/-!
# The stabilizer of a strict maximal background

For a nonextendible aperiodic equality pair, the stabilizer of a strict
background sum is its maximal background period. This removes the
stabilizer identity premise from the strict-background pair theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance maximalBackgroundLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_background_stabilizer_eq_of_maximal_period
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H A)
    (hBm : MeasurableSet B) (hBgpos : 0 < loebMeasure U hU p.background)
    (hBpos : 0 < loebMeasure U hU B)
    (hsmall : internalInnerMeasure U hU (p.background + B) <
      loebMeasure U hU p.background + loebMeasure U hU B)
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hmax : ∀ L : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (L : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (L : Set _) →
      loebMeasure U hU ((p.background + (L : Set _)) \ p.background) = 0 → L ≤ H)
    (hnotperiod : ¬ ∃ L : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (L : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (L : Set _) ∧
      (A + B) + (L : Set _) = A + B) :
    H = AddAction.stabilizer ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) (p.background + B) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let T := p.background + B
  let L := AddAction.stabilizer G T
  have hAm : MeasurableSet A := p.partition.symm ▸ (p.background_measurable.union p.active_measurable)
  have hBgsub : p.background ⊆ A := subset_union_left.trans p.partition.ge
  have hTsub : T ⊆ A + B := add_subset_add hBgsub Subset.rfl
  obtain ⟨hTm, hLm, hLpos, _⟩ := loeb_measurable_kneser_identity U hU q p.background B
    p.background_measurable hBm hBgpos hBpos hsmall
  have hTperiod : T + (L : Set G) = T := by
    apply subset_antisymm
    · rintro x ⟨s, hs, k, hk, rfl⟩
      have hfix : k +ᵥ T = T := hk
      have hm : k + s ∈ T := by rw [← hfix]; exact ⟨s, hs, rfl⟩
      simpa only [add_comm s k] using hm
    · intro x hx
      exact ⟨x, hx, 0, L.zero_mem, add_zero x⟩
  have shrink (S : Set G) (J K : AddSubgroup G) (hJK : J ≤ K)
      (hS : S + (K : Set G) = S) : S + (J : Set G) = S := by
    apply subset_antisymm
    · intro x hx
      have hx' := add_subset_add (show S ⊆ S from Subset.rfl) hJK hx
      rwa [hS] at hx'
    · intro x hx
      exact ⟨x, hx, 0, J.zero_mem, add_zero x⟩
  obtain ⟨_, hJpos⟩ := loeb_positive_subgroup_intersection U hU q H L hHm hLm hHpos hLpos
  have hTJ := shrink T (H ⊓ L) L inf_le_right hTperiod
  have hTHJ : (T + (H : Set G)) + ((H ⊓ L : AddSubgroup G) : Set G) = T + (H : Set G) := by
    calc
      (T + (H : Set G)) + ((H ⊓ L : AddSubgroup G) : Set G) =
          (T + ((H ⊓ L : AddSubgroup G) : Set G)) + (H : Set G) := by ac_rfl
      _ = T + (H : Set G) := by rw [hTJ]
  have hTHae : T + (H : Set G) =ᵐ[μ] T := by
    have h := (loeb_sum_with_essentially_periodic_summand U hU q H hHm hHpos B p.background p.background_periodic).2
    simpa only [add_comm B p.background] using h
  have hTH : T + (H : Set G) = T := loeb_periodic_sets_eq_of_ae U hU q (H ⊓ L) hJpos
    _ _ hTHJ hTJ hTHae
  have hHL : H ≤ L := subgroup_le_stabilizer_of_add_eq H T hTH
  let C := p.background + (L : Set G)
  have hCm : MeasurableSet C := measurable_saturation_of_positive_subgroup U hU q L hLm hLpos p.background
  have hCB : C + B = T := by
    calc
      C + B = T + (L : Set G) := by dsimp only [C, T]; ac_rfl
      _ = T := hTperiod
  have hdisjoint : Disjoint C p.active := by
    apply Set.disjoint_left.mpr
    intro x hxC hxAct
    have hActC : p.active ⊆ C := by
      intro y hy
      obtain ⟨kx, hkx, hkxx⟩ := p.active_subset_coset hxAct
      obtain ⟨ky, hky, hkyy⟩ := p.active_subset_coset hy
      obtain ⟨c, hc, l, hl, hlx⟩ := hxC
      refine ⟨c, hc, l + (ky - kx), L.add_mem hl (hHL (H.sub_mem hky hkx)), ?_⟩
      change p.anchor + kx = x at hkxx
      change p.anchor + ky = y at hkyy
      change c + l = x at hlx
      change c + (l + (ky - kx)) = y
      calc
        c + (l + (ky - kx)) = x + (ky - kx) := by rw [← add_assoc, hlx]
        _ = y := by rw [← hkxx, ← hkyy]; abel
    have hAC : A ⊆ C := by
      intro y hy
      rcases (p.partition ▸ hy) with hyBg | hyAct
      · exact ⟨y, hyBg, 0, L.zero_mem, add_zero y⟩
      · exact hActC hyAct
    have hSsub : A + B ⊆ T := by rw [← hCB]; exact add_subset_add hAC Subset.rfl
    have hST : A + B = T := subset_antisymm hSsub hTsub
    apply hnotperiod
    refine ⟨L, hLm, hLpos, ?_⟩
    rw [hST]
    exact hTperiod
  let A' := A ∪ C
  have hA'm : MeasurableSet A' := hAm.union hCm
  have hsum : A' + B = A + B := by
    change (A ∪ C) + B = A + B
    rw [union_add, hCB, union_eq_left.mpr hTsub]
  have hAmass : μ A' = μ A := loeb_nonextendible_left_extension_eq U hU A B A'
    hBm hA'm subset_union_left hne (by rw [hsum])
  have hAprimeNull : μ (A' \ A) = 0 := by
    rw [measure_sdiff subset_union_left hAm.nullMeasurableSet (measure_ne_top μ A), hAmass, tsub_self]
  have hCnull : μ (C \ A) = 0 := measure_mono_null (sdiff_subset_sdiff_left subset_union_right) hAprimeNull
  have hperiodBg : μ (C \ p.background) = 0 := by
    apply measure_mono_null _ hCnull
    rintro x ⟨hxC, hxBg⟩
    refine ⟨hxC, ?_⟩
    intro hxA
    rcases (p.partition ▸ hxA) with hBg | hAct
    · exact hxBg hBg
    · exact Set.disjoint_left.mp hdisjoint hxC hAct
  have hLH : L ≤ H := hmax L hLm hLpos hperiodBg
  exact hHL.antisymm hLH

end Erdos335.Loeb

end
