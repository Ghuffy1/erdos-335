import Erdos335.LoebMaximalBackground
import Erdos335.LoebTranslationStructure
import Erdos335.LoebIrreducibleCore

/-!
# Strictness of a quasi-periodic background sum

For an irreducible equality pair with no positive essential period, a
positive quasi-periodic active part forces a strict background sum.
The equality case would give a positive period for both disjoint pieces
of a full-measure enlargement of the original sumset.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance strictBackgroundLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_background_sum_strict_of_irreducible
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H A)
    (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (hActpos : 0 < loebMeasure U hU p.active)
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hnotperiod : ¬ ∃ L : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (L : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (L : Set _) ∧
      (A + B) + (L : Set _) =ᵐ[loebMeasure U hU] A + B) :
    internalInnerMeasure U hU (p.background + B) <
      loebMeasure U hU p.background + loebMeasure U hU B := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  change μ (A + B) = μ A + μ B at hfull
  let T := p.background + B
  let P := T + (H : Set G)
  let S := (A + B) ∪ P
  have hAm : MeasurableSet A := p.partition.symm ▸ (p.background_measurable.union p.active_measurable)
  have hBgsub : p.background ⊆ A := subset_union_left.trans p.partition.ge
  have hActsub : p.active ⊆ A := subset_union_right.trans p.partition.ge
  have hTsub : T ⊆ A + B := add_subset_add hBgsub Subset.rfl
  obtain ⟨hTm, hPae⟩ := loeb_sum_with_essentially_periodic_summand U hU q H hHm hHpos
    B p.background p.background_periodic
  rw [add_comm B p.background] at hTm hPae
  have hPm : MeasurableSet P := measurable_saturation_of_positive_subgroup U hU q H hHm hHpos T
  have hPP : P + (H : Set G) = P := by
    dsimp only [P]
    rw [add_assoc, coe_add_coe]
  have hTP : T ⊆ P := fun x hx => ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  have hPmass : μ P = μ T := measure_congr hPae
  have hSae : S =ᵐ[μ] A + B := by
    filter_upwards [hPae] with x hx
    change (x ∈ A + B ∨ x ∈ P) = (x ∈ A + B)
    apply propext
    constructor
    · rintro (hxS | hxP)
      · exact hxS
      · exact hTsub (hx.mp hxP)
    · exact Or.inl
  have hSm' : MeasurableSet S := hSm.union hPm
  have hSmass : μ S = μ (A + B) := measure_congr hSae
  have hSS : A + B ⊆ S := subset_union_left
  have essential_of_period (L : AddSubgroup G) (hperiod : S + (L : Set G) = S) :
      (A + B) + (L : Set G) =ᵐ[μ] A + B := by
    have hinner : internalInnerMeasure U hU (A + B) = μ S :=
      (internalInnerMeasure_eq U hU _ hSm).trans hSmass.symm
    exact loeb_essential_period_of_full_inner_subset U hU q L (A + B) S hSS hinner hperiod
  have hparts : Disjoint p.background p.active := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp p.separated ⟨x, hy, 0, H.zero_mem, add_zero x⟩ hx
  have hAmass : μ A = μ p.background + μ p.active :=
    (congrArg μ p.partition).trans (measure_union hparts p.active_measurable)
  obtain ⟨a, ha⟩ := p.active_nonempty
  obtain ⟨ka, hka, hkaa⟩ := p.active_subset_coset ha
  have hAcoset : p.active ⊆ a +ᵥ (H : Set G) := by
    intro x hx
    obtain ⟨kx, hkx, hkxx⟩ := p.active_subset_coset hx
    refine ⟨kx - ka, H.sub_mem hkx hka, ?_⟩
    change p.anchor + ka = a at hkaa
    change p.anchor + kx = x at hkxx
    change a + (kx - ka) = x
    rw [← hkaa, ← hkxx]
    abel
  let C := B ∩ (fun b : G => a + b) ⁻¹' Pᶜ
  let X := p.active + C
  have hCm : MeasurableSet C := hBm.inter (hPm.compl.preimage (measurable_add_left U hU a))
  have in_periodic_coset (x : G) (hx : x ∈ p.active) (b : G) :
      x + b ∈ P ↔ a + b ∈ P := by
    obtain ⟨k, hk, hkx⟩ := hAcoset hx
    change a + k = x at hkx
    constructor
    · intro hxb
      have hm : (x + b) + (-k) ∈ P + (H : Set G) := ⟨x + b, hxb, -k, H.neg_mem hk, rfl⟩
      rw [hPP] at hm
      convert hm using 1
      rw [← hkx]
      abel
    · intro hab
      have hm : (a + b) + k ∈ P + (H : Set G) := ⟨a + b, hab, k, hk, rfl⟩
      rw [hPP] at hm
      convert hm using 1
      rw [← hkx]
      abel
  have hPX : Disjoint P X := by
    apply Set.disjoint_left.mpr
    rintro z hzP ⟨x, hx, b, hb, rfl⟩
    exact hb.2 ((in_periodic_coset x hx b).mp hzP)
  have hdecomp : S = P ∪ X := by
    ext z
    constructor
    · rintro (hzS | hzP)
      · obtain ⟨x, hx, b, hb, rfl⟩ := hzS
        by_cases hab : a + b ∈ P
        · rcases (p.partition ▸ hx) with hxBg | hxAct
          · exact Or.inl (hTP ⟨x, hxBg, b, hb, rfl⟩)
          · exact Or.inl ((in_periodic_coset x hxAct b).mpr hab)
        · rcases (p.partition ▸ hx) with hxBg | hxAct
          · exact Or.inl (hTP ⟨x, hxBg, b, hb, rfl⟩)
          · exact Or.inr ⟨x, hxAct, b, ⟨hb, hab⟩, rfl⟩
      · exact Or.inl hzP
    · rintro (hzP | ⟨x, hx, b, hb, rfl⟩)
      · exact Or.inr hzP
      · exact Or.inl ⟨x, hActsub hx, b, hb.1, rfl⟩
  have hXeq : X = S \ P := by
    rw [hdecomp]
    ext x
    constructor
    · intro hx
      exact ⟨Or.inr hx, fun hp => Set.disjoint_left.mp hPX hp hx⟩
    · rintro ⟨hp | hx, hn⟩
      · exact False.elim (hn hp)
      · exact hx
  have hXm : MeasurableSet X := hXeq.symm ▸ hSm'.diff hPm
  have hCne : C.Nonempty := by
    by_contra hn
    have hCempty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    have hSP : S = P := by simpa only [X, hCempty, add_empty, union_empty] using hdecomp
    apply hnotperiod
    refine ⟨H, hHm, hHpos, essential_of_period H ?_⟩
    rw [hSP]
    exact hPP
  have hmass : μ S = μ P + μ X := by rw [hdecomp, measure_union hPX hXm]
  have hXlower : μ p.active ≤ μ X := by
    obtain ⟨b, hb⟩ := hCne
    have hsub : b +ᵥ p.active ⊆ X := by
      rintro z ⟨x, hx, rfl⟩
      exact ⟨x, hx, b, hb, add_comm _ _⟩
    calc
      μ p.active = μ (b +ᵥ p.active) := (loebMeasure_image_add_left U hU b _).symm
      _ ≤ μ X := measure_mono hsub
  have hTbound : μ T ≤ μ p.background + μ B := by
    apply (ENNReal.add_le_add_iff_right (measure_ne_top μ p.active)).mp
    calc
      μ T + μ p.active ≤ μ P + μ X := add_le_add hPmass.symm.le hXlower
      _ = (μ p.background + μ B) + μ p.active := by rw [← hmass, hSmass, hfull, hAmass]; ac_rfl
  rw [internalInnerMeasure_eq U hU T hTm]
  apply lt_of_le_of_ne hTbound
  intro heq
  have hXmass : μ X = μ p.active := by
    apply (ENNReal.add_right_inj (measure_ne_top μ P)).mp
    calc
      μ P + μ X = μ S := hmass.symm
      _ = μ P + μ p.active := by rw [hSmass, hfull, hAmass, hPmass, heq]; ac_rfl
  have hCpos : 0 < μ C := by
    apply pos_iff_ne_zero.mpr
    intro hCzero
    let B' := B \ C
    have hB'm : MeasurableSet B' := hBm.diff hCm
    have hB'mass : μ B' = μ B := by
      rw [measure_sdiff inter_subset_left hCm.nullMeasurableSet (measure_ne_top μ C), hCzero, tsub_zero]
    have hAB' : A + B' ⊆ P := by
      rintro z ⟨x, hx, b, hb, rfl⟩
      rcases (p.partition ▸ hx) with hxBg | hxAct
      · exact hTP ⟨x, hxBg, b, hb.1, rfl⟩
      · apply (in_periodic_coset x hxAct b).mpr
        by_contra hn
        exact hb.2 ⟨hb.1, hn⟩
    have hinner : internalInnerMeasure U hU (A + B') = μ (A + B) :=
      (hirr A B' hAm hB'm Subset.rfl sdiff_subset rfl hB'mass).trans
        (internalInnerMeasure_eq U hU _ hSm)
    have hbad : μ (A + B) ≤ μ P := by
      rw [← hinner, ← internalInnerMeasure_eq U hU P hPm]
      exact internalInnerMeasure_mono U hU hAB'
    have hstrict : μ P < μ (A + B) := by
      rw [hPmass, heq, hfull, hAmass]
      calc
        μ p.background + μ B < (μ p.background + μ B) + μ p.active :=
          ENNReal.lt_add_right (by finiteness) hActpos.ne'
        _ = (μ p.background + μ p.active) + μ B := by ac_rfl
    exact (not_lt_of_ge hbad) hstrict
  have hcritical : internalInnerMeasure U hU X < μ p.active + μ C := by
    rw [internalInnerMeasure_eq U hU X hXm, hXmass]
    exact ENNReal.lt_add_right (measure_ne_top μ p.active) hCpos.ne'
  let L := AddAction.stabilizer G X
  obtain ⟨_, hLm, hLpos, _⟩ := loeb_measurable_kneser_identity U hU q p.active C
    p.active_measurable hCm hActpos hCpos hcritical
  obtain ⟨hJm, hJpos⟩ := loeb_positive_subgroup_intersection U hU q H L hHm hLm hHpos hLpos
  have hXJ : X + ((H ⊓ L : AddSubgroup G) : Set G) = X := by
    apply subset_antisymm
    · rintro z ⟨x, hx, k, hk, rfl⟩
      have hfix : k +ᵥ X = X := hk.2
      have hm : k + x ∈ X := by rw [← hfix]; exact ⟨x, hx, rfl⟩
      simpa only [add_comm x k] using hm
    · intro x hx
      exact ⟨x, hx, 0, (H ⊓ L).zero_mem, add_zero x⟩
  have hPJ : P + ((H ⊓ L : AddSubgroup G) : Set G) = P := by
    apply subset_antisymm
    · intro x hx
      have hm := add_subset_add (show P ⊆ P from Subset.rfl) (show H ⊓ L ≤ H from inf_le_left) hx
      rwa [hPP] at hm
    · intro x hx
      exact ⟨x, hx, 0, (H ⊓ L).zero_mem, add_zero x⟩
  apply hnotperiod
  refine ⟨H ⊓ L, hJm, hJpos, essential_of_period (H ⊓ L) ?_⟩
  rw [hdecomp, union_add, hPJ, hXJ]

end Erdos335.Loeb

end
