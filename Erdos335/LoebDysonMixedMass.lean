import Erdos335.DysonCosetDecomposition
import Erdos335.LoebCriticalSolidity

/-!
# The mass of an occupied mixed coset

The Kneser deficit for the transformed pair is bounded by the combined
mass of the disjoint A and B sections in every occupied mixed coset.
This is equation (5.47) in Griesmer's compact inverse proof.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

theorem dysonMixedPart_coset_partition
    {G : Type*} [AddCommGroup G] (H : AddSubgroup G) (A B : Set G) (g : G)
    (hg : g ∈ dysonMixedPart H A B) :
    (A ∪ B) ∩ (g +ᵥ (H : Set G)) =
      (dysonMixedPart H A B ∩ (g +ᵥ (H : Set G))) ∪
        (dysonMixedPart H B A ∩ (g +ᵥ (H : Set G))) := by
  have hsat (S : Set G) (hS : g ∈ S + (H : Set G)) :
      g +ᵥ (H : Set G) ⊆ S + (H : Set G) := by
    rintro x ⟨k, hk, rfl⟩
    obtain ⟨s, hs, l, hl, hlg⟩ := hS
    refine ⟨s, hs, l + k, H.add_mem hl hk, ?_⟩
    change s + l = g at hlg
    change s + (l + k) = g + k
    rw [← hlg]
    abel
  have hAsat : g ∈ A + (H : Set G) := ⟨g, hg.1.1, 0, H.zero_mem, add_zero g⟩
  have hBsat : g ∈ B + (H : Set G) := hg.1.2
  have houtside : ∀ x ∈ g +ᵥ (H : Set G), x ∉ (A ∩ B) + (H : Set G) := by
    rintro x ⟨k, hk, hkx⟩ hx
    obtain ⟨d, hd, l, hl, hlx⟩ := hx
    apply hg.2
    refine ⟨d, hd, l - k, H.sub_mem hl hk, ?_⟩
    change g + k = x at hkx
    change d + l = x at hlx
    change d + (l - k) = g
    calc
      d + (l - k) = (d + l) - k := by abel
      _ = g := by rw [hlx, ← hkx]; abel
  apply subset_antisymm
  · rintro x ⟨hx, hxC⟩
    rcases hx with hxA | hxB
    · exact Or.inl ⟨⟨⟨hxA, hsat B hBsat hxC⟩, houtside x hxC⟩, hxC⟩
    · refine Or.inr ⟨⟨⟨hxB, hsat A hAsat hxC⟩, ?_⟩, hxC⟩
      simpa only [inter_comm B A] using houtside x hxC
  · rintro x (hx | hx)
    · exact ⟨Or.inl hx.1.1.1, hx.2⟩
    · exact ⟨Or.inr hx.1.1.1, hx.2⟩

local instance dysonMixedMassLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_dyson_mixed_coset_bound
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hIpos : 0 < loebMeasure U hU (A ∩ B))
    (hsmall : internalInnerMeasure U hU ((A ∪ B) + (A ∩ B)) <
      loebMeasure U hU (A ∪ B) + loebMeasure U hU (A ∩ B)) :
    let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
    let H := AddAction.stabilizer G ((A ∪ B) + (A ∩ B))
    ∀ g ∈ dysonMixedPart H A B,
      loebMeasure U hU A + loebMeasure U hU B ≤
        loebMeasure U hU ((A ∪ B) + (A ∩ B)) +
          (loebMeasure U hU (dysonMixedPart H A B ∩ (g +ᵥ (H : Set G))) +
            loebMeasure U hU (dysonMixedPart H B A ∩ (g +ᵥ (H : Set G)))) := by
  classical
  dsimp only
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let H := AddAction.stabilizer G ((A ∪ B) + (A ∩ B))
  have hUpos : 0 < μ (A ∪ B) := hIpos.trans_le (measure_mono (inter_subset_left.trans subset_union_left))
  obtain ⟨_, hHm, hHpos, hid⟩ := loeb_measurable_kneser_identity U hU q (A ∪ B) (A ∩ B)
    (hAm.union hBm) (hAm.inter hBm) hUpos hIpos hsmall
  intro g hg
  have hbound := loeb_coset_section_bound_of_kneser_identity U hU H hHm
    (A ∪ B) (A ∩ B) hid g (Or.inl hg.1.1)
  have hAhs : MeasurableSet (A + (H : Set G)) :=
    measurable_saturation_of_positive_subgroup U hU q H hHm hHpos A
  have hIhs : MeasurableSet ((A ∩ B) + (H : Set G)) :=
    measurable_saturation_of_positive_subgroup U hU q H hHm hHpos (A ∩ B)
  have hBmixed : MeasurableSet (dysonMixedPart H B A) := by
    simpa only [dysonMixedPart, inter_comm B A] using (hBm.inter hAhs).diff hIhs
  have hgm : MeasurableSet (g +ᵥ (H : Set G)) := measurable_loeb_coset U hU H hHm g
  have hd : Disjoint (dysonMixedPart H A B ∩ (g +ᵥ (H : Set G)))
      (dysonMixedPart H B A ∩ (g +ᵥ (H : Set G))) := by
    apply Set.disjoint_left.mpr
    rintro x hx hy
    exact Set.disjoint_left.mp (dysonMixedPart_disjoint H A B) hx.1 hy.1.1.1
  have hmass : μ ((A ∪ B) ∩ (g +ᵥ (H : Set G))) =
      μ (dysonMixedPart H A B ∩ (g +ᵥ (H : Set G))) +
        μ (dysonMixedPart H B A ∩ (g +ᵥ (H : Set G))) := by
    rw [dysonMixedPart_coset_partition H A B g hg, measure_union hd (hBmixed.inter hgm)]
  rw [measure_union_add_inter A hBm, hmass] at hbound
  exact hbound

end Erdos335.Loeb

end
