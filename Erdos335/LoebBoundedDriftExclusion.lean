import Erdos335.DensityMacroscopicIntervals
import Erdos335.LoebCyclicModelMeasures
import Erdos335.LoebCompactHom
import Erdos335.CyclicWindowDensities

/-!
# Excluding a fixed integral drift with a separated interval

Privately checked supporting development.
The geometric separated-interval premise is explicit. It is the remaining
circle-geometry input when a nonzero integral drift is fixed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

private def prefixAnnulus (S : Set ℕ) (L R : ℕ) : Finset ℕ := by
  classical
  exact ((Finset.range R).filter (· ∈ S)) \ ((Finset.range L).filter (· ∈ S))

private def cyclicAnnulus (S : Set ℕ) (q : ℕ+) (L R : ℕ) : Finset (ZMod (q : ℕ)) := by
  classical
  exact (prefixAnnulus S L R).image ((↑) : ℕ → ZMod (q : ℕ))

private theorem mem_prefixAnnulus (S : Set ℕ) (L R k : ℕ) :
    k ∈ prefixAnnulus S L R ↔ k ∈ S ∧ L ≤ k ∧ k < R := by
  classical
  simp only [prefixAnnulus, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨⟨hkR, hkS⟩, hnot⟩
    refine ⟨hkS, ?_, hkR⟩
    by_contra hle
    exact hnot ⟨by omega, hkS⟩
  · rintro ⟨hkS, hkL, hkR⟩
    exact ⟨⟨hkR, hkS⟩, fun h => by omega⟩

private theorem cyclicAnnulus_card (S : Set ℕ) (q : ℕ+) (L R : ℕ)
    (hLR : L ≤ R) (hRq : R ≤ (q : ℕ)) :
    ((cyclicAnnulus S q L R).card : ℝ) =
      (prefixCount S R : ℝ) - (prefixCount S L : ℝ) := by
  classical
  have hsub : ((Finset.range L).filter (· ∈ S)) ⊆ ((Finset.range R).filter (· ∈ S)) := by
    exact Finset.filter_subset_filter _ (Finset.range_mono hLR)
  have hinj : Set.InjOn ((↑) : ℕ → ZMod (q : ℕ)) (prefixAnnulus S L R : Set ℕ) := by
    intro a ha b hb hab
    have haR := (mem_prefixAnnulus S L R a).mp ha
    have hbR := (mem_prefixAnnulus S L R b).mp hb
    have hval := congrArg ZMod.val hab
    rwa [ZMod.val_natCast_of_lt (haR.2.2.trans_le hRq),
      ZMod.val_natCast_of_lt (hbR.2.2.trans_le hRq)] at hval
  rw [cyclicAnnulus, Finset.card_image_of_injOn hinj, prefixAnnulus,
    Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]
  rfl

local instance boundedDriftLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_bounded_drift_exclusion_of_separated_interval
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (ell : ℕ+) (B : Set ℕ) (ρ : ℝ)
    (hρ : 0 < ρ) (hB : HasDensity (B ∩ {k : ℕ | (ell : ℕ) ∣ k}) ρ)
    (χ : ∀ n, ZMod (q n : ℕ) →+ AddCircle (1 : ℝ))
    (d : ℤ) (J : Set (AddCircle (1 : ℝ)))
    (hmodel : internalSet U
      (fun n => (cyclicWindow B 0 (q n : ℕ) : Set (ZMod (q n : ℕ))))
        =ᵐ[loebMeasure U hU] (ultralimitAddHom U χ) ⁻¹' J)
    (hχ : ∀ᶠ n in U, ∀ k ∈ B, (ell : ℕ) ∣ k → k < (q n : ℕ) →
      χ n (k : ZMod (q n : ℕ)) =
        (((d : ℝ) * (k : ℝ) / (q n : ℕ) : ℝ) : AddCircle (1 : ℝ)))
    (u α β v η : ℝ) (hu : 0 ≤ u) (huα : u < α) (hαβ : α < β)
    (hβv : β < v) (hv : v ≤ 1) (hη : 0 < η)
    (hsep : ∀ t ∈ Icc u v, η ≤ Metric.infDist
      ((((d : ℝ) * t : ℝ)) : AddCircle (1 : ℝ)) J) : False := by
  classical
  let S := B ∩ {k : ℕ | (ell : ℕ) ∣ k}
  let L : ℕ → ℕ := fun n => Nat.floor (α * ((q n : ℕ) : ℝ))
  let R : ℕ → ℕ := fun n => Nat.floor (β * ((q n : ℕ) : ℝ))
  let F : ∀ n, Finset (ZMod (q n : ℕ)) := fun n => cyclicAnnulus S (q n) (L n) (R n)
  let C := internalSet U (fun n => (F n : Set (ZMod (q n : ℕ))))
  let B₀ := internalSet U (fun n => (cyclicWindow B 0 (q n : ℕ) : Set (ZMod (q n : ℕ))))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have hα : 0 ≤ α := (hu.trans_lt huα).le
  have hβ : 0 ≤ β := hα.trans hαβ.le
  have hβone : β ≤ 1 := hβv.le.trans hv
  have hLR (n : ℕ) : L n ≤ R n := by
    exact Nat.floor_mono (mul_le_mul_of_nonneg_right hαβ.le (by positivity))
  have hRq (n : ℕ) : R n ≤ (q n : ℕ) := by
    have hfloor : (R n : ℝ) ≤ β * ((q n : ℕ) : ℝ) := Nat.floor_le (by positivity)
    have hreal : (R n : ℝ) ≤ ((q n : ℕ) : ℝ) := by
      calc
        (R n : ℝ) ≤ β * ((q n : ℕ) : ℝ) := hfloor
        _ ≤ 1 * ((q n : ℕ) : ℝ) := mul_le_mul_of_nonneg_right hβone (by positivity)
        _ = _ := one_mul _
    exact_mod_cast hreal
  have hcounts : Tendsto (fun n => ((F n).card : ℝ) / (q n : ℕ))
      atTop (𝓝 (ρ * (β - α))) := by
    have hlim := hB.macroscopic_interval_pnat_tendsto q hq α β hα hαβ.le
    apply hlim.congr
    intro n
    rw [cyclicAnnulus_card S (q n) (L n) (R n) (hLR n) (hRq n)]
  have hmass : (μ C).toReal = ρ * (β - α) := loeb_finset_measure_eq U hU q F _ hcounts
  have hCsub : C ⊆ B₀ := by
    apply (internalSet_subset_iff U _ _).mpr
    exact Eventually.of_forall fun n x hx => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      have hk' := (mem_prefixAnnulus S (L n) (R n) k).mp hk
      have hkq : k < (q n : ℕ) := hk'.2.2.trans_le (hRq n)
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa only [zero_add, ZMod.val_natCast_of_lt hkq] using hk'.1.1
  have hqR : Tendsto (fun n => ((q n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hq
  have hLratio : Tendsto (fun n => (L n : ℝ) / (q n : ℕ)) atTop (𝓝 α) := by
    simpa only [L, Function.comp_def] using (tendsto_nat_floor_mul_div_atTop hα).comp hqR
  have hLlower : ∀ᶠ n in U, u < (L n : ℝ) / (q n : ℕ) :=
    (hLratio.mono_left hU).eventually (lt_mem_nhds huα)
  have haway : C ⊆ ((ultralimitAddHom U χ) ⁻¹' J)ᶜ := by
    intro x hx
    induction x using Quotient.inductionOn with
    | h f =>
      have hfinite : ∀ᶠ n in U, η ≤ Metric.infDist (χ n (f n)) J := by
        filter_upwards [hx, hχ, hLlower] with n hn hχn hLn
        obtain ⟨k, hk, hkf⟩ := Finset.mem_image.mp hn
        have hk' := (mem_prefixAnnulus S (L n) (R n) k).mp hk
        have hkq : k < (q n : ℕ) := hk'.2.2.trans_le (hRq n)
        have hqpos : (0 : ℝ) < (q n : ℕ) := by exact_mod_cast (q n).pos
        have hkreal : (L n : ℝ) ≤ k := by exact_mod_cast hk'.2.1
        have hlower : u ≤ (k : ℝ) / (q n : ℕ) :=
          hLn.le.trans (div_le_div_of_nonneg_right hkreal hqpos.le)
        have hupper : (k : ℝ) / (q n : ℕ) ≤ v := by
          have hkR : (k : ℝ) ≤ R n := by exact_mod_cast hk'.2.2.le
          have hfloor : (R n : ℝ) ≤ β * ((q n : ℕ) : ℝ) := Nat.floor_le (by positivity)
          have hkb : (k : ℝ) / (q n : ℕ) ≤ β := (div_le_iff₀ hqpos).mpr (hkR.trans hfloor)
          exact hkb.trans hβv.le
        rw [← hkf, hχn k hk'.1.1 hk'.1.2 hkq]
        simpa only [mul_div_assoc] using hsep ((k : ℝ) / (q n : ℕ)) ⟨hlower, hupper⟩
      have hlim := (Metric.continuous_infDist_pt J).tendsto
        (ultralimitAddHom U χ (f : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
      have hbound : η ≤ Metric.infDist
          (ultralimitAddHom U χ (f : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) J :=
        ge_of_tendsto (hlim.comp (tendsto_ultralimitFunction U (fun n => χ n) f)) hfinite
      intro hmem
      change ultralimitAddHom U χ
        (f : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) ∈ J at hmem
      rw [Metric.infDist_zero_of_mem hmem] at hbound
      exact (not_le_of_gt hη) hbound
  have hzero : μ C = 0 := by
    have hnull : μ (B₀ \ ((ultralimitAddHom U χ) ⁻¹' J)) = 0 := ae_le_set.mp hmodel.le
    have hsubset : C ⊆ B₀ \ ((ultralimitAddHom U χ) ⁻¹' J) :=
      fun x hx => ⟨hCsub hx, haway hx⟩
    exact measure_mono_null hsubset hnull
  rw [hzero, ENNReal.toReal_zero] at hmass
  have hpositive : 0 < ρ * (β - α) := mul_pos hρ (sub_pos.mpr hαβ)
  exact (ne_of_gt hpositive) hmass.symm

end Erdos335.Loeb

end
