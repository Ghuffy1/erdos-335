import Erdos335.HighGapDenseStartExclusion
import Erdos335.FourierModelSubsequence

/-!
# Vanishing proportions of bad starts in the High branch

Private proof development. Verification status is recorded separately. A strict subsequence restricts the supplied
scales and both Fourier witnesses together. Dense-start exclusion then
applies to those same restricted data.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

theorem high_gap_bad_start_fraction_tendsto_zero
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A B : Set ℕ) (a b δA δB : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hAdensity : HasDensity A a) (hBdensity : HasDensity B b)
    (hCdensity : HasDensity (A + B) (a + b))
    (hgap : a + b < gamma A B)
    (hhighA : gamma A B < a + b + δA)
    (hhighB : gamma A B < a + b + δB)
    (hcapA : ∀ h : ℕ+, a + δA ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ))
    (hcapB : ∀ h : ℕ+, b + δB ≤ ((residues (h : ℕ) B).card : ℝ) / (h : ℕ))
    (N L V H : ℕ → ℕ) (hN : ∀ s, 0 < N s)
    (hLpos : ∀ s, 0 < L s) (hVpos : ∀ s, 0 < V s)
    (hL : Tendsto L atTop atTop)
    (hLV : Tendsto (fun s => (L s : ℝ) / V s) atTop (𝓝 0))
    (hHpos : ∀ s, 0 < H s) (hH : Tendsto H atTop atTop)
    (hLH : Tendsto (fun s => (L s : ℝ) / H s) atTop (𝓝 0))
    (hHV : Tendsto (fun s => (H s : ℝ) / V s) atTop (𝓝 0))
    (hHN : Tendsto (fun s => (H s : ℝ) / N s) atTop (𝓝 0))
    (mA : IntermediateFourierModel (A.indicator (fun _ => (1 : ℝ))) N L V)
    (mB : IntermediateFourierModel (B.indicator (fun _ => (1 : ℝ))) N L V)
    (hAerror : Tendsto (fun s => prefixError A a (N s) / H s) atTop (𝓝 0))
    (hBerror : Tendsto (fun s => prefixError B b (N s) / H s) atTop (𝓝 0))
    (hCerror : Tendsto (fun s => prefixError (A + B) (a + b) (N s) / H s)
      atTop (𝓝 0))
    (M : ℕ+)
    (hM : ∀ h : ℕ+, ((h : ℕ) : ℝ) * (gamma A B - (a + b)) < 1 →
      (h : ℕ) ∣ (M : ℕ))
    (vA vB : ZMod (M : ℕ) → ℝ)
    (hprefixA : ∀ r, Tendsto (fun s => ((M : ℕ) : ℝ) *
      ((prefixCount {k : ℕ | k ∈ A ∧ (k : ZMod (M : ℕ)) = r} (H s) : ℝ) / H s))
        atTop (𝓝 (vA r)))
    (hprefixB : ∀ r, Tendsto (fun s => ((M : ℕ) : ℝ) *
      ((prefixCount {k : ℕ | k ∈ B ∧ (k : ZMod (M : ℕ)) = r} (H s) : ℝ) / H s))
        atTop (𝓝 (vB r)))
    (side : Bool) (r : ZMod (M : ℕ)) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun s =>
      (((Finset.range (N s)).filter (fun n => ε ≤
        |((M : ℕ) : ℝ) *
          (((@cyclicWindow
            {k : ℕ | k ∈ (if side then B else A) ∧ (k : ZMod (M : ℕ)) = r}
            (n + 3 * H s) (H s) ⟨(hHpos s).ne'⟩).card : ℝ) / H s) -
              (if side then vB r else vA r)|)).card : ℝ) / N s)
        atTop (𝓝 0) := by
  classical
  letI (s : ℕ) : NeZero (H s) := ⟨(hHpos s).ne'⟩
  let S : ℕ → Finset ℕ := fun s => (Finset.range (N s)).filter (fun n => ε ≤
    |((M : ℕ) : ℝ) *
      (((cyclicWindow
        {k : ℕ | k ∈ (if side then B else A) ∧ (k : ZMod (M : ℕ)) = r}
        (n + 3 * H s) (H s)).card : ℝ) / H s) -
          (if side then vB r else vA r)|)
  change Tendsto (fun s => ((S s).card : ℝ) / N s) atTop (𝓝 0)
  apply tendsto_order.mpr
  constructor
  · intro c hc
    exact Eventually.of_forall (fun s => hc.trans_le (by positivity))
  · intro δ hδ
    by_contra hnot
    have hfrequent : ∃ᶠ s in atTop, δ ≤ ((S s).card : ℝ) / N s := by
      simpa only [not_lt] using Filter.not_eventually.mp hnot
    obtain ⟨σ, hσ, hlarge⟩ := extraction_of_frequently_atTop hfrequent
    have hcard : ∀ᶠ s in atTop, δ ≤ ((S (σ s)).card : ℝ) / N (σ s) :=
      Eventually.of_forall hlarge
    exact high_gap_dense_start_exclusion U hU A B a b δA δB ha hb
      hAdensity hBdensity hCdensity hgap hhighA hhighB hcapA hcapB
        (N ∘ σ) (L ∘ σ) (V ∘ σ) (H ∘ σ) (fun s => hN (σ s))
          (fun s => hHpos (σ s)) (hH.comp hσ.tendsto_atTop)
            (hLH.comp hσ.tendsto_atTop) (hHV.comp hσ.tendsto_atTop)
              (hHN.comp hσ.tendsto_atTop)
                (mA.subsequence hLpos hVpos hL hLV σ hσ)
                (mB.subsequence hLpos hVpos hL hLV σ hσ)
                (hAerror.comp hσ.tendsto_atTop) (hBerror.comp hσ.tendsto_atTop)
                  (hCerror.comp hσ.tendsto_atTop) M hM vA vB
                    (fun t => (hprefixA t).comp hσ.tendsto_atTop)
                    (fun t => (hprefixB t).comp hσ.tendsto_atTop)
                      (S ∘ σ) (fun s => Finset.filter_subset _ _) δ hδ hcard side r ε hε
                        (fun s n hn => (Finset.mem_filter.mp hn).2)

end Erdos335.Loeb

end
