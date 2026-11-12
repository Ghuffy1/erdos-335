import Erdos335.HighGapBadStartFractions
import Erdos335.FiniteBadSetAverages
import Erdos335.WindowProfileAveraging

/-!
# Macro prefix profiles from the fixed High-branch window scale

Private proof development. Verification status is recorded separately. Averaging uses the function M times the
indicator of a literal residue section, bounded between zero and M.
The shift is 3H and its boundary error tends to zero with H/N.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal BigOperators

noncomputable section

namespace Erdos335.Loeb

private theorem prefix_profile_tendsto_of_bad_fractions
    (T : Set ℕ) (M : ℕ+) (N H : ℕ → ℕ)
    (hN : ∀ s, 0 < N s) (hH : ∀ s, 0 < H s)
    (hHN : Tendsto (fun s => (H s : ℝ) / N s) atTop (𝓝 0))
    (v : ℝ)
    (hbad : ∀ ε : ℝ, 0 < ε → Tendsto (fun s =>
      (((Finset.range (N s)).filter (fun n => ε ≤
        |((M : ℕ) : ℝ) *
          (((@cyclicWindow T (n + 3 * H s) (H s) ⟨(hH s).ne'⟩).card : ℝ) / H s) - v|)).card : ℝ) /
            N s) atTop (𝓝 0)) :
    Tendsto (fun s => ((M : ℕ) : ℝ) * ((prefixCount T (N s) : ℝ) / N s))
      atTop (𝓝 v) := by
  classical
  letI (s : ℕ) : NeZero (H s) := ⟨(hH s).ne'⟩
  let f : ℕ → ℝ := T.indicator (fun _ => ((M : ℕ) : ℝ))
  have hf : ∀ k, f k ∈ Set.Icc (0 : ℝ) ((M : ℕ) : ℝ) := by
    intro k
    by_cases hk : k ∈ T <;> simp [f, hk]
  have hsum (J K : ℕ) : (∑ i ∈ Finset.range K, f (J + i)) =
      ((M : ℕ) : ℝ) * (prefixCount (tailShift T J) K : ℝ) := by
    calc
      _ = ∑ i ∈ (Finset.range K).filter (fun i => J + i ∈ T), ((M : ℕ) : ℝ) := by
        rw [Finset.sum_filter]
        simp only [f, Set.indicator_apply]
      _ = ((M : ℕ) : ℝ) *
          (((Finset.range K).filter (fun i => J + i ∈ T)).card : ℝ) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
      _ = ((M : ℕ) : ℝ) * (prefixCount (tailShift T J) K : ℝ) := by
        simp only [prefixCount, tailShift, Set.mem_setOf_eq, Nat.add_comm]
  let w : ℕ → ℕ → ℝ := fun s n =>
    (∑ i ∈ Finset.range (H s), f (n + 3 * H s + i)) / H s
  have hw (s n : ℕ) : w s n = ((M : ℕ) : ℝ) *
      (((cyclicWindow T (n + 3 * H s) (H s)).card : ℝ) / H s) := by
    letI : NeZero (H s) := ⟨(hH s).ne'⟩
    dsimp only [w]
    rw [hsum, cyclicWindow_card_eq_prefixCount]
    ring
  have hwbound (s n : ℕ) : w s n ∈ Set.Icc (0 : ℝ) ((M : ℕ) : ℝ) := by
    have hHr : (0 : ℝ) < H s := by exact_mod_cast hH s
    have hlower : (0 : ℝ) ≤ ∑ i ∈ Finset.range (H s), f (n + 3 * H s + i) :=
      Finset.sum_nonneg (fun i _ => (hf _).1)
    have hupper : (∑ i ∈ Finset.range (H s), f (n + 3 * H s + i)) ≤
        (H s : ℝ) * ((M : ℕ) : ℝ) := by
      calc
        _ ≤ ∑ _i ∈ Finset.range (H s), ((M : ℕ) : ℝ) :=
          Finset.sum_le_sum (fun i _ => (hf _).2)
        _ = _ := by simp
    refine ⟨div_nonneg hlower hHr.le, (div_le_iff₀ hHr).mpr ?_⟩
    simpa only [mul_comm] using hupper
  let e : ℕ → ℕ → ℝ := fun s n => |w s n - v|
  have he (s n : ℕ) : e s n ∈ Set.Icc (0 : ℝ) (((M : ℕ) : ℝ) + |v|) := by
    refine ⟨abs_nonneg _, ?_⟩
    change |w s n - v| ≤ ((M : ℕ) : ℝ) + |v|
    calc
      _ ≤ |w s n - 0| + |0 - v| := abs_sub_le _ _ _
      _ = w s n + |v| := by
        rw [sub_zero, zero_sub, abs_neg, abs_of_nonneg (hwbound s n).1]
      _ ≤ _ := by linarith [(hwbound s n).2]
  have hbadError : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun s => (((Finset.range (N s)).filter (fun n => ε ≤ e s n)).card : ℝ) /
        N s) atTop (𝓝 0) := by
    intro ε hε
    simpa only [e, hw] using hbad ε hε
  have hmeanError := finite_mean_tendsto_zero_of_bad_fractions e
    (((M : ℕ) : ℝ) + |v|) N hN (fun s n _ => he s n) hbadError
  let avg : ℕ → ℝ := fun s => (∑ n ∈ Finset.range (N s), w s n) / N s
  have haverageBound (s : ℕ) : |avg s - v| ≤
      (∑ n ∈ Finset.range (N s), e s n) / N s := by
    have hNr : (0 : ℝ) < N s := by exact_mod_cast hN s
    have hidentity : avg s - v =
        (∑ n ∈ Finset.range (N s), (w s n - v)) / N s := by
      dsimp only [avg]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [hNr.ne']
      <;> ring
    rw [hidentity, abs_div, abs_of_pos hNr]
    apply div_le_div_of_nonneg_right _ hNr.le
    exact Finset.abs_sum_le_sum_abs (fun n => w s n - v) (Finset.range (N s))
  have havgAbs : Tendsto (fun s => |avg s - v|) atTop (𝓝 0) :=
    squeeze_zero (fun _ => abs_nonneg _) haverageBound hmeanError
  have havg : Tendsto avg atTop (𝓝 v) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [Real.norm_eq_abs] using havgAbs
  have hedge : Tendsto (fun s => ((3 * H s + H s : ℕ) : ℝ) / N s)
      atTop (𝓝 0) := by
    have hscaled := hHN.const_mul 4
    simp only [mul_zero] at hscaled
    apply hscaled.congr
    intro s
    push_cast
    ring
  have hmacro := prefix_mean_tendsto_of_offset_window_means f ((M : ℕ) : ℝ) v hf
    N (fun s => 3 * H s) H hN hH hedge havg
  have hprefix (s : ℕ) : (∑ k ∈ Finset.range (N s), f k) =
      ((M : ℕ) : ℝ) * (prefixCount T (N s) : ℝ) := by
    have hzero : tailShift T 0 = T := by
      ext k
      simp [tailShift]
    simpa only [zero_add, hzero] using hsum 0 (N s)
  apply hmacro.congr
  intro s
  rw [hprefix s]
  ring

theorem high_gap_macro_prefix_profiles
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
        atTop (𝓝 (vB r))) :
    (∀ r, Tendsto (fun s => ((M : ℕ) : ℝ) *
      ((prefixCount {k : ℕ | k ∈ A ∧ (k : ZMod (M : ℕ)) = r} (N s) : ℝ) / N s))
        atTop (𝓝 (vA r))) ∧
    (∀ r, Tendsto (fun s => ((M : ℕ) : ℝ) *
      ((prefixCount {k : ℕ | k ∈ B ∧ (k : ZMod (M : ℕ)) = r} (N s) : ℝ) / N s))
        atTop (𝓝 (vB r))) := by
  have hbad := high_gap_bad_start_fraction_tendsto_zero U hU A B a b δA δB ha hb
    hAdensity hBdensity hCdensity hgap hhighA hhighB hcapA hcapB N L V H hN
      hLpos hVpos hL hLV hHpos hH hLH hHV hHN mA mB hAerror hBerror hCerror
        M hM vA vB hprefixA hprefixB
  constructor
  · intro r
    apply prefix_profile_tendsto_of_bad_fractions
      {k : ℕ | k ∈ A ∧ (k : ZMod (M : ℕ)) = r} M N H hN hHpos hHN (vA r)
    intro ε hε
    simpa using hbad false r ε hε
  · intro r
    apply prefix_profile_tendsto_of_bad_fractions
      {k : ℕ | k ∈ B ∧ (k : ZMod (M : ℕ)) = r} M N H hN hHpos hHN (vB r)
    intro ε hε
    simpa using hbad true r ε hε

end Erdos335.Loeb

end
