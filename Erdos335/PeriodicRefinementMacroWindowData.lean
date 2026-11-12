import Erdos335.PeriodicRefinementActualMacroWindowsCross
import Erdos335.PeriodicRefinementInputFamily
import Erdos335.PeriodicRefinementLocalWindowLabels
import Erdos335.PeriodicRefinementMacroAssemblyTotalization
import Erdos335.PeriodicRefinementPrefixProfiles
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Actual window schedules and macroscopic profile data

Every scheduled period is attached to a literal physical window.  The
record retains the prefix-error and convolution-error bounds consumed by
the local inverse theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open MeasureTheory.Measure
open Erdos335.IntermediateScale Erdos335.Loeb
open Erdos335.PeriodicRefinementLabelClosure Erdos335.PeriodicRefinementMacroAssembly
open scoped Pointwise NNReal ENNReal BigOperators

noncomputable section

namespace Erdos335.PeriodicRefinement

def macroStart (N H : ℕ → ℕ) (t : ℝ) (n : ℕ) : ℕ :=
  Nat.floor (t * N n) + 3 * H n

theorem selected_length_ratio_of_gap
    (H : ℕ → ℕ) (q : ℕ → ℕ+) (hHq : ∀ n, H n ≤ (q n : ℕ))
    (hgap : Tendsto (fun n => (((q n : ℕ) - H n : ℕ) : ℝ) / (q n : ℕ))
      atTop (𝓝 0)) :
    Tendsto (fun n => ((q n : ℕ) : ℝ) / H n) atTop (𝓝 1) := by
  have hrecip : Tendsto (fun n => (H n : ℝ) / (q n : ℕ)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hgap
    simp only [sub_zero] at h
    apply h.congr
    intro n
    rw [Nat.cast_sub (hHq n)]
    have hqne : ((q n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (q n).ne_zero
    field_simp [hqne]
    ring
  simpa only [inv_div, inv_one] using hrecip.inv₀ (by norm_num : (1 : ℝ) ≠ 0)

structure ScheduledMacroWindow (A B : Set ℕ) (a b : ℝ)
    (N H : ℕ → ℕ) (t : ℝ) where
  enlargement : ℕ+
  parameter_lt : t < (enlargement : ℕ)
  period : Bool → ℕ → ℕ+
  length_lower : ∀ o n, H n ≤ (period o n : ℕ)
  length_ratio : ∀ o, Tendsto (fun n => ((period o n : ℕ) : ℝ) / H n) atTop (𝓝 1)
  divides : ∀ o (k : ℕ+), ∀ᶠ n in atTop, (k : ℕ) ∣ (period o n : ℕ)
  inside : ∀ o, ∀ᶠ n in atTop,
    macroStart N H t n + (period o n : ℕ) ≤ (enlargement : ℕ) * N n
  left_error : Tendsto (fun n => prefixError A a ((enlargement : ℕ) * N n) / H n)
    atTop (𝓝 0)
  right_error : Tendsto (fun n => prefixError B b ((enlargement : ℕ) * N n) / H n)
    atTop (𝓝 0)
  output_error : Tendsto (fun n => prefixError (A + B) (a + b)
    ((enlargement : ℕ) * N n) / H n) atTop (𝓝 0)
  convolution_error : ∀ o, Tendsto (fun n =>
    convolutionTranslationError (if o then B else A) (if o then A else B)
      (macroStart N H t n) (period o n : ℕ) / ((period o n : ℕ) : ℝ) ^ 2)
        atTop (𝓝 0)

structure MacroWindowSequence (A B : Set ℕ) (a b : ℝ) (M : ℕ+) where
  cutoff : ℕ → ℕ
  width : ℕ → ℕ
  cutoff_positive : ∀ n, 0 < cutoff n
  width_positive : ∀ n, 0 < width n
  width_tendsto : Tendsto width atTop atTop
  width_ratio : Tendsto (fun n => (width n : ℝ) / cutoff n) atTop (𝓝 0)
  cumulative : Fin 3 → ZMod (M : ℕ) → C(ℝ, ℝ)
  cumulative_lipschitz : ∀ i r, LipschitzWith 1 (cumulative i r)
  cumulative_zero : ∀ i r, cumulative i r 0 = 0
  approximation : ∀ (L : ℕ+) i r, UniformCumulativeApproximation
    {k : ℕ | k ∈ macroInput A B i ∧ (k : ZMod (M : ℕ)) = r}
    (cumulative i r) cutoff width (L : ℕ)
  windows : ∀ᵐ t : ℝ, 0 < t →
    Nonempty (ScheduledMacroWindow A B a b cutoff width t)

theorem MacroWindowSequence.endpoint_prefix_tendsto
    {A B : Set ℕ} {a b : ℝ} {M : ℕ+} (d : MacroWindowSequence A B a b M)
    (i : Fin 3) (r : ZMod (M : ℕ)) :
    Tendsto (fun n => normalizedResiduePrefix (macroInput A B i) M (d.cutoff n) r)
      atTop (𝓝 (((M : ℕ) : ℝ) * d.cumulative i r 1)) := by
  let approximation := d.approximation (⟨2, by decide⟩ : ℕ+) i r
  have hproduct := approximation.error_small.mul d.width_ratio
  simp only [mul_zero] at hproduct
  have herror : Tendsto approximation.error atTop (𝓝 0) := by
    apply hproduct.congr
    intro n
    have hn : (d.cutoff n : ℝ) ≠ 0 := by exact_mod_cast (d.cutoff_positive n).ne'
    have hh : (d.width n : ℝ) ≠ 0 := by exact_mod_cast (d.width_positive n).ne'
    field_simp [hn, hh]
  have hbound : ∀ᶠ n in atTop,
      |(prefixCount {k : ℕ | k ∈ macroInput A B i ∧ (k : ZMod (M : ℕ)) = r}
        (d.cutoff n) : ℝ) / d.cutoff n - d.cumulative i r 1| ≤ approximation.error n := by
    filter_upwards [approximation.bound] with n hn
    simpa only [one_mul, approximation.agreesOnNaturals] using
      hn 1 (by constructor <;> norm_num)
  have habs := squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) hbound herror
  have hraw : Tendsto (fun n =>
      (prefixCount {k : ℕ | k ∈ macroInput A B i ∧ (k : ZMod (M : ℕ)) = r}
        (d.cutoff n) : ℝ) / d.cutoff n) atTop (𝓝 (d.cumulative i r 1)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [Real.norm_eq_abs] using habs
  simpa only [normalizedResiduePrefix, literalResidue] using hraw.const_mul ((M : ℕ) : ℝ)

theorem lipschitz_const_mul_unit (F : ℝ → ℝ) (hF : LipschitzWith 1 F) (M : ℕ+) :
    LipschitzWith (M : ℕ) (fun t => ((M : ℕ) : ℝ) * F t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := hF.dist_le_mul x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at h
  rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  simpa only [NNReal.coe_natCast, Real.dist_eq] using
    mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ ((M : ℕ) : ℝ) by positivity)

theorem macroWindowSequence_rawData
    (A B : Set ℕ) (a b δA δB : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hδA : 0 < δA) (hδB : 0 < δB)
    (hAdensity : HasDensity A a) (hBdensity : HasDensity B b)
    (hCdensity : HasDensity (A + B) (a + b)) (hgap : a + b < gamma A B)
    (hlowA : ∀ η : ℝ, gamma A B - (a + b) < η →
      ∃ k : ℕ+, ((residues (k : ℕ) A).card : ℝ) / (k : ℕ) < a + η)
    (hcapA : ∀ k : ℕ+, a + δA ≤ ((residues (k : ℕ) A).card : ℝ) / (k : ℕ))
    (hcapB : ∀ k : ℕ+, b + δB ≤ ((residues (k : ℕ) B).card : ℝ) / (k : ℕ))
    (D : ℕ)
    (hD : max (1 / δA) (max (1 / δB) (1 / (gamma A B - (a + b)))) ≤ (D : ℝ))
    (d : MacroWindowSequence A B a b ⟨D.factorial, Nat.factorial_pos D⟩) :
    ∃ raw : RawMacroProfileData (residues D.factorial A) (residues D.factorial B)
        ((D.factorial : ℝ) * a) ((D.factorial : ℝ) * b),
      raw.leftCumulative = (fun r t => (D.factorial : ℝ) * d.cumulative 0 r t) ∧
      raw.rightCumulative = (fun r t => (D.factorial : ℝ) * d.cumulative 1 r t) := by
  classical
  let M : ℕ+ := ⟨D.factorial, Nat.factorial_pos D⟩
  let rawProfile : Fin 3 → ℝ → ZMod D.factorial → ℝ :=
    fun i t r => (D.factorial : ℝ) * deriv (d.cumulative i r) t
  have hM : (0 : ℝ) < D.factorial := by exact_mod_cast Nat.factorial_pos D
  have hdifferentiable : ∀ᵐ t : ℝ, ∀ (i : Fin 3) (r : ZMod D.factorial),
      DifferentiableAt ℝ (d.cumulative i r) t := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro r
    exact (d.cumulative_lipschitz i r).ae_differentiableAt
  have hframes : ∀ᵐ t : ℝ, 0 < t → RawFramedAt
      (residues D.factorial A) (residues D.factorial B)
      ((D.factorial : ℝ) * a) ((D.factorial : ℝ) * b)
      (rawProfile 0) (rawProfile 1) (rawProfile 2) t := by
    filter_upwards [d.windows, hdifferentiable] with t ht hd htpos
    obtain ⟨window⟩ := ht htpos
    let start := macroStart d.cutoff d.width t
    have hshift : ∀ᶠ n in atTop,
        |(start n : ℝ) - (Nat.floor (t * d.cutoff n) : ℝ)| ≤ 3 * d.width n := by
      apply Eventually.of_forall
      intro n
      simp only [start, macroStart, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        add_sub_cancel_left, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 * d.width n)]
      exact le_rfl
    have hprofiles (i : Fin 3) (r : ZMod D.factorial) :
        Tendsto (fun n => (D.factorial : ℝ) *
          (((@cyclicWindow {k : ℕ | k ∈ macroInput A B i ∧ (k : ZMod D.factorial) = r}
            (start n) (d.width n) ⟨(d.width_positive n).ne'⟩).card : ℝ) / d.width n))
          atTop (𝓝 (rawProfile i t r)) := by
      have h := actual_macro_floor_window_density
        {k : ℕ | k ∈ macroInput A B i ∧ (k : ZMod D.factorial) = r}
        (d.cumulative i r) d.cutoff d.width start (window.enlargement : ℕ) t
        (deriv (d.cumulative i r) t) 3 d.cutoff_positive d.width_positive d.width_ratio
        (d.approximation window.enlargement i r) htpos window.parameter_lt
        (hd i r).hasDerivAt hshift
      simpa only [rawProfile, mul_div_assoc] using h.const_mul (D.factorial : ℝ)
    let U : Ultrafilter ℕ := Ultrafilter.of atTop
    have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
    obtain ⟨p, hpA, hpB, hpC, label, hlabel, hframe⟩ :=
      prescribed_small_error_window_has_label A B a b δA δB ha hb hδA hδB
        hAdensity hBdensity hCdensity hgap hlowA hcapA hcapB D hD U hU
        (fun n => (window.enlargement : ℕ) * d.cutoff n) d.width start window.period
        d.width_positive d.width_tendsto window.length_lower window.length_ratio window.divides
        (Eventually.of_forall fun n => by
          dsimp only [start, macroStart]
          have hpos := d.width_positive n
          omega)
        window.inside window.left_error window.right_error window.output_error
        window.convolution_error (rawProfile 0 t) (rawProfile 1 t) (rawProfile 2 t)
        (by simpa [macroInput] using hprofiles 0)
        (by simpa [macroInput] using hprofiles 1)
        (by simpa [macroInput] using hprofiles 2)
    have valid : RawProfileValid (residues D.factorial A) (residues D.factorial B)
        ((D.factorial : ℝ) * a) ((D.factorial : ℝ) * b) p.left p.right p.output :=
      ⟨p.left_bound, p.right_bound, p.output_bound, p.left_zero, p.right_zero,
        p.left_mass, p.right_mass, p.output_mass, p.literal_left, p.literal_right⟩
    rw [hpA, hpB, hpC] at valid
    have heq : valid.toLocalProfile = p := localProfile_ext _ _ hpA.symm hpB.symm hpC.symm
    refine ⟨valid, label, ?_, ?_⟩
    · rwa [heq]
    · rwa [heq]
  have hcross : ∀ᵐ w : ℝ × ℝ ∂volume.prod volume,
      0 < w.1 → 0 < w.2 → RawCrossInequality
        (rawProfile 0) (rawProfile 1) (rawProfile 2) w.1 w.2 := by
    have hfst := (quasiMeasurePreserving_fst (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).ae hdifferentiable
    have hsnd := (quasiMeasurePreserving_snd (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).ae hdifferentiable
    have hsum := (quasiMeasurePreserving_add (volume : Measure ℝ) (volume : Measure ℝ)).ae hdifferentiable
    filter_upwards [hfst, hsnd, hsum] with w ht hu htu htpos hupos
    intro r v hr hv
    obtain ⟨k, hk⟩ := exists_nat_gt (w.1 + w.2)
    have hkpos : 0 < k := by
      have hkr : (0 : ℝ) < k := (add_pos htpos hupos).trans hk
      exact_mod_cast hkr
    let L : ℕ+ := ⟨k, hkpos⟩
    have hrpos : 0 < deriv (d.cumulative 0 r) w.1 :=
      (mul_pos_iff_of_pos_left hM).mp hr
    have hvpos : 0 < deriv (d.cumulative 1 v) w.2 :=
      (mul_pos_iff_of_pos_left hM).mp hv
    have hc := derivative_residue_cross_max A B M r v
      (d.cumulative 0 r) (d.cumulative 1 v) (d.cumulative 2 (r + v))
      d.cutoff d.width k w.1 w.2 _ _ _ d.cutoff_positive d.width_positive d.width_ratio
      (by simpa [macroInput, L] using d.approximation L 0 r)
      (by simpa [macroInput, L] using d.approximation L 1 v)
      (by simpa [macroInput, L] using d.approximation L 2 (r + v))
      htpos hupos hk (ht 0 r).hasDerivAt (hu 1 v).hasDerivAt
      (htu 2 (r + v)).hasDerivAt hrpos hvpos
    exact max_le
      (mul_le_mul_of_nonneg_left ((le_max_left _ _).trans hc) hM.le)
      (mul_le_mul_of_nonneg_left ((le_max_right _ _).trans hc) hM.le)
  refine ⟨{
    leftCumulative := fun r t => (D.factorial : ℝ) * d.cumulative 0 r t
    rightCumulative := fun r t => (D.factorial : ℝ) * d.cumulative 1 r t
    leftLipschitzConstant := D.factorial
    rightLipschitzConstant := D.factorial
    leftLipschitz := fun r => lipschitz_const_mul_unit _ (d.cumulative_lipschitz 0 r) M
    rightLipschitz := fun r => lipschitz_const_mul_unit _ (d.cumulative_lipschitz 1 r) M
    leftZero := by intro r; rw [d.cumulative_zero]; ring
    rightZero := by intro r; rw [d.cumulative_zero]; ring
    rawLeft := rawProfile 0
    rawRight := rawProfile 1
    rawOutput := rawProfile 2
    leftMeasurable := fun r => measurable_const.mul (measurable_deriv _)
    rightMeasurable := fun r => measurable_const.mul (measurable_deriv _)
    outputMeasurable := fun r => measurable_const.mul (measurable_deriv _)
    leftDerivative := ?_
    rightDerivative := ?_
    frames := hframes
    cross := hcross
  }, rfl, rfl⟩
  · filter_upwards [hdifferentiable] with t ht _
    intro r
    exact ((ht 0 r).hasDerivAt.const_mul (D.factorial : ℝ)).deriv
  · filter_upwards [hdifferentiable] with t ht _
    intro r
    exact ((ht 1 r).hasDerivAt.const_mul (D.factorial : ℝ)).deriv

end Erdos335.PeriodicRefinement

end
