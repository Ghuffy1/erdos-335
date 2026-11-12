import Erdos335.PeriodicRefinementMacroAssembly

/-!
# Totalizing almost-everywhere finite profile data

Private proof development. Verification status is recorded separately. A genuine profile at one positive good
time supplies the fallback. All three raw coordinate vectors are preserved
at almost every positive time.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Filter Set Topology MeasureTheory
open MeasureTheory.Measure
open Erdos335.PeriodicRefinementLabelClosure
open scoped Pointwise BigOperators NNReal

noncomputable section

namespace Erdos335.PeriodicRefinementMacroAssembly

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

structure RawProfileValid (R S : Finset G) (a b : ℝ) (L B C : G → ℝ) : Prop where
  left_bound : ∀ r, 0 ≤ L r ∧ L r ≤ 1
  right_bound : ∀ r, 0 ≤ B r ∧ B r ≤ 1
  output_bound : ∀ r, 0 ≤ C r ∧ C r ≤ 1
  left_zero : ∀ r ∉ R, L r = 0
  right_zero : ∀ r ∉ S, B r = 0
  left_mass : (∑ r, L r) = a
  right_mass : (∑ r, B r) = b
  output_mass : (∑ r, C r) = a + b
  literal_left : ∀ r, ∀ v ∈ S, L r ≤ C (r + v)
  literal_right : ∀ r ∈ R, ∀ v, B v ≤ C (r + v)

def RawProfileValid.toLocalProfile {R S : Finset G} {a b : ℝ} {L B C : G → ℝ}
    (h : RawProfileValid R S a b L B C) : LocalProfile R S a b where
  left := L
  right := B
  output := C
  left_bound := h.left_bound
  right_bound := h.right_bound
  output_bound := h.output_bound
  left_zero := h.left_zero
  right_zero := h.right_zero
  left_mass := h.left_mass
  right_mass := h.right_mass
  output_mass := h.output_mass
  literal_left := h.literal_left
  literal_right := h.literal_right

private theorem measurableSet_forall_index {I : Type*} [Countable I]
    (P : ℝ → I → Prop) (hP : ∀ i, MeasurableSet {t | P t i}) :
    MeasurableSet {t | ∀ i, P t i} := by
  have heq : {t | ∀ i, P t i} = ⋂ i, {t | P t i} := by ext t; simp
  rw [heq]
  exact MeasurableSet.iInter hP

theorem measurableSet_rawProfileValid
    (R S : Finset G) (a b : ℝ) (L B C : ℝ → G → ℝ)
    (hL : ∀ r, Measurable (fun t => L t r))
    (hB : ∀ r, Measurable (fun t => B t r))
    (hC : ∀ r, Measurable (fun t => C t r)) :
    MeasurableSet {t | RawProfileValid R S a b (L t) (B t) (C t)} := by
  have hleft := measurableSet_forall_index (fun t r => 0 ≤ L t r ∧ L t r ≤ 1)
    (fun r => (measurableSet_le measurable_const (hL r)).inter
      (measurableSet_le (hL r) measurable_const))
  have hright := measurableSet_forall_index (fun t r => 0 ≤ B t r ∧ B t r ≤ 1)
    (fun r => (measurableSet_le measurable_const (hB r)).inter
      (measurableSet_le (hB r) measurable_const))
  have houtput := measurableSet_forall_index (fun t r => 0 ≤ C t r ∧ C t r ≤ 1)
    (fun r => (measurableSet_le measurable_const (hC r)).inter
      (measurableSet_le (hC r) measurable_const))
  have hleftzero : MeasurableSet {t | ∀ r ∉ R, L t r = 0} := by
    apply measurableSet_forall_index
    intro r
    by_cases hr : r ∈ R
    · simp [hr]
    · simpa only [hr, not_false_eq_true, true_implies] using
        measurableSet_eq_fun (hL r) measurable_const
  have hrightzero : MeasurableSet {t | ∀ r ∉ S, B t r = 0} := by
    apply measurableSet_forall_index
    intro r
    by_cases hr : r ∈ S
    · simp [hr]
    · simpa only [hr, not_false_eq_true, true_implies] using
        measurableSet_eq_fun (hB r) measurable_const
  have hsumL : Measurable (fun t => ∑ r, L t r) :=
    Finset.univ.measurable_sum (fun r _ => hL r)
  have hsumB : Measurable (fun t => ∑ r, B t r) :=
    Finset.univ.measurable_sum (fun r _ => hB r)
  have hsumC : Measurable (fun t => ∑ r, C t r) :=
    Finset.univ.measurable_sum (fun r _ => hC r)
  have hliteralleft : MeasurableSet {t | ∀ r, ∀ v ∈ S, L t r ≤ C t (r + v)} := by
    apply measurableSet_forall_index
    intro r
    apply measurableSet_forall_index
    intro v
    by_cases hv : v ∈ S
    · simpa only [hv, true_implies] using measurableSet_le (hL r) (hC (r + v))
    · simp [hv]
  have hliteralright : MeasurableSet {t | ∀ r ∈ R, ∀ v, B t v ≤ C t (r + v)} := by
    apply measurableSet_forall_index
    intro r
    by_cases hr : r ∈ R
    · simpa only [hr, true_implies] using measurableSet_forall_index
        (fun t v => B t v ≤ C t (r + v))
        (fun v => measurableSet_le (hB v) (hC (r + v)))
    · simp [hr]
  have heq : {t | RawProfileValid R S a b (L t) (B t) (C t)} =
      {t | (∀ r, 0 ≤ L t r ∧ L t r ≤ 1) ∧
        (∀ r, 0 ≤ B t r ∧ B t r ≤ 1) ∧
        (∀ r, 0 ≤ C t r ∧ C t r ≤ 1) ∧
        (∀ r ∉ R, L t r = 0) ∧ (∀ r ∉ S, B t r = 0) ∧
        (∑ r, L t r) = a ∧ (∑ r, B t r) = b ∧ (∑ r, C t r) = a + b ∧
        (∀ r, ∀ v ∈ S, L t r ≤ C t (r + v)) ∧
        (∀ r ∈ R, ∀ v, B t v ≤ C t (r + v))} := by
    ext t
    constructor
    · intro h
      exact ⟨h.left_bound, h.right_bound, h.output_bound, h.left_zero, h.right_zero,
        h.left_mass, h.right_mass, h.output_mass, h.literal_left, h.literal_right⟩
    · rintro ⟨hleft, hright, houtput, hleftzero, hrightzero,
        hleftmass, hrightmass, houtputmass, hliteralleft, hliteralright⟩
      exact ⟨hleft, hright, houtput, hleftzero, hrightzero,
        hleftmass, hrightmass, houtputmass, hliteralleft, hliteralright⟩
  rw [heq]
  exact hleft.inter (hright.inter (houtput.inter (hleftzero.inter (hrightzero.inter
    ((measurableSet_eq_fun hsumL measurable_const).inter
      ((measurableSet_eq_fun hsumB measurable_const).inter
        ((measurableSet_eq_fun hsumC measurable_const).inter
          (hliteralleft.inter hliteralright))))))))

theorem exists_totalized_profile
    (R S : Finset G) (a b : ℝ) (L B C : ℝ → G → ℝ)
    (hL : ∀ r, Measurable (fun t => L t r))
    (hB : ∀ r, Measurable (fun t => B t r))
    (hC : ∀ r, Measurable (fun t => C t r))
    (hvalid : ∀ᵐ t : ℝ, 0 < t → RawProfileValid R S a b (L t) (B t) (C t)) :
    ∃ p : ℝ → LocalProfile R S a b,
      (∀ r, Measurable (fun t => (p t).left r)) ∧
      (∀ r, Measurable (fun t => (p t).right r)) ∧
      (∀ r, Measurable (fun t => (p t).output r)) ∧
      (∀ᵐ t : ℝ, 0 < t →
        (p t).left = L t ∧ (p t).right = B t ∧ (p t).output = C t) := by
  classical
  have hunit : volume (Ioo (0 : ℝ) 1) ≠ 0 := by simp
  obtain ⟨t₀, ht₀, ht₀valid⟩ := exists_mem_of_measure_ne_zero_of_ae hunit
    (ae_restrict_of_ae hvalid)
  let fallback := (ht₀valid ht₀.1).toLocalProfile
  let good : Set ℝ := {t | 0 < t ∧ RawProfileValid R S a b (L t) (B t) (C t)}
  have hgood : MeasurableSet good :=
    measurableSet_Ioi.inter (measurableSet_rawProfileValid R S a b L B C hL hB hC)
  let p : ℝ → LocalProfile R S a b :=
    fun t => if ht : t ∈ good then ht.2.toLocalProfile else fallback
  refine ⟨p, ?_, ?_, ?_, ?_⟩
  · intro r
    have hm : Measurable (fun t : ℝ => if t ∈ good then L t r else fallback.left r) :=
      Measurable.ite hgood (hL r) measurable_const
    convert hm using 1
    funext t
    by_cases ht : t ∈ good <;> simp [p, ht, RawProfileValid.toLocalProfile]
  · intro r
    have hm : Measurable (fun t : ℝ => if t ∈ good then B t r else fallback.right r) :=
      Measurable.ite hgood (hB r) measurable_const
    convert hm using 1
    funext t
    by_cases ht : t ∈ good <;> simp [p, ht, RawProfileValid.toLocalProfile]
  · intro r
    have hm : Measurable (fun t : ℝ => if t ∈ good then C t r else fallback.output r) :=
      Measurable.ite hgood (hC r) measurable_const
    convert hm using 1
    funext t
    by_cases ht : t ∈ good <;> simp [p, ht, RawProfileValid.toLocalProfile]
  · filter_upwards [hvalid] with t ht hpos
    have htg : t ∈ good := ⟨hpos, ht hpos⟩
    simp [p, htg, RawProfileValid.toLocalProfile]

theorem localProfile_ext {R S : Finset G} {a b : ℝ}
    (p q : LocalProfile R S a b)
    (hleft : p.left = q.left) (hright : p.right = q.right) (houtput : p.output = q.output) :
    p = q := by
  cases p
  cases q
  cases hleft
  cases hright
  cases houtput
  rfl

def RawCrossInequality (L B C : ℝ → G → ℝ) (t u : ℝ) : Prop :=
  ∀ r v, 0 < L t r → 0 < B u v → max (L t r) (B u v) ≤ C (t + u) (r + v)

theorem cross_of_ae_raw_coordinates {R S : Finset G} {a b : ℝ}
    (p : ℝ → LocalProfile R S a b) (L B C : ℝ → G → ℝ)
    (hagree : ∀ᵐ t : ℝ, 0 < t →
      (p t).left = L t ∧ (p t).right = B t ∧ (p t).output = C t)
    (hcross : ∀ᵐ w : ℝ × ℝ ∂volume.prod volume,
      0 < w.1 → 0 < w.2 → RawCrossInequality L B C w.1 w.2) :
    ∀ᵐ w : ℝ × ℝ ∂volume.prod volume,
      0 < w.1 → 0 < w.2 → CrossInequality (p w.1) (p w.2) (p (w.1 + w.2)) := by
  have hfst := (quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ))).ae hagree
  have hsnd := (quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ))).ae hagree
  have hsum := (quasiMeasurePreserving_add (volume : Measure ℝ) (volume : Measure ℝ)).ae hagree
  filter_upwards [hfst, hsnd, hsum, hcross] with w hfirst hsecond htarget hraw ht hu
  have hleft := (hfirst ht).1
  have hright := (hsecond hu).2.1
  have houtput := (htarget (add_pos ht hu)).2.2
  dsimp only [CrossInequality]
  rw [hleft, hright, houtput]
  exact hraw ht hu

def RawFramedAt (R S : Finset G) (a b : ℝ) (L B C : ℝ → G → ℝ) (t : ℝ) : Prop :=
  ∃ h : RawProfileValid R S a b (L t) (B t) (C t),
    ∃ label, HasLabel h.toLocalProfile label ∧ LabelFrame h.toLocalProfile label

theorem frames_of_ae_raw_coordinates {R S : Finset G} {a b : ℝ}
    (p : ℝ → LocalProfile R S a b) (L B C : ℝ → G → ℝ)
    (hagree : ∀ᵐ t : ℝ, 0 < t →
      (p t).left = L t ∧ (p t).right = B t ∧ (p t).output = C t)
    (hframes : ∀ᵐ t : ℝ, 0 < t → RawFramedAt R S a b L B C t) :
    ∀ᵐ t : ℝ, 0 < t → ∃ label, HasLabel (p t) label ∧ LabelFrame (p t) label := by
  filter_upwards [hagree, hframes] with t ht hf hpos
  obtain ⟨hvalid, label, hlabel, hframe⟩ := hf hpos
  have heq : p t = hvalid.toLocalProfile :=
    localProfile_ext (p t) hvalid.toLocalProfile (ht hpos).1 (ht hpos).2.1 (ht hpos).2.2
  rw [heq]
  exact ⟨label, hlabel, hframe⟩

structure RawMacroProfileData (R S : Finset G) (a b : ℝ) where
  leftCumulative : G → ℝ → ℝ
  rightCumulative : G → ℝ → ℝ
  leftLipschitzConstant : ℝ≥0
  rightLipschitzConstant : ℝ≥0
  leftLipschitz : ∀ r, LipschitzWith leftLipschitzConstant (leftCumulative r)
  rightLipschitz : ∀ r, LipschitzWith rightLipschitzConstant (rightCumulative r)
  leftZero : ∀ r, leftCumulative r 0 = 0
  rightZero : ∀ r, rightCumulative r 0 = 0
  rawLeft : ℝ → G → ℝ
  rawRight : ℝ → G → ℝ
  rawOutput : ℝ → G → ℝ
  leftMeasurable : ∀ r, Measurable (fun t => rawLeft t r)
  rightMeasurable : ∀ r, Measurable (fun t => rawRight t r)
  outputMeasurable : ∀ r, Measurable (fun t => rawOutput t r)
  leftDerivative : ∀ᵐ t : ℝ, 0 < t → ∀ r, deriv (leftCumulative r) t = rawLeft t r
  rightDerivative : ∀ᵐ t : ℝ, 0 < t → ∀ r, deriv (rightCumulative r) t = rawRight t r
  frames : ∀ᵐ t : ℝ, 0 < t → RawFramedAt R S a b rawLeft rawRight rawOutput t
  cross : ∀ᵐ w : ℝ × ℝ ∂volume.prod volume,
    0 < w.1 → 0 < w.2 → RawCrossInequality rawLeft rawRight rawOutput w.1 w.2

def RawMacroProfileData.endpoint {R S : Finset G} {a b : ℝ}
    (d : RawMacroProfileData R S a b) : ProfilePair G :=
  (fun r => d.leftCumulative r 1, fun r => d.rightCumulative r 1)

theorem RawMacroProfileData.totalize {R S : Finset G} {a b : ℝ}
    (d : RawMacroProfileData R S a b) :
    ∃ p : MacroProfileData R S a b,
      p.leftCumulative = d.leftCumulative ∧ p.rightCumulative = d.rightCumulative ∧
      (∀ r, Measurable (fun t => (p.profile t).output r)) ∧
      (∀ᵐ t : ℝ, 0 < t → (p.profile t).left = d.rawLeft t ∧
        (p.profile t).right = d.rawRight t ∧ (p.profile t).output = d.rawOutput t) := by
  have hvalid : ∀ᵐ t : ℝ, 0 < t →
      RawProfileValid R S a b (d.rawLeft t) (d.rawRight t) (d.rawOutput t) := by
    filter_upwards [d.frames] with t ht hpos
    exact (ht hpos).choose
  obtain ⟨p, hleft, hright, houtput, hagree⟩ := exists_totalized_profile R S a b
    d.rawLeft d.rawRight d.rawOutput d.leftMeasurable d.rightMeasurable d.outputMeasurable hvalid
  let total : MacroProfileData R S a b := {
    leftCumulative := d.leftCumulative
    rightCumulative := d.rightCumulative
    leftLipschitzConstant := d.leftLipschitzConstant
    rightLipschitzConstant := d.rightLipschitzConstant
    leftLipschitz := d.leftLipschitz
    rightLipschitz := d.rightLipschitz
    leftZero := d.leftZero
    rightZero := d.rightZero
    profile := p
    leftMeasurable := hleft
    rightMeasurable := hright
    leftDerivative := by
      filter_upwards [d.leftDerivative, hagree] with t ht hp hpos
      intro r
      exact (ht hpos r).trans (congrFun (hp hpos).1 r).symm
    rightDerivative := by
      filter_upwards [d.rightDerivative, hagree] with t ht hp hpos
      intro r
      exact (ht hpos r).trans (congrFun (hp hpos).2.1 r).symm
    frames := frames_of_ae_raw_coordinates p d.rawLeft d.rawRight d.rawOutput hagree d.frames
    cross := cross_of_ae_raw_coordinates p d.rawLeft d.rawRight d.rawOutput hagree d.cross
  }
  exact ⟨total, rfl, rfl, houtput, hagree⟩

theorem RawMacroProfileData.exists_endpoint_slice {R S : Finset G} {a b : ℝ}
    (d : RawMacroProfileData R S a b)
    (ha : 0 < a) (hb : 0 < b) (hgap : a + b < ((R + S).card : ℝ)) :
    ∃ label, d.endpoint ∈ periodicInputSlice R S a b label := by
  obtain ⟨total, hleft, hright, _, _⟩ := d.totalize
  obtain ⟨label, hlabel⟩ := total.exists_endpoint_slice ha hb hgap
  refine ⟨label, ?_⟩
  simpa only [MacroProfileData.endpoint, RawMacroProfileData.endpoint, hleft, hright] using hlabel

theorem exists_periodic_coordinate_limit_of_raw_cluster_profiles
    {R S : Finset G} {a b : ℝ}
    (u : ℕ → ProfilePair G) (K : Set (ProfilePair G))
    (ha : 0 < a) (hb : 0 < b) (hgap : a + b < ((R + S).card : ℝ))
    (hK : IsCompact K) (hmem : ∀ᶠ n in atTop, u n ∈ K)
    (hstep : Tendsto (fun n => dist (u (n + 1)) (u n)) atTop (𝓝 0))
    (hmacro : ∀ v, MapClusterPt v atTop u →
      ∃ d : RawMacroProfileData R S a b, d.endpoint = v)
    (hprefix : ∀ v, MapClusterPt v atTop u →
      ∃ p : LocalProfile R S a b, p.left = v.1 ∧ p.right = v.2) :
    (∃ P : Finset G, Tendsto (fun n => (u n).1) atTop (𝓝 (maskVector P))) ∨
      (∃ Q : Finset G, Tendsto (fun n => (u n).2) atTop (𝓝 (maskVector Q))) := by
  apply exists_periodic_coordinate_limit_of_cluster_profiles
    u K ha hb hgap hK hmem hstep ?_ hprefix
  intro v hv
  obtain ⟨raw, hraw⟩ := hmacro v hv
  obtain ⟨total, hleft, hright, _, _⟩ := raw.totalize
  refine ⟨total, ?_⟩
  simpa only [MacroProfileData.endpoint, RawMacroProfileData.endpoint, hleft, hright] using hraw

end Erdos335.PeriodicRefinementMacroAssembly

end
