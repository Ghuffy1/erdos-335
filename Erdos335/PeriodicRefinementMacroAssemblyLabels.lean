import Erdos335.PeriodicRefinementGlobalMeasure
import Erdos335.PeriodicRefinementLabelClosure
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Measurable periodic-profile labels and their closed endpoint slices

Private proof development. Verification status is recorded separately. Profile coordinates are measurable
functions of time. The local profile record retains its finite mass and
literal-translation conditions.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

open Filter Set Topology MeasureTheory
open Erdos335.PeriodicRefinementLabelClosure
open scoped Pointwise BigOperators

noncomputable section

namespace Erdos335.PeriodicRefinementMacroAssembly

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

abbrev ProfilePair (G : Type*) := (G → ℝ) × (G → ℝ)

def maskVector (P : Finset G) : G → ℝ :=
  fun r => if r ∈ P then 1 else 0

theorem isIndicator_iff_eq_maskVector (f : G → ℝ) (P : Finset G) :
    IsIndicator f P ↔ f = maskVector P := by
  constructor
  · intro h
    exact funext h
  · intro h r
    exact congrFun h r

def periodicInputSlice (R S : Finset G) (a b : ℝ) : LocalLabel G → Set (ProfilePair G)
  | .left P => {v | v.1 = maskVector P ∧ ((P + S).card : ℝ) < a + b}
  | .right Q => {v | v.2 = maskVector Q ∧ ((R + Q).card : ℝ) < a + b}
  | .both P Q => {v | v.1 = maskVector P ∧ v.2 = maskVector Q ∧
      ((P + S).card : ℝ) = a + b ∧ ((R + Q).card : ℝ) = a + b}

theorem profile_pair_mem_slice_iff {R S : Finset G} {a b : ℝ}
    (p : LocalProfile R S a b) (label : LocalLabel G) :
    (p.left, p.right) ∈ periodicInputSlice R S a b label ↔ HasLabel p label := by
  cases label <;>
    simp only [periodicInputSlice, mem_setOf_eq, HasLabel, isIndicator_iff_eq_maskVector]

theorem isClosed_periodicInputSlice (R S : Finset G) (a b : ℝ) (label : LocalLabel G) :
    IsClosed (periodicInputSlice R S a b label) := by
  cases label with
  | left P =>
    by_cases h : ((P + S).card : ℝ) < a + b
    · simpa only [periodicInputSlice, h, and_true] using
        (isClosed_eq continuous_fst (continuous_const : Continuous (fun _ : ProfilePair G => maskVector P)))
    · simp [periodicInputSlice, h]
  | right Q =>
    by_cases h : ((R + Q).card : ℝ) < a + b
    · simpa only [periodicInputSlice, h, and_true] using
        (isClosed_eq continuous_snd (continuous_const : Continuous (fun _ : ProfilePair G => maskVector Q)))
    · simp [periodicInputSlice, h]
  | both P Q =>
    by_cases hP : ((P + S).card : ℝ) = a + b
    · by_cases hQ : ((R + Q).card : ℝ) = a + b
      · simpa only [periodicInputSlice, hP, hQ, and_true, Set.setOf_and] using
          (isClosed_eq continuous_fst
            (continuous_const : Continuous (fun _ : ProfilePair G => maskVector P))).inter
          (isClosed_eq continuous_snd
            (continuous_const : Continuous (fun _ : ProfilePair G => maskVector Q)))
      · simp [periodicInputSlice, hQ]
    · simp [periodicInputSlice, hP]

theorem measurableSet_isIndicator (f : ℝ → G → ℝ)
    (hf : ∀ r, Measurable (fun t => f t r)) (P : Finset G) :
    MeasurableSet {t | IsIndicator (f t) P} := by
  have heq : {t | IsIndicator (f t) P} =
      ⋂ r : G, {t | f t r = if r ∈ P then (1 : ℝ) else 0} := by
    ext t
    simp only [mem_setOf_eq, mem_iInter, IsIndicator]
  rw [heq]
  exact MeasurableSet.iInter (fun r => measurableSet_eq_fun (hf r) measurable_const)

theorem measurableSet_hasLabel {R S : Finset G} {a b : ℝ}
    (p : ℝ → LocalProfile R S a b)
    (hleft : ∀ r, Measurable (fun t => (p t).left r))
    (hright : ∀ r, Measurable (fun t => (p t).right r))
    (label : LocalLabel G) : MeasurableSet {t | HasLabel (p t) label} := by
  cases label with
  | left P =>
    exact (measurableSet_isIndicator (fun t => (p t).left) hleft P).inter
      (MeasurableSet.const _)
  | right Q =>
    exact (measurableSet_isIndicator (fun t => (p t).right) hright Q).inter
      (MeasurableSet.const _)
  | both P Q =>
    exact (measurableSet_isIndicator (fun t => (p t).left) hleft P).inter
      ((measurableSet_isIndicator (fun t => (p t).right) hright Q).inter
        ((MeasurableSet.const _).inter (MeasurableSet.const _)))

theorem hasLabel_unique {R S : Finset G} {a b : ℝ}
    (p : LocalProfile R S a b) (ha : 0 < a) (hb : 0 < b)
    (hgap : a + b < ((R + S).card : ℝ))
    (label target : LocalLabel G) (hlabel : HasLabel p label) (htarget : HasLabel p target) :
    label = target := by
  cases target with
  | right Q =>
    exact label_eq_right_of_indicator p ha hb hgap label hlabel Q htarget.1 htarget.2
  | left P =>
    have h := label_eq_right_of_indicator p.swap hb ha
      (by simpa only [add_comm] using hgap) label.swap hlabel.swap P htarget.1
      (by simpa only [add_comm] using htarget.2)
    have hback := congrArg LocalLabel.swap h
    rw [LocalLabel.swap_swap] at hback
    exact hback
  | both P Q =>
    exact label_eq_both_of_indicators p label hlabel P Q
      htarget.1 htarget.2.1 htarget.2.2.1 htarget.2.2.2

theorem label_eq_of_local_profile_slices {R S : Finset G} {a b : ℝ}
    (p : LocalProfile R S a b) (ha : 0 < a) (hb : 0 < b)
    (hgap : a + b < ((R + S).card : ℝ))
    (v : ProfilePair G) (hleft : p.left = v.1) (hright : p.right = v.2)
    (label target : LocalLabel G)
    (hlabel : v ∈ periodicInputSlice R S a b label)
    (htarget : v ∈ periodicInputSlice R S a b target) : label = target := by
  have hv : v = (p.left, p.right) := Prod.ext hleft.symm hright.symm
  rw [hv] at hlabel htarget
  exact hasLabel_unique p ha hb hgap label target
    ((profile_pair_mem_slice_iff p label).mp hlabel)
    ((profile_pair_mem_slice_iff p target).mp htarget)

theorem exists_ae_profile_label {R S : Finset G} {a b : ℝ}
    (p : ℝ → LocalProfile R S a b) (ha : 0 < a) (hb : 0 < b)
    (hgap : a + b < ((R + S).card : ℝ))
    (hleft : ∀ r, Measurable (fun t => (p t).left r))
    (hright : ∀ r, Measurable (fun t => (p t).right r))
    (hframes : ∀ᵐ t : ℝ, 0 < t →
      ∃ label, HasLabel (p t) label ∧ LabelFrame (p t) label)
    (hcross : ∀ᵐ w : ℝ × ℝ ∂volume.prod volume,
      0 < w.1 → 0 < w.2 → CrossInequality (p w.1) (p w.2) (p (w.1 + w.2))) :
    ∃ label, ∀ᵐ t : ℝ, 0 < t → HasLabel (p t) label := by
  classical
  letI : Fintype (LocalLabel G) := Fintype.ofFinite _
  let E : LocalLabel G → Set ℝ := fun label => {t | 0 < t ∧ HasLabel (p t) label}
  have hEm (label : LocalLabel G) : MeasurableSet (E label) :=
    measurableSet_Ioi.inter (measurableSet_hasLabel p hleft hright label)
  have hEpos (label : LocalLabel G) : E label ⊆ Ioi 0 := fun _ ht => ht.1
  have hcover : ∀ᵐ t : ℝ, 0 < t → ∃ label, t ∈ E label := by
    filter_upwards [hframes] with t ht hpos
    obtain ⟨label, hl, _⟩ := ht hpos
    exact ⟨label, hpos, hl⟩
  have hdisjoint (label target : LocalLabel G) (hne : label ≠ target) :
      Disjoint (E label) (E target) := by
    apply Set.disjoint_left.mpr
    intro t ht hu
    exact hne (hasLabel_unique (p t) ha hb hgap label target ht.2 hu.2)
  have htarget : ∀ᵐ w : ℝ × ℝ ∂volume.prod volume,
      0 < w.1 + w.2 → ∃ label,
        HasLabel (p (w.1 + w.2)) label ∧ LabelFrame (p (w.1 + w.2)) label :=
    (quasiMeasurePreserving_add volume volume).ae hframes
  have hclosed (label : LocalLabel G) : PeriodicRefinementGlobal.AEAddClosed (E label) := by
    filter_upwards [htarget, hcross] with w ht hc hw₁ hw₂
    have hsum : 0 < w.1 + w.2 := add_pos hw₁.1 hw₂.1
    obtain ⟨target, htargetLabel, htargetFrame⟩ := ht hsum
    have heq := same_label_sum_has_same_label (p w.1) (p w.2) (p (w.1 + w.2))
      ha hb hgap label target hw₁.2 hw₂.2 htargetLabel htargetFrame (hc hw₁.1 hw₂.1)
    exact ⟨hsum, heq.symm ▸ htargetLabel⟩
  obtain ⟨label, hlabel⟩ := PeriodicRefinementGlobal.exists_conull_label_of_ae_add_closed_partition
    E hEm hEpos hcover hdisjoint hclosed
  refine ⟨label, ?_⟩
  filter_upwards [hlabel] with t ht hpos
  exact (ht hpos).2

end Erdos335.PeriodicRefinementMacroAssembly

end
