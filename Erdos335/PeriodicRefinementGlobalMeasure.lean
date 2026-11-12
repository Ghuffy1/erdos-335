import Erdos335.HaarTranslation
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

/-!
# Measurable addition closure on the positive real axis

Private proof development. Verification status is recorded separately. Pairwise addition closure is imposed
with respect to two-dimensional Lebesgue measure. In particular it gives
no assertion about the diagonal before the measure argument is applied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Filter Set Topology MeasureTheory
open MeasureTheory.Measure
open scoped ENNReal

noncomputable section

namespace Erdos335.PeriodicRefinementGlobal

def AEAddClosed (E : Set ℝ) : Prop :=
  ∀ᵐ p : ℝ × ℝ ∂volume.prod volume,
    p.1 ∈ E → p.2 ∈ E → p.1 + p.2 ∈ E

def selfIntegral (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t, f t * f (x - t)

theorem continuous_selfIntegral
    (f : ℝ → ℝ) (hf : Integrable f volume) (hbound : ∀ t, ‖f t‖ ≤ 1) :
    Continuous (selfIntegral f) := by
  have hprod (x : ℝ) : Integrable (fun t => f t * f (x - t)) volume :=
    hf.mul_bdd (hf.comp_sub_left x).aestronglyMeasurable
      (Eventually.of_forall (fun t => hbound (x - t)))
  have hestimate (x y : ℝ) : dist (selfIntegral f x) (selfIntegral f y) ≤
      ∫ t, ‖f ((x - y) + t) - f t‖ := by
    have hdiff := (hf.comp_sub_left x).sub (hf.comp_sub_left y)
    have hprodDiff : Integrable (fun t => f t * (f (x - t) - f (y - t))) volume := by
      apply ((hprod x).sub (hprod y)).congr
      filter_upwards [] with t
      change f t * f (x - t) - f t * f (y - t) = f t * (f (x - t) - f (y - t))
      ring
    calc
      dist (selfIntegral f x) (selfIntegral f y) =
          ‖∫ t, f t * (f (x - t) - f (y - t))‖ := by
        rw [dist_eq_norm, selfIntegral, selfIntegral, ← integral_sub (hprod x) (hprod y)]
        congr 1
        apply integral_congr_ae
        exact Eventually.of_forall (fun t => by ring)
      _ ≤ ∫ t, ‖f t * (f (x - t) - f (y - t))‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ t, ‖f (x - t) - f (y - t)‖ := by
        apply integral_mono hprodDiff.norm hdiff.norm
        intro t
        change ‖f t * (f (x - t) - f (y - t))‖ ≤ ‖f (x - t) - f (y - t)‖
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hbound t)
      _ = ∫ t, ‖f ((x - y) + t) - f t‖ := by
        have heq (t : ℝ) : (x - y) + (y - t) = x - t := by ring
        simpa only [heq] using integral_sub_left_eq_self
          (fun t : ℝ => ‖f ((x - y) + t) - f t‖) volume y
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have htranslate : Continuous (fun y : ℝ => y - x) :=
    continuous_id.sub continuous_const
  have hlim := ((Erdos335.Loeb.continuous_integral_norm_add_sub volume f hf).comp
    htranslate).tendsto x
  have hzero : Tendsto (fun y : ℝ => ∫ t, ‖f ((y - x) + t) - f t‖)
      (𝓝 x) (𝓝 0) := by
    simpa only [Function.comp_def, sub_self, zero_add, norm_zero, integral_zero] using hlim
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun y => by simpa only [dist_eq_norm] using hestimate y x) hzero

theorem ae_add_closed_fiber (E : Set ℝ) (hE : AEAddClosed E) :
    ∀ᵐ z : ℝ, ∀ᵐ t : ℝ, t ∈ E → z - t ∈ E → t + (z - t) ∈ E := by
  exact ae_ae_of_ae_prod
    ((measurePreserving_prod_sub_swap volume volume).quasiMeasurePreserving.ae hE)

theorem selfIntegral_indicator_zero_off
    (E K : Set ℝ) (hKE : K ⊆ E) (hE : AEAddClosed E) :
    ∀ᵐ z : ℝ, z ∉ E → selfIntegral (K.indicator (fun _ => (1 : ℝ))) z = 0 := by
  filter_upwards [ae_add_closed_fiber E hE] with z hz hnot
  apply integral_eq_zero_of_ae
  filter_upwards [hz] with t ht
  by_cases htk : t ∈ K
  · by_cases hzk : z - t ∈ K
    · have hzE := ht (hKE htk) (hKE hzk)
      have heq : t + (z - t) = z := by ring
      exact (hnot (heq ▸ hzE)).elim
    · simp only [Set.indicator_of_notMem hzk, mul_zero, Pi.zero_apply]
  · simp only [Set.indicator_of_notMem htk, zero_mul, Pi.zero_apply]

theorem exists_positive_interval_ae_subset_of_ae_add_closed
    (E : Set ℝ) (hEm : MeasurableSet E) (hEpos : E ⊆ Ioi 0)
    (hEmeasure : volume E ≠ 0) (hE : AEAddClosed E) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ ∀ᵐ t : ℝ, t ∈ Ioo a b → t ∈ E := by
  have hbounded : ∃ N : ℕ, volume (E ∩ Icc (0 : ℝ) N) ≠ 0 := by
    by_contra! hzero
    have hnull : volume (⋃ N : ℕ, E ∩ Icc (0 : ℝ) N) = 0 :=
      measure_iUnion_null hzero
    apply hEmeasure
    apply measure_mono_null ?_ hnull
    intro t ht
    obtain ⟨N, hN⟩ := exists_nat_ge t
    exact mem_iUnion.mpr ⟨N, ht, (hEpos ht).le, hN⟩
  obtain ⟨N, hN⟩ := hbounded
  let K : Set ℝ := E ∩ Icc (0 : ℝ) N
  let f : ℝ → ℝ := K.indicator (fun _ => (1 : ℝ))
  have hKm : MeasurableSet K := hEm.inter measurableSet_Icc
  have hKfin : volume K ≠ ∞ :=
    ne_of_lt ((measure_mono inter_subset_right).trans_lt isCompact_Icc.measure_lt_top)
  have hf : Integrable f volume :=
    (integrable_indicator_iff hKm).mpr (integrableOn_const hKfin)
  have hbound (t : ℝ) : ‖f t‖ ≤ 1 := by
    by_cases ht : t ∈ K <;> simp [f, ht]
  have hmean : ∫ x, selfIntegral f x = (∫ x, f x) * (∫ x, f x) := by
    simpa only [selfIntegral, convolution, ContinuousLinearMap.mul_apply'] using
      (integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hf hf)
  have hfmass : 0 < ∫ x, f x := by
    rw [show f = K.indicator (fun _ => (1 : ℝ)) from rfl, integral_indicator_const (1 : ℝ) hKm]
    simpa only [smul_eq_mul, mul_one, Measure.real] using ENNReal.toReal_pos hN hKfin
  have hex : ∃ z, 0 < selfIntegral f z := by
    by_contra! hn
    have hnonpos : ∫ z, selfIntegral f z ≤ 0 := integral_nonpos hn
    rw [hmean] at hnonpos
    exact (not_le_of_gt (mul_pos hfmass hfmass)) hnonpos
  obtain ⟨z, hz⟩ := hex
  have hzpos : 0 < z := by
    by_contra! hnonpos
    have hz0 : selfIntegral f z = 0 := by
      apply integral_eq_zero_of_ae
      apply Eventually.of_forall
      intro t
      by_cases ht : t ∈ K
      · have hznot : z - t ∉ K := by
          intro hzt
          have htpos : 0 < t := hEpos ht.1
          have hztpos : 0 < z - t := hEpos hzt.1
          linarith
        simp [f, hznot]
      · simp [f, ht]
    exact (ne_of_gt hz) hz0
  have hopen : IsOpen {x : ℝ | 0 < x ∧ 0 < selfIntegral f x} :=
    isOpen_Ioi.inter (isOpen_lt continuous_const (continuous_selfIntegral f hf hbound))
  obtain ⟨a, b, hab, hinterval⟩ := hopen.exists_Ioo_subset ⟨z, hzpos, hz⟩
  let a' := (a + b) / 2
  let b' := (a + 3 * b) / 4
  have ha'mem : a' ∈ Ioo a b := by dsimp [a']; constructor <;> linarith
  have ha' : 0 < a' := (hinterval ha'mem).1
  have hab' : a' < b' := by dsimp [a', b']; linarith
  refine ⟨a', b', ha', hab', ?_⟩
  filter_upwards [selfIntegral_indicator_zero_off E K inter_subset_left hE] with t ht htab
  by_contra htE
  have htin : t ∈ Ioo a b := by dsimp [a', b'] at htab; constructor <;> linarith [htab.1, htab.2]
  have hpositive := (hinterval htin).2
  exact (ne_of_gt hpositive) (ht htE)

theorem ae_interval_add_subset
    (E : Set ℝ) (hE : AEAddClosed E)
    (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (habE : ∀ᵐ t : ℝ, t ∈ Ioo a b → t ∈ E)
    (hcdE : ∀ᵐ t : ℝ, t ∈ Ioo c d → t ∈ E) :
    ∀ᵐ z : ℝ, z ∈ Ioo (a + c) (b + d) → z ∈ E := by
  filter_upwards [ae_add_closed_fiber E hE] with z hz hzin
  let J : Set ℝ := Ioo (max a (z - d)) (min b (z - c))
  have hJlength : max a (z - d) < min b (z - c) := by
    apply max_lt
    · apply lt_min
      · exact hab
      · linarith [hzin.1]
    · apply lt_min
      · linarith [hzin.2]
      · linarith
  have hJpos : volume J ≠ 0 := by
    rw [show J = Ioo (max a (z - d)) (min b (z - c)) from rfl, Real.volume_Ioo]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hJlength)).ne'
  have hshift : ∀ᵐ t : ℝ, z - t ∈ Ioo c d → z - t ∈ E :=
    (measurePreserving_sub_left volume z).quasiMeasurePreserving.ae hcdE
  obtain ⟨t, htJ, htAB, htCD, htadd⟩ := exists_mem_of_measure_ne_zero_of_ae hJpos
    (ae_restrict_of_ae (habE.and (hshift.and hz)))
  have htA : t ∈ Ioo a b :=
    ⟨lt_of_le_of_lt (le_max_left _ _) htJ.1, lt_of_lt_of_le htJ.2 (min_le_left _ _)⟩
  have htC : z - t ∈ Ioo c d := by
    have hlo := lt_of_le_of_lt (le_max_right a (z - d)) htJ.1
    have hhi := lt_of_lt_of_le htJ.2 (min_le_right b (z - c))
    constructor <;> linarith
  have hsum := htadd (htAB htA) (htCD htC)
  convert hsum using 1 <;> ring

theorem exists_tail_ae_subset_of_ae_add_closed
    (E : Set ℝ) (hEm : MeasurableSet E) (hEpos : E ⊆ Ioi 0)
    (hEmeasure : volume E ≠ 0) (hE : AEAddClosed E) :
    ∃ T : ℝ, ∀ᵐ t : ℝ, T < t → t ∈ E := by
  obtain ⟨a, b, ha, hab, hinterval⟩ :=
    exists_positive_interval_ae_subset_of_ae_add_closed E hEm hEpos hEmeasure hE
  have hb : 0 < b := ha.trans hab
  have hintervals (n : ℕ) : ∀ᵐ t : ℝ,
      t ∈ Ioo (((n + 1 : ℕ) : ℝ) * a) (((n + 1 : ℕ) : ℝ) * b) → t ∈ E := by
    induction n with
    | zero => simpa using hinterval
    | succ n ih =>
      have habn : (((n + 1 : ℕ) : ℝ) * a) < (((n + 1 : ℕ) : ℝ) * b) :=
        mul_lt_mul_of_pos_left hab (by positivity)
      convert ae_interval_add_subset E hE _ _ a b habn hab ih hinterval using 1 <;>
        push_cast <;> ring
  let T : ℝ := a * b / (b - a) + 1
  refine ⟨T, ?_⟩
  filter_upwards [ae_all_iff.mpr hintervals] with t ht htT
  have hba : 0 < b - a := sub_pos.mpr hab
  have hTpos : 0 < T := by dsimp [T]; positivity
  have htpos : 0 < t := hTpos.trans htT
  let n : ℕ := ⌊t / b⌋₊
  have hfloor : (n : ℝ) ≤ t / b := Nat.floor_le (div_nonneg htpos.le hb.le)
  have hupper : t < ((n : ℝ) + 1) * b := by
    have h := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one (t / b)) hb
    simpa only [div_mul_cancel₀ _ hb.ne'] using h
  have hlarge : a * b < t * (b - a) := by
    apply (div_lt_iff₀ hba).mp
    exact lt_trans (by dsimp [T]; linarith) htT
  have hlower_aux : (t / b + 1) * a < t := by
    apply (mul_lt_mul_iff_left₀ hb).mp
    calc
      ((t / b + 1) * a) * b = (t / b * b) * a + a * b := by ring
      _ = t * a + a * b := by rw [div_mul_cancel₀ _ hb.ne']
      _ < t * b := by nlinarith [hlarge]
  have hlower : ((n : ℝ) + 1) * a < t :=
    (mul_le_mul_of_nonneg_right (add_le_add hfloor le_rfl) ha.le).trans_lt hlower_aux
  exact ht n (by simpa only [Nat.cast_add, Nat.cast_one, Set.mem_Ioo] using And.intro hlower hupper)

theorem exists_conull_label_of_ae_add_closed_partition
    {I : Type*} [Fintype I]
    (E : I → Set ℝ) (hEm : ∀ i, MeasurableSet (E i))
    (hEpos : ∀ i, E i ⊆ Ioi 0)
    (hcover : ∀ᵐ t : ℝ, 0 < t → ∃ i, t ∈ E i)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (E i) (E j))
    (hclosed : ∀ i, AEAddClosed (E i)) :
    ∃ i, ∀ᵐ t : ℝ, 0 < t → t ∈ E i := by
  classical
  have hsome : ∃ i, volume (E i) ≠ 0 := by
    by_contra! hzero
    have hnone : ∀ᵐ t : ℝ, ∀ i, t ∉ E i := by
      apply ae_all_iff.mpr
      intro i
      apply ae_iff.mpr
      simpa only [not_not, setOf_mem_eq] using hzero i
    have hunit : volume (Ioo (0 : ℝ) 1) ≠ 0 := by simp
    obtain ⟨t, ht, htnone, htcover⟩ := exists_mem_of_measure_ne_zero_of_ae hunit
      (ae_restrict_of_ae (hnone.and hcover))
    obtain ⟨i, hi⟩ := htcover ht.1
    exact htnone i hi
  obtain ⟨i, hi⟩ := hsome
  obtain ⟨T, hT⟩ := exists_tail_ae_subset_of_ae_add_closed
    (E i) (hEm i) (hEpos i) hi (hclosed i)
  have hzero (j : I) (hji : j ≠ i) : volume (E j) = 0 := by
    by_contra hj
    obtain ⟨U, hU⟩ := exists_tail_ae_subset_of_ae_add_closed
      (E j) (hEm j) (hEpos j) hj (hclosed j)
    have hinterval : volume (Ioo (max T U) (max T U + 1)) ≠ 0 := by simp
    obtain ⟨t, ht, htT, htU⟩ := exists_mem_of_measure_ne_zero_of_ae hinterval
      (ae_restrict_of_ae (hT.and hU))
    exact (Set.disjoint_left.mp (hdisjoint i j hji.symm))
      (htT (lt_of_le_of_lt (le_max_left T U) ht.1))
      (htU (lt_of_le_of_lt (le_max_right T U) ht.1))
  have hothers : ∀ᵐ t : ℝ, ∀ j, j ≠ i → t ∉ E j := by
    apply ae_all_iff.mpr
    intro j
    by_cases hji : j = i
    · exact Eventually.of_forall (fun _ hne => (hne hji).elim)
    · have hj : ∀ᵐ t : ℝ, t ∉ E j := by
        apply ae_iff.mpr
        simpa only [not_not, setOf_mem_eq] using hzero j hji
      filter_upwards [hj] with t ht _ using ht
  refine ⟨i, ?_⟩
  filter_upwards [hcover, hothers] with t htcover htother htpos
  obtain ⟨j, hj⟩ := htcover htpos
  by_cases hji : j = i
  · simpa only [hji] using hj
  · exact (htother j hji hj).elim

theorem measurable_finite_label_ae_constant
    {I : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (label : ℝ → I) (hmeas : Measurable label)
    (hadd : ∀ᵐ p : ℝ × ℝ ∂volume.prod volume,
      0 < p.1 → 0 < p.2 → label p.1 = label p.2 →
        label (p.1 + p.2) = label p.1) :
    ∃ i, ∀ᵐ t : ℝ, 0 < t → label t = i := by
  let E : I → Set ℝ := fun i => {t | 0 < t ∧ label t = i}
  have hEm (i : I) : MeasurableSet (E i) :=
    measurableSet_Ioi.inter (hmeas (measurableSet_singleton i))
  have hpos (i : I) : E i ⊆ Ioi 0 := fun _ ht => ht.1
  have hcover : ∀ᵐ t : ℝ, 0 < t → ∃ i, t ∈ E i :=
    Eventually.of_forall (fun t ht => ⟨label t, ht, rfl⟩)
  have hdisjoint (i j : I) (hij : i ≠ j) : Disjoint (E i) (E j) := by
    apply Set.disjoint_left.mpr
    intro t hti htj
    exact hij (hti.2.symm.trans htj.2)
  have hclosed (i : I) : AEAddClosed (E i) := by
    filter_upwards [hadd] with p hp hpi hpj
    exact ⟨add_pos hpi.1 hpj.1,
      (hp hpi.1 hpj.1 (hpi.2.trans hpj.2.symm)).trans hpi.2⟩
  obtain ⟨i, hi⟩ := exists_conull_label_of_ae_add_closed_partition
    E hEm hpos hcover hdisjoint hclosed
  refine ⟨i, ?_⟩
  filter_upwards [hi] with t ht htpos
  exact (ht htpos).2

end Erdos335.PeriodicRefinementGlobal

end
