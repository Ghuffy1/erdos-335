import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Finite

/-!
# Almost-everywhere sampling away from countably many sparse bad-start sets

Private draft for the periodic refinement of Erdős 335. The finite bad sets
may have arbitrary supports. Their cardinalities divided by the ambient
scale are the only hypotheses used by the sampling argument.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Filter Topology Set MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

namespace Erdos335.PeriodicRefinement

/-- Positive macroscopic parameters whose sampled integer start is bad. -/
def floorBadStartSet (N : ℕ) (B : Finset ℕ) : Set ℝ :=
  {t | 0 < t ∧ ⌊t * (N : ℝ)⌋₊ ∈ B}

theorem measurableSet_floorBadStartSet (N : ℕ) (B : Finset ℕ) :
    MeasurableSet (floorBadStartSet N B) := by
  change MeasurableSet
    (Ioi (0 : ℝ) ∩ (fun t : ℝ => ⌊t * (N : ℝ)⌋₊) ⁻¹' (B : Set ℕ))
  exact measurableSet_Ioi.inter
    (B.measurableSet.preimage ((measurable_id.mul_const (N : ℝ)).nat_floor))

/-- Each bad integer contributes one grid interval of length `1 / N`. -/
theorem floorBadStartSet_subset_grid (N : ℕ) (hN : 0 < N) (B : Finset ℕ) :
    floorBadStartSet N B ⊆
      ⋃ b ∈ B, Ico ((b : ℝ) / N) (((b : ℝ) + 1) / N) := by
  intro t ht
  rcases ht with ⟨htpos, htbad⟩
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hnonneg : 0 ≤ t * (N : ℝ) := (mul_pos htpos hNreal).le
  refine mem_iUnion.mpr ⟨⌊t * (N : ℝ)⌋₊, mem_iUnion.mpr ⟨htbad, ?_⟩⟩
  exact ⟨(div_le_iff₀ hNreal).mpr (Nat.floor_le hnonneg),
    (lt_div_iff₀ hNreal).mpr (Nat.lt_floor_add_one (t * (N : ℝ)))⟩

theorem volume_floorBadStartSet_le (N : ℕ) (hN : 0 < N) (B : Finset ℕ) :
    volume (floorBadStartSet N B) ≤ ENNReal.ofReal ((B.card : ℝ) / N) := by
  classical
  calc
    volume (floorBadStartSet N B) ≤
        volume (⋃ b ∈ B, Ico ((b : ℝ) / N) (((b : ℝ) + 1) / N)) :=
      measure_mono (floorBadStartSet_subset_grid N hN B)
    _ ≤ ∑ b ∈ B, volume (Ico ((b : ℝ) / N) (((b : ℝ) + 1) / N)) :=
      measure_biUnion_finset_le B _
    _ = ∑ _b ∈ B, ENNReal.ofReal (1 / (N : ℝ)) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Real.volume_Ico]
      congr 1
      ring
    _ = (B.card : ℝ≥0∞) * ENNReal.ofReal (1 / (N : ℝ)) := by
      simp [nsmul_eq_mul]
    _ = ENNReal.ofReal ((B.card : ℝ) * (1 / (N : ℝ))) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg B.card), ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal ((B.card : ℝ) / N) := by
      congr 1
      ring

/-- One strict subsequence gives a summable bound for every fixed bad-set
family after its own finite initial segment. -/
theorem exists_geometric_bad_start_subsequence
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (bad : ℕ → ℕ → Finset ℕ)
    (hbad : ∀ j, Tendsto (fun n => ((bad j n).card : ℝ) / N n) atTop (𝓝 0)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ (∀ k, 0 < N (σ k)) ∧
      ∀ k j, j ≤ k →
        ((bad j (σ k)).card : ℝ) / N (σ k) ≤ (1 / 2 : ℝ) ^ k := by
  classical
  let Q := fun k n : ℕ => 0 < N n ∧
    ∀ j ≤ k, ((bad j n).card : ℝ) / N n ≤ (1 / 2 : ℝ) ^ k
  have hQ (k : ℕ) : ∀ᶠ n in atTop, Q k n := by
    have hpositive : 0 < (1 / 2 : ℝ) ^ k := pow_pos (by norm_num) k
    have hall : ∀ᶠ n in atTop, ∀ j ∈ Finset.range (k + 1),
        ((bad j n).card : ℝ) / N n ≤ (1 / 2 : ℝ) ^ k := by
      apply (eventually_all_finset (Finset.range (k + 1))).mpr
      intro j _
      exact ((hbad j).eventually (eventually_lt_nhds hpositive)).mono fun _ hn => hn.le
    filter_upwards [hN.eventually (eventually_ge_atTop 1), hall] with n hn hgood
    refine ⟨by omega, fun j hj => ?_⟩
    exact hgood j (Finset.mem_range.mpr (by omega))
  have hchoose : ∀ k b : ℕ, ∃ n, b ≤ n ∧ Q k n := by
    intro k b
    obtain ⟨n, hgood, hn⟩ := ((hQ k).and (eventually_ge_atTop b)).exists
    exact ⟨n, hn, hgood⟩
  choose pick hpick using hchoose
  let σ : ℕ → ℕ := Nat.rec (pick 0 0)
    (fun k previous => pick (k + 1) (previous + 1))
  have hstep (k : ℕ) : σ k < σ (k + 1) := by
    have hn := (hpick (k + 1) (σ k + 1)).1
    change σ k + 1 ≤ σ (k + 1) at hn
    omega
  have hgood (k : ℕ) : Q k (σ k) := by
    cases k with
    | zero => exact (hpick 0 0).2
    | succ k => exact (hpick (k + 1) (σ k + 1)).2
  exact ⟨σ, strictMono_nat_of_lt_succ hstep,
    fun k => (hgood k).1, fun k j hj => (hgood k).2 j hj⟩

/-- A single strict subsequence avoids each fixed sparse family eventually
for almost every positive macroscopic parameter on the whole half-line. -/
theorem exists_ae_good_floor_subsequence
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (bad : ℕ → ℕ → Finset ℕ)
    (hbad : ∀ j, Tendsto (fun n => ((bad j n).card : ℝ) / N n) atTop (𝓝 0)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ (∀ k, 0 < N (σ k)) ∧
      ∀ᵐ t : ℝ ∂volume, 0 < t → ∀ j,
        ∀ᶠ k in atTop, ⌊t * (N (σ k) : ℝ)⌋₊ ∉ bad j (σ k) := by
  classical
  obtain ⟨σ, hσ, hNσ, hbound⟩ :=
    exists_geometric_bad_start_subsequence N hN bad hbad
  refine ⟨σ, hσ, hNσ, ?_⟩
  have hall : ∀ j, ∀ᵐ t : ℝ ∂volume, 0 < t →
      ∀ᶠ k in atTop, ⌊t * (N (σ k) : ℝ)⌋₊ ∉ bad j (σ k) := by
    intro j
    let S := fun k => if j ≤ k then floorBadStartSet (N (σ k)) (bad j (σ k)) else ∅
    have hmeasure (k : ℕ) : volume (S k) ≤ (2 : ℝ≥0∞)⁻¹ ^ k := by
      by_cases hjk : j ≤ k
      · change volume (if j ≤ k then _ else _) ≤ _
        rw [if_pos hjk]
        calc
          volume (floorBadStartSet (N (σ k)) (bad j (σ k))) ≤
              ENNReal.ofReal (((bad j (σ k)).card : ℝ) / N (σ k)) :=
            volume_floorBadStartSet_le _ (hNσ k) _
          _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) :=
            ENNReal.ofReal_le_ofReal (hbound k j hjk)
          _ = (2 : ℝ≥0∞)⁻¹ ^ k := by
            rw [ENNReal.ofReal_pow (by norm_num)]
            congr 1
            rw [ENNReal.ofReal_div_of_pos (by norm_num)]
            norm_num
      · simp [S, hjk]
    have hsum : (∑' k, volume (S k)) ≠ ∞ := by
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hmeasure)
      simpa only [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
        using ENNReal.ofNat_ne_top
    filter_upwards [ae_eventually_notMem hsum] with t ht
    intro htpos
    filter_upwards [ht, eventually_ge_atTop j] with k hk hjk
    intro hbadmem
    apply hk
    change t ∈ (if j ≤ k then floorBadStartSet (N (σ k)) (bad j (σ k)) else ∅)
    rw [if_pos hjk]
    exact ⟨htpos, hbadmem⟩
  filter_upwards [ae_all_iff.mpr hall] with t ht
  exact fun htpos j => ht j htpos

end Erdos335.PeriodicRefinement

end
