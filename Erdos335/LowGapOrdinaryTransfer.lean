import Erdos335.FixedScaleFourierModels
import Erdos335.ConstrainedCyclicModels
import Erdos335.LoebPrefixAgreement
import Erdos335.SelectedLengthComparison
import Erdos335.FiniteBadSetAverages

/-!
# Ordinary density from null defects in constrained paired windows

Private proof development. Verification status is recorded separately.

The defect set is fixed before the macro sequence, Fourier witnesses, scales,
and window starts are chosen. The local premise is tested on paired actual
windows with a common physical start. Either selected cyclic length may
certify that the defect is null.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory Finset
open scoped BigOperators Pointwise ENNReal

noncomputable section

namespace Erdos335.IntermediateScale

local instance ordinaryTransferLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) :=
  Loeb.loebMeasurableSpace U

theorem indicator_prefix_sum (T : Set ℕ) (N : ℕ) :
    (∑ n ∈ range N, T.indicator (fun _ => (1 : ℝ)) n) = (prefixCount T N : ℝ) := by
  classical
  simp [prefixCount, Set.indicator, Set.mem_setOf_eq]

theorem indicator_window_sum (T : Set ℕ) (start q : ℕ) [NeZero q] :
    (∑ n ∈ range q, T.indicator (fun _ => (1 : ℝ)) (start + n)) =
      ((cyclicWindow T start q).card : ℝ) := by
  classical
  rw [cyclicWindow_card_eq_prefixCount]
  simp [prefixCount, Set.indicator, Finset.sum_filter]
  congr 1
  apply Finset.filter_congr
  intro n _
  change (start + n ∈ T) ↔ (n + start ∈ T)
  rw [Nat.add_comm start n]

theorem prefix_density_le_bad_window_fraction
    (T : Set ℕ) (N : ℕ) (H : ℕ+) (ε : ℝ) (hN : 0 < N) (hε : 0 ≤ ε) :
    (prefixCount T N : ℝ) / N ≤ ε +
      (((range N).filter (fun n => ε ≤
        ((cyclicWindow T (n + 3 * (H : ℕ)) (H : ℕ)).card : ℝ) / (H : ℕ))).card : ℝ) / N +
      4 * (H : ℕ) / N := by
  classical
  let f := T.indicator (fun _ => (1 : ℝ))
  let e := fun n => (∑ i ∈ range (H : ℕ), f (n + 3 * (H : ℕ) + i)) / (H : ℕ)
  have hf (n : ℕ) : f n ∈ Icc (0 : ℝ) 1 := by
    by_cases hn : n ∈ T <;> simp [f, hn]
  have he (n : ℕ) : e n ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sum_nonneg fun i hi => (hf _).1) (by positivity)
    · apply (div_le_one (by positivity : (0 : ℝ) < (H : ℕ))).mpr
      calc
        (∑ i ∈ range (H : ℕ), f (n + 3 * (H : ℕ) + i)) ≤
            ∑ _i ∈ range (H : ℕ), (1 : ℝ) := sum_le_sum fun i hi => (hf _).2
        _ = _ := by simp
  have hwindow (n : ℕ) : e n =
      ((cyclicWindow T (n + 3 * (H : ℕ)) (H : ℕ)).card : ℝ) / (H : ℕ) := by
    dsimp only [e, f]
    rw [indicator_window_sum]
  have hmean := prefix_mean_le_offset_window_mean f 1 hf N (3 * (H : ℕ)) (H : ℕ) hN H.pos
  push_cast at hmean
  have hbad := finite_mean_le_threshold_add_bad_fraction e 1 ε N hN hε (fun n hn => he n)
  change (∑ n ∈ range N, f n) / N ≤ (∑ n ∈ range N, e n) / N + _ at hmean
  have h : (∑ n ∈ range N, f n) / N ≤ ε +
      1 * (((range N).filter (fun n => ε ≤ e n)).card : ℝ) / N +
      1 * (3 * (H : ℕ) + (H : ℕ)) / N := by
    linarith [hmean, hbad]
  dsimp only [f] at h
  rw [indicator_prefix_sum] at h
  have hfour : (3 : ℝ) * (H : ℕ) + (H : ℕ) = 4 * (H : ℕ) := by ring
  simpa only [hwindow, one_mul, hfour] using h

theorem loeb_window_null_tendsto_common_length
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (T : Set ℕ) (start H : ℕ → ℕ) (q : ℕ → ℕ+)
    (hH : ∀ n, 0 < H n) (hHq : ∀ n, H n ≤ (q n : ℕ))
    (hqgap : Tendsto (fun n => (((q n : ℕ) - H n : ℕ) : ℝ) / (q n : ℕ))
      atTop (𝓝 0))
    (hnull : Loeb.loebMeasure U hU (Loeb.internalSet U
      (fun n => (cyclicWindow T (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))) = 0) :
    Tendsto (fun n =>
      ((@cyclicWindow T (start n) (H n) ⟨(hH n).ne'⟩).card : ℝ) / H n)
      (U : Filter ℕ) (𝓝 0) := by
  let p : ℕ → ℕ+ := fun n => ⟨H n, hH n⟩
  letI (n : ℕ) : NeZero (H n) := ⟨(hH n).ne'⟩
  have hp : Tendsto (fun n => (((p n : ℕ) - H n : ℕ) : ℝ) / (p n : ℕ))
      atTop (𝓝 0) := by
    change Tendsto (fun n => (((H n - H n : ℕ) : ℝ) / H n)) atTop (𝓝 0)
    simpa only [Nat.sub_self, Nat.cast_zero, zero_div] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hHp (n : ℕ) : H n ≤ (p n : ℕ) := by
    change H n ≤ H n
    exact le_rfl
  have hcomparison := selected_cyclic_profiles_agree (fun _ => T) start H p q
    hH hHp hHq hp hqgap
  change Tendsto (fun n => ((cyclicWindow T (start n) (H n)).card : ℝ) / H n -
    ((cyclicWindow T (start n) (q n : ℕ)).card : ℝ) / (q n : ℕ)) atTop (𝓝 0) at hcomparison
  have hsmall : Tendsto (fun n => ((cyclicWindow T (start n) (q n : ℕ)).card : ℝ) /
      (q n : ℕ)) (U : Filter ℕ) (𝓝 0) := by
    simpa only [hnull, ENNReal.toReal_zero] using
      Loeb.loeb_finset_measure_tendsto U hU q (fun n => cyclicWindow T (start n) (q n : ℕ))
  change Tendsto (fun n => ((cyclicWindow T (start n) (H n)).card : ℝ) / H n)
    (U : Filter ℕ) (𝓝 0)
  simpa only [sub_add_cancel, add_zero] using (hcomparison.mono_left hU).add hsmall

private theorem positive_subsequence_of_not_tendsto_zero
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (hnot : ¬ Tendsto f atTop (𝓝 0)) :
    ∃ (δ : ℝ) (N : ℕ → ℕ), 0 < δ ∧ Tendsto N atTop atTop ∧ ∀ n, δ ≤ f (N n) := by
  have hex : ∃ δ : ℝ, 0 < δ ∧ ¬ ∀ᶠ n in atTop, f n < δ := by
    by_contra! h
    apply hnot
    apply tendsto_order.mpr
    constructor
    · intro x hx
      exact Eventually.of_forall fun n => hx.trans_le (hf n)
    · intro x hx
      exact h x hx
  obtain ⟨δ, hδ, hbad⟩ := hex
  have hfreq : ∃ᶠ n in atTop, δ ≤ f n := by
    simpa only [Filter.Frequently, not_le] using hbad
  obtain ⟨N, hN, hbadN⟩ := Filter.exists_seq_forall_of_frequently hfreq
  exact ⟨δ, N, hδ, hN, hbadN⟩

/-- The local premise is the actual-window interface returned by the paired
constrained cyclic construction. Its conclusion may use either orientation.
The set `T` is fixed before this premise is invoked. -/
theorem negligible_of_constrained_window_null
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A B T : Set ℕ) (a b c : ℝ)
    (hA : HasDensity A a) (hB : HasDensity B b) (hC : HasDensity (A + B) c)
    (hlocal : ∀ (q : Bool → ℕ → ℕ+)
      (hdiv : ∀ o, ∀ h : ℕ+, ∀ᶠ n in atTop, (h : ℕ) ∣ (q o n : ℕ))
      (hq : ∀ o, Tendsto (fun n => (q o n : ℕ)) atTop atTop)
      (H : ℕ → ℕ) (hH : ∀ n, 0 < H n) (hHq : ∀ o n, H n ≤ (q o n : ℕ))
      (hqgap : ∀ o, Tendsto (fun n => (((q o n : ℕ) - H n : ℕ) : ℝ) /
        (q o n : ℕ)) atTop (𝓝 0))
      (start : ℕ → ℕ) (D : ∀ o n, Set (ZMod (q o n : ℕ))) (E : Bool → ℕ → Set ℕ),
      (∀ o, Loeb.internalSet U (D o) ⊆ Loeb.internalSet U
        (fun n => (cyclicWindow (if o then B else A) (start n) (q o n : ℕ) :
          Set (ZMod (q o n : ℕ))))) →
      (∀ o, Loeb.internalSet U (D o) =ᵐ[Loeb.loebMeasure U hU] Loeb.internalSet U
        (fun n => (cyclicWindow (if o then B else A) (start n) (q o n : ℕ) :
          Set (ZMod (q o n : ℕ))))) →
      (∀ o, ∀ᶠ n in U, E o n ⊆ (if o then A else B)) →
      (∀ o, ∀ v ∈ (if o then A else B), ∀ᶠ n in U, v ∈ E o n) →
      (∀ o, Loeb.internalSet U (fun n => ((↑) : ℕ → ZMod (q o n : ℕ)) '' E o n)
        =ᵐ[Loeb.loebMeasure U hU] Loeb.internalSet U
          (fun n => (cyclicWindow (if o then A else B) 0 (q o n : ℕ) :
            Set (ZMod (q o n : ℕ))))) →
      (∀ o, (Loeb.loebMeasure U hU (Loeb.internalSet U
        (fun n => (cyclicWindow (if o then B else A) (start n) (q o n : ℕ) :
          Set (ZMod (q o n : ℕ)))))).toReal = (if o then b else a)) →
      (∀ o, (Loeb.loebMeasure U hU (Loeb.internalSet U
        (fun n => (cyclicWindow (if o then A else B) (start n) (q o n : ℕ) :
          Set (ZMod (q o n : ℕ)))))).toReal = (if o then a else b)) →
      (∀ o, (Loeb.loebMeasure U hU (Loeb.internalSet U
        (fun n => (cyclicWindow (A + B) (start n) (q o n : ℕ) :
          Set (ZMod (q o n : ℕ)))))).toReal = c) →
      (∀ o, (Loeb.loebMeasure U hU
        (Loeb.internalSet U (fun n => ((↑) : ℕ → ZMod (q o n : ℕ)) '' E o n))).toReal =
          (if o then a else b)) →
      (∀ o, Loeb.internalSet U (D o) +
        Loeb.internalSet U (fun n => ((↑) : ℕ → ZMod (q o n : ℕ)) '' E o n)
          ≤ᵐ[Loeb.loebMeasure U hU] Loeb.internalSet U
            (fun n => (cyclicWindow (A + B) (start n) (q o n : ℕ) :
              Set (ZMod (q o n : ℕ))))) →
      ∃ o : Bool, Loeb.loebMeasure U hU (Loeb.internalSet U
        (fun n => (cyclicWindow T (start n) (q o n : ℕ) : Set (ZMod (q o n : ℕ))))) = 0) :
    Negligible T := by
  classical
  apply (hasDensity_iff_prefixCount T 0).mpr
  by_contra hnot
  obtain ⟨δ, M, hδ, hM, hbadM⟩ := positive_subsequence_of_not_tendsto_zero
    (fun n => (prefixCount T n : ℝ) / n) (fun n => by positivity) hnot
  obtain ⟨σ, hσ, hNmono, hprev⟩ := exists_sparse_prefix_subsequence M hM
  let N := M ∘ σ
  have hN : Tendsto N atTop atTop := hM.comp hσ.tendsto_atTop
  have hNpos (s : ℕ) : 0 < N s := by
    have hb := hbadM (σ s)
    by_contra hn
    have hz : N s = 0 := by omega
    change δ ≤ (prefixCount T (N s) : ℝ) / N s at hb
    simp only [hz, Nat.cast_zero, div_zero] at hb
    exact hδ.not_ge hb
  letI (s : ℕ) : NeZero (N s) := ⟨(hNpos s).ne'⟩
  obtain ⟨τ, L, V, H, hτ, _, _, hH, _, hHtop, _, hLH, hHV, hHN,
      hAe, hBe, hCe, ⟨mA⟩, ⟨mB⟩⟩ :=
    exists_fixed_scale_fourier_models_of_density N hN hNmono.monotone hprev
      A B a b c hA hB hC U hU
  letI (s : ℕ) : NeZero (H s) := ⟨(hH s).ne'⟩
  let S (s : ℕ) : Finset ℕ := (range (N (τ s))).filter fun n => δ / 4 ≤
    ((cyclicWindow T (n + 3 * H s) (H s)).card : ℝ) / H s
  have hS (s : ℕ) : S s ⊆ range (N (τ s)) := filter_subset _ _
  have hSlarge : ∀ᶠ s in atTop, δ / 2 ≤ ((S s).card : ℝ) / N (τ s) := by
    have hedge : Tendsto (fun s => 4 * (H s : ℝ) / N (τ s)) atTop (𝓝 0) := by
      simpa only [mul_div_assoc, mul_zero] using hHN.const_mul 4
    filter_upwards [hedge.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < δ / 4))]
      with s hs
    have hp := prefix_density_le_bad_window_fraction T (N (τ s)) ⟨H s, hH s⟩
      (δ / 4) (hNpos (τ s)) (by positivity)
    have hb : δ ≤ (prefixCount T (N (τ s)) : ℝ) / N (τ s) := hbadM (σ (τ s))
    change (prefixCount T (N (τ s)) : ℝ) / N (τ s) ≤
      δ / 4 + ((S s).card : ℝ) / N (τ s) + 4 * (H s : ℝ) / N (τ s) at hp
    linarith
  let moving : Bool → Set ℕ := fun o => if o then B else A
  let other : Bool → Set ℕ := fun o => if o then A else B
  let da : Bool → ℝ := fun o => if o then b else a
  let db : Bool → ℝ := fun o => if o then a else b
  have hdensity (o : Bool) : HasDensity (other o) (db o) := by
    cases o
    · exact hB
    · exact hA
  have hmodels (o : Bool) : IntermediateFourierModel
      ((moving o).indicator (fun _ => (1 : ℝ))) (N ∘ τ) L V := by
    cases o
    · exact mA
    · exact mB
  have heMoving (o : Bool) : Tendsto
      (fun s => prefixError (moving o) (da o) (N (τ s)) / H s) atTop (𝓝 0) := by
    cases o
    · exact hAe
    · exact hBe
  have heOther (o : Bool) : Tendsto
      (fun s => prefixError (other o) (db o) (N (τ s)) / H s) atTop (𝓝 0) := by
    cases o
    · exact hBe
    · exact hAe
  have heSum (o : Bool) : Tendsto
      (fun s => prefixError (moving o + other o) c (N (τ s)) / H s) atTop (𝓝 0) := by
    cases o
    · exact hCe
    · simpa [moving, other, add_comm B A] using hCe
  obtain ⟨n, q, _, hnS, hqdata⟩ := exists_constrained_cyclic_models
    moving other da db (fun _ => c) hdensity (N ∘ τ) L V H
      (fun s => hNpos (τ s)) hH hHtop hLH hHV hHN hmodels heMoving heSum
        S hS (δ / 2) (by positivity) hSlarge
  choose DF PF hfinite using fun o => (hqdata o).2.2.2.2.2
  let start := fun s => n s + 3 * H s
  let D := fun o s => (DF o s : Set (ZMod (q o s : ℕ)))
  let E := fun o s => (cyclicLift (PF o s) : Set ℕ)
  have himage (o : Bool) (s : ℕ) :
      ((↑) : ℕ → ZMod (q o s : ℕ)) '' E o s = (PF o s : Set (ZMod (q o s : ℕ))) := by
    dsimp only [E]
    rw [← Finset.coe_image]
    exact congrArg (fun F : Finset (ZMod (q o s : ℕ)) => (F : Set (ZMod (q o s : ℕ))))
      (cyclicLift_image (PF o s))
  have hHq (o : Bool) : ∀ s, H s ≤ (q o s : ℕ) := (hqdata o).1
  have hq (o : Bool) : Tendsto (fun s => (q o s : ℕ)) atTop atTop := (hqdata o).2.1
  have hqgap (o : Bool) : Tendsto
      (fun s => (((q o s : ℕ) - H s : ℕ) : ℝ) / (q o s : ℕ)) atTop (𝓝 0) :=
    (hqdata o).2.2.1
  have hdiv (o : Bool) (h : ℕ+) : ∀ᶠ s in atTop, (h : ℕ) ∣ (q o s : ℕ) :=
    (hqdata o).2.2.2.1 h h.pos
  have hinside (o : Bool) : ∀ᶠ s in atTop, start s + (q o s : ℕ) ≤ N (τ s) :=
    (hqdata o).2.2.2.2.1
  have herrorq (o : Bool) (R : Set ℕ) (d : ℝ)
      (he : Tendsto (fun s => prefixError R d (N (τ s)) / H s) atTop (𝓝 0)) :
      Tendsto (fun s => prefixError R d (N (τ s)) / (q o s : ℕ)) atTop (𝓝 0) := by
    apply squeeze_zero (fun s => div_nonneg (prefixError_nonneg R d _) (by positivity))
      (fun s => ?_) he
    exact div_le_div_of_nonneg_left (prefixError_nonneg R d _)
      (by exact_mod_cast hH s) (by exact_mod_cast hHq o s)
  have hMovingCount (o : Bool) : Tendsto
      (fun s => ((cyclicWindow (moving o) (start s) (q o s : ℕ)).card : ℝ) / (q o s : ℕ))
      atTop (𝓝 (da o)) :=
    cyclic_window_density_of_general_prefix_error (moving o) (da o) (N ∘ τ)
      (fun s => (q o s : ℕ)) start (hq o) (hinside o) (herrorq o _ _ (heMoving o))
  have hOtherCount (o : Bool) : Tendsto
      (fun s => ((cyclicWindow (other o) (start s) (q o s : ℕ)).card : ℝ) / (q o s : ℕ))
      atTop (𝓝 (db o)) :=
    cyclic_window_density_of_general_prefix_error (other o) (db o) (N ∘ τ)
      (fun s => (q o s : ℕ)) start (hq o) (hinside o) (herrorq o _ _ (heOther o))
  have hDsub (o : Bool) : Loeb.internalSet U (D o) ⊆ Loeb.internalSet U
      (fun s => (cyclicWindow (moving o) (start s) (q o s : ℕ) : Set (ZMod (q o s : ℕ)))) := by
    apply (Loeb.internalSet_subset_iff U _ _).mpr
    exact Eventually.of_forall fun s => ((hfinite o).1 s).1
  have hDAE (o : Bool) : Loeb.internalSet U (D o) =ᵐ[Loeb.loebMeasure U hU]
      Loeb.internalSet U (fun s =>
        (cyclicWindow (moving o) (start s) (q o s : ℕ) : Set (ZMod (q o s : ℕ)))) :=
    Loeb.loeb_finset_ae_eq_of_same_density U hU (q o) (DF o)
      (fun s => cyclicWindow (moving o) (start s) (q o s : ℕ)) (da o)
      (fun s => ((hfinite o).1 s).1) (hfinite o).2.2.1 (hMovingCount o)
  have hEsub (o : Bool) : ∀ᶠ s in U, E o s ⊆ other o :=
    Eventually.of_forall fun s => cyclicLift_subset (other o) (PF o s) ((hfinite o).1 s).2
  have hexhaust (o : Bool) : ∀ v ∈ other o, ∀ᶠ s in U, v ∈ E o s := by
    intro v hv
    exact (cyclicLift_exhaustion (other o) (fun s => (q o s : ℕ)) (hq o) (PF o)
      (hfinite o).2.1 v hv).filter_mono hU
  have hP0 (o : Bool) : Loeb.internalSet U
      (fun s => ((↑) : ℕ → ZMod (q o s : ℕ)) '' E o s)
      =ᵐ[Loeb.loebMeasure U hU] Loeb.internalSet U
        (fun s => (cyclicWindow (other o) 0 (q o s : ℕ) : Set (ZMod (q o s : ℕ)))) := by
    simpa only [himage] using Loeb.loeb_finite_prefix_agreement U hU (q o) (hq o)
      (other o) (db o) (hdensity o) (PF o)
      (fun s => ((hfinite o).1 s).2) (hfinite o).2.2.2.1
  have hmMoving (o : Bool) : (Loeb.loebMeasure U hU (Loeb.internalSet U
      (fun s => (cyclicWindow (moving o) (start s) (q o s : ℕ) :
        Set (ZMod (q o s : ℕ)))))).toReal = da o :=
    Loeb.loeb_finset_measure_eq U hU (q o) _ (da o) (hMovingCount o)
  have hmOther (o : Bool) : (Loeb.loebMeasure U hU (Loeb.internalSet U
      (fun s => (cyclicWindow (other o) (start s) (q o s : ℕ) :
        Set (ZMod (q o s : ℕ)))))).toReal = db o :=
    Loeb.loeb_finset_measure_eq U hU (q o) _ (db o) (hOtherCount o)
  have hmC (o : Bool) : (Loeb.loebMeasure U hU (Loeb.internalSet U
      (fun s => (cyclicWindow (A + B) (start s) (q o s : ℕ) :
        Set (ZMod (q o s : ℕ)))))).toReal = c := by
    have hc := Loeb.loeb_finset_measure_eq U hU (q o)
      (fun s => cyclicWindow (moving o + other o) (start s) (q o s : ℕ)) c
        (hfinite o).2.2.2.2.1
    cases o
    · exact hc
    · simpa [moving, other, add_comm B A] using hc
  have hmE (o : Bool) : (Loeb.loebMeasure U hU (Loeb.internalSet U
      (fun s => ((↑) : ℕ → ZMod (q o s : ℕ)) '' E o s))).toReal = db o := by
    simpa only [himage] using Loeb.loeb_finset_measure_eq U hU (q o) (PF o) (db o)
      (hfinite o).2.2.2.1
  have hsum (o : Bool) : Loeb.internalSet U (D o) +
      Loeb.internalSet U (fun s => ((↑) : ℕ → ZMod (q o s : ℕ)) '' E o s)
      ≤ᵐ[Loeb.loebMeasure U hU] Loeb.internalSet U
        (fun s => (cyclicWindow (A + B) (start s) (q o s : ℕ) : Set (ZMod (q o s : ℕ)))) := by
    have hs := Loeb.loeb_cyclic_sum_ae_subset U hU (q o) (DF o) (PF o)
      (fun s => cyclicWindow (moving o + other o) (start s) (q o s : ℕ))
        (hfinite o).2.2.2.2.2
    cases o
    · simpa [D, himage, moving, other] using hs
    · simpa [D, himage, moving, other, add_comm B A] using hs
  obtain ⟨o, hnull⟩ := hlocal q hdiv hq H hH hHq hqgap start D E
    hDsub hDAE hEsub hexhaust hP0 hmMoving hmOther hmC hmE hsum
  have hsmall := loeb_window_null_tendsto_common_length U hU T start H (q o)
    hH (hHq o) (hqgap o) hnull
  change Tendsto (fun s => ((cyclicWindow T (start s) (H s)).card : ℝ) / H s)
    (U : Filter ℕ) (𝓝 0) at hsmall
  have hbad : ∀ᶠ s in U, δ / 4 ≤
      ((cyclicWindow T (start s) (H s)).card : ℝ) / H s := by
    filter_upwards [hnS.filter_mono hU] with s hs
    exact (mem_filter.mp hs).2
  obtain ⟨s, hs, ht⟩ := (hbad.and
    (hsmall.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < δ / 4)))).exists
  exact (not_lt_of_ge hs) ht

end Erdos335.IntermediateScale

end
