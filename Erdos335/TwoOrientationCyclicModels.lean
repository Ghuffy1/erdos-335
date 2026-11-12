import Erdos335.JointIntermediateFourierModels
import Erdos335.JointCyclicModels

/-!
# The two sumset orientations on common-start windows
-/

set_option autoImplicit false

open Filter Set Topology
open scoped Pointwise

namespace Erdos335.IntermediateScale

theorem exists_two_orientation_cyclic_models
    (N : ℕ → ℕ) [∀ s, NeZero (N s)]
    (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (hprev : Tendsto (fun s => (N (s - 1) : ℝ) / N s) atTop (𝓝 0))
    (lower upper : ℕ → ℕ)
    (hlower : Tendsto lower atTop atTop) (hupper : Tendsto upper atTop atTop)
    (hgap : Tendsto (fun s => (upper s : ℝ) / lower s) atTop atTop)
    (hupperN : ∀ᶠ s in atTop, upper s ≤ N s)
    (A B : Set ℕ) (a b c : ℝ) (hA : HasDensity A a) (hB : HasDensity B b)
    (hAe : Tendsto (fun s => prefixError A a (N s) / lower s) atTop (𝓝 0))
    (hBe : Tendsto (fun s => prefixError B b (N s) / lower s) atTop (𝓝 0))
    (hCe : Tendsto (fun s => prefixError (A + B) c (N s) / lower s) atTop (𝓝 0))
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
    ∃ (τ H start : ℕ → ℕ) (q : Bool → ℕ → ℕ+),
      StrictMono τ ∧ (∀ s, 0 < H s) ∧ Tendsto H atTop atTop ∧
      Tendsto (fun s => (H s : ℝ) / N (τ s)) atTop (𝓝 0) ∧
      (∀ s, 0 < start s) ∧ ∀ i : Bool,
      (∀ s, H s ≤ (q i s : ℕ)) ∧ Tendsto (fun s => (q i s : ℕ)) atTop atTop ∧
      Tendsto (fun s => (((q i s : ℕ) - H s : ℕ) : ℝ) / (q i s : ℕ)) atTop (𝓝 0) ∧
      Tendsto (fun s => ((q i s : ℕ) : ℝ) / N (τ s)) atTop (𝓝 0) ∧
      Tendsto (fun s => (lower (τ s) : ℝ) / (q i s : ℕ)) atTop (𝓝 0) ∧
      (∀ M : ℕ, 0 < M → ∀ᶠ s in atTop, M ∣ (q i s : ℕ)) ∧
      (∀ᶠ s in atTop, start s + (q i s : ℕ) ≤ N (τ s)) ∧
      ∃ D E : ∀ s, Finset (ZMod (q i s : ℕ)),
        (∀ s, D s ⊆ cyclicWindow (cond i B A) (start s) (q i s : ℕ) ∧
          E s ⊆ cyclicWindow (cond i A B) 0 (q i s : ℕ)) ∧
        (∀ v ∈ cond i A B, ∀ᶠ s in atTop, (v : ZMod (q i s : ℕ)) ∈ E s) ∧
        Tendsto (fun s => ((D s).card : ℝ) / (q i s : ℕ)) atTop (𝓝 (cond i b a)) ∧
        Tendsto (fun s => ((E s).card : ℝ) / (q i s : ℕ)) atTop (𝓝 (cond i a b)) ∧
        Tendsto (fun s => ((cyclicWindow (A + B) (start s) (q i s : ℕ)).card : ℝ) /
          (q i s : ℕ)) atTop (𝓝 c) ∧
        Tendsto (fun s => (((D s + E s) \ cyclicWindow (A + B) (start s) (q i s : ℕ)).card : ℝ) /
          (q i s : ℕ)) atTop (𝓝 0) := by
  classical
  have hFa (n : ℕ) : A.indicator (fun _ => (1 : ℝ)) n ∈ Icc (0 : ℝ) 1 := by
    by_cases hn : n ∈ A <;> simp [hn]
  have hFb (n : ℕ) : B.indicator (fun _ => (1 : ℝ)) n ∈ Icc (0 : ℝ) 1 := by
    by_cases hn : n ∈ B <;> simp [hn]
  obtain ⟨τ, L, V, hτ, hp, hpos, hL, hlo, hLV, hhi, ⟨mA⟩, ⟨mB⟩⟩ :=
    exists_joint_intermediate_fourier_models N hN hmono hprev lower upper hlower hupper hgap
      hupperN (A.indicator (fun _ => (1 : ℝ))) (B.indicator (fun _ => (1 : ℝ))) hFa hFb U hU
  let X : Bool → Set ℕ := fun i => cond i B A
  let Y : Bool → Set ℕ := fun i => cond i A B
  let x : Bool → ℝ := fun i => cond i b a
  let y : Bool → ℝ := fun i => cond i a b
  have hmodels : ∀ i, IntermediateFourierModel ((X i).indicator (fun _ => (1 : ℝ))) (N ∘ τ) L V := by
    intro i
    cases i
    · exact mA
    · exact mB
  have hY : ∀ i, HasDensity (Y i) (y i) := by
    intro i
    cases i
    · exact hB
    · exact hA
  have herrors (S : Set ℕ) (d : ℝ)
      (he : Tendsto (fun s => prefixError S d (N s) / lower s) atTop (𝓝 0)) :
      Tendsto (fun s => prefixError S d (N (τ s)) / L s) atTop (𝓝 0) := by
    have ht := (he.comp hτ.tendsto_atTop).mul hlo
    simp only [mul_zero] at ht
    apply ht.congr'
    filter_upwards [(hlower.comp hτ.tendsto_atTop).eventually (eventually_gt_atTop 0)] with s hs
    have hl : (lower (τ s) : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
    dsimp only [Function.comp_def]
    field_simp
  have hXe : ∀ i, Tendsto (fun s => prefixError (X i) (x i) (N (τ s)) / L s) atTop (𝓝 0) := by
    intro i
    cases i
    · exact herrors A a hAe
    · exact herrors B b hBe
  have hXYe : ∀ i, Tendsto (fun s => prefixError (X i + Y i) c (N (τ s)) / L s) atTop (𝓝 0) := by
    intro i
    cases i
    · exact herrors (A + B) c hCe
    · simpa only [X, Y, Bool.cond_true, add_comm B A] using herrors (A + B) c hCe
  have hVN : Tendsto (fun s => (V s : ℝ) / N (τ s)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun s => by positivity) ?_ hhi
    filter_upwards [hτ.tendsto_atTop.eventually hupperN,
      (hupper.comp hτ.tendsto_atTop).eventually (eventually_gt_atTop 0)] with s hs hp
    exact div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hp) (by exact_mod_cast hs)
  obtain ⟨H, start, q, hHpos, hHtop, hHN, hstart, hq⟩ :=
    exists_joint_cyclic_models X Y x y (fun _ => c) hY (N ∘ τ) L V
      (fun s => NeZero.pos (N (τ s))) (fun s => (hpos s).1) (fun s => (hpos s).2)
      hL hLV hVN hmodels hXe hXYe
  refine ⟨τ, H, start, q, hτ, hHpos, hHtop, hHN, hstart, ?_⟩
  intro i
  obtain ⟨hHq, hqtop, hqgap, hqN, hLq, hqdiv, hinside, D, E, hsub,
    hexhaust, hD, hE, hC, hsum⟩ := hq i
  have hlowq := window_ratio_tendsto_zero_of_intermediate (fun s => (q i s : ℕ)) L (lower ∘ τ)
    (fun s => (hpos s).1) hlo hLq
  refine ⟨hHq, hqtop, hqgap, hqN, hlowq, hqdiv, hinside, D, E, hsub,
    hexhaust, hD, hE, ?_, ?_⟩
  · cases i <;> simpa only [X, Y, Bool.cond_false, Bool.cond_true, add_comm B A] using hC
  · cases i <;> simpa only [X, Y, Bool.cond_false, Bool.cond_true, add_comm B A] using hsum

end Erdos335.IntermediateScale
