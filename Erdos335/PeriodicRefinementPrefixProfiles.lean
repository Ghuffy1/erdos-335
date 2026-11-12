import Erdos335.PeriodicRefinementLabelClosureCore
import Erdos335.DysonCounting
import Erdos335.DensityLimits
import Mathlib.Topology.Sequences

/-!
# Ordinary residue-prefix limits as literal local profiles

Private proof development. Verification status is recorded separately.
All limits below are taken along the supplied ordinary cutoff sequence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology
open Erdos335.PeriodicRefinementLabelClosure
open scoped Pointwise BigOperators

noncomputable section

namespace Erdos335.PeriodicRefinement

def literalResidue (A : Set ℕ) (M : ℕ+) (r : ZMod (M : ℕ)) : Set ℕ :=
  {n | n ∈ A ∧ (n : ZMod (M : ℕ)) = r}

def normalizedResiduePrefix (A : Set ℕ) (M : ℕ+) (N : ℕ) : ZMod (M : ℕ) → ℝ :=
  fun r => ((M : ℕ) : ℝ) * ((prefixCount (literalResidue A M r) N : ℝ) / N)

theorem literal_residue_prefix_sum (A : Set ℕ) (M : ℕ+) (N : ℕ) :
    (∑ r : ZMod (M : ℕ), (prefixCount (literalResidue A M r) N : ℝ)) =
      (prefixCount A N : ℝ) := by
  classical
  let F := (Finset.range N).filter (fun n => n ∈ A)
  have hsum := Finset.sum_fiberwise' F (fun n : ℕ => (n : ZMod (M : ℕ)))
    (fun _ => (1 : ℝ))
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, F,
    Finset.filter_filter, prefixCount, literalResidue, Set.mem_setOf_eq] using hsum

theorem normalized_residue_prefix_sum (A : Set ℕ) (M : ℕ+) (N : ℕ) :
    (∑ r, normalizedResiduePrefix A M N r) =
      ((M : ℕ) : ℝ) * ((prefixCount A N : ℝ) / N) := by
  simp only [normalizedResiduePrefix]
  rw [← Finset.mul_sum, ← Finset.sum_div, literal_residue_prefix_sum]

theorem normalized_residue_prefix_nonneg (A : Set ℕ) (M : ℕ+) (N : ℕ)
    (r : ZMod (M : ℕ)) : 0 ≤ normalizedResiduePrefix A M N r := by
  unfold normalizedResiduePrefix
  positivity

theorem normalized_residue_prefix_mono {A B : Set ℕ} (M : ℕ+) (N : ℕ)
    (r : ZMod (M : ℕ)) (hAB : A ⊆ B) :
    normalizedResiduePrefix A M N r ≤ normalizedResiduePrefix B M N r := by
  unfold normalizedResiduePrefix
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hsub : literalResidue A M r ⊆ literalResidue B M r :=
    fun n hn => ⟨hAB hn.1, hn.2⟩
  exact_mod_cast prefixCount_mono_set hsub N

theorem pure_residue_hasDensity (M : ℕ+) (r : ZMod (M : ℕ)) :
    HasDensity {n : ℕ | (n : ZMod (M : ℕ)) = r} (1 / (M : ℕ)) := by
  have hp : HasDensity (periodicSet ({r} : Finset (ZMod (M : ℕ)))) (1 / (M : ℕ)) := by
    simpa only [Finset.card_singleton, Nat.cast_one] using
      hasDensity_periodicSet ({r} : Finset (ZMod (M : ℕ)))
  apply hp.of_eventually_eq 0
  intro n hn
  simp only [periodicSet, Set.mem_setOf_eq, Finset.mem_singleton, hn, true_and]

theorem normalized_residue_prefix_limit_bounds
    (A : Set ℕ) (M : ℕ+) (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (r : ZMod (M : ℕ)) (v : ℝ)
    (hlimit : Tendsto (fun n => normalizedResiduePrefix A M (N n) r) atTop (𝓝 v)) :
    0 ≤ v ∧ v ≤ 1 := by
  constructor
  · exact ge_of_tendsto' hlimit (fun n => normalized_residue_prefix_nonneg A M (N n) r)
  · let R : Set ℕ := {n : ℕ | (n : ZMod (M : ℕ)) = r}
    have hR := ((hasDensity_iff_prefixCount R (1 / (M : ℕ))).mp
      (pure_residue_hasDensity M r)).comp hN
    have hscaled := hR.const_mul ((M : ℕ) : ℝ)
    have hcancel : ((M : ℕ) : ℝ) * (1 / (M : ℕ)) = 1 := by
      have hm : ((M : ℕ) : ℝ) ≠ 0 := by exact_mod_cast M.ne_zero
      field_simp [hm]
    rw [hcancel] at hscaled
    apply le_of_tendsto_of_tendsto' hlimit hscaled
    intro n
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have hsub : literalResidue A M r ⊆ R := fun k hk => hk.2
    exact_mod_cast prefixCount_mono_set hsub (N n)

theorem normalized_residue_prefix_limit_zero
    (A : Set ℕ) (M : ℕ+) (N : ℕ → ℕ) (r : ZMod (M : ℕ)) (v : ℝ)
    (hr : r ∉ residues (M : ℕ) A)
    (hlimit : Tendsto (fun n => normalizedResiduePrefix A M (N n) r) atTop (𝓝 v)) :
    v = 0 := by
  have hset : literalResidue A M r = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro n hn
    exact hr (mem_residues.mpr ⟨n, hn.1, hn.2⟩)
  have hzero : Tendsto (fun n => normalizedResiduePrefix A M (N n) r) atTop (𝓝 0) := by
    simpa [normalizedResiduePrefix, hset, prefixCount] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hlimit hzero

theorem normalized_residue_prefix_limit_mass
    (A : Set ℕ) (M : ℕ+) (a : ℝ) (hA : HasDensity A a)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (v : ZMod (M : ℕ) → ℝ)
    (hlimit : ∀ r, Tendsto (fun n => normalizedResiduePrefix A M (N n) r)
      atTop (𝓝 (v r))) :
    (∑ r, v r) = ((M : ℕ) : ℝ) * a := by
  have hsum := tendsto_finset_sum (Finset.univ : Finset (ZMod (M : ℕ)))
    (fun r hr => hlimit r)
  have htotal := (((hasDensity_iff_prefixCount A a).mp hA).comp hN).const_mul ((M : ℕ) : ℝ)
  have htotal' : Tendsto (fun n => ∑ r, normalizedResiduePrefix A M (N n) r)
      atTop (𝓝 (((M : ℕ) : ℝ) * a)) := by
    simpa only [normalized_residue_prefix_sum, Function.comp_def] using htotal
  exact tendsto_nhds_unique hsum htotal'

theorem prefixCount_translate_le (S T : Set ℕ) (b N : ℕ)
    (hST : shift S b ⊆ T) : prefixCount S N ≤ prefixCount T N + b := by
  classical
  have hfirst : prefixCount S N ≤ prefixCount T (N + b) := by
    unfold prefixCount
    apply Finset.card_le_card_of_injOn (fun n => n + b)
    · intro n hn
      obtain ⟨hnN, hnS⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
        (Nat.add_lt_add_right (Finset.mem_range.mp hnN) b), hST ⟨n, hnS, rfl⟩⟩
    · intro n hn k hk hnk
      exact Nat.add_right_cancel hnk
  exact hfirst.trans (prefixCount_add_le T N b)

theorem fixed_translate_prefix_limit_le
    (S T : Set ℕ) (M : ℕ+) (b : ℕ) (hST : shift S b ⊆ T)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (a c : ℝ)
    (hS : Tendsto (fun n => ((M : ℕ) : ℝ) * ((prefixCount S (N n) : ℝ) / N n))
      atTop (𝓝 a))
    (hT : Tendsto (fun n => ((M : ℕ) : ℝ) * ((prefixCount T (N n) : ℝ) / N n))
      atTop (𝓝 c)) : a ≤ c := by
  have herror : Tendsto (fun n => (((M : ℕ) : ℝ) * b) / N n) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (((M : ℕ) : ℝ) * b)).comp hN
  have hupper : Tendsto (fun n => ((M : ℕ) : ℝ) * ((prefixCount T (N n) : ℝ) / N n) +
      (((M : ℕ) : ℝ) * b) / N n) atTop (𝓝 c) := by
    simpa only [add_zero] using hT.add herror
  apply le_of_tendsto_of_tendsto' hS hupper
  intro n
  have hc : (prefixCount S (N n) : ℝ) ≤ (prefixCount T (N n) : ℝ) + b := by
    exact_mod_cast prefixCount_translate_le S T b (N n) hST
  have hd := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hc (Nat.cast_nonneg (N n)))
      (Nat.cast_nonneg (M : ℕ))
  convert hd using 1 <;> ring

theorem literal_residue_prefix_limit_le
    (A B : Set ℕ) (M : ℕ+) (r v : ZMod (M : ℕ))
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (a c : ℝ)
    (hv : v ∈ residues (M : ℕ) B)
    (hA : Tendsto (fun n => normalizedResiduePrefix A M (N n) r) atTop (𝓝 a))
    (hC : Tendsto (fun n => normalizedResiduePrefix (A + B) M (N n) (r + v)) atTop (𝓝 c)) :
    a ≤ c := by
  obtain ⟨b, hb, hbr⟩ := mem_residues.mp hv
  have hsub : shift (literalResidue A M r) b ⊆ literalResidue (A + B) M (r + v) := by
    rintro n ⟨k, hk, rfl⟩
    refine ⟨⟨k, hk.1, b, hb, rfl⟩, ?_⟩
    simp only [Nat.cast_add, hk.2, hbr]
  exact fixed_translate_prefix_limit_le (literalResidue A M r)
    (literalResidue (A + B) M (r + v)) M b hsub N hN a c hA hC

theorem localProfile_of_residue_prefix_limits
    (A B : Set ℕ) (M : ℕ+) (a b : ℝ)
    (hA : HasDensity A a) (hB : HasDensity B b) (hC : HasDensity (A + B) (a + b))
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (vA vB vC : ZMod (M : ℕ) → ℝ)
    (hLA : ∀ r, Tendsto (fun n => normalizedResiduePrefix A M (N n) r) atTop (𝓝 (vA r)))
    (hLB : ∀ r, Tendsto (fun n => normalizedResiduePrefix B M (N n) r) atTop (𝓝 (vB r)))
    (hLC : ∀ r, Tendsto (fun n => normalizedResiduePrefix (A + B) M (N n) r) atTop (𝓝 (vC r))) :
    ∃ p : LocalProfile (residues (M : ℕ) A) (residues (M : ℕ) B)
        (((M : ℕ) : ℝ) * a) (((M : ℕ) : ℝ) * b),
      p.left = vA ∧ p.right = vB ∧ p.output = vC := by
  let p : LocalProfile (residues (M : ℕ) A) (residues (M : ℕ) B)
      (((M : ℕ) : ℝ) * a) (((M : ℕ) : ℝ) * b) := {
    left := vA
    right := vB
    output := vC
    left_bound := fun r => normalized_residue_prefix_limit_bounds A M N hN r (vA r) (hLA r)
    right_bound := fun r => normalized_residue_prefix_limit_bounds B M N hN r (vB r) (hLB r)
    output_bound := fun r => normalized_residue_prefix_limit_bounds (A + B) M N hN r (vC r) (hLC r)
    left_zero := fun r hr => normalized_residue_prefix_limit_zero A M N r (vA r) hr (hLA r)
    right_zero := fun r hr => normalized_residue_prefix_limit_zero B M N r (vB r) hr (hLB r)
    left_mass := normalized_residue_prefix_limit_mass A M a hA N hN vA hLA
    right_mass := normalized_residue_prefix_limit_mass B M b hB N hN vB hLB
    output_mass := by
      simpa only [mul_add] using normalized_residue_prefix_limit_mass (A + B) M (a + b) hC N hN vC hLC
    literal_left := fun r v hv => literal_residue_prefix_limit_le A B M r v N hN
      (vA r) (vC (r + v)) hv (hLA r) (hLC (r + v))
    literal_right := by
      intro r hr v
      have hc : Tendsto (fun n => normalizedResiduePrefix (B + A) M (N n) (v + r))
          atTop (𝓝 (vC (r + v))) := by
        simpa only [add_comm B A, add_comm v r] using hLC (r + v)
      exact literal_residue_prefix_limit_le B A M v r N hN
        (vB v) (vC (r + v)) hr (hLB v) hc
  }
  exact ⟨p, rfl, rfl, rfl⟩

end Erdos335.PeriodicRefinement

end
