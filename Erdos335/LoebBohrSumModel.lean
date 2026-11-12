import Erdos335.LoebBohrPairProfiles

/-!
# Sum containers and exact sum models for internal Bohr pairs
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance bohrSumModelLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem internalBohrCoset_add_subset
    (U : Ultrafilter ℕ) (q : ℕ → ℕ+) (m : ℕ+)
    (ρ : ∀ n, ZMod (q n : ℕ) →+ ZMod (m : ℕ))
    (χ : ∀ n, ZMod (q n : ℕ) →+ AddCircle (1 : ℝ))
    (a b : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
    (x y : AddCircle (1 : ℝ)) (s t : ℝ) :
    internalBohrCoset U q m ρ χ a x s + internalBohrCoset U q m ρ χ b y t ⊆
      internalBohrCoset U q m ρ χ (a + b) (x + y) (s + t) := by
  rintro z ⟨u, hu, v, hv, rfl⟩
  obtain ⟨k, hk, hku⟩ := hu.1
  obtain ⟨l, hl, hlv⟩ := hv.1
  constructor
  · refine ⟨k + l, (finiteQuotient U ρ).ker.add_mem hk hl, ?_⟩
    change (a + b) + (k + l) = u + v
    change a + k = u at hku
    change b + l = v at hlv
    rw [← hku, ← hlv]
    abel
  · obtain ⟨c, ⟨r, hr, hrc⟩, hc⟩ := hu.2
    obtain ⟨d, ⟨w, hw, hwd⟩, hd⟩ := hv.2
    refine ⟨c + d, ⟨r + w, ⟨add_nonneg hr.1 hw.1, add_le_add hr.2 hw.2⟩, ?_⟩, ?_⟩
    · rw [AddCircle.coe_add, hrc, hwd]
    · change (x + y) + (c + d) = ultralimitAddHom U χ (u + v)
      rw [map_add, ← hc, ← hd]
      change (x + y) + (c + d) = (x + c) + (y + d)
      abel

theorem internalBohrCoset_measure_toReal
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+) (m : ℕ+)
    (hd : ∀ᶠ n in U, (m : ℕ) ∣ (q n : ℕ))
    (ρ : ∀ n, ZMod (q n : ℕ) →+ ZMod (m : ℕ))
    (hρ : ∀ᶠ n in U, ∀ k : ℕ, ρ n (k : ZMod (q n : ℕ)) = (k : ZMod (m : ℕ)))
    (χ : ∀ n, ZMod (q n : ℕ) →+ AddCircle (1 : ℝ))
    (hχ : Function.Surjective (ultralimitAddHom U χ))
    (a : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
    (x : AddCircle (1 : ℝ)) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (loebMeasure U hU (internalBohrCoset U q m ρ χ a x s)).toReal = s / (m : ℕ) := by
  let C := internalBohrCoset U q m ρ χ a x s
  have heq := finiteQuotient_eq_of_eventually_natural U q m ρ
    (fun n => naturalCyclicProjection (q n) m) hρ
    (hd.mono fun n hn k => naturalCyclicProjection_natCast (q n) m hn k)
  have hsub : C ⊆ (finiteQuotient U ρ) ⁻¹' {finiteQuotient U ρ a} := by
    have hh : C ⊆ a +ᵥ ((finiteQuotient U ρ).ker : Set _) := inter_subset_left
    rwa [← addHom_fiber_eq_coset] at hh
  have hp := loeb_natural_bohr_residue_profile U hU q m m hd dvd_rfl χ hχ a x s hs0 hs1
    (finiteQuotient U (fun n => naturalCyclicProjection (q n) m) a)
  have hid : naturalCyclicProjection m m = AddMonoidHom.id (ZMod (m : ℕ)) := by
    ext r
    rw [naturalCyclicProjection_val m m dvd_rfl, ZMod.natCast_zmod_val]
    rfl
  rw [hid, AddMonoidHom.id_apply, if_pos rfl] at hp
  simp only [internalBohrCoset, ← heq] at hp
  change loebResidueProfile U hU q m C (finiteQuotient U ρ a) = s at hp
  unfold loebResidueProfile at hp
  rw [← heq, inter_eq_self_of_subset_left hsub] at hp
  apply (eq_div_iff (by exact_mod_cast m.ne_zero : ((m : ℕ) : ℝ) ≠ 0)).mpr
  simpa only [mul_comm] using hp

theorem InternalBohrPairData.sum_model
    {U : Ultrafilter ℕ} {hU : (U : Filter ℕ) ≤ atTop} {q : ℕ → ℕ+}
    {A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))}
    (b : InternalBohrPairData U hU q A B) (hSm : MeasurableSet (A + B))
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B) :
    A + B =ᵐ[loebMeasure U hU]
      internalBohrCoset U q b.modulus b.residue b.character (b.left_anchor + b.right_anchor)
        (b.left_start + b.right_start) (b.left_length + b.right_length) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ : Measure G := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let C := internalBohrCoset U q b.modulus b.residue b.character (b.left_anchor + b.right_anchor)
    (b.left_start + b.right_start) (b.left_length + b.right_length)
  have hd : ∀ᶠ n in U, (b.modulus : ℕ) ∣ (q n : ℕ) := by
    filter_upwards [b.natural_residue] with n hn
    have hh := hn.2 (q n : ℕ)
    rw [ZMod.natCast_self, map_zero] at hh
    exact (ZMod.natCast_eq_zero_iff (q n : ℕ) (b.modulus : ℕ)).mp hh.symm
  have mass (a : G) (x : AddCircle (1 : ℝ)) (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1) :=
    internalBohrCoset_measure_toReal U hU q b.modulus hd b.residue
      (b.natural_residue.mono fun n hn => hn.2) b.character b.character_surjective a x s h0 h1
  have hA : (μ A).toReal = b.left_length / (b.modulus : ℕ) :=
    (congrArg ENNReal.toReal (measure_congr b.left_model)).trans
      (mass _ _ _ b.left_positive.le (by linarith [b.length_sum_lt_one, b.right_positive]))
  have hB : (μ B).toReal = b.right_length / (b.modulus : ℕ) :=
    (congrArg ENNReal.toReal (measure_congr b.right_model)).trans
      (mass _ _ _ b.right_positive.le (by linarith [b.length_sum_lt_one, b.left_positive]))
  have hC : (μ C).toReal = (b.left_length + b.right_length) / (b.modulus : ℕ) :=
    mass _ _ _ (add_nonneg b.left_positive.le b.right_positive.le) b.length_sum_lt_one.le
  have heq : μ (A + B) = μ C := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top μ _)).mp
    rw [hfull, ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _), hA, hB, hC, add_div]
  have hsub : A + B ⊆ C := (add_subset_add b.left_containment b.right_containment).trans
    (internalBohrCoset_add_subset U q b.modulus b.residue b.character b.left_anchor b.right_anchor
      b.left_start b.right_start b.left_length b.right_length)
  exact ae_eq_of_ae_subset_of_measure_ge hsub.eventuallySubset heq.symm.le hSm.nullMeasurableSet (measure_ne_top μ _)

end Erdos335.Loeb

end
