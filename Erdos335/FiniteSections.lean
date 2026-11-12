import Erdos335.BlockCounting
import Erdos335.RunIntervals

/-!
# Positive residue sections and finite frames

These lemmas use the exact positive-index sections in the full target. Initial
points and the zero residue are retained in the counting identities.
-/

set_option autoImplicit false

open Filter Topology
open scoped Pointwise

namespace Erdos335.Proposed

def zeroSection (A : Set ℕ) (q : ℕ+) (r : ZMod (q : ℕ)) : Set ℕ :=
  {k | (q : ℕ) * k + r.val ∈ A}

theorem section_eq_zeroSection (A : Set ℕ) (q : ℕ+) (r : ZMod (q : ℕ))
    (hA : A ⊆ Set.Ioi 0) :
    residueSection A q r = if r.val = 0 then zeroSection A q r else shift (zeroSection A q r) 1 := by
  classical
  split_ifs with hr
  ·
    have hrep : positiveRepresentative q r = q := by simp [positiveRepresentative, hr]
    ext k
    have hpoint (hk : 0 < k) : (q : ℕ) * (k - 1) + (q : ℕ) = (q : ℕ) * k := by
      calc
        (q : ℕ) * (k - 1) + (q : ℕ) = (q : ℕ) * ((k - 1) + 1) := by ring
        _ = (q : ℕ) * k := by rw [Nat.sub_add_cancel hk]
    constructor
    · rintro ⟨hk, ha⟩
      change (q : ℕ) * k + r.val ∈ A
      simpa only [hrep, hpoint hk, hr, add_zero] using ha
    · intro ha
      change (q : ℕ) * k + r.val ∈ A at ha
      have hk : 0 < k := by
        by_contra hk
        have hk0 : k = 0 := by omega
        have ha0 := hA ha
        simp [hk0, hr] at ha0
      refine ⟨hk, ?_⟩
      simpa only [hrep, hpoint hk, hr, add_zero] using ha
  ·
    have hrep : positiveRepresentative q r = r.val := by simp [positiveRepresentative, hr]
    ext k
    constructor
    · rintro ⟨hk, ha⟩
      refine ⟨k - 1, ?_, Nat.sub_add_cancel hk⟩
      change (q : ℕ) * (k - 1) + r.val ∈ A
      simpa only [hrep] using ha
    · rintro ⟨j, hj, rfl⟩
      refine ⟨by change 0 < j + 1; omega, ?_⟩
      change (q : ℕ) * (j + 1 - 1) + positiveRepresentative q r ∈ A
      change (q : ℕ) * j + r.val ∈ A at hj
      simpa only [hrep, Nat.add_sub_cancel] using hj

theorem hasDensity_zeroSection {A : Set ℕ} {q : ℕ+} {r : ZMod (q : ℕ)} {d : ℝ}
    (hA : A ⊆ Set.Ioi 0) (h : HasDensity (residueSection A q r) d) :
    HasDensity (zeroSection A q r) d := by
  rw [section_eq_zeroSection A q r hA] at h
  split_ifs at h with hr
  · exact h
  · exact (hasDensity_shift_iff _ 1 d).mp h

theorem prefixCount_residueFiber (A : Set ℕ) (q : ℕ+) (r : ZMod (q : ℕ))
    (hA : A ⊆ Set.Ioi 0) (N : ℕ) :
    prefixCount (residueFiber A r) ((q : ℕ) * N) = prefixCount (zeroSection A q r) N := by
  classical
  symm
  apply Finset.card_bij (fun k _ => (q : ℕ) * k + r.val)
  · intro k hk
    obtain ⟨hk, ha⟩ := Finset.mem_filter.mp hk
    have hkN := Finset.mem_range.mp hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := r.val_lt; nlinarith), ?_⟩
    refine ⟨ha, hA ha, ?_⟩
    simp
  · intro k hk j hj hkj
    exact Nat.eq_of_mul_eq_mul_left q.pos (Nat.add_right_cancel hkj)
  · intro n hn
    obtain ⟨hnN, hn⟩ := Finset.mem_filter.mp hn
    have hnlt := Finset.mem_range.mp hnN
    have hnr : (n : ZMod (q : ℕ)) = r := by simpa using hn.2.2
    have hnval : n % (q : ℕ) = r.val := by
      simpa only [ZMod.val_natCast] using congrArg ZMod.val hnr
    have hpoint : (q : ℕ) * (n / (q : ℕ)) + r.val = n := by
      have h := Nat.mod_add_div n (q : ℕ)
      omega
    refine ⟨n / (q : ℕ), Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩, hpoint⟩
    · exact (Nat.div_lt_iff_lt_mul q.pos).mpr (by simpa only [Nat.mul_comm] using hnlt)
    · change (q : ℕ) * (n / (q : ℕ)) + r.val ∈ A
      simpa only [hpoint] using hn.1

theorem hasDensity_residueFiber {A : Set ℕ} {q : ℕ+} {r : ZMod (q : ℕ)} {d : ℝ}
    (hA : A ⊆ Set.Ioi 0) (h : HasDensity (residueSection A q r) d) :
    HasDensity (residueFiber A r) (d / q) := by
  have hz := hasDensity_zeroSection hA h
  have hp := ((hasDensity_iff_prefixCount (zeroSection A q r) d).mp hz).div_const (q : ℝ)
  apply (hasDensity_iff_prefixCount_multiples (residueFiber A r) q (d / q)).mpr
  apply hp.congr
  intro N
  rw [prefixCount_residueFiber A q r hA N]
  simp only [Nat.cast_mul]
  rw [div_div, mul_comm (N : ℝ) (q : ℝ)]

theorem full_residueFiber {A : Set ℕ} {q : ℕ+} {r : ZMod (q : ℕ)}
    (hA : A ⊆ Set.Ioi 0) (h : HasDensity (residueSection A q r) 1) :
    DensityEquivalent (residueFiber A r) (periodicSet ({r} : Finset (ZMod (q : ℕ)))) := by
  classical
  have hf := hasDensity_residueFiber hA h
  have hsub : residueFiber A r ⊆ periodicSet ({r} : Finset (ZMod (q : ℕ))) :=
    fun _ hn => hn.2
  have hout : Negligible (residueFiber A r \ periodicSet ({r} : Finset (ZMod (q : ℕ)))) := by
    apply (show Negligible (∅ : Set ℕ) from hasDensity_empty).mono
    rintro n ⟨hn, hnot⟩
    exact (hnot (hsub hn)).elim
  refine ⟨hout, ?_⟩
  have hd := (hasDensity_periodicSet ({r} : Finset (ZMod (q : ℕ)))).sdiff_of_negligible_reverse hf hout
  change HasDensity (periodicSet {r} \ residueFiber A r) 0
  simpa only [Finset.card_singleton, Nat.cast_one, sub_self] using hd

theorem hasDensity_union_of_disjoint {A B : Set ℕ} {a b : ℝ}
    (hA : HasDensity A a) (hB : HasDensity B b) (hdisjoint : Disjoint A B) :
    HasDensity (A ∪ B) (a + b) := by
  have h := hA.add hB
  apply h.congr
  intro N
  rw [count_union_of_disjoint A B hdisjoint, Nat.cast_add, add_div]

theorem positiveRepresentative_pos (q : ℕ+) (r : ZMod (q : ℕ)) :
    0 < positiveRepresentative q r := by
  unfold positiveRepresentative
  split_ifs with hr
  · exact q.pos
  · exact Nat.pos_of_ne_zero hr

theorem positiveRepresentative_cast (q : ℕ+) (r : ZMod (q : ℕ)) :
    ((positiveRepresentative q r : ℕ) : ZMod (q : ℕ)) = r := by
  unfold positiveRepresentative
  split_ifs with hr
  · rw [ZMod.natCast_self]
    exact (r.val_eq_zero.mp hr).symm
  · exact ZMod.natCast_zmod_val r

def sectionPoint (q : ℕ+) (r : ZMod (q : ℕ)) (k : ℕ) : ℕ :=
  (q : ℕ) * (k - 1) + positiveRepresentative q r

theorem sectionPoint_pos (q : ℕ+) (r : ZMod (q : ℕ)) (k : ℕ) :
    0 < sectionPoint q r k :=
  Nat.add_pos_right _ (positiveRepresentative_pos q r)

theorem sectionPoint_cast (q : ℕ+) (r : ZMod (q : ℕ)) (k : ℕ) :
    ((sectionPoint q r k : ℕ) : ZMod (q : ℕ)) = r := by
  simp only [sectionPoint, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul,
    zero_add, positiveRepresentative_cast]

theorem residueFiber_eq_image (A : Set ℕ) (q : ℕ+) (r : ZMod (q : ℕ)) :
    residueFiber A r = sectionPoint q r '' residueSection A q r := by
  classical
  ext n
  constructor
  · rintro ⟨ha, hn0, hnres⟩
    have hnr : (n : ZMod (q : ℕ)) = r := by simpa using hnres
    have hnval : n % (q : ℕ) = r.val := by
      simpa only [ZMod.val_natCast] using congrArg ZMod.val hnr
    have hdecomp : (q : ℕ) * (n / (q : ℕ)) + r.val = n := by
      have h := Nat.mod_add_div n (q : ℕ)
      omega
    by_cases hr : r.val = 0
    · have hk : 0 < n / (q : ℕ) := by
        by_contra hk
        have hk0 : n / (q : ℕ) = 0 := Nat.eq_zero_of_not_pos hk
        simp only [hk0, hr, mul_zero, add_zero] at hdecomp
        omega
      have hpoint : sectionPoint q r (n / (q : ℕ)) = n := by
        have hrep : positiveRepresentative q r = q := by simp [positiveRepresentative, hr]
        dsimp only [sectionPoint]
        rw [hrep]
        calc
          (q : ℕ) * (n / (q : ℕ) - 1) + (q : ℕ) =
              (q : ℕ) * ((n / (q : ℕ) - 1) + 1) := by ring
          _ = (q : ℕ) * (n / (q : ℕ)) := by rw [Nat.sub_add_cancel hk]
          _ = n := by simpa only [hr, add_zero] using hdecomp
      refine ⟨n / (q : ℕ), ⟨hk, ?_⟩, hpoint⟩
      change sectionPoint q r (n / (q : ℕ)) ∈ A
      rw [hpoint]
      exact ha
    · have hpoint : sectionPoint q r (n / (q : ℕ) + 1) = n := by
        simpa only [sectionPoint, positiveRepresentative, hr, ite_false, Nat.add_sub_cancel]
          using hdecomp
      refine ⟨n / (q : ℕ) + 1, ⟨Nat.succ_pos _, ?_⟩, hpoint⟩
      change sectionPoint q r (n / (q : ℕ) + 1) ∈ A
      rw [hpoint]
      exact ha
  · rintro ⟨k, hk, rfl⟩
    exact ⟨hk.2, sectionPoint_pos q r k, by simpa only [Finset.mem_singleton] using sectionPoint_cast q r k⟩

theorem singleton_residueFiber {A : Set ℕ} {q : ℕ+} {r : ZMod (q : ℕ)} {k : ℕ}
    (h : residueSection A q r = {k}) : residueFiber A r = {sectionPoint q r k} := by
  rw [residueFiber_eq_image A q r, h]
  exact Set.image_singleton

theorem missing_fiber_of_full_section {A : Set ℕ} {q : ℕ+} {r : ZMod (q : ℕ)}
    (hA : A ⊆ Set.Ioi 0) (h : HasDensity (residueSection A q r) 1) :
    Negligible (periodicSet ({r} : Finset (ZMod (q : ℕ))) \ A) := by
  apply (full_residueFiber hA h).2.mono
  rintro n ⟨hn, hout⟩
  exact ⟨hn, fun hF => hout hF.1⟩

theorem hasDensity_from_residue_background (A : Set ℕ) (q : ℕ+)
    (i : ZMod (q : ℕ)) (d : ℝ) (hA : A ⊆ Set.Ioi 0)
    (hi : i ∈ residues (q : ℕ) A)
    (hbackground : ∀ r ∈ residues (q : ℕ) A, r ≠ i →
      Negligible (periodicSet ({r} : Finset (ZMod (q : ℕ))) \ A))
    (hactive : HasDensity (residueFiber A i) d) :
    HasDensity A ((((residues (q : ℕ) A).card : ℝ) - 1) / q + d) := by
  classical
  let U := (residues (q : ℕ) A).erase i
  have hholes : Negligible (periodicSet U \ A) := by
    apply negligible_periodic_diff_of_singletons
    intro r hr
    have hr' := Finset.mem_erase.mp hr
    exact hbackground r hr'.2 hr'.1
  have hsub : A ⊆ periodicSet U ∪ residueFiber A i := by
    intro n hn
    have hn0 : 0 < n := hA hn
    have hnr : (n : ZMod (q : ℕ)) ∈ residues (q : ℕ) A := mem_residues.mpr ⟨n, hn, rfl⟩
    by_cases hni : (n : ZMod (q : ℕ)) = i
    · exact Or.inr ⟨hn, hn0, by simpa only [Finset.mem_singleton] using hni⟩
    · exact Or.inl ⟨hn0, Finset.mem_erase.mpr ⟨hni, hnr⟩⟩
  have heq : DensityEquivalent A (periodicSet U ∪ residueFiber A i) := by
    constructor
    · apply (show Negligible (∅ : Set ℕ) from hasDensity_empty).mono
      rintro n ⟨hn, hout⟩
      exact (hout (hsub hn)).elim
    · apply hholes.mono
      rintro n ⟨hn, hout⟩
      rcases hn with hn | hn
      · exact ⟨hn, hout⟩
      · exact (hout hn.1).elim
  have hdisjoint : Disjoint (periodicSet U) (residueFiber A i) := by
    apply Set.disjoint_left.mpr
    intro n hnU hni
    have hnval : (n : ZMod (q : ℕ)) = i := by simpa using hni.2.2
    exact (Finset.mem_erase.mp hnU.2).1 hnval
  have hUnion := hasDensity_union_of_disjoint (hasDensity_periodicSet U) hactive hdisjoint
  have hcard : (U.card : ℝ) = ((residues (q : ℕ) A).card : ℝ) - 1 := by
    have hc : U.card + 1 = (residues (q : ℕ) A).card := Finset.card_erase_add_one hi
    have hc' : (U.card : ℝ) + 1 = ((residues (q : ℕ) A).card : ℝ) := by exact_mod_cast hc
    linarith
  simpa only [hcard] using heq.symm.hasDensity hUnion

theorem missing_output_of_full_right {A B : Set ℕ} {q : ℕ+}
    {r t : ZMod (q : ℕ)}
    (hB : DensityEquivalent (residueFiber B t) (periodicSet ({t} : Finset (ZMod (q : ℕ)))))
    (hr : r ∈ residues (q : ℕ) A) :
    Negligible (periodicSet ({r + t} : Finset (ZMod (q : ℕ))) \ (A + B)) := by
  have h := missing_left_baseline_singleton hB
    (Finset.add_mem_add hr (Finset.mem_singleton_self t))
  apply h.mono
  rintro n ⟨hn, hout⟩
  refine ⟨hn, ?_⟩
  rintro ⟨a, ha, b, hb, hab⟩
  exact hout ⟨a, ha, b, hb.1, hab⟩

end Erdos335.Proposed
