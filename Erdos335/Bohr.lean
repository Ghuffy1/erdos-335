import Erdos335.ArcSum
import Erdos335.Singleton

/-!
# The parallel Bohr-arc branch

Positive-index sections are lifted through a common integer dilation. The
finite-frame theorem then transfers their exact sum density to the full pair.
-/

set_option autoImplicit false

open Filter Topology
open scoped Pointwise

namespace Erdos335.Proposed

def dilate (A : Set ℕ) (q : ℕ+) : Set ℕ := (fun n => (q : ℕ) * n) '' A

theorem dilate_positive {A : Set ℕ} (hA : A ⊆ Set.Ioi 0) (q : ℕ+) :
    dilate A q ⊆ Set.Ioi 0 := by
  rintro n ⟨k, hk, rfl⟩
  exact Nat.mul_pos q.pos (hA hk)

theorem zeroSection_dilate (A : Set ℕ) (q : ℕ+) : zeroSection (dilate A q) q 0 = A := by
  ext k
  change (q : ℕ) * k + (0 : ZMod (q : ℕ)).val ∈ dilate A q ↔ k ∈ A
  simp only [ZMod.val_zero, add_zero]
  constructor
  · rintro ⟨j, hj, h⟩
    have heq : j = k := Nat.eq_of_mul_eq_mul_left q.pos h
    simpa only [heq] using hj
  · intro hk
    exact ⟨k, hk, rfl⟩

theorem residueFiber_dilate (A : Set ℕ) (q : ℕ+) (hA : A ⊆ Set.Ioi 0) :
    residueFiber (dilate A q) (0 : ZMod (q : ℕ)) = dilate A q := by
  ext n
  constructor
  · exact fun hn => hn.1
  · intro hn
    refine ⟨hn, dilate_positive hA q hn, ?_⟩
    obtain ⟨k, hk, rfl⟩ := hn
    simp

theorem hasDensity_dilate {A : Set ℕ} {d : ℝ} (q : ℕ+)
    (hA : A ⊆ Set.Ioi 0) (hd : HasDensity A d) : HasDensity (dilate A q) (d / q) := by
  have hpos := dilate_positive hA q
  have hsection : residueSection (dilate A q) q 0 = A := by
    rw [section_eq_zeroSection _ _ _ hpos]
    simpa only [ZMod.val_zero, ite_true] using zeroSection_dilate A q
  have h := hasDensity_residueFiber hpos (show HasDensity (residueSection (dilate A q) q 0) d from hsection.symm ▸ hd)
  simpa only [residueFiber_dilate A q hA] using h

theorem shift_add (A B : Set ℕ) (s t : ℕ) :
    shift (A + B) (s + t) = shift A s + shift B t := by
  ext n
  constructor
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    refine ⟨a + s, ⟨a, ha, rfl⟩, b + t, ⟨b, hb, rfl⟩, ?_⟩
    change (a + s) + (b + t) = (a + b) + (s + t)
    omega
  · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    refine ⟨a + b, ⟨a, ha, b, hb, rfl⟩, ?_⟩
    change (a + b) + (s + t) = (a + s) + (b + t)
    omega

theorem dilate_add (A B : Set ℕ) (q : ℕ+) :
    dilate (A + B) q = dilate A q + dilate B q := by
  ext n
  constructor
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    refine ⟨(q : ℕ) * a, ⟨a, ha, rfl⟩, (q : ℕ) * b, ⟨b, hb, rfl⟩, ?_⟩
    change (q : ℕ) * a + (q : ℕ) * b = (q : ℕ) * (a + b)
    ring
  · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    refine ⟨a + b, ⟨a, ha, b, hb, rfl⟩, ?_⟩
    change (q : ℕ) * (a + b) = (q : ℕ) * a + (q : ℕ) * b
    ring

theorem sectionPoint_add_modulus (q : ℕ+) (r : ZMod (q : ℕ)) {k : ℕ} (hk : 0 < k) :
    sectionPoint q r k + (q : ℕ) = (q : ℕ) * k + positiveRepresentative q r := by
  unfold sectionPoint
  calc
    ((q : ℕ) * (k - 1) + positiveRepresentative q r) + (q : ℕ) =
        (q : ℕ) * ((k - 1) + 1) + positiveRepresentative q r := by ring
    _ = (q : ℕ) * k + positiveRepresentative q r := by rw [Nat.sub_add_cancel hk]

theorem shift_fiber_eq_dilate (A : Set ℕ) (q : ℕ+) (r : ZMod (q : ℕ)) :
    shift (residueFiber A r) q = shift (dilate (residueSection A q r) q) (positiveRepresentative q r) := by
  rw [residueFiber_eq_image A q r]
  ext n
  constructor
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    refine ⟨(q : ℕ) * k, ⟨k, hk, rfl⟩, ?_⟩
    exact (sectionPoint_add_modulus q r hk.1).symm
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    refine ⟨sectionPoint q r k, ⟨k, hk, rfl⟩, ?_⟩
    exact sectionPoint_add_modulus q r hk.1

theorem fiber_sum_hasDensity {A B : Set ℕ} (q : ℕ+) (r t : ZMod (q : ℕ)) {d : ℝ}
    (h : HasDensity (residueSection A q r + residueSection B q t) d) :
    HasDensity (residueFiber A r + residueFiber B t) (d / q) := by
  have hposA : residueSection A q r ⊆ Set.Ioi 0 := fun _ hn => hn.1
  have hposB : residueSection B q t ⊆ Set.Ioi 0 := fun _ hn => hn.1
  have hd := hasDensity_dilate q (sumset_positive hposA hposB) h
  have hshift := hd.shift (positiveRepresentative q r + positiveRepresentative q t)
  have heq : shift (residueFiber A r + residueFiber B t) ((q : ℕ) + (q : ℕ)) =
      shift (dilate (residueSection A q r + residueSection B q t) q)
        (positiveRepresentative q r + positiveRepresentative q t) := by
    rw [shift_add, shift_fiber_eq_dilate, shift_fiber_eq_dilate, ← shift_add, ← dilate_add]
  rw [← heq] at hshift
  exact (hasDensity_shift_iff _ _ _).mp hshift

theorem BohrBranch.hasDensity {A B : Set ℕ} {a b : ℝ}
    (h : BohrBranch A B) (hApos : A ⊆ Set.Ioi 0) (hBpos : B ⊆ Set.Ioi 0)
    (hA : HasDensity A a) (hB : HasDensity B b) : HasDensity (A + B) (a + b) := by
  obtain ⟨f, θ, startA, startB, lenA, lenB, hθ, hlenA, hlenB, hlen,
    hsubA, hsubB, hholesA, hholesB⟩ := h
  have hDA := filled_closedArc_hasDensity hθ hlenA (by linarith) hsubA hholesA
  have hDB := filled_closedArc_hasDensity hθ hlenB (by linarith) hsubB hholesB
  have hDSum := filled_closedArcs_sum_hasDensity hθ hlenA hlenB hlen.le hsubA hsubB hholesA hholesB
  have hFA := hasDensity_residueFiber hApos hDA
  have hFB := hasDensity_residueFiber hBpos hDB
  apply f.hasDensity_of_active_sum hApos hBpos hA hB hFA hFB
  have hFsum := fiber_sum_hasDensity f.modulus f.activeA f.activeB hDSum
  simpa only [add_div] using hFsum

theorem isErdos335Pair_of_bohrBranch (A B : Set ℕ) (a b : ℝ)
    (hApos : A ⊆ Set.Ioi 0) (hBpos : B ⊆ Set.Ioi 0)
    (ha0 : 0 < a) (hb0 : 0 < b) (hA : HasDensity A a) (hB : HasDensity B b)
    (h : BohrBranch A B) : IsErdos335Pair A B :=
  ⟨hApos, hBpos, a, b, ha0, hb0, hA, hB, h.hasDensity hApos hBpos hA hB⟩

end Erdos335.Proposed
