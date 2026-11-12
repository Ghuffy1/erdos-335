import Erdos335.CircleArcMeasures

/-!
# Addition and containment of short circle arcs
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Pointwise

namespace Erdos335.Loeb

theorem unitCircle_zero_closedArc_add
    (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 p) +
      (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 q) =
        ((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 (p + q) := by
  ext z
  constructor
  · rintro ⟨x, ⟨u, hu, rfl⟩, y, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨u + v, ⟨add_nonneg hu.1 hv.1, add_le_add hu.2 hv.2⟩, AddCircle.coe_add 1 u v⟩
  · rintro ⟨w, hw, rfl⟩
    by_cases hwp : w ≤ p
    · exact ⟨(w : AddCircle (1 : ℝ)), ⟨w, ⟨hw.1, hwp⟩, rfl⟩,
        0, ⟨0, ⟨le_rfl, hq⟩, by simp⟩, by simp⟩
    · have hpw : p < w := lt_of_not_ge hwp
      refine ⟨(p : AddCircle (1 : ℝ)), ⟨p, ⟨hp, le_rfl⟩, rfl⟩,
        ((w - p : ℝ) : AddCircle (1 : ℝ)), ⟨w - p, ⟨by linarith, by linarith [hw.2]⟩, rfl⟩, ?_⟩
      change (p : AddCircle (1 : ℝ)) + ((w - p : ℝ) : AddCircle (1 : ℝ)) = (w : AddCircle (1 : ℝ))
      rw [← AddCircle.coe_add]
      congr 1
      ring

theorem unitCircle_translate_closedArc_subset_iff
    (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hsum : p + q < 1)
    (x : AddCircle (1 : ℝ)) :
    x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 q) ⊆
      (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 (p + q)) ↔
        x ∈ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 p) := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  constructor
  · intro hsub
    have hx : x ∈ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 (p + q)) := by
      have h := hsub (show x + 0 ∈ x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 q) from
        ⟨0, ⟨0, ⟨le_rfl, hq⟩, by simp⟩, rfl⟩)
      simpa only [add_zero] using h
    obtain ⟨u, hu, hueq⟩ := hx
    by_cases hup : u ≤ p
    · exact ⟨u, ⟨hu.1, hup⟩, hueq⟩
    · have hpu : p < u := lt_of_not_ge hup
      let w : ℝ := (p + q + min 1 (u + q)) / 2
      have hmin : p + q < min 1 (u + q) := lt_min hsum (by linarith)
      have hwlow : p + q < w := by dsimp [w]; linarith
      have hwupper : w < min 1 (u + q) := by dsimp [w]; linarith
      have hwone : w < 1 := hwupper.trans_le (min_le_left _ _)
      have hwuq : w < u + q := hwupper.trans_le (min_le_right _ _)
      have hwu : u < w := lt_of_le_of_lt hu.2 hwlow
      have hv : w - u ∈ Icc (0 : ℝ) q := ⟨by linarith, by linarith⟩
      have hcalc : x + ((w - u : ℝ) : AddCircle (1 : ℝ)) = (w : AddCircle (1 : ℝ)) := by
        rw [← hueq, ← AddCircle.coe_add]
        congr 1
        ring
      have hwmem : (w : AddCircle (1 : ℝ)) ∈
          (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 (p + q)) := by
        rw [← hcalc]
        exact hsub ⟨((w - u : ℝ) : AddCircle (1 : ℝ)), ⟨w - u, hv, rfl⟩, rfl⟩
      obtain ⟨v, hvbounds, hveq⟩ := hwmem
      have hvI : v ∈ Ico (0 : ℝ) (0 + 1) := by
        exact ⟨hvbounds.1, by linarith [hvbounds.2]⟩
      have hwI : w ∈ Ico (0 : ℝ) (0 + 1) := ⟨by linarith, by simpa only [zero_add] using hwone⟩
      have hvw : v = w := (AddCircle.coe_eq_coe_iff_of_mem_Ico hvI hwI).mp hveq
      exact False.elim (not_lt_of_ge hvbounds.2 (hvw ▸ hwlow))
  · rintro ⟨u, hu, rfl⟩ z ⟨v, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨u + w, ⟨add_nonneg hu.1 hw.1, add_le_add hu.2 hw.2⟩, AddCircle.coe_add 1 u w⟩

end Erdos335.Loeb
