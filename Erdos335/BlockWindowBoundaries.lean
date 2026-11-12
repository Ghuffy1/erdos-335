import Erdos335.FiniteBlockSums
import Mathlib.Data.Nat.ModEq

/-!
# Counting windows that cross a fixed block boundary
-/

set_option autoImplicit false

open Finset
open scoped Classical

namespace Erdos335.IntermediateScale

theorem block_crossing_remainder (H W n : ℕ) (hH : 0 < H)
    (hcross : n / H ≠ (n + W) / H) : H ≤ n % H + W := by
  by_contra h
  have hsmall : n % H + W < H := by omega
  have hrepr : n + W = H * (n / H) + (n % H + W) := by
    have hmod := Nat.mod_add_div n H
    omega
  have heq : (n + W) / H = n / H := by
    rw [hrepr, Nat.mul_add_div hH, Nat.div_eq_of_lt hsmall, add_zero]
  exact hcross heq.symm

theorem block_crossing_window_card (N H W : ℕ) (hH : 0 < H) :
    ((range N).filter (fun n => n / H ≠ (n + W) / H)).card ≤ (N / H + 1) * W := by
  let S := (range N).filter (fun n => n / H ≠ (n + W) / H)
  let T := (range (N / H + 1)).product (range W)
  let p := fun n : ℕ => (n / H, n % H + W - H)
  have hp (n : ℕ) (hn : n ∈ S) : p n ∈ T := by
    obtain ⟨hnN, hcross⟩ := mem_filter.mp hn
    have hquot : n / H ≤ N / H := Nat.div_le_div_right (mem_range.mp hnN).le
    have hrem := Nat.mod_lt n hH
    have hlow := block_crossing_remainder H W n hH hcross
    apply mem_product.mpr
    constructor
    · exact mem_range.mpr (by dsimp [p]; omega)
    · exact mem_range.mpr (by dsimp [p]; omega)
  have hinj : Set.InjOn p (S : Set ℕ) := by
    intro n hn m hm heq
    have hnlow := block_crossing_remainder H W n hH (mem_filter.mp hn).2
    have hmlow := block_crossing_remainder H W m hH (mem_filter.mp hm).2
    have hquot : n / H = m / H := congrArg Prod.fst heq
    have hshift : n % H + W - H = m % H + W - H := congrArg Prod.snd heq
    have hrem : n % H = m % H := by omega
    have hnrepr := Nat.mod_add_div n H
    have hmrepr := Nat.mod_add_div m H
    rw [hquot, hrem] at hnrepr
    omega
  have hcard : S.card ≤ T.card := card_le_card_of_injOn p hp hinj
  change S.card ≤ (N / H + 1) * W
  calc
    S.card ≤ T.card := hcard
    _ = (N / H + 1) * W := by
      dsimp [T]
      rw [Finset.card_product, card_range, card_range]

end Erdos335.IntermediateScale
