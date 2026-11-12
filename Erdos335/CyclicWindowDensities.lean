import Erdos335.CyclicWindowRepresentatives
import Erdos335.MovingWindows

/-!
# Ordinary densities carried by cyclic windows and their large subsets
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem cyclicWindow_card_eq_prefixCount (A : Set ℕ) (start q : ℕ) [NeZero q] :
    (cyclicWindow A start q).card = prefixCount (tailShift A start) q := by
  classical
  unfold cyclicWindow prefixCount
  apply card_bij (fun x hx => x.val)
  · intro x hx
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (ZMod.val_lt x), ?_⟩
    simpa only [tailShift, Set.mem_ofPred_eq, Nat.add_comm] using (mem_filter.mp hx).2
  · intro x hx y hy hxy
    exact ZMod.val_injective q hxy
  · intro n hn
    obtain ⟨hnq, hnA⟩ := mem_filter.mp hn
    have hnlt := mem_range.mp hnq
    refine ⟨(n : ZMod q), ?_, ZMod.val_natCast_of_lt hnlt⟩
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    rw [ZMod.val_natCast_of_lt hnlt]
    simpa only [tailShift, Set.mem_ofPred_eq, Nat.add_comm] using hnA

theorem cyclic_window_density_of_prefix_error (A : Set ℕ) (a : ℝ)
    (N q start : ℕ → ℕ) [∀ s, NeZero (q s)]
    (hstart : ∀ᶠ s in atTop, 0 < start s)
    (hinside : ∀ᶠ s in atTop, start s + q s ≤ N s)
    (herror : Tendsto (fun s => prefixError A a (N s) / q s) atTop (𝓝 0)) :
    Tendsto (fun s => ((cyclicWindow A (start s) (q s)).card : ℝ) / q s) atTop (𝓝 a) := by
  have h := moving_window_density_of_prefix_error A a N q (fun s => start s - 1)
    (Eventually.of_forall fun s => NeZero.pos _) (hinside.mono fun s hs => by omega) herror
  apply h.congr'
  filter_upwards [hstart] with s hs
  rw [Nat.sub_add_cancel hs, cyclicWindow_card_eq_prefixCount]

theorem density_of_small_removed_subset (q : ℕ → ℕ) [∀ s, NeZero (q s)]
    (S T : ∀ s, Finset (ZMod (q s))) (hsub : ∀ s, T s ⊆ S s) (a : ℝ)
    (hS : Tendsto (fun s => ((S s).card : ℝ) / q s) atTop (𝓝 a))
    (hloss : Tendsto (fun s => ((S s \ T s).card : ℝ) / q s) atTop (𝓝 0)) :
    Tendsto (fun s => ((T s).card : ℝ) / q s) atTop (𝓝 a) := by
  have h := hS.sub hloss
  simp only [sub_zero] at h
  apply h.congr
  intro s
  rw [card_sdiff_of_subset (hsub s), Nat.cast_sub (card_le_card (hsub s))]
  ring

end Erdos335.IntermediateScale
