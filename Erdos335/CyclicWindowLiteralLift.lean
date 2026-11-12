import Erdos335.CyclicWindowRemoval

/-!
# Literal integer exhaustion behind cyclic window inputs
-/

set_option autoImplicit false

open Filter Topology Finset

namespace Erdos335.IntermediateScale

noncomputable def cyclicLift {q : ℕ} (S : Finset (ZMod q)) : Finset ℕ :=
  S.image ZMod.val

theorem cyclicLift_image {q : ℕ} [NeZero q] (S : Finset (ZMod q)) :
    (cyclicLift S).image (fun b : ℕ => (b : ZMod q)) = S := by
  classical
  simp [cyclicLift, image_image, Function.comp_def]

theorem cyclicLift_subset {q : ℕ} [NeZero q] (B : Set ℕ)
    (S : Finset (ZMod q)) (hS : S ⊆ cyclicWindow B 0 q) :
    (cyclicLift S : Set ℕ) ⊆ B := by
  classical
  intro b hb
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hb
  have h := (mem_filter.mp (hS hx)).2
  simpa only [zero_add] using h

theorem cyclicLift_exhaustion (B : Set ℕ) (q : ℕ → ℕ)
    [∀ n, NeZero (q n)] (hq : Tendsto q atTop atTop)
    (S : ∀ n, Finset (ZMod (q n)))
    (hS : ∀ b ∈ B, ∀ᶠ n in atTop, (b : ZMod (q n)) ∈ S n) :
    ∀ b ∈ B, ∀ᶠ n in atTop, b ∈ cyclicLift (S n) := by
  classical
  intro b hb
  filter_upwards [hS b hb, hq.eventually (eventually_gt_atTop b)] with n hbn hqn
  apply mem_image.mpr
  exact ⟨(b : ZMod (q n)), hbn, ZMod.val_natCast_of_lt hqn⟩

end Erdos335.IntermediateScale
