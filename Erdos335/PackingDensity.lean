import Erdos335.Density
import Erdos335.IntervalPacking

set_option autoImplicit false

open Filter Topology

namespace Erdos335.IntervalPacking

/-- Sublinear packing size is equivalent to sublinear union size. -/
theorem packing_vanishes_iff_covered_vanishes (F : ℕ → Finset Interval) :
    Tendsto (fun N => (packingSize (F N) : ℝ) / N) atTop (𝓝 0) ↔
    Tendsto (fun N => ((covered (F N)).card : ℝ) / N) atTop (𝓝 0) := by
  constructor
  · intro h
    have hthree : Tendsto (fun N => 3 * ((packingSize (F N) : ℝ) / N))
        atTop (𝓝 0) := by simpa using h.const_mul 3
    apply squeeze_zero (fun N => by positivity) ?_ hthree
    intro N
    have hcard : ((covered (F N)).card : ℝ) ≤ 3 * (packingSize (F N) : ℝ) := by
      exact_mod_cast card_le_three_mul_packingSize (F N)
    simpa only [mul_div_assoc] using
      div_le_div_of_nonneg_right hcard (Nat.cast_nonneg N)
  · intro h
    apply squeeze_zero (fun N => by positivity) ?_ h
    intro N
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast packingSize_le_card (F N)) (Nat.cast_nonneg N)

end Erdos335.IntervalPacking
