import Erdos335.FiniteSaturatedFrame
import Erdos335.FiniteNaturalCriticalCore

/-!
# Natural cyclic quotients for saturated finite output masks
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Pointwise

noncomputable section

namespace Erdos335.Loeb

theorem exists_saturated_natural_frame (m : ℕ+)
    (P Q R S U : Finset (ZMod (m : ℕ)))
    (hP : P.Nonempty) (hQ : Q.Nonempty) (hPR : P ⊆ R) (hQS : Q ⊆ S)
    (hPS : P + S = U) (hRQ : R + Q = U)
    (hcard : U.card = P.card + Q.card) (houtside : ¬R + S ⊆ U) :
    ∃ h : ℕ+, (h : ℕ) ∣ (m : ℕ) ∧
      let π := naturalCyclicProjection m h
      π ⁻¹' (P.image π : Set (ZMod (h : ℕ))) = P ∧
      π ⁻¹' (Q.image π : Set (ZMod (h : ℕ))) = Q ∧
      π ⁻¹' (U.image π : Set (ZMod (h : ℕ))) = U ∧
      ((P.image π).card : ℝ) / (h : ℕ) = (P.card : ℝ) / (m : ℕ) ∧
      ((Q.image π).card : ℝ) / (h : ℕ) = (Q.card : ℝ) / (m : ℕ) ∧
      ((U.image π).card : ℝ) / (h : ℕ) = (U.card : ℝ) / (m : ℕ) ∧
      (U.image π).card = (P.image π).card + (Q.image π).card ∧
      ∃ i j : ZMod (h : ℕ), i ∉ P.image π ∧ j ∉ Q.image π ∧
        R.image π = insert i (P.image π) ∧ S.image π = insert j (Q.image π) ∧
        i + j ∉ U.image π ∧
        (R.image π + S.image π) = insert (i + j) (U.image π) := by
  classical
  have hU : U.Nonempty := by rw [← hPS]; exact hP.add (hQ.mono hQS)
  obtain ⟨hPinv, hQinv⟩ := FiniteKneser.saturated_cross_stabilizer_invariance
    P Q R S U hP hQ hPR hQS hPS hRQ hcard houtside
  let K := AddAction.stabilizer (ZMod (m : ℕ)) (U : Set (ZMod (m : ℕ)))
  obtain ⟨h, π, hindex, hdiv, hπ, hker, hnat⟩ := exists_natural_cyclic_quotient m K
  have hπeq : π = naturalCyclicProjection m h := by
    ext x
    rw [← ZMod.natCast_zmod_val x, hnat, naturalCyclicProjection_natCast m h hdiv]
  subst π
  let π := naturalCyclicProjection m h
  have hKcoe : (K : Set (ZMod (m : ℕ))) = (U.addStab : Set (ZMod (m : ℕ))) :=
    (Finset.coe_addStab hU).symm
  have hUinv : U + U.addStab = U := by rw [Finset.add_addStab]
  have hpre (V : Finset (ZMod (m : ℕ))) (hV : V + U.addStab = V) :
      π ⁻¹' (V.image π : Set (ZMod (h : ℕ))) = V := by
    rw [Finset.coe_image, ← addHom_saturation_eq_preimage_image, hker, hKcoe,
      ← Finset.coe_add, hV]
  have hprod : U.addStab.card * (h : ℕ) = (m : ℕ) := by
    rw [hindex, ← natCard_stabilizer_eq_card U hU]
    simpa only [Nat.card_zmod] using K.card_mul_index
  have hcount (V : Finset (ZMod (m : ℕ))) (hV : V + U.addStab = V) :
      U.addStab.card * (V.image π).card = V.card := by
    have hc := card_stabilizer_quotient U V π hπ hker
    rwa [hV] at hc
  have hratio (V : Finset (ZMod (m : ℕ))) (hV : V + U.addStab = V) :
      ((V.image π).card : ℝ) / (h : ℕ) = (V.card : ℝ) / (m : ℕ) := by
    have hc : (U.addStab.card : ℝ) * (V.image π).card = V.card := by exact_mod_cast hcount V hV
    have hp : (U.addStab.card : ℝ) * (h : ℕ) = (m : ℕ) := by exact_mod_cast hprod
    apply (div_eq_div_iff (by exact_mod_cast h.ne_zero : ((h : ℕ) : ℝ) ≠ 0)
      (by exact_mod_cast m.ne_zero : ((m : ℕ) : ℝ) ≠ 0)).mpr
    rw [← hp, ← hc]
    ring
  have himage (V W : Finset (ZMod (m : ℕ))) : (V + W).image π = V.image π + W.image π := by
    apply Finset.coe_injective
    simp only [Finset.coe_image, Finset.coe_add, Set.image_add]
  have hPS' : P.image π + S.image π = U.image π := by rw [← himage, hPS]
  have hRQ' : R.image π + Q.image π = U.image π := by rw [← himage, hRQ]
  have hcard' : (U.image π).card = (P.image π).card + (Q.image π).card := by
    have hp := hcount P hPinv
    have hq := hcount Q hQinv
    have hu := hcount U hUinv
    have hpos : 0 < U.addStab.card := Finset.card_pos.mpr ⟨0, Finset.zero_mem_addStab.mpr hU⟩
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [Nat.mul_add, hp, hq, hu, hcard]
  have houtside' : ¬R.image π + S.image π ⊆ U.image π := by
    intro hsub
    apply houtside
    intro x hx
    have him : π x ∈ U.image π := hsub (by rw [← himage]; exact Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    have hp := hpre U hUinv
    change x ∈ (U : Set (ZMod (m : ℕ)))
    rw [← hp]
    exact him
  have haperiodic : (U.image π).addStab = {0} :=
    stabilizer_image_quotient_eq_zero U hU π hπ hker
  have hframe := FiniteKneser.saturated_cross_aperiodic_frame (P.image π) (Q.image π)
    (R.image π) (S.image π) (U.image π) (hP.image π) (hQ.image π)
    (Finset.image_subset_image hPR) (Finset.image_subset_image hQS) hPS' hRQ' hcard' houtside' haperiodic
  exact ⟨h, hdiv, hpre P hPinv, hpre Q hQinv, hpre U hUinv,
    hratio P hPinv, hratio Q hQinv, hratio U hUinv, hcard', hframe⟩

end Erdos335.Loeb

end
