import Erdos335.FiniteKneser

/-!
# Saturated finite cross-sums and their exceptional residues
-/

set_option autoImplicit false

open scoped Pointwise

namespace Erdos335.FiniteKneser

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem saturated_cross_single_extra (P Q R S U : Finset G)
    (hP : P.Nonempty) (hQ : Q.Nonempty) (hPR : P ⊆ R) (hQS : Q ⊆ S)
    (hPS : P + S = U) (hRQ : R + Q = U)
    (hcard : U.card = P.card + Q.card) (houtside : ¬R + S ⊆ U)
    (haperiodic : U.addStab = {0}) :
    ∃ r : G, r ∉ P ∧ R = insert r P := by
  classical
  have hne : P ≠ R := by
    intro heq
    apply houtside
    rw [← heq, hPS]
  have hproper : P ⊂ R := Finset.ssubset_iff_subset_ne.mpr ⟨hPR, hne⟩
  obtain ⟨r, hrR, hrP⟩ := Finset.exists_of_ssubset hproper
  have hbound := Finset.add_kneser R Q
  rw [hRQ, haperiodic] at hbound
  simp at hbound
  have hlt := Finset.card_lt_card hproper
  have hRcard : R.card = P.card + 1 := by omega
  have hins : insert r P ⊆ R := Finset.insert_subset hrR hPR
  refine ⟨r, hrP, (Finset.eq_of_subset_of_card_le hins ?_).symm⟩
  rw [Finset.card_insert_of_notMem hrP, hRcard]

theorem saturated_cross_aperiodic_frame (P Q R S U : Finset G)
    (hP : P.Nonempty) (hQ : Q.Nonempty) (hPR : P ⊆ R) (hQS : Q ⊆ S)
    (hPS : P + S = U) (hRQ : R + Q = U)
    (hcard : U.card = P.card + Q.card) (houtside : ¬R + S ⊆ U)
    (haperiodic : U.addStab = {0}) :
    ∃ r s : G, r ∉ P ∧ s ∉ Q ∧ R = insert r P ∧ S = insert s Q ∧
      r + s ∉ U ∧ R + S = insert (r + s) U := by
  classical
  obtain ⟨r, hr, hR⟩ := saturated_cross_single_extra P Q R S U hP hQ hPR hQS hPS hRQ hcard houtside haperiodic
  obtain ⟨s, hs, hS⟩ := saturated_cross_single_extra Q P S R U hQ hP hQS hPR
    (by simpa only [add_comm] using hRQ) (by simpa only [add_comm] using hPS)
    (by simpa only [Nat.add_comm] using hcard) (by simpa only [add_comm] using houtside) haperiodic
  have hsum : R + S = insert (r + s) U := by
    apply Finset.Subset.antisymm
    · intro z hz
      obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
      rw [hR, Finset.mem_insert] at hx
      rw [hS, Finset.mem_insert] at hy
      rcases hx with rfl | hx
      · rcases hy with rfl | hy
        · exact Finset.mem_insert_self _ _
        · apply Finset.mem_insert_of_mem
          rw [← hRQ]
          exact Finset.add_mem_add (by rw [hR]; exact Finset.mem_insert_self _ _) hy
      · apply Finset.mem_insert_of_mem
        rw [← hPS]
        exact Finset.add_mem_add hx (by rw [hS]; exact Finset.mem_insert.mpr hy)
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact Finset.add_mem_add (by rw [hR]; exact Finset.mem_insert_self r P)
          (by rw [hS]; exact Finset.mem_insert_self s Q)
      · rw [← hPS] at hz
        exact Finset.add_subset_add hPR (Finset.Subset.refl S) hz
  have hrs : r + s ∉ U := by
    intro hin
    apply houtside
    rw [hsum, Finset.insert_eq_of_mem hin]
  exact ⟨r, s, hr, hs, hR, hS, hrs, hsum⟩

theorem saturated_cross_stabilizer_invariance (P Q R S U : Finset G)
    (hP : P.Nonempty) (hQ : Q.Nonempty) (hPR : P ⊆ R) (hQS : Q ⊆ S)
    (hPS : P + S = U) (hRQ : R + Q = U)
    (hcard : U.card = P.card + Q.card) (houtside : ¬R + S ⊆ U) :
    P + U.addStab = P ∧ Q + U.addStab = Q := by
  classical
  have hU : U.Nonempty := by rw [← hPS]; exact hP.add (hQ.mono hQS)
  have single (P Q R S : Finset G) (hP : P.Nonempty) (hQ : Q.Nonempty)
      (hPR : P ⊆ R) (hQS : Q ⊆ S) (hPS : P + S = U) (hRQ : R + Q = U)
      (hcard : U.card = P.card + Q.card) (houtside : ¬R + S ⊆ U) : P + U.addStab = P := by
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨p, hp, t, ht, rfl⟩ := Finset.mem_add.mp hx
      by_contra hn
      let P' := insert (p + t) P
      have hP'S : P' + S ⊆ U := by
        intro z hz
        obtain ⟨v, hv, s, hs, rfl⟩ := Finset.mem_add.mp hz
        rcases Finset.mem_insert.mp hv with rfl | hv
        · have hps : p + s ∈ U := by rw [← hPS]; exact Finset.add_mem_add hp hs
          have hmem := (Finset.mem_addStab' hU).mp ht hps
          simpa only [vadd_eq_add, add_assoc, add_comm, add_left_comm] using hmem
        · rw [← hPS]
          exact Finset.add_mem_add hv hs
      have hP'Q : P' + Q ⊆ U := (Finset.add_subset_add (Finset.Subset.refl P') hQS).trans hP'S
      have hsmall : U.card < P'.card + Q.card := by
        dsimp only [P']
        rw [Finset.card_insert_of_notMem hn, hcard]
        omega
      have hinside := extended_support_sum_subset (P := P') (Q := Q) (S := R) (T := S)
        (Finset.insert_nonempty _ _) hQ hP'Q hRQ.le hP'S hsmall
      exact houtside (hinside.trans hP'Q)
    · exact subset_add_stabilizer_right P (Finset.zero_mem_addStab.mpr hU)
  refine ⟨single P Q R S hP hQ hPR hQS hPS hRQ hcard houtside, ?_⟩
  exact single Q P S R hQ hP hQS hPR
    (by simpa only [add_comm] using hRQ) (by simpa only [add_comm] using hPS)
    (by simpa only [Nat.add_comm] using hcard) (by simpa only [add_comm] using houtside)

end Erdos335.FiniteKneser
