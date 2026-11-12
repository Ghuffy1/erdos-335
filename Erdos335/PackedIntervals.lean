import Erdos335.ResiduePacking
import Erdos335.DysonProgressions

/-!
# Long intervals after packing residue classes

Simultaneous progressions through a representative of each occupied residue
give a full interval in the packed coordinates.
-/

set_option autoImplicit false

open Filter Topology
open scoped Pointwise

namespace Erdos335

theorem exists_finite_residue_representatives (A : Set ℕ) (g : ℕ+) :
    ∃ T : Finset ℕ, (T : Set ℕ) ⊆ A ∧
      ∀ r ∈ residues (g : ℕ) A, ∃ a ∈ T, (a : ZMod (g : ℕ)) = r := by
  classical
  let S := residues (g : ℕ) A
  have hrep : ∀ r : S, ∃ a ∈ A, (a : ZMod (g : ℕ)) = r.val := by
    intro r
    exact mem_residues.mp r.property
  choose rep hmem hres using hrep
  refine ⟨S.attach.image rep, ?_, ?_⟩
  · intro a ha
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ha
    exact hmem r
  · intro r hr
    exact ⟨rep ⟨r, hr⟩, Finset.mem_image.mpr ⟨⟨r, hr⟩, by simp, rfl⟩, hres ⟨r, hr⟩⟩

theorem packed_interval_of_progressions (g h : ℕ+)
    (label : ZMod (g : ℕ) → Fin (h : ℕ)) (S : Finset (ZMod (g : ℕ)))
    (hsurj : ∀ j : Fin (h : ℕ), ∃ r ∈ S, label r = j)
    (T : Finset ℕ) (hrep : ∀ r ∈ S, ∃ a ∈ T, (a : ZMod (g : ℕ)) = r)
    (E : Set ℕ) (hE : ∀ e ∈ E, (e : ZMod (g : ℕ)) ∈ S)
    (z k : ℕ)
    (hprog : ∀ a ∈ T, ∀ i ≤ T.sup id + k + 1, a + z + i * (g : ℕ) ∈ E) :
    ∃ u : ℕ, ∀ j < k, u + j ∈ packedSet g h label E := by
  classical
  let M := T.sup id
  let N := M + z / (g : ℕ) + 1
  have hM : ∀ a ∈ T, a ≤ M := by
    intro a ha
    exact Finset.le_sup (f := id) ha
  have himage : S.image (fun r => r + (z : ZMod (g : ℕ))) = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro r hr
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨a, ha, har⟩ := hrep s hs
      have h := hE (a + z) (by simpa using hprog a ha 0 (by omega))
      simpa only [Nat.cast_add, har] using h
    · rw [Finset.card_image_of_injective S (fun a b h => add_right_cancel h)]
  refine ⟨(h : ℕ) * N, ?_⟩
  intro j hj
  let m := (h : ℕ) * N + j
  let t := m / (h : ℕ)
  let ell : Fin (h : ℕ) := ⟨m % (h : ℕ), Nat.mod_lt _ h.pos⟩
  obtain ⟨r, hr, hlab⟩ := hsurj ell
  have hrimage : r ∈ S.image (fun s => s + (z : ZMod (g : ℕ))) := by rwa [himage]
  obtain ⟨s, hs, hsr⟩ := Finset.mem_image.mp hrimage
  obtain ⟨a, ha, has⟩ := hrep s hs
  let d := (a + z) / (g : ℕ)
  have hdiv_upper : d ≤ M + z / (g : ℕ) := by
    have hag : a ≤ (g : ℕ) * M := by
      have hg := g.pos
      have ham := hM a ha
      nlinarith
    have hd : (a + z) / (g : ℕ) ≤ ((g : ℕ) * M + z) / (g : ℕ) :=
      Nat.div_le_div_right (Nat.add_le_add_right hag z)
    have heq : ((g : ℕ) * M + z) / (g : ℕ) = M + z / (g : ℕ) := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ g.pos]
      omega
    exact hd.trans_eq heq
  have hdiv_lower : z / (g : ℕ) ≤ d := Nat.div_le_div_right (by omega : z ≤ a + z)
  have ht : t = N + j / (h : ℕ) := by
    dsimp only [t, m]
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ h.pos]
    omega
  have hdt : d ≤ t := by
    calc
      d ≤ M + z / (g : ℕ) := hdiv_upper
      _ ≤ N := by dsimp only [N]; omega
      _ ≤ t := by rw [ht]; exact Nat.le_add_right _ _
  have hi : t - d ≤ M + k + 1 := by
    have hjdiv := Nat.div_le_self j (h : ℕ)
    dsimp only [N] at ht
    omega
  have hn : a + z + (t - d) * (g : ℕ) ∈ E := hprog a ha (t - d) hi
  refine ⟨a + z + (t - d) * (g : ℕ), hn, ?_⟩
  have hres : ((a + z + (t - d) * (g : ℕ) : ℕ) : ZMod (g : ℕ)) = r := by
    simpa only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero, has] using hsr
  have hquot : (a + z + (t - d) * (g : ℕ)) / (g : ℕ) = t := by
    rw [Nat.add_mul_div_right _ _ g.pos]
    change d + (t - d) = t
    omega
  have hlabval : (label r).val = m % (h : ℕ) := congrArg Fin.val hlab
  unfold packedCode
  rw [hquot, hres, hlabval]
  exact Nat.div_add_mod m (h : ℕ)

theorem exists_dysonDerived_packed_intervals (A B : Set ℕ) (q g h : ℕ+)
    (hg : (g : ℕ) = Nat.setGcd B)
    (hstable : ∀ C D : Set ℕ, DysonDerived A B C D →
      HasGap D q ∧ Nat.setGcd D = Nat.setGcd B ∧
        residues (q : ℕ) D = residues (q : ℕ) B)
    (label : ZMod (g : ℕ) → Fin (h : ℕ))
    (hsurj : ∀ j : Fin (h : ℕ), ∃ r ∈ residues (g : ℕ) A, label r = j)
    (k : ℕ) :
    ∃ (C D : Set ℕ) (u : ℕ), DysonDerived A B C D ∧
      ∀ i < k, u + i ∈ packedSet g h label C := by
  obtain ⟨T, hT, hrep⟩ := exists_finite_residue_representatives A g
  have hgpos : 0 < Nat.setGcd B := by rw [← hg]; exact g.pos
  obtain ⟨C, D, z, hCD, hprog⟩ :=
    exists_dysonDerived_progressions A B q hgpos hstable T hT (T.sup id + k + 1)
  have hB : ∀ b ∈ B, (g : ℕ) ∣ b := fun b hb => hg ▸ Nat.setGcd_dvd_of_mem hb
  have hC : ∀ c ∈ C, (c : ZMod (g : ℕ)) ∈ residues (g : ℕ) A := by
    intro c hc
    rw [← hCD.residues_left_of_dvd g hB]
    exact mem_residues.mpr ⟨c, hc, rfl⟩
  obtain ⟨u, hu⟩ := packed_interval_of_progressions g h label (residues (g : ℕ) A)
    hsurj T hrep C hC z k (by simpa only [hg] using hprog)
  exact ⟨C, D, u, hCD, hu⟩

end Erdos335
