import Erdos335.DensityRescaling
import Mathlib.Data.Fintype.EquivFin

/-!
# Packing occupied residue classes

Each occupied class receives one position in a shorter block. The labeling is
explicit and injective on the carrier, so all prefix and sum identities retain
the literal input elements.
-/

set_option autoImplicit false

open Filter Topology
open scoped Pointwise

namespace Erdos335

def packedCode (g h : ℕ+) (label : ZMod (g : ℕ) → Fin (h : ℕ)) (n : ℕ) : ℕ :=
  (h : ℕ) * (n / (g : ℕ)) + (label (n : ZMod (g : ℕ))).val

def packedSet (g h : ℕ+) (label : ZMod (g : ℕ) → Fin (h : ℕ)) (A : Set ℕ) : Set ℕ :=
  packedCode g h label '' A

theorem packedCode_div (g h : ℕ+) (label : ZMod (g : ℕ) → Fin (h : ℕ)) (n : ℕ) :
    packedCode g h label n / (h : ℕ) = n / (g : ℕ) := by
  unfold packedCode
  rw [show (h : ℕ) * (n / (g : ℕ)) + (label (n : ZMod (g : ℕ))).val =
      (label (n : ZMod (g : ℕ))).val + (h : ℕ) * (n / (g : ℕ)) by omega]
  rw [Nat.add_mul_div_left _ _ h.pos, Nat.div_eq_of_lt (label _).isLt, zero_add]

theorem packedCode_mod (g h : ℕ+) (label : ZMod (g : ℕ) → Fin (h : ℕ)) (n : ℕ) :
    packedCode g h label n % (h : ℕ) = (label (n : ZMod (g : ℕ))).val := by
  simp [packedCode, Nat.add_mod, Nat.mod_eq_of_lt (label _).isLt]

theorem packedCode_lt_block (g h : ℕ+) (label : ZMod (g : ℕ) → Fin (h : ℕ)) (n N : ℕ) :
    packedCode g h label n < (h : ℕ) * N ↔ n < (g : ℕ) * N := by
  calc
    packedCode g h label n < (h : ℕ) * N ↔ packedCode g h label n / (h : ℕ) < N := by
      simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul h.pos).symm
    _ ↔ n / (g : ℕ) < N := by rw [packedCode_div]
    _ ↔ n < (g : ℕ) * N := by simpa only [Nat.mul_comm] using Nat.div_lt_iff_lt_mul g.pos

theorem packedCode_injOn (g h : ℕ+) (label : ZMod (g : ℕ) → Fin (h : ℕ))
    (S : Finset (ZMod (g : ℕ))) (A : Set ℕ)
    (hA : ∀ a ∈ A, (a : ZMod (g : ℕ)) ∈ S) (hlabel : Set.InjOn label (S : Set (ZMod (g : ℕ)))) :
    Set.InjOn (packedCode g h label) A := by
  intro a ha b hb hab
  have hdiv := congrArg (fun n => n / (h : ℕ)) hab
  rw [packedCode_div, packedCode_div] at hdiv
  have hmod := congrArg (fun n => n % (h : ℕ)) hab
  rw [packedCode_mod, packedCode_mod] at hmod
  have hlab : label (a : ZMod (g : ℕ)) = label (b : ZMod (g : ℕ)) := Fin.ext hmod
  have hres := hlabel (hA a ha) (hA b hb) hlab
  have hres' := (ZMod.natCast_eq_natCast_iff a b (g : ℕ)).mp hres
  change a % (g : ℕ) = b % (g : ℕ) at hres'
  have ha' := Nat.div_add_mod a (g : ℕ)
  have hb' := Nat.div_add_mod b (g : ℕ)
  rw [hdiv, hres'] at ha'
  omega

theorem prefixCount_packedSet (g h : ℕ+) (label : ZMod (g : ℕ) → Fin (h : ℕ))
    (S : Finset (ZMod (g : ℕ))) (A : Set ℕ)
    (hA : ∀ a ∈ A, (a : ZMod (g : ℕ)) ∈ S) (hlabel : Set.InjOn label (S : Set (ZMod (g : ℕ))))
    (N : ℕ) : prefixCount (packedSet g h label A) ((h : ℕ) * N) =
      prefixCount A ((g : ℕ) * N) := by
  classical
  unfold prefixCount
  symm
  apply Finset.card_bij (fun n _ => packedCode g h label n)
  · intro n hn
    obtain ⟨hn, ha⟩ := Finset.mem_filter.mp hn
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ⟨n, ha, rfl⟩⟩
    exact (packedCode_lt_block g h label n N).mpr (Finset.mem_range.mp hn)
  · intro a ha b hb hab
    exact packedCode_injOn g h label S A hA hlabel
      (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 hab
  · intro n hn
    obtain ⟨hn, a, ha, rfl⟩ := Finset.mem_filter.mp hn
    refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ha⟩, rfl⟩
    exact (packedCode_lt_block g h label a N).mp (Finset.mem_range.mp hn)

theorem lowerDensity_packedSet (g h : ℕ+) (label : ZMod (g : ℕ) → Fin (h : ℕ))
    (S : Finset (ZMod (g : ℕ))) (A : Set ℕ)
    (hA : ∀ a ∈ A, (a : ZMod (g : ℕ)) ∈ S) (hlabel : Set.InjOn label (S : Set (ZMod (g : ℕ)))) :
    lowerDensity (packedSet g h label A) = ((g : ℕ) : ℝ) / (h : ℕ) * lowerDensity A :=
  lowerDensity_scale_of_prefix_identity A _ g h (prefixCount_packedSet g h label S A hA hlabel)

theorem packedCode_add_of_dvd (g h : ℕ+) (label : ZMod (g : ℕ) → Fin (h : ℕ))
    (a b : ℕ) (hb : (g : ℕ) ∣ b) :
    packedCode g h label (a + b) = packedCode g h label a +
      packedCode g h (fun _ => 0) b := by
  obtain ⟨k, rfl⟩ := hb
  have hd : (a + (g : ℕ) * k) / (g : ℕ) = a / (g : ℕ) + k :=
    Nat.add_mul_div_left a k g.pos
  have hk : ((g : ℕ) * k) / (g : ℕ) = k := by
    simp
  simp only [packedCode, hd, hk, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self,
    zero_mul, add_zero, Fin.val_zero]
  ring

theorem packedSet_add (g h : ℕ+) (label : ZMod (g : ℕ) → Fin (h : ℕ)) (A B : Set ℕ)
    (hB : ∀ b ∈ B, (g : ℕ) ∣ b) :
    packedSet g h label (A + B) = packedSet g h label A + packedSet g h (fun _ => 0) B := by
  ext n
  constructor
  · rintro ⟨s, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    exact ⟨packedCode g h label a, ⟨a, ha, rfl⟩,
      packedCode g h (fun _ => 0) b, ⟨b, hb, rfl⟩,
      (packedCode_add_of_dvd g h label a b (hB b hb)).symm⟩
  · rintro ⟨x, ⟨a, ha, rfl⟩, y, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, packedCode_add_of_dvd g h label a b (hB b hb)⟩

theorem prefixCount_packed_multiples (g h : ℕ+) (B : Set ℕ)
    (hB : ∀ b ∈ B, (g : ℕ) ∣ b) (N : ℕ) :
    prefixCount (packedSet g h (fun _ => 0) B) ((h : ℕ) * N) = prefixCount B ((g : ℕ) * N) := by
  have hs : ∀ b ∈ B, (b : ZMod (g : ℕ)) ∈ ({0} : Finset (ZMod (g : ℕ))) := by
    intro b hb
    obtain ⟨k, rfl⟩ := hB b hb
    simp
  apply prefixCount_packedSet g h (fun _ => 0) {0} B hs
  intro r hr t ht _
  exact (Finset.mem_singleton.mp hr).trans (Finset.mem_singleton.mp ht).symm

theorem jointLowerDensity_packed (g h : ℕ+) (label : ZMod (g : ℕ) → Fin (h : ℕ))
    (S : Finset (ZMod (g : ℕ))) (A B : Set ℕ)
    (hA : ∀ a ∈ A, (a : ZMod (g : ℕ)) ∈ S) (hlabel : Set.InjOn label (S : Set (ZMod (g : ℕ))))
    (hB : ∀ b ∈ B, (g : ℕ) ∣ b) :
    jointLowerDensity (packedSet g h label A) (packedSet g h (fun _ => 0) B) =
      ((g : ℕ) : ℝ) / (h : ℕ) * jointLowerDensity A B :=
  jointLowerDensity_scale_of_prefix_identities A B _ _ g h
    (prefixCount_packedSet g h label S A hA hlabel) (prefixCount_packed_multiples g h B hB)

theorem lowerDensity_packed_sum (g h : ℕ+) (label : ZMod (g : ℕ) → Fin (h : ℕ))
    (S : Finset (ZMod (g : ℕ))) (A B : Set ℕ)
    (hA : ∀ a ∈ A, (a : ZMod (g : ℕ)) ∈ S) (hlabel : Set.InjOn label (S : Set (ZMod (g : ℕ))))
    (hB : ∀ b ∈ B, (g : ℕ) ∣ b) :
    lowerDensity (packedSet g h label A + packedSet g h (fun _ => 0) B) =
      ((g : ℕ) : ℝ) / (h : ℕ) * lowerDensity (A + B) := by
  rw [← packedSet_add g h label A B hB]
  apply lowerDensity_packedSet g h label S (A + B) _ hlabel
  rintro n ⟨a, ha, b, hb, rfl⟩
  obtain ⟨k, rfl⟩ := hB b hb
  simpa using hA a ha

theorem zero_mem_packed_multiples (g h : ℕ+) {B : Set ℕ} (hB0 : 0 ∈ B) :
    0 ∈ packedSet g h (fun _ => 0) B := by
  exact ⟨0, hB0, by simp [packedCode]⟩

theorem exists_residue_label (g : ℕ+) (S : Finset (ZMod (g : ℕ))) (hS : S.Nonempty) :
    ∃ h : ℕ+, (h : ℕ) = S.card ∧ ∃ label : ZMod (g : ℕ) → Fin (h : ℕ),
      Set.InjOn label (S : Set (ZMod (g : ℕ))) ∧
        ∀ j : Fin (h : ℕ), ∃ r ∈ S, label r = j := by
  classical
  let h : ℕ+ := ⟨S.card, Finset.card_pos.mpr hS⟩
  let e : S ≃ Fin (h : ℕ) := S.equivFin
  let label : ZMod (g : ℕ) → Fin (h : ℕ) := fun r => if hr : r ∈ S then e ⟨r, hr⟩ else 0
  refine ⟨h, rfl, label, ?_, ?_⟩
  · intro r hr t ht heq
    change r ∈ S at hr
    change t ∈ S at ht
    have heq' : e ⟨r, hr⟩ = e ⟨t, ht⟩ := by simpa [label, hr, ht] using heq
    exact congrArg Subtype.val (e.injective heq')
  · intro j
    obtain ⟨r, hr⟩ := e.surjective j
    exact ⟨r.val, r.property, by simpa [label] using hr⟩

theorem packedSet_mem_iff (g h : ℕ+) (label : ZMod (g : ℕ) → Fin (h : ℕ))
    (S : Finset (ZMod (g : ℕ))) (A : Set ℕ)
    (hA : ∀ a ∈ A, (a : ZMod (g : ℕ)) ∈ S) (hlabel : Set.InjOn label (S : Set (ZMod (g : ℕ))))
    {n : ℕ} (hn : (n : ZMod (g : ℕ)) ∈ S) :
    packedCode g h label n ∈ packedSet g h label A ↔ n ∈ A := by
  constructor
  · rintro ⟨a, ha, heq⟩
    have hinj := packedCode_injOn g h label S {x : ℕ | (x : ZMod (g : ℕ)) ∈ S}
      (fun x hx => hx) hlabel
    have han := hinj (hA a ha) hn heq
    simpa only [← han] using ha
  · intro hnA
    exact ⟨n, hnA, rfl⟩

theorem cofinite_packed_sum_reflect (g h : ℕ+) (label : ZMod (g : ℕ) → Fin (h : ℕ))
    (S : Finset (ZMod (g : ℕ))) (A B : Set ℕ)
    (hA : ∀ a ∈ A, (a : ZMod (g : ℕ)) ∈ S) (hlabel : Set.InjOn label (S : Set (ZMod (g : ℕ))))
    (hB : ∀ b ∈ B, (g : ℕ) ∣ b)
    (hfull : ∃ K : ℕ, ∀ n : ℕ, K ≤ n →
      n ∈ packedSet g h label A + packedSet g h (fun _ => 0) B) :
    ∃ K : ℕ, ∀ n : ℕ, K ≤ n → (n ∈ A + B ↔ (n : ZMod (g : ℕ)) ∈ S) := by
  obtain ⟨K, hK⟩ := hfull
  have hsum : ∀ n ∈ A + B, (n : ZMod (g : ℕ)) ∈ S := by
    rintro n ⟨a, ha, b, hb, rfl⟩
    obtain ⟨k, rfl⟩ := hB b hb
    simpa using hA a ha
  refine ⟨(g : ℕ) * (K + 1), ?_⟩
  intro n hn
  constructor
  · exact hsum n
  · intro hnS
    have hlarge : (h : ℕ) * (K + 1) ≤ packedCode g h label n := by
      by_contra hsmall
      have hlt : packedCode g h label n < (h : ℕ) * (K + 1) := by omega
      have hnlt := (packedCode_lt_block g h label n (K + 1)).mp hlt
      omega
    have hHK : K ≤ (h : ℕ) * (K + 1) := by have hp := h.pos; nlinarith
    have hc := hK (packedCode g h label n) (hHK.trans hlarge)
    rw [← packedSet_add g h label A B hB] at hc
    exact (packedSet_mem_iff g h label S (A + B) hsum hlabel hnS).mp hc

theorem DysonDerived.residues_left_of_dvd {A B C D : Set ℕ}
    (hCD : DysonDerived A B C D) (g : ℕ+) (hB : ∀ b ∈ B, (g : ℕ) ∣ b) :
    residues (g : ℕ) C = residues (g : ℕ) A := by
  have hcarrier : ∀ c ∈ C, (c : ZMod (g : ℕ)) ∈ residues (g : ℕ) A := by
    induction hCD with
    | refl => exact fun c hc => mem_residues.mpr ⟨c, hc, rfl⟩
    | @step C D h e he ih =>
        intro c hc
        rcases hc with hc | ⟨b, hb, rfl⟩
        · exact ih c hc
        · have hd := hB b (h.right_subset hb)
          obtain ⟨k, rfl⟩ := hd
          simpa using ih e he
  apply Finset.Subset.antisymm
  · intro r hr
    obtain ⟨c, hc, rfl⟩ := mem_residues.mp hr
    exact hcarrier c hc
  · intro r hr
    obtain ⟨a, ha, rfl⟩ := mem_residues.mp hr
    exact mem_residues.mpr ⟨a, hCD.left_subset ha, rfl⟩

end Erdos335
