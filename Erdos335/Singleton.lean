import Erdos335.FiniteSections

/-!
# The singleton branch of the proposed characterization

The unique active expression isolates a fixed translate of one positive-density
section. Every other occupied output residue is filled by a background section.
-/

set_option autoImplicit false

open Filter Topology
open scoped Pointwise

namespace Erdos335.Proposed

def FiniteFrame.swap {A B : Set ℕ} (f : FiniteFrame A B) : FiniteFrame B A where
  modulus := f.modulus
  activeA := f.activeB
  activeB := f.activeA
  activeA_mem := f.activeB_mem
  activeB_mem := f.activeA_mem
  backgroundA := f.backgroundB
  backgroundB := f.backgroundA
  uniqueExpression := by
    intro r hr t ht hrt
    have h := f.uniqueExpression t ht r hr (by simpa only [add_comm] using hrt)
    exact ⟨h.2, h.1⟩
  card_sum := by simpa only [add_comm] using f.card_sum

theorem FiniteFrame.outputFiber_eq {A B : Set ℕ} (f : FiniteFrame A B)
    (hA : A ⊆ Set.Ioi 0) (hB : B ⊆ Set.Ioi 0) :
    residueFiber (A + B) (f.activeA + f.activeB) =
      residueFiber A f.activeA + residueFiber B f.activeB := by
  classical
  ext n
  constructor
  · rintro ⟨hn, hn0, hnres⟩
    have hnval : (n : ZMod (f.modulus : ℕ)) = f.activeA + f.activeB := by simpa using hnres
    obtain ⟨a, ha, b, hb, hab⟩ := hn
    change a + b = n at hab
    have hsum : (a : ZMod (f.modulus : ℕ)) + (b : ZMod (f.modulus : ℕ)) =
        f.activeA + f.activeB := by
      rw [← Nat.cast_add, hab]
      exact hnval
    have hpair := f.uniqueExpression (a : ZMod (f.modulus : ℕ))
      (mem_residues.mpr ⟨a, ha, rfl⟩) (b : ZMod (f.modulus : ℕ))
      (mem_residues.mpr ⟨b, hb, rfl⟩) hsum
    refine ⟨a, ⟨ha, hA ha, ?_⟩, b, ⟨hb, hB hb, ?_⟩, hab⟩
    · simpa only [Finset.mem_singleton] using hpair.1
    · simpa only [Finset.mem_singleton] using hpair.2
  · rintro ⟨a, ha, b, hb, rfl⟩
    have har : (a : ZMod (f.modulus : ℕ)) = f.activeA := by simpa using ha.2.2
    have hbr : (b : ZMod (f.modulus : ℕ)) = f.activeB := by simpa using hb.2.2
    refine ⟨⟨a, ha.1, b, hb.1, rfl⟩, by have := ha.2.1; have := hb.2.1; change 0 < a + b; omega, ?_⟩
    simp only [Nat.cast_add, har, hbr, Finset.mem_singleton]

theorem FiniteFrame.output_background {A B : Set ℕ} (f : FiniteFrame A B)
    (hA : A ⊆ Set.Ioi 0) (hB : B ⊆ Set.Ioi 0)
    {w : ZMod (f.modulus : ℕ)} (hw : w ∈ residues (f.modulus : ℕ) (A + B))
    (hne : w ≠ f.activeA + f.activeB) :
    Negligible (periodicSet ({w} : Finset (ZMod (f.modulus : ℕ))) \ (A + B)) := by
  rw [residues_add] at hw
  obtain ⟨r, hr, t, ht, rfl⟩ := Finset.mem_add.mp hw
  by_cases hri : r = f.activeA
  · have htj : t ≠ f.activeB := by
      intro htj
      exact hne (by rw [hri, htj])
    exact missing_output_of_full_right (full_residueFiber hB (f.backgroundB t ht htj)) hr
  · have hh := missing_output_of_full_right (A := B) (B := A)
      (full_residueFiber hA (f.backgroundA r hr hri)) ht
    simpa only [add_comm] using hh

theorem singleton_add_eq_shift (a : ℕ) (B : Set ℕ) : ({a} : Set ℕ) + B = shift B a := by
  ext n
  constructor
  · rintro ⟨x, hx, b, hb, hxb⟩
    have hx' : x = a := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨b, hb, by simpa only [add_comm] using hxb⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨a, Set.mem_singleton a, b, hb, by simp only [add_comm]⟩

theorem FiniteFrame.hasDensity_of_active_sum {A B : Set ℕ} (f : FiniteFrame A B)
    (hApos : A ⊆ Set.Ioi 0) (hBpos : B ⊆ Set.Ioi 0)
    {a b x y : ℝ} (hA : HasDensity A a) (hB : HasDensity B b)
    (hactiveA : HasDensity (residueFiber A f.activeA) x)
    (hactiveB : HasDensity (residueFiber B f.activeB) y)
    (hactiveSum : HasDensity (residueFiber A f.activeA + residueFiber B f.activeB) (x + y)) :
    HasDensity (A + B) (a + b) := by
  classical
  let q := f.modulus
  let S := residues (q : ℕ) A
  let T := residues (q : ℕ) B
  let W := S + T
  have hactiveC : HasDensity (residueFiber (A + B) (f.activeA + f.activeB)) (x + y) := by
    rwa [f.outputFiber_eq hApos hBpos]
  have hDA := hasDensity_from_residue_background A q f.activeA x hApos f.activeA_mem
    (fun r hr hne => missing_fiber_of_full_section hApos (f.backgroundA r hr hne)) hactiveA
  have hDB := hasDensity_from_residue_background B q f.activeB y hBpos f.activeB_mem
    (fun r hr hne => missing_fiber_of_full_section hBpos (f.backgroundB r hr hne)) hactiveB
  have hmem : f.activeA + f.activeB ∈ residues (q : ℕ) (A + B) := by
    rw [residues_add]
    exact Finset.add_mem_add f.activeA_mem f.activeB_mem
  have hDC := hasDensity_from_residue_background (A + B) q (f.activeA + f.activeB) (x + y)
    (sumset_positive hApos hBpos) hmem (fun r hr hne => f.output_background hApos hBpos hr hne) hactiveC
  have ha : a = ((S.card : ℝ) - 1) / q + x := hA.unique hDA
  have hb : b = ((T.card : ℝ) - 1) / q + y := hB.unique hDB
  have hc : (W.card : ℝ) + 1 = (S.card : ℝ) + T.card := by exact_mod_cast f.card_sum
  have hmass : ((W.card : ℝ) - 1) / q + (x + y) = a + b := by
    rw [ha, hb]
    have hnum : (W.card : ℝ) - 1 = ((S.card : ℝ) - 1) + ((T.card : ℝ) - 1) := by linarith
    rw [hnum]
    ring
  rw [residues_add] at hDC
  exact hmass ▸ hDC

theorem FiniteFrame.singleton_left_hasDensity {A B : Set ℕ} (f : FiniteFrame A B)
    (hApos : A ⊆ Set.Ioi 0) (hBpos : B ⊆ Set.Ioi 0)
    {a b x : ℝ} (hA : HasDensity A a) (hB : HasDensity B b)
    {k : ℕ} (hsingleton : residueSection A f.modulus f.activeA = {k})
    (hactiveB : HasDensity (residueSection B f.modulus f.activeB) x) :
    HasDensity (A + B) (a + b) := by
  let a₀ := sectionPoint f.modulus f.activeA k
  have hsingle : residueFiber A f.activeA = {a₀} := singleton_residueFiber hsingleton
  have hactiveA : HasDensity (residueFiber A f.activeA) 0 := by
    rw [hsingle]
    apply Negligible.of_bounded a₀
    intro n hn
    exact (Set.mem_singleton_iff.mp hn).le
  have hactiveB' := hasDensity_residueFiber hBpos hactiveB
  apply f.hasDensity_of_active_sum hApos hBpos hA hB hactiveA hactiveB'
  rw [hsingle, singleton_add_eq_shift, zero_add]
  exact hactiveB'.shift a₀

theorem SingletonBranch.hasDensity {A B : Set ℕ} {a b : ℝ}
    (h : SingletonBranch A B) (hApos : A ⊆ Set.Ioi 0) (hBpos : B ⊆ Set.Ioi 0)
    (hA : HasDensity A a) (hB : HasDensity B b) : HasDensity (A + B) (a + b) := by
  obtain ⟨f, x, hx0, hx1, hcase⟩ := h
  rcases hcase with ⟨⟨k, hk⟩, hactive⟩ | ⟨⟨k, hk⟩, hactive⟩
  · exact f.singleton_left_hasDensity hApos hBpos hA hB hk hactive
  · have hh := f.swap.singleton_left_hasDensity hBpos hApos hB hA hk hactive
    simpa only [add_comm] using hh

theorem isErdos335Pair_of_singletonBranch (A B : Set ℕ) (a b : ℝ)
    (hApos : A ⊆ Set.Ioi 0) (hBpos : B ⊆ Set.Ioi 0)
    (ha0 : 0 < a) (hb0 : 0 < b) (hA : HasDensity A a) (hB : HasDensity B b)
    (h : SingletonBranch A B) : IsErdos335Pair A B :=
  ⟨hApos, hBpos, a, b, ha0, hb0, hA, hB, h.hasDensity hApos hBpos hA hB⟩

end Erdos335.Proposed
