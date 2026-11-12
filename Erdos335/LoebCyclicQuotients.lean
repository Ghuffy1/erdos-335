import Erdos335.CyclicQuotients
import Erdos335.LoebEventualQuotients

/-!
# A fixed cyclic quotient from bounded coordinate indices

The index of a coordinate subgroup is constant on an ultrafilter-large set
when the indices are bounded. Natural residue maps then give one fixed
finite cyclic quotient of the ultraproduct.
-/

set_option autoImplicit false

open Filter Set Topology
open scoped ENNReal

namespace Erdos335.Loeb

theorem exists_eventually_constant_of_bounded_nat
    {I : Type*} (U : Ultrafilter I) (d : I → ℕ) (D : ℕ)
    (hD : ∀ᶠ i in U, d i ≤ D) :
    ∃ h : ℕ, h ≤ D ∧ ∀ᶠ i in U, d i = h := by
  have hex : ∀ᶠ i in U, ∃ h : Fin (D + 1), d i = h := by
    apply hD.mono
    intro i hi
    exact ⟨⟨d i, by omega⟩, rfl⟩
  obtain ⟨h, hh⟩ := Ultrafilter.eventually_exists_iff.mp hex
  exact ⟨h, by omega, hh⟩

theorem exists_fixed_natural_cyclic_quotient
    {I : Type*} (U : Ultrafilter I) (q : I → ℕ+)
    (K : ∀ i, AddSubgroup (ZMod (q i : ℕ))) (D : ℕ)
    (hD : ∀ᶠ i in U, (K i).index ≤ D) :
    ∃ (h : ℕ+) (p : ∀ i, ZMod (q i : ℕ) →+ ZMod (h : ℕ)),
      (h : ℕ) ≤ D ∧
      (∀ᶠ i in U, (h : ℕ) ∣ (q i : ℕ) ∧ Function.Surjective (p i) ∧
        (p i).ker = K i ∧ ∀ n : ℕ, p i (n : ZMod (q i : ℕ)) = (n : ZMod (h : ℕ))) ∧
      (finiteQuotient U p).ker = internalAddSubgroup U K := by
  classical
  obtain ⟨m, hmD, hm⟩ := exists_eventually_constant_of_bounded_nat U (fun i => (K i).index) D hD
  have hmpos : 0 < m := by
    obtain ⟨i, hi⟩ := Filter.nonempty_of_mem hm
    rw [← hi]
    change 0 < Nat.card (ZMod (q i : ℕ) ⧸ K i)
    exact Nat.card_pos
  let h : ℕ+ := ⟨m, hmpos⟩
  have hex (i : I) (hi : (K i).index = (h : ℕ)) :
      ∃ p : ZMod (q i : ℕ) →+ ZMod (h : ℕ),
        (h : ℕ) ∣ (q i : ℕ) ∧ Function.Surjective p ∧ p.ker = K i ∧
          ∀ n : ℕ, p (n : ZMod (q i : ℕ)) = (n : ZMod (h : ℕ)) := by
    obtain ⟨k, p, hk, hdiv, hp, hker, hnat⟩ := exists_natural_cyclic_quotient (q i) (K i)
    have hkh : k = h := by
      apply Subtype.ext
      exact hk.trans hi
    subst k
    exact ⟨p, hdiv, hp, hker, hnat⟩
  let p (i : I) : ZMod (q i : ℕ) →+ ZMod (h : ℕ) :=
    if hi : (K i).index = (h : ℕ) then (hex i hi).choose else 0
  have hp : ∀ᶠ i in U, (h : ℕ) ∣ (q i : ℕ) ∧ Function.Surjective (p i) ∧
      (p i).ker = K i ∧ ∀ n : ℕ, p i (n : ZMod (q i : ℕ)) = (n : ZMod (h : ℕ)) := by
    apply hm.mono
    intro i hi
    have hi' : (K i).index = (h : ℕ) := hi
    simpa [p, hi'] using (hex i hi').choose_spec
  refine ⟨h, p, hmD, hp, ?_⟩
  rw [finiteQuotient_ker]
  apply SetLike.coe_injective
  change internalSet U (fun i => ((p i).ker : Set (ZMod (q i : ℕ)))) =
    internalSet U (fun i => (K i : Set (ZMod (q i : ℕ))))
  apply (internalSet_eq_iff U _ _).mpr
  exact hp.mono fun i hi => congrArg (fun H : AddSubgroup (ZMod (q i : ℕ)) =>
    (H : Set (ZMod (q i : ℕ)))) hi.2.2.1

theorem finiteQuotient_natCast_of_eventually
    {I : Type*} (U : Ultrafilter I) (q : I → ℕ+) (h : ℕ+)
    (p : ∀ i, ZMod (q i : ℕ) →+ ZMod (h : ℕ))
    (hp : ∀ᶠ i in U, ∀ n : ℕ, p i (n : ZMod (q i : ℕ)) = (n : ZMod (h : ℕ)))
    (n : ℕ) :
    finiteQuotient U p (productProjection (U : Filter I) (fun i => (n : ZMod (q i : ℕ)))) =
      (n : ZMod (h : ℕ)) := by
  change finiteValue U (fun i => p i (n : ZMod (q i : ℕ))) = (n : ZMod (h : ℕ))
  exact finiteValue_eq_of_eventually U _ _ (hp.mono fun i hi => hi n)

theorem exists_natural_quotient_of_positive_loebMeasure
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (K : ∀ n, AddSubgroup (ZMod (q n : ℕ)))
    (hpos : 0 < loebMeasure U hU (internalAddSubgroup U K :
      Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))) :
    ∃ (h : ℕ+) (p : ∀ n, ZMod (q n : ℕ) →+ ZMod (h : ℕ)),
      Function.Surjective (finiteQuotient U p) ∧
      (finiteQuotient U p).ker = internalAddSubgroup U K ∧
      (∀ n : ℕ, finiteQuotient U p
        (productProjection (U : Filter ℕ) (fun i => (n : ZMod (q i : ℕ)))) =
          (n : ZMod (h : ℕ))) ∧
      loebMeasure U hU (internalAddSubgroup U K :
        Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) =
          1 / ((h : ℕ) : ℝ≥0∞) := by
  obtain ⟨D, hD⟩ := eventually_bounded_index_of_positive_loebMeasure U hU K hpos
  obtain ⟨h, p, _, hp, hker⟩ := exists_fixed_natural_cyclic_quotient U q K D hD
  have hsurj := hp.mono fun _ hi => hi.2.1
  refine ⟨h, p, finiteQuotient_surjective_of_eventually U p hsurj, hker, ?_, ?_⟩
  · intro n
    exact finiteQuotient_natCast_of_eventually U q h p (hp.mono fun _ hi => hi.2.2.2) n
  · rw [← hker, finiteQuotient_ker]
    simpa only [Nat.card_zmod] using
      loebMeasure_internalSubgroup_of_eventually_quotients U hU p hsurj

theorem exists_natural_quotient_of_supergroup
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+) (h : ℕ+)
    (p : ∀ n, ZMod (q n : ℕ) →+ ZMod (h : ℕ))
    (hp : ∀ᶠ i in U, Function.Surjective (p i) ∧
      ∀ n : ℕ, p i (n : ZMod (q i : ℕ)) = (n : ZMod (h : ℕ)))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hcontain : (finiteQuotient U p).ker ≤ H) :
    ∃ (k : ℕ+) (r : ∀ n, ZMod (q n : ℕ) →+ ZMod (k : ℕ)),
      (k : ℕ) ∣ (h : ℕ) ∧
      (∀ᶠ i in U, Function.Surjective (r i) ∧
        ∀ n : ℕ, r i (n : ZMod (q i : ℕ)) = (n : ZMod (k : ℕ))) ∧
      (finiteQuotient U r).ker = H ∧
      loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) =
        1 / ((k : ℕ) : ℝ≥0∞) := by
  obtain ⟨k, ψ, _, hdiv, hψ, hψker, hψnat⟩ :=
    exists_natural_cyclic_quotient h (H.map (finiteQuotient U p))
  let r := fun i => ψ.comp (p i)
  have hr : ∀ᶠ i in U, Function.Surjective (r i) ∧
      ∀ n : ℕ, r i (n : ZMod (q i : ℕ)) = (n : ZMod (k : ℕ)) := by
    apply hp.mono
    intro i hi
    refine ⟨hψ.comp hi.1, ?_⟩
    intro n
    change ψ (p i (n : ZMod (q i : ℕ))) = (n : ZMod (k : ℕ))
    rw [hi.2 n, hψnat n]
  have hrker : (finiteQuotient U r).ker = H := by
    rw [show finiteQuotient U r = ψ.comp (finiteQuotient U p) from
      finiteQuotient_comp U p ψ]
    rw [← AddMonoidHom.comap_ker, hψker, AddSubgroup.comap_map_eq_self hcontain]
  refine ⟨k, r, hdiv, hr, hrker, ?_⟩
  rw [← hrker, finiteQuotient_ker]
  simpa only [Nat.card_zmod] using
    loebMeasure_internalSubgroup_of_eventually_quotients U hU r (hr.mono fun _ hi => hi.1)

end Erdos335.Loeb
