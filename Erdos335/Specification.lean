import Erdos335.Residues
import Erdos335.PackingDensity
import Mathlib.NumberTheory.Real.Irrational

/-!
# Proposed full classification, stated as a proposition

`FullSolution` below is the exact proof obligation proposed for the 23:57 packet.
It is a definition of a proposition. This module does not contain a proof of it.
The type distinction is intentional, so checking these definitions cannot be
mistaken for checking the full solution.
-/

set_option autoImplicit false

open Filter Topology
open scoped Pointwise

namespace Erdos335.Proposed

def positiveRepresentative (q : ℕ+) (r : ZMod (q : ℕ)) : ℕ :=
  if r.val = 0 then q else r.val

def residueSection (A : Set ℕ) (q : ℕ+) (r : ZMod (q : ℕ)) : Set ℕ :=
  {k | 0 < k ∧ (q : ℕ) * (k - 1) + positiveRepresentative q r ∈ A}

structure FiniteFrame (A B : Set ℕ) where
  modulus : ℕ+
  activeA : ZMod (modulus : ℕ)
  activeB : ZMod (modulus : ℕ)
  activeA_mem : activeA ∈ residues (modulus : ℕ) A
  activeB_mem : activeB ∈ residues (modulus : ℕ) B
  backgroundA : ∀ r ∈ residues (modulus : ℕ) A, r ≠ activeA →
    HasDensity (residueSection A modulus r) 1
  backgroundB : ∀ r ∈ residues (modulus : ℕ) B, r ≠ activeB →
    HasDensity (residueSection B modulus r) 1
  uniqueExpression : ∀ r ∈ residues (modulus : ℕ) A,
    ∀ t ∈ residues (modulus : ℕ) B,
      r + t = activeA + activeB → r = activeA ∧ t = activeB
  card_sum : (residues (modulus : ℕ) A + residues (modulus : ℕ) B).card + 1 =
    (residues (modulus : ℕ) A).card + (residues (modulus : ℕ) B).card

def closedArcPullback (θ start length : ℝ) : Set ℕ :=
  {n | 0 < n ∧ ∃ k : ℤ,
    start + k ≤ (n : ℝ) * θ ∧ (n : ℝ) * θ ≤ start + length + k}

def BohrBranch (A B : Set ℕ) : Prop :=
  ∃ f : FiniteFrame A B, ∃ θ startA startB lengthA lengthB : ℝ,
    Irrational θ ∧ 0 < lengthA ∧ 0 < lengthB ∧ lengthA + lengthB < 1 ∧
    residueSection A f.modulus f.activeA ⊆ closedArcPullback θ startA lengthA ∧
    residueSection B f.modulus f.activeB ⊆ closedArcPullback θ startB lengthB ∧
    HasDensity (closedArcPullback θ startA lengthA \
      residueSection A f.modulus f.activeA) 0 ∧
    HasDensity (closedArcPullback θ startB lengthB \
      residueSection B f.modulus f.activeB) 0

def SingletonBranch (A B : Set ℕ) : Prop :=
  ∃ f : FiniteFrame A B, ∃ x : ℝ, 0 < x ∧ x < 1 ∧
    ((∃ n : ℕ, residueSection A f.modulus f.activeA = {n}) ∧
      HasDensity (residueSection B f.modulus f.activeB) x ∨
     (∃ n : ℕ, residueSection B f.modulus f.activeB = {n}) ∧
      HasDensity (residueSection A f.modulus f.activeA) x)

noncomputable def mask (A : Set ℕ) (q : ℕ+) (k : ℕ) : Finset (ZMod (q : ℕ)) := by
  classical
  exact Finset.univ.filter (fun r => (q : ℕ) * k + r.val ∈ A)

noncomputable def outputMask (A B : Set ℕ) (q : ℕ+) (k : ℕ) :
    Finset (ZMod (q : ℕ)) :=
  (mask A q k + residues (q : ℕ) B) ∪ (residues (q : ℕ) A + mask B q k)

noncomputable def pairedMask (A B : Set ℕ) (q : ℕ+) (k : ℕ) :=
  (mask A q k, mask B q k)

noncomputable def transitionCount (A B : Set ℕ) (q : ℕ+) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.range N).filter (fun k =>
    pairedMask A B q k ≠ pairedMask A B q (k + 1))).card

def SparseTransitions (A B : Set ℕ) (q : ℕ+) : Prop :=
  Tendsto (fun N => (transitionCount A B q N : ℝ) / N) atTop (𝓝 0)

def PrefixRun (A B : Set ℕ) (q : ℕ+) (N : ℕ) (I : ℕ × ℕ) : Prop :=
  I.1 ≤ I.2 ∧ I.2 < N ∧
    (∀ k ∈ Finset.Icc I.1 I.2, pairedMask A B q k = pairedMask A B q I.1) ∧
    (I.1 = 0 ∨ pairedMask A B q (I.1 - 1) ≠ pairedMask A B q I.1) ∧
    (I.2 + 1 = N ∨ pairedMask A B q (I.2 + 1) ≠ pairedMask A B q I.1)

noncomputable def prefixRuns (A B : Set ℕ) (q : ℕ+) (N : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.range N).product (Finset.range N)).filter (PrefixRun A B q N)

def carry (q : ℕ+) (r t : ZMod (q : ℕ)) : ℕ := (r.val + t.val) / (q : ℕ)

def clippedInterval (q : ℕ+) (I J K : ℕ × ℕ) (r t : ZMod (q : ℕ)) :
    IntervalPacking.Interval :=
  (max ((I.1 : ℤ) + J.1 + carry q r t) K.1,
    min ((I.2 : ℤ) + J.2 + carry q r t) K.2)

/-- The source and target runs are clipped to the first N blocks. -/
noncomputable def escapingIntervals (A B : Set ℕ) (q : ℕ+) (N : ℕ)
    (w : ZMod (q : ℕ)) : Finset IntervalPacking.Interval := by
  classical
  let runs := prefixRuns A B q N
  exact runs.biUnion fun I => runs.biUnion fun J => runs.biUnion fun K =>
    (((mask A q I.1).product (mask B q J.1)).filter
      (fun p => p.1 + p.2 = w ∧ w ∉ outputMask A B q K.1)).image
        (fun p => clippedInterval q I J K p.1 p.2)

def MaskMean (A B : Set ℕ) (q : ℕ+) (s : ℝ) : Prop :=
  Tendsto (fun N => (∑ k ∈ Finset.range N, ((outputMask A B q k).card : ℝ)) /
    ((q : ℕ) * N : ℕ)) atTop (𝓝 s)

def EscapingPackingVanishes (A B : Set ℕ) (q : ℕ+) : Prop :=
  ∀ w : ZMod (q : ℕ), Tendsto
    (fun N => (IntervalPacking.packingSize (escapingIntervals A B q N w) : ℝ) / N)
      atTop (𝓝 0)

def MaskBranch (A B : Set ℕ) (s : ℝ) : Prop :=
  ∃ q : ℕ+, SparseTransitions A B q ∧ MaskMean A B q s ∧
    EscapingPackingVanishes A B q

def Classified (A B : Set ℕ) (s : ℝ) : Prop :=
  gamma A B = s ∨ (s < gamma A B ∧
    (BohrBranch A B ∨ SingletonBranch A B ∨ MaskBranch A B s))

/-- Unproved full-problem target. A value of this proposition is still required. -/
def FullSolution : Prop :=
  ∀ (A B : Set ℕ) (a b : ℝ), A ⊆ Set.Ioi 0 → B ⊆ Set.Ioi 0 →
    0 < a → 0 < b → HasDensity A a → HasDensity B b →
      (HasDensity (A + B) (a + b) ↔ Classified A B (a + b))

end Erdos335.Proposed
