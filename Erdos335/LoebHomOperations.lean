import Erdos335.LoebCompactHom

/-!
# Operations on internal compact homomorphisms

Taking the ultralimit commutes with addition and negation of coordinate
homomorphisms. These identities give the multiplicative and conjugation
closure of the internal character family on a compact quotient.
-/

set_option autoImplicit false

open Filter Set Topology

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)]
  {E : Type*} [AddCommGroup E] [MetricSpace E] [CompactSpace E]
  [IsTopologicalAddGroup E]

theorem ultralimitAddHom_zero_family (U : Ultrafilter ℕ) :
    ultralimitAddHom (X := X) (E := E) U (fun _ => 0) = 0 := by
  ext x
  change ultralimitFunction U (fun _ _ => (0 : E)) x = 0
  induction x using Quotient.inductionOn with
  | h a =>
    exact tendsto_nhds_unique (tendsto_ultralimitFunction U (fun _ _ => (0 : E)) a)
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : E)) (U : Filter ℕ) (𝓝 0))

theorem ultralimitAddHom_add_family (U : Ultrafilter ℕ) (f g : ∀ n, X n →+ E) :
    ultralimitAddHom U (fun n => f n + g n) = ultralimitAddHom U f + ultralimitAddHom U g := by
  ext x
  change ultralimitFunction U (fun n y => f n y + g n y) x =
    ultralimitFunction U (fun n => f n) x + ultralimitFunction U (fun n => g n) x
  induction x using Quotient.inductionOn with
  | h a =>
    exact tendsto_nhds_unique (tendsto_ultralimitFunction U (fun n y => f n y + g n y) a)
      ((tendsto_ultralimitFunction U (fun n => f n) a).add
        (tendsto_ultralimitFunction U (fun n => g n) a))

theorem ultralimitAddHom_neg_family (U : Ultrafilter ℕ) (f : ∀ n, X n →+ E) :
    ultralimitAddHom U (fun n => -f n) = -ultralimitAddHom U f := by
  ext x
  change ultralimitFunction U (fun n y => -f n y) x = -ultralimitFunction U (fun n => f n) x
  induction x using Quotient.inductionOn with
  | h a =>
    exact tendsto_nhds_unique (tendsto_ultralimitFunction U (fun n y => -f n y) a)
      ((tendsto_ultralimitFunction U (fun n => f n) a).neg)

end Erdos335.Loeb
