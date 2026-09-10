import DifferentialGeometry.Topology.Homology.Algebra.FiniteType
import Mathlib.Algebra.Homology.QuasiIso

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe u v
namespace Poincare.HomologicalComplex
variable {k : Type u} [Field k]
  {K L : ChainComplex (ModuleCat.{v} k) ℕ} (φ : K ⟶ L) [QuasiIso φ]

include φ

theorem finiteHomologyType_iff_of_quasiIso : finiteHomologyType K ↔ finiteHomologyType L := by
  have transport {A B : ChainComplex (ModuleCat.{v} k) ℕ}
      (e : ∀ n, A.homology n ≅ B.homology n) (h : finiteHomologyType A) :
      finiteHomologyType B := by
    constructor
    · intro n
      have := h.1 n
      exact (e n).toLinearEquiv.finiteDimensional
    · obtain ⟨N, hN⟩ := h.2
      exact ⟨N, fun n hn => (hN n hn).of_iso (e n).symm⟩
  exact ⟨transport (fun n => isoOfQuasiIsoAt φ n), transport (fun n => (isoOfQuasiIsoAt φ n).symm)⟩

theorem homologyEulerChar_eq_of_quasiIso : K.homologyEulerChar = L.homologyEulerChar := by
  apply finsum_congr
  intro n
  rw [(isoOfQuasiIsoAt φ n).toLinearEquiv.finrank_eq]

end Poincare.HomologicalComplex
