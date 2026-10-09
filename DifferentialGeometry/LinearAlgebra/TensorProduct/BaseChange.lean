import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic

set_option autoImplicit false

open scoped TensorProduct

namespace LinearMap

variable {R A M N : Type*} [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

theorem ker_baseChange [Module.Flat R A] (f : M →ₗ[R] N) :
    ker (f.baseChange A) = (ker f).baseChange A := by
  have h : Function.Exact ((ker f).subtype.baseChange A) (f.baseChange A) :=
    Module.Flat.lTensor_exact A (exact_subtype_ker_map f)
  exact exact_iff.mp h

end LinearMap

namespace Module.End

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module.Flat R A]

theorem eigenspace_baseChange (f : Module.End R M) (r : R) :
    eigenspace (f.baseChange A) (algebraMap R A r) = (eigenspace f r).baseChange A := by
  rw [eigenspace_def, eigenspace_def, ← LinearMap.ker_baseChange]
  congr 1
  simp only [LinearMap.baseChange_sub, LinearMap.baseChange_smul, LinearMap.baseChange_one,
    algebraMap_smul]

end Module.End

namespace Submodule

variable {R A M : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  [AddCommMonoid M] [Module R M]

theorem baseChange_le_iff_le_comap {p : Submodule R M} {q : Submodule A (A ⊗[R] M)} :
    p.baseChange A ≤ q ↔
      p ≤ (q.restrictScalars R).comap (TensorProduct.mk R A M 1) := by
  rw [baseChange_eq_span, span_le]
  change p.map (TensorProduct.mk R A M 1) ≤ q.restrictScalars R ↔ _
  exact map_le_iff_le_comap

theorem baseChange_iSup {ι : Sort*} (p : ι → Submodule R M) :
    (iSup p).baseChange A = ⨆ i, (p i).baseChange A := by
  apply le_antisymm
  · apply baseChange_le_iff_le_comap.mpr
    apply iSup_le
    intro i
    apply baseChange_le_iff_le_comap.mp
    exact le_iSup (fun j => (p j).baseChange A) i
  · exact iSup_le fun i => baseChange_mono A (le_iSup p i)

end Submodule
