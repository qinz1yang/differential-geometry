import DifferentialGeometry.Topology.Manifold.SmoothOrientationPullback
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false

noncomputable section

open Manifold
open TopologicalSpace (Opens)
open scoped Manifold ContDiff

namespace DifferentialGeometry.PartialDiffeomorph

open DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {H K : Type*} [TopologicalSpace H] [TopologicalSpace K]
variable {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]

def pullbackSmoothOrientation
    (Φ : _root_.PartialDiffeomorph I J M N (∞ : WithTop ℕ∞))
    {U : Opens M} (hU : (U : Set M) ⊆ Φ.source)
    (o : SmoothOrientation J N) : SmoothOrientation I U :=
  DifferentialGeometry.Topology.Manifold.pullbackSmoothOrientation I J
    (fun x : U => Φ x.val)
    (fun x => by
      rw [contMDiffAt_subtype_iff]
      exact Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds (hU x.property)))
    (fun x => by
      rw [mfderiv_restrict_open]
      exact ((Φ.isLocalDiffeomorphAt I J ∞ (hU x.property)).mfderivToContinuousLinearEquiv
        (by simp)).bijective) o

theorem pullbackSmoothOrientation_apply
    (Φ : _root_.PartialDiffeomorph I J M N (∞ : WithTop ℕ∞))
    {U : Opens M} (hU : (U : Set M) ⊆ Φ.source)
    (o : SmoothOrientation J N) (x : U) :
    (pullbackSmoothOrientation Φ hU o).val x =
      tangentOrientationEquiv
        ((Φ.isLocalDiffeomorphAt I J ∞ (hU x.property)).mfderivToContinuousLinearEquiv
          (by simp)).toLinearEquiv.symm (o.val (Φ x.val)) := by
  dsimp only [pullbackSmoothOrientation]
  erw [DifferentialGeometry.Topology.Manifold.pullbackSmoothOrientation_apply]
  congr 2
  rw [ContinuousLinearEquiv.toLinearEquiv_symm]
  apply congrArg LinearEquiv.symm
  apply LinearEquiv.ext
  intro v
  exact congrArg (fun D : E →L[ℝ] F => D v) (mfderiv_restrict_open (Φ : M → N) U x)

theorem pullbackSmoothOrientation_pushforward
    (Φ : _root_.PartialDiffeomorph I J M N (∞ : WithTop ℕ∞))
    {U : Opens M} (hU : (U : Set M) ⊆ Φ.source)
    (o : SmoothOrientation J N) (x : U) :
    tangentOrientationEquiv
        ((Φ.isLocalDiffeomorphAt I J ∞ (hU x.property)).mfderivToContinuousLinearEquiv
          (by simp)).toLinearEquiv
        ((pullbackSmoothOrientation Φ hU o).val x) = o.val (Φ x.val) := by
  rw [pullbackSmoothOrientation_apply]
  exact tangentOrientationEquiv_symm
    ((Φ.isLocalDiffeomorphAt I J ∞ (hU x.property)).mfderivToContinuousLinearEquiv
      (by simp)).toLinearEquiv.symm (o.val (Φ x.val))

theorem pullbackSmoothOrientation_map
    {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P]
    (Φ : _root_.PartialDiffeomorph I I M P (∞ : WithTop ℕ∞))
    {U : Opens M} (hU : (U : Set M) ⊆ Φ.source)
    (o : SmoothOrientation I P) (x : U) :
    Orientation.map (Fin (Module.finrank ℝ E))
        ((Φ.isLocalDiffeomorphAt I I ∞ (hU x.property)).mfderivToContinuousLinearEquiv
          (by simp)).toLinearEquiv
        ((pullbackSmoothOrientation Φ hU o).val x) = o.val (Φ x.val) := by
  let A : E ≃ₗ[ℝ] E :=
    ((Φ.isLocalDiffeomorphAt I I ∞ (hU x.property)).mfderivToContinuousLinearEquiv
      (by simp)).toLinearEquiv
  have h : tangentOrientationEquiv A ((pullbackSmoothOrientation Φ hU o).val x) =
      o.val (Φ x.val) := pullbackSmoothOrientation_pushforward Φ hU o x
  rw [tangentOrientationEquiv_self] at h
  exact h

end DifferentialGeometry.PartialDiffeomorph
