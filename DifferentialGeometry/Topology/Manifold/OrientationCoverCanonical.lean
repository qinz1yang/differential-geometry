import DifferentialGeometry.Topology.Manifold.OrientationCoverDeck
import DifferentialGeometry.Bundle.Orientation.Map

noncomputable section
open Bundle Manifold
open scoped Manifold ContDiff
open DifferentialGeometry.VectorBundle

namespace DifferentialGeometry.Topology.Manifold

variable {n : ℕ} {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def tangentOrientationCanonical (hdim : Module.finrank ℝ E = n) :
    letI := tangentOrientationChartedSpace (M := M) hdim
    ∀ z : tangentOrientationCover (M := M) hdim,
      Orientation ℝ (TangentSpace 𝓘(ℝ, E) z) (Fin n) := by
  letI := tangentOrientationChartedSpace (M := M) hdim
  intro z
  exact Orientation.map (Fin n)
    ((tangentOrientationProjection_isLocalDiffeomorph hdim).mfderivToContinuousLinearEquiv
      (by decide) z).toLinearEquiv.symm z.snd

theorem tangentOrientationCanonical_projects (hdim : Module.finrank ℝ E = n) :
    letI := tangentOrientationChartedSpace (M := M) hdim
    ∀ z : tangentOrientationCover (M := M) hdim,
      Orientation.map (Fin n)
        ((tangentOrientationProjection_isLocalDiffeomorph hdim).mfderivToContinuousLinearEquiv
          (by decide) z).toLinearEquiv
        (tangentOrientationCanonical hdim z) = z.snd := by
  let := tangentOrientationChartedSpace (M := M) hdim
  intro z
  unfold tangentOrientationCanonical
  exact (Orientation.map (Fin n)
    ((tangentOrientationProjection_isLocalDiffeomorph hdim).mfderivToContinuousLinearEquiv
      (by decide) z).toLinearEquiv).apply_symm_apply z.snd

theorem tangentOrientationCanonical_basis_iff (hdim : Module.finrank ℝ E = n) :
    letI := tangentOrientationChartedSpace (M := M) hdim
    ∀ (z : tangentOrientationCover (M := M) hdim)
      (b : Module.Basis (Fin n) ℝ (TangentSpace 𝓘(ℝ, E) z)),
      b.orientation = tangentOrientationCanonical hdim z ↔
        (b.map ((tangentOrientationProjection_isLocalDiffeomorph hdim).mfderivToContinuousLinearEquiv
          (by decide) z).toLinearEquiv).orientation = z.snd := by
  let := tangentOrientationChartedSpace (M := M) hdim
  intro z b
  rw [Module.Basis.orientation_map, ← tangentOrientationCanonical_projects hdim z]
  exact (Orientation.map (Fin n) _).injective.eq_iff.symm

theorem tangentOrientationDeck_reverses_canonical (hdim : Module.finrank ℝ E = n) :
    letI := tangentOrientationChartedSpace (M := M) hdim
    ∀ z : tangentOrientationCover (M := M) hdim,
      Orientation.map (Fin n)
        ((tangentOrientationDeckDiffeomorph hdim).mfderivToContinuousLinearEquiv
          (by decide) z).toLinearEquiv
        (tangentOrientationCanonical hdim z) =
      -tangentOrientationCanonical hdim (tangentOrientationDeck hdim z) := by
  let := tangentOrientationChartedSpace (M := M) hdim
  intro z
  let proj := tangentOrientationProjection (M := M) hdim
  let τ := tangentOrientationDeckDiffeomorph (M := M) hdim
  let hp := tangentOrientationProjection_isLocalDiffeomorph (M := M) hdim
  let D := (τ.mfderivToContinuousLinearEquiv (by decide) z).toLinearEquiv
  let P := (hp.mfderivToContinuousLinearEquiv (by decide) z).toLinearEquiv
  let Q := (hp.mfderivToContinuousLinearEquiv (by decide) (τ z)).toLinearEquiv
  have hcomp : D.trans Q = P := by
    ext v
    have hc := mfderiv_comp_apply (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E)) (I'' := 𝓘(ℝ, E))
      (g := proj) (f := (τ : _ → _)) (x := z)
      (hp.contMDiff.mdifferentiable (by decide) (τ z))
      (τ.contMDiff.mdifferentiable (by decide) z) v
    have heq : proj ∘ τ = proj := funext (tangentOrientationDeck_projects hdim)
    rw [heq] at hc
    exact hc.symm
  apply (Orientation.map (Fin n) Q).injective
  change Orientation.map (Fin n) Q (Orientation.map (Fin n) D _) =
    Orientation.map (Fin n) Q (-tangentOrientationCanonical hdim (τ z))
  rw [map_orientation_trans_between, hcomp, Orientation.map_neg]
  exact (tangentOrientationCanonical_projects hdim z).trans
    ((@neg_neg (Orientation ℝ E (Fin n)) inferInstance z.snd).symm.trans
      (congrArg (fun o : Orientation ℝ E (Fin n) => -o)
        (tangentOrientationCanonical_projects hdim (τ z))).symm)

end DifferentialGeometry.Topology.Manifold
