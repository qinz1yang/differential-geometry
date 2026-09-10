import DifferentialGeometry.Geometry.Neck.Chart
import DifferentialGeometry.Geometry.Curvature.LeastRicciOverlap
import DifferentialGeometry.Geometry.Gradient.SignedDifference

noncomputable section
open Set Bundle
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature
open Poincare.Geometry.Curvature Poincare.Geometry.Gradient

namespace Poincare.Geometry.Neck

theorem exists_compatible_least_ricci_fields
    {ι F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    [BoundarylessManifold J M]
    (g : SmoothRiemannianMetric J M) (C : ι → cylindricalChart J (M := M))
    (U : ∀ i, Set (C i).domain) (hU : ∀ i, IsOpen (U i))
    (ε δ : ℝ) (hε : ε < 1 / 200000) (hδ : 92354 * ε + δ < 1)
    (hsmall : ∀ i, (C i).metricCloseOn g ε (U i))
    (σ : ι → ι → ℝ) (hσ : ∀ i j, σ i j = 1 ∨ σ i j = -1)
    (hoverlap : ∀ i j, ∀ x ∈ (C i).region (U i), x ∈ (C j).region (U j) →
      Real.sqrt (g.inner x (gradFun g (C i).axial x - σ i j • gradFun g (C j).axial x)
        (gradFun g (C i).axial x - σ i j • gradFun g (C j).axial x)) ≤ δ) :
    ∃ (ν : ι → M → ℝ) (Y : ι → ∀ x : M, TangentSpace J x),
      (∀ i, ContMDiffOn J 𝓘(ℝ) ∞ (C i).axial (C i).target ∧
        ContMDiffOn J 𝓘(ℝ) ∞ (ν i) ((C i).region (U i)) ∧
        ContMDiffOn J J.tangent ∞ (fun x ↦ (⟨x, Y i x⟩ : TangentBundle J M)) ((C i).region (U i)) ∧
        ∀ x ∈ (C i).region (U i), g.inner x (Y i x) (Y i x) = 1 ∧
          ricciSharp g x (Y i x) = ν i x • Y i x ∧
          (∀ z : TangentSpace J x, g.inner x z z = 1 → ν i x ≤ ricciTensor g x z z) ∧
          |ν i x| ≤ 5772 * (C i).scale * ε ∧
          Module.End.eigenspace (ricciSharp g x).toLinearMap (ν i x) = Submodule.span ℝ {Y i x} ∧
          0 < mvfderiv J (C i).axial x (Y i x) ∧
          |mvfderiv J (C i).axial x (Y i x) - 1| ≤ 92354 * ε) ∧
      ∀ i j, ∀ x ∈ (C i).region (U i), x ∈ (C j).region (U j) →
        ν i x = ν j x ∧ Y i x = σ i j • Y j x ∧
          |mvfderiv J (C i).axial x (σ i j • Y j x) - 1| ≤ 92354 * ε + δ := by
  classical
  choose ν Y hu hν hY hp using fun i ↦
    (C i).exists_least_ricci_field g (hU i) ε hε (hsmall i)
  refine ⟨ν, Y, fun i ↦ ⟨hu i, hν i, hY i, hp i⟩, ?_⟩
  intro i j x hxi hxj
  obtain ⟨hin, hie, him, _, _, _, hid⟩ := hp i x hxi
  obtain ⟨hjn, hje, hjm, _, hjs, _, hjd⟩ := hp j x hxj
  have hc (z : TangentSpace J x) :
      |mvfderiv J (C i).axial x z - σ i j * mvfderiv J (C j).axial x z| ≤
        δ * Real.sqrt (g.inner x z z) :=
    (abs_mvfderiv_signed_difference_le_gradient_norm g (C i).axial (C j).axial (σ i j) x z).trans
      (mul_le_mul_of_nonneg_right (hoverlap i j x hxi hxj) (Real.sqrt_nonneg _))
  exact least_ricci_eigenpair_eq_of_signed_covector_error g x
    (mvfderiv J (C i).axial x).toLinearMap (mvfderiv J (C j).axial x).toLinearMap
    (ν i x) (ν j x) (Y i x) (Y j x) hin hjn hie hje him hjm hjs
    (σ i j) (92354 * ε) (92354 * ε) δ (hσ i j) hid hjd (by linarith) hδ hc

end Poincare.Geometry.Neck
