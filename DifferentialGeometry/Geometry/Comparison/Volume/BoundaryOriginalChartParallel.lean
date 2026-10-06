import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryOriginalChartFrame
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.PartialDiffeomorph

set_option autoImplicit false

noncomputable section

open Bundle Filter
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [FiniteDimensional ℝ E₁]
  {H₁ : Type*} [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  [I₁.Boundaryless]
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
  [IsManifold I₁ ∞ M₁] [T2Space M₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  [FiniteDimensional ℝ E₂]
  {H₂ : Type*} [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
  [I₂.Boundaryless]
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  [IsManifold I₂ ∞ M₂] [T2Space M₂]

/-- A local metric isometry reflects parallel transport to its source metric. -/
theorem partialIsometry_reflects_parallel
    (g : SmoothRiemannianMetric I₁ M₁) (h : SmoothRiemannianMetric I₂ M₂)
    (Φ : PartialDiffeomorph I₁ I₂ M₁ M₂ ∞)
    (hmet : ∀ x ∈ Φ.source, ∀ v w : TangentSpace I₁ x,
      h.inner (Φ x) (mfderiv I₁ I₂ Φ x v) (mfderiv I₁ I₂ Φ x w) =
        g.inner x v w)
    (γ : ℝ → M₁) (V : ∀ s, TangentSpace I₁ (γ s)) {t : ℝ}
    (ht : γ t ∈ Φ.source)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I₁ γ t)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I₁) γ V t) t)
    (hparallel : covDerivAlong h (fun s => Φ (γ s))
      (fun s => mfderiv I₁ I₂ Φ (γ s) (V s)) t = 0) :
    covDerivAlong g γ V t = 0 := by
  have hnat := mfderiv_covDerivAlong_partialDiffeomorph g h Φ hmet γ V ht hγ hV
  rw [hparallel] at hnat
  have htarget : Φ (γ t) ∈ Φ.target := Φ.map_source' ht
  have hΦ : MDifferentiableAt I₁ I₂ Φ (γ t) :=
    (Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds ht)).mdifferentiableAt
      (by simp)
  have hΦsymm : MDifferentiableAt I₂ I₁ Φ.symm (Φ (γ t)) :=
    (Φ.contMDiffOn_invFun.contMDiffAt
      (Φ.open_target.mem_nhds htarget)).mdifferentiableAt (by simp)
  have heq : (fun x : M₁ => Φ.symm (Φ x)) =ᶠ[𝓝 (γ t)] id := by
    filter_upwards [Φ.open_source.mem_nhds ht] with x hx
    exact Φ.left_inv' hx
  have hcomp : (mfderiv I₂ I₁ Φ.symm (Φ (γ t))).comp
      (mfderiv I₁ I₂ Φ (γ t)) = ContinuousLinearMap.id ℝ
        (TangentSpace I₁ (γ t)) := by
    have h := (mfderiv_comp (γ t) hΦsymm hΦ).symm.trans heq.mfderiv_eq
    rw [mfderiv_id] at h
    exact h
  have hinj : Function.Injective (mfderiv I₁ I₂ Φ (γ t)) :=
    (ContinuousLinearMap.leftInverse_of_comp hcomp).injective
  apply hinj
  calc
    mfderiv I₁ I₂ Φ (γ t) (covDerivAlong g γ V t) = 0 := hnat
    _ = mfderiv I₁ I₂ Φ (γ t) 0 := by simp

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

end
