import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross

noncomputable section

open Bundle Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M V : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]
  [TopologicalSpace V] [ChartedSpace ThreeSpace V] [IsManifold ThreeModel ∞ V] [T2Space V]
  {g : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ}

namespace NormalizedNeck

def lift (N : NormalizedNeck g δ k) (f : V → M)
    (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
    (Φ : neckBuffer δ → V) (hΦ : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ Φ)
    (hcomp : f ∘ Φ = N.chart) : NormalizedNeck (localPullMetric g f hf) δ k where
  delta_pos := N.delta_pos
  delta_lt_one := N.delta_lt_one
  sphereMark := N.sphereMark
  center := Φ ⟨(N.sphereMark, 0), by
    have := inv_pos.mpr N.delta_pos
    constructor <;> linarith⟩
  chart := ⟨Φ, hΦ.contMDiff.continuous⟩
  chart_smooth := hΦ
  marked := rfl
  scale := N.scale
  scale_pos := N.scale_pos
  scale_scalar := by
    rw [metricScalarAt_localPull]
    have hpoint := congrFun hcomp ⟨(N.sphereMark, 0), by
      have := inv_pos.mpr N.delta_pos
      constructor <;> linarith⟩
    change f (Φ _) = _ at hpoint
    rw [hpoint, N.marked]
    exact N.scale_scalar
  normalizedMetric := N.normalizedMetric
  normalized_inner := by
    intro x v w
    rw [N.normalized_inner, localPullMetric_inner]
    have hv := mfderiv_comp_apply x (hf.mdifferentiable (by decide) (Φ x))
      (hΦ.contMDiff.mdifferentiableAt (by decide)) v
    have hw := mfderiv_comp_apply x (hf.mdifferentiable (by decide) (Φ x))
      (hΦ.contMDiff.mdifferentiableAt (by decide)) w
    rw [hcomp] at hv hw
    have hp := congrFun hcomp x
    change f (Φ x) = N.chart x at hp
    have hslots := congrArg₂ (fun a b : ThreeSpace => g.inner (N.chart x) a b) hv hw
    have hpoint := congrArg (fun y : M => g.inner y
      (mfderiv ThreeModel ThreeModel f (Φ x) (mfderiv NeckCylinderModel ThreeModel Φ x v))
      (mfderiv ThreeModel ThreeModel f (Φ x) (mfderiv NeckCylinderModel ThreeModel Φ x w))) hp
    exact congrArg (fun a : ℝ => N.scale * a) (hslots.trans hpoint.symm)
  closeness := N.closeness

@[simp] theorem lift_chart (N : NormalizedNeck g δ k) (f : V → M)
    (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
    (Φ : neckBuffer δ → V) (hΦ : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ Φ)
    (hcomp : f ∘ Φ = N.chart) :
    ((N.lift f hf Φ hΦ hcomp).chart : neckBuffer δ → V) = Φ := rfl

@[simp] theorem lift_scale (N : NormalizedNeck g δ k) (f : V → M)
    (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
    (Φ : neckBuffer δ → V) (hΦ : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ Φ)
    (hcomp : f ∘ Φ = N.chart) :
    (N.lift f hf Φ hΦ hcomp).scale = N.scale := rfl

@[simp] theorem lift_normalizedMetric (N : NormalizedNeck g δ k) (f : V → M)
    (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
    (Φ : neckBuffer δ → V) (hΦ : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ Φ)
    (hcomp : f ∘ Φ = N.chart) :
    (N.lift f hf Φ hΦ hcomp).normalizedMetric = N.normalizedMetric := rfl

@[simp] theorem lift_sphereMark (N : NormalizedNeck g δ k) (f : V → M)
    (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
    (Φ : neckBuffer δ → V) (hΦ : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ Φ)
    (hcomp : f ∘ Φ = N.chart) :
    (N.lift f hf Φ hΦ hcomp).sphereMark = N.sphereMark := rfl

@[simp] theorem lift_center (N : NormalizedNeck g δ k) (f : V → M)
    (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
    (Φ : neckBuffer δ → V) (hΦ : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ Φ)
    (hcomp : f ∘ Φ = N.chart) :
    (N.lift f hf Φ hΦ hcomp).center = Φ ⟨(N.sphereMark, 0), by
      have := inv_pos.mpr N.delta_pos
      constructor <;> linarith⟩ := rfl

theorem map_lift_center (N : NormalizedNeck g δ k) (f : V → M)
    (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
    (Φ : neckBuffer δ → V) (hΦ : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ Φ)
    (hcomp : f ∘ Φ = N.chart) :
    f (N.lift f hf Φ hΦ hcomp).center = N.center := by
  change f (Φ _) = N.center
  exact (congrFun hcomp _).trans N.marked

theorem map_lift_chart (N : NormalizedNeck g δ k) (f : V → M)
    (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
    (Φ : neckBuffer δ → V) (hΦ : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ Φ)
    (hcomp : f ∘ Φ = N.chart) :
    f ∘ (N.lift f hf Φ hΦ hcomp).chart = N.chart := hcomp

omit [T2Space M] in
theorem pullback_normalizedMetric
    (N : NormalizedNeck g δ k) (f : V → M)
    (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
    (Φ : neckBuffer δ → V) (hΦ : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Φ)
    (hcomp : f ∘ Φ = N.chart) :
    localPullMetric (scaleMetric N.scale N.scale_pos (localPullMetric g f hf)) Φ hΦ =
      N.normalizedMetric := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [localPullMetric_inner, scaleMetric_inner, localPullMetric_inner, N.normalized_inner]
  have hd := mfderiv_comp x ((hf (Φ x)).mdifferentiableAt (by simp))
    ((hΦ x).mdifferentiableAt (by simp))
  have hx : f (Φ x) = N.chart x := congrFun hcomp x
  have hdv : mfderiv ThreeModel ThreeModel f (Φ x) (mfderiv NeckCylinderModel ThreeModel Φ x v) =
      mfderiv NeckCylinderModel ThreeModel N.chart x v := by
    rw [← ContinuousLinearMap.comp_apply, ← hd, hcomp]
    rfl
  have hdw : mfderiv ThreeModel ThreeModel f (Φ x) (mfderiv NeckCylinderModel ThreeModel Φ x w) =
      mfderiv NeckCylinderModel ThreeModel N.chart x w := by
    rw [← ContinuousLinearMap.comp_apply, ← hd, hcomp]
    rfl
  congr 1
  exact congrArg₂ (fun V W => g.inner (f (Φ x)) V W) hdv hdw |>.trans (by rw [hx])

end NormalizedNeck

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
