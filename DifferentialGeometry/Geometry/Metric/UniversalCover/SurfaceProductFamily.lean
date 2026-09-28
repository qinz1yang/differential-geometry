import DifferentialGeometry.Geometry.Curvature.DimensionOne.Flat
import DifferentialGeometry.Geometry.Curvature.Product
import DifferentialGeometry.Geometry.Metric.UniversalCover.Metric
import DifferentialGeometry.Geometry.Metric.Product
import DifferentialGeometry.Geometry.Metric.Pullback.Cross
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross

set_option autoImplicit false

universe uN

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover

open Bundle Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff InnerProductSpace

variable {ι : Type*}
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real (Fin 3 → Real) H}
variable [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
variable [LocallyPathConnectedSpace M]
variable [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
variable [Inhabited M]

structure SurfaceProductFamily
    (g : ι → SmoothRiemannianMetric I M) where
  N : Type uN
  [topologyN : TopologicalSpace N]
  [chartedN : ChartedSpace
    (Fin 2 → Real) N]
  [manifoldN : IsManifold
    (𝓘(Real, Fin 2 → Real))
    (↑(⊤ : ℕ∞) : WithTop ℕ∞) N]
  [t2N : T2Space N]
  surfaceMetric : ι → SmoothRiemannianMetric
    (𝓘(Real, Fin 2 → Real)) N
  F : Diffeomorph
    ((𝓘(Real, Fin 2 → Real)).prod
      𝓘(Real, Real)) I (N × Real)
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (↑(⊤ : ℕ∞) : WithTop ℕ∞)
  isometry : ∀ (t : ι) (y : N) (s : Real)
      (u v : TangentSpace
        (𝓘(Real, Fin 2 → Real)) y)
      (r q : Real),
    (liftedMetric (I := I) (g t)).inner (F (y, s))
        ((mfderiv
          ((𝓘(Real, Fin 2 → Real)).prod
            𝓘(Real, Real)) I (fun z : N × Real => F z) (y, s))
          (u, r))
        ((mfderiv
          ((𝓘(Real, Fin 2 → Real)).prod
            𝓘(Real, Real)) I (fun z : N × Real => F z) (y, s))
          (v, q)) =
      (surfaceMetric t).inner y u v + r * q

omit [I.Boundaryless] [T2Space M] in
theorem SurfaceProductFamily.horizontal_inner
    (g : ι → SmoothRiemannianMetric I M)
    (W : SurfaceProductFamily (I := I) (M := M) g) :
    let _ : TopologicalSpace W.N := W.topologyN
    let _ : ChartedSpace
        (Fin 2 → Real) W.N := W.chartedN
    let _ : IsManifold
        (𝓘(Real, Fin 2 → Real))
        (↑(⊤ : ℕ∞) : WithTop ℕ∞) W.N := W.manifoldN
    let _ : T2Space W.N := W.t2N
    ∀ (t : ι) (y : W.N) (s : Real)
      (u v : TangentSpace
        (𝓘(Real, Fin 2 → Real)) y),
    (liftedMetric (I := I) (g t)).inner (W.F (y, s))
        ((mfderiv
          ((𝓘(Real, Fin 2 → Real)).prod
            𝓘(Real, Real)) I (fun z : W.N × Real => W.F z) (y, s))
          (u, 0))
        ((mfderiv
          ((𝓘(Real, Fin 2 → Real)).prod
            𝓘(Real, Real)) I (fun z : W.N × Real => W.F z) (y, s))
          (v, 0)) =
      (W.surfaceMetric t).inner y u v := by
  dsimp
  let _ : TopologicalSpace W.N := W.topologyN
  let _ : ChartedSpace
      (Fin 2 → Real) W.N := W.chartedN
  let _ : IsManifold
      (𝓘(Real, Fin 2 → Real))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) W.N := W.manifoldN
  let _ : T2Space W.N := W.t2N
  intro t y s u v
  have h := W.isometry t y s u v 0 0
  simpa only [zero_mul, add_zero] using h

omit [I.Boundaryless] [T2Space M] in
theorem SurfaceProductFamily.vertical_inner
    (g : ι → SmoothRiemannianMetric I M)
    (W : SurfaceProductFamily (I := I) (M := M) g) :
    let _ : TopologicalSpace W.N := W.topologyN
    let _ : ChartedSpace
        (Fin 2 → Real) W.N := W.chartedN
    let _ : IsManifold
        (𝓘(Real, Fin 2 → Real))
        (↑(⊤ : ℕ∞) : WithTop ℕ∞) W.N := W.manifoldN
    let _ : T2Space W.N := W.t2N
    ∀ (t : ι) (y : W.N) (s r q : Real),
    (liftedMetric (I := I) (g t)).inner (W.F (y, s))
        ((mfderiv
          ((𝓘(Real, Fin 2 → Real)).prod
            𝓘(Real, Real)) I (fun z : W.N × Real => W.F z) (y, s))
          (0, r))
        ((mfderiv
          ((𝓘(Real, Fin 2 → Real)).prod
            𝓘(Real, Real)) I (fun z : W.N × Real => W.F z) (y, s))
          (0, q)) = r * q := by
  dsimp
  let _ : TopologicalSpace W.N := W.topologyN
  let _ : ChartedSpace
      (Fin 2 → Real) W.N := W.chartedN
  let _ : IsManifold
      (𝓘(Real, Fin 2 → Real))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) W.N := W.manifoldN
  let _ : T2Space W.N := W.t2N
  intro t y s r q
  have h := W.isometry t y s
    (0 : TangentSpace
      (𝓘(Real, Fin 2 → Real)) y)
    (0 : TangentSpace
      (𝓘(Real, Fin 2 → Real)) y) r q
  have hzero : (W.surfaceMetric t).inner y
      (0 : TangentSpace
        (𝓘(Real, Fin 2 → Real)) y)
      (0 : TangentSpace
        (𝓘(Real, Fin 2 → Real)) y) = 0 := by
    simp
  rw [hzero, zero_add] at h
  exact h

omit [I.Boundaryless] [T2Space M] in
theorem SurfaceProductFamily.mixed_inner
    (g : ι → SmoothRiemannianMetric I M)
    (W : SurfaceProductFamily (I := I) (M := M) g) :
    let _ : TopologicalSpace W.N := W.topologyN
    let _ : ChartedSpace
        (Fin 2 → Real) W.N := W.chartedN
    let _ : IsManifold
        (𝓘(Real, Fin 2 → Real))
        (↑(⊤ : ℕ∞) : WithTop ℕ∞) W.N := W.manifoldN
    let _ : T2Space W.N := W.t2N
    ∀ (t : ι) (y : W.N) (s : Real)
      (u : TangentSpace
        (𝓘(Real, Fin 2 → Real)) y)
      (r : Real),
    (liftedMetric (I := I) (g t)).inner (W.F (y, s))
        ((mfderiv
          ((𝓘(Real, Fin 2 → Real)).prod
            𝓘(Real, Real)) I (fun z : W.N × Real => W.F z) (y, s))
          (u, 0))
        ((mfderiv
          ((𝓘(Real, Fin 2 → Real)).prod
            𝓘(Real, Real)) I (fun z : W.N × Real => W.F z) (y, s))
          (0, r)) = 0 := by
  dsimp
  let _ : TopologicalSpace W.N := W.topologyN
  let _ : ChartedSpace
      (Fin 2 → Real) W.N := W.chartedN
  let _ : IsManifold
      (𝓘(Real, Fin 2 → Real))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) W.N := W.manifoldN
  let _ : T2Space W.N := W.t2N
  intro t y s u r
  have h := W.isometry t y s u
    (0 : TangentSpace
      (𝓘(Real, Fin 2 → Real)) y) 0 r
  have hzero : (W.surfaceMetric t).inner y u
      (0 : TangentSpace
        (𝓘(Real, Fin 2 → Real)) y) = 0 :=
    ((W.surfaceMetric t).inner y u).map_zero
  rw [hzero, zero_mul, add_zero] at h
  exact h

omit [I.Boundaryless] [T2Space M] in
set_option backward.isDefEq.respectTransparency false in
theorem SurfaceProductFamily.pullbackMetric_eq_prod
    (g : ι → SmoothRiemannianMetric I M)
    (data : SurfaceProductFamily (I := I) (M := M) g) :
    let _ : TopologicalSpace data.N := data.topologyN
    let _ : ChartedSpace
        (Fin 2 → Real) data.N := data.chartedN
    let _ : IsManifold
        (𝓘(Real, Fin 2 → Real))
        (↑(⊤ : ℕ∞) : WithTop ℕ∞) data.N := data.manifoldN
    let _ : T2Space data.N := data.t2N
    ∀ t : ι,
      Diffeomorph.pullbackMetricCross
          (I := (𝓘(Real, Fin 2 → Real)).prod
            𝓘(Real, Real))
          (J := I) (liftedMetric (I := I) (g t)) data.F =
        (data.surfaceMetric t).prod (euclideanMetric (E := Real)) := by
  dsimp
  let _ : TopologicalSpace data.N := data.topologyN
  let _ : ChartedSpace
      (Fin 2 → Real) data.N := data.chartedN
  let _ : IsManifold
      (𝓘(Real, Fin 2 → Real))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) data.N := data.manifoldN
  let _ : T2Space data.N := data.t2N
  intro t
  apply SmoothRiemannianMetric.ext_inner
  intro z u v
  rw [Diffeomorph.pullbackMetricCross_inner]
  rw [SmoothRiemannianMetric.prod_inner]
  have hflat : (euclideanMetric (E := Real)).inner z.2 u.2 v.2 = u.2 * v.2 := by
    change inner Real u.2 v.2 = _
    rw [RCLike.inner_apply]
    simp
    ring
  rw [hflat]
  exact data.isometry t z.1 z.2 u.1 v.1 u.2 v.2

theorem SurfaceProductFamily.surface_scalar_eq_lifted
    (g : ι → SmoothRiemannianMetric I M)
    (data : SurfaceProductFamily (I := I) (M := M) g) :
    let _ : TopologicalSpace data.N := data.topologyN
    let _ : ChartedSpace
        (Fin 2 → Real) data.N := data.chartedN
    let _ : IsManifold
        (𝓘(Real, Fin 2 → Real))
        (↑(⊤ : ℕ∞) : WithTop ℕ∞) data.N := data.manifoldN
    let _ : T2Space data.N := data.t2N
    ∀ (t : ι) (y : data.N) (s : Real),
      metricScalarAt
          (I := 𝓘(Real, Fin 2 → Real))
          (data.surfaceMetric t) y =
        metricScalarAt (I := I)
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) (g t)) (data.F (y, s)) := by
  dsimp
  let _ : TopologicalSpace data.N := data.topologyN
  let _ : ChartedSpace
      (Fin 2 → Real) data.N := data.chartedN
  let _ : IsManifold
      (𝓘(Real, Fin 2 → Real))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) data.N := data.manifoldN
  let _ : T2Space data.N := data.t2N
  intro t y s
  have hprod :
      metricScalarAt ((data.surfaceMetric t).prod (euclideanMetric (E := Real))) (y, s) =
        metricScalarAt (data.surfaceMetric t) y := by
    rw [metricScalarAt_productMetric,
      metricScalarAt_eq_zero_of_finrank_le_one (euclideanMetric (E := Real)) (by simp), add_zero]
  have hpull := DifferentialGeometry.CheegerGromovCompactness.metricScalar_cross
    (I := (𝓘(Real, Fin 2 → Real)).prod
      𝓘(Real, Real))
    (J := I) (g := liftedMetric (I := I) (g t)) (Phi := data.F)
    (x := (y, s))
  have heq := SurfaceProductFamily.pullbackMetric_eq_prod (I := I) (M := M) g data t
  have heqscalar := congrArg
      (fun q : SmoothRiemannianMetric
        ((𝓘(Real, Fin 2 → Real)).prod
          𝓘(Real, Real)) (data.N × Real) =>
        metricScalarAt
          (I := (𝓘(Real, Fin 2 → Real)).prod
            𝓘(Real, Real)) q (y, s)) heq
  rw [hprod] at heqscalar
  exact heqscalar.symm.trans hpull

omit [I.Boundaryless] [T2Space M] in
theorem SurfaceProductFamily.vertical_inner_eq
    (g : ι → SmoothRiemannianMetric I M)
    (data : SurfaceProductFamily (I := I) (M := M) g) :
    let _ : TopologicalSpace data.N := data.topologyN
    let _ : ChartedSpace
        (Fin 2 → Real) data.N := data.chartedN
    let _ : IsManifold
        (𝓘(Real, Fin 2 → Real))
        (↑(⊤ : ℕ∞) : WithTop ℕ∞) data.N := data.manifoldN
    let _ : T2Space data.N := data.t2N
    ∀ (t₁ t₂ : ι) (y : data.N) (s r q : Real),
      (liftedMetric (I := I) (g t₁)).inner (data.F (y, s))
          ((mfderiv
            ((𝓘(Real, Fin 2 → Real)).prod
              𝓘(Real, Real)) I (fun z : data.N × Real => data.F z) (y, s))
            (0, r))
          ((mfderiv
            ((𝓘(Real, Fin 2 → Real)).prod
              𝓘(Real, Real)) I (fun z : data.N × Real => data.F z) (y, s))
            (0, q)) =
        (liftedMetric (I := I) (g t₂)).inner (data.F (y, s))
          ((mfderiv
            ((𝓘(Real, Fin 2 → Real)).prod
              𝓘(Real, Real)) I (fun z : data.N × Real => data.F z) (y, s))
            (0, r))
          ((mfderiv
            ((𝓘(Real, Fin 2 → Real)).prod
              𝓘(Real, Real)) I (fun z : data.N × Real => data.F z) (y, s))
            (0, q)) := by
  dsimp
  let _ : TopologicalSpace data.N := data.topologyN
  let _ : ChartedSpace
      (Fin 2 → Real) data.N := data.chartedN
  let _ : IsManifold
      (𝓘(Real, Fin 2 → Real))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) data.N := data.manifoldN
  let _ : T2Space data.N := data.t2N
  intro t₁ t₂ y s r q
  rw [SurfaceProductFamily.vertical_inner g data, SurfaceProductFamily.vertical_inner g data]

omit [I.Boundaryless] [T2Space M] in
set_option backward.isDefEq.respectTransparency false in
theorem surface_metric_unique_of_pullback_eq_prod
    {N : Type*}
    [TopologicalSpace N]
    [ChartedSpace (Fin 2 → Real) N]
    [IsManifold
      (𝓘(Real, Fin 2 → Real))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) N]
    [T2Space N]
    (g : ι → SmoothRiemannianMetric I M)
    (F : Diffeomorph
      ((𝓘(Real, Fin 2 → Real)).prod
        𝓘(Real, Real)) I (N × Real)
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞))
    (h₁ h₂ : ι → SmoothRiemannianMetric
      (𝓘(Real, Fin 2 → Real)) N)
    (hh₁ : ∀ t : ι,
      Diffeomorph.pullbackMetricCross
          (I := (𝓘(Real, Fin 2 → Real)).prod
            𝓘(Real, Real))
          (J := I) (liftedMetric (I := I) (g t)) F =
        (h₁ t).prod (euclideanMetric (E := Real)))
    (hh₂ : ∀ t : ι,
      Diffeomorph.pullbackMetricCross
          (I := (𝓘(Real, Fin 2 → Real)).prod
            𝓘(Real, Real))
          (J := I) (liftedMetric (I := I) (g t)) F =
        (h₂ t).prod (euclideanMetric (E := Real))) :
    ∀ t : ι, h₁ t = h₂ t := by
  intro t
  apply SmoothRiemannianMetric.ext_inner
  intro y u v
  have heq : (h₁ t).prod (euclideanMetric (E := Real)) =
      (h₂ t).prod (euclideanMetric (E := Real)) := (hh₁ t).symm.trans (hh₂ t)
  have he := congrArg
      (fun G => G.inner (y, (0 : Real))
        ((u, (0 : Real)) : TangentSpace
          ((𝓘(Real, Fin 2 → Real)).prod
            𝓘(Real, Real)) (y, (0 : Real)))
        ((v, (0 : Real)) : TangentSpace
          ((𝓘(Real, Fin 2 → Real)).prod
            𝓘(Real, Real)) (y, (0 : Real)))) heq
  rw [DifferentialGeometry.SmoothRiemannianMetric.prod_inner (h₁ t)
      (euclideanMetric (E := Real)) (y, (0 : Real)) (u, (0 : Real)) (v, (0 : Real)),
    DifferentialGeometry.SmoothRiemannianMetric.prod_inner (h₂ t)
      (euclideanMetric (E := Real)) (y, (0 : Real)) (u, (0 : Real)) (v, (0 : Real))] at he
  have hflat : ∀ x : Real,
      (euclideanMetric (E := Real)).inner x (0 : Real) (0 : Real) = 0 := by
    intro x
    change inner Real (0 : Real) (0 : Real) = 0
    simp
  simp only [hflat, add_zero] at he
  exact he

end DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover

end
