import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.RampAngleEvolution

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    {D : RealTimeInterval} {a b : ℝ}

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem ProductCurve.inner_self_nonneg (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda x t : ℝ) (V : c.Field (I := I)) :
    0 ≤ c.inner g lambda x t (V x t) (V x t) := by
  rw [ProductCurve.inner]
  have h1 : 0 ≤ (g t).inner (c.projection.lift x t) (V x t).1 (V x t).1 :=
    DifferentialGeometry.metric_inner_self_nonneg (g t) (c.projection.lift x t) (V x t).1
  nlinarith [sq_nonneg ((V x t).2)]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem ProductCurve.inner_X_self_eq_speed_sq (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda x t : ℝ) :
    c.inner g lambda x t (c.X (I := I) x t) (c.X (I := I) x t) =
      c.speed g lambda x t ^ 2 := by
  rw [ProductCurve.speed,
    Real.sq_sqrt (ProductCurve.inner_self_nonneg c g lambda x t (c.X (I := I)))]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem ProductCurve.inner_unitTangent_self_le_one (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda x t : ℝ) :
    c.inner g lambda x t (c.unitTangent g lambda x t) (c.unitTangent g lambda x t) ≤ 1 := by
  rw [ProductCurve.unitTangent]
  have hsmul : c.inner g lambda x t
      ((c.speed g lambda x t)⁻¹ • c.X (I := I) x t)
      ((c.speed g lambda x t)⁻¹ • c.X (I := I) x t) =
      (c.speed g lambda x t)⁻¹ * (c.speed g lambda x t)⁻¹ *
        c.inner g lambda x t (c.X (I := I) x t) (c.X (I := I) x t) := by
    simp only [map_smul, smul_apply, smul_eq_mul, ProductCurve.inner, Prod.smul_fst, Prod.smul_snd]
    ring
  rw [hsmul, ProductCurve.inner_X_self_eq_speed_sq]
  by_cases h : c.speed g lambda x t = 0
  · simp [h]
  · field_simp
    norm_num

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem ProductCurve.first_component_inner_le_one (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda x t : ℝ) :
    (g t).inner (c.projection.lift x t) (c.unitTangent g lambda x t).1
      (c.unitTangent g lambda x t).1 ≤ 1 := by
  have hsplit : c.inner g lambda x t (c.unitTangent g lambda x t) (c.unitTangent g lambda x t) =
      (g t).inner (c.projection.lift x t) (c.unitTangent g lambda x t).1
          (c.unitTangent g lambda x t).1 +
        lambda ^ 2 * ((c.unitTangent g lambda x t).2 * (c.unitTangent g lambda x t).2) := by
    rw [ProductCurve.inner]
    ring
  have hle := ProductCurve.inner_unitTangent_self_le_one c g lambda x t
  nlinarith [sq_nonneg lambda, sq_nonneg ((c.unitTangent g lambda x t).2), hsplit, hle]

omit [SigmaCompactSpace M] in
theorem ProductCurve.ricciTangent_lower_bound (B : RicciBackground (I := I) (M := M) D a b)
    (lambda x t : ℝ) (ht : t ∈ Icc a b) (c : ProductCurve M) :
    -(B.B₀) ≤ c.ricciTangent B.family lambda x t := by
  rw [ProductCurve.ricciTangent]
  have hle := ProductCurve.first_component_inner_le_one c B.family.metric lambda x t
  have h := ricci_pair_ge B t ht (p := c.projection.lift x t)
    (c.unitTangent B.family.metric lambda x t).1
  have h2 : -(B.B₀) ≤ -(B.B₀ * (B.family.metric t).inner (c.projection.lift x t)
      (c.unitTangent B.family.metric lambda x t).1
      (c.unitTangent B.family.metric lambda x t).1) := by
    nlinarith [B.B₀_nonneg, hle]
  linarith

omit [SigmaCompactSpace M] in
theorem ProductCurve.curvatureSq_add_ricciTangent_lower_bound
    (B : RicciBackground (I := I) (M := M) D a b) (lambda x t : ℝ) (ht : t ∈ Icc a b)
    (c : ProductCurve M) :
    -(B.B₀) ≤ c.curvatureSq B.family.metric lambda x t + c.ricciTangent B.family lambda x t := by
  have h1 := ProductCurve.ricciTangent_lower_bound B lambda x t ht c
  have h2 : 0 ≤ c.curvatureSq B.family.metric lambda x t :=
    ProductCurve.inner_self_nonneg c B.family.metric lambda x t
      (c.curvatureVector B.family.metric lambda)
  linarith

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
