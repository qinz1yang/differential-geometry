import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalRegularity

noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {M : Type*}

def toProductCurve (c : CurveMap M) : ProductCurve M where
  map x t := (c x t, 0)
  y _ _ := 0
  degree := 0
  lift_eq _ _ := by simp
  increment _ _ := by simp

@[simp] theorem toProductCurve_projection (c : CurveMap M) : c.toProductCurve.projection = c := rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def toProductField (c : CurveMap M) (V : c.Field (I := I)) : c.toProductCurve.Field (I := I) :=
  fun x t => (V x t, 0)

omit [IsManifold I ∞ M] in
@[simp] theorem toProductCurve_X (c : CurveMap M) :
    c.toProductCurve.X (I := I) = c.toProductField c.X := by
  funext x t
  change (c.X (I := I) x t, deriv (fun _ : ℝ => (0 : ℝ)) x) = (c.X (I := I) x t, 0)
  rw [deriv_const]

omit [IsManifold I ∞ M] in
@[simp] theorem toProductCurve_velocity (c : CurveMap M) (J : Set ℝ) :
    c.toProductCurve.velocity (I := I) J = c.toProductField (c.velocity J) := by
  funext x t
  change (c.velocity (I := I) J x t, derivWithin (Function.const ℝ (0 : ℝ)) J t) =
    (c.velocity (I := I) J x t, 0)
  rw [derivWithin_const]
  rfl

@[simp] theorem toProductCurve_speed (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda x t : ℝ) : c.toProductCurve.speed g lambda x t = c.speed g x t := by
  simp only [ProductCurve.speed, toProductCurve_X, ProductCurve.inner, toProductField,
    toProductCurve_projection, mul_zero, add_zero, speed]
  rfl

@[simp] theorem toProductCurve_unitTangent (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) : c.toProductCurve.unitTangent g lambda = c.toProductField (c.unitTangent g) := by
  funext x t
  simp only [ProductCurve.unitTangent, toProductCurve_speed, toProductCurve_X, toProductField,
    unitTangent]
  apply Prod.ext
  · rfl
  · exact smul_zero _

variable [FiniteDimensional ℝ E]

@[simp] theorem toProductCurve_Ds (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (V : c.Field (I := I)) :
    c.toProductCurve.Ds g lambda (c.toProductField V) = c.toProductField (c.Ds g V) := by
  funext x t
  simp only [ProductCurve.Ds, toProductCurve_speed, ProductCurve.Dx, toProductField,
    toProductCurve_projection, deriv_const, Ds, Dx]
  apply Prod.ext
  · rfl
  · exact smul_zero _

@[simp] theorem toProductCurve_curvatureVector (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) : c.toProductCurve.curvatureVector g lambda = c.toProductField (c.curvatureVector g) := by
  rw [ProductCurve.curvatureVector, toProductCurve_unitTangent, toProductCurve_Ds]
  rfl

@[simp] theorem toProductCurve_iteratedDs (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (m : ℕ) (V : c.Field (I := I)) :
    c.toProductCurve.iteratedDs g lambda m (c.toProductField V) = c.toProductField (c.iteratedDs g m V) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [ProductCurve.iteratedDs, iteratedDs, Function.iterate_succ_apply'] at ih ⊢
    rw [ih, toProductCurve_Ds]

omit [FiniteDimensional ℝ E] in
@[simp] theorem toProductCurve_normSq (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (V : c.Field (I := I)) (x t : ℝ) :
    c.toProductCurve.normSq g lambda (c.toProductField V) x t = c.normSq g V x t := by
  simp only [ProductCurve.normSq, ProductCurve.inner, toProductCurve_projection, toProductField,
    mul_zero, add_zero, normSq]
  rfl

@[simp] theorem toProductCurve_curvatureSq (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda x t : ℝ) : c.toProductCurve.curvatureSq g lambda x t = c.curvatureSq g x t := by
  rw [ProductCurve.curvatureSq, toProductCurve_curvatureVector, toProductCurve_normSq]
  rfl

@[simp] theorem toProductCurve_curvature (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda x t : ℝ) : c.toProductCurve.curvature g lambda x t = c.curvature g x t := by
  simp only [ProductCurve.curvature, toProductCurve_curvatureSq, curvature]

omit [FiniteDimensional ℝ E] in
@[simp] theorem toProductCurve_length (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda t : ℝ) : c.toProductCurve.length g lambda t = c.length g t := by
  simp only [ProductCurve.length, ProductCurve.integral, toProductCurve_speed, length, integral]

@[simp] theorem toProductCurve_totalCurvature (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda t : ℝ) : c.toProductCurve.totalCurvature g lambda t = c.totalCurvature g t := by
  simp only [ProductCurve.totalCurvature, ProductCurve.integral, toProductCurve_speed,
    toProductCurve_curvature, totalCurvature, integral]

omit [FiniteDimensional ℝ E] in
@[simp] theorem toProductCurve_arcLength (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda p q t : ℝ) : c.toProductCurve.arcLength g lambda p q t = c.arcLength g p q t := by
  simp only [ProductCurve.arcLength, toProductCurve_speed, arcLength]

@[simp] theorem toProductCurve_arcTotalCurvature (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda p q t : ℝ) : c.toProductCurve.arcTotalCurvature g lambda p q t = c.arcTotalCurvature g p q t := by
  simp only [ProductCurve.arcTotalCurvature, toProductCurve_speed, toProductCurve_curvature, arcTotalCurvature]

@[simp] theorem toProductCurve_isSolutionOn_iff (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (J : Set ℝ) : c.toProductCurve.IsSolutionOn g lambda J ↔ c.IsSolutionOn g J := by
  constructor
  · intro hc
    refine ⟨hc.smooth.1, ?_, ?_⟩
    · intro x t ht heq
      apply hc.immersed x t ht
      rw [toProductCurve_X]
      change (c.X (I := I) x t, (0 : ℝ)) = (0, 0)
      rw [heq]
    · intro x t ht
      have hh := congrArg Prod.fst (hc.equation x t ht)
      change (c.toProductCurve.velocity (I := I) J x t).1 =
        (c.toProductCurve.curvatureVector g lambda x t).1 at hh
      rw [toProductCurve_velocity, toProductCurve_curvatureVector] at hh
      exact hh
  · intro hc
    refine ⟨⟨hc.smooth, contDiffOn_const⟩, ?_, ?_⟩
    · intro x t ht heq
      apply hc.immersed x t ht
      have hh := congrArg Prod.fst heq
      rw [toProductCurve_X] at hh
      exact hh
    · intro x t ht
      simp only [toProductCurve_velocity, toProductCurve_curvatureVector, toProductField, hc.equation x t ht]

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap
