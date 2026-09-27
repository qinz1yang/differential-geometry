import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Local
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalAlternativeTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PositiveComponentModels

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle

universe u

private instance roundSphereFourFinrank :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

section ScaledEigenvalue

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
theorem secLower_iff_eigenvalue_lower_bound (g : SmoothRiemannianMetric I3 M) (c : ℝ)
    (U : Set M) :
    SecLower g c U ↔ ∀ y ∈ U, c ≤ leastCurvatureOperatorEigenvalueAt (I := I3) g y
      (metricAlgebraicCurvatureTensorAt (I := I3) (M := M) g y) :=
  secLower_iff_le_leastCurvatureOperatorEigenvalueAt g (by simp [ThreeSpace]) c U

omit [SigmaCompactSpace M] in
theorem secLower_iff_scaled_eigenvalue_lower_bound {a c : ℝ} (ha : 0 < a)
    (g : SmoothRiemannianMetric I3 M) (U : Set M) :
    SecLower (scaleMetric (I := I3) a ha g) c U ↔
      ∀ y ∈ U, c ≤ leastCurvatureOperatorEigenvalueAt (I := I3)
        (scaleMetric (I := I3) a ha g) y
        (metricAlgebraicCurvatureTensorAt (I := I3) (M := M)
          (scaleMetric (I := I3) a ha g) y) :=
  secLower_iff_le_leastCurvatureOperatorEigenvalueAt (scaleMetric (I := I3) a ha g)
    (by simp [ThreeSpace]) c U

omit [SigmaCompactSpace M] in
theorem secLower_of_scaled_eigenvalue_lower_bound {a c : ℝ} (ha : 0 < a)
    (g : SmoothRiemannianMetric I3 M) {U : Set M}
    (h : ∀ y ∈ U, c ≤ leastCurvatureOperatorEigenvalueAt (I := I3)
      (scaleMetric (I := I3) a ha g) y
      (metricAlgebraicCurvatureTensorAt (I := I3) (M := M)
        (scaleMetric (I := I3) a ha g) y)) :
    SecLower g (c * a) U :=
  (secLower_scaleMetric_iff ha g U).mp ((secLower_iff_scaled_eigenvalue_lower_bound ha g U).mpr h)

theorem canonicalAlternative_transport_positive_of_scaled_eigenvalue_lower_bound
    {P : Type u} [TopologicalSpace P] [ChartedSpace ThreeSpace P] [IsManifold I3 ∞ P]
    [T2Space P] [SigmaCompactSpace P]
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
    {x : M} {t : ℝ} {eps C : ℝ} {U : Set P}
    (data : PositiveComponent (M := P) U) (e : PartialDiffeomorph I3 I3 P M ∞)
    (he : U ⊆ e.source) (hwhole : e '' U = connectedComponent x)
    (hQ : 0 < S.scalar t x) {c : ℝ} (hc : C⁻¹ ≤ c)
    (h : ∀ y ∈ e '' U, c ≤ leastCurvatureOperatorEigenvalueAt (I := I3)
      (scaleMetric (I := I3) (S.scalar t x) hQ (S.base.metric t)) y
      (metricAlgebraicCurvatureTensorAt (I := I3) (M := M)
        (scaleMetric (I := I3) (S.scalar t x) hQ (S.base.metric t)) y)) :
    Nonempty (CanonicalAlternative S eps C x t (connectedComponent x)) :=
  canonicalAlternative_transport_positive data e he hwhole
    (secLower_of_scaleInvariant_lower_bound S hQ hc h)

end ScaledEigenvalue

theorem secLower_scaleMetric_roundMetricSphereThree {a : ℝ} (ha : 0 < a) :
    SecLower (M := Sphere 3)
      (scaleMetric (I := I3) a ha
        (roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3))) a⁻¹ Set.univ :=
  (secLower_scaleMetric_iff ha (roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3))
    Set.univ).mpr (by
      rw [inv_mul_cancel₀ ha.ne']
      exact secLower_roundMetricSphereThree)

theorem one_le_leastCurvatureOperatorEigenvalueAt_roundMetricSphereThree :
    ∀ y : Sphere 3, 1 ≤ leastCurvatureOperatorEigenvalueAt (I := I3)
      (roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3)) y
      (metricAlgebraicCurvatureTensorAt (I := I3) (M := Sphere 3)
        (roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3)) y) :=
  fun y => (secLower_iff_eigenvalue_lower_bound
      (roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3)) 1 Set.univ).mp
    secLower_roundMetricSphereThree y (Set.mem_univ y)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.DifferentialGeometry.Manifold ContDiff

universe u

variable {M N : Type u}
  [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N] [T2Space N]

theorem secLower_image_of_openPullbackMetric
    (F : PartialDiffeomorph I3 I3 N M ∞) {U : Set N} (hU : U ⊆ F.source)
    (g : SmoothRiemannianMetric I3 M) {c : ℝ}
    (h : SecLower (openPullbackMetric F (sourceOpen F) (sourceOpen_subset F) g) c
      (Subtype.val ⁻¹' U)) :
    SecLower g c (F '' U) := by
  rintro z ⟨y, hy, rfl⟩ v w
  let Ω := sourceOpen F
  let V : TopologicalSpace.Opens M :=
    ⟨F '' (Ω : Set N), image_opens_isOpen F (sourceOpen_subset F)⟩
  let Φ : Ω ≃ₘ⟮I3, I3⟯ V := PartialDiffeomorph.toOpensDiffeo F (sourceOpen_subset F)
  let y' : Ω := ⟨y, hU hy⟩
  have hderiv (a : TangentSpace I3 y') :
      Φ.mfderivToContinuousLinearEquiv (by simp) y' a = mfderiv I3 I3 F y a := by
    have he := congrArg (fun L : TangentSpace I3 y' →L[ℝ] TangentSpace I3 (Φ y') => L a)
      (Diffeomorph.mfderivToContinuousLinearEquiv_coe Φ (by simp) (x := y'))
    exact he.trans (PartialDiffeomorph.mfderiv_toOpensDiffeo F (sourceOpen_subset F) y' a)
  obtain ⟨a, ha⟩ := (Φ.mfderivToContinuousLinearEquiv (by simp) y').surjective v
  obtain ⟨b, hb⟩ := (Φ.mfderivToContinuousLinearEquiv (by simp) y').surjective w
  rw [hderiv] at ha hb
  have hab := h y' hy a b
  rw [openPullbackMetric_inner, openPullbackMetric_inner, openPullbackMetric_inner,
    ha, hb] at hab
  have hcurv := metricRm04StandardAt_pullback_localDiffeo g V Ω Φ y' a b b a
  dsimp only [Φ] at hcurv
  erw [PartialDiffeomorph.mfderiv_toOpensDiffeo F (sourceOpen_subset F) y' a,
    PartialDiffeomorph.mfderiv_toOpensDiffeo F (sourceOpen_subset F) y' b] at hcurv
  change metricRm04StandardAt (openPullbackMetric F Ω (sourceOpen_subset F) g) y' a b b a =
    metricRm04StandardAt g (F y) (mfderiv I3 I3 F y a) (mfderiv I3 I3 F y b)
      (mfderiv I3 I3 F y b) (mfderiv I3 I3 F y a) at hcurv
  rw [ha, hb] at hcurv
  have htuple {P : Type u} [TopologicalSpace P] [ChartedSpace ThreeSpace P]
      (p : P) (a b : TangentSpace I3 p) :
      vec4 (I := I3) (x := p) a b b a = (fun i : Fin 4 => ![a, b, b, a] i) := by
    ext i
    fin_cases i <;> rfl
  simp only [metricRm04StandardAt_apply] at hcurv
  erw [htuple, htuple] at hcurv
  exact hcurv ▸ hab

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
