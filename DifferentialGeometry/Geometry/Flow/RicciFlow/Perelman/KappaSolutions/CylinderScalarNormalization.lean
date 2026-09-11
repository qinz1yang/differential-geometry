import DifferentialGeometry.Geometry.Metric.Product.ScalarCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropyBasic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderDeckRecentering
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderAxialNormalization
import DifferentialGeometry.Geometry.Curvature.Sphere.ConstCurvature
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff BigOperators

local notation "SphereAmbient" => EuclideanSpace ℝ (Fin 3)
local notation "SphereTwo" => Metric.sphere (0 : SphereAmbient) 1
local notation "Cylinder" => SphereTwo × ℝ
local notation "CylinderI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
local notation "sphereMetric" => roundMetric (E := SphereAmbient) (n := 2)

private local instance scalarCylinderSphereDimension :
    Fact (Module.finrank ℝ SphereAmbient = 2 + 1) := ⟨by simp⟩
private local instance scalarCylinderSphereC1 : IsManifold (𝓡 2) 1 SphereTwo :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance scalarCylinderC1 : IsManifold CylinderI 1 Cylinder :=
  IsManifold.of_le (n := ∞) (by decide)

theorem roundSphereTwo_metricScalarAt (x : SphereTwo) :
    metricScalarAt (I := 𝓡 2) sphereMetric x = 2 := by
  classical
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 2) x) = 2 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2
    simp
  have hb := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis
    (I := 𝓡 2) sphereMetric x
  rw [hdim] at hb
  obtain ⟨b, hb⟩ := hb
  rw [metricScalarAt_eq_sum_sum_rm04_of_orthonormal sphereMetric b hb]
  change (∑ i : Fin 2, ∑ j : Fin 2,
    metricRm04StandardAt (I := 𝓡 2) sphereMetric x (b j) (b i) (b i) (b j)) = 2
  simp_rw [roundMetric_sec_value, hb]
  norm_num [Fin.sum_univ_two]

theorem metricScalarAt_roundCylinder_of_inner_eq
    (gP : SmoothRiemannianMetric CylinderI Cylinder) (c : ℝ) (hc : 0 < c)
    (hproduct : ∀ (x : SphereTwo) (s : ℝ)
      (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
      gP.inner (x, s) (v, a) (w, b) = c * (sphereMetric).inner x v w + a * b)
    (p : Cylinder) : metricScalarAt (I := CylinderI) gP p = 2 / c := by
  have hscaled : ∀ (x : SphereTwo) (s : ℝ)
      (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
      gP.inner (x, s) (v, a) (w, b) =
        (scaleMetric c hc sphereMetric).inner x v w + a * b := by
    intro x s v w a b
    rw [scaleMetric_inner]
    exact hproduct x s v w a b
  rw [metricScalarAt_product_real_of_inner_eq (scaleMetric c hc sphereMetric)
    gP hscaled p.1 p.2, metricScalarAt_scaleMetric, roundSphereTwo_metricScalarAt]
  ring

theorem doubleSphereCylinderMetric_scalar (p : SpatialNeckCylinder) :
    metricScalarAt (I := SpatialNeckCylinderModel) doubleSphereCylinderMetric p = 1 := by
  have h := metricScalarAt_roundCylinder_of_inner_eq doubleSphereCylinderMetric 2
    (by norm_num) doubleSphereCylinderMetric_inner p
  norm_num at h ⊢
  exact h

section Marking

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

private local instance scalarCylinderBaseC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

theorem cylinder_parameter_eq_one_of_scalar_base_one
    (g : SmoothRiemannianMetric I M) (T : ℝ) (hT : 0 < T)
    (d : Cylinder ≃ₘ⟮CylinderI, I⟯ M)
    (hproduct : ∀ (x : SphereTwo) (s : ℝ)
      (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
      g.inner (d (x, s)) (mfderiv CylinderI I d (x, s) (v, a))
        (mfderiv CylinderI I d (x, s) (w, b)) =
          (2 * T) * (sphereMetric).inner x v w + a * b)
    (p : M) (hscalar : metricScalarAt (I := I) g p = 1) : T = 1 := by
  let gP := Diffeomorph.pullbackMetricCross g d
  have hinner : ∀ (x : SphereTwo) (s : ℝ)
      (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
      gP.inner (x, s) (v, a) (w, b) =
        (2 * T) * (sphereMetric).inner x v w + a * b := by
    intro x s v w a b
    exact (Diffeomorph.pullbackMetricCross_inner g d (x, s) (v, a) (w, b)).trans
      (hproduct x s v w a b)
  have hvalue := metricScalarAt_roundCylinder_of_inner_eq gP (2 * T)
    (by positivity) hinner (d.symm p)
  have hpull := metricScalar_cross g d (d.symm p)
  rw [d.apply_symm_apply, hscalar] at hpull
  have heq : (1 : ℝ) = 2 / (2 * T) := hpull.symm.trans hvalue
  have h := (eq_div_iff (by positivity : (2 * T) ≠ 0)).mp heq
  linarith

theorem exists_marked_normalized_cylinder
    (g : ℝ → SmoothRiemannianMetric I M) (T : ℝ) (hT : 0 < T)
    (d : Cylinder ≃ₘ⟮CylinderI, I⟯ M)
    (hproduct : ∀ t : ℝ, t ≤ 0 → ∀ (x : SphereTwo) (s : ℝ)
      (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
      (g t).inner (d (x, s)) (mfderiv CylinderI I d (x, s) (v, a))
        (mfderiv CylinderI I d (x, s) (w, b)) =
          (2 * (T - t)) * (sphereMetric).inner x v w + a * b)
    (p : M) (hscalar : metricScalarAt (I := I) (g 0) p = 1) :
    ∃ (yStar : SphereTwo) (e : Cylinder ≃ₘ⟮CylinderI, I⟯ M),
      e (yStar, 0) = p ∧
      Diffeomorph.pullbackMetricCross (g 0) e = doubleSphereCylinderMetric ∧
      ∀ t : ℝ, t ≤ 0 → ∀ (x : SphereTwo) (s : ℝ)
        (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
        (g t).inner (e (x, s)) (mfderiv CylinderI I e (x, s) (v, a))
          (mfderiv CylinderI I e (x, s) (w, b)) =
            (2 * (1 - t)) * (sphereMetric).inner x v w + a * b := by
  have hT1 := cylinder_parameter_eq_one_of_scalar_base_one (g 0) T hT d
    (by simpa only [sub_zero] using hproduct 0 le_rfl) p hscalar
  subst T
  let q := d.symm p
  let e := (cylinderLineTranslation q.2).trans d
  have hmarked : e (q.1, 0) = p := by
    change d (q.1, (0 : ℝ) + q.2) = p
    rw [zero_add]
    exact d.apply_symm_apply p
  have hderiv (x : SphereTwo) (s : ℝ) (v : TangentSpace (𝓡 2) x) (a : ℝ) :
      mfderiv CylinderI I e (x, s) (v, a) =
        mfderiv CylinderI I d (x, s + q.2) (v, a) := by
    change mfderiv CylinderI I
      ((d : Cylinder → M) ∘ cylinderLineTranslation q.2) (x, s) (v, a) = _
    have h := mfderiv_comp_apply (x, s)
      (d.mdifferentiable (by decide) (cylinderLineTranslation q.2 (x, s)))
      ((cylinderLineTranslation q.2).mdifferentiable (by decide) (x, s)) (v, a)
    rw [mfderiv_cylinderLineTranslation, cylinderLineTranslation_apply] at h
    exact h
  have hmetric : ∀ t : ℝ, t ≤ 0 → ∀ (x : SphereTwo) (s : ℝ)
      (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
      (g t).inner (e (x, s)) (mfderiv CylinderI I e (x, s) (v, a))
        (mfderiv CylinderI I e (x, s) (w, b)) =
          (2 * (1 - t)) * (sphereMetric).inner x v w + a * b := by
    intro t ht x s v w a b
    rw [hderiv, hderiv]
    exact hproduct t ht x (s + q.2) v w a b
  refine ⟨q.1, e, hmarked, ?_, hmetric⟩
  apply SmoothRiemannianMetric.ext_inner
  intro z V W
  rcases z with ⟨x, s⟩
  rcases V with ⟨v, a⟩
  rcases W with ⟨w, b⟩
  have hpull := Diffeomorph.pullbackMetricCross_inner (g 0) e (x, s) (v, a) (w, b)
  have hzero := hmetric 0 le_rfl x s v w a b
  have hmodel := doubleSphereCylinderMetric_inner x s v w a b
  exact hpull.trans (hzero.trans (by simpa only [sub_zero, mul_one] using hmodel.symm))

end Marking

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
