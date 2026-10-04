import DifferentialGeometry.Geometry.Thurston.SphericalProductQuotient
import DifferentialGeometry.Geometry.Thurston.ElementaryModels
import DifferentialGeometry.Geometry.Curvature.RicciPullback
import DifferentialGeometry.Geometry.Curvature.Product
import DifferentialGeometry.Geometry.Curvature.RoundSphere
import DifferentialGeometry.Geometry.Curvature.Line
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderDeckProductForm

/-!
# Isometries of the model `S² × ℝ` are product isometries

Chapter 7, packet P8b. The Ricci tensor of the model metric `sphericalProductModelMetric` is
the round metric of the sphere factor (`ricciTensor_sphericalProductModelMetric`), so its kernel
is the line factor. An isometry preserves the Ricci tensor (`ricciTensor_pullbackMetricCross`),
hence maps the line factor to itself and, being orthogonal, the sphere factor to itself. It then
preserves every metric `λ g_{S²} + dt²`, and the two-scale product theorem
`cylinderDeck_exists_orthogonal_product` shows it is `(x, s) ↦ (A x, ε s + c)`:
`exists_cylinderIsometry_of_isometry` writes it as `cylinderAct γ` with `γ : CylinderIsometry`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff

namespace GC.Geometry.SphericalProduct

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "CI" => SpatialNeckCylinderModel
local notation "gS" => roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

private local instance sphericalProductIsometryDimension :
    Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

private theorem gS_inner_zero_left (q : SpatialNeckSphere) (x : E2) :
    (gS).inner q (0 : E2) x = 0 := by
  have h := map_zero ((gS).inner q)
  exact congrArg (fun L : TangentSpace (𝓡 2) q →L[ℝ] ℝ => L x) h

private theorem gS_inner_zero_right (q : SpatialNeckSphere) (x : E2) :
    (gS).inner q x (0 : E2) = 0 :=
  map_zero ((gS).inner q x)

theorem sphericalProductModelMetric_inner (p : SpatialNeckCylinder)
    (V W : TangentSpace CI p) :
    sphericalProductModelMetric.inner p V W = (gS).inner p.1 V.1 W.1 + V.2 * W.2 := by
  rw [sphericalProductModelMetric_eq_prod, SmoothRiemannianMetric.prod_inner]
  change _ + inner ℝ V.2 W.2 = _ + V.2 * W.2
  congr 1
  exact mul_comm W.2 V.2

theorem ricciTensor_sphericalProductModelMetric (p : SpatialNeckCylinder)
    (V W : TangentSpace CI p) :
    ricciTensor sphericalProductModelMetric p V W = (gS).inner p.1 V.1 W.1 := by
  have h1 := ricciTensor_productMetric gS (DifferentialGeometry.euclideanMetric (E := ℝ)) p V W
  have h2 := ricciTensor_roundSphere (E := E3) (n := 2) p.1 V.1 W.1
  have h3 := ricciTensor_line_eq_zero (DifferentialGeometry.euclideanMetric (E := ℝ)) p.2 V.2 W.2
  calc ricciTensor sphericalProductModelMetric p V W =
        ricciTensor ((gS).prod (DifferentialGeometry.euclideanMetric (E := ℝ))) p V W := by
          rw [sphericalProductModelMetric_eq_prod]
    _ = (((2 : ℕ) : ℝ) - 1) * (gS).inner p.1 V.1 W.1 + 0 := by
          rw [h1, h2, h3]
    _ = (gS).inner p.1 V.1 W.1 := by norm_num

variable (Φ : SpatialNeckCylinder ≃ₘ⟮CI, CI⟯ SpatialNeckCylinder)
  (hΦ : ∀ (p : SpatialNeckCylinder) (V W : TangentSpace CI p),
    sphericalProductModelMetric.inner (Φ p) (mfderiv CI CI Φ p V) (mfderiv CI CI Φ p W) =
      sphericalProductModelMetric.inner p V W)

include hΦ in
theorem isometry_components (p : SpatialNeckCylinder) (V W : E2 × ℝ) :
    (gS).inner (Φ p).1 (mfderiv CI CI Φ p V).1 (mfderiv CI CI Φ p W).1 +
        (mfderiv CI CI Φ p V).2 * (mfderiv CI CI Φ p W).2 =
      (gS).inner p.1 V.1 W.1 + V.2 * W.2 :=
  (sphericalProductModelMetric_inner (Φ p) (mfderiv CI CI Φ p V) (mfderiv CI CI Φ p W)).symm.trans
    ((hΦ p V W).trans (sphericalProductModelMetric_inner p V W))

include hΦ in
theorem mfderiv_vertical_fst_eq_zero (p : SpatialNeckCylinder) :
    (mfderiv CI CI Φ p ((0, 1) : E2 × ℝ)).1 = 0 := by
  have hpull : Diffeomorph.pullbackMetricCross sphericalProductModelMetric Φ =
      sphericalProductModelMetric := by
    apply SmoothRiemannianMetric.ext_inner
    intro x V W
    rw [Diffeomorph.pullbackMetricCross_inner]
    exact hΦ x V W
  have h := ricciTensor_pullbackMetricCross sphericalProductModelMetric Φ p
    ((0, 1) : E2 × ℝ) ((0, 1) : E2 × ℝ)
  rw [hpull] at h
  have hL := ricciTensor_sphericalProductModelMetric p ((0, 1) : E2 × ℝ) ((0, 1) : E2 × ℝ)
  have hR := ricciTensor_sphericalProductModelMetric (Φ p) (mfderiv CI CI Φ p ((0, 1) : E2 × ℝ))
    (mfderiv CI CI Φ p ((0, 1) : E2 × ℝ))
  have h' := hL.symm.trans (h.trans hR)
  have h0 := gS_inner_zero_left p.1 0
  by_contra hne
  have hpos := (gS).pos (Φ p).1 _ hne
  change (gS).inner p.1 (0 : E2) (0 : E2) = _ at h'
  rw [h0] at h'
  linarith

include hΦ in
theorem isometry_scaled (p : SpatialNeckCylinder) (lam : ℝ) (v w : E2) (a c : ℝ) :
    lam * (gS).inner (Φ p).1 (mfderiv CI CI Φ p ((v, a) : E2 × ℝ)).1
        (mfderiv CI CI Φ p ((w, c) : E2 × ℝ)).1 +
        (mfderiv CI CI Φ p ((v, a) : E2 × ℝ)).2 * (mfderiv CI CI Φ p ((w, c) : E2 × ℝ)).2 =
      lam * (gS).inner p.1 v w + a * c := by
  let D : (E2 × ℝ) →L[ℝ] (E2 × ℝ) := mfderiv CI CI Φ p
  have hu1 : (D (0, 1)).1 = 0 := mfderiv_vertical_fst_eq_zero Φ hΦ p
  let k : ℝ := (D (0, 1)).2
  have hsplit : ∀ (x : E2) (b : ℝ), D (x, b) = D (x, 0) + b • D (0, 1) := by
    intro x b
    rw [← D.map_smul, ← D.map_add]
    congr 1
    refine Prod.ext ?_ ?_
    · simp
    · simp
  have hk : k * k = 1 := by
    have h := isometry_components Φ hΦ p (0, 1) (0, 1)
    change (gS).inner (Φ p).1 (D (0, 1)).1 (D (0, 1)).1 + k * k =
      (gS).inner p.1 (0 : E2) (0 : E2) + 1 * 1 at h
    rw [hu1, gS_inner_zero_left, gS_inner_zero_left] at h
    linarith
  have hhor : ∀ x : E2, (D (x, 0)).2 = 0 := by
    intro x
    have h := isometry_components Φ hΦ p (x, 0) (0, 1)
    change (gS).inner (Φ p).1 (D (x, 0)).1 (D (0, 1)).1 + (D (x, 0)).2 * k =
      (gS).inner p.1 x (0 : E2) + 0 * 1 at h
    rw [hu1, gS_inner_zero_right, gS_inner_zero_right, zero_add, zero_mul, add_zero] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact h'
    · rw [h'] at hk
      norm_num at hk
  have hS : ∀ x y : E2,
      (gS).inner (Φ p).1 (D (x, 0)).1 (D (y, 0)).1 = (gS).inner p.1 x y := by
    intro x y
    have h := isometry_components Φ hΦ p (x, 0) (y, 0)
    change (gS).inner (Φ p).1 (D (x, 0)).1 (D (y, 0)).1 + (D (x, 0)).2 * (D (y, 0)).2 =
      (gS).inner p.1 x y + 0 * 0 at h
    rw [hhor x, hhor y] at h
    linarith
  change lam * (gS).inner (Φ p).1 (D (v, a)).1 (D (w, c)).1 + (D (v, a)).2 * (D (w, c)).2 = _
  rw [hsplit v a, hsplit w c]
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, hu1, smul_zero,
    add_zero, smul_eq_mul]
  rw [hS v w, hhor v, hhor w]
  change lam * (gS).inner p.1 v w + (0 + a * k) * (0 + c * k) = _
  linear_combination (a * c) * hk

include hΦ in
theorem exists_cylinderIsometry_of_isometry :
    ∃ γ : CylinderIsometry, ∀ p : SpatialNeckCylinder, Φ p = cylinderAct γ p := by
  obtain ⟨e, ε, c, hε, hform⟩ := cylinderDeck_exists_orthogonal_product Φ
    (T := 1) (t₀ := 1 / 2) (t₁ := 0) (by norm_num)
    (fun t _ p v w a c => isometry_scaled Φ hΦ p _ v w a c)
  have hε' : (ε - 1) * (ε + 1) = 0 := by linear_combination hε
  rcases mul_eq_zero.mp hε' with h1 | h1
  · refine ⟨(e, AffineIsometryEquiv.vaddConst ℝ c), fun p => ?_⟩
    have hp := hform p.1 p.2
    refine Prod.ext (Subtype.ext ?_) ?_
    · rw [hp]
      rfl
    · rw [hp]
      change ε * p.2 + c = p.2 + c
      rw [show ε = 1 by linarith, one_mul]
  · refine ⟨(e, AffineIsometryEquiv.pointReflection ℝ (c / 2)), fun p => ?_⟩
    have hp := hform p.1 p.2
    refine Prod.ext (Subtype.ext ?_) ?_
    · rw [hp]
      rfl
    · rw [hp]
      change ε * p.2 + c = AffineIsometryEquiv.pointReflection ℝ (c / 2) p.2
      rw [AffineIsometryEquiv.pointReflection_apply, show ε = -1 by linarith]
      simp only [vsub_eq_sub, vadd_eq_add]
      ring

end GC.Geometry.SphericalProduct
