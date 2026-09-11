import DifferentialGeometry.Geometry.Comparison.Soul.SbrDirectional
import DifferentialGeometry.Geometry.Comparison.Soul.SbrDistanceContraction

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem inner_normalized_support_nonneg_of_le_intrinsic_level
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (F : M → ℝ) (p : M) (G : TangentSpace I p)
    (hsupport : ∀ v : TangentSpace I p,
      intrinsicRightDerivative g hEnorm F p v ≤ g.inner p G v)
    (v : TangentSpace I p)
    (hconc : ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm p v t)))
    (t : ℝ) (ht : 0 < t)
    (hlevel : F p ≤ F (intrinsicGeodesic g hEnorm p v t)) :
    0 ≤ g.inner p ((g.inner p G G)⁻¹ • G) v := by
  have hsec := slope_le_intrinsicRightDerivative g hEnorm F p v hconc ht
  have hpos : 0 ≤ (F (intrinsicGeodesic g hEnorm p v t) - F p) / t :=
    div_nonneg (sub_nonneg.mpr hlevel) ht.le
  have hinner : 0 ≤ g.inner p G v := hpos.trans (hsec.trans (hsupport v))
  rw [map_smul, _root_.smul_apply, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr (gInner_self_nonneg g p G)) hinner

theorem antitoneOn_dist_of_normalized_gradient_right_derivatives
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (F : M → ℝ)
    (hconc : ∀ (p : M) (v : TangentSpace I p),
      ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm p v t)))
    (G : (p : M) → TangentSpace I p)
    (hsupport : ∀ (p : M) (v : TangentSpace I p),
      intrinsicRightDerivative g hEnorm F p v ≤ g.inner p (G p) v)
    (xi zeta : ℝ → M) {a b : ℝ}
    (hxi : ContinuousOn xi (Icc a b)) (hzeta : ContinuousOn zeta (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I xi (Ici t) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        ((g.inner (xi t) (G (xi t)) (G (xi t)))⁻¹ • G (xi t))))
    (hY : ∀ t ∈ Ico a b, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I zeta (Ici t) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        ((g.inner (zeta t) (G (zeta t)) (G (zeta t)))⁻¹ • G (zeta t))))
    (hlevel : ∀ t ∈ Ico a b, F (xi t) = F (zeta t)) :
    AntitoneOn (fun t => dist (xi t) (zeta t)) (Icc a b) := by
  apply antitoneOn_dist_of_right_first_variation_nonpos g hEnorm xi zeta hxi hzeta
    (fun t => (1 : ℝ →L[ℝ] ℝ).smulRight
      ((g.inner (xi t) (G (xi t)) (G (xi t)))⁻¹ • G (xi t)))
    (fun t => (1 : ℝ →L[ℝ] ℝ).smulRight
      ((g.inner (zeta t) (G (zeta t)) (G (zeta t)))⁻¹ • G (zeta t))) hX hY
  intro t ht hne u _hu hend
  let ell := dist (xi t) (zeta t)
  let gamma := intrinsicGeodesic g hEnorm (xi t) u
  have hgammaEnd : gamma ell = zeta t := hend
  have hell : 0 < ell := dist_pos.mpr hne
  have hx := inner_normalized_support_nonneg_of_le_intrinsic_level
    g hEnorm F (xi t) (G (xi t)) (hsupport (xi t)) u (hconc (xi t) u)
      ell hell (by rw [hend]; exact (hlevel t ht).le)
  have hback : intrinsicGeodesic g hEnorm (gamma ell)
      (-curveVelocity (I := I) gamma ell) ell = xi t := by
    calc
      _ = intrinsicGeodesic g hEnorm (gamma ell)
          (curveVelocity (I := I) gamma ell) (-ell) := by
        simpa only [neg_one_smul, neg_one_mul] using
          intrinsicGeo_smul_apply g hEnorm (gamma ell)
            (curveVelocity (I := I) gamma ell) (-1) ell
      _ = gamma (-ell + ell) :=
        (congrFun (intrinsicGeodesic_continuation g hEnorm (xi t) u ell) (-ell)).symm
      _ = xi t := by simp only [neg_add_cancel, gamma, intrinsicGeodesic_zero]
  have hy0 := inner_normalized_support_nonneg_of_le_intrinsic_level
    g hEnorm F (gamma ell) (G (gamma ell)) (hsupport (gamma ell))
      (-curveVelocity (I := I) gamma ell)
      (hconc (gamma ell) (-curveVelocity (I := I) gamma ell)) ell hell
      (by rw [hback, hgammaEnd]; exact (hlevel t ht).ge)
  rw [map_neg] at hy0
  have hy (q : M) (h : gamma ell = q) :
      g.inner q ((g.inner q (G q) (G q))⁻¹ • G q)
        (h ▸ curveVelocity (I := I) gamma ell) ≤ 0 := by
    cases h
    exact neg_nonneg.mp hy0
  simp only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul]
  exact add_nonpos (neg_nonpos.mpr hx) (hy (zeta t) hgammaEnd)

theorem antitoneOn_dist_fixed_of_normalized_gradient_right_derivative
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (F : M → ℝ)
    (hconc : ∀ (p : M) (v : TangentSpace I p),
      ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm p v t)))
    (G : (p : M) → TangentSpace I p)
    (hsupport : ∀ (p : M) (v : TangentSpace I p),
      intrinsicRightDerivative g hEnorm F p v ≤ g.inner p (G p) v)
    (xi : ℝ → M) {a b : ℝ} (hxi : ContinuousOn xi (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I xi (Ici t) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        ((g.inner (xi t) (G (xi t)) (G (xi t)))⁻¹ • G (xi t))))
    (q : M) (hlevel : ∀ t ∈ Ico a b, F (xi t) ≤ F q) :
    AntitoneOn (fun t => dist (xi t) q) (Icc a b) := by
  apply antitoneOn_dist_of_right_first_variation_nonpos g hEnorm xi (fun _ => q)
    hxi continuousOn_const
    (fun t => (1 : ℝ →L[ℝ] ℝ).smulRight
      ((g.inner (xi t) (G (xi t)) (G (xi t)))⁻¹ • G (xi t)))
    (fun _ => (0 : ℝ →L[ℝ] TangentSpace I q)) hX
    (fun t _ => hasMFDerivWithinAt_const q (Ici t) t)
  intro t ht hne u _hu hend
  have hx := inner_normalized_support_nonneg_of_le_intrinsic_level
    g hEnorm F (xi t) (G (xi t)) (hsupport (xi t)) u (hconc (xi t) u)
      (dist (xi t) q) (dist_pos.mpr hne) (by rw [hend]; exact hlevel t ht)
  simp only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul,
    map_zero, zero_apply, add_zero]
  exact neg_nonpos.mpr hx

end DifferentialGeometry.Geometry.Topology
