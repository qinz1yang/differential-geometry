import DifferentialGeometry.Topology.Diffeomorph.Product
import DifferentialGeometry.Geometry.Curvature.Product
import DifferentialGeometry.Geometry.Curvature.DimensionTwo.RicciScalar
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciNaturalityCross
import DifferentialGeometry.Geometry.Metric.Pullback.Product
import DifferentialGeometry.Geometry.Metric.Pullback.Euclidean

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

set_option backward.isDefEq.respectTransparency false in
private theorem ricciTensor_prod_real_self_eq_zero_iff
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 2)
    (x : M × ℝ) (hscalar : metricScalarAt g x.1 ≠ 0)
    (v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) x) :
    ricciTensor (g.prod (euclideanMetric (E := ℝ))) x v v = 0 ↔ v.1 = 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  rw [ricciTensor_productMetric]
  have hflat : ricciTensor (euclideanMetric (E := ℝ)) x.2 v.2 v.2 = 0 := by
    rw [ricciTensor_apply]
    have hz : ricciEndo (euclideanMetric (E := ℝ)) x.2 v.2 v.2 = 0 := by
      apply LinearMap.ext
      intro w
      change riemannOp (Connection.LeviCivita (euclideanMetric (E := ℝ))) x.2 w v.2 v.2 = 0
      exact riemannOp_eq_zero_of_finrank_le_one
        (I := 𝓘(ℝ, ℝ)) (F := ℝ) (Connection.LeviCivita (euclideanMetric (E := ℝ)))
        (by simp) x.2 w v.2 v.2
    rw [hz, map_zero]
  rw [hflat, add_zero,
    ricciTensor_eq_half_metricScalarAt_mul_inner_of_finrank_eq_two g hdim]
  rw [mul_eq_zero, or_iff_right (div_ne_zero hscalar (by norm_num))]
  constructor
  · intro hz
    by_contra hn
    exact (ne_of_gt (g.pos x.1 v.1 hn)) hz
  · intro hz
    rw [hz]
    simp

private theorem mfderiv_prod_real_vertical_fst_eq_zero
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 2)
    (Φ : (M × ℝ) ≃ₘ⟮I.prod 𝓘(ℝ, ℝ), I.prod 𝓘(ℝ, ℝ)⟯ (M × ℝ))
    (hmetric : Diffeomorph.pullbackMetricCross (g.prod (euclideanMetric (E := ℝ))) Φ =
      g.prod (euclideanMetric (E := ℝ)))
    (x : M × ℝ) (hscalar : metricScalarAt g (Φ x).1 ≠ 0) (r : ℝ) :
    (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) Φ x
      (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) x from (0, r))).1 = 0 := by
  apply (ricciTensor_prod_real_self_eq_zero_iff g hdim (Φ x) hscalar _).mp
  let vv : TangentSpace (I.prod 𝓘(ℝ, ℝ)) x := (0, r)
  have hric := ricciTensor_pullbackCross
    (I := I.prod 𝓘(ℝ, ℝ)) (J := I.prod 𝓘(ℝ, ℝ))
    (g.prod (euclideanMetric (E := ℝ))) Φ x vv vv
  rw [hmetric] at hric
  have hzero := ricciTensor_productReal_vertical_eq_zero g x r vv
  rw [hzero] at hric
  exact hric.symm

omit [I.Boundaryless] in
set_option backward.isDefEq.respectTransparency false in
private theorem prod_real_inner_coordinates
    (g : SmoothRiemannianMetric I M) (x : M × ℝ)
    (v w : TangentSpace (I.prod 𝓘(ℝ, ℝ)) x) :
    (g.prod (euclideanMetric (E := ℝ))).inner x v w =
      g.inner x.1 v.1 w.1 + v.2 * w.2 := by
  rw [SmoothRiemannianMetric.prod_inner]
  change g.inner x.1 v.1 w.1 + inner ℝ v.2 w.2 = _
  change g.inner x.1 v.1 w.1 + w.2 * v.2 = _
  rw [mul_comm w.2 v.2]

set_option backward.isDefEq.respectTransparency false in
private theorem mfderiv_prod_real_vertical_unit_snd_sq
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 2)
    (Φ : (M × ℝ) ≃ₘ⟮I.prod 𝓘(ℝ, ℝ), I.prod 𝓘(ℝ, ℝ)⟯ (M × ℝ))
    (hmetric : Diffeomorph.pullbackMetricCross (g.prod (euclideanMetric (E := ℝ))) Φ =
      g.prod (euclideanMetric (E := ℝ)))
    (x : M × ℝ) (hscalar : metricScalarAt g (Φ x).1 ≠ 0) :
    ((mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) Φ x
      (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) x from (0, 1))).2) ^ 2 = 1 := by
  let v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) x := (0, 1)
  have h := congrArg (fun q : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ) =>
    q.inner x v v) hmetric
  rw [Diffeomorph.pullbackMetricCross_inner, prod_real_inner_coordinates,
    prod_real_inner_coordinates] at h
  rw [mfderiv_prod_real_vertical_fst_eq_zero g hdim Φ hmetric x hscalar 1] at h
  simpa [v, pow_two] using h

set_option backward.isDefEq.respectTransparency false in
private theorem mfderiv_prod_real_horizontal_snd_eq_zero
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 2)
    (Φ : (M × ℝ) ≃ₘ⟮I.prod 𝓘(ℝ, ℝ), I.prod 𝓘(ℝ, ℝ)⟯ (M × ℝ))
    (hmetric : Diffeomorph.pullbackMetricCross (g.prod (euclideanMetric (E := ℝ))) Φ =
      g.prod (euclideanMetric (E := ℝ)))
    (x : M × ℝ) (hscalar : metricScalarAt g (Φ x).1 ≠ 0)
    (u : TangentSpace I x.1) :
    (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) Φ x
      (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) x from (u, 0))).2 = 0 := by
  let v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) x := (u, 0)
  let w : TangentSpace (I.prod 𝓘(ℝ, ℝ)) x := (0, 1)
  have h := congrArg (fun q : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ) =>
    q.inner x v w) hmetric
  rw [Diffeomorph.pullbackMetricCross_inner, prod_real_inner_coordinates,
    prod_real_inner_coordinates] at h
  rw [mfderiv_prod_real_vertical_fst_eq_zero g hdim Φ hmetric x hscalar 1] at h
  have heq : (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) Φ x v).2 *
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) Φ x w).2 = 0 := by
    simpa [v, w] using h
  apply (mul_eq_zero.mp heq).resolve_right
  intro hz
  have hsq := mfderiv_prod_real_vertical_unit_snd_sq g hdim Φ hmetric x hscalar
  rw [hz] at hsq
  norm_num at hsq


set_option backward.isDefEq.respectTransparency false in
theorem exists_prod_isometries_of_scalar_ne_zero [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 2)
    (hscalar : ∀ x, metricScalarAt g x ≠ 0)
    (Φ : (M × ℝ) ≃ₘ⟮I.prod 𝓘(ℝ, ℝ), I.prod 𝓘(ℝ, ℝ)⟯ (M × ℝ))
    (hmetric : Diffeomorph.pullbackMetricCross (g.prod (euclideanMetric (E := ℝ))) Φ =
      g.prod (euclideanMetric (E := ℝ))) :
    ∃ (φ : M ≃ₘ⟮I, I⟯ M) (ψ : ℝ ≃ₘ[ℝ] ℝ),
      Φ = φ.prodCongr ψ ∧ Diffeomorph.pullbackMetric g φ = g ∧
      Diffeomorph.pullbackMetric (euclideanMetric (E := ℝ)) ψ = euclideanMetric := by
  obtain ⟨y₀⟩ := (inferInstance : Nonempty M)
  have hfst := fun x r => mfderiv_prod_real_vertical_fst_eq_zero g hdim Φ hmetric x
    (hscalar (Φ x).1) r
  have hsnd := fun x v => mfderiv_prod_real_horizontal_snd_eq_zero g hdim Φ hmetric x
    (hscalar (Φ x).1) v
  obtain ⟨φ, ψ, hsplit⟩ := DifferentialGeometry.exists_prod_diffeomorph_of_coordinate_split Φ y₀
    (fun y r => DifferentialGeometry.product_eq_of_mfderiv_off_diagonal_zero Φ hfst hsnd y y₀ r)
  have hΦ : Φ = φ.prodCongr ψ := by
    apply _root_.Diffeomorph.ext
    intro x
    exact hsplit x.1 x.2
  rw [hΦ, Diffeomorph.pullbackMetricCross_eq_pullbackMetric,
    Diffeomorph.pullbackMetric_prodCongr] at hmetric
  refine ⟨φ, ψ, hΦ, ?_, ?_⟩
  · apply SmoothRiemannianMetric.ext_inner
    intro y v w
    have h := congrArg (fun q : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ) =>
      q.inner (y, 0)
        (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (y, 0) from (v, 0))
        (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (y, 0) from (w, 0))) hmetric
    rw [SmoothRiemannianMetric.prod_inner, SmoothRiemannianMetric.prod_inner] at h
    change (Diffeomorph.pullbackMetric g φ).inner y v w +
      (Diffeomorph.pullbackMetric (euclideanMetric (E := ℝ)) ψ).inner 0 0 0 =
        g.inner y v w + (euclideanMetric (E := ℝ)).inner 0 0 0 at h
    simpa only [map_zero, zero_apply, add_zero] using h
  · apply SmoothRiemannianMetric.ext_inner
    intro r v w
    have h := congrArg (fun q : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ) =>
      q.inner (y₀, r)
        (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (y₀, r) from (0, v))
        (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (y₀, r) from (0, w))) hmetric
    rw [SmoothRiemannianMetric.prod_inner, SmoothRiemannianMetric.prod_inner] at h
    change (Diffeomorph.pullbackMetric g φ).inner y₀ 0 0 +
      (Diffeomorph.pullbackMetric (euclideanMetric (E := ℝ)) ψ).inner r v w =
        g.inner y₀ 0 0 + (euclideanMetric (E := ℝ)).inner r v w at h
    simpa only [map_zero, zero_apply, zero_add] using h

theorem exists_prod_affine_isometry_of_scalar_ne_zero [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 2)
    (hscalar : ∀ x, metricScalarAt g x ≠ 0)
    (Φ : (M × ℝ) ≃ₘ⟮I.prod 𝓘(ℝ, ℝ), I.prod 𝓘(ℝ, ℝ)⟯ (M × ℝ))
    (hmetric : Diffeomorph.pullbackMetricCross (g.prod (euclideanMetric (E := ℝ))) Φ =
      g.prod (euclideanMetric (E := ℝ))) :
    ∃ (φ : M ≃ₘ⟮I, I⟯ M) (ε c : ℝ),
      (ε = 1 ∨ ε = -1) ∧ Diffeomorph.pullbackMetric g φ = g ∧
        ∀ y r, Φ (y, r) = (φ y, ε * r + c) := by
  obtain ⟨φ, ψ, hΦ, hφ, hψ⟩ := exists_prod_isometries_of_scalar_ne_zero g hdim hscalar Φ hmetric
  obtain ⟨ε, hε, haff⟩ := Diffeomorph.real_affine_of_pullbackMetric_eq_euclidean ψ hψ
  refine ⟨φ, ε, ψ 0, hε, hφ, ?_⟩
  intro y r
  rw [hΦ]
  change (φ y, ψ r) = (φ y, ε * r + ψ 0)
  rw [haff]
end DifferentialGeometry.Geometry.Curvature
