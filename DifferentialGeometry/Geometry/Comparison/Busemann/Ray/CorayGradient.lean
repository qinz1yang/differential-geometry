import DifferentialGeometry.Geometry.Comparison.Busemann.Ray.BusemannDifferentiability

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology NNReal ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem riemannian_toReal_eq_dist (p q : M) :
    (riemannianEDist I p q).toReal = dist p q := by
  rw [← IsRiemannianManifold.out (I := I), edist_dist,
    ENNReal.toReal_ofReal dist_nonneg]

private theorem gradient_dist_of_minimizing_exp
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (q : M) (v : TangentSpace I q) (hv : 0 < g.inner q v v)
    (hmin : Real.sqrt (g.inner q v v) =
      dist q (intrinsicGeodesic (I := I) g hEnorm q v 1))
    (hd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => dist q y)
      (intrinsicGeodesic (I := I) g hEnorm q v 1)) :
    gradientFun (I := I) g (fun y => dist q y)
        (intrinsicGeodesic (I := I) g hEnorm q v 1) =
      (Real.sqrt (g.inner q v v))⁻¹ •
        curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm q v) 1 := by
  obtain ⟨ρ, hρ, hcontact, hbound, hgrad⟩ :=
    smooth_distance_upper_support_of_minimizing_exp (I := I) g hEnorm q v hv
      (by simpa only [riemannian_toReal_eq_dist (I := I)] using hmin)
  have heq := gradientFun_eq_of_differentiable_lower_support (I := I) g
    (hρ.mdifferentiableAt (by simp)) hd
    (hmin.symm.trans hcontact.symm)
    (by simpa only [riemannian_toReal_eq_dist (I := I)] using hbound)
  exact heq.symm.trans hgrad

theorem gradient_intrinsic_ray_distance_support
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (fun t : ℝ≥0 => intrinsicGeodesic (I := I) g hEnorm p u (t : ℝ)))
    (a s : ℝ) (hs : 0 < s) :
    gradientFun (I := I) g
      (fun x => a + s - dist x (intrinsicGeodesic (I := I) g hEnorm p u s)) p = u := by
  let gamma : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p u
  have hgamma0 : gamma 0 = p := intrinsicGeodesic_zero (I := I) g hEnorm p u
  have hgammaSmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma :=
    intrinsicGeodesic_contMDiff (I := I) g hEnorm p u
  have hspeed : g.inner (gamma s) (curveVelocity (I := I) gamma s)
      (curveVelocity (I := I) gamma s) = 1 :=
    (intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p u s).trans hu
  have hradial : dist p (gamma s) = s := by
    have h := hiso.dist_eq 0 ⟨s, hs.le⟩
    change dist (gamma 0) (gamma s) = |(0 : ℝ) - s| at h
    simpa only [hgamma0, zero_sub, abs_neg, abs_of_nonneg hs.le] using h
  let v : TangentSpace I (gamma s) := (-s) • curveVelocity (I := I) gamma s
  have hvsq : g.inner (gamma s) v v = s ^ 2 := by
    dsimp only [v]
    rw [gInner_smul_self (I := I) g (gamma s), hspeed, mul_one, neg_sq]
  have hvpos : 0 < g.inner (gamma s) v v := hvsq.symm ▸ sq_pos_of_pos hs
  have hvlen : Real.sqrt (g.inner (gamma s) v v) = s := by
    rw [hvsq, Real.sqrt_sq hs.le]
  let delta : ℝ → M := intrinsicGeodesic (I := I) g hEnorm (gamma s) v
  have hreverse : delta = fun t => gamma ((-s) * t + s) := by
    funext t
    calc
      delta t = intrinsicGeodesic (I := I) g hEnorm (gamma s)
          (curveVelocity (I := I) gamma s) ((-s) * t) :=
        intrinsicGeo_smul_apply (I := I) g hEnorm (gamma s)
          (curveVelocity (I := I) gamma s) (-s) t
      _ = _ := (congrFun (intrinsicGeodesic_continuation (I := I) g hEnorm p u s)
        ((-s) * t)).symm
  have htime : (-s) * 1 + s = 0 := by ring
  have hdelta1 : delta 1 = p := by
    rw [hreverse]
    change gamma ((-s) * 1 + s) = p
    rw [htime, hgamma0]
  have hvel : (curveVelocity (I := I) delta 1 : E) = (-s) • (u : E) := by
    have h := curveVelocity_affine (I := I) gamma (-s) s 1
      (hgammaSmooth.contMDiffAt.mdifferentiableAt (by simp))
    rw [htime] at h
    have hz : (curveVelocity (I := I) gamma 0 : E) = (u : E) :=
      intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm p u
    rw [hz] at h
    rw [hreverse]
    exact h
  have hd := (contMDiffAt_dist_from_intrinsic_ray
    (I := I) g hEnorm p u hu hiso s hs).mdifferentiableAt (by simp)
  have hmin : Real.sqrt (g.inner (gamma s) v v) = dist (gamma s) (delta 1) := by
    rw [hvlen, hdelta1, dist_comm, hradial]
  have hdistSmooth : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => dist (gamma s) y) (delta 1) := by
    simpa only [hdelta1, dist_comm] using hd
  have hgrad := gradient_dist_of_minimizing_exp (I := I) g hEnorm (gamma s) v
    hvpos hmin hdistSmooth
  change (gradientFun (I := I) g (fun y => dist (gamma s) y) (delta 1) : E) =
    (Real.sqrt (g.inner (gamma s) v v))⁻¹ • (curveVelocity (I := I) delta 1 : E) at hgrad
  rw [hvlen, hvel, hdelta1, smul_smul, mul_neg, inv_mul_cancel₀ hs.ne', neg_one_smul] at hgrad
  have hdistGrad : gradientFun (I := I) g (fun y => dist y (gamma s)) p = -u := by
    simpa only [dist_comm] using hgrad
  rw [gradientFun_sub (I := I) g mdifferentiableAt_const hd,
    gradientFun_const, hdistGrad, zero_sub, neg_neg]

theorem gradient_busemann_eq_of_calibrated_intrinsic_ray
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (c : ℝ≥0 → M) (hc : Isometry c) (p : M)
    (hb : MDifferentiableAt I 𝓘(ℝ, ℝ) (busemann c) p)
    (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (fun t : ℝ≥0 => intrinsicGeodesic (I := I) g hEnorm p u (t : ℝ)))
    (hcal : ∀ t : ℝ, 0 ≤ t → busemann c (intrinsicGeodesic (I := I) g hEnorm p u t) =
      busemann c p + t) :
    gradientFun (I := I) g (busemann c) p = u := by
  let q := intrinsicGeodesic (I := I) g hEnorm p u 1
  let φ : M → ℝ := fun x => busemann c p + 1 - dist x q
  have hdist : dist p q = 1 := by
    have h := hiso.dist_eq 0 1
    change dist (intrinsicGeodesic (I := I) g hEnorm p u 0)
      (intrinsicGeodesic (I := I) g hEnorm p u 1) = |(0 : ℝ) - 1| at h
    simpa only [NNReal.coe_zero, NNReal.coe_one, intrinsicGeodesic_zero,
      Real.dist_eq, zero_sub, abs_neg, abs_one] using h
  have hφ : MDifferentiableAt I 𝓘(ℝ, ℝ) φ p :=
    mdifferentiableAt_const.sub ((contMDiffAt_dist_from_intrinsic_ray
      (I := I) g hEnorm p u hu hiso 1 zero_lt_one).mdifferentiableAt (by simp))
  have hcontact : φ p = busemann c p := by
    dsimp only [φ]
    rw [hdist]
    ring
  have hbelow (y : M) : φ y ≤ busemann c y := by
    have h := (lipschitzWith_busemann hc).dist_le_mul q y
    rw [NNReal.coe_one, one_mul, Real.dist_eq, hcal 1 zero_le_one, dist_comm] at h
    have hle := (abs_le.mp h).2
    dsimp only [φ]
    linarith
  calc
    gradientFun (I := I) g (busemann c) p = gradientFun (I := I) g φ p :=
      gradientFun_eq_of_differentiable_lower_support (I := I) g hb hφ hcontact
        (Eventually.of_forall hbelow)
    _ = u := gradient_intrinsic_ray_distance_support (I := I) g hEnorm p u hu hiso
      (busemann c p) 1 zero_lt_one

variable [PreconnectedSpace M]

theorem opposite_busemann_gradient_unit
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    {γ : ℝ → M} (hγ : Isometry γ) (p : M) :
    g.inner p (gradientFun (I := I) g (busemann (fun t : ℝ≥0 => γ t)) p)
        (gradientFun (I := I) g (busemann (fun t : ℝ≥0 => γ t)) p) = 1 ∧
      g.inner p (gradientFun (I := I) g (busemann (fun t : ℝ≥0 => γ (-(t : ℝ)))) p)
        (gradientFun (I := I) g (busemann (fun t : ℝ≥0 => γ (-(t : ℝ)))) p) = 1 := by
  have hp : Isometry (fun t : ℝ≥0 => γ t) := by
    apply Isometry.of_dist_eq
    intro s t
    exact hγ.dist_eq s t
  obtain ⟨u, hu, hiso, hcal⟩ :=
    exists_calibrated_intrinsic_ray (I := I) g hEnorm (fun t : ℝ≥0 => γ t) hp p
  have hgrad := gradient_busemann_eq_of_calibrated_intrinsic_ray (I := I) g hEnorm
    (fun t : ℝ≥0 => γ t) hp p
    ((opposite_busemann_mdifferentiable (I := I) g hEnorm hRic hγ).1 p) u hu hiso hcal
  refine ⟨by rw [hgrad, hu], ?_⟩
  rw [opposite_busemann_gradient_neg (I := I) g hEnorm hRic hγ p, hgrad]
  simpa only [map_neg, neg_apply, neg_neg] using hu

end DifferentialGeometry.Geometry.Topology

end
