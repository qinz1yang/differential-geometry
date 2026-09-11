import DifferentialGeometry.Geometry.Comparison.Busemann.Ray.CorayGradient
import DifferentialGeometry.Geometry.Comparison.Busemann.Support.LineDistanceSupport

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
  obtain ⟨rho, hrho, hcontact, hbound, hgrad⟩ :=
    smooth_distance_upper_support_of_minimizing_exp (I := I) g hEnorm q v hv
      (by simpa only [riemannian_toReal_eq_dist (I := I)] using hmin)
  have heq := gradientFun_eq_of_differentiable_lower_support (I := I) g
    (hrho.mdifferentiableAt (by simp)) hd
    (hmin.symm.trans hcontact.symm)
    (by simpa only [riemannian_toReal_eq_dist (I := I)] using hbound)
  exact heq.symm.trans hgrad

theorem gradient_dist_normSq_eq_one
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (q x : M) (hqx : q ≠ x)
    (hd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => dist q y) x) :
    g.inner x (gradientFun (I := I) g (fun y => dist q y) x)
      (gradientFun (I := I) g (fun y => dist q y) x) = 1 := by
  have hfin : riemannianEDist I q x ≠ ⊤ := by
    rw [← IsRiemannianManifold.out (I := I)]
    exact edist_ne_top q x
  obtain ⟨v, hexp, hlen⟩ :=
    hopf_rinow_expMapIntrinsic_surjective_minimizing_of_ne_top (I := I) g hEnorm q x hfin
  rw [riemannian_toReal_eq_dist (I := I)] at hlen
  have hv : 0 < g.inner q v v := Real.sqrt_pos.mp (hlen.symm ▸ dist_pos.mpr hqx)
  have hend : intrinsicGeodesic (I := I) g hEnorm q v 1 = x := hexp
  have hmin : Real.sqrt (g.inner q v v) =
      dist q (intrinsicGeodesic (I := I) g hEnorm q v 1) := by
    rw [hend]
    exact hlen
  rw [← hend] at hd ⊢
  rw [gradient_dist_of_minimizing_exp (I := I) g hEnorm q v hv hmin hd,
    gInner_smul_self (I := I) g]
  have hspeed : g.inner (intrinsicGeodesic (I := I) g hEnorm q v 1)
      (curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm q v) 1)
      (curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm q v) 1) =
        g.inner q v v := intrinsicGeodesic_speedSq_eq (I := I) g hEnorm q v 1
  rw [hspeed]
  simp only [inv_pow, Real.sq_sqrt hv.le]
  exact inv_mul_cancel₀ hv.ne'

theorem gradient_const_sub_dist_normSq_eq_one
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (a : ℝ) (q x : M) (hxq : x ≠ q)
    (hd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => dist y q) x) :
    g.inner x (gradientFun (I := I) g (fun y => a - dist y q) x)
      (gradientFun (I := I) g (fun y => a - dist y q) x) = 1 := by
  rw [gradientFun_sub (I := I) g mdifferentiableAt_const hd, gradientFun_const, zero_sub]
  simp only [map_neg, neg_apply, neg_neg]
  have h := gradient_dist_normSq_eq_one (I := I) g hEnorm q x hxq.symm
    (by simpa only [dist_comm] using hd)
  simpa only [dist_comm] using h

theorem exists_open_lineDistanceSupport_eikonal
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (intrinsicGeodesic (I := I) g hEnorm p u))
    (s R : ℝ) (hR : s < R) :
    let eta := intrinsicGeodesic (I := I) g hEnorm p u
    ∃ U : Set M, IsOpen U ∧ eta s ∈ U ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (lineDistanceSupport eta R) U ∧
      ∀ x ∈ U, g.inner x (gradientFun (I := I) g (lineDistanceSupport eta R) x)
        (gradientFun (I := I) g (lineDistanceSupport eta R) x) = 1 := by
  let eta := intrinsicGeodesic (I := I) g hEnorm p u
  obtain ⟨U, hU, hx, hf⟩ := exists_open_smooth_lineDistanceSupport (I := I)
    g hEnorm p u hu hiso s R hR
  have hne : eta s ≠ eta R := fun h => (ne_of_lt hR) (hiso.injective h)
  refine ⟨U \ {eta R}, hU.sdiff isClosed_singleton, ⟨hx, hne⟩,
    hf.mono sdiff_subset, ?_⟩
  intro x hx
  have hphi := (hf x hx.1).mdifferentiableWithinAt (by simp)
  have hphiAt : MDifferentiableAt I 𝓘(ℝ, ℝ) (lineDistanceSupport eta R) x :=
    hphi.mdifferentiableAt (hU.mem_nhds hx.1)
  have hd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => dist y (eta R)) x := by
    have ht := (mdifferentiableAt_const (c := R)).sub hphiAt
    change MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => R - lineDistanceSupport eta R y) x at ht
    have heq : (fun y => R - lineDistanceSupport eta R y) = fun y => dist y (eta R) := by
      funext y
      dsimp only [lineDistanceSupport]
      ring
    rwa [heq] at ht
  exact gradient_const_sub_dist_normSq_eq_one (I := I) g hEnorm R (eta R) x hx.2 hd

theorem gradient_lineDistanceSupport_on_line
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (intrinsicGeodesic (I := I) g hEnorm p u))
    (s R : ℝ) (hR : s < R) :
    let eta := intrinsicGeodesic (I := I) g hEnorm p u
    gradientFun (I := I) g (lineDistanceSupport eta R) (eta s) =
      curveVelocity (I := I) eta s := by
  let eta := intrinsicGeodesic (I := I) g hEnorm p u
  have hcont : (fun t => eta (t + s)) = intrinsicGeodesic (I := I) g hEnorm
      (eta s) (curveVelocity (I := I) eta s) := by
    with_unfolding_all exact intrinsicGeodesic_continuation (I := I) g hEnorm p u s
  have hshift : Isometry (fun t : ℝ≥0 => intrinsicGeodesic (I := I) g hEnorm
      (eta s) (curveVelocity (I := I) eta s) (t : ℝ)) := by
    apply Isometry.of_dist_eq
    intro a b
    rw [← hcont]
    change dist (eta ((a : ℝ) + s)) (eta ((b : ℝ) + s)) = dist a b
    rw [hiso.dist_eq, dist_add_right]
    rfl
  have hv : g.inner (eta s) (curveVelocity (I := I) eta s)
      (curveVelocity (I := I) eta s) = 1 :=
    (intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p u s).trans hu
  have hend : intrinsicGeodesic (I := I) g hEnorm (eta s)
      (curveVelocity (I := I) eta s) (R - s) = eta R := by
    have h := congrFun hcont (R - s)
    simpa only [sub_add_cancel] using h.symm
  have h := gradient_intrinsic_ray_distance_support (I := I) g hEnorm (eta s)
    (curveVelocity (I := I) eta s) hv hshift s (R - s) (sub_pos.mpr hR)
  have heq : (fun x => s + (R - s) - dist x (intrinsicGeodesic (I := I) g hEnorm
      (eta s) (curveVelocity (I := I) eta s) (R - s))) = lineDistanceSupport eta R := by
    funext x
    rw [hend]
    dsimp only [lineDistanceSupport]
    ring
  rw [heq] at h
  exact h

end DifferentialGeometry.Geometry.Topology

end
