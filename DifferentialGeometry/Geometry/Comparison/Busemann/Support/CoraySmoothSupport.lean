import DifferentialGeometry.Geometry.Comparison.Busemann.Ray.CalibratedCoray
import DifferentialGeometry.Geometry.Comparison.Busemann.Support.DistanceGerm
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Domain.NoConjugatePoints
import DifferentialGeometry.Geometry.Comparison.Toponogov.PrescribedDistanceSupport

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology NNReal ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Comparison.Toponogov

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

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem riemannian_toReal_eq_dist (p q : M) :
    (riemannianEDist I p q).toReal = dist p q := by
  rw [← IsRiemannianManifold.out (I := I), edist_dist,
    ENNReal.toReal_ofReal dist_nonneg]

private theorem exists_open_smooth_distance_of_unique
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p q : M) (u : TangentSpace I p)
    (hexp : expMapIntrinsic (I := I) g hEnorm p u = q)
    (hupos : 0 < g.inner p u u)
    (hnot : ¬ IsConjVec (I := I) g hEnorm p
      (tangentSpaceModelContinuousLinearEquiv (I := I) p u))
    (huniq : ∀ w : TangentSpace I p,
      expMapIntrinsic (I := I) g hEnorm p w = q →
      Real.sqrt (g.inner p w w) = dist p q → w = u) :
    ∃ U : Set M, IsOpen U ∧ q ∈ U ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y : M => dist p y) U := by
  classical
  have hmin (y : M) : ∃ w : TangentSpace I p,
      expMapIntrinsic (I := I) g hEnorm p w = y ∧
        Real.sqrt (g.inner p w w) = dist p y := by
    have hfin : riemannianEDist I p y ≠ ⊤ := by
      rw [← IsRiemannianManifold.out (I := I)]
      exact edist_ne_top p y
    simpa only [riemannian_toReal_eq_dist (I := I)] using
      minExp_of_ne_top (I := I) g hEnorm p y hfin
  choose v hv hlen using hmin
  have hvlim := tendsto_minimizing_vectors_of_unique (I := I) g hEnorm p q u v hv hlen huniq
  obtain ⟨B, huB⟩ := branch_of_not_conj (I := I) g hEnorm hnot
  have hmem : ∀ᶠ y in 𝓝 q,
      tangentSpaceModelContinuousLinearEquiv (I := I) p (v y) ∈ B.hom.source :=
    ((tangentSpaceModelContinuousLinearEquiv (I := I) p).continuous.tendsto u).comp hvlim
      (B.hom.open_source.mem_nhds huB)
  obtain ⟨U, hU, hqU, hsmooth⟩ := branchRadius_open (I := I) B huB hupos
  rw [hexp] at hqU
  obtain ⟨V, hVsub, hV, hqV⟩ := mem_nhds_iff.mp hmem
  refine ⟨U ∩ V, hU.inter hV, ⟨hqU, hqV⟩, ?_⟩
  apply (hsmooth.mono inter_subset_left).congr
  intro y hy
  have hsource := hVsub hy.2
  calc
    dist p y = Real.sqrt (g.inner p (v y) (v y)) := (hlen y).symm
    _ = branchRadius (I := I) g B (expMapIntrinsic (I := I) g hEnorm p (v y)) :=
      (branchRadius_exp (I := I) B hsource).symm
    _ = branchRadius (I := I) g B y := by rw [hv]

theorem exists_open_smooth_dist_from_intrinsic_ray
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (fun t : ℝ≥0 => intrinsicGeodesic (I := I) g hEnorm p u (t : ℝ)))
    (s : ℝ) (hs : 0 < s) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => dist x (intrinsicGeodesic (I := I) g hEnorm p u s)) U := by
  let gamma : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p u
  have hgamma0 : gamma 0 = p := intrinsicGeodesic_zero (I := I) g hEnorm p u
  have hgammaSmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma :=
    intrinsicGeodesic_contMDiff (I := I) g hEnorm p u
  have hspeed (t : ℝ) : g.inner (gamma t)
      (curveVelocity (I := I) gamma t) (curveVelocity (I := I) gamma t) = 1 :=
    (intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p u t).trans hu
  have hradial (t : ℝ) (ht : 0 ≤ t) : dist p (gamma t) = t := by
    have h := hiso.dist_eq 0 ⟨t, ht⟩
    change dist (gamma 0) (gamma t) = |(0 : ℝ) - t| at h
    simpa only [hgamma0, zero_sub, abs_neg, abs_of_nonneg ht] using h
  let w0 : TangentSpace I (gamma s) := (-s) • curveVelocity (I := I) gamma s
  have hw0sq : g.inner (gamma s) w0 w0 = s ^ 2 := by
    dsimp only [w0]
    rw [gInner_smul_self (I := I) g (gamma s), hspeed, mul_one, neg_sq]
  have hw0pos : 0 < g.inner (gamma s) w0 w0 := hw0sq.symm ▸ sq_pos_of_pos hs
  have hreverse : intrinsicGeodesic (I := I) g hEnorm (gamma s) w0 =
      fun t => gamma ((-s) * t + s) := by
    funext t
    calc
      _ = intrinsicGeodesic (I := I) g hEnorm (gamma s)
          (curveVelocity (I := I) gamma s) ((-s) * t) :=
        intrinsicGeo_smul_apply (I := I) g hEnorm (gamma s)
          (curveVelocity (I := I) gamma s) (-s) t
      _ = _ := (congrFun (intrinsicGeodesic_continuation (I := I) g hEnorm p u s)
        ((-s) * t)).symm
  have hrevExp : expMapIntrinsic (I := I) g hEnorm (gamma s) w0 = p := by
    rw [expMapIntrinsic_def, hreverse]
    change gamma ((-s) * 1 + s) = p
    have ht : (-s) * 1 + s = 0 := by ring
    rw [ht, hgamma0]
  have hlong : (2 * s) • u ∈ SegmentDom (I := I) g hEnorm p := by
    rw [mem_segmentDom, sqrt_gInner_smul_self (I := I) g p (by positivity),
      hu, Real.sqrt_one, mul_one, riemannian_toReal_eq_dist (I := I),
      expMapIntrinsic_def, intrinsicGeodesic_smul, hradial (2 * s) (by positivity)]
  have hlong_ne : (2 * s) • u ≠ 0 := by
    apply smul_ne_zero (by positivity : 2 * s ≠ 0)
    intro hz
    rw [hz, map_zero] at hu
    norm_num at hu
  have hnoForward : ¬ IsConjVec (I := I) g hEnorm p ((s • u : TangentSpace I p) : E) := by
    have h := segmentDom_no_conj (I := I) g hEnorm hlong hlong_ne
      (1 / 2) (by norm_num)
    have hhalf : (1 / 2 : ℝ) • ((2 * s) • u) = s • u := by
      rw [smul_smul]
      congr 1
      ring
    rw [hhalf] at h
    exact h
  let short : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p (s • u)
  have hshort : short = fun t => gamma (s * t + 0) := by
    funext t
    simpa only [add_zero] using intrinsicGeo_smul_apply (I := I) g hEnorm p u s t
  have hshort1 : short 1 = gamma s := by
    rw [hshort]
    simp only [mul_one, add_zero]
  have hshortVel : (curveVelocity (I := I) short 1 : E) =
      s • (curveVelocity (I := I) gamma s : E) := by
    have h := curveVelocity_affine (I := I) gamma s 0 1
      (hgammaSmooth.contMDiffAt.mdifferentiableAt (by simp))
    have ht : s * 1 + 0 = s := by ring
    rw [ht] at h
    change (curveVelocity (I := I) (fun t => gamma (s * t + 0)) 1 : E) =
      s • (curveVelocity (I := I) gamma s : E) at h
    rw [hshort]
    exact h
  have hnoReverse : ¬ IsConjVec (I := I) g hEnorm (gamma s)
      (tangentSpaceModelContinuousLinearEquiv (I := I) (gamma s) w0) := by
    have h := (conjVec_reverse (I := I) g hEnorm p (s • u)).not.mp hnoForward
    change ¬ IsConjVec (I := I) g hEnorm (short 1)
      (-(curveVelocity (I := I) short 1) : E) at h
    have hvec : (-(curveVelocity (I := I) short 1) : E) = (w0 : E) := by
      change -(curveVelocity (I := I) short 1 : E) =
        (-s) • (curveVelocity (I := I) gamma s : E)
      rw [hshortVel, neg_smul]
      with_unfolding_all rfl
    rw [hvec] at h
    rw [hshort1] at h
    exact h
  have huniq (w : TangentSpace I (gamma s))
      (hwExp : expMapIntrinsic (I := I) g hEnorm (gamma s) w = p)
      (hwlen : Real.sqrt (g.inner (gamma s) w w) = dist (gamma s) p) : w = w0 := by
    rw [dist_comm, hradial s hs.le] at hwlen
    let z : TangentSpace I (gamma s) := s⁻¹ • w
    have hwSq : g.inner (gamma s) w w = s ^ 2 := by
      rw [← Real.sq_sqrt (gInner_self_nonneg (I := I) g (gamma s) w), hwlen]
    have hzUnit : g.inner (gamma s) z z = 1 := by
      dsimp only [z]
      rw [gInner_smul_self (I := I) g (gamma s), hwSq, ← mul_pow,
        inv_mul_cancel₀ hs.ne', one_pow]
    have hsz : s • z = w := by
      dsimp only [z]
      rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
    let delta : ℝ → M := intrinsicGeodesic (I := I) g hEnorm (gamma s) z
    have hdelta0 : delta 0 = gamma s := intrinsicGeodesic_zero (I := I) g hEnorm (gamma s) z
    have hdeltaEnd : delta s = p := by
      calc
        _ = expMapIntrinsic (I := I) g hEnorm (gamma s) (s • z) := by
          rw [expMapIntrinsic_def, intrinsicGeodesic_smul]
        _ = p := by rw [hsz, hwExp]
    let eta : ℝ → M := fun t => gamma ((-1) * t + 2 * s)
    have hetaGeo : IsGeodesicOn (I := I) g eta (Icc 0 s) := by
      have h := isGeodesicOn_comp_affine (c := -1) (d := 2 * s)
        ((intrinsicGeodesic_isGeodesic (I := I) g hEnorm p u).isGeodesicOn univ)
      exact h.mono (fun _ _ => mem_univ _)
    have hetaSmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ eta :=
      hgammaSmooth.comp ((contMDiff_const.mul contMDiff_id).add contMDiff_const)
    have hetaVel (t : ℝ) : (curveVelocity (I := I) eta t : E) =
        (-1 : ℝ) • (curveVelocity (I := I) gamma ((-1) * t + 2 * s) : E) :=
      curveVelocity_affine (I := I) gamma (-1) (2 * s) t
        (hgammaSmooth.contMDiffAt.mdifferentiableAt (by simp))
    have hetaUnit (t : ℝ) : g.inner (eta t)
        (curveVelocity (I := I) eta t) (curveVelocity (I := I) eta t) = 1 := by
      change g.inner (gamma ((-1) * t + 2 * s))
        (curveVelocity (I := I) eta t) (curveVelocity (I := I) eta t) = 1
      rw [hetaVel, gInner_smul_self (I := I) g, hspeed]
      norm_num
    have heta0 : eta 0 = gamma (2 * s) := by simp only [eta, mul_zero, zero_add]
    have hetaS : eta s = gamma s := by
      dsimp only [eta]
      congr 1
      ring
    have hmin : riemannianEDist I (eta 0) (delta s) = ENNReal.ofReal (s + s) := by
      rw [heta0, hdeltaEnd, ← IsRiemannianManifold.out (I := I), edist_dist,
        dist_comm, hradial (2 * s) (by positivity)]
      congr 1
      ring
    have hmatch := broken_minimizer_velocity_match (I := I) g hEnorm hs hs hetaGeo
      ((intrinsicGeodesic_isGeodesic (I := I) g hEnorm (gamma s) z).isGeodesicOn (Icc 0 s))
      hetaSmooth (intrinsicGeodesic_contMDiff (I := I) g hEnorm (gamma s) z)
      (fun t _ => hetaUnit t)
      (fun t _ => (intrinsicGeodesic_speedSq_eq (I := I) g hEnorm (gamma s) z t).trans hzUnit)
      (hetaS.trans hdelta0.symm) hmin
    have hdeltaVel : (curveVelocity (I := I) delta 0 : E) = (z : E) :=
      intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm (gamma s) z
    change (curveVelocity (I := I) eta s : E) = (curveVelocity (I := I) delta 0 : E) at hmatch
    rw [hetaVel, hdeltaVel] at hmatch
    have ht : (-1 : ℝ) * s + 2 * s = s := by ring
    rw [ht] at hmatch
    have hmul := congrArg (fun a : E => s • a) hmatch
    change s • ((-1 : ℝ) • (curveVelocity (I := I) gamma s : E)) = (s • z : E) at hmul
    rw [hsz, smul_smul, mul_neg_one] at hmul
    exact hmul.symm
  have hdistSmooth := exists_open_smooth_distance_of_unique (I := I)
    g hEnorm (gamma s) p w0 hrevExp hw0pos hnoReverse huniq
  simpa only [dist_comm] using hdistSmooth

theorem contMDiffAt_dist_from_intrinsic_ray
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (fun t : ℝ≥0 => intrinsicGeodesic (I := I) g hEnorm p u (t : ℝ)))
    (s : ℝ) (hs : 0 < s) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => dist x (intrinsicGeodesic (I := I) g hEnorm p u s)) p := by
  obtain ⟨U, hU, hp, hf⟩ := exists_open_smooth_dist_from_intrinsic_ray
    (I := I) g hEnorm p u hu hiso s hs
  exact (hf p hp).contMDiffAt (hU.mem_nhds hp)

theorem exists_smooth_intrinsic_coray_support
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (c : ℝ≥0 → M) (hc : Isometry c) (p : M) :
    ∃ u : TangentSpace I p, g.inner p u u = 1 ∧
      Isometry (fun s : ℝ≥0 => intrinsicGeodesic (I := I) g hEnorm p u (s : ℝ)) ∧
      (∀ s : ℝ, 0 ≤ s → busemann c (intrinsicGeodesic (I := I) g hEnorm p u s) =
        busemann c p + s) ∧
      ∀ s : ℝ, 0 < s →
        ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x : M => busemann c p + s -
          dist x (intrinsicGeodesic (I := I) g hEnorm p u s)) U ∧
        (∀ x : M, busemann c p + s -
          dist x (intrinsicGeodesic (I := I) g hEnorm p u s) ≤ busemann c x) ∧
        busemann c p + s - dist p (intrinsicGeodesic (I := I) g hEnorm p u s) =
          busemann c p := by
  obtain ⟨u, hu, hiso, hcal⟩ := exists_calibrated_intrinsic_ray (I := I) g hEnorm c hc p
  refine ⟨u, hu, hiso, hcal, fun s hs => ?_⟩
  obtain ⟨U, hU, hp, hd⟩ := exists_open_smooth_dist_from_intrinsic_ray
    (I := I) g hEnorm p u hu hiso s hs
  refine ⟨U, hU, hp, contMDiffOn_const.sub hd, fun x => ?_, ?_⟩
  · have h := (lipschitzWith_busemann hc).dist_le_mul
      (intrinsicGeodesic (I := I) g hEnorm p u s) x
    rw [NNReal.coe_one, one_mul, Real.dist_eq, hcal s hs.le, dist_comm] at h
    have hle := (abs_le.mp h).2
    linarith
  · have h := hiso.dist_eq 0 ⟨s, hs.le⟩
    change dist (intrinsicGeodesic (I := I) g hEnorm p u 0)
      (intrinsicGeodesic (I := I) g hEnorm p u s) = |(0 : ℝ) - s| at h
    rw [intrinsicGeodesic_zero (I := I) g hEnorm p u,
      zero_sub, abs_neg, abs_of_nonneg hs.le] at h
    rw [h]
    ring

end DifferentialGeometry.Geometry.Topology

end
