import DifferentialGeometry.Geometry.Comparison.Busemann.Ray.BusemannBasic
import DifferentialGeometry.Geometry.Comparison.Splitting.MetricLineLimit
import DifferentialGeometry.Geometry.Comparison.Toponogov.MinimizingRay

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology NNReal ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
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

theorem lipschitzWith_one_intrinsicGeodesic
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1) :
    LipschitzWith 1 (intrinsicGeodesic (I := I) g hEnorm p u) := by
  have hbound (s t : ℝ) (hst : s ≤ t) :
      dist (intrinsicGeodesic (I := I) g hEnorm p u s)
        (intrinsicGeodesic (I := I) g hEnorm p u t) ≤ t - s := by
    have h := intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm p u hst
    rw [hu, Real.sqrt_one, one_mul] at h
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rwa [ENNReal.toReal_ofReal (sub_nonneg.mpr hst),
      riemannian_toReal_eq_dist (I := I)] at hr
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rcases le_total s t with hst | hts
  · simpa only [NNReal.coe_one, one_mul, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr hst), neg_sub] using hbound s t hst
  · simpa only [NNReal.coe_one, one_mul, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr hts), dist_comm] using hbound t s hts

private theorem unit_minimizing_initial
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p q : M) (hd : 0 < dist p q) :
    ∃ u : TangentSpace I p, g.inner p u u = 1 ∧
      intrinsicGeodesic (I := I) g hEnorm p u (dist p q) = q := by
  have hfin : riemannianEDist I p q ≠ ⊤ := by
    rw [← IsRiemannianManifold.out (I := I)]
    exact edist_ne_top p q
  obtain ⟨v, hv, hlen⟩ := minExp_of_ne_top (I := I) g hEnorm p q hfin
  rw [riemannian_toReal_eq_dist (I := I)] at hlen
  let d : ℝ := dist p q
  let u : TangentSpace I p := d⁻¹ • v
  have hsq : g.inner p v v = d ^ 2 := by
    rw [← Real.sq_sqrt (gInner_self_nonneg (I := I) g p v), hlen]
  have hu : g.inner p u u = 1 := by
    dsimp only [u]
    rw [gInner_smul_self (I := I) g p d⁻¹ v, hsq, ← mul_pow,
      inv_mul_cancel₀ hd.ne', one_pow]
  have hsmul : d • u = v := by
    dsimp only [u]
    rw [smul_smul, mul_inv_cancel₀ hd.ne', one_smul]
  refine ⟨u, hu, ?_⟩
  calc
    _ = expMapIntrinsic (I := I) g hEnorm p (d • u) := by
      rw [expMapIntrinsic_def]
      exact (intrinsicGeodesic_smul (I := I) g hEnorm p u d).symm
    _ = q := by rw [hsmul, hv]

theorem exists_calibrated_intrinsic_ray
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (c : ℝ≥0 → M) (hc : Isometry c) (p : M) :
    ∃ u : TangentSpace I p, g.inner p u u = 1 ∧
      Isometry (fun s : ℝ≥0 => intrinsicGeodesic (I := I) g hEnorm p u (s : ℝ)) ∧
      ∀ s : ℝ, 0 ≤ s → busemann c (intrinsicGeodesic (I := I) g hEnorm p u s) =
        busemann c p + s := by
  classical
  let t : ℕ → ℝ≥0 := fun n =>
    ⟨(n : ℝ) + dist p (c 0) + 1, by positivity⟩
  let d : ℕ → ℝ := fun n => dist p (c (t n))
  have hd_lower (n : ℕ) : (n : ℝ) + 1 ≤ d n := by
    have hrad : dist (c 0) (c (t n)) = (t n : ℝ) := by
      rw [hc.dist_eq]
      simp only [NNReal.dist_eq, NNReal.coe_zero, zero_sub, abs_neg,
        abs_of_nonneg (t n).coe_nonneg]
    have htri := dist_triangle (c 0) p (c (t n))
    rw [hrad, dist_comm (c 0) p] at htri
    change (n : ℝ) + dist p (c 0) + 1 ≤ dist p (c 0) + d n at htri
    linarith
  have hdpos (n : ℕ) : 0 < d n := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith [hd_lower n]
  have hd : Tendsto d atTop atTop := Filter.tendsto_atTop.2 fun B => by
    obtain ⟨N, hN⟩ := exists_nat_gt B
    filter_upwards [eventually_ge_atTop N] with n hn
    have hcast : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
    linarith [hd_lower n]
  have ht : Tendsto t atTop atTop := Filter.tendsto_atTop.2 fun B => by
    obtain ⟨N, hN⟩ := exists_nat_gt (B : ℝ)
    filter_upwards [eventually_ge_atTop N] with n hn
    change (B : ℝ) ≤ (n : ℝ) + dist p (c 0) + 1
    have hcast : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
    linarith [dist_nonneg (x := p) (y := c 0)]
  choose v hunit hend using fun n =>
    unit_minimizing_initial (I := I) g hEnorm p (c (t n)) (hdpos n)
  have hmin (n : ℕ) : (riemannianEDist I p
      (intrinsicGeodesic (I := I) g hEnorm p (v n) (d n))).toReal = d n := by
    rw [hend n, riemannian_toReal_eq_dist (I := I)]
  obtain ⟨u, hu, phi, hphi, hlim, hray⟩ :=
    exists_minimizing_ray_subsequence (I := I) g hEnorm p v d hunit hdpos hmin hd
  let gamma : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p u
  have hgamma0 : gamma 0 = p := intrinsicGeodesic_zero (I := I) g hEnorm p u
  have hgammaLip : LipschitzWith 1 gamma :=
    lipschitzWith_one_intrinsicGeodesic (I := I) g hEnorm p u hu
  have hradial (s : ℝ) (hs : 0 ≤ s) : dist (gamma 0) (gamma s) = s := by
    rw [hgamma0, ← riemannian_toReal_eq_dist (I := I), hray s hs,
      ENNReal.toReal_ofReal hs]
  have hiso : Isometry (fun s : ℝ≥0 => gamma (s : ℝ)) := by
    apply Isometry.of_dist_eq
    intro s r
    have hordered (a b : ℝ≥0) (hab : a ≤ b) :
        dist (gamma (a : ℝ)) (gamma (b : ℝ)) = (b : ℝ) - a :=
      dist_eq_sub_of_lipschitzWith_one_of_endpoints hgammaLip
        (a := 0) a.coe_nonneg hab le_rfl (by simpa only [sub_zero] using hradial b b.coe_nonneg)
    rcases le_total s r with hsr | hrs
    · have hsr' : (s : ℝ) ≤ r := hsr
      rw [hordered s r hsr, NNReal.dist_eq, abs_of_nonpos (sub_nonpos.mpr hsr'), neg_sub]
    · have hrs' : (r : ℝ) ≤ s := hrs
      rw [dist_comm (gamma (s : ℝ)) (gamma (r : ℝ)), hordered r s hrs,
        NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr hrs')]
  refine ⟨u, hu, hiso, fun s hs => ?_⟩
  have hpoint : Tendsto (fun n =>
      intrinsicGeodesic (I := I) g hEnorm p (v (phi n)) s) atTop (𝓝 (gamma s)) := by
    have hcpt := (expMapIntrinsic_continuous (I := I) g hEnorm p).comp
      (continuous_const_smul s : Continuous (fun w : TangentSpace I p => s • w))
    have h := (hcpt.tendsto u).comp hlim
    simpa only [Function.comp_def, expMapIntrinsic_def, intrinsicGeodesic_smul] using h
  have happrox := tendsto_busemannApprox_of_tendsto hc (ht.comp hphi.tendsto_atTop) hpoint
  have hevent : ∀ᶠ n in atTop,
      busemannApprox c (t (phi n))
        (intrinsicGeodesic (I := I) g hEnorm p (v (phi n)) s) =
          busemannApprox c (t (phi n)) p + s := by
    filter_upwards [(hd.comp hphi.tendsto_atTop) (eventually_ge_atTop s)] with n hn
    change s ≤ d (phi n) at hn
    let f : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p (v (phi n))
    have hf0 : f 0 = p := intrinsicGeodesic_zero (I := I) g hEnorm p (v (phi n))
    have hfend : f (d (phi n)) = c (t (phi n)) := hend (phi n)
    have hfLip : LipschitzWith 1 f :=
      lipschitzWith_one_intrinsicGeodesic (I := I) g hEnorm p (v (phi n)) (hunit (phi n))
    have hlength : dist (f 0) (f (d (phi n))) = d (phi n) - 0 := by
      rw [hf0, hfend, sub_zero]
    have htail := dist_eq_sub_of_lipschitzWith_one_of_endpoints hfLip
      hs hn le_rfl hlength
    rw [hfend] at htail
    change dist (f s) (c (t (phi n))) = d (phi n) - s at htail
    change (t (phi n) : ℝ) - dist (f s) (c (t (phi n))) =
      (t (phi n) : ℝ) - d (phi n) + s
    rw [htail]
    ring
  have hright := ((tendsto_busemannApprox hc p).comp (ht.comp hphi.tendsto_atTop)).add_const s
  exact tendsto_nhds_unique happrox (hright.congr' (Filter.EventuallyEq.symm hevent))

theorem exists_intrinsic_coray_distance_support
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (c : ℝ≥0 → M) (hc : Isometry c) (p : M) :
    ∃ u : TangentSpace I p, g.inner p u u = 1 ∧
      Isometry (fun s : ℝ≥0 => intrinsicGeodesic (I := I) g hEnorm p u (s : ℝ)) ∧
      ∀ s : ℝ, 0 ≤ s →
        (∀ x : M, busemann c p + s -
          dist x (intrinsicGeodesic (I := I) g hEnorm p u s) ≤ busemann c x) ∧
        busemann c p + s - dist p (intrinsicGeodesic (I := I) g hEnorm p u s) =
          busemann c p := by
  obtain ⟨u, hu, hiso, hcal⟩ := exists_calibrated_intrinsic_ray (I := I) g hEnorm c hc p
  refine ⟨u, hu, hiso, fun s hs => ⟨fun x => ?_, ?_⟩⟩
  · have h := (lipschitzWith_busemann hc).dist_le_mul
      (intrinsicGeodesic (I := I) g hEnorm p u s) x
    rw [NNReal.coe_one, one_mul, Real.dist_eq, hcal s hs, dist_comm] at h
    have hle := (abs_le.mp h).2
    linarith
  · have h := hiso.dist_eq 0 ⟨s, hs⟩
    change dist (intrinsicGeodesic (I := I) g hEnorm p u 0)
      (intrinsicGeodesic (I := I) g hEnorm p u s) = |(0 : ℝ) - s| at h
    rw [intrinsicGeodesic_zero (I := I) g hEnorm p u,
      zero_sub, abs_neg, abs_of_nonneg hs] at h
    rw [h]
    ring

end DifferentialGeometry.Geometry.Topology

end
