import DifferentialGeometry.Geometry.Comparison.Toponogov.EscapingRadialArms

set_option autoImplicit false
noncomputable section
open Bundle Filter Manifold Set
open scoped Topology Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] [ConnectedSpace M]

theorem intrinsicGeodesic_continues_of_distance_add
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (p q : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hpq : riemannianEDist I p q = ENNReal.ofReal (a + b))
    (hxq : riemannianEDist I (intrinsicGeodesic g hEnorm p u a) q = ENNReal.ofReal b) :
    intrinsicGeodesic g hEnorm p u (a + b) = q := by
  let gamma : ℝ → M := intrinsicGeodesic g hEnorm p u
  have hlen : (riemannianEDist I (gamma a) q).toReal = b := by
    rw [hxq, ENNReal.toReal_ofReal hb.le]
  obtain ⟨v, hv, hvend⟩ := exists_unit_intrinsic_vector_of_pos_distance g hEnorm
    (gamma a) q (by rw [hlen]; exact hb)
  rw [hlen] at hvend
  let sigma : ℝ → M := intrinsicGeodesic g hEnorm (gamma a) v
  have hgamma : Geodesic.IsGeodesic g gamma := intrinsicGeodesic_isGeodesic g hEnorm p u
  have hsigma : Geodesic.IsGeodesic g sigma := intrinsicGeodesic_isGeodesic g hEnorm (gamma a) v
  have hmatch := broken_minimizer_velocity_match g hEnorm ha hb
    (hgamma.isGeodesicOn (Icc 0 a)) (hsigma.isGeodesicOn (Icc 0 b))
    (intrinsicGeodesic_contMDiff g hEnorm p u)
    (intrinsicGeodesic_contMDiff g hEnorm (gamma a) v)
    (fun t _ => (intrinsicGeodesic_speedSq_eq g hEnorm p u t).trans hu)
    (fun t _ => (intrinsicGeodesic_speedSq_eq g hEnorm (gamma a) v t).trans hv)
    (intrinsicGeodesic_zero g hEnorm (gamma a) v).symm
    (by simpa only [gamma, sigma, intrinsicGeodesic_zero, hvend] using hpq)
  have hvelocity : (mfderiv 𝓘(ℝ, ℝ) I gamma a 1 : E) = (v : E) :=
    hmatch.trans (intrinsicGeodesic_mfderiv_zero g hEnorm (gamma a) v)
  calc
    _ = gamma (b + a) := by congr 1; ring
    _ = intrinsicGeodesic g hEnorm (gamma a) (mfderiv 𝓘(ℝ, ℝ) I gamma a 1) b :=
      congrFun (intrinsicGeodesic_continuation g hEnorm p u a) b
    _ = sigma b := by rw [hvelocity]
    _ = q := hvend

omit [ConnectedSpace M] in
theorem unit_intrinsic_vector_eq_of_short_endpoint
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (p : M) {u v : TangentSpace I p} (hu : g.inner p u u = 1) (hv : g.inner p v v = 1)
    {L : ℝ} (hL : 0 < L) (hsmall : L < expDiffeoRadius g hEnorm p)
    (hend : intrinsicGeodesic g hEnorm p u L = intrinsicGeodesic g hEnorm p v L) :
    u = v := by
  have hunorm : Real.sqrt (g.inner p (L • u) (L • u)) = L := by
    rw [sqrt_gInner_smul_self g p hL.le, hu, Real.sqrt_one, mul_one]
  have hvnorm : Real.sqrt (g.inner p (L • v) (L • v)) = L := by
    rw [sqrt_gInner_smul_self g p hL.le, hv, Real.sqrt_one, mul_one]
  have husmall := hunorm.trans_lt hsmall
  have hvsmall := hvnorm.trans_lt hsmall
  have hscaled : L • u = L • v := by
    apply (NormalCoordinates.expMapDiffeo (I := I) g p).toPartialEquiv.injOn
      (expDiffeo_mem_of_lt g hEnorm p husmall) (expDiffeo_mem_of_lt g hEnorm p hvsmall)
    rw [expDiffeo_eq_intr g hEnorm p husmall, expDiffeo_eq_intr g hEnorm p hvsmall,
      expMapIntrinsic_def, expMapIntrinsic_def, intrinsicGeodesic_smul, intrinsicGeodesic_smul]
    exact hend
  have h := congrArg (fun w : TangentSpace I p => L⁻¹ • w) hscaled
  simpa only [smul_smul, inv_mul_cancel₀ hL.ne', one_smul] using h

theorem exists_intrinsicGeodesic_eq_short_metric_segment
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {L : ℝ} (hL : 0 < L) (f : Icc (0 : ℝ) L → M)
    (hsmall : L < expDiffeoRadius g hEnorm (f ⟨0, ⟨le_rfl, hL.le⟩⟩))
    (hdist : ∀ s t, riemannianEDist I (f s) (f t) = ENNReal.ofReal |(s : ℝ) - t|) :
    ∃ u : TangentSpace I (f ⟨0, ⟨le_rfl, hL.le⟩⟩),
      g.inner _ u u = 1 ∧ ∀ s, f s = intrinsicGeodesic g hEnorm _ u s := by
  let z : Icc (0 : ℝ) L := ⟨0, ⟨le_rfl, hL.le⟩⟩
  let o : Icc (0 : ℝ) L := ⟨L, ⟨hL.le, le_rfl⟩⟩
  have hfull : riemannianEDist I (f z) (f o) = ENNReal.ofReal L := by
    simpa only [z, o, zero_sub, abs_neg, abs_of_pos hL] using hdist z o
  obtain ⟨u, hu, huend⟩ := exists_unit_intrinsic_vector_of_pos_distance g hEnorm
    (f z) (f o) (by rw [hfull, ENNReal.toReal_ofReal hL.le]; exact hL)
  rw [hfull, ENNReal.toReal_ofReal hL.le] at huend
  refine ⟨u, hu, ?_⟩
  intro s
  rcases eq_or_lt_of_le s.property.1 with hs0 | hspos
  · have hsz : s = z := Subtype.ext hs0.symm
    subst s
    exact (intrinsicGeodesic_zero g hEnorm (f z) u).symm
  rcases eq_or_lt_of_le s.property.2 with hsL | hslt
  · have hso : s = o := Subtype.ext hsL
    subst s
    exact huend.symm
  have hfirst : riemannianEDist I (f z) (f s) = ENNReal.ofReal (s : ℝ) := by
    simpa only [z, zero_sub, abs_neg, abs_of_pos hspos] using hdist z s
  obtain ⟨v, hv, hvend⟩ := exists_unit_intrinsic_vector_of_pos_distance g hEnorm
    (f z) (f s) (by rw [hfirst, ENNReal.toReal_ofReal hspos.le]; exact hspos)
  rw [hfirst, ENNReal.toReal_ofReal hspos.le] at hvend
  have hremaining : riemannianEDist I (intrinsicGeodesic g hEnorm (f z) v (s : ℝ))
      (f o) = ENNReal.ofReal (L - s) := by
    rw [hvend, hdist]
    congr 1
    change |(s : ℝ) - L| = L - s
    rw [abs_of_nonpos (sub_nonpos.mpr hslt.le)]
    ring
  have hadd : (s : ℝ) + (L - s) = L := by ring
  have hvfull := intrinsicGeodesic_continues_of_distance_add g hEnorm (f z) (f o) v hv
    hspos (sub_pos.mpr hslt) (by rw [hadd]; exact hfull) hremaining
  rw [hadd] at hvfull
  have hvu : v = u := unit_intrinsic_vector_eq_of_short_endpoint g hEnorm (f z) hv hu
    hL hsmall (hvfull.trans huend.symm)
  rw [hvu] at hvend
  exact hvend.symm

theorem exists_intrinsicGeodesic_eq_centered_metric_segment
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {L : ℝ} (hL : 0 < L) (f : Icc (-L) L → M)
    (hsmall : L < expDiffeoRadius g hEnorm (f ⟨0, ⟨by linarith, hL.le⟩⟩))
    (hdist : ∀ s t, riemannianEDist I (f s) (f t) = ENNReal.ofReal |(s : ℝ) - t|) :
    ∃ u : TangentSpace I (f ⟨0, ⟨by linarith, hL.le⟩⟩),
      g.inner _ u u = 1 ∧ ∀ s, f s = intrinsicGeodesic g hEnorm _ u s := by
  let z : Icc (-L) L := ⟨0, ⟨by linarith, hL.le⟩⟩
  let left : Icc (-L) L := ⟨-L, ⟨le_rfl, by linarith⟩⟩
  let right : Icc (-L) L := ⟨L, ⟨by linarith, le_rfl⟩⟩
  let plus (s : Icc (0 : ℝ) L) : Icc (-L) L :=
    ⟨s, ⟨(by linarith : -L ≤ (0 : ℝ)).trans s.property.1, s.property.2⟩⟩
  let minus (s : Icc (0 : ℝ) L) : Icc (-L) L :=
    ⟨-s, ⟨neg_le_neg s.property.2, by linarith [s.property.1]⟩⟩
  have hmz : minus ⟨0, ⟨le_rfl, hL.le⟩⟩ = z := by
    apply Subtype.ext
    simp [minus, z]
  obtain ⟨u, hu, huall⟩ := exists_intrinsicGeodesic_eq_short_metric_segment g hEnorm hL
    (fun s => f (plus s)) hsmall (fun s t => hdist (plus s) (plus t))
  obtain ⟨v, hv, hvall⟩ := exists_intrinsicGeodesic_eq_short_metric_segment g hEnorm hL
    (fun s => f (minus s)) (by rw [hmz]; exact hsmall) (by
      intro s t
      have h := hdist (minus s) (minus t)
      change riemannianEDist I (f (minus s)) (f (minus t)) =
        ENNReal.ofReal |-(s : ℝ) - -(t : ℝ)| at h
      simpa only [neg_sub_neg, abs_sub_comm] using h)
  rw [hmz] at hv hvall
  have huend : intrinsicGeodesic g hEnorm (f z) u L = f right :=
    (huall ⟨L, ⟨hL.le, le_rfl⟩⟩).symm
  have hvend : intrinsicGeodesic g hEnorm (f z) v L = f left :=
    (hvall ⟨L, ⟨hL.le, le_rfl⟩⟩).symm
  have hleft : riemannianEDist I (f left) (f z) = ENNReal.ofReal L := by
    simpa only [left, z, sub_zero, abs_neg, abs_of_pos hL] using hdist left z
  have hright : riemannianEDist I (f z) (f right) = ENNReal.ofReal L := by
    simpa only [right, z, zero_sub, abs_neg, abs_of_pos hL] using hdist z right
  have htotal : riemannianEDist I (f left) (f right) = ENNReal.ofReal (L + L) := by
    have h := hdist left right
    change riemannianEDist I (f left) (f right) = ENNReal.ofReal (|-L - L|) at h
    rw [abs_of_nonpos (by linarith : -L - L ≤ 0)] at h
    simpa only [show -(-L - L) = L + L by ring] using h
  obtain ⟨w, hw, hwend⟩ := exists_unit_intrinsic_vector_of_pos_distance g hEnorm
    (f left) (f z) (by rw [hleft, ENNReal.toReal_ofReal hL.le]; exact hL)
  rw [hleft, ENNReal.toReal_ofReal hL.le] at hwend
  let gamma : ℝ → M := intrinsicGeodesic g hEnorm (f left) w
  have hfull : gamma (L + L) = f right :=
    intrinsicGeodesic_continues_of_distance_add g hEnorm (f left) (f right) w hw
      hL hL htotal (by rw [hwend]; exact hright)
  let mid : TangentSpace I (f z) := (mfderiv 𝓘(ℝ, ℝ) I gamma L 1 : E)
  have hmid : g.inner (f z) mid mid = 1 := by
    have h := (intrinsicGeodesic_speedSq_eq g hEnorm (f left) w L).trans hw
    have hbase := congrArg (fun p => g.inner p (mid : E) (mid : E)) hwend
    exact hbase.symm.trans h
  have hshift (s : ℝ) : gamma (s + L) = intrinsicGeodesic g hEnorm (f z) mid s := by
    have h := congrFun (intrinsicGeodesic_continuation g hEnorm (f left) w L) s
    exact h.trans (congrArg (fun p => intrinsicGeodesic g hEnorm p (mid : E) s) hwend)
  have hmidend : intrinsicGeodesic g hEnorm (f z) mid L = f right :=
    (hshift L).symm.trans hfull
  have hmideq : mid = u := unit_intrinsic_vector_eq_of_short_endpoint g hEnorm (f z)
    hmid hu hL hsmall (hmidend.trans huend.symm)
  have hneg (s : ℝ) : intrinsicGeodesic g hEnorm (f z) (-u) s =
      intrinsicGeodesic g hEnorm (f z) u (-s) := by
    simpa only [neg_one_smul, neg_one_mul] using
      intrinsicGeo_smul_apply g hEnorm (f z) u (-1) s
  have hnegend : intrinsicGeodesic g hEnorm (f z) (-u) L = f left := by
    rw [hneg]
    have h := hshift (-L)
    rw [neg_add_cancel, hmideq] at h
    exact h.symm.trans (intrinsicGeodesic_zero g hEnorm (f left) w)
  have hnegunit : g.inner (f z) (-u) (-u) = 1 := by
    simpa only [neg_one_smul, neg_one_sq, one_mul] using
      (gInner_smul_self g (f z) (-1) u).trans (by rw [hu]; norm_num)
  have hveq : v = -u := unit_intrinsic_vector_eq_of_short_endpoint g hEnorm (f z)
    hv hnegunit hL hsmall (hvend.trans hnegend.symm)
  refine ⟨u, hu, ?_⟩
  intro s
  rcases le_total (0 : ℝ) (s : ℝ) with hs | hs
  · exact huall ⟨s, ⟨hs, s.property.2⟩⟩
  · have h := hvall ⟨-(s : ℝ), ⟨neg_nonneg.mpr hs, by linarith [s.property.1]⟩⟩
    simpa only [minus, neg_zero, neg_neg, hveq, hneg] using h

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
