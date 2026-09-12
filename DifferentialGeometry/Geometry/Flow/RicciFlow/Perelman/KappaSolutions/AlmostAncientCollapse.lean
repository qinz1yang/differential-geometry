import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimLocalCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimUniformLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedBallVolumeLower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientAvrZero

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Manifold Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance almostAncientTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology
private local instance almostAncientCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted
private local instance almostAncientSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth
private local instance almostAncientC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
private local instance almostAncientT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space F.M := F.t2
private local instance almostAncientSigma {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : SigmaCompactSpace F.M := F.sigmaCompact
private local instance almostAncientTangentT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space (TangentBundle I F.M) :=
  F.t2TangentBundle
private local instance almostAncientMeasurable {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : MeasurableSpace F.M := borel F.M
private local instance almostAncientBorel {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : BorelSpace F.M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_normalized_klim_three_collapse_radius
    (hdim : Module.finrank ℝ E = 3) (kappa epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval,
        KLim (I := I) kappa F → PointedFlowScalarAtBase (I := I) F 1 →
        (∀ z : F.M, z ∈ riemannianBallOf (I := I) (F.S.base.metric 0) F.basepoint A →
          F.S.scalar 0 z ≤ 2) →
        riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)
            (riemannianBallOf (I := I) (F.S.base.metric 0) F.basepoint A) ≤
          ENNReal.ofReal epsilon * ENNReal.ofReal (A ^ 3) := by
  classical
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  by_contra hfailure
  push Not at hfailure
  let a : ℕ → ℝ := fun i => (i : ℝ) + 1
  have ha (i : ℕ) : 1 ≤ a i := by
    have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
    dsimp only [a]
    linarith
  have hcounter : ∀ i : ℕ,
      ∃ F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval,
        KLim (I := I) kappa F ∧ PointedFlowScalarAtBase (I := I) F 1 ∧
        (∀ z : F.M, z ∈ riemannianBallOf (I := I) (F.S.base.metric 0) F.basepoint (a i) →
          F.S.scalar 0 z ≤ 2) ∧
        ENNReal.ofReal epsilon * ENNReal.ofReal ((a i) ^ 3) <
          riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)
            (riemannianBallOf (I := I) (F.S.base.metric 0) F.basepoint (a i)) := by
    intro i
    exact hfailure (a i) (ha i)
  choose F hK hbase hlocal hvolume using hcounter
  let X : PointedFlowSeq.{u, uE, uH} (I := I) :=
    { D := ancientTimeInterval, term := F }
  have hexpand : Tendsto a atTop atTop := by
    apply tendsto_atTop_mono _ (tendsto_natCast_atTop_atTop (R := ℝ))
    intro i
    dsimp only [a]
    linarith
  have hlarge (i : ℕ) : 1 / 4 < a i := lt_of_lt_of_le (by norm_num) (ha i)
  obtain ⟨L, phi, hphi, Phi, hconnected, hcomplete, hconv⟩ :=
    exists_klim_three_ancient_limit X rfl hK hdim a hlarge hlocal hexpand
  have hcanonical : ∀ t ∈ X.D.carrier,
      ∃ C : MetricConvergenceData (I := I)
          (Phi.atTime (X := X) (L := L) (phi := phi) t),
        ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
          (I := I) (Phi.atTime (X := X) (L := L) (phi := phi) t) k := by
    intro t ht
    obtain ⟨C, hc, _hr⟩ := hconv t ht
    exact ⟨C, hc⟩
  have huniform : ∀ A : ℝ, ∀ᶠ i in atTop, ∀ t ∈ X.D.carrier, ∀ z : (X.term i).M,
      (riemannianEDistOf (I := I) ((X.term i).S.base.metric 0)
          (X.term i).basepoint z).toReal ≤ A →
        0 ≤ (X.term i).S.scalar t z ∧ (X.term i).S.scalar t z ≤ 2 := by
    intro A
    filter_upwards [hexpand.eventually_gt_atTop A] with i hi
    intro t ht z hz
    let _ : ConnectedSpace (F i).M := (hK i).connected
    let g := (F i).S.base.metric 0
    let _ : RiemannianBundle (fun y : (F i).M => TangentSpace I y) :=
      ⟨g.toRiemannianMetric⟩
    let _ : IsContinuousRiemannianBundle E (fun y : (F i).M => TangentSpace I y) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro y v w; rfl⟩⟩
    have hfinite : riemannianEDistOf (I := I) g (F i).basepoint z ≠ ⊤ := by
      change riemannianEDist I (F i).basepoint z ≠ ⊤
      exact Geometry.Riemannian.Exponential.riemannianEDist_ne_top
        (I := I) (F i).basepoint z
    have hzball : z ∈ riemannianBallOf (I := I) g (F i).basepoint (a i) := by
      change riemannianEDistOf (I := I) g (F i).basepoint z < ENNReal.ofReal (a i)
      rw [← ENNReal.ofReal_toReal hfinite]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).2
        (hz.trans_lt hi)
    have ht0 : t ≤ 0 := by
      change t ∈ ancientTimeInterval.carrier at ht
      simpa using ht
    exact ⟨(hK i).scalar_nonneg ht0 z,
      ((hK i).scalar_le_terminal ht0 z).trans (hlocal i z hzball)⟩
  have hlimit := ancientKappaThree_of_uniformly_bounded_KLim_limit
    X L Phi hdim rfl 2 (by norm_num) hK hbase hphi huniform
      hconnected hcomplete hcanonical
  obtain ⟨C0, hc0, _hr0⟩ := hconv 0
    (by change (0 : ℝ) ∈ ancientTimeInterval.carrier; simp)
  have hsourceComplete : SeqMetricComplete (I := I) (X.atTime (I := I) 0) :=
    ⟨fun i => (hK i).complete 0 (by simp)⟩
  have hRic : ∀ i : ℕ, RicciBoundedBelow (I := I) ((F i).S.base.metric 0) 0 := by
    intro i z v
    rw [zero_mul, ← metricRicciAt_apply_eq_ricciTensor]
    apply metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (I := I) ((F i).S.base.metric 0) z).mpr
    intro n c u w
    simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
      (hK i).nonnegativeCurvatureOperator 0 (by simp) z n c u w
  have hsourceVolume : ∀ i : ℕ,
      ENNReal.ofReal epsilon * ENNReal.ofReal ((a i) ^ Module.finrank ℝ E) ≤
        riemannianVolumeMeasure (I := I) (M := (F i).M) ((F i).S.base.metric 0)
          (riemannianBallOf (I := I) ((F i).S.base.metric 0) (F i).basepoint (a i)) := by
    intro i
    simpa only [hdim] using (hvolume i).le
  obtain ⟨_hballs, havr, hnoncompact⟩ := pointed_ball_volume_lower_of_expanding_radii
    C0 hc0 (hcomplete 0 (by change (0 : ℝ) ∈ ancientTimeInterval.carrier; simp))
      hsourceComplete (fun i => (hK i).connected) hRic hphi a hexpand
      (ENNReal.ofReal epsilon) hsourceVolume
  have heps0 : ENNReal.ofReal epsilon ≠ 0 := (ENNReal.ofReal_pos.mpr hepsilon).ne'
  have hzero := ancientKappaThree_terminal_avr_eq_zero L hlimit.1 hdim
    (hnoncompact heps0) L.basepoint
  change ENNReal.ofReal epsilon / euclideanUnitBallVolume (Module.finrank ℝ E) ≤
    asymptoticVolumeRatio (I := I) (L.S.base.metric 0) L.basepoint at havr
  rw [hzero] at havr
  exact (ENNReal.div_pos heps0 (euclideanUnitBallVolume_ne_top _)).not_ge havr

theorem exists_almost_ancient_collapse_constants
    (hdim : Module.finrank ℝ E = 3) (kappa epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ A L : ℝ, 1 ≤ A ∧ A ^ 2 ≤ L ∧
      ∀ (D : RealTimeInterval) (F : PointedFlowData.{u, uE, uH} (I := I) D),
        KLim (I := I) kappa F → ∀ (x : F.M) (Q r : ℝ),
        0 < Q → F.S.scalar 0 x = Q → 0 < r →
        (∀ t : ℝ, t ≤ 0 → ∀ z : F.M,
          z ∈ riemannianBallOf (I := I) (F.S.base.metric 0) x r →
            F.S.scalar t z ≤ 2 * Q) → L ≤ r ^ 2 * Q →
        riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)
            (riemannianBallOf (I := I) (F.S.base.metric 0) x (A / Real.sqrt Q)) ≤
          ENNReal.ofReal epsilon * ENNReal.ofReal ((A / Real.sqrt Q) ^ 3) := by
  obtain ⟨A, hA, hcollapse⟩ :=
    exists_normalized_klim_three_collapse_radius (I := I) hdim kappa epsilon hepsilon
  refine ⟨A, A ^ 2, hA, le_rfl, ?_⟩
  intro D F hK x Q r hQ hvalue hr hlocal hscale
  let _ : TopologicalSpace F.M := F.topology
  let _ : ChartedSpace H F.M := F.charted
  let _ : IsManifold I ∞ F.M := F.smooth
  have hzero : (0 : ℝ) ∈ D.carrier := by
    simpa only [hK.carrier_eq, Set.mem_Iic] using (le_rfl : (0 : ℝ) ≤ 0)
  let G := curvatureNormalizedFlow F hK.carrier_eq hK.regular_eq 0 Q hQ hzero x
  have hGbase : G.basepoint = x := rfl
  have hG : KLim (I := I) kappa G :=
    KLim.curvatureNormalizedFlow F hK 0 Q hQ hzero x hvalue
  have hbase : PointedFlowScalarAtBase (I := I) G 1 :=
    curvatureNormalizedFlow_scalar_base F hK.carrier_eq hK.regular_eq
      0 Q hQ hzero x hvalue
  have hg : G.S.base.metric 0 = scaleMetric Q hQ (F.S.base.metric 0) := by
    change scaleMetric Q hQ (F.S.base.metric (parabolicTime 0 Q 0)) = _
    rw [parabolicTime_zero]
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hAr : A ≤ Real.sqrt Q * r := by
    apply (sq_le_sq₀ hApos.le (mul_pos hsqrt hr).le).1
    rw [mul_pow, Real.sq_sqrt hQ.le]
    nlinarith
  have hnormalized : ∀ z : G.M,
      z ∈ riemannianBallOf (I := I) (G.S.base.metric 0) G.basepoint A →
        G.S.scalar 0 z ≤ 2 := by
    intro z hz
    have hzscaled : z ∈ riemannianBallOf (I := I)
        (scaleMetric Q hQ (F.S.base.metric 0)) x A := by
      rw [hg, hGbase] at hz
      convert hz using 1
      rfl
    have hzsource : z ∈ riemannianBallOf (I := I) (F.S.base.metric 0) x r := by
      rw [← riemannianBallOf_scaleMetric (F.S.base.metric 0) Q hQ x r]
      change riemannianEDistOf (I := I) (scaleMetric Q hQ (F.S.base.metric 0)) x z <
        ENNReal.ofReal (Real.sqrt Q * r)
      exact hzscaled.trans_le (ENNReal.ofReal_le_ofReal hAr)
    change (curvatureNormalizedSolution F.S 0 Q hQ hzero).scalar 0 z ≤ 2
    rw [curvatureNormalizedSolution_scalar]
    change Q⁻¹ * F.S.scalar (parabolicTime 0 Q 0) z ≤ 2
    rw [parabolicTime_zero]
    calc
      Q⁻¹ * F.S.scalar 0 z ≤ Q⁻¹ * (2 * Q) :=
        mul_le_mul_of_nonneg_left (hlocal 0 le_rfl z hzsource) (inv_nonneg.mpr hQ.le)
      _ = 2 := by rw [mul_left_comm, inv_mul_cancel₀ hQ.ne', mul_one]
  have hvolume := hcollapse G hG hbase hnormalized
  have hball : riemannianBallOf (I := I) (scaleMetric Q hQ (F.S.base.metric 0)) x A =
      riemannianBallOf (I := I) (F.S.base.metric 0) x (A / Real.sqrt Q) := by
    simpa only [mul_div_cancel₀ A hsqrt.ne'] using
      riemannianBallOf_scaleMetric (F.S.base.metric 0) Q hQ x (A / Real.sqrt Q)
  change @riemannianVolumeMeasure E _ _ _ H _ I F.M
    F.topology F.charted F.smooth F.t2 F.sigmaCompact (G.S.base.metric 0)
    {z : F.M | @riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
      (G.S.base.metric 0) x z < ENNReal.ofReal A} ≤
      ENNReal.ofReal epsilon * ENNReal.ofReal (A ^ 3) at hvolume
  rw [hg] at hvolume
  change riemannianVolumeMeasure (I := I) (M := F.M)
    (scaleMetric Q hQ (F.S.base.metric 0))
    (riemannianBallOf (I := I) (scaleMetric Q hQ (F.S.base.metric 0)) x A) ≤
      ENNReal.ofReal epsilon * ENNReal.ofReal (A ^ 3) at hvolume
  rw [hball, volume_scale_apply, hdim] at hvolume
  have hpower : ENNReal.ofReal (A ^ 3) =
      ENNReal.ofReal (Real.sqrt Q) ^ 3 * ENNReal.ofReal ((A / Real.sqrt Q) ^ 3) := by
    calc
      ENNReal.ofReal (A ^ 3) =
          ENNReal.ofReal ((Real.sqrt Q * (A / Real.sqrt Q)) ^ 3) := by
        rw [mul_div_cancel₀ A hsqrt.ne']
      _ = _ := by
        rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg hsqrt.le _),
          ENNReal.ofReal_pow hsqrt.le]
  rw [hpower] at hvolume
  have hcoef0 : ENNReal.ofReal (Real.sqrt Q) ^ 3 ≠ 0 :=
    pow_ne_zero _ (ENNReal.ofReal_pos.mpr hsqrt).ne'
  have hcoeftop : ENNReal.ofReal (Real.sqrt Q) ^ 3 ≠ ⊤ :=
    ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  apply (ENNReal.mul_le_mul_iff_right hcoef0 hcoeftop).1
  calc
    ENNReal.ofReal (Real.sqrt Q) ^ 3 *
        riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)
          (riemannianBallOf (I := I) (F.S.base.metric 0) x (A / Real.sqrt Q)) ≤
        ENNReal.ofReal epsilon *
          (ENNReal.ofReal (Real.sqrt Q) ^ 3 * ENNReal.ofReal ((A / Real.sqrt Q) ^ 3)) :=
      hvolume
    _ = ENNReal.ofReal (Real.sqrt Q) ^ 3 *
        (ENNReal.ofReal epsilon * ENNReal.ofReal ((A / Real.sqrt Q) ^ 3)) := by ac_rfl

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
