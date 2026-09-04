import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Domain
import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.Ball
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.FrameBound
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Measure
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.NoConjugatePoints
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Polar

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

omit [T2Space M] [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem gBall_model_eucl
    (g : SmoothRiemannianMetric I M) (x : M) {R : ℝ} (hR : 0 < R) :
    (∫⁻ θ : Metric.sphere (0 : E) 1,
        ENNReal.ofReal (normalChartDensity (I := I) g x 0 *
          (Real.sqrt (g.inner x θ.1 θ.1) ^ (Module.finrank ℝ E))⁻¹)
        ∂(modelHaar (E := E)).toSphere) *
      ENNReal.ofReal (hypRadVol 0 (Module.finrank ℝ E - 1) R) =
        (volume : Measure E) (Metric.ball (0 : E) R) := by
  let _ : Nontrivial E :=
    Module.nontrivial_of_finrank_pos
      (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  let L : E ≃L[ℝ] E := normalFrame (I := I) (E := E) g x
  have hpreclosed :
      L ⁻¹' closedGBall (I := I) g x R =
        Metric.closedBall (0 : E) R := by
    ext w
    simp only [Set.mem_preimage, closedGBall, Set.mem_ofPred_eq,
      Metric.mem_closedBall, dist_zero_right]
    have hsqrt : Real.sqrt (g.inner x (L w) (L w)) = ‖w‖ := by
      with_unfolding_all exact normalFrame_sqrt (I := I) g x w
    rw [hsqrt]
  have hclosed : MeasurableSet (closedGBall (I := I) g x R) :=
    (isClosed_closedGBall (I := I) g x R).measurableSet
  have hmodel := gBall_model_int (I := I) g x 0 R (by positivity) hR
  calc
    (∫⁻ θ : Metric.sphere (0 : E) 1,
        ENNReal.ofReal (normalChartDensity (I := I) g x 0 *
          (Real.sqrt (g.inner x θ.1 θ.1) ^ (Module.finrank ℝ E))⁻¹)
        ∂(modelHaar (E := E)).toSphere) *
        ENNReal.ofReal (hypRadVol 0 (Module.finrank ℝ E - 1) R) =
      ∫⁻ v in closedGBall (I := I) g x R,
        ENNReal.ofReal (normalChartDensity (I := I) g x 0 *
          hypDensity (0 * Real.sqrt (g.inner x
            (show TangentSpace I x from v)
            (show TangentSpace I x from v)))
            (Module.finrank ℝ E - 1) 1) ∂(modelHaar (E := E)) :=
      hmodel.symm
    _ = ENNReal.ofReal (normalChartDensity (I := I) g x 0) *
        (modelHaar (E := E)) (closedGBall (I := I) g x R) := by
      have hfun : (fun v : E =>
          ENNReal.ofReal (normalChartDensity (I := I) g x 0 *
            hypDensity (0 * Real.sqrt (g.inner x
              (show TangentSpace I x from v)
              (show TangentSpace I x from v)))
              (Module.finrank ℝ E - 1) 1)) =
          fun _ : E =>
            ENNReal.ofReal (normalChartDensity (I := I) g x 0) := by
        funext v
        simp [hypDensity, hypSn]
      rw [hfun, setLIntegral_const]
    _ = (ENNReal.ofReal (normalChartDensity (I := I) g x 0) •
          modelHaar (E := E)) (closedGBall (I := I) g x R) := by
      simp only [Measure.smul_apply, smul_eq_mul]
    _ = (Measure.map L (volume : Measure E))
        (closedGBall (I := I) g x R) := by
      with_unfolding_all exact
        (congrArg
          (fun μ : Measure E => μ (closedGBall (I := I) g x R))
          (normalHaar_eq (E := E) (M := M) (I := I) g x))
    _ = (volume : Measure E)
        (L ⁻¹' closedGBall (I := I) g x R) := by
      rw [Measure.map_apply L.continuous.measurable hclosed]
    _ = (volume : Measure E) (Metric.closedBall (0 : E) R) := by
      rw [hpreclosed]
    _ = (volume : Measure E) (Metric.ball (0 : E) R) :=
      Measure.addHaar_closedBall_eq_addHaar_ball
        (volume : Measure E) (0 : E) R

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem segBall_vol_le_euclidean [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (x : M) {q R : ℝ} (hq : 0 ≤ q) (hR : 0 < R)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2))) :
    riemannianVolumeMeasure (I := I) (M := M) g
        {y : M | riemannianEDist I x y < ENNReal.ofReal R}
      ≤ ((MeasureTheory.volume : MeasureTheory.Measure
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere Set.univ)
        * ENNReal.ofReal (hypRadVol q (Module.finrank ℝ E - 1) R) := by
  classical
  let : Nontrivial E :=
    Module.nontrivial_of_finrank_pos
      (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  let L : E ≃L[ℝ] E := normalFrame (I := I) (E := E) g x
  let K : Set E :=
    (SegDom (I := I) g hEnorm x : Set E) ∩
      L '' Metric.closedBall (0 : E) R
  have hK : IsCompact K := by
    dsimp only [K]
    exact
      ((isCompact_closedBall (0 : E) R).image L.continuous).inter_left
        (isClosed_segDom (I := I) g hEnorm x)
  have hpre :
      L ⁻¹' gBall (I := I) g x R = Metric.ball (0 : E) R := by
    with_unfolding_all exact preimage_gBall (I := I) (E := E) g x R
  have hcover :
      {y : M | riemannianEDist I x y < ENNReal.ofReal R} ⊆
        (fun b : E =>
          expMapIntrinsic (I := I) g hEnorm x
            (show TangentSpace I x from b)) '' K := by
    intro y hy
    obtain ⟨v, hv, hexp⟩ :=
      ball_sub_image_segDom (I := I) g hEnorm x R hy
    have hwopen : L.symm v ∈ Metric.ball (0 : E) R := by
      rw [← hpre]
      change (show TangentSpace I x from
        L (L.symm (show E from v))) ∈ gBall (I := I) g x R
      have hL : L (L.symm (show E from v)) = (show E from v) :=
        L.apply_symm_apply (show E from v)
      rw [hL]
      exact hv.2
    refine ⟨v, ⟨hv.1, ?_⟩, hexp⟩
    exact ⟨L.symm v, Metric.ball_subset_closedBall hwopen, L.apply_symm_apply v⟩
  let Dn : E → ℝ := fun w =>
    curveDensity (I := I) g
      (intrinsicGeodesic (I := I) g hEnorm x (L w))
      (fun i t =>
        intrinsicJacobi (I := I) g hEnorm x (L w)
          ((normalBasis (I := I) g x) i) t)
      1
  let Dh : E → ℝ≥0∞ := fun w =>
    ENNReal.ofReal
      (hypDensity (q * ‖w‖) (Module.finrank ℝ E - 1) 1)
  have hpreK :
      L ⁻¹' K ⊆ Metric.closedBall (0 : E) R := by
    intro w hw
    change L w ∈ K at hw
    rcases hw.2 with ⟨z, hz, hzw⟩
    have hzw' : z = w := L.injective hzw
    simpa only [hzw'] using hz
  have hpreK_meas : MeasurableSet (L ⁻¹' K) :=
    (hK.isClosed.preimage L.continuous).measurableSet
  have hpoint :
      ∀ᵐ w ∂(volume : Measure E), w ∈ L ⁻¹' K →
        ENNReal.ofReal (Dn w) ≤ Dh w := by
    filter_upwards [Measure.ae_ne (volume : Measure E) (0 : E)] with w hw0 hw
    change L w ∈ K at hw
    have hu0 : L w ≠ 0 := by
      intro hLw
      apply hw0
      apply L.injective
      simpa only [map_zero] using hLw
    have hno :
        ∀ t ∈ Set.Ioo (0 : ℝ) 1,
          ¬ IsConjVec (I := I) g hEnorm x
            ((t • L w : TangentSpace I x) : E) :=
      segDom_no_conj (I := I) g hEnorm hw.1 hu0
    have hdens :=
      expDens_le_hyp (I := I) g hEnorm x (L w)
        (normalBasis (I := I) g x)
        (normalBasis_inner (I := I) g x)
        q hq hu0 hno hRic
    have hsqrt :
        Real.sqrt (g.inner x (L w) (L w)) = ‖w‖ := by
      with_unfolding_all exact normalFrame_sqrt (I := I) g x w
    apply ENNReal.ofReal_le_ofReal
    simpa only [Dn, Dh, hsqrt] using hdens
  have hmono :
      (∫⁻ w in L ⁻¹' K, ENNReal.ofReal (Dn w) ∂(volume : Measure E)) ≤
        ∫⁻ w in L ⁻¹' K, Dh w ∂(volume : Measure E) :=
    setLIntegral_mono_ae' hpreK_meas hpoint
  have hball_ae :
      Metric.closedBall (0 : E) R =ᵐ[(volume : Measure E)]
        Metric.ball (0 : E) R := by
    have hmeasure :
        (volume : Measure E) (Metric.closedBall (0 : E) R) =
          (volume : Measure E) (Metric.ball (0 : E) R) :=
      Measure.addHaar_closedBall_eq_addHaar_ball
        (volume : Measure E) (0 : E) R
    exact
      (ae_eq_of_subset_of_measure_ge Metric.ball_subset_closedBall
        hmeasure.le measurableSet_ball.nullMeasurableSet
        measure_closedBall_lt_top.ne).symm
  have hnormal :
      (∫⁻ w in L ⁻¹' K, ENNReal.ofReal (Dn w) ∂(volume : Measure E)) ≤
        ((volume : Measure
            (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere Set.univ)
          * ENNReal.ofReal
              (hypRadVol q (Module.finrank ℝ E - 1) R) := by
    calc
      (∫⁻ w in L ⁻¹' K,
          ENNReal.ofReal (Dn w) ∂(volume : Measure E)) ≤
          ∫⁻ w in L ⁻¹' K, Dh w ∂(volume : Measure E) := hmono
      _ ≤ ∫⁻ w in Metric.closedBall (0 : E) R,
          Dh w ∂(volume : Measure E) :=
        lintegral_mono_set hpreK
      _ = ∫⁻ w in Metric.ball (0 : E) R,
          Dh w ∂(volume : Measure E) :=
        setLIntegral_congr hball_ae
      _ = (volume : Measure E).toSphere Set.univ *
          ENNReal.ofReal
            (hypRadVol q (Module.finrank ℝ E - 1) R) := by
        simpa only [Dh] using hypBall_lintegral (E := E) q hq hR
      _ = ((volume : Measure
            (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere Set.univ)
          * ENNReal.ofReal
              (hypRadVol q (Module.finrank ℝ E - 1) R) := by
        rw [volSphere_finrank (E := E)]
  calc
    riemannianVolumeMeasure (I := I) (M := M) g
        {y : M | riemannianEDist I x y < ENNReal.ofReal R} ≤
      riemannianVolumeMeasure (I := I) (M := M) g
        ((fun b : E =>
          expMapIntrinsic (I := I) g hEnorm x
            (show TangentSpace I x from b)) '' K) :=
      measure_mono hcover
    _ ≤ ∫⁻ v in K,
        ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v)
          ∂(modelHaar (E := E)) :=
      riemVol_exp_image_le (I := I) g hEnorm x hK
    _ = ∫⁻ w in L ⁻¹' K,
        ENNReal.ofReal (Dn w) ∂(volume : Measure E) := by
      with_unfolding_all exact
        expJac_normal_int (I := I) (E := E) g hEnorm x K
    _ ≤ ((volume : Measure
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere Set.univ)
        * ENNReal.ofReal
            (hypRadVol q (Module.finrank ℝ E - 1) R) :=
      hnormal

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem segBall_vol_pow [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {s R : ℝ} (hs : 0 < s) (hsR : s ≤ R)
    (hRic : RicciBoundedBelow (I := I) g 0) :
    riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I x y < ENNReal.ofReal R}
        * ENNReal.ofReal (s ^ Module.finrank ℝ E) ≤
      ENNReal.ofReal (R ^ Module.finrank ℝ E) *
        riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I x y < ENNReal.ofReal s} := by
  let n : ℕ := Module.finrank ℝ E
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hR : 0 < R := hs.trans_le hsR
  have hrel := segBall_vol_rel (I := I) g hEnorm x
    (q := 0) (s := s) (R := R) (by positivity) hs hsR (by simpa using hRic)
  have hmodel (t : ℝ) (ht : 0 ≤ t) :
      ENNReal.ofReal (hypRadVol 0 (n - 1) t) =
        ENNReal.ofReal (t ^ n) * ENNReal.ofReal ((n : ℝ)⁻¹) := by
    have hnR : ((n - 1 : ℕ) : ℝ) + 1 = n := by
      rw [Nat.cast_sub hn]
      norm_num
    rw [hypRadVol_zero, Nat.sub_add_cancel hn, hnR, div_eq_mul_inv,
      ENNReal.ofReal_mul (pow_nonneg ht n)]
  rw [show Module.finrank ℝ E - 1 = n - 1 by rfl,
    hmodel s hs.le, hmodel R hR.le] at hrel
  have hfactor_pos : 0 < ENNReal.ofReal ((n : ℝ)⁻¹) :=
    ENNReal.ofReal_pos.mpr (inv_pos.mpr (Nat.cast_pos.mpr hn))
  have hscaled :
      ENNReal.ofReal ((n : ℝ)⁻¹) *
          (riemannianVolumeMeasure (I := I) (M := M) g
              {y : M | riemannianEDist I x y < ENNReal.ofReal R} *
            ENNReal.ofReal (s ^ n)) ≤
        ENNReal.ofReal ((n : ℝ)⁻¹) *
          (ENNReal.ofReal (R ^ n) *
            riemannianVolumeMeasure (I := I) (M := M) g
              {y : M | riemannianEDist I x y < ENNReal.ofReal s}) := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hrel
  exact (ENNReal.mul_le_mul_iff_right hfactor_pos.ne' ENNReal.ofReal_ne_top).mp hscaled

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
