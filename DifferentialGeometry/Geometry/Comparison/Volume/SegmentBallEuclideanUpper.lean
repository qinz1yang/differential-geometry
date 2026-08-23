import DifferentialGeometry.Geometry.Comparison.Volume.SegmentDomain
import DifferentialGeometry.Geometry.Comparison.Volume.BishopBall
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentFrameBound
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentMeasure
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentNoConj

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

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
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
  letI : Nontrivial E :=
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
    simpa only [L] using preimage_gBall (I := I) (E := E) g x R
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
      simpa only [Set.mem_preimage, L.apply_symm_apply] using hv.2
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
      simpa only [L] using normalFrame_sqrt (I := I) g x w
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
      simpa only [Dn, L] using
        expJac_normal_int (I := I) (E := E) g hEnorm x K
    _ ≤ ((volume : Measure
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere Set.univ)
        * ENNReal.ofReal
            (hypRadVol q (Module.finrank ℝ E - 1) R) :=
      hnormal

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
