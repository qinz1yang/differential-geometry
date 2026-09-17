import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AlmostAncientCollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AnchoredSpatialPointSelection

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle _root_.Manifold Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance anchoredFlowTopology {T : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) T) : TopologicalSpace F.M := F.topology
private local instance anchoredFlowCharted {T : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) T) : ChartedSpace H F.M := F.charted
private local instance anchoredFlowSmooth {T : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) T) : IsManifold I ∞ F.M := F.smooth
private local instance anchoredFlowC1 {T : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) T) : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
private local instance anchoredFlowT2 {T : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) T) : T2Space F.M := F.t2
private local instance anchoredFlowSigma {T : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) T) : SigmaCompactSpace F.M := F.sigmaCompact
private local instance anchoredFlowTangentT2 {T : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) T) : T2Space (TangentBundle I F.M) :=
  F.t2TangentBundle
private local instance anchoredFlowMeasurable {T : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) T) : MeasurableSpace F.M := borel F.M
private local instance anchoredFlowBorel {T : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) T) : BorelSpace F.M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_anchored_scalar_bound
    (hdim : Module.finrank ℝ E = 3) (kappa v D : ℝ) (hv : 0 < v) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : RealTimeInterval) (F : PointedFlowData.{u, uE, uH} (I := I) T),
        KLim (I := I) kappa F → ∀ p : F.M,
        ENNReal.ofReal v ≤
          riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)
            (riemannianBallOf (I := I) (F.S.base.metric 0) p 1) →
        ∀ q : F.M, q ∈ riemannianBallOf (I := I) (F.S.base.metric 0) p D →
          F.S.scalar 0 q ≤ C := by
  classical
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let eta : ℝ := 1 - 1 / Real.sqrt 2
  have hroot : 0 < Real.sqrt 2 := zero_lt_one.trans Real.one_lt_sqrt_two
  have heta : 0 < eta :=
    sub_pos.mpr ((div_lt_one hroot).2 Real.one_lt_sqrt_two)
  have heta_one : eta < 1 := by
    dsimp only [eta]
    linarith [one_div_pos.mpr hroot]
  let b : ℝ := D + 1
  let B : ℝ := D + 2
  have hb : 0 < b := by dsimp only [b]; linarith only [hD]
  have hB : 0 < B := by dsimp only [B]; linarith only [hD]
  let epsilon : ℝ := v / (2 * B ^ 3)
  have hepsilon : 0 < epsilon := div_pos hv (mul_pos (by norm_num) (pow_pos hB 3))
  obtain ⟨A, L, hA, hAL, hcollapse⟩ :=
    exists_almost_ancient_collapse_constants (I := I) hdim kappa epsilon hepsilon
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hL : 0 ≤ L := (sq_nonneg A).trans hAL
  have hproduct : 0 ≤ A ^ 2 * b ^ 2 := mul_nonneg (sq_nonneg A) (sq_nonneg b)
  let C : ℝ := (L + A ^ 2 * b ^ 2 + 1) / eta ^ 2
  have hC : 0 < C := div_pos (by linarith) (sq_pos_of_pos heta)
  refine ⟨C, hC, ?_⟩
  intro T F hK p hanchor q hq
  by_contra hqbound
  have hqC : C < F.S.scalar 0 q := lt_of_not_ge hqbound
  have hqpos : 0 < F.S.scalar 0 q := hC.trans hqC
  let _ : ConnectedSpace F.M := hK.connected
  let g := F.S.base.metric 0
  have hzero : (0 : ℝ) ∈ T.carrier := by
    simpa only [hK.carrier_eq, Set.mem_Iic] using (le_rfl : (0 : ℝ) ≤ 0)
  have hcomplete : RiemannianMetricComplete (I := I) g := ⟨hK.complete 0 hzero⟩
  have hqdist : (riemannianEDistOf (I := I) g p q).toReal < D :=
    ENNReal.toReal_lt_of_lt_ofReal hq
  obtain ⟨w, hw, hsigma, hs, hQ, hweight, hlocal⟩ :=
    exists_anchoredScalarSpatialPointSelection g hcomplete p hD q hqdist hqpos
  let sigma : ℝ := D + 1 - (riemannianEDistOf (I := I) g p w).toReal
  let s : ℝ := eta * sigma
  let Q : ℝ := F.S.scalar 0 w
  change 0 < sigma at hsigma
  change 0 < s at hs
  change 0 < Q at hQ
  change eta ^ 2 * F.S.scalar 0 q ≤ Q * s ^ 2 at hweight
  change ∀ z : F.M, riemannianEDistOf (I := I) g w z < ENNReal.ofReal s →
    F.S.scalar 0 z ≤ 2 * Q at hlocal
  have hthreshold : L + A ^ 2 * b ^ 2 + 1 < eta ^ 2 * F.S.scalar 0 q := by
    have h := (div_lt_iff₀ (sq_pos_of_pos heta)).1 hqC
    simpa only [mul_comm] using h
  have hlarge : L + A ^ 2 * b ^ 2 + 1 < Q * s ^ 2 :=
    hthreshold.trans_le hweight
  have hscale : L ≤ s ^ 2 * Q := by nlinarith only [hlarge, hproduct]
  have hsigma_b : sigma ≤ b := by
    have hd : 0 ≤ (riemannianEDistOf (I := I) g p w).toReal := ENNReal.toReal_nonneg
    dsimp only [sigma, b]
    linarith only [hd]
  have hs_b : s ≤ b :=
    (mul_le_of_le_one_left hsigma.le heta_one.le).trans hsigma_b
  have hs_square : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.le hb.le).2 hs_b
  have hQ_square : A ^ 2 < Q := by
    have hupper : Q * s ^ 2 ≤ Q * b ^ 2 :=
      mul_le_mul_of_nonneg_left hs_square hQ.le
    have hstrict : A ^ 2 * b ^ 2 < Q * b ^ 2 := by
      linarith only [hlarge, hupper, hL]
    exact (mul_lt_mul_iff_left₀ (sq_pos_of_pos hb)).1 hstrict
  let rho : ℝ := A / Real.sqrt Q
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hrho : 0 < rho := div_pos hApos hsqrt
  have hrho_one : rho < 1 :=
    (div_lt_one hsqrt).2 ((Real.lt_sqrt hApos.le).2 hQ_square)
  have hrho_B : rho ≤ B := by dsimp only [B]; linarith only [hrho_one, hD]
  have hpast : ∀ t : ℝ, t ≤ 0 → ∀ z : F.M,
      z ∈ riemannianBallOf (I := I) (F.S.base.metric 0) w s →
        F.S.scalar t z ≤ 2 * Q := by
    intro t ht z hz
    exact (hK.scalar_le_terminal ht z).trans (hlocal z hz)
  have hsmall := hcollapse T F hK w Q s hQ rfl hs hpast hscale
  change riemannianVolumeMeasure (I := I) (M := F.M) g
      (riemannianBallOf (I := I) g w rho) ≤
    ENNReal.ofReal epsilon * ENNReal.ofReal (rho ^ 3) at hsmall
  let _ : RiemannianBundle (fun z : F.M => TangentSpace I z) :=
    ⟨g.toRiemannianMetric⟩
  have hcomm : riemannianEDistOf (I := I) g w p =
      riemannianEDistOf (I := I) g p w := Manifold.riemannianEDist_comm
  have hunit_subset : riemannianBallOf (I := I) g p 1 ⊆
      riemannianBallOf (I := I) g w B := by
    intro z hz
    have hzin := riemannianBallOf_subset_add_distance (I := I) g w p 1 hz
    have hrad : 1 + (riemannianEDistOf (I := I) g w p).toReal ≤ B := by
      rw [hcomm]
      dsimp only [B]
      linarith only [hw]
    exact riemannianBallOf_mono (I := I) g w hrad hzin
  have hbig : ENNReal.ofReal v ≤ riemannianVolumeMeasure (I := I) (M := F.M) g
      (riemannianBallOf (I := I) g w B) := hanchor.trans (measure_mono hunit_subset)
  have hRic : RicciBoundedBelow (I := I) g 0 := by
    intro z v
    rw [zero_mul, ← metricRicciAt_apply_eq_ricciTensor]
    apply metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (I := I) g z).mpr
    intro n c u w
    simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
      hK.nonnegativeCurvatureOperator 0 hzero z n c u w
  have hbishop := (riemannianBallOf_volume_bishop_nonnegative
    (I := I) g hcomplete hRic w).1 rho B hrho hrho_B
  simp only [hdim] at hbishop
  have hratio : ENNReal.ofReal (rho ^ 3) * ENNReal.ofReal v ≤
      ENNReal.ofReal (rho ^ 3) * (ENNReal.ofReal (B ^ 3) * ENNReal.ofReal epsilon) := by
    calc
      ENNReal.ofReal (rho ^ 3) * ENNReal.ofReal v =
          ENNReal.ofReal v * ENNReal.ofReal (rho ^ 3) := mul_comm _ _
      _ ≤ riemannianVolumeMeasure (I := I) (M := F.M) g
          (riemannianBallOf (I := I) g w B) * ENNReal.ofReal (rho ^ 3) :=
        mul_le_mul_left hbig _
      _ ≤ ENNReal.ofReal (B ^ 3) * riemannianVolumeMeasure (I := I) (M := F.M) g
          (riemannianBallOf (I := I) g w rho) := hbishop
      _ ≤ ENNReal.ofReal (B ^ 3) *
          (ENNReal.ofReal epsilon * ENNReal.ofReal (rho ^ 3)) :=
        mul_le_mul_right hsmall _
      _ = _ := by ac_rfl
  have hrho0 : ENNReal.ofReal (rho ^ 3) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (pow_pos hrho 3)).ne'
  have hbad := (ENNReal.mul_le_mul_iff_right hrho0 ENNReal.ofReal_ne_top).1 hratio
  rw [← ENNReal.ofReal_mul (pow_nonneg hB.le 3)] at hbad
  have hbadReal : v ≤ B ^ 3 * epsilon :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (pow_nonneg hB.le 3) hepsilon.le)).1 hbad
  have hepsilon_value : B ^ 3 * epsilon = v / 2 := by
    dsimp only [epsilon]
    field_simp [hB.ne']
  rw [hepsilon_value] at hbadReal
  linarith only [hbadReal, hv]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
