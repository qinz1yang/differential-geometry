import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RegularPoleCenters
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientNegativeScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CurvatureNormalization

section

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open CanonicalNeighborhood
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

private local instance regularRescalingComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

private local instance regularRescalingTopology : TopologicalSpace F.M := F.topology
private local instance regularRescalingCharted : ChartedSpace H F.M := F.charted
private local instance regularRescalingSmooth : IsManifold I ∞ F.M := F.smooth
private local instance regularRescalingSigma : SigmaCompactSpace F.M := F.sigmaCompact
private local instance regularRescalingT2 : T2Space F.M := F.t2

theorem exists_eventually_curvatureNormalizedFlow_with_redLength_bound
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) {b : ℝ} (hb : b < 0) {t : ℝ} (ht : t ≤ b) (x : F.M)
    (hx : normSq0S (F.S.base.metric t) x 4 (F.S.base.rm04 t x) ≠ 0)
    (tau : ℕ → ℝ) (hescape : Tendsto tau atTop atTop) :
    let hbmem : b ∈ D.carrier := by simpa only [hF.carrier_eq, mem_Iic] using hb.le
    ∃ q : ℕ → F.M, ∀ᶠ i in atTop, ∃ hsigma : 0 < tau i + b,
      redLength F.S b p (q i) (tau i + b) ≤ (Module.finrank ℝ E : ℝ) / 2 ∧
      IsAncientKappaSolution kappa
        (curvatureNormalizedFlow F hF.carrier_eq hF.regular_eq
          b (tau i + b)⁻¹ (inv_pos.mpr hsigma) hbmem (q i)) ∧
      (curvatureNormalizedFlow F hF.carrier_eq hF.regular_eq
        b (tau i + b)⁻¹ (inv_pos.mpr hsigma) hbmem (q i)).S.base.metric (-1) =
        scaleMetric (tau i + b)⁻¹ (inv_pos.mpr hsigma) (F.S.base.metric (-tau i)) := by
  dsimp only
  obtain ⟨q, hq⟩ :=
    exists_eventually_redLength_le_half_finrank_of_ancient_of_neg F hF p hb tau hescape
  refine ⟨q, ?_⟩
  filter_upwards [hq] with i hi
  refine ⟨hi.1, hi.2, ?_, ?_⟩
  · exact isAncientKappaSolution_curvatureNormalizedFlow_of_rmNormSq_ne_zero
      F hF b (tau i + b)⁻¹ (inv_pos.mpr hi.1)
      (by simpa only [hF.carrier_eq, mem_Iic] using hb.le) (q i) ht x hx
  · change scaleMetric (tau i + b)⁻¹ (inv_pos.mpr hi.1)
      (F.S.base.metric (parabolicTime b (tau i + b)⁻¹ (-1))) = _
    have htime : parabolicTime b (tau i + b)⁻¹ (-1) = -tau i := by
      simp only [parabolicTime, div_inv_eq_mul, neg_one_mul]
      ring
    rw [htime]

theorem exists_neg_pole_eventually_curvatureNormalizedFlow_with_redLength_bound
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (hescape : Tendsto tau atTop atTop) :
    ∃ (b : ℝ) (_hb : b < 0) (hbmem : b ∈ D.carrier) (q : ℕ → F.M),
      ∀ᶠ i in atTop, ∃ hsigma : 0 < tau i + b,
        redLength F.S b p (q i) (tau i + b) ≤ (Module.finrank ℝ E : ℝ) / 2 ∧
        IsAncientKappaSolution kappa
          (curvatureNormalizedFlow F hF.carrier_eq hF.regular_eq
            b (tau i + b)⁻¹ (inv_pos.mpr hsigma) hbmem (q i)) ∧
        (curvatureNormalizedFlow F hF.carrier_eq hF.regular_eq
          b (tau i + b)⁻¹ (inv_pos.mpr hsigma) hbmem (q i)).S.base.metric (-1) =
          scaleMetric (tau i + b)⁻¹ (inv_pos.mpr hsigma) (F.S.base.metric (-tau i)) := by
  obtain ⟨b, hb, x, hnorm⟩ := exists_neg_time_rmNormSq_ne_zero_of_ancient F hF
  obtain ⟨q, hq⟩ := exists_eventually_curvatureNormalizedFlow_with_redLength_bound
    F hF p hb le_rfl x hnorm tau hescape
  exact ⟨b, hb, by simpa only [hF.carrier_eq, mem_Iic] using hb.le, q, hq⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

private local instance tailRescalingComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

private local instance tailRescalingTopology : TopologicalSpace F.M := F.topology
private local instance tailRescalingCharted : ChartedSpace H F.M := F.charted
private local instance tailRescalingSmooth : IsManifold I ∞ F.M := F.smooth
private local instance tailRescalingSigma : SigmaCompactSpace F.M := F.sigmaCompact
private local instance tailRescalingT2 : T2Space F.M := F.t2

abbrev poleRescaledFlowSeq
    (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b) : PointedFlowSeq.{u, uE, uH} (I := I) where
  D := ancientTimeInterval
  term i := curvatureNormalizedFlow F hcar hreg b (tau i + b)⁻¹
    (inv_pos.mpr (hsigma i)) hbmem (q i)

theorem poleRescaledFlowSeq_basepoint
    (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b) (i : ℕ) :
    ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).basepoint =
      q i := rfl

theorem poleRescaledFlowSeq_metric
    (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b) (i : ℕ) (s : ℝ) :
    ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S.base.metric s =
      scaleMetric (tau i + b)⁻¹ (inv_pos.mpr (hsigma i))
        (F.S.base.metric (parabolicTime b (tau i + b)⁻¹ s)) := rfl

theorem poleRescaledFlowSeq_metric_neg_one
    (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b) (i : ℕ) :
    ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S.base.metric (-1) =
      scaleMetric (tau i + b)⁻¹ (inv_pos.mpr (hsigma i)) (F.S.base.metric (-tau i)) := by
  rw [poleRescaledFlowSeq_metric]
  have htime : parabolicTime b (tau i + b)⁻¹ (-1) = -tau i := by
    simp only [parabolicTime, div_inv_eq_mul, neg_one_mul]
    ring
  rw [htime]

private theorem exists_poleRescaledFlowSeq_tail_of_eventually
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (b : ℝ) (hbmem : b ∈ D.carrier)
    (tau : ℕ → ℝ) (hescape : Tendsto tau atTop atTop) (q : ℕ → F.M)
    (h : ∀ᶠ i in atTop, ∃ hsigma : 0 < tau i + b,
      redLength F.S b p (q i) (tau i + b) ≤ (Module.finrank ℝ E : ℝ) / 2 ∧
      IsAncientKappaSolution kappa
        (curvatureNormalizedFlow F hF.carrier_eq hF.regular_eq
          b (tau i + b)⁻¹ (inv_pos.mpr hsigma) hbmem (q i))) :
    ∃ (N : ℕ) (hsigma : ∀ i, 0 < tau (i + N) + b),
      StrictMono (fun i : ℕ => i + N) ∧
      Tendsto (fun i : ℕ => i + N) atTop atTop ∧
      Tendsto (fun i : ℕ => tau (i + N)) atTop atTop ∧
      Tendsto (fun i : ℕ => tau (i + N) + b) atTop atTop ∧
      (∀ i, redLength F.S b p (q (i + N)) (tau (i + N) + b) ≤
        (Module.finrank ℝ E : ℝ) / 2) ∧
      (∀ i, IsAncientKappaSolution kappa
        ((poleRescaledFlowSeq F hF.carrier_eq hF.regular_eq b hbmem
          (fun j => tau (j + N)) (fun j => q (j + N)) hsigma).term i)) ∧
      ∀ i, ((poleRescaledFlowSeq F hF.carrier_eq hF.regular_eq b hbmem
          (fun j => tau (j + N)) (fun j => q (j + N)) hsigma).term i).S.base.metric (-1) =
        scaleMetric (tau (i + N) + b)⁻¹ (inv_pos.mpr (hsigma i))
          (F.S.base.metric (-tau (i + N))) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  have hpos (i : ℕ) : 0 < tau (i + N) + b := by
    obtain ⟨hsigma, _⟩ := hN (i + N) (Nat.le_add_left N i)
    exact hsigma
  have heta : Tendsto (fun i : ℕ => i + N) atTop atTop := tendsto_add_atTop_nat N
  have htau : Tendsto (fun i : ℕ => tau (i + N)) atTop atTop := hescape.comp heta
  have hsigma : Tendsto (fun i : ℕ => tau (i + N) + b) atTop atTop := by
    apply tendsto_atTop.mpr
    intro C
    filter_upwards [htau.eventually_ge_atTop (C - b)] with i hi
    linarith
  refine ⟨N, hpos, (fun _ _ hij => Nat.add_lt_add_right hij N), heta, htau, hsigma,
    ?_, ?_, ?_⟩
  · intro i
    obtain ⟨_, hbound, _⟩ := hN (i + N) (Nat.le_add_left N i)
    exact hbound
  · intro i
    obtain ⟨_, _, hancient⟩ := hN (i + N) (Nat.le_add_left N i)
    exact hancient
  · intro i
    exact poleRescaledFlowSeq_metric_neg_one F hF.carrier_eq hF.regular_eq
      b hbmem (fun j => tau (j + N)) (fun j => q (j + N)) hpos i

variable [I.Boundaryless]

theorem exists_poleRescaledFlowSeq_tail_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (hescape : Tendsto tau atTop atTop) :
    ∃ (b : ℝ) (_hb : b < 0) (hbmem : b ∈ D.carrier) (q : ℕ → F.M)
      (N : ℕ) (hsigma : ∀ i, 0 < tau (i + N) + b),
      StrictMono (fun i : ℕ => i + N) ∧
      Tendsto (fun i : ℕ => i + N) atTop atTop ∧
      Tendsto (fun i : ℕ => tau (i + N)) atTop atTop ∧
      Tendsto (fun i : ℕ => tau (i + N) + b) atTop atTop ∧
      (∀ i, redLength F.S b p (q (i + N)) (tau (i + N) + b) ≤
        (Module.finrank ℝ E : ℝ) / 2) ∧
      (∀ i, IsAncientKappaSolution kappa
        ((poleRescaledFlowSeq F hF.carrier_eq hF.regular_eq b hbmem
          (fun j => tau (j + N)) (fun j => q (j + N)) hsigma).term i)) ∧
      ∀ i, ((poleRescaledFlowSeq F hF.carrier_eq hF.regular_eq b hbmem
          (fun j => tau (j + N)) (fun j => q (j + N)) hsigma).term i).S.base.metric (-1) =
        scaleMetric (tau (i + N) + b)⁻¹ (inv_pos.mpr (hsigma i))
          (F.S.base.metric (-tau (i + N))) := by
  obtain ⟨b, hb, hbmem, q, hq⟩ :=
    exists_neg_pole_eventually_curvatureNormalizedFlow_with_redLength_bound F hF p tau hescape
  obtain ⟨N, hsigma, hmono, heta, htau, hsigmaTop, hbound, hancient, hmetric⟩ :=
    exists_poleRescaledFlowSeq_tail_of_eventually F hF p b hbmem tau hescape q
      (hq.mono fun i hi => by
        obtain ⟨hsigma, hbound, hancient, _⟩ := hi
        exact ⟨hsigma, hbound, hancient⟩)
  exact ⟨b, hb, hbmem, q, N, hsigma, hmono, heta, htau, hsigmaTop, hbound, hancient, hmetric⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end

section

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

private local instance endpointRescalingComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

private local instance endpointRescalingTopology : TopologicalSpace F.M := F.topology
private local instance endpointRescalingCharted : ChartedSpace H F.M := F.charted
private local instance endpointRescalingSmooth : IsManifold I ∞ F.M := F.smooth
private local instance endpointRescalingSigma : SigmaCompactSpace F.M := F.sigmaCompact
private local instance endpointRescalingT2 : T2Space F.M := F.t2

private theorem endpointRescaling_time_mem
    (hcar : D.carrier = Iic 0) {b tau : ℝ} (hbmem : b ∈ D.carrier)
    (hsigma : 0 < tau + b) : -tau ∈ D.carrier := by
  have hb : b ≤ 0 := by simpa only [hcar, mem_Iic] using hbmem
  rw [hcar]
  change -tau ≤ 0
  linarith

abbrev poleEndpointRescaledFlowSeq
    (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b) : PointedFlowSeq.{u, uE, uH} (I := I) where
  D := ancientTimeInterval
  term i := curvatureNormalizedFlow F hcar hreg (-tau i) (tau i + b)⁻¹
    (inv_pos.mpr (hsigma i)) (endpointRescaling_time_mem hcar hbmem (hsigma i)) (q i)

theorem poleEndpointRescaledFlowSeq_basepoint
    (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b) (i : ℕ) :
    ((poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).basepoint =
      q i := rfl

theorem poleEndpointRescaledFlowSeq_metric
    (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b) (i : ℕ) (s : ℝ) :
    ((poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S.base.metric s =
      scaleMetric (tau i + b)⁻¹ (inv_pos.mpr (hsigma i))
        (F.S.base.metric (-tau i + (tau i + b) * s)) := by
  change scaleMetric (tau i + b)⁻¹ (inv_pos.mpr (hsigma i))
    (F.S.base.metric (parabolicTime (-tau i) (tau i + b)⁻¹ s)) = _
  simp only [parabolicTime, div_inv_eq_mul, mul_comm]

theorem poleEndpointRescaledFlowSeq_metric_zero
    (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b) (i : ℕ) :
    ((poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S.base.metric 0 =
      scaleMetric (tau i + b)⁻¹ (inv_pos.mpr (hsigma i)) (F.S.base.metric (-tau i)) := by
  rw [poleEndpointRescaledFlowSeq_metric]
  simp only [mul_zero, add_zero]
  rfl

theorem poleEndpointRescaledFlowSeq_metric_eq_shift
    (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b) (i : ℕ) (s : ℝ) :
    ((poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S.base.metric s =
      ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S.base.metric
        (s - 1) := by
  rw [poleEndpointRescaledFlowSeq_metric, poleRescaledFlowSeq_metric]
  have htime : -tau i + (tau i + b) * s = parabolicTime b (tau i + b)⁻¹ (s - 1) := by
    simp only [parabolicTime, div_inv_eq_mul]
    ring
  rw [htime]

private theorem endpointRescaling_parabolicTime_mem
    (hcar : D.carrier = Iic 0) {b tau s : ℝ} (hbmem : b ∈ D.carrier)
    (hsigma : 0 < tau + b) (hs : s ≤ 0) :
    parabolicTime (-tau) (tau + b)⁻¹ s ∈ D.carrier := by
  have htime : -tau ≤ 0 := by
    simpa only [hcar, mem_Iic] using endpointRescaling_time_mem hcar hbmem hsigma
  rw [hcar]
  exact parabolicTime_nonpos htime (inv_pos.mpr hsigma) hs

theorem poleEndpointRescaledFlowSeq_complete
    (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b)
    (hcomplete : ∀ t ∈ D.carrier, RiemannianMetricComplete (I := I) (F.S.base.metric t)) :
    FlowMetricComplete (poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma) := by
  constructor
  intro i s hs
  have hsource : RiemannianMetricComplete (I := I)
      (F.S.base.metric (parabolicTime (-tau i) (tau i + b)⁻¹ s)) :=
    hcomplete _ (endpointRescaling_parabolicTime_mem hcar hbmem (hsigma i) hs)
  exact (curvatureNormalizedSolution_complete F.S (-tau i) (tau i + b)⁻¹
    (inv_pos.mpr (hsigma i)) (endpointRescaling_time_mem hcar hbmem (hsigma i)) s
    hsource).complete

theorem poleEndpointRescaledFlowSeq_nonnegativeCurvatureOperator
    (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b)
    (hcurv : ∀ t ∈ D.carrier, PointedFlowNonnegativeCurvatureOperator F t)
    (i : ℕ) {s : ℝ} (hs : s ≤ 0) :
    PointedFlowNonnegativeCurvatureOperator
      ((poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i) s :=
  curvatureNormalizedFlow_nonnegativeCurvatureOperator F hcar hreg
    (-tau i) (tau i + b)⁻¹ (inv_pos.mpr (hsigma i))
    (endpointRescaling_time_mem hcar hbmem (hsigma i)) (q i) s
    (hcurv _ (endpointRescaling_parabolicTime_mem hcar hbmem (hsigma i) hs))


theorem poleEndpointRescaledFlowSeq_noncollapsed
    (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b) (kappa : ℝ)
    (hnc : PointedFlowNoncollapsedAllScales F kappa) (i : ℕ) :
    PointedFlowNoncollapsedAllScales
      ((poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i) kappa := by
  let _ : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)
  exact curvatureNormalizedSolution_noncollapsed F.S hcar (-tau i) (tau i + b)⁻¹
    (inv_pos.mpr (hsigma i)) (endpointRescaling_time_mem hcar hbmem (hsigma i))
    kappa hnc

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end
