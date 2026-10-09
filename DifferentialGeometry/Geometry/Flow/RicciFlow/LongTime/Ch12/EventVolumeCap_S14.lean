import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EventVolumeHausdorff_S14
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCapDistance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildComparisonLocalLength

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory TopologicalSpace Manifold
open DifferentialGeometry DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal Topology
universe u
namespace GC.LongTime.Ch12

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
  {fixed : StaticCapScaffold} {D : ℝ} {m : ℕ} {η : ℝ} {b : E.RetainedBoundaryIndex}

/-- The inclusion of a presented static cap into the output stage does not increase the length
distance (it is a local isometry). -/
theorem inclusion_edist_le_S14 (S : E.PresentedStaticCap fixed D m η b)
    (u v : S.witness.Output) :
    riemannianEDistOf E.outputMetric (S.inclusion u) (S.inclusion v) ≤
      riemannianEDistOf S.witness.metric u v := by
  have hld : IsLocalDiffeomorph ThreeModel ThreeModel ∞
      (S.inclusion : S.witness.Output → Q.Carrier) := by
    obtain ⟨Q', hQng, hQns, hQimm⟩ := S.inclusion_smooth.isImmersion
    refine DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
      S.inclusion_smooth.contMDiff (fun x => ?_) (by simp)
    exact DifferentialGeometry.Topology.Manifold.injective_mfderiv_of_isImmersionAt
      ThreeModel ThreeModel _ x ⟨Q', hQng, hQns, hQimm x⟩
  have h := DifferentialGeometry.Geometry.Metric.edistOf_le_of_quad_of_localDiffeomorph
    S.witness.metric E.outputMetric (S.inclusion : S.witness.Output → Q.Carrier) hld
    (c := 1) one_pos (fun x v => by
      simpa only [one_mul] using (S.inclusion_metric x v v).ge) u v
  simpa using h

/-- Cylinder coordinates `tip ≤ z ≤ 1` of a presented static cap: the region replaced by the cap
together with the first unit of retained collar. -/
def capBandBuf_S14 (S : E.PresentedStaticCap fixed D m η b) : Set (neckBuffer S.delta) :=
  {x | S.witness.tipCoordinate ≤ x.1.2 ∧ x.1.2 ≤ 1}

theorem one_lt_inv_delta_S14 (S : E.PresentedStaticCap fixed D m η b) : 1 < S.delta⁻¹ := by
  have h0 := S.neck.delta_pos
  have h1 := S.neck.delta_lt_one
  rw [lt_inv_comm₀ one_pos h0]
  simpa using h1

theorem capBandBuf_subset_central_S14 (S : E.PresentedStaticCap fixed D m η b) :
    capBandBuf_S14 S ⊆ neckCentralDomain S.delta := by
  intro x hx
  exact ⟨lt_of_lt_of_le S.witness.tipCoordinate_lower hx.1,
    lt_of_le_of_lt hx.2 (one_lt_inv_delta_S14 S)⟩

theorem isCompact_capBandBuf_S14 (S : E.PresentedStaticCap fixed D m η b) :
    IsCompact (capBandBuf_S14 S) := by
  have hT : IsCompact ((univ : Set (Sphere 2)) ×ˢ Icc S.witness.tipCoordinate 1) :=
    isCompact_univ.prod isCompact_Icc
  have hsub : ((univ : Set (Sphere 2)) ×ˢ Icc S.witness.tipCoordinate 1) ⊆
      (neckBuffer S.delta : Set NeckCylinder) := by
    intro x hx
    have h1 := S.witness.tipCoordinate_lower
    have h2 := one_lt_inv_delta_S14 S
    exact ⟨by have := hx.2.1; linarith, by have := hx.2.2; linarith⟩
  have himg : (Subtype.val : neckBuffer S.delta → NeckCylinder) '' capBandBuf_S14 S =
      (univ : Set (Sphere 2)) ×ˢ Icc S.witness.tipCoordinate 1 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨mem_univ _, hy.1, hy.2⟩
    · intro hx
      exact ⟨⟨x, hsub hx⟩, ⟨hx.2.1, hx.2.2⟩, rfl⟩
  exact (Topology.IsInducing.subtypeVal.isCompact_iff).mpr (himg ▸ hT)

/-- The central-domain version of `capBandBuf_S14`. -/
def capBandDom_S14 (S : E.PresentedStaticCap fixed D m η b) :
    Set (neckCentralDomain S.delta) :=
  {x | x.1 ∈ capBandBuf_S14 S}

/-- Central-domain point with prescribed cylinder coordinates. -/
def centralPt_S14 {δ : ℝ} (hδ : 0 < δ) (y : Sphere 2) (z : ℝ) (h1 : -δ⁻¹ < z) (h2 : z < δ⁻¹) :
    neckCentralDomain δ :=
  ⟨⟨(y, z), by
    have := inv_pos.mpr hδ
    exact ⟨by linarith, by linarith⟩⟩, h1, h2⟩

theorem retained_mem_collapse_image_S14 (S : E.PresentedStaticCap fixed D m η b)
    (x : neckRetainedCollar S.delta) (hx : x.1.2 ≤ 1) :
    S.witness.retained x ∈ S.witness.collapse '' capBandDom_S14 S := by
  have hδ := S.neck.delta_pos
  have hpos := inv_pos.mpr hδ
  have h1 : -S.delta⁻¹ < x.1.2 := by have := x.2.1; linarith
  let y := centralPt_S14 hδ x.1.1 x.1.2 h1 x.2.2
  have hy : y ∈ capBandDom_S14 S := ⟨by
    have := S.witness.tipCoordinate_lower
    have := x.2.1
    change S.witness.tipCoordinate ≤ x.1.2
    linarith [S.witness.tipCoordinate_upper, S.witness.radius_pos, fixed.collar_pos,
      standardCapL_pos], hx⟩
  refine ⟨y, hy, ?_⟩
  rw [S.witness.collapse_retained y x.2.1]
  rfl

theorem range_cap_subset_collapse_image_S14 (S : E.PresentedStaticCap fixed D m η b) :
    range S.witness.cap ⊆ S.witness.collapse '' capBandDom_S14 S := by
  have hδ := S.neck.delta_pos
  have hpos := inv_pos.mpr hδ
  have hL := standardCapL_pos
  have htip0 : S.witness.tipCoordinate ≤ 0 := by
    have := S.witness.tipCoordinate_upper
    have := fixed.collar_pos
    linarith
  have hbandOK : ∀ z : ℝ, S.witness.tipCoordinate ≤ z → z ≤ 0 → -S.delta⁻¹ < z ∧ z < S.delta⁻¹ := by
    intro z h1 h2
    exact ⟨lt_of_lt_of_le S.witness.tipCoordinate_lower h1, by linarith⟩
  rw [← S.witness.capChart_range]
  rintro _ ⟨p, rfl⟩
  by_cases hp0 : p.1 = 0
  · obtain ⟨y⟩ : Nonempty (Sphere 2) := ⟨S.neck.sphereMark⟩
    have hz := hbandOK _ le_rfl htip0
    let x := centralPt_S14 hδ y S.witness.tipCoordinate hz.1 hz.2
    refine ⟨x, ⟨le_rfl, (htip0.trans zero_le_one : S.witness.tipCoordinate ≤ 1)⟩, ?_⟩
    rw [S.witness.collapse_tip x le_rfl]
    have hmem : (0 : ThreeSpace) ∈ standardCapClosedCore := by
      simp [standardCapClosedCore, hL.le]
    rw [← S.witness.capChart_tip hmem]
    congr 1
    exact Subtype.ext hp0.symm
  · have hr : 0 < ‖p.1‖ := norm_pos_iff.mpr hp0
    have hrL : ‖p.1‖ ≤ standardCapL := by
      have := p.2
      simpa [standardCapClosedCore] using this
    have hivt := intermediate_value_Icc htip0 S.witness.radial_continuous
    have hmem : ‖p.1‖ ∈ Icc (S.witness.radial S.witness.tipCoordinate) (S.witness.radial 0) := by
      rw [S.witness.radial_tip, S.witness.radial_boundary]
      exact ⟨hr.le, hrL⟩
    obtain ⟨z, hzI, hz⟩ := hivt hmem
    have hzne : S.witness.tipCoordinate < z := by
      rcases hzI.1.eq_or_lt with h | h
      · exfalso
        rw [← h, S.witness.radial_tip] at hz
        exact hr.ne hz
      · exact h
    have hz' := hbandOK z hzI.1 hzI.2
    have hy : ‖‖p.1‖⁻¹ • p.1‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
    let yS : Sphere 2 := ⟨‖p.1‖⁻¹ • p.1, by simpa using hy⟩
    let x := centralPt_S14 hδ yS z hz'.1 hz'.2
    refine ⟨x, ⟨hzI.1, hzI.2.trans (by linarith)⟩, ?_⟩
    have hxmem : S.witness.radial z • yS.1 ∈ standardCapClosedCore := by
      have : S.witness.radial z • yS.1 = p.1 := by
        simp only [yS, hz, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      rw [this]; exact p.2
    rw [S.witness.collapse_radial x hzne hzI.2 hxmem]
    congr 1
    apply Subtype.ext
    change S.witness.radial z • yS.1 = p.1
    simp only [yS, hz, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]

private local instance sigmaCompactTRO2_S14 {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

private local instance secondCountableTRO_S14 {a s : ℝ} (G : P.IncomingSlab a s) :
    SecondCountableTopology G.terminalRegularOpen :=
  have : SecondCountableTopology P.Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace P.Carrier
  inferInstance

theorem isOpenEmbedding_neckChartCentral_S14 (S : E.PresentedStaticCap fixed D m η b) :
    _root_.Topology.IsOpenEmbedding
      (fun x : neckCentralDomain S.delta => S.neck.chart x.1) := by
  have hchart : _root_.Topology.IsOpenEmbedding (S.neck.chart : neckBuffer S.delta →
      E.incoming.terminalRegularOpen) :=
    DifferentialGeometry.Topology.Manifold.isOpenEmbedding_of_injective_immersion
      S.neck.chart S.neck.chart_smooth.contMDiff S.neck.chart_smooth.isEmbedding.injective
      (fun z => DifferentialGeometry.Topology.Manifold.injective_mfderiv_of_isImmersionAt
        NeckCylinderModel ThreeModel S.neck.chart z (S.neck.chart_smooth.isImmersion.isImmersionAt z))
      (by simp [Module.finrank_prod, ThreeSpace])
  exact hchart.comp (isOpen_neckCentralDomain S.delta).isOpenEmbedding_subtypeVal

theorem collapse_volume_le_band_S14 (S : E.PresentedStaticCap fixed D m η b) :
    riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric
        (S.inclusion '' (S.witness.collapse '' capBandDom_S14 S)) ≤
      riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen E.terminal.metric
        (S.neck.chart '' capBandBuf_S14 S) := by
  have hδ := S.neck.delta_pos
  let Φ : neckCentralDomain S.delta → E.incoming.terminalRegularOpen :=
    fun x => S.neck.chart x.1
  have hΦ : _root_.Topology.IsOpenEmbedding Φ := isOpenEmbedding_neckChartCentral_S14 S
  have hne : Nonempty (neckCentralDomain S.delta) :=
    ⟨centralPt_S14 hδ S.neck.sphereMark 0 (by simpa using inv_pos.mpr hδ)
      (by simpa using inv_pos.mpr hδ)⟩
  let f : E.incoming.terminalRegularOpen → Q.Carrier :=
    fun x => S.inclusion (S.witness.collapse (Function.invFun Φ x))
  have himg : S.inclusion '' (S.witness.collapse '' capBandDom_S14 S) = f '' (Φ '' capBandDom_S14 S) := by
    rw [image_image, image_image]
    apply image_congr
    intro x _
    simp only [f, Function.leftInverse_invFun hΦ.injective x]
  have hcomp : IsCompact (S.neck.chart '' capBandBuf_S14 S) :=
    (isCompact_capBandBuf_S14 S).image S.neck.chart.continuous
  have hset : S.neck.chart '' capBandBuf_S14 S = Φ '' capBandDom_S14 S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, capBandBuf_subset_central_S14 S hy⟩, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.1, hy, rfl⟩
  rw [himg, ← hset]
  let : MeasurableSpace E.incoming.terminalRegularOpen := borel _
  have : BorelSpace E.incoming.terminalRegularOpen := ⟨rfl⟩
  refine riemannianVolumeMeasure_image_le_of_local_edist_le_S14 (I := ThreeModel) (J := ThreeModel)
    (by simp [ThreeSpace]) (by simp [ThreeSpace]) E.terminal.metric E.outputMetric f
    (hcomp.isClosed.measurableSet) ?_
  intro x hx
  rw [hset] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨U, hU, hUle⟩ := S.witness.exists_mem_nhds_collapse_riemannianEDistOf_le p
  refine ⟨Φ '' U, hΦ.isOpenMap.image_mem_nhds hU, ?_⟩
  rintro _ ⟨y1, hy1, rfl⟩ _ ⟨y2, hy2, rfl⟩
  simp only [f, Function.leftInverse_invFun hΦ.injective y1, Function.leftInverse_invFun hΦ.injective y2]
  exact (inclusion_edist_le_S14 S _ _).trans (hUle y1 hy1 y2 hy2)

end GC.LongTime.Ch12
