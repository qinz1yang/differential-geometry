import Batteries.Tactic.OpenPrivate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornCutoffRecord
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornFineCutNecks

open private PreparedCutoffEventGeometry PreparedCutoffEventGeometry.neck
  PreparedCutoffEventGeometry.static PreparedCutoffEventGeometry.protected_interior
  PreparedCutoffEventGeometry.retained_meets_protected orientedRotatedNeck_eq_datum_chart
  cutoffParametersOfFiniteCap sqrt_inv_lt_of_inv_sq_lt exists_scalar_upper_bound_on_cores
  range_oldOutput_eq_of_buffered_trace_stage finite_presented_static_cap_inclusion_cap_stage
  finitePresentedStaticCapsOfStage presented_static_cap_scale_of_terminal_neck_heq
  hasCanonicalWindow_of_finite_metric_stage
  exists_preparedCutoffEventGeometry_of_static_family_stage
  original_neck_data_of_terminal_heq exists_record_from_original_backward_with_static
  exists_append_metricCutCapEvent from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornCutoffRecord

open private exists_finite_first_hit_oriented_horn_neck_data_of_fineCutNecks from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornFineCutNecks

open private exists_precision_order_compatible precision_order_compatible_of_le from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornMetricEvent

set_option autoImplicit false

noncomputable section

open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Manifold
open DifferentialGeometry.PDE.RicciFlow.StandardCap DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

section

universe u

attribute [local instance] threeBallChartedSpace threeBall_isManifold

open private terminal_data_transport from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FinitePresentedStaticCap

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)


private theorem exists_prepared_horn_cutoff_event_with_original_neck_bounds_of_fineCutNecks :
    ∃ (c : ℝ) (_ : 4 ≤ c) (A : ℝ) (hA : 0 < A) (Kreset : ℝ), 3 ≤ Kreset ∧
      ∃ εcoarse : ℝ, 0 < εcoarse ∧
      ∀ Dcap : ℝ, 0 < Dcap → ∀ m : ℕ, ∀ accuracy : ℝ, 0 < accuracy →
      ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ δ ≤ η ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
      ε ≤ εcoarse → ∀ {εc Qc : ℝ}, 0 < εc → εc ≤ ε → εc ≤ ε₀ → P.FineCutNecks εc Qc →
      ∃ coreBound : ℝ, 0 ≤ coreBound ∧
      ∀ Q : ℝ, 2 * Λ * (P.coreRadius ^ 2)⁻¹ < Q →
      (((δ ^ 2 * D.parameters.neckRadius D.endTime) ^ 2)⁻¹) < Q → Qc ≤ Q →
      ∃ (Qout : OrientedThreeStage.{u})
        (E : MetricCutCapEvent D.stage Qout D.startTime D.endTime)
        (p : CutoffParameters)
        (N : E.transition.trace.tubes.Index → NormalizedNeck E.terminal.metric δ
          (max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4))),
        0 < Q ∧ E.incoming = D.slab ∧ HEq E.terminal D.terminal ∧
        E.old = E.transition.trace.retainedCore ∧ E.transition.boundaryFrameReversing ∧
        p.delta = (fun _ => δ) ∧ p.protectedRadius = (fun _ => P.coreRadius) ∧
        p.neckRadius = (fun _ => D.parameters.neckRadius D.endTime) ∧
        p.fixed = StaticCapScaffold.ofCollarLength A hA ∧ p.modelOrder = m ∧
        p.modelRadius = Dcap ∧ p.modelAccuracy = accuracy ∧ p.recenterConstant = c ∧
        Real.sqrt Q⁻¹ < (p.delta D.endTime)^2 * p.neckRadius D.endTime ∧
        (∃ Kvol : Set D.slab.terminalRegularOpen, IsCompact Kvol ∧
          riemannianVolumeMeasure ThreeModel Qout.Carrier E.outputMetric univ + ENNReal.ofReal
            ((Nat.card E.transition.trace.tubes.Index : ℝ) * Q ^ (-3 / 2 : ℝ)) ≤
          riemannianVolumeMeasure ThreeModel D.slab.terminalRegularOpen D.terminal.metric Kvol) ∧
        (∀ q ∈ E.capRegion, Q / 4 ≤ metricScalarAt E.outputMetric q) ∧
        (∀ q, metricScalarAt E.outputMetric q ≤ max coreBound (Kreset * Q)) ∧
        ∃ F : PreparedCutoffEventGeometry E p δ (Real.sqrt Q⁻¹)
          (max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4)), PreparedCutoffEventGeometry.neck F = N ∧
          (transitionEnd < p.modelRadius + 1 →
            ∀ b, (PreparedCutoffEventGeometry.static F b).hasCanonicalWindow) ∧
          ∃ (n : ℕ) (δOriginal : Fin n → ℝ) (kOriginal : Fin n → ℕ)
            (NOriginal : ∀ j, NormalizedNeck E.terminal.metric (δOriginal j) (kOriginal j))
            (hδOriginal : ∀ j, δOriginal j ≤ δ)
            (rotation : Fin n → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
            (hmark : ∀ j, DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j)
              spherePoint = (NOriginal j).sphereMark)
            (side : Fin n → Bool)
            (horder : ∀ j, max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4) ≤ kOriginal j)
            (hδ1 : δ < 1) (e : Fin n ≃ E.transition.trace.tubes.Index),
            (∀ j, (NOriginal j).scale = Q) ∧
            (∀ j, δOriginal j ≤ 2 * εc ∧ ⌊εc⁻¹⌋₊ + 1 ≤ kOriginal j) ∧
            (∃ (x₀ : Fin n → D.slab.terminalRegularOpen)
              (d₀ : ∀ j, normalizedDatum D.terminal.metric (x₀ j) δ (p.modelOrder + 6)),
              let hδ := fun j => (d₀ j).precision_pos
              let f := fun j => neckAmbientMap D.slab.terminalRegularOpen (d₀ j)
              ∃ (hf : ∀ j, _root_.Topology.IsOpenEmbedding (f j))
                (hd : Pairwise fun j k => Disjoint (range (f j)) (range (f k)))
                (hs : ∀ j, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (f j))
                (R : Set (ConnectedComponents (cutCore f)))
                (hRet : MapsTo (Subtype.val : cutCore f → D.stage.Carrier)
                  (retainedCore f R) D.slab.terminalRegularOpen),
                let Bidx := {b : Fin n × Bool // cuttingSphereComponent hδ f hf hd b ∈ R}
                ∃ (hrec : ∀ _ : Bidx, (p.recenterConstant * δ)⁻¹ + 1 ≤ δ⁻¹)
                  (dCap : ∀ b : Bidx, normalizedDatum D.terminal.metric
                    ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
                    (p.recenterConstant * δ) (p.modelOrder + 4))
                  (hmap : ∀ b, (dCap b).map =
                    (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
                  (hside : ∀ b, (dCap b).retainedSide = true)
                  (w : ∀ b, CanonicalStaticInsertionWitness (dCap b)
                    p.fixed.collarLength p.fixed.collar_pos p.modelRadius
                    p.modelOrder p.modelAccuracy),
                  let Qcap := FiniteCapQuotient transitionEnd_pos hδ f
                    (fun j => (hf j).injective) hd
                  letI : LocallyPathConnectedSpace D.stage.Carrier :=
                    originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
                  let Ret := finiteCapRetained transitionEnd_pos hδ f hf hd R
                  letI : ChartedSpace ThreeSpace Qcap := finiteCapChartedSpace ThreeModel
                    finrank_threeSpace_eq_three transitionEnd_pos hδ f hf hd
                  letI : IsManifold ThreeModel ∞ Qcap := finiteCapQuotient_isManifold
                    finrank_threeSpace_eq_three transitionEnd_pos hδ f hf hd hs
                  letI : T2Space Qcap := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hd
                  letI : CompactSpace Qcap := finiteCapQuotient_compactSpace
                    transitionEnd_pos hδ f hf hd
                  letI : CompactSpace Ret :=
                    (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf hd R).1
                  ∃ oRet : SmoothOrientation ThreeModel Ret,
                    Qout = OrientedThreeStage.ofSmoothOrientation Ret oRet ∧
                  (∀ j, metricScalarAt D.terminal.metric (x₀ j) = Q) ∧
                  (∀ b : Bidx,
                    |metricScalarAt D.terminal.metric
                      ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) /
                        metricScalarAt D.terminal.metric (x₀ b.val.1) - 1| ≤
                      p.recenterConstant * δ) ∧
                  HEq E.outputMetric
                    (finiteFullPreparedMetric ThreeModel hδ f hf hd hs
                      D.slab.terminalRegularOpen D.terminal.metric R hRet
                      p.recenterConstant p.recenterConstant_ge_four x₀
                      (fun _ => p.modelOrder + 6) d₀ (fun _ => rfl)
                      hrec dCap hmap hside w) ∧
                  HEq (range E.oldOutput)
                    (range (finiteRetainedCoreInclusion transitionEnd_pos hδ f hf hd R)) ∧
                  ∃ (S : ∀ b : E.RetainedBoundaryIndex,
                      E.PresentedStaticCap p.fixed p.modelRadius p.modelOrder p.modelAccuracy b)
                    (eB : E.RetainedBoundaryIndex ≃ Bidx),
                    PreparedCutoffEventGeometry.static F = S ∧ (∀ b, HEq b.val (eB b).val) ∧
                    (∀ b, HEq (S b).neck
                      (dCap (eB b)).oriented.toNormalizedNeck) ∧
                    (∀ b, (S b).neck.scale =
                      metricScalarAt D.terminal.metric
                        ((d₀ (eB b).val.1).offsetPoint (cuttingSign_sq (eB b).val.2))) ∧
                    (∀ b (z : standardCapWindow p.modelRadius),
                      HEq ((S b).inclusion ((S b).witness.window z))
                        (finiteFullWitnessMap ThreeModel finrank_threeSpace_eq_three
                          transitionEnd_pos hδ f hf hd hs R p.recenterConstant
                          p.recenterConstant_ge_four (eB b) ((w (eB b)).window z))) ∧
                    (transitionEnd < p.modelRadius + 1 → ∀ b (z : ThreeBall),
                      ∃ u : standardCapWindow p.modelRadius, ‖u.val‖ ≤ transitionEnd ∧
                        HEq (finiteFullWitnessMap ThreeModel finrank_threeSpace_eq_three
                          transitionEnd_pos hδ f hf hd hs R p.recenterConstant
                          p.recenterConstant_ge_four (eB b) ((w (eB b)).window u))
                          ((S b).inclusion ((S b).witness.cap z)))) ∧
            ∀ j, PreparedCutoffEventGeometry.neck F (e j) =
              ((((NOriginal j).monoDelta (hδOriginal j) hδ1).rotatedDatum (rotation j) (hmark j)
                (side j)).oriented).toNormalizedNeck.lowerOrder (horder j) := by
  classical
  obtain ⟨c, hc, C, hC, A, hA, hsmall, hfactory⟩ :=
    exists_uniform_metricCutCapEvent_volume_debit_with_recenter_data.{u}
  obtain ⟨eta, heta, hchoose⟩ := exists_finite_first_hit_oriented_horn_neck_data_of_fineCutNecks.{u}
  choose δcap hδcap hcapHalf hcapScalar using
    exists_metricCutCapEvent_capRegion_scalar_lower A hA
  let Kreset := max 3 (2 * C 0)
  have hKreset : 3 ≤ Kreset := le_max_left _ _
  refine ⟨c, hc, A, hA, Kreset, hKreset, eta, heta, ?_⟩
  intro Dcap hDcap m accuracy haccuracy η hη
  obtain ⟨δ₀, hδ₀, hquarter₀, hmake⟩ := hfactory Dcap hDcap m accuracy haccuracy δcap hδcap
  let δ := min δ₀ η
  have hδ : 0 < δ := lt_min hδ₀ hη
  have hδη : δ ≤ η := min_le_right _ _
  have hδle : δ ≤ δ₀ := min_le_left _ _
  have hquarter : δ < 1 / 4 := hδle.trans_lt hquarter₀
  have hδ1 : δ < 1 := hquarter.trans (by norm_num)
  obtain ⟨εbase, hεbase, hεeta, hεδ, hεsmall, hwidth, horderBase⟩ :=
    exists_precision_order_compatible hδ heta m
  let ε₀ := min (εbase / 2) (((2 * ⌊δ⁻¹⌋₊ + 4 : ℕ) : ℝ))⁻¹
  have hε₀ : 0 < ε₀ := lt_min (half_pos hεbase) (by positivity)
  have hεorder : 2 * ⌊δ⁻¹⌋₊ + 4 ≤ ⌊ε₀⁻¹⌋₊ + 1 := by
    have hle : ((2 * ⌊δ⁻¹⌋₊ + 4 : ℕ) : ℝ) ≤ ε₀⁻¹ := by
      simpa only [inv_inv] using inv_anti₀ hε₀ (min_le_right (εbase / 2)
        (((2 * ⌊δ⁻¹⌋₊ + 4 : ℕ) : ℝ))⁻¹)
    exact (Nat.le_floor hle).trans (Nat.le_succ _)
  refine ⟨δ, hδ, hδ1, hδη, ε₀, hε₀, ?_⟩
  intro D ε Λ P hε εc Qc hεc hεcε hεc₀ hfine
  let _ : SigmaCompactSpace D.slab.terminalRegularOpen :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
        D.slab.terminalRegularOpen.isOpen)
  obtain ⟨coreBound, hcoreNonneg, hcoreBound⟩ := exists_scalar_upper_bound_on_cores P
  let ρ := D.parameters.neckRadius D.endTime
  have ht : 0 ≤ D.endTime := D.startTime_nonneg.trans D.startTime_lt_endTime.le
  have hρ : 0 < ρ := D.parameters.neckRadius_pos _ ht
  refine ⟨coreBound, hcoreNonneg, ?_⟩
  intro Q hQscale hQnominal hQc
  have hQ : 0 < Q :=
    (inv_pos.mpr (sq_pos_of_pos (mul_pos (pow_pos hδ 2) hρ))).trans hQnominal
  have hr : Real.sqrt Q⁻¹ < δ^2 * ρ :=
    sqrt_inv_lt_of_inv_sq_lt hQ (mul_pos (pow_pos hδ 2) hρ) hQnominal
  have hεdouble : 2 * εc ≤ εbase := by
    have hh := hεc₀.trans (min_le_left _ _)
    linarith
  have hcompat := precision_order_compatible_of_le (mul_pos (by norm_num) hεc)
    hεdouble hεeta hεδ hεsmall hwidth horderBase
  have hm : m + 6 ≤ ⌊εc⁻¹⌋₊ + 1 := hcompat.2.2.2.2.trans
    (Nat.add_le_add_right (Nat.floor_mono (inv_anti₀ hεc
      (by linarith only [hεc] : εc ≤ 2 * εc))) 1)
  obtain ⟨r, hrc, hle, lambda, hlambda, hQpos, Fhorn, Khorn, hK, hfix, hF, hcore,
    e, a, ν, x₀, d, hscaleOrig, htrunc, ha, hside, hmap, hf, hd, hlocal, hRet,
    hfaces, hboundRet, horiginal⟩ :=
    hchoose P hε hεc hεcε hfine hcompat.2.1 hδ1 hcompat.2.2.2.1 m hm Q coreBound hQscale hQc
      hcoreBound
  let Padapt := (P.restrictHornCollars r hrc hle).rescaleHornParameters lambda hlambda
  let P' := Padapt.reparametrizeHornsOfCompactSupport Fhorn hfix Khorn hK hF
  let f := fun j => neckAmbientMap D.slab.terminalRegularOpen (d j)
  let R :=
    scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric f (P'.coreRadius^2)⁻¹
  have hone (j) : cuttingSphereComponent (fun j => (d j).precision_pos) f hf hd (j,true) ∈ R ∧
      cuttingSphereComponent (fun j => (d j).precision_pos) f hf hd (j,false) ∉ R :=
    ⟨(hfaces j true).mpr rfl, fun h => Bool.false_ne_true ((hfaces j false).mp h)⟩
  have hevent := hmake D.slab D.terminal (fun _ => δ) (fun j => (d j).precision_pos)
    (fun _ => hδle) x₀ d f hf hd hlocal (fun _ => rfl) R hRet D.singular hone Q hQpos hscaleOrig
  let hnontrivial := D.slab.nonempty_cut_or_discardedCore_of_singularEndpoint D.singular f R hRet
  let Qcap := FiniteCapQuotient transitionEnd_pos (fun j => (d j).precision_pos)
    f (fun j => (hf j).injective) hd
  let _ : LocallyPathConnectedSpace D.stage.Carrier :=
    originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
  let Ret := finiteCapRetained transitionEnd_pos (fun j => (d j).precision_pos) f hf hd R
  let Disc := finiteCapDiscarded transitionEnd_pos (fun j => (d j).precision_pos) f hf hd R
  let _ : ChartedSpace ThreeSpace Qcap := finiteCapChartedSpace ThreeModel
    finrank_threeSpace_eq_three transitionEnd_pos (fun j => (d j).precision_pos) f hf hd
  let _ : IsManifold ThreeModel ∞ Qcap := finiteCapQuotient_isManifold
    finrank_threeSpace_eq_three transitionEnd_pos (fun j => (d j).precision_pos) f hf hd hlocal
  let _ : T2Space Qcap := finiteCapQuotient_t2Space transitionEnd_pos
    (fun j => (d j).precision_pos) f hf hd
  let _ : CompactSpace Qcap := finiteCapQuotient_compactSpace transitionEnd_pos
    (fun j => (d j).precision_pos) f hf hd
  let _ : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace transitionEnd_pos
    (fun j => (d j).precision_pos) f hf hd R).1
  let _ : CompactSpace Disc := (finiteCapRetained_discarded_compactSpace transitionEnd_pos
    (fun j => (d j).precision_pos) f hf hd R).2
  obtain ⟨oQ, oRet, oDisc, rotationCap, B, aCap, hboundary, hchoice, hB, E,
    hDisc, hCap, htrace, htubes, hG, hL, hOld, hBoundary, hpin, hfloor, hvol,
    hrec, dCap, hcapMap, hcapSide, w, hOutput, hratio, hw, hcapPrecision, hlow⟩ := hevent
  obtain ⟨δOrig, kOrig, NOrig, hδOrig, rotation, hmark, side, horder, hdata, hdet, hdatum⟩ :=
    horiginal
  let k := max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4)
  have hk (j) : k ≤ kOrig j := by
    apply max_le (horder j)
    exact (hεorder.trans (Nat.add_le_add_right
      (Nat.floor_mono (inv_anti₀ hεc hεc₀)) 1)).trans (hdata j).2.2.2
  let Nhigh := fun j => ((((NOrig j).monoDelta (hδOrig j) hδ1).rotatedDatum (rotation j)
    (hmark j) (side j)).oriented).toNormalizedNeck.lowerOrder (hk j)
  have hNdata (j) := orientedRotatedNeck_eq_datum_chart (NOrig j) (hδOrig j) hδ1
    (rotation j) (hmark j) (side j) (hk j) (horder j) (hdata j).1 (d j) (hdatum j)
  let p := cutoffParametersOfFiniteCap δ hδ hδ1 ρ hρ P'.coreRadius P'.coreRadius_pos
    (StaticCapScaffold.ofCollarLength A hA) Dcap hDcap m accuracy haccuracy c hc
  have hprotected : ∀ x : D.slab.terminalRegularOpen,
      metricScalarAt D.terminal.metric x ≤ ((p.protectedRadius D.endTime)^2)⁻¹ →
      x.val ∈ interior ((Subtype.val : cutCore f → D.stage.Carrier) '' retainedCore f R) := by
    intro x hx
    exact P'.retainedCore_protected_of_central_horn_matching (fun _ => δ) e
      (fun j => a (e j).1.val (e j).2)
      (fun j => by linarith [ha (e j).1.val (e j).2, inv_pos.mpr hδ]) f (fun j => ν j)
      (fun j q _ => congrArg Subtype.val (hmap j q)) x hx
  have hscale (j) : metricScalarAt D.terminal.metric (x₀ j) = ((Real.sqrt Q⁻¹)^2)⁻¹ := by
    rw [hscaleOrig j, Real.sq_sqrt (inv_nonneg.mpr hQ.le), inv_inv]
  have hNchart (j q) : (Nhigh j).chart q = (d j).map q :=
    congrArg (fun C => C q) (hNdata j).1
  have hNmark (j) : (Nhigh j).sphereMark = spherePoint := (hNdata j).2.2.1
  have hNscale (j) : (Nhigh j).scale = metricScalarAt D.terminal.metric (x₀ j) :=
    (hNdata j).2.2.2.trans ((hdata j).2.1.trans (hscaleOrig j).symm)
  have hcapMake := hcapScalar (fun j => (d j).precision_pos) (fun j => (d j).precision_lt_one)
    f hf hd hlocal R hnontrivial (t₀ := D.startTime) (t₁ := D.endTime)
    (D := Dcap) (ε := accuracy) (m := m)
  have hcapBound := hcapMake oQ oRet oDisc E (fun b => (B b).toHomeomorph)
    (fun b => (aCap b).toHomeomorph) hboundary hDisc hCap htrace
    D.slab.terminalRegularOpen D.terminal.metric hRet c hc x₀ (fun _ => m + 6) d
    (fun _ => rfl) (fun _ => m + 4) hrec dCap hcapMap hcapSide w
    hcapPrecision (fun _ => by omega) (Q / 2) hlow hOutput
  have hbound : ∀ q ∈ E.capRegion, Q / 4 ≤ metricScalarAt E.outputMetric q := by
    intro q hq
    convert hcapBound q hq using 1
    ring
  have hupper := MetricCutCapEvent.scalar_le_of_finiteFullPreparedMetric ThreeModel
    (fun j => (d j).precision_pos) f hf hd hlocal D.slab.terminalRegularOpen
    D.terminal.metric R hRet c hc x₀ (fun _ => m + 6) d (fun _ => rfl)
    hrec dCap hcapMap hcapSide w hw (hC 0).le hratio (max coreBound (3 * Q)) Q hQ.le
    hboundRet (fun b => (hscaleOrig b.val.1).le) oRet E hOutput
  have hreset : ∀ q, metricScalarAt E.outputMetric q ≤ max coreBound (Kreset * Q) := by
    intro q
    apply (hupper q).trans
    apply max_le
    · exact max_le (le_max_left _ _)
        ((mul_le_mul_of_nonneg_right (le_max_left _ _) hQ.le).trans (le_max_right _ _))
    · exact (mul_le_mul_of_nonneg_right (le_max_right _ _) hQ.le).trans (le_max_right _ _)
  have hpreserve := terminal_data_transport E D.slab D.terminal hG hL
    (F := fun G L =>
      (∀ z : ℝ, 0 < z → (∀ x, InFixedHamiltonIveyRegion L.metric z x) →
        ∀ x, InFixedHamiltonIveyRegion E.outputMetric z x) ∧
      (∀ z : ℝ, z ≤ 0 → (∀ x, z ≤ metricScalarAt L.metric x) →
        ∀ x, z ≤ metricScalarAt E.outputMetric x)) ⟨hpin, hfloor⟩
  let caps :=
    finitePresentedStaticCapsOfStage
      (fixed := p.fixed) (D := p.modelRadius) (m := p.modelOrder) (ε := p.modelAccuracy) D.stage
      (fun j => (d j).precision_pos) (fun j => (d j).precision_lt_one)
      f hf hd hlocal R hnontrivial p.modelRadius_pos oQ oRet oDisc
      D.slab D.terminal E rotationCap (fun b => (B b).toHomeomorph) aCap
      hboundary hB hDisc hCap htrace hG hL hRet p.recenterConstant
      p.recenterConstant_ge_four x₀ (fun _ => p.modelOrder + 6) d (fun _ => rfl)
      (fun _ => p.modelOrder + 4) hrec dCap hcapMap hcapSide w hOutput
  let eBoundary := caps.1
  let S := caps.2.1
  have hBoundaryLabel := caps.2.2.1
  have hSδ := fun b => (caps.2.2.2 b).1
  have hSk := fun b => (caps.2.2.2 b).2.1
  have hSN := fun b => (caps.2.2.2 b).2.2.1
  have hSwindow := fun b => (caps.2.2.2 b).2.2.2
  have hSscale (b) : (S b).neck.scale = metricScalarAt D.terminal.metric
      ((d (eBoundary b).val.1).offsetPoint (cuttingSign_sq (eBoundary b).val.2)) :=
    presented_static_cap_scale_of_terminal_neck_heq (S b) D.slab D.terminal hG hL
      (dCap (eBoundary b)) (hSδ b) (hSk b) (hSN b)
  have hmarkWindow : transitionEnd < p.modelRadius + 1 → ∀ b (z : ThreeBall),
      ∃ u : standardCapWindow p.modelRadius, ‖u.val‖ ≤ transitionEnd ∧
        (S b).window u = (S b).inclusion ((S b).witness.cap z) := by
    intro hfit b z
    have hcapEq := finite_presented_static_cap_inclusion_cap_stage
      (fixed := p.fixed) (D := p.modelRadius) (m := p.modelOrder) (ε := p.modelAccuracy)
      D.stage (fun j => (d j).precision_pos) (fun j => (d j).precision_lt_one)
      f hf hd hlocal R hnontrivial p.modelRadius_pos oQ oRet oDisc D.slab D.terminal E
      (fun b => (B b).toHomeomorph) aCap hboundary hDisc hCap htrace hG hL
      p.recenterConstant p.recenterConstant_ge_four x₀ (fun _ => p.modelOrder + 6) d
      (fun _ => p.modelOrder + 4) dCap w eBoundary hBoundaryLabel b (S b) z
    exact ((w (eBoundary b)).exists_window_preimage_cap
      (E := ThreeSpace) (H := ThreeSpace) (M := D.slab.terminalRegularOpen) (I := ThreeModel)
      (g := D.terminal.metric)
      (x₀ := (d (eBoundary b).val.1).offsetPoint (cuttingSign_sq (eBoundary b).val.2))
      (δ := p.recenterConstant * δ) (k := p.modelOrder + 4) (d := dCap (eBoundary b))
      (A := p.fixed.collarLength) (hA := p.fixed.collar_pos) (D := p.modelRadius)
      (m := p.modelOrder) (ε := p.modelAccuracy) hfit (B (eBoundary b).val z)).imp fun u hu =>
        ⟨hu.1, (hSwindow b u).trans
          ((congrArg (finiteFullWitnessMap ThreeModel finrank_threeSpace_eq_three transitionEnd_pos
            (fun j => (d j).precision_pos) f hf hd hlocal R c hc (eBoundary b)) hu.2).trans
              hcapEq.symm)⟩
  have hcanonical : transitionEnd < p.modelRadius + 1 → ∀ b, (S b).hasCanonicalWindow := by
    intro hfit
    exact hasCanonicalWindow_of_finite_metric_stage
      (fixed := p.fixed) (D := p.modelRadius) (m := p.modelOrder) (ε := p.modelAccuracy)
      D.stage (fun j => (d j).precision_pos) f hf hd hlocal R oRet
      D.slab D.terminal E hG hL hRet c hc x₀ (fun _ => p.modelOrder + 6) d (fun _ => rfl)
      (fun _ => p.modelOrder + 4) hrec dCap hcapMap hcapSide w hOutput
      eBoundary S hSscale hSwindow (hmarkWindow hfit)
  obtain ⟨eEvent, geometry, hgeometry, hStatic⟩ :=
    exists_preparedCutoffEventGeometry_of_static_family_stage D.stage
      (fun j => (d j).precision_pos) (fun j => (d j).precision_lt_one)
      f hf hd hlocal R hnontrivial p oQ oRet oDisc D.slab D.terminal E rotationCap
      (fun b => (B b).toHomeomorph) aCap hboundary hB hDisc hCap htrace hG hL D.singular hOld
      x₀ d (fun _ => rfl) Nhigh hNchart hNmark hNscale hscale hprotected
      Subset.rfl hone hrec dCap hcapMap hcapSide eBoundary hBoundaryLabel
      S hSδ hSk hSN hratio hpreserve.1 hpreserve.2
  have hOldRange := range_oldOutput_eq_of_buffered_trace_stage D.stage
    (fun j => (d j).precision_pos) (fun j => (d j).precision_lt_one)
    f hf hd hlocal R hnontrivial oQ oRet oDisc B aCap hboundary E
    hDisc hCap htrace hOld
  obtain ⟨NOrigE, hmarkE, hNE, hNEpoint, hNEscale, hNEhigh⟩ := original_neck_data_of_terminal_heq
    E D.slab D.terminal hG hL hδ1 δOrig kOrig NOrig hδOrig rotation hmark side hk
  have hEscale (j) : (NOrigE j).scale = Q := by
    exact (hNEscale j).trans (hdata j).2.1
  refine ⟨_, E, p, PreparedCutoffEventGeometry.neck geometry, hQ, hG, hL, hOld, hBoundary,
    rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, hr, hvol, hbound, hreset, geometry, rfl,
    (fun hfit b => by rw [hStatic]; exact hcanonical hfit b),
    _, δOrig, kOrig, NOrigE, hδOrig, rotation, hmarkE, side, hk, hδ1, eEvent, hEscale,
    (fun j => ⟨(hdata j).2.2.1, (hdata j).2.2.2⟩), ?_, ?_⟩
  · exact funext fun _ => rfl
  · refine ⟨x₀, d, hf, hd, hlocal, R, hRet, hrec, dCap,
      hcapMap, hcapSide, w, oRet, rfl, hscaleOrig, hratio, heq_of_eq hOutput, heq_of_eq hOldRange,
      S, eBoundary, hStatic, hBoundaryLabel, hSN, hSscale,
      (fun b z => heq_of_eq (hSwindow b z)), ?_⟩
    intro hfit b z
    exact (hmarkWindow hfit b z).imp fun u hu =>
      ⟨hu.1, heq_of_eq ((hSwindow b u).symm.trans hu.2)⟩
  · intro j
    exact eq_of_heq ((hgeometry j).trans (hNEhigh j).symm)

end

section

universe u

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

theorem exists_horn_cutoff_history_extension_with_canonical_windows_of_fineCutNecks :
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ),
      4 ≤ recenterConstant ∧ ∃ εcoarse : ℝ, 0 < εcoarse ∧
    ∀ Dcap : ℝ, 0 < Dcap → transitionEnd < Dcap + 1 → ∀ m : ℕ, ∀ accuracy : ℝ, 0 < accuracy →
    ∀ η : ℝ, 0 < η →
    ∃ δ ε₀ : ℝ, 0 < δ ∧ δ < 1 ∧ δ ≤ η ∧ 0 < ε₀ ∧
    ∀ {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric}
      (H : RetainedCoreHistory.{u}) (initial : InitialIdentification P₀ g₀ H.toHistory),
      H.time (Fin.last H.eventCount) = H.horizon →
      ∀ (D : OneStepIncoming.{u}), H.stage (Fin.last H.eventCount) = D.stage →
      H.time (Fin.last H.eventCount) = D.startTime →
      HEq (D.slab.flow.base.metric D.startTime) (H.initialMetric (Fin.last H.eventCount)) →
      ∀ {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ), ε ≤ εcoarse →
      ∀ {εc Qc : ℝ}, 0 < εc → εc ≤ ε → εc ≤ ε₀ → P.FineCutNecks εc Qc →
      ∀ Q : ℝ, 2 * Λ * (P.coreRadius ^ 2)⁻¹ < Q →
      (((δ ^ 2 * D.parameters.neckRadius D.endTime) ^ 2)⁻¹) < Q → Qc ≤ Q →
      ∃ (Qout : OrientedThreeStage.{u}) (E : MetricCutCapEvent D.stage Qout D.startTime D.endTime)
        (hOld : E.old = E.transition.trace.retainedCore)
        (K : RetainedCoreHistory.{u}) (initialK : InitialIdentification P₀ g₀ K.toHistory)
        (i : Fin K.eventCount) (parameters : CutoffParameters)
        (n : ℕ) (δOriginal : Fin n → ℝ) (kOriginal : Fin n → ℕ)
        (NOriginal : ∀ j, NormalizedNeck (K.toHistory.event i).terminal.metric
          (δOriginal j) (kOriginal j))
        (hδOriginal : ∀ j, δOriginal j ≤ δ)
        (rotation : Fin n → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
        (hmark : ∀ j, DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j)
          spherePoint = (NOriginal j).sphereMark)
        (side : Fin n → Bool)
        (horder : ∀ j, max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4) ≤ kOriginal j)
        (hδ1 : δ < 1)
        (Nrecord : (K.toHistory.event i).transition.trace.tubes.Index →
          NormalizedNeck (K.toHistory.event i).terminal.metric δ
            (max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4)))
        (eOriginal : Fin n ≃ (K.toHistory.event i).transition.trace.tubes.Index),
        0 < Q ∧ E.incoming = D.slab ∧ HEq E.terminal D.terminal ∧
        E.transition.boundaryFrameReversing ∧
        initial.IsPrefixOf initialK ∧ K.horizon = D.endTime ∧ K.eventCount = H.eventCount + 1 ∧
        K.time (Fin.last K.eventCount) = D.endTime ∧ K.stage (Fin.last K.eventCount) = Qout ∧
        HEq (K.initialMetric (Fin.last K.eventCount)) E.outputMetric ∧
        i.val = H.eventCount ∧ K.stage i.castSucc = D.stage ∧ K.time i.castSucc = D.startTime ∧
        K.stage i.succ = Qout ∧ K.time i.succ = D.endTime ∧
        HEq (K.coreEvent i) (E.toRetainedCoreEvent hOld) ∧
        (∃ (Eappend : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Qout
            (H.time (Fin.last H.eventCount)) D.endTime)
          (hOldAppend : Eappend.old = Eappend.transition.trace.retainedCore)
          (hInitial : Eappend.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
            H.initialMetric (Fin.last H.eventCount)),
          HEq Eappend E ∧ K = H.appendEvent Eappend.incoming.lt
            (Eappend.toRetainedCoreEvent hOldAppend) hInitial) ∧
        parameters.delta = (fun _ => δ) ∧ parameters.protectedRadius = (fun _ => P.coreRadius) ∧
        parameters.neckRadius = (fun _ => D.parameters.neckRadius D.endTime) ∧
        parameters.fixed = fixed ∧ parameters.recenterConstant = recenterConstant ∧
        parameters.modelOrder = m ∧ parameters.modelRadius = Dcap ∧
        parameters.modelAccuracy = accuracy ∧
        (∀ x : E.incoming.terminalRegularOpen,
          metricScalarAt E.terminal.metric x ≤ ((parameters.protectedRadius D.endTime) ^ 2)⁻¹ →
          x.val ∈ interior (Subtype.val '' E.old)) ∧
        (∀ c : ConnectedComponents E.transition.trace.tubes.core,
          (∃ x : E.transition.trace.tubes.core,
            ConnectedComponents.mk x = c ∧ x ∈ E.transition.trace.retainedCore) →
          ∃ x : E.incoming.terminalRegularOpen,
            ∃ hx : x.val ∈ E.transition.trace.tubes.core,
              ConnectedComponents.mk ⟨x.val, hx⟩ = c ∧ metricScalarAt E.terminal.metric x ≤
                ((parameters.protectedRadius D.endTime) ^ 2)⁻¹) ∧
        (∀ j, (NOriginal j).scale = Q) ∧
        (∀ j, δOriginal j ≤ 2 * εc ∧ ⌊εc⁻¹⌋₊ + 1 ≤ kOriginal j) ∧
        (∀ j, Nrecord (eOriginal j) =
          (((NOriginal j).monoDelta (hδOriginal j) hδ1).rotatedDatum
            (rotation j) (hmark j) (side j)).oriented.toNormalizedNeck.lowerOrder (horder j)) ∧
        (∀ j (z : TubeDomain) (hz : (z.1, z.2.val) ∈ neckBuffer δ),
          (K.toHistory.event i).transition.trace.tubes.tube j z =
            ((Nrecord j).chart ⟨(z.1, z.2.val), hz⟩).val) ∧
        ((∀ j, Nonempty (IncomingBackwardNeck K.toHistory i (Nrecord j) (Real.sqrt Q⁻¹))) →
          ∃ G : GeometricCutoffRecord K.toHistory i parameters,
            G.delta = (fun _ => δ) ∧
            G.order = (fun _ => max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4)) ∧
            HEq G.neck Nrecord ∧ (∀ j, (G.neck j).scale = Q) ∧
            (∀ b, (G.static b).hasCanonicalWindow)) ∧
        (∃ Kvol : Set D.slab.terminalRegularOpen, IsCompact Kvol ∧
          riemannianVolumeMeasure ThreeModel Qout.Carrier E.outputMetric univ + ENNReal.ofReal
            ((Nat.card E.transition.trace.tubes.Index : ℝ) * Q ^ (-3 / 2 : ℝ)) ≤
          riemannianVolumeMeasure ThreeModel D.slab.terminalRegularOpen D.terminal.metric Kvol) ∧
        (∀ q ∈ E.capRegion, Q / 4 ≤ metricScalarAt E.outputMetric q) := by
  classical
  obtain ⟨c, hc, A, hA, Kreset, hKreset, εcoarse, hεcoarse, hfamily⟩ :=
    exists_prepared_horn_cutoff_event_with_original_neck_bounds_of_fineCutNecks.{u}
  refine ⟨StaticCapScaffold.ofCollarLength A hA, c, hc, εcoarse, hεcoarse, ?_⟩
  intro Dcap hDcap hDfit m accuracy haccuracy η hη
  obtain ⟨δ, hδ, hδ1, hδη, ε₀, hε₀, hmake⟩ := hfamily Dcap hDcap m accuracy haccuracy η hη
  refine ⟨δ, ε₀, hδ, hδ1, hδη, hε₀, ?_⟩
  intro P₀ g₀ H initial htime D hstage hstart hinit ε Λ P hε εc Qc hεc hεcε hεc₀ hfine
    Q hQscale hQnominal hQc
  obtain ⟨coreBound, hcoreNonneg, hproduce⟩ := hmake P hε hεc hεcε hεc₀ hfine
  obtain ⟨Qout, E, p, N, hQ, hG, hL, hOld, hBoundary,
    hpδ, hpR, hpρ, hpFixed, hpM, hpD, hpAcc, hpC, hr, hvol, hcap, hreset,
    geometry, hgeometry, hcanonical, n, δOrig, kOrig, NOrig, hδOrig, rotation, hmark,
    side, horder, hδ1', e, hscale, hsource, hrecipe, hneck⟩ := hproduce Q hQscale hQnominal hQc
  have hext : ∃ (K : RetainedCoreHistory.{u}) (B : InitialIdentification P₀ g₀ K.toHistory),
      initial.IsPrefixOf B ∧ K.horizon = D.endTime ∧ K.eventCount = H.eventCount + 1 ∧
      K.time (Fin.last K.eventCount) = D.endTime ∧ K.stage (Fin.last K.eventCount) = Qout ∧
      HEq (K.initialMetric (Fin.last K.eventCount)) E.outputMetric ∧
      ∃ i : Fin K.eventCount, i.val = H.eventCount ∧
        K.stage i.castSucc = D.stage ∧ K.time i.castSucc = D.startTime ∧
        K.stage i.succ = Qout ∧ K.time i.succ = D.endTime ∧
        HEq (K.coreEvent i) (E.toRetainedCoreEvent hOld) ∧
        ∃ (Eappend : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Qout
            (H.time (Fin.last H.eventCount)) D.endTime)
          (hOldAppend : Eappend.old = Eappend.transition.trace.retainedCore)
          (hInitial : Eappend.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
            H.initialMetric (Fin.last H.eventCount)),
          HEq Eappend E ∧ K = H.appendEvent Eappend.incoming.lt
            (Eappend.toRetainedCoreEvent hOldAppend) hInitial := by
    cases D with
    | mk stage startTime endTime hnonneg hlt slab terminal singular params =>
      cases hstage
      cases hstart
      have hinitE : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount) := by
        rw [hG]
        exact eq_of_heq hinit
      obtain ⟨K, B, hpref, hhor, hcount, htimeLast, hstageLast, hmetricLast,
        i, hi, hsource, hsourceTime, htarget, htargetTime, hEvent, hK⟩ :=
        exists_append_metricCutCapEvent H initial htime E hOld hinitE
      exact ⟨K, B, hpref, hhor, hcount, htimeLast, hstageLast, hmetricLast,
        i, hi, hsource, hsourceTime, htarget, htargetTime, hEvent,
        E, hOld, hinitE, HEq.rfl, hK⟩
  obtain ⟨K, B, hprefix, hhor, hcount, hlasttime, hlaststage, hlastmetric,
    i, hi, hsrc, hsrcTime, hout, houtTime, hEvent, happend⟩ := hext
  have hdelta : δ ≤ p.delta D.endTime := by rw [hpδ]
  have hk : max (p.modelOrder + 6) (2 * ⌊δ⁻¹⌋₊ + 4) ≤
      max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4) := by rw [hpM]
  obtain ⟨NOrigH, hmarkH, Nrecord, eOriginal, hNOrigH, hscaleH, hNrecord, hTube, hrecord⟩ :=
    exists_record_from_original_backward_with_static
    E hsrc hout hsrcTime houtTime geometry hEvent hdelta hk hr
    δOrig kOrig NOrig hδOrig hδ1' rotation hmark side horder e hneck
  refine ⟨Qout, E, hOld, K, B, i, p, n, δOrig, kOrig, NOrigH,
    hδOrig, rotation, hmarkH, side, horder, hδ1', Nrecord, eOriginal,
    hQ, hG, hL, hBoundary, hprefix, hhor, hcount, hlasttime, hlaststage, hlastmetric,
    hi, hsrc, hsrcTime, hout, houtTime, hEvent, happend, hpδ, hpR, hpρ, hpFixed, hpC, hpM,
    hpD, hpAcc,
    (by simpa only [hOld] using PreparedCutoffEventGeometry.protected_interior geometry),
    PreparedCutoffEventGeometry.retained_meets_protected geometry,
    (fun j => (hscaleH j).trans (hscale j)), hsource,
    hNrecord, hTube, ?_, hvol, hcap⟩
  intro hB
  obtain ⟨G, hδG, hkG, hNG, hscaleG, -, -, -, -, -, -, -, -, hcanon⟩ := hrecord hB
  refine ⟨G, hδG, hkG, hNG, ?_, hcanon (hcanonical (by simpa only [hpD] using hDfit))⟩
  intro j
  exact (hscaleG j).trans (by rw [Real.sq_sqrt (inv_nonneg.mpr hQ.le), inv_inv])

end

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
