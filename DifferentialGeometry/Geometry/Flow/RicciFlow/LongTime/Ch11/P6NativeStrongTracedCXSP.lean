import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongCeilingWireC11SC
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.NeckRmBoundCXCC
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegion

set_option autoImplicit false

/-!
# Native strong neck to an actual traced region / 原 history 上的 native neck 窗

使用 S16 选出的同一 witness，由其 neck implication 取得实际 survivor flow。
空间半径为 1/(2 sqrt R)、时间深度为 1/R、Rm 界为 1200 R。
该 universal constant 仅需 neck 自带的 eps < 1/11；未新增 trace、curvature bound 或 S11 输入。

同 W 的 neck 分支仍须由实际 minimizing segment 的双端 scalar gap 证明。
本文件不声称整个 native Claim 2 分支或 hspine 已闭合，也不处理非 regular 查询时刻。
S16 原 history 的全窗 metric identity 支付 ordinary 点；RegularCrossing 的
Rm 等式支付每个 incoming terminal face。
-/

noncomputable section

open Set Manifold
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch11

universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩

private theorem cylinder_rmNormSq_le_one_CXSP {s : ℝ} (hs : s ≤ 0) (y : Cylinder) :
    normSq0S (cylinderReferenceMetric s) y 4
      (metricRm04At (cylinderReferenceMetric s) y) ≤ 1 := by
  have hmax : max (2 * (1 - s)) 1 = 2 * (1 - s) := max_eq_left (by linarith)
  have hp : 0 < 2 * (1 - s) := by linarith
  have hprod : cylinderReferenceMetric s =
      (scaleMetric (max (2 * (1 - s)) 1)
        (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
        (Geometry.roundMetric (E := ThreeSpace) (n := 2))).prod
          (euclideanMetric (E := ℝ)) := by
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    rw [Perelman.CanonicalNeighborhood.FiniteHorn.cylinderReferenceMetric,
      Geometry.Metric.cylinderMetric_inner,
      SmoothRiemannianMetric.prod_inner]
    congr 1
    change v.2 * w.2 = w.2 * v.2
    ring
  rw [hprod, normSq0S_metricRm04At_productReal,
    GC.Geometry.normSq0S_metricRm04At_eq_sq_of_finrank_two (by simp),
    metricScalarAt_scaleMetric, metricScalarAt_roundMetric_eq (by norm_num), hmax]
  have hi : 0 ≤ (2 * (1 - s))⁻¹ := inv_nonneg.mpr hp.le
  have hi' : (2 * (1 - s))⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ hp (by norm_num)]
    linarith
  nlinarith

/-- The actual spatial comparison at every normalized time bounds Rm, without PDE reuse. -/
private theorem strongNeck_rmNormSq_map_le_CXSP
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [T2Space M]
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
    {eps t : ℝ} {x : M} (nk : StrongNeck S eps x t)
    {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 0) {y : Cylinder}
    (hy : y ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) :
    normSq0S (S.base.metric (t + s / S.scalar t x)) (nk.map y) 4
        (metricRm04At (S.base.metric (t + s / S.scalar t x)) (nk.map y)) ≤
      (1200 * S.scalar t x) ^ 2 := by
  let O : TopologicalSpace.Opens Cylinder :=
    ⟨univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, isOpen_univ.prod isOpen_Ioo⟩
  let V : TopologicalSpace.Opens M :=
    ⟨nk.map '' (O : Set Cylinder), image_opens_isOpen nk.map nk.domain⟩
  let Phi : O ≃ₘ⟮IC, I3⟯ V := PartialDiffeomorph.toOpensDiffeo nk.map nk.domain
  let Q := S.scalar t x
  let G := scaleMetric Q nk.Q_pos
    (Diffeomorph.pullbackMetricCross ((S.base.metric (t + s / Q)).restrictOpen V) Phi)
  let z : O := ⟨y, hy⟩
  let _ : SigmaCompactSpace O := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen IC O.isOpen)
  have hG (w : O) (v v' : TangentSpace IC w) :
      G.inner w v v' =
        (Perelman.CanonicalNeighborhood.rescaledMetric S t Q nk.Q_pos s).inner (nk.map w.val)
        (mfderiv IC I3 nk.map w.val v) (mfderiv IC I3 nk.map w.val v') := by
    simp only [G, Perelman.CanonicalNeighborhood.rescaledMetric,
      parabolicTime, scaleMetric_inner,
      Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.restrictOpen_inner]
    change Q * (S.base.metric (t + s / Q)).inner (nk.map w.val)
      (mfderiv IC I3 (PartialDiffeomorph.toOpensDiffeo nk.map nk.domain) w v)
      (mfderiv IC I3 (PartialDiffeomorph.toOpensDiffeo nk.map nk.domain) w v') = _
    rw [PartialDiffeomorph.mfderiv_toOpensDiffeo,
      PartialDiffeomorph.mfderiv_toOpensDiffeo]
  have horder : 2 ≤ ⌈eps⁻¹⌉₊ := by
    have hi : (2 : ℝ) ≤ eps⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) nk.eps_pos]
      linarith [nk.eps_small]
    exact_mod_cast hi.trans (Nat.le_ceil eps⁻¹)
  have hjet (j : ℕ) (hj : j ≤ 2) :
      metricDerivNorm j G ((nk.cylinder.metric s).restrictOpen O)
        ((nk.cylinder.metric s).restrictOpen O) z ≤ eps := by
    rw [nk.comparison.metricDerivNorm_of_local_metric O subset_rfl s G hG j z]
    exact nk.comparison.close j 0 (by simpa using hj.trans horder) s hs y hy
  have hpert := sqrt_normSq_metricRm04At_le_of_metricDerivNorm_le
    ((nk.cylinder.metric s).restrictOpen O) G z (delta := eps)
      (by linarith [nk.eps_small]) hjet
  have href : Real.sqrt (normSq0S ((nk.cylinder.metric s).restrictOpen O) z 4
      (metricRm04At ((nk.cylinder.metric s).restrictOpen O) z)) ≤ 1 := by
    rw [rmNormSq_restrictOpen_CXCC,
      nk.cylinder.metric_eq_cylinderReferenceMetric hs.2]
    exact (Real.sqrt_le_sqrt (cylinder_rmNormSq_le_one_CXSP hs.2 y)).trans_eq
      Real.sqrt_one
  have hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) : ℝ) = 3 := by simp
  rw [hdim] at hpert
  have hbound : Real.sqrt (normSq0S G z 4 (metricRm04At G z)) ≤ 1200 := by
    have heps := nk.eps_pos
    have hsmall := nk.eps_small
    have hprod := mul_le_mul_of_nonneg_left href nk.eps_pos.le
    have hn := Real.sqrt_nonneg
      (normSq0S ((nk.cylinder.metric s).restrictOpen O) z 4
        (metricRm04At ((nk.cylinder.metric s).restrictOpen O) z))
    nlinarith
  dsimp only [G] at hbound
  rw [rmNormSq_scaleMetric_CXCC, riemannNormSq_cross,
    rmNormSq_restrictOpen_CXCC] at hbound
  change Real.sqrt (Q⁻¹ ^ 2 * normSq0S (S.base.metric (t + s / Q)) (nk.map y) 4
    (metricRm04At (S.base.metric (t + s / Q)) (nk.map y))) ≤ 1200 at hbound
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.mpr nk.Q_pos.le),
    inv_mul_le_iff₀ nk.Q_pos] at hbound
  have hn := normSq0S_nonneg (S.base.metric (t + s / Q)) (nk.map y) 4
    (metricRm04At (S.base.metric (t + s / Q)) (nk.map y))
  have hsqrt := Real.sq_sqrt hn
  have hnonneg := Real.sqrt_nonneg
    (normSq0S (S.base.metric (t + s / Q)) (nk.map y) 4
      (metricRm04At (S.base.metric (t + s / Q)) (nk.map y)))
  have hQ := nk.Q_pos
  nlinarith

private theorem spatialNeck_metric_cast_map_CXSP
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    {g g' : SmoothRiemannianMetric I3 M} {eps : ℝ} {x : M} (h : g = g')
    (nk : SpatialNeck g eps x) : (h ▸ nk : SpatialNeck g' eps x).map = nk.map := by
  cases h
  rfl

private theorem trace_normSq_eq_of_stage_eq_CXSP {H : ObservedHistory.{u}}
    {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {x : (H.stage last).Carrier}
    (A : BackwardPointTrace H first last hle x) {j k : Fin (H.eventCount + 1)}
    (hjk : j = k) (hj : first ≤ j) (hjl : j ≤ last) (hk : first ≤ k) (hkl : k ≤ last)
    (v : ℝ) :
    normSq0S (H.stageMetric j v) (A.point j hj hjl) 4
        (metricRm04At (H.stageMetric j v) (A.point j hj hjl)) =
      normSq0S (H.stageMetric k v) (A.point k hk hkl) 4
        (metricRm04At (H.stageMetric k v) (A.point k hk hkl)) := by
  subst hjk
  rfl

/-- S16's full-window branch gives a genuine original-history canonical-scale traced ball. -/
theorem native_strong_branch_traced_CXSP
    (H : ObservedHistory.{u}) {eps : ℝ}
    {y : (H.stage (Fin.last H.eventCount)).Carrier}
    (hQ : 0 < metricScalarAt (H.stageMetric (Fin.last H.eventCount) H.horizon) y)
    (U : TopologicalSpace.Opens (H.stage (Fin.last H.eventCount)).Carrier) (hyU : y ∈ U)
    (a : Icc (0 : ℝ) H.horizon)
    (E : RegularOpenBackwardTrace_C11E H (H.activeStage a) U)
    (S : SolutionOn (I := ThreeModel) (M := U)
      (RealTimeInterval.closed
        (H.horizon - (metricScalarAt (H.stageMetric (Fin.last H.eventCount) H.horizon) y)⁻¹)
        H.horizon (sub_le_self _ (inv_nonneg.mpr hQ.le))))
    (ha : (a : ℝ) = H.horizon -
      (metricScalarAt (H.stageMetric (Fin.last H.eventCount) H.horizon) y)⁻¹)
    (hwindow : ∀ v : Icc (0 : ℝ) H.horizon, ∀ hav : a ≤ v,
      S.base.metric v = localPullMetric (H.stageMetric (H.activeStage v) v)
        (E.atStage (H.activeStage v) (H.activeStage_mono hav) (Fin.le_last _))
        (E.atStage_isLocalDiffeomorph _ _ _))
    (htop : S.base.metric H.horizon =
      (H.stageMetric (Fin.last H.eventCount) H.horizon).restrictOpen U)
    (nk : StrongNeck S eps ⟨y, hyU⟩ H.horizon) :
    ∀ yt : (H.stageAt ⟨H.horizon, H.horizon_nonneg, le_rfl⟩).Carrier, HEq yt y →
      H.isTracedRegion ⟨H.horizon, H.horizon_nonneg, le_rfl⟩ yt
        (1 / (2 * Real.sqrt
          (metricScalarAt (H.stageMetric (Fin.last H.eventCount) H.horizon) y)))
        (metricScalarAt (H.stageMetric (Fin.last H.eventCount) H.horizon) y)⁻¹
        (1200 * metricScalarAt (H.stageMetric (Fin.last H.eventCount) H.horizon) y) := by
  let g := H.stageMetric (Fin.last H.eventCount) H.horizon
  let Q := metricScalarAt g y
  have hscalar : S.scalar H.horizon ⟨y, hyU⟩ = Q := by
    change metricScalarAt (S.base.metric H.horizon) ⟨y, hyU⟩ = Q
    rw [htop, metricScalarAt_restrictOpen]
  let ns : SpatialNeck (g.restrictOpen U) eps ⟨y, hyU⟩ := htop ▸ nk.toSpatialNeck
  have hnsmap (z : Cylinder) : ns.ofRestrictOpen.map z = (nk.map z).val := by
    rw [SpatialNeck.ofRestrictOpen_map]
    exact congrArg (fun m : PartialDiffeomorph IC I3 Cylinder U ∞ => (m z).val)
      (spatialNeck_metric_cast_map_CXSP htop nk.toSpatialNeck)
  have hinv : (1 : ℝ) < eps⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) nk.eps_pos]
    linarith [nk.eps_small]
  have hrad : 1 / (2 * Real.sqrt Q) ≤ Real.sqrt (1 - eps) / Real.sqrt Q := by
    have hroot := Real.sqrt_pos.mpr hQ
    have hs := Real.sq_sqrt (show 0 ≤ 1 - eps by linarith [nk.eps_small])
    have hn := Real.sqrt_nonneg (1 - eps)
    have hh : 1 / 2 ≤ Real.sqrt (1 - eps) := by nlinarith [nk.eps_small]
    calc 1 / (2 * Real.sqrt Q) = (1 / 2) / Real.sqrt Q := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hh hroot.le
  have hball : ∀ z ∈ riemannianBallOf g y (1 / (2 * Real.sqrt Q)),
      ∃ w ∈ (univ : Set (Sphere 2)) ×ˢ Icc (-1 : ℝ) 1, (nk.map w).val = z := by
    intro z hz
    have hz' := riemannianBallOf_mono g y hrad hz
    obtain ⟨w, hw, hwz⟩ := ns.ofRestrictOpen.ball_subset_image_slab
      (by norm_num : (0 : ℝ) < 1) hinv (by simpa using hz')
    exact ⟨w, hw, (hnsmap w).symm.trans hwz⟩
  have htraced : ∀ (k : Fin (H.eventCount + 1))
      (hk : H.activeStage ⟨H.horizon, H.horizon_nonneg, le_rfl⟩ = k),
      ∀ yt : (H.stage k).Carrier, HEq yt y →
      ∀ z ∈ riemannianBallOf (H.stageMetric k H.horizon) yt (1 / (2 * Real.sqrt Q)),
      ∃ B : BackwardPointTrace H (H.activeStage a) k
          ((H.activeStage_mono (show a ≤ ⟨H.horizon, H.horizon_nonneg, le_rfl⟩ from
            a.property.2)).trans_eq hk) z,
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v)
          (hvt : v ≤ ⟨H.horizon, H.horizon_nonneg, le_rfl⟩),
          normSq0S (H.stageMetric (H.activeStage v) v)
              (B.point (H.activeStage v) (H.activeStage_mono hav)
                ((H.activeStage_mono hvt).trans_eq hk)) 4
            (metricRm04At (H.stageMetric (H.activeStage v) v)
              (B.point (H.activeStage v) (H.activeStage_mono hav)
                ((H.activeStage_mono hvt).trans_eq hk))) ≤ (1200 * Q) ^ 2) ∧
        ∀ (i : Fin H.eventCount) (hf : H.activeStage a ≤ i.castSucc) (hl : i.succ ≤ k),
          let x : (H.event i).incoming.terminalRegularOpen :=
            ⟨B.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl),
              (B.crossing i hf hl).mem_terminalRegularRegion (H.event i)⟩
          normSq0S (H.event i).terminal.metric x 4
            (metricRm04At (H.event i).terminal.metric x) ≤ (1200 * Q) ^ 2 := by
    intro k hk
    have hk' : Fin.last H.eventCount = k := H.activeStage_at_horizon.symm.trans hk
    subst hk'
    intro yt hyt
    have hy : yt = y := eq_of_heq hyt
    subst yt
    intro z hz
    obtain ⟨w, hw, hwz⟩ := hball z hz
    have hzU : z ∈ U := hwz ▸ (nk.map w).property
    let zU : U := ⟨z, hzU⟩
    let B := Classical.choice (E.survive z hzU)
    have hwdom : w ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
      exact ⟨hw.1, by linarith [hw.2.1], by linarith [hw.2.2]⟩
    have hwu : nk.map w = zU := Subtype.ext hwz
    have hall (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v)
        (hvt : v ≤ ⟨H.horizon, H.horizon_nonneg, le_rfl⟩) :
        normSq0S (H.stageMetric (H.activeStage v) v)
            (B.point (H.activeStage v) (H.activeStage_mono hav) (Fin.le_last _)) 4
          (metricRm04At (H.stageMetric (H.activeStage v) v)
            (B.point (H.activeStage v) (H.activeStage_mono hav) (Fin.le_last _))) ≤
          (1200 * Q) ^ 2 := by
      have hav' : H.horizon - Q⁻¹ ≤ (v : ℝ) := by
        rw [← ha]
        exact hav
      have hv' : (v : ℝ) ≤ H.horizon := hvt
      have hs : Q * ((v : ℝ) - H.horizon) ∈ Icc (-1 : ℝ) 0 := by
        constructor
        · have hi : Q * Q⁻¹ = 1 := mul_inv_cancel₀ hQ.ne'
          have hm := mul_le_mul_of_nonneg_left hav' hQ.le
          nlinarith
        · exact mul_nonpos_of_nonneg_of_nonpos hQ.le (sub_nonpos.mpr hv')
      have ht : H.horizon + Q * ((v : ℝ) - H.horizon) / Q = v := by
        rw [mul_div_cancel_left₀ _ (show Q ≠ 0 from hQ.ne')]
        ring
      have hn := strongNeck_rmNormSq_map_le_CXSP nk hs hwdom
      rw [hscalar, ht, hwu, hwindow v hav,
        normSq0S_metricRm04At_localPullMetric] at hn
      have hp : E.atStage (H.activeStage v) (H.activeStage_mono hav) (Fin.le_last _) zU =
          B.point (H.activeStage v) (H.activeStage_mono hav) (Fin.le_last _) := by
        rfl
      rwa [hp] at hn
    refine ⟨B, hall, ?_⟩
    intro i hf hl x
    have hi := (H.crossed_event_iff_mem_Ioc a
      ⟨H.horizon, H.horizon_nonneg, le_rfl⟩ i).mp ⟨hf, by
        simpa only [H.activeStage_at_horizon] using hl⟩
    let v : Icc (0 : ℝ) H.horizon :=
      ⟨H.time i.succ, H.time_nonneg _, H.time_le_horizon_at _⟩
    have hv : H.activeStage v = i.succ := H.activeStage_at_time i.succ
    have hav : a ≤ v := hi.1.le
    have hvt : v ≤ ⟨H.horizon, H.horizon_nonneg, le_rfl⟩ := hi.2
    have hb := hall v hav hvt
    rw [trace_normSq_eq_of_stage_eq_CXSP B hv (H.activeStage_mono hav)
      (Fin.le_last _) (hf.trans i.castSucc_lt_succ.le) hl] at hb
    rw [MetricCutCapEvent.RegularCrossing.rmNormSq_eq (H.event i) (p := x)
      (B.crossing i hf hl), H.event_output i, ← H.stageMetric_initial]
    exact hb
  intro yt hyt
  refine ⟨by positivity, inv_pos.mpr hQ, a, a.property.2, ha, ?_⟩
  exact htraced _ rfl yt hyt

/-- chain 实际供给同一 W；其 neck alternative 留给 minimizing-geodesic consumer 支付。 -/
theorem native_chosen_neck_traced_of_chain_CXSP
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} (S : PreparedSpatialChain pBase C P g)
    (F : GC.Interface.RawSurgery P g) (hTower : F.tower = S.tower) (q : CutoffParameters)
    (hdiag : ∀ t : ℝ, 0 ≤ t → q.neckRadius t = (chainDiagonal_C11A S).neckRadius t)
    {C1 C2 : ℝ} (hC1 : C1ceil_C11SC.{u} C ≤ C1) (hC2 : C2ceil_C11SC.{u} C ≤ C2) :
    ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ x : s.stage.Carrier, (q.neckRadius s.time ^ 2)⁻¹ < metricScalarAt s.metric x →
      ∃ W : SpatialCanonicalWitness s.metric C.epsilon C1 C2 x,
        W.capTubeHasNeckChart C.epsilon ∧
        ∀ nk, W.alternative = SpatialCanonicalAlternative.neck nk →
          ∀ xt : (s.history.stageAt
            ⟨s.time, s.positive.le, le_rfl⟩).Carrier, HEq xt x →
            s.history.isTracedRegion ⟨s.time, s.positive.le, le_rfl⟩ xt
              (1 / (2 * Real.sqrt (metricScalarAt s.metric x)))
              (metricScalarAt s.metric x)⁻¹ (1200 * metricScalarAt s.metric x) := by
  obtain ⟨T, hT⟩ := strongCanonicalSupplyV2_mono_C12X
    (strongCanonicalSupplyV2_ceiling_C11SC S F hTower q hdiag) hC1 hC2
  refine ⟨T, fun s hs x hR => ?_⟩
  obtain ⟨W, hW, hn⟩ := hT s hs x hR
  refine ⟨W, hW, fun nk hnk => ?_⟩
  obtain ⟨U, hxU, a, E, flow, ha, -, hwindow, htop, ⟨strong⟩⟩ := hn nk hnk
  exact native_strong_branch_traced_CXSP s.history
    (lt_of_le_of_lt (inv_nonneg.mpr (sq_nonneg _)) hR)
    U hxU a E flow ha hwindow htop strong

end GC.LongTime.Ch11

end
