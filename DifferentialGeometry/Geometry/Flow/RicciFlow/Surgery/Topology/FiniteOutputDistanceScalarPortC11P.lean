import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventDistanceScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapPhysicalScalarGlue
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventSurvivorMap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CanonicalCapChart
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteFullWitnessMap
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapExhaustiveness
import DifferentialGeometry.Topology.Manifold.ImmersionImageNhds
import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphCurves
import DifferentialGeometry.Geometry.Metric.CurveVariation.Distance
import DifferentialGeometry.Geometry.Metric.Distance.Neighborhood
import DifferentialGeometry.Geometry.Metric.Euclidean

/-!
# S-CH11-FIX7 port of astra `FiniteOutputDistanceScalar`（`PortC11P`）

来源：donor `FiniteOutputDistanceScalar.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树有若干 elaboration error（`CapPhysicalScalarGlue` 落地后暴露）；本 port 只做
elaboration 层面修补（no statement / definition / proof idea altered）：
* namespace 开头加 `attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace` 与 file-local `Nonempty (Sphere 2)` 实例（同
  `NeckAnnulusControl` / `CapSeamScalarGlue` 的 port；本树里这两个 Tensor0S 实例是全局的，抢在
  Riemannian bundle 实例前面，`InnerProductSpace ℝ (TangentSpace ThreeModel x)` 综合失败）。
* `hsource ▸ …`（`hmetric` 的实参与 `hxW`）：`▸` 的目标是 `Opens` 成员，找不到等式两端，
  改 `by rw [hsource] at …; exact …`。`hUclosed`：`fun _ hy => hy.le` 改成带 `show` 的 `.le`。
* 若干 `simpa only [...] using X`（`htrunc` / `hinv` / `hret` / `hwin` / `hvalue` 收尾 /
  `hcenter` / 最后的 `h`）：simp 之后类型只差 let / `Sum.rec` / `Carrier` 展开，改成
  `have h := X; simp only [...] at h; exact h`。`windowMap_eq_capChart` 的 `rw` 改
  `rw [show … from …]`；`mul_le_mul_right'` 改 `mul_le_mul' … le_rfl`；`hxwindow` 的 `linarith`
  先把 `x.property` 落成原子形；`hclosedWindow` 里 `let := radialCapAttachmentChartedSpace …`
  （`finiteCapFullInsertionDiffeomorph_symm_cap` 要求）。
* 全局化的最后一步里 `U : Opens Ret` 写成 `(U : Set ↥Ret)`。
* heartbeat（donor 主定理 `exists_uniform_finite_output_distance_scalar` 约 240 行，单声明
  1.4M heartbeat > 200000；不加 `set_option`，拆声明）：把证明按块抽成五个 `private theorem`，
  主定理陈述不变、证明变成这些块的组合：
  `fods_closed_window`（`hclosedWindow`）、`fods_boundary_scalar`（`hboundary` + 商上的标量
  `Gfull`）、`fods_collar_value`（`hGcollar`，对一般 `E` 陈述）、`fods_local_patch`（`hGloc`
  的 cap 一支，对一般 `E` 陈述）、`fods_global_of_local`（最后的 Riemannian 距离全局化）。
  证明体逐行取自 donor，只有：`rw [hw]`（motive 太大，单步 840k heartbeat）换成
  `congrArg (fun y => …) hw`；`obtain … := <term>` 换成 `have h := <term>; obtain … := h`
  （单步 163k → 6k）。`[Fintype ι]` 在 helper 陈述里写成 `[Finite ι]`（只在证明里用到，
  `unusedFintypeInType`）；helper 里的 `letI` 写成 `let`（haveILetI）。
原路径 `FiniteOutputDistanceScalar` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section

open Set Bundle Filter Function Manifold TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Topology.Manifold.Attachment
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

private local instance : Nonempty (Sphere 2) :=
  (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype

private theorem local_distance_scalar_bound_on_old_interior
    {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s)
    (p : E.incoming.terminalRegularOpen) (N : ℝ≥0) (G : Q.Carrier → ℝ)
    (hG : ∀ z : E.old, G (E.oldOutput z) =
      (min (riemannianEDistOf E.terminal.metric (E.oldTerminal z) p)
        (N : ℝ≥0∞)).toReal)
    (q : Q.Carrier) (hq : q ∈ interior (range E.oldOutput)) :
    ∃ U : TopologicalSpace.Opens Q.Carrier, q ∈ U ∧
      ∀ y ∈ U, ∀ z ∈ U,
        edist (G y) (G z) ≤ riemannianEDistOf E.outputMetric y z := by
  letI : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
  letI : IsManifold (𝓡∂ 3) ∞ E.old := E.oldSmooth
  obtain ⟨_, z, hzint, _, hzq⟩ :=
    E.exists_terminal_regularCrossing_of_mem_interior_oldOutput q hq
  have hnhds : Subtype.val '' E.old ∈ 𝓝 z.val.val := by
    have h := DifferentialGeometry.Topology.immersion_image_mem_nhds
      (E.old_induced.isImmersion.isImmersionAt z) rfl hzint
      (s := (univ : Set E.old)) Filter.univ_mem
    have hr : range (fun w : E.old => w.val.val) = Subtype.val '' E.old := by
      ext x
      constructor
      · rintro ⟨w, rfl⟩
        exact ⟨w.val, w.property, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨⟨w, hw⟩, rfl⟩
    simpa only [image_univ, hr] using h
  let W : Opens E.incoming.terminalRegularOpen :=
    ⟨Subtype.val ⁻¹' interior (Subtype.val '' E.old),
      isOpen_interior.preimage continuous_subtype_val⟩
  have hzW : E.oldTerminal z ∈ W := by
    change (E.oldTerminal z).val ∈ interior (Subtype.val '' E.old)
    rw [E.oldTerminal_eq]
    exact mem_interior_iff_mem_nhds.mpr hnhds
  have hW (x : E.incoming.terminalRegularOpen) (hx : x ∈ W) :
      x.val ∈ interior (Subtype.val '' E.old) := hx
  obtain ⟨F, hsource, _, hFold, hmetric⟩ :=
    E.exists_survivor_partialDiffeomorph W ⟨E.oldTerminal z, hzW⟩ hW
  have hFz : F (E.oldTerminal z) = q := (hFold z hzW).trans hzq
  have hqtarget : q ∈ F.target := hFz ▸ F.map_source' (hsource.symm ▸ hzW)
  have hinverse : ∀ y ∈ F.target, ∀ v : TangentSpace ThreeModel y,
      E.terminal.metric.inner (F.symm y)
        (mfderiv ThreeModel ThreeModel (F.symm : Q.Carrier → _) y v)
        (mfderiv ThreeModel ThreeModel (F.symm : Q.Carrier → _) y v) ≤
          (1 : ℝ) ^ 2 * E.outputMetric.inner y v v := by
    have h := DifferentialGeometry.PartialDiffeomorph.metric_upper_symm_of_metric_lower
      F E.terminal.metric E.outputMetric (V := F.source) (L := 1) subset_rfl
      (fun x hx v => by
        simpa only [one_pow, one_mul] using
          (hmetric x (by rw [hsource] at hx; exact hx) v v).symm.le)
    intro y hy v
    exact h y ⟨F.symm y, F.map_target' hy, F.right_inv' hy⟩ v
  obtain ⟨ρ, hρ, hball⟩ := exists_riemannianBallOf_subset_of_mem_nhds
    E.outputMetric q (F.open_target.mem_nhds hqtarget)
  have hclosed : riemannianClosedBallOf E.outputMetric q (ρ / 2) ⊆ F.target := by
    intro y hy
    exact hball (hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hρ).mpr (by linarith)))
  letI : RiemannianBundle (TangentSpace ThreeModel : Q.Carrier → Type _) :=
    ⟨E.outputMetric.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle ThreeSpace
      (TangentSpace ThreeModel : Q.Carrier → Type _) :=
    ⟨E.outputMetric.inner, E.outputMetric.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : PseudoEMetricSpace Q.Carrier := .ofRiemannianMetric ThreeModel Q.Carrier
  let U : Opens Q.Carrier :=
    ⟨riemannianBallOf E.outputMetric q (ρ / 8),
      isOpen_lt (continuous_const.edist continuous_id) continuous_const⟩
  have hUclosed : (U : Set Q.Carrier) ⊆
      riemannianClosedBallOf E.outputMetric q (ρ / 8) := fun y hy =>
    (show riemannianEDistOf E.outputMetric q y < ENNReal.ofReal (ρ / 8) from hy).le
  have hUtarget : (U : Set Q.Carrier) ⊆ F.target := by
    intro y hy
    exact hclosed ((hUclosed hy).trans (ENNReal.ofReal_le_ofReal (by linarith)))
  have hvalues (y : Q.Carrier) (hy : y ∈ U) :
      G y = (min (riemannianEDistOf E.terminal.metric (F.symm y) p)
        (N : ℝ≥0∞)).toReal := by
    have hxW : F.symm y ∈ W := by
      have h := F.map_target' (hUtarget hy)
      rw [hsource] at h
      exact h
    obtain ⟨w, hw, _, _⟩ := E.exists_oldTerminal_eq_of_mem_interior_old
      (F.symm y) (hW _ hxW)
    have hwout : E.oldOutput w = y := by
      rw [← hFold w (hw.symm ▸ hxW), hw]
      exact F.right_inv' (hUtarget hy)
    calc
      G y = G (E.oldOutput w) := congrArg G hwout.symm
      _ = _ := hG w
      _ = _ := by rw [hw]
  refine ⟨U, ?_, ?_⟩
  · change riemannianEDistOf E.outputMetric q q < ENNReal.ofReal (ρ / 8)
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  · intro y hy z hz
    rw [hvalues y hy, hvalues z hz]
    letI : RiemannianBundle
        (TangentSpace ThreeModel : E.incoming.terminalRegularOpen → Type _) :=
      ⟨E.terminal.metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle ThreeSpace
        (TangentSpace ThreeModel : E.incoming.terminalRegularOpen → Type _) :=
      ⟨E.terminal.metric.inner, E.terminal.metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : PseudoEMetricSpace E.incoming.terminalRegularOpen :=
      .ofRiemannianMetric ThreeModel E.incoming.terminalRegularOpen
    have htrunc := EMetric.lipschitzWith_truncated_edist_level p N (F.symm y) (F.symm z)
    have hinv := Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_buffered_ball
      E.outputMetric E.terminal.metric F.symm q y z
      (by linarith : 0 ≤ ρ / 8) (by linarith : 3 * (ρ / 8) < ρ / 2)
      (by norm_num : (0 : ℝ) < 1) hclosed
      (fun x hx => hinverse x (hclosed hx)) (hUclosed hy) (hUclosed hz)
    exact (show edist
      ((min (riemannianEDistOf E.terminal.metric (F.symm y) p) (N : ℝ≥0∞)).toReal)
      ((min (riemannianEDistOf E.terminal.metric (F.symm z) p) (N : ℝ≥0∞)).toReal) ≤
        riemannianEDistOf E.terminal.metric (F.symm y) (F.symm z) by
          simp only [ENNReal.coe_one, one_mul] at htrunc
          exact htrunc).trans
      (by
        simp only [ENNReal.ofReal_one, one_mul] at hinv
        exact hinv)

/-- Descent along the literal generating relation; the actual scalar data and
boundary agreement are supplied by the finite construction below. -/
private theorem exists_scalar_on_finite_quotient
    {ι M : Type*} {precision : ι → ℝ} {L : ℝ}
    (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, Injective (f i))
    (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
    (v : cutCore f → ℝ) (w : IndexedCaps ι L → ℝ)
    (hboundary : ∀ x : CuttingSpheres ι,
      w (indexedCapBoundary hL x) = v (cuttingSphereAttachment hδ f hf hdisj x)) :
    ∃ G : FiniteCapQuotient hL hδ f hf hdisj → ℝ,
      (∀ x, G (finiteCoreInclusion hL hδ f hf hdisj x) = v x) ∧
      ∀ x, G (finiteCapInclusion hL hδ f hf hdisj x) = w x := by
  let raw : IndexedCaps ι L ⊕ cutCore f → ℝ := Sum.elim w v
  have hrel : ∀ a b,
      adjunctionRel (indexedCapBoundary hL) (cuttingSphereAttachment hδ f hf hdisj) a b →
        raw a = raw b := by
    rintro a b ⟨x, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact hboundary x
    · exact (hboundary x).symm
  exact ⟨Quot.lift raw hrel, fun _ => rfl, fun _ => rfl⟩

private theorem real_edistOf_euclidean (x y : ℝ) :
    riemannianEDistOf (I := 𝓘(ℝ, ℝ))
      (DifferentialGeometry.euclideanMetric (E := ℝ)) x y = edist x y :=
  (IsRiemannianManifold.out (I := 𝓘(ℝ, ℝ)) x y).symm

/-- The closed part of a presented cap window is the literal finite-cap point. -/
private theorem fods_closed_window :
    ∀ (P : OrientedThreeStage.{u}) {ι : Type} [Finite ι] {precision : ι → ℝ}
      (hδ : ∀ j, 0 < precision j)
      (f : ∀ j : ι, bufferedCylinder (precision j) → P.Carrier)
      (hf : ∀ j, _root_.Topology.IsOpenEmbedding (f j))
      (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
      (hs : ∀ j, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (f j))
      (R : Set (ConnectedComponents (cutCore f))) (c : ℝ) (hc : 4 ≤ c),
    letI : LocallyPathConnectedSpace P.Carrier :=
      originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
    let Qcap := FiniteCapQuotient StandardCap.transitionEnd_pos hδ f
      (fun j => (hf j).injective) hdisj
    let Ret := finiteCapRetained StandardCap.transitionEnd_pos hδ f hf hdisj R
    let Bidx := {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
    letI : ChartedSpace ThreeSpace Qcap := finiteCapChartedSpace ThreeModel
      finrank_threeSpace_eq_three StandardCap.transitionEnd_pos hδ f hf hdisj
    letI : IsManifold ThreeModel ∞ Qcap := finiteCapQuotient_isManifold
      finrank_threeSpace_eq_three StandardCap.transitionEnd_pos hδ f hf hdisj hs
    letI : T2Space Qcap := finiteCapQuotient_t2Space
      StandardCap.transitionEnd_pos hδ f hf hdisj
    letI : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace
      StandardCap.transitionEnd_pos hδ f hf hdisj R).1
    ∀ (oRet : SmoothOrientation ThreeModel Ret) {a s : ℝ}
      (E : MetricCutCapEvent P (OrientedThreeStage.ofSmoothOrientation Ret oRet) a s)
      {fixed : StaticCapScaffold} {D η : ℝ} {m : ℕ}
      (S : ∀ b : E.RetainedBoundaryIndex, E.PresentedStaticCap fixed D m η b),
    ∀ (xB : Bidx → E.incoming.terminalRegularOpen) (kB : Bidx → ℕ)
      (d : ∀ b : Bidx, normalizedDatum E.terminal.metric (xB b)
        (c * precision b.val.1) (kB b))
      (w : ∀ b : Bidx, StandardCap.CanonicalStaticInsertionWitness (d b)
        fixed.collarLength fixed.collar_pos D m η)
      (eB : E.RetainedBoundaryIndex ≃ Bidx),
    (∀ (b : E.RetainedBoundaryIndex) (x : standardCapWindow D),
      (S b).window x = finiteFullWitnessMap ThreeModel finrank_threeSpace_eq_three
        StandardCap.transitionEnd_pos hδ f hf hdisj hs R c hc (eB b) ((w (eB b)).window x)) →
    ∀ (b : E.RetainedBoundaryIndex) (x : standardCapWindow D) (hx : ‖x.val‖ ≤ standardCapL),
      (S b).window x = (⟨finiteCapInclusion StandardCap.transitionEnd_pos hδ f
        (fun j => (hf j).injective) hdisj ⟨(eB b).val, ⟨x.val, hx⟩⟩, (eB b).property⟩ : Ret) := by
  intro P ι _ precision hδ f hf hdisj hs R c hc
  let : LocallyPathConnectedSpace P.Carrier :=
    originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
  let Qcap := FiniteCapQuotient StandardCap.transitionEnd_pos hδ f
    (fun j => (hf j).injective) hdisj
  let Ret := finiteCapRetained StandardCap.transitionEnd_pos hδ f hf hdisj R
  let Bidx := {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
  let : ChartedSpace ThreeSpace Qcap := finiteCapChartedSpace ThreeModel
    finrank_threeSpace_eq_three StandardCap.transitionEnd_pos hδ f hf hdisj
  let : IsManifold ThreeModel ∞ Qcap := finiteCapQuotient_isManifold
    finrank_threeSpace_eq_three StandardCap.transitionEnd_pos hδ f hf hdisj hs
  let : T2Space Qcap := finiteCapQuotient_t2Space
    StandardCap.transitionEnd_pos hδ f hf hdisj
  let : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace
    StandardCap.transitionEnd_pos hδ f hf hdisj R).1
  dsimp only
  intro oRet a s E fixed D η m S xB kB d w eB hwindow b x hx
  classical
  have hxcore : x.val ∈ standardCapClosedCore := by
    simpa only [standardCapClosedCore, Metric.mem_closedBall, dist_zero_right] using hx
  have hw : (w (eB b)).window x =
      adjunctionCell (radialCapBoundary StandardCap.transitionEnd_pos)
        (retainedBoundary (inv_pos.mpr (d (eB b)).precision_pos)) ⟨x.val, hx⟩ := by
    change (w (eB b)).data.windowMap x = _
    rw [show (w (eB b)).data.windowMap x = _ from
      (w (eB b)).windowMap_eq_capChart x.val x.property hxcore]
    change (w (eB b)).data.capMap (standardCapCoreHomeomorph ⟨x.val, hxcore⟩) = _
    rw [(w (eB b)).properties.capMap_eq, (w (eB b)).properties.capInclusion_eq]
    rfl
  rw [hwindow b x]
  apply Subtype.ext
  let := radialCapAttachmentChartedSpace StandardCap.transitionEnd_pos
    (preparedFullCapWidth_bounds c (precision (eB b).val.1) hc (hδ (eB b).val.1)).1
  change ((finiteCapFullInsertionDiffeomorph ThreeModel finrank_threeSpace_eq_three
    StandardCap.transitionEnd_pos hδ f hf hdisj hs (eB b).val
    (preparedFullCapWidth_bounds c (precision (eB b).val.1) hc (hδ (eB b).val.1)).2.le
    (preparedFullCapWidth_bounds c (precision (eB b).val.1) hc (hδ (eB b).val.1)).1).symm
      ((w (eB b)).window x)).val = _
  have key := finiteCapFullInsertionDiffeomorph_symm_cap ThreeModel
    finrank_threeSpace_eq_three StandardCap.transitionEnd_pos hδ f hf hdisj hs (eB b).val
    (preparedFullCapWidth_bounds c (precision (eB b).val.1) hc (hδ (eB b).val.1)).2.le
    (preparedFullCapWidth_bounds c (precision (eB b).val.1) hc (hδ (eB b).val.1)).1
    ⟨x.val, hx⟩
  have key2 := congrArg Subtype.val key
  refine Eq.trans ?_ key2
  exact congrArg (fun y => ((finiteCapFullInsertionDiffeomorph ThreeModel
    finrank_threeSpace_eq_three StandardCap.transitionEnd_pos hδ f hf hdisj hs (eB b).val
    (preparedFullCapWidth_bounds c (precision (eB b).val.1) hc (hδ (eB b).val.1)).2.le
    (preparedFullCapWidth_bounds c (precision (eB b).val.1) hc (hδ (eB b).val.1)).1).symm y).val)
    hw

/-- Outside the closed core, on the seam ball, a scalar already equal to the old distance on the
old part takes the prescribed physical value. -/
private theorem fods_collar_value
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
    {fixed : StaticCapScaffold} {D η : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
    (S : E.PresentedStaticCap fixed D m η b) (hOld : E.old = E.transition.trace.retainedCore)
    (p : E.incoming.terminalRegularOpen) (N : ℝ≥0) (G : Q.Carrier → ℝ) (φ : ThreeSpace → ℝ)
    (hGold : ∀ z : E.old, G (E.oldOutput z) =
      (min (riemannianEDistOf E.terminal.metric (E.oldTerminal z) p) (N : ℝ≥0∞)).toReal)
    (hretained : ∀ (x : neckRetainedCollar S.delta)
      (hx : (standardCapL + x.val.2) • (x.val.1 : ThreeSpace) ∈ standardCapWindow D),
      (standardCapL + x.val.2) • (x.val.1 : ThreeSpace) ∈ capSeamOpen →
      S.inclusion (S.witness.window
        ⟨(standardCapL + x.val.2) • (x.val.1 : ThreeSpace), hx⟩) =
          E.oldOutput (S.collarOldPoint hOld x) ∧
      φ ((standardCapL + x.val.2) • (x.val.1 : ThreeSpace)) =
        (min (riemannianEDistOf E.terminal.metric
          (E.oldTerminal (S.collarOldPoint hOld x)) p) (N : ℝ≥0∞)).toReal)
    (x₀ x : standardCapWindow D)
    (hx₀ : ‖x₀.val‖ ≤ standardCapL) (hx : x.val ∈ Metric.ball x₀.val capSeamWidth)
    (hout : standardCapL < ‖x.val‖) : G (S.window x) = φ x.val := by
  have hL : 0 < standardCapL := StandardCap.transitionEnd_pos
  have hnorm : ‖x.val‖ < standardCapL + capSeamWidth := by
    have hdist := Metric.mem_ball.mp hx
    have htri := norm_le_norm_add_norm_sub' x.val x₀.val
    rw [← dist_eq_norm] at htri
    linarith
  have hinv : 1 < S.delta⁻¹ :=
    (one_lt_inv₀ S.neck.delta_pos).mpr S.neck.delta_lt_one
  let z : neckRetainedCollar S.delta := ⟨capRadialCoordinates x.val, by
    change 0 ≤ ‖x.val‖ - standardCapL ∧ ‖x.val‖ - standardCapL < S.delta⁻¹
    constructor <;> linarith [capSeamWidth_le_one]⟩
  have hz : (standardCapL + z.val.2) • (z.val.1 : ThreeSpace) = x.val := by
    change (standardCapL + (‖x.val‖ - standardCapL)) •
      (sphereDirection (Classical.choice (inferInstance : Nonempty (Sphere 2))) x.val :
        ThreeSpace) = x.val
    rw [show standardCapL + (‖x.val‖ - standardCapL) = ‖x.val‖ by ring]
    exact norm_smul_sphereDirection _ (norm_pos_iff.mp (hL.trans hout))
  have hzwindow : (standardCapL + z.val.2) • (z.val.1 : ThreeSpace) ∈
      standardCapWindow D := hz.symm ▸ x.property
  have hznear : (standardCapL + z.val.2) • (z.val.1 : ThreeSpace) ∈ capSeamOpen := by
    rw [hz]
    change |‖x.val‖ - standardCapL| < 2 * capSeamWidth
    rw [abs_of_pos (sub_pos.mpr hout)]
    linarith [capSeamWidth_pos]
  obtain ⟨hpoint, hvalue⟩ := hretained z hzwindow hznear
  have hxw : (⟨(standardCapL + z.val.2) • (z.val.1 : ThreeSpace), hzwindow⟩ :
      standardCapWindow D) = x := Subtype.ext hz
  change S.window _ = _ at hpoint
  rw [hxw] at hpoint
  rw [hz] at hvalue
  rw [hpoint, hGold, hvalue]

/-- One cap chart: a scalar that agrees with the Lipschitz chart value on the seam ball is
locally `C`-Lipschitz at the chart centre. -/
private theorem fods_local_patch
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
    {fixed : StaticCapScaffold} {D η : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
    (S : E.PresentedStaticCap fixed D m η b) (C : ℝ≥0) (G : Q.Carrier → ℝ)
    (φ : ThreeSpace → ℝ) (x₀ : standardCapWindow D)
    (hlocal : ∃ (U : TopologicalSpace.Opens Q.Carrier) (Ψ : Q.Carrier → ℝ),
      S.window x₀ ∈ U ∧
      (∀ y ∈ U, ∀ z ∈ U,
        edist (Ψ y) (Ψ z) ≤ (C : ℝ≥0∞) * riemannianEDistOf E.outputMetric y z) ∧
      (∀ x : standardCapWindow D, S.window x ∈ U → Ψ (S.window x) = φ x.val) ∧
      (U : Set Q.Carrier) ⊆
        S.window '' {x : standardCapWindow D | x.val ∈ Metric.ball x₀.val capSeamWidth})
    (hGeq : ∀ x : standardCapWindow D, x.val ∈ Metric.ball x₀.val capSeamWidth →
      G (S.window x) = φ x.val) :
    ∃ U : TopologicalSpace.Opens Q.Carrier, S.window x₀ ∈ U ∧ ∀ y ∈ U, ∀ z ∈ U,
      edist (G y) (G z) ≤ (C : ℝ≥0∞) * riemannianEDistOf E.outputMetric y z := by
  obtain ⟨U, Ψ, hxU, hΨ, hpullback, hsubset⟩ := hlocal
  have hequal (y : Q.Carrier) (hy : y ∈ U) : G y = Ψ y := by
    obtain ⟨x, hxball, hxy⟩ := hsubset hy
    rw [← hxy, hpullback x (hxy.symm ▸ hy)]
    exact hGeq x hxball
  refine ⟨U, hxU, ?_⟩
  intro y hy z hz
  rw [hequal y hy, hequal z hz]
  exact hΨ y hy z hz

/-- Local `C`-Lipschitz control of a real scalar along the Riemannian distance globalizes. -/
private theorem fods_global_of_local {Q : OrientedThreeStage.{u}} (g : Q.Metric)
    (G : Q.Carrier → ℝ) (C : ℝ≥0) (hC : 1 ≤ C)
    (hloc : ∀ q : Q.Carrier, ∃ U : TopologicalSpace.Opens Q.Carrier, q ∈ U ∧
      ∀ y ∈ U, ∀ z ∈ U, edist (G y) (G z) ≤ (C : ℝ≥0∞) * riemannianEDistOf g y z) :
    ∀ y z : Q.Carrier, edist (G y) (G z) ≤ (C : ℝ≥0∞) * riemannianEDistOf g y z := by
  have hCne : C ≠ 0 := (zero_lt_one.trans_le hC).ne'
  have hglobal := riemannianEDistOf_comp_le_of_local_riemannianCurveVariation_of_ne_zero
    g (DifferentialGeometry.euclideanMetric (E := ℝ)) G C hCne (by
      intro q
      obtain ⟨U, hqU, hU⟩ := hloc q
      refine ⟨(U : Set Q.Carrier), U.isOpen.mem_nhds hqU, ?_⟩
      intro a b γ _ _ hγ _
      have h := riemannianCurveVariation_comp_le_of_mapsTo g
        (DifferentialGeometry.euclideanMetric (E := ℝ)) G (U : Set Q.Carrier) (ell := (C : ℝ))
        (fun y hy z hz => by
          rw [real_edistOf_euclidean, ENNReal.ofReal_coe_nnreal]
          exact hU y hy z hz) γ a b hγ
      simp only [ENNReal.ofReal_coe_nnreal] at h
      exact h)
  intro y z
  simpa only [real_edistOf_euclidean] using hglobal y z

/-- The physical scalar descends to the finite cap quotient: it is the old distance on the
retained core and the selected extension on every closed cap. -/
private theorem fods_boundary_scalar :
    ∀ (P : OrientedThreeStage.{u}) {ι : Type} [Finite ι] {precision : ι → ℝ}
      (hδ : ∀ j, 0 < precision j)
      (f : ∀ j : ι, bufferedCylinder (precision j) → P.Carrier)
      (hf : ∀ j, _root_.Topology.IsOpenEmbedding (f j))
      (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
      (hs : ∀ j, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (f j))
      (R : Set (ConnectedComponents (cutCore f))),
    letI : LocallyPathConnectedSpace P.Carrier :=
      originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
    let Qcap := FiniteCapQuotient StandardCap.transitionEnd_pos hδ f
      (fun j => (hf j).injective) hdisj
    let Ret := finiteCapRetained StandardCap.transitionEnd_pos hδ f hf hdisj R
    let Bidx := {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
    letI : ChartedSpace ThreeSpace Qcap := finiteCapChartedSpace ThreeModel
      finrank_threeSpace_eq_three StandardCap.transitionEnd_pos hδ f hf hdisj
    letI : IsManifold ThreeModel ∞ Qcap := finiteCapQuotient_isManifold
      finrank_threeSpace_eq_three StandardCap.transitionEnd_pos hδ f hf hdisj hs
    letI : T2Space Qcap := finiteCapQuotient_t2Space
      StandardCap.transitionEnd_pos hδ f hf hdisj
    letI : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace
      StandardCap.transitionEnd_pos hδ f hf hdisj R).1
    ∀ (oRet : SmoothOrientation ThreeModel Ret) {a s : ℝ}
      (E : MetricCutCapEvent P (OrientedThreeStage.ofSmoothOrientation Ret oRet) a s)
      {fixed : StaticCapScaffold} {D η : ℝ} {m : ℕ}
      (S : ∀ b : E.RetainedBoundaryIndex, E.PresentedStaticCap fixed D m η b),
    (hOld : E.old = E.transition.trace.retainedCore) →
    standardCapL + 1 ≤ D →
    ∀ (eB : E.RetainedBoundaryIndex ≃ Bidx),
    range E.oldOutput = range (finiteRetainedCoreInclusion
      StandardCap.transitionEnd_pos hδ f hf hdisj R) →
    ∀ (p : E.incoming.terminalRegularOpen) (N : ℝ≥0)
      (fcap φ : E.RetainedBoundaryIndex → ThreeSpace → ℝ),
    (∀ b : E.RetainedBoundaryIndex, ∀ (x : ThreeSpace) (hx : x ∈ standardCapWindow D)
      (hcc : x ∈ standardCapClosedCore),
      (S b).inclusion ((S b).witness.window ⟨x, hx⟩) =
        (S b).inclusion ((S b).witness.capChart ⟨x, hcc⟩) ∧ φ b x = fcap b x) →
    (∀ b : E.RetainedBoundaryIndex, ∀ (x : neckRetainedCollar (S b).delta)
      (hx : (standardCapL + x.val.2) • (x.val.1 : ThreeSpace) ∈ standardCapWindow D),
      (standardCapL + x.val.2) • (x.val.1 : ThreeSpace) ∈ capSeamOpen →
      (S b).inclusion ((S b).witness.window
        ⟨(standardCapL + x.val.2) • (x.val.1 : ThreeSpace), hx⟩) =
          E.oldOutput ((S b).collarOldPoint hOld x) ∧
      φ b ((standardCapL + x.val.2) • (x.val.1 : ThreeSpace)) =
        (min (riemannianEDistOf E.terminal.metric
          (E.oldTerminal ((S b).collarOldPoint hOld x)) p) (N : ℝ≥0∞)).toReal) →
    (∀ (b : E.RetainedBoundaryIndex) (x : standardCapWindow D) (hx : ‖x.val‖ ≤ standardCapL),
      (S b).window x = (⟨finiteCapInclusion StandardCap.transitionEnd_pos hδ f
        (fun j => (hf j).injective) hdisj ⟨(eB b).val, ⟨x.val, hx⟩⟩, (eB b).property⟩ : Ret)) →
    ∃ Gfull : Qcap → ℝ,
      (∀ z : E.old, Gfull (show Ret from E.oldOutput z).val =
        (min (riemannianEDistOf E.terminal.metric (E.oldTerminal z) p)
          (N : ℝ≥0∞)).toReal) ∧
      ∀ (b : Bidx) (x : {v : ThreeSpace // ‖v‖ ≤ standardCapL}),
        Gfull (finiteCapInclusion StandardCap.transitionEnd_pos hδ f
          (fun j => (hf j).injective) hdisj ⟨b.val, x⟩) = fcap (eB.symm b) x.val := by
  intro P ι _ precision hδ f hf hdisj hs R
  let : LocallyPathConnectedSpace P.Carrier :=
    originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
  let Qcap := FiniteCapQuotient StandardCap.transitionEnd_pos hδ f
    (fun j => (hf j).injective) hdisj
  let Ret := finiteCapRetained StandardCap.transitionEnd_pos hδ f hf hdisj R
  let Bidx := {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
  let : ChartedSpace ThreeSpace Qcap := finiteCapChartedSpace ThreeModel
    finrank_threeSpace_eq_three StandardCap.transitionEnd_pos hδ f hf hdisj
  let : IsManifold ThreeModel ∞ Qcap := finiteCapQuotient_isManifold
    finrank_threeSpace_eq_three StandardCap.transitionEnd_pos hδ f hf hdisj hs
  let : T2Space Qcap := finiteCapQuotient_t2Space
    StandardCap.transitionEnd_pos hδ f hf hdisj
  let : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace
    StandardCap.transitionEnd_pos hδ f hf hdisj R).1
  dsimp only
  intro oRet a s E fixed D η m S hOld hD eB hOldRange p N fcap φ hinside hretained hcw
  classical
  have hL : 0 < standardCapL := StandardCap.transitionEnd_pos
  let capPoint (b : Bidx) (x : {v : ThreeSpace // ‖v‖ ≤ standardCapL}) : Ret :=
    ⟨finiteCapInclusion StandardCap.transitionEnd_pos hδ f
      (fun j => (hf j).injective) hdisj ⟨b.val, x⟩, b.property⟩
  have hclosedWindow (b : E.RetainedBoundaryIndex) (x : standardCapWindow D)
      (hx : ‖x.val‖ ≤ standardCapL) :
      (S b).window x = capPoint (eB b) ⟨x.val, hx⟩ := hcw b x hx
  let oldScalar : Ret → ℝ := Function.extend E.oldOutput
    (fun z => (min (riemannianEDistOf E.terminal.metric (E.oldTerminal z) p)
      (N : ℝ≥0∞)).toReal) (fun _ => 0)
  have holdScalar (z : E.old) : oldScalar (E.oldOutput z) =
      (min (riemannianEDistOf E.terminal.metric (E.oldTerminal z) p)
        (N : ℝ≥0∞)).toReal := E.oldOutput_injective.extend_apply _ _ z
  let coreValue (x : cutCore f) : ℝ :=
    if hx : finiteCoreInclusion StandardCap.transitionEnd_pos hδ f
        (fun j => (hf j).injective) hdisj x ∈ (Ret : Set Qcap) then
      oldScalar ⟨finiteCoreInclusion StandardCap.transitionEnd_pos hδ f
        (fun j => (hf j).injective) hdisj x, hx⟩ else 0
  let capValue (x : IndexedCaps ι standardCapL) : ℝ :=
    if hb : cuttingSphereComponent hδ f hf hdisj x.1 ∈ R then
      fcap (eB.symm ⟨x.1, hb⟩) x.2.val else 0
  have hboundary (x : CuttingSpheres ι) :
      capValue (indexedCapBoundary StandardCap.transitionEnd_pos x) =
        coreValue (cuttingSphereAttachment hδ f (fun j => (hf j).injective) hdisj x) := by
    rcases x with ⟨idx, y⟩
    have hmembership :
        finiteCoreInclusion StandardCap.transitionEnd_pos hδ f
          (fun j => (hf j).injective) hdisj
          (cuttingSphereAttachment hδ f (fun j => (hf j).injective) hdisj ⟨idx, y⟩)
          ∈ (Ret : Set Qcap) ↔ cuttingSphereComponent hδ f hf hdisj idx ∈ R := by
      change ConnectedComponents.mk
        (cuttingSphereAttachment hδ f (fun j => (hf j).injective) hdisj ⟨idx, y⟩) ∈ R ↔ _
      rw [cuttingSphere_component_eq hδ f hf hdisj idx y]
    by_cases hidx : cuttingSphereComponent hδ f hf hdisj idx ∈ R
    · have hmem := hmembership.mpr hidx
      let b : E.RetainedBoundaryIndex := eB.symm ⟨idx, hidx⟩
      have hnorm : ‖standardCapL • (y : ThreeSpace)‖ = standardCapL := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL, norm_eq_of_mem_sphere, mul_one]
      have hxwindow : standardCapL • (y : ThreeSpace) ∈ standardCapWindow D := by
        change ‖standardCapL • (y : ThreeSpace)‖ < D + 1
        rw [hnorm]
        linarith
      let xw : standardCapWindow D := ⟨standardCapL • (y : ThreeSpace), hxwindow⟩
      have hxcore : xw.val ∈ standardCapClosedCore := by
        simpa only [standardCapClosedCore, Metric.mem_closedBall, dist_zero_right]
          using hnorm.le
      let z₀ : neckRetainedCollar (S b).delta :=
        ⟨(y, 0), le_rfl, inv_pos.mpr (S b).neck.delta_pos⟩
      have hzwindow : (standardCapL + z₀.val.2) • (z₀.val.1 : ThreeSpace) ∈
          standardCapWindow D := by simpa only [z₀, add_zero] using hxwindow
      have hznear : (standardCapL + z₀.val.2) • (z₀.val.1 : ThreeSpace) ∈ capSeamOpen := by
        change |‖(standardCapL + 0) • (y : ThreeSpace)‖ - standardCapL| < 2 * capSeamWidth
        rw [add_zero, hnorm, sub_self, abs_zero]
        exact mul_pos (by norm_num) capSeamWidth_pos
      have hret : (S b).window xw = E.oldOutput ((S b).collarOldPoint hOld z₀) ∧
          φ b xw.val = (min (riemannianEDistOf E.terminal.metric
            (E.oldTerminal ((S b).collarOldPoint hOld z₀)) p) (N : ℝ≥0∞)).toReal := by
        have h := hretained b z₀ hzwindow hznear
        simp only [z₀, add_zero] at h
        exact h
      have hwin : (S b).window xw = capPoint ⟨idx, hidx⟩
          (radialCapBoundary StandardCap.transitionEnd_pos y) := by
        have h := hclosedWindow b xw hnorm.le
        simp only [b, eB.apply_symm_apply] at h
        exact h
      have hsame : (⟨finiteCoreInclusion StandardCap.transitionEnd_pos hδ f
            (fun j => (hf j).injective) hdisj
            (cuttingSphereAttachment hδ f (fun j => (hf j).injective) hdisj ⟨idx, y⟩),
          hmem⟩ : Ret) = (S b).window xw := by
        rw [hwin]
        apply Subtype.ext
        exact (finiteCapQuotient_coherence StandardCap.transitionEnd_pos hδ f
          (fun j => (hf j).injective) hdisj ⟨idx, y⟩).symm
      have hvalue : fcap b xw.val = oldScalar ((S b).window xw) := by
        calc
          _ = φ b xw.val := (hinside b xw.val xw.property hxcore).2.symm
          _ = _ := hret.2
          _ = oldScalar (E.oldOutput ((S b).collarOldPoint hOld z₀)) :=
            (holdScalar _).symm
          _ = _ := congrArg oldScalar hret.1.symm
      have h := hvalue.trans (congrArg oldScalar hsame.symm)
      simp only [capValue, coreValue, indexedCapBoundary, dif_pos hidx, dif_pos hmem]
      exact h
    · have hmem := mt hmembership.mp hidx
      simp only [capValue, coreValue, indexedCapBoundary, dif_neg hidx, dif_neg hmem]
  have hex := exists_scalar_on_finite_quotient
    StandardCap.transitionEnd_pos hδ f (fun j => (hf j).injective) hdisj
    coreValue capValue hboundary
  obtain ⟨Gfull, hGcore, hGcap⟩ := hex
  let G : Ret → ℝ := fun y => Gfull y.val
  have hGold (z : E.old) : G (E.oldOutput z) =
      (min (riemannianEDistOf E.terminal.metric (E.oldTerminal z) p)
        (N : ℝ≥0∞)).toReal := by
    have hzrange : E.oldOutput z ∈ range (finiteRetainedCoreInclusion
        StandardCap.transitionEnd_pos hδ f hf hdisj R) := hOldRange ▸ mem_range_self z
    obtain ⟨x, hx⟩ := hzrange
    have hmem : finiteCoreInclusion StandardCap.transitionEnd_pos hδ f
        (fun j => (hf j).injective) hdisj x.val ∈ (Ret : Set Qcap) := x.property
    calc
      G (E.oldOutput z) = G (finiteRetainedCoreInclusion
          StandardCap.transitionEnd_pos hδ f hf hdisj R x) := congrArg G hx.symm
      _ = coreValue x.val := hGcore x.val
      _ = oldScalar (finiteRetainedCoreInclusion
          StandardCap.transitionEnd_pos hδ f hf hdisj R x) := dif_pos hmem
      _ = oldScalar (E.oldOutput z) := congrArg oldScalar hx
      _ = _ := holdScalar z
  have hGcapPoint (b : Bidx) (x : {v : ThreeSpace // ‖v‖ ≤ standardCapL}) :
      G (capPoint b x) = fcap (eB.symm b) x.val := by
    change Gfull (finiteCapInclusion StandardCap.transitionEnd_pos hδ f
      (fun j => (hf j).injective) hdisj ⟨b.val, x⟩) = _
    rw [hGcap]
    exact dif_pos b.property
  exact ⟨Gfull, fun z => hGold z, fun b x => hGcapPoint b x⟩

/-- A fixed physical constant for the literal finite cap output. The single
scalar for each truncated original distance is descended from the same selected
cap extensions; no global distance comparison is assumed. -/
theorem exists_uniform_finite_output_distance_scalar :
    ∃ C : ℝ≥0, 1 ≤ C ∧
      ∀ (P : OrientedThreeStage.{u}) {ι : Type} [Fintype ι] {precision : ι → ℝ}
        (hδ : ∀ j, 0 < precision j)
        (f : ∀ j : ι, bufferedCylinder (precision j) → P.Carrier)
        (hf : ∀ j, _root_.Topology.IsOpenEmbedding (f j))
        (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
        (hs : ∀ j, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (f j))
        (R : Set (ConnectedComponents (cutCore f))) (c : ℝ) (hc : 4 ≤ c),
      letI : LocallyPathConnectedSpace P.Carrier :=
        originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
      let Qcap := FiniteCapQuotient StandardCap.transitionEnd_pos hδ f
        (fun j => (hf j).injective) hdisj
      let Ret := finiteCapRetained StandardCap.transitionEnd_pos hδ f hf hdisj R
      let Bidx := {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
      letI : ChartedSpace ThreeSpace Qcap := finiteCapChartedSpace ThreeModel
        finrank_threeSpace_eq_three StandardCap.transitionEnd_pos hδ f hf hdisj
      letI : IsManifold ThreeModel ∞ Qcap := finiteCapQuotient_isManifold
        finrank_threeSpace_eq_three StandardCap.transitionEnd_pos hδ f hf hdisj hs
      letI : T2Space Qcap := finiteCapQuotient_t2Space
        StandardCap.transitionEnd_pos hδ f hf hdisj
      letI : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace
        StandardCap.transitionEnd_pos hδ f hf hdisj R).1
      ∀ (oRet : SmoothOrientation ThreeModel Ret) {a s : ℝ}
        (E : MetricCutCapEvent P (OrientedThreeStage.ofSmoothOrientation Ret oRet) a s)
        {fixed : StaticCapScaffold} {D η : ℝ} {m : ℕ}
        (S : ∀ b : E.RetainedBoundaryIndex, E.PresentedStaticCap fixed D m η b),
      E.old = E.transition.trace.retainedCore →
      (∀ b, (S b).witness.HasRadialCoordinates) →
      (∀ b, (S b).hasCanonicalWindow) → η ≤ 1 / 2 → standardCapL + 1 ≤ D →
      ∀ (xB : Bidx → E.incoming.terminalRegularOpen) (kB : Bidx → ℕ)
        (d : ∀ b : Bidx, normalizedDatum E.terminal.metric (xB b)
          (c * precision b.val.1) (kB b))
        (w : ∀ b : Bidx, StandardCap.CanonicalStaticInsertionWitness (d b)
          fixed.collarLength fixed.collar_pos D m η)
        (eB : E.RetainedBoundaryIndex ≃ Bidx),
      range E.oldOutput = range (finiteRetainedCoreInclusion
        StandardCap.transitionEnd_pos hδ f hf hdisj R) →
      (∀ (b : E.RetainedBoundaryIndex) (x : standardCapWindow D),
        (S b).window x = finiteFullWitnessMap ThreeModel finrank_threeSpace_eq_three
          StandardCap.transitionEnd_pos hδ f hf hdisj hs R c hc (eB b) ((w (eB b)).window x)) →
      E.HasUniformDistanceScalar C := by
  have hglue := exists_uniform_actual_local_physical_scalar_glue_on_closed_core.{u}
  obtain ⟨C, hC, hphysical⟩ := hglue
  refine ⟨C, hC, ?_⟩
  intro P ι _ precision hδ f hf hdisj hs R c hc
  letI : LocallyPathConnectedSpace P.Carrier :=
    originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
  let Qcap := FiniteCapQuotient StandardCap.transitionEnd_pos hδ f
    (fun j => (hf j).injective) hdisj
  let Ret := finiteCapRetained StandardCap.transitionEnd_pos hδ f hf hdisj R
  let Bidx := {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
  letI : ChartedSpace ThreeSpace Qcap := finiteCapChartedSpace ThreeModel
    finrank_threeSpace_eq_three StandardCap.transitionEnd_pos hδ f hf hdisj
  letI : IsManifold ThreeModel ∞ Qcap := finiteCapQuotient_isManifold
    finrank_threeSpace_eq_three StandardCap.transitionEnd_pos hδ f hf hdisj hs
  letI : T2Space Qcap := finiteCapQuotient_t2Space
    StandardCap.transitionEnd_pos hδ f hf hdisj
  letI : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace
    StandardCap.transitionEnd_pos hδ f hf hdisj R).1
  dsimp only
  intro oRet a s E fixed D η m S hOld hcoordinates hcanonical hη hD xB kB d w eB
    hOldRange hwindow p N
  classical
  have hL : 0 < standardCapL := StandardCap.transitionEnd_pos
  let capPoint (b : Bidx) (x : {v : ThreeSpace // ‖v‖ ≤ standardCapL}) : Ret :=
    ⟨finiteCapInclusion StandardCap.transitionEnd_pos hδ f
      (fun j => (hf j).injective) hdisj ⟨b.val, x⟩, b.property⟩
  have hclosedWindow (b : E.RetainedBoundaryIndex) (x : standardCapWindow D)
      (hx : ‖x.val‖ ≤ standardCapL) :
      (S b).window x = capPoint (eB b) ⟨x.val, hx⟩ :=
    fods_closed_window P hδ f hf hdisj hs R c hc oRet E S xB kB d w eB hwindow b x hx
  choose fcap φ _hfcap hinside hretained hlocal using fun b : E.RetainedBoundaryIndex =>
    hphysical (S b) hOld (hcoordinates b) (hcanonical b) hη hD p N
  have hbd := fods_boundary_scalar P hδ f hf hdisj hs R oRet E S
    hOld hD eB hOldRange p N fcap φ hinside hretained hclosedWindow
  obtain ⟨Gfull, hGoldFull, hGcapFull⟩ := hbd
  let G : Ret → ℝ := fun y => Gfull y.val
  have hGold (z : E.old) : G (E.oldOutput z) =
      (min (riemannianEDistOf E.terminal.metric (E.oldTerminal z) p)
        (N : ℝ≥0∞)).toReal := hGoldFull z
  have hGcapPoint (b : Bidx) (x : {v : ThreeSpace // ‖v‖ ≤ standardCapL}) :
      G (capPoint b x) = fcap (eB.symm b) x.val := hGcapFull b x
  have hGclosed (b : E.RetainedBoundaryIndex) (x : standardCapWindow D)
      (hx : ‖x.val‖ ≤ standardCapL) : G ((S b).window x) = φ b x.val := by
    rw [hclosedWindow b x hx, hGcapPoint, eB.symm_apply_apply]
    exact (hinside b x.val x.property (by
      simpa only [standardCapClosedCore, Metric.mem_closedBall, dist_zero_right] using hx)).2.symm
  have hGcollar (b : E.RetainedBoundaryIndex) (x₀ x : standardCapWindow D)
      (hx₀ : ‖x₀.val‖ ≤ standardCapL) (hx : x.val ∈ Metric.ball x₀.val capSeamWidth)
      (hout : standardCapL < ‖x.val‖) : G ((S b).window x) = φ b x.val :=
    fods_collar_value (S b) hOld p N G (φ b) hGold (hretained b) x₀ x hx₀ hx hout
  have hGloc (q : Ret) : ∃ U : Opens Ret, q ∈ U ∧
      ∀ y ∈ U, ∀ z ∈ U,
        edist (G y) (G z) ≤ (C : ℝ≥0∞) * riemannianEDistOf E.outputMetric y z := by
    by_cases hq : q ∈ interior (range E.oldOutput)
    · obtain ⟨U, hqU, hU⟩ := local_distance_scalar_bound_on_old_interior E p N G hGold q hq
      refine ⟨U, hqU, fun y hy z hz => (hU y hy z hz).trans ?_⟩
      calc
        _ = (1 : ℝ≥0∞) * riemannianEDistOf E.outputMetric y z := (one_mul _).symm
        _ ≤ _ := mul_le_mul' (ENNReal.coe_le_coe.mpr hC) le_rfl
    · have hqcap : q ∈ (interior (range (finiteRetainedCoreInclusion
          StandardCap.transitionEnd_pos hδ f hf hdisj R)))ᶜ := by
        rwa [← hOldRange]
      rw [finiteRetained_compl_interior_core StandardCap.transitionEnd_pos hδ f hf hdisj R]
        at hqcap
      obtain ⟨bidx, x, hxq⟩ := mem_iUnion.mp hqcap
      let b : E.RetainedBoundaryIndex := eB.symm bidx
      have hxwindow : x.val ∈ standardCapWindow D := by
        change ‖x.val‖ < D + 1
        have hxn : ‖x.val‖ ≤ standardCapL := x.property
        linarith
      let x₀ : standardCapWindow D := ⟨x.val, hxwindow⟩
      have hx₀ : ‖x₀.val‖ ≤ standardCapL := x.property
      have hcenter : (S b).window x₀ = q := by
        rw [hclosedWindow b x₀ x.property]
        simp only [b, eB.apply_symm_apply]
        exact hxq
      have hGeq : ∀ x : standardCapWindow D, x.val ∈ Metric.ball x₀.val capSeamWidth →
          G ((S b).window x) = φ b x.val := by
        intro x hxball
        by_cases hxcore : ‖x.val‖ ≤ standardCapL
        · exact hGclosed b x hxcore
        · exact hGcollar b x₀ x hx₀ hxball (lt_of_not_ge hxcore)
      obtain ⟨U, hU, hUloc⟩ := fods_local_patch (S b) C G (φ b) x₀ (hlocal b x₀ hx₀) hGeq
      exact ⟨U, hcenter ▸ hU, hUloc⟩
  exact ⟨G, hGold, fods_global_of_local E.outputMetric G C hC hGloc⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
