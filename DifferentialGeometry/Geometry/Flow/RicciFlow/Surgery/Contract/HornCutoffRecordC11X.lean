import Batteries.Tactic.OpenPrivate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornCutoffRecord
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FinitePresentedStaticCapC11X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LinkedCanonicalWindowC12X

/-!
# HornCutoffRecordC11X（S-CH11-EXT1，extension of 已跟踪 `Contract/HornCutoffRecord`）

astra `Contract/HornCutoffRecord.lean` 把 `HasRadialCoordinates` 一路穿过 prepared-event 链。
宿主（W8 的 `HornCutoffRecord`，4545 行）保持不变；这里抄写 donor 的三处加强 / 新增（证明体逐字，
只改名字后缀与调用处）：

* `PreparedCutoffEventGeometry.exists_of_retainedEvent_heq_C11X`（宿主私有同名定理的加强，
  结论多一个 `HasRadialCoordinates` 合取；SIG，改名 `_C11X`）；
* `finitePresentedStaticCapsOfStage_C11X`（宿主私有同名 `def` 的加强：类型多 `HasRadialCoordinates`，
  body 走 `FinitePresentedStaticCapC11X` 的 `…OfTerminal_C11X` 与 `…_hasRadialCoordinates`；SIG）；
* `exists_record_from_original_backward_with_static_and_radial_coordinates`（donor 新增，W8 无此名）。

**唯一一处非逐字改动**：`finitePresentedStaticCapsOfStage_C11X` 末尾
`refine ⟨caps.1, ⟨caps.2.1, caps.2.2.1, ?_⟩⟩; intro b; obtain ⟨…⟩ := caps.2.2.2 b; exact ⟨…⟩`
改成同义的 term 模式 `exact ⟨caps.1, ⟨caps.2.1, caps.2.2.1, fun b => ⟨(caps.2.2.2 b).1, …⟩⟩⟩`
（同一个 statement；donor 的 tactic 写法在树内 > 8 分钟，term 写法整个文件 145 s）。

宿主的私有声明用 `open private … from` 取得（`PreparedCutoffEventGeometry` 是宿主私有结构，
点记号 `F.exists_of_retainedEvent_heq_C11X` 在本模块里解析不到，所以调用处改成显式前缀形式）。
-/

open private PreparedCutoffEventGeometry PreparedCutoffEventGeometry.toRetained
  PreparedCutoffEventGeometry.neck PreparedCutoffEventGeometry.static
  PreparedCutoffEventGeometry.old_eq_retained PreparedCutoffEventGeometry.tube_eq
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.orientedRotatedNeck
  exists_original_backward_transfer
  exists_geometricCutoffRecord_of_preparedEventGeometry from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornCutoffRecord


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
private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

private theorem PreparedCutoffEventGeometry.exists_of_retainedEvent_heq_C11X
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    {E : MetricCutCapEvent P Q a s} {p : CutoffParameters} {δ r : ℝ} {k : ℕ}
    (F : PreparedCutoffEventGeometry E p δ r k)
    (E' : RetainedCoreEvent P' Q' a' s')
    (hP : P' = P) (hQ : Q' = Q) (ha : a' = a) (hs : s' = s)
    (hE : HEq E' (E.toRetainedCoreEvent (PreparedCutoffEventGeometry.old_eq_retained F))) :
    ∃ F' : PreparedCutoffEventGeometry E'.toMetricCutCapEvent p δ r k,
      ∃ e : E'.transition.trace.tubes.Index ≃ E.transition.trace.tubes.Index,
        (∀ j, HEq ((PreparedCutoffEventGeometry.neck F') j) ((PreparedCutoffEventGeometry.neck F) (e j))) ∧
        ∃ eB : E'.toMetricCutCapEvent.RetainedBoundaryIndex ≃ E.RetainedBoundaryIndex,
          (∀ b, HEq b.val (eB b).val) ∧
          (∀ b, HEq ((PreparedCutoffEventGeometry.static F') b).neck ((PreparedCutoffEventGeometry.static F) (eB b)).neck) ∧
          (∀ b, ((PreparedCutoffEventGeometry.static F') b).neck.scale = ((PreparedCutoffEventGeometry.static F) (eB b)).neck.scale) ∧
          (∀ b, HEq ((PreparedCutoffEventGeometry.static F') b).witness ((PreparedCutoffEventGeometry.static F) (eB b)).witness) ∧
          (∀ b, HEq ((PreparedCutoffEventGeometry.static F') b).inclusion ((PreparedCutoffEventGeometry.static F) (eB b)).inclusion) ∧
          (∀ b z, HEq (((PreparedCutoffEventGeometry.static F') b).inclusion (((PreparedCutoffEventGeometry.static F') b).witness.window z))
            (((PreparedCutoffEventGeometry.static F) (eB b)).inclusion (((PreparedCutoffEventGeometry.static F) (eB b)).witness.window z))) ∧
          (∀ b z, HEq (((PreparedCutoffEventGeometry.static F') b).inclusion (((PreparedCutoffEventGeometry.static F') b).witness.cap z))
            (((PreparedCutoffEventGeometry.static F) (eB b)).inclusion (((PreparedCutoffEventGeometry.static F) (eB b)).witness.cap z))) ∧
          (((∀ b, ((PreparedCutoffEventGeometry.static F) b).hasCanonicalWindow) →
            ∀ b, ((PreparedCutoffEventGeometry.static F') b).hasCanonicalWindow) ∧
            ((∀ b, ((PreparedCutoffEventGeometry.static F) b).hasLinkedCanonicalWindow_C12X) →
            ∀ b, ((PreparedCutoffEventGeometry.static F') b).hasLinkedCanonicalWindow_C12X)) ∧
          ((∀ b, ((PreparedCutoffEventGeometry.static F) b).witness.HasRadialCoordinates) →
            ∀ b, ((PreparedCutoffEventGeometry.static F') b).witness.HasRadialCoordinates) := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  exact ⟨(PreparedCutoffEventGeometry.toRetained F), Equiv.refl _, (fun _ => HEq.rfl), Equiv.refl _,
    (fun _ => HEq.rfl), (fun _ => HEq.rfl), (fun _ => rfl), (fun _ => HEq.rfl),
    (fun _ => HEq.rfl), (fun _ _ => HEq.rfl), (fun _ _ => HEq.rfl),
    ⟨fun h => h, fun h => h⟩, fun h => h⟩


end

section

universe u

attribute [local instance] threeBallChartedSpace threeBall_isManifold

open private terminal_data_transport from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FinitePresentedStaticCap

universe v

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)
private def finitePresentedStaticCapsOfStage_C11X
    (P : OrientedThreeStage.{u})
    {ι : Type} [Fintype ι] {precision : ι → ℝ}
    (hδ : ∀ j, 0 < precision j) (hδ1 : ∀ j, precision j < 1)
    (f : ∀ j : ι, bufferedCylinder (precision j) → P.Carrier)
    (hf : ∀ j, _root_.Topology.IsOpenEmbedding (f j))
    (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
    (hs : ∀ j, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f j))
    (R : Set (ConnectedComponents (cutCore f)))
    (hnontrivial : Nonempty ι ∨ Nonempty (retainedCore f Rᶜ))
    {t₀ t₁ : ℝ} {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} (hD : 0 < D) :
    letI : LocallyPathConnectedSpace P.Carrier :=
      originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
    let Q := FiniteCapQuotient transitionEnd_pos hδ f
      (fun j => (hf j).injective) hdisj
    let Ret := finiteCapRetained transitionEnd_pos hδ f hf hdisj R
    let Disc := finiteCapDiscarded transitionEnd_pos hδ f hf hdisj R
    let Bidx := {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
    letI : ChartedSpace ThreeSpace Q :=
      finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three transitionEnd_pos hδ f hf hdisj
    letI : IsManifold ThreeModel ∞ Q :=
      finiteCapQuotient_isManifold finrank_threeSpace_eq_three transitionEnd_pos hδ f hf hdisj hs
    letI : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    letI : CompactSpace Q := finiteCapQuotient_compactSpace transitionEnd_pos hδ f hf hdisj
    letI : CompactSpace Ret :=
      (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf hdisj R).1
    letI : CompactSpace Disc :=
      (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf hdisj R).2
    ∀ (oQ : SmoothOrientation ThreeModel Q) (oRet : SmoothOrientation ThreeModel Ret)
      (oDisc : SmoothOrientation ThreeModel Disc)
      (G : P.IncomingSlab t₀ t₁)
      (L : G.TerminalLimitMetric)
      (E : MetricCutCapEvent P
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) t₀ t₁)
      (A : (ι × Bool) → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
      (B : (ι × Bool) → ThreeBall ≃ₜ ThreeBall)
      (a : (ι × Bool) → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
      (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (a b y)),
      (∀ b x, (B b x : ThreeSpace) = A b x) →
      E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc →
      E.capped = OrientedThreeStage.ofSmoothOrientation Q oQ →
      HEq E.transition.trace
        ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj R hnontrivial).reparametrizeCaps B (fun b => (a b).toHomeomorph) hboundary) →
      E.incoming = G → HEq E.terminal L →
      ∀ (hRet : MapsTo (Subtype.val : cutCore f → P.Carrier) (retainedCore f R)
          (fun x : P.Carrier => G.terminalRegularRegion x))
        (c : ℝ) (hc : 4 ≤ c) (x₀ : ι → G.terminalRegularOpen) (order : ι → ℕ)
        (d₀ : ∀ i, normalizedDatum L.metric (x₀ i) (precision i) (order i))
        (hOriginal : ∀ i, f i = neckAmbientMap G.terminalRegularOpen (d₀ i))
        (k' : Bidx → ℕ)
        (hrec : ∀ b : Bidx, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹)
        (d : ∀ b : Bidx, normalizedDatum L.metric
          ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b))
        (hmap : ∀ b : Bidx, (d b).map =
          (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
        (hside : ∀ b : Bidx, (d b).retainedSide = true)
        (w : ∀ b : Bidx,
          CanonicalStaticInsertionWitness (d b) fixed.collarLength fixed.collar_pos D m ε),
        E.outputMetric = finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
          G.terminalRegularOpen L.metric R hRet c hc x₀ order d₀
          hOriginal hrec d hmap hside w →
        Σ e : E.RetainedBoundaryIndex ≃ Bidx,
          {S : ∀ b : E.RetainedBoundaryIndex, E.PresentedStaticCap fixed D m ε b //
            (∀ b, HEq b.val (e b).val) ∧
            ∀ b, (S b).delta = c * precision (e b).val.1 ∧
              (S b).order = k' (e b) ∧
              HEq (S b).neck (d (e b)).oriented.toNormalizedNeck ∧
              (S b).witness.HasRadialCoordinates ∧
              ∀ u : standardCapWindow D,
                (S b).inclusion ((S b).witness.window u) =
                  finiteFullWitnessMap ThreeModel (by simp) transitionEnd_pos
                    hδ f hf hdisj hs R c hc (e b) ((w (e b)).window u)} := by
  revert f
  rw [← P.ofSmoothOrientation_smoothOrientation]
  intro f hf hdisj hs R hnontrivial
  dsimp only
  intro oQ oRet oDisc G L E A B a hboundary hB hDisc hCap htrace hG hL
    hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside w hOutput
  let caps := finitePresentedStaticCapsOfTerminal_C11X
    hδ hδ1 f hf hdisj hs R P.smoothOrientation hnontrivial hD
    oQ oRet oDisc G L E A B a hboundary hB hDisc hCap htrace hG hL
    hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside w hOutput
  have hcoordinates := finitePresentedStaticCapsOfTerminal_hasRadialCoordinates
    hδ hδ1 f hf hdisj hs R P.smoothOrientation hnontrivial hD
    oQ oRet oDisc G L E A B a hboundary hB hDisc hCap htrace hG hL
    hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside w hOutput
  exact ⟨caps.1, ⟨caps.2.1, caps.2.2.1, fun b =>
    ⟨(caps.2.2.2 b).1, (caps.2.2.2 b).2.1, (caps.2.2.2 b).2.2.1, hcoordinates b,
      (caps.2.2.2 b).2.2.2⟩⟩⟩


end

section

universe u

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)
private theorem exists_record_from_original_backward_with_static_and_radial_coordinates
    {P Q : OrientedThreeStage.{u}} {H : RetainedCoreHistory.{u}} {i : Fin H.eventCount}
    {a s : ℝ} (E : MetricCutCapEvent P Q a s)
    (hP : H.stage i.castSucc = P) (hQ : H.stage i.succ = Q)
    (ha : H.time i.castSucc = a) (hs : H.time i.succ = s)
    {p : CutoffParameters} {δ r : ℝ} {k : ℕ}
    (F : PreparedCutoffEventGeometry E p δ r k)
    (hE : HEq (H.coreEvent i) (E.toRetainedCoreEvent (PreparedCutoffEventGeometry.old_eq_retained F)))
    (hδ : δ ≤ p.delta s)
    (hk : max (p.modelOrder + 6) (2 * ⌊δ⁻¹⌋₊ + 4) ≤ k)
    (hr : r < (p.delta s) ^ 2 * p.neckRadius s)
    {n : ℕ} (δOriginal : Fin n → ℝ) (kOriginal : Fin n → ℕ)
    (N : ∀ j, NormalizedNeck E.terminal.metric (δOriginal j) (kOriginal j))
    (hδOrig : ∀ j, δOriginal j ≤ δ) (hδ1 : δ < 1)
    (rotation : Fin n → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
    (hmark : ∀ j, DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j)
      spherePoint = (N j).sphereMark) (side : Fin n → Bool)
    (horder : ∀ j, k ≤ kOriginal j)
    (e : Fin n ≃ E.transition.trace.tubes.Index)
    (hneck : ∀ j, (PreparedCutoffEventGeometry.neck F) (e j) = DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.orientedRotatedNeck (N j) (hδOrig j) hδ1
      (rotation j) (hmark j) (side j) (horder j)) :
    ∃ (NH : ∀ j, NormalizedNeck (H.toHistory.event i).terminal.metric (δOriginal j) (kOriginal j))
      (hmarkH : ∀ j, DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j)
        spherePoint = (NH j).sphereMark)
      (Nrecord : (H.toHistory.event i).transition.trace.tubes.Index →
        NormalizedNeck (H.toHistory.event i).terminal.metric δ k)
      (eOriginal : Fin n ≃ (H.toHistory.event i).transition.trace.tubes.Index),
      HEq NH N ∧ (∀ j, (NH j).scale = (N j).scale) ∧
      (∀ j, Nrecord (eOriginal j) = DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.orientedRotatedNeck (NH j) (hδOrig j) hδ1
        (rotation j) (hmarkH j) (side j) (horder j)) ∧
      (∀ j (z : TubeDomain) (hz : (z.1, z.2.val) ∈ neckBuffer δ),
        (H.toHistory.event i).transition.trace.tubes.tube j z =
          ((Nrecord j).chart ⟨(z.1, z.2.val), hz⟩).val) ∧
      ((∀ j, Nonempty (IncomingBackwardNeck H.toHistory i (Nrecord j) r)) →
        ∃ G : GeometricCutoffRecord H.toHistory i p,
          G.delta = (fun _ => δ) ∧ G.order = (fun _ => k) ∧
          HEq G.neck Nrecord ∧ (∀ j, (G.neck j).scale = (r ^ 2)⁻¹) ∧
          ∃ eB : (H.toHistory.event i).RetainedBoundaryIndex ≃ E.RetainedBoundaryIndex,
            (∀ b, HEq b.val (eB b).val) ∧
            (∀ b, HEq (G.static b).neck ((PreparedCutoffEventGeometry.static F) (eB b)).neck) ∧
            (∀ b, (G.static b).neck.scale = ((PreparedCutoffEventGeometry.static F) (eB b)).neck.scale) ∧
            (∀ b, HEq (G.static b).witness ((PreparedCutoffEventGeometry.static F) (eB b)).witness) ∧
            (∀ b, HEq (G.static b).inclusion ((PreparedCutoffEventGeometry.static F) (eB b)).inclusion) ∧
            (∀ b z, HEq ((G.static b).inclusion ((G.static b).witness.window z))
              (((PreparedCutoffEventGeometry.static F) (eB b)).inclusion (((PreparedCutoffEventGeometry.static F) (eB b)).witness.window z))) ∧
            (∀ b z, HEq ((G.static b).inclusion ((G.static b).witness.cap z))
              (((PreparedCutoffEventGeometry.static F) (eB b)).inclusion (((PreparedCutoffEventGeometry.static F) (eB b)).witness.cap z))) ∧
            (((∀ b, ((PreparedCutoffEventGeometry.static F) b).hasCanonicalWindow) →
              ∀ b, (G.static b).hasCanonicalWindow) ∧
              ((∀ b, ((PreparedCutoffEventGeometry.static F) b).hasLinkedCanonicalWindow_C12X) →
              ∀ b, (G.static b).hasLinkedCanonicalWindow_C12X)) ∧
            ((∀ b, ((PreparedCutoffEventGeometry.static F) b).witness.HasRadialCoordinates) →
              ∀ b, (G.static b).witness.HasRadialCoordinates)) := by
  obtain ⟨NH, NHhigh, hNH, hNHpoint, hNHscale, hmarkH, hhighDef,
    hNHhigh, hNHhighpoint, hback⟩ := exists_original_backward_transfer
    E hP hQ ha hs (PreparedCutoffEventGeometry.old_eq_retained F) hE N hδOrig hδ1 rotation hmark side horder
  obtain ⟨FH, er, hNr, eB, hlabel, hcapNeck, hcapScale, hwitness, hinclusion, hwindow, hcap, hcanonical, hcoordinates⟩ :=
    PreparedCutoffEventGeometry.exists_of_retainedEvent_heq_C11X F (H.coreEvent i) hP hQ ha hs hE
  let eOriginal := e.trans er.symm
  have hrecord (j) : (PreparedCutoffEventGeometry.neck FH) j = NHhigh (e.symm (er j)) := by
    let z := e.symm (er j)
    have hh : HEq ((PreparedCutoffEventGeometry.neck FH) j) ((PreparedCutoffEventGeometry.neck F) (e z)) := by
      simpa only [z, e.apply_symm_apply] using hNr j
    exact eq_of_heq (hh.trans ((heq_of_eq (hneck z)).trans (hNHhighpoint z).symm))
  refine ⟨NH, hmarkH, (PreparedCutoffEventGeometry.neck FH), eOriginal, hNH, hNHscale, ?_, (PreparedCutoffEventGeometry.tube_eq FH), ?_⟩
  · intro j
    rw [hrecord]
    have hind : e.symm (er (eOriginal j)) = j := by simp [eOriginal]
    exact (congrArg NHhigh hind).trans (hhighDef j)
  · intro hB
    obtain ⟨G, hδG, hkG, hNG, hscaleG, hstatic⟩ := exists_geometricCutoffRecord_of_preparedEventGeometry FH
      (by simpa only [hs] using hδ) hk (by simpa only [hs] using hr)
      (fun j => Classical.choice (hB j))
    refine ⟨G, hδG, hkG, hNG, hscaleG, eB, hlabel, ?_⟩
    rw [hstatic]
    exact ⟨hcapNeck, hcapScale, hwitness, hinclusion, hwindow, hcap, hcanonical, hcoordinates⟩


end

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
