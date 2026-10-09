import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.P5LinkedSupplyC12X

set_option autoImplicit false

/-!
# P5L 供给的 nominal 追踪版（S-CH11-NOMID G1b，后缀 `_P6NI`）

`exists_rewindowed_linked_record_C12X` / `lateLinkedRecordsSupply_of_astra_C12X` / `…_of_outer_C12X`
（ch12 External，已跟踪）的结论是 `∃ R'` / `LateLinkedRecordsSupply_C11E F q`，late record 与底 record 的
关系不可见。lead R-C11-8 裁定：两套 records 的 `CutoffParameters` 不同（`q.withModelWindow D m ζ` vs `q`）
时必须**证** reparameterization 保留实际 neck / window，不能仅凭"同一 event"。
证明里
`R' = { R with static := …, recenter_… := …, order_lower := … }` 不动 tube 数据，且
`restrictCanonicalWindow` 保留 `neck / inclusion / cap`（只缩 window）。所以追踪版重证，结论多一个
**reparameterization 合取**（inline，不是具名 Prop）：
`R'.nominalRadius = R.nominalRadius ∧ R'.delta = R.delta ∧ R'.order = R.order ∧
(∀ α, HEq (R'.neck α) (R.neck α)) ∧ (∀ b, scale 同) ∧ cap 嵌入同`：
* `exists_rewindowed_linked_record_nominal_P6NI`：单 event（`hraw` 比原版多 `raw.neck.scale`、cap 嵌入
  两项，outer 的 `hblockOuter` 已含）；
* `lateLinkedRecordsSupplyNom_of_astra_P6NI` / `…_of_outer_P6NI`：`hP5L` 的 `∃ records'` 多合取
  `∀ i hi, reparam (records' i hi) (records n i)`（`records` = 底 records 族，参数 `q`）；
  即 `exists_lateKdata_of_P5L_antitone_nominal_P6NI` 的 `hP5L` binder（`K n := F.tower.history n`）。
私有引理 `p5l_recenter_transport` / `p5l_order_transport`（原文件 private）原样重证为 `_P6NI` 私有副本。
由 build-logs/scratch/S-CH11-NOMID/mk_c.py 从 ch12 External 两个文件逐段取证明体生成。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Neck
open Set
open scoped Manifold ContDiff

namespace GC.LongTime.Ch11

universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

/-- 分量级搬运：tube 数据 `(δ, o, N)` 与 static neck `SN` 从 transition `X`（terminal `U, h`）
搬到 `X'`（`U', h'`）：static scale，以及 recenter 的 mark / delta / scale comparison / chart /
in-buffer。 -/
private theorem p5l_recenter_transport_P6NI
    {P P' Q Q' D₀ N₀ D₁ N₁ : OrientedThreeStage.{u}}
    (hP : P = P') (hQ : Q = Q') (hD : D₀ = D₁) (hN : N₀ = N₁)
    {X : SmoothCutCapTransition P Q D₀ N₀} {X' : SmoothCutCapTransition P' Q' D₁ N₁}
    (hX : HEq X X')
    {U : TopologicalSpace.Opens P.Carrier} {U' : TopologicalSpace.Opens P'.Carrier}
    (hU : HEq U U') {h : SmoothRiemannianMetric ThreeModel U}
    {h' : SmoothRiemannianMetric ThreeModel U'} (hh : HEq h h')
    {δ : X.trace.tubes.Index → ℝ} {δ' : X'.trace.tubes.Index → ℝ} (hδ : HEq δ' δ)
    {o : X.trace.tubes.Index → ℕ} {o' : X'.trace.tubes.Index → ℕ} (ho : HEq o' o)
    {N : ∀ α, NormalizedNeck h (δ α) (o α)} {N' : ∀ α, NormalizedNeck h' (δ' α) (o' α)}
    (hNk : HEq N' N)
    (b : {β : X.trace.tubes.Boundary //
      ∀ y, X.trace.tubes.coreBoundarySphere β y ∈ X.trace.retainedCore})
    (b' : {β : X'.trace.tubes.Boundary //
      ∀ y, X'.trace.tubes.coreBoundarySphere β y ∈ X'.trace.retainedCore})
    (hb : HEq b b')
    {sδ sδ' : ℝ} {sk sk' : ℕ} (hsδ : sδ' = sδ) (hsk : sk' = sk)
    {SN : NormalizedNeck h sδ sk} {SN' : NormalizedNeck h' sδ' sk'} (hSN : HEq SN' SN)
    (rc : ℝ) :
    SN'.scale = SN.scale ∧
    (SN.sphereMark = (N b.1.1).sphereMark → SN'.sphereMark = (N' b'.1.1).sphereMark) ∧
    (sδ = rc * δ b.1.1 → sδ' = rc * δ' b'.1.1) ∧
    (|SN.scale / (N b.1.1).scale - 1| ≤ rc * δ b.1.1 →
      |SN'.scale / (N' b'.1.1).scale - 1| ≤ rc * δ' b'.1.1) ∧
    ((∀ x : neckBuffer sδ,
        ∀ hx : (x.1.1, (if b.1.2 then 1 else -1) * (1 + x.1.2)) ∈ neckBuffer (δ b.1.1),
        SN.chart x = (N b.1.1).chart ⟨(x.1.1, (if b.1.2 then 1 else -1) * (1 + x.1.2)), hx⟩) →
      ∀ x : neckBuffer sδ',
        ∀ hx : (x.1.1, (if b'.1.2 then 1 else -1) * (1 + x.1.2)) ∈ neckBuffer (δ' b'.1.1),
        SN'.chart x =
          (N' b'.1.1).chart ⟨(x.1.1, (if b'.1.2 then 1 else -1) * (1 + x.1.2)), hx⟩) ∧
    ((∀ x : neckBuffer sδ,
        (x.1.1, (if b.1.2 then 1 else -1) * (1 + x.1.2)) ∈ neckBuffer (δ b.1.1)) →
      ∀ x : neckBuffer sδ',
        (x.1.1, (if b'.1.2 then 1 else -1) * (1 + x.1.2)) ∈ neckBuffer (δ' b'.1.1)) := by
  subst hP hQ hD hN
  cases hX
  cases hU
  cases hh
  cases hδ
  cases ho
  cases hNk
  cases hb
  subst hsδ hsk
  cases hSN
  exact ⟨rfl, id, id, id, id, id⟩

/-- 分量级搬运：tube order 的下界。 -/
private theorem p5l_order_transport_P6NI
    {P P' Q Q' D₀ N₀ D₁ N₁ : OrientedThreeStage.{u}}
    (hP : P = P') (hQ : Q = Q') (hD : D₀ = D₁) (hN : N₀ = N₁)
    {X : SmoothCutCapTransition P Q D₀ N₀} {X' : SmoothCutCapTransition P' Q' D₁ N₁}
    (hX : HEq X X') {o : X.trace.tubes.Index → ℕ} {o' : X'.trace.tubes.Index → ℕ}
    (ho : HEq o' o) (c : ℕ) (hc : ∀ α, c ≤ o α) : ∀ α, c ≤ o' α := by
  subst hP hQ hD hN
  cases hX
  cases ho
  exact hc

/-- **单 event 核心**：tower event `j` 上的 record `R` + native fine record `FR`（平移后与 `j`
同 presentation，tube 数据 `HEq`）+ tower 上与 `FR.static` 同几何的 raw caps + `FR` 的 linked
windows ⇒ 同一 tower event 上参数 `q.withModelWindow D m ζ` 的 record，每个 static linked，且是 `R` 的
**reparameterization**（`_P6NI`：`nominalRadius / delta / order / neck` 全同，static neck 的 scale 与
cap 嵌入同 `R.static`——`{ R with … }` 不动 tube 数据，`restrictCanonicalWindow` 只缩 window）。 -/
theorem exists_rewindowed_linked_record_nominal_P6NI {H K : RetainedCoreHistory.{u}}
    {j : Fin H.eventCount} {i : Fin K.eventCount} {c : ℝ} {q fp : CutoffParameters}
    (R : GeometricCutoffRecord H.toHistory j q) (FR : GeometricCutoffRecord K.toHistory i fp)
    (hsame : MetricCutCapEvent.SamePresentation
      (GC.GeneralFlow.translate_retained_event (K.coreEvent i) c).toMetricCutCapEvent
      (H.toHistory.event j))
    (hδ : HEq R.delta FR.delta) (ho : HEq R.order FR.order) (hN : HEq R.neck FR.neck)
    (hfixed : fp.fixed = q.fixed) (hrc : fp.recenterConstant = q.recenterConstant)
    (hraw : ∀ b' : (H.toHistory.event j).RetainedBoundaryIndex,
      ∃ (b : (K.toHistory.event i).RetainedBoundaryIndex)
        (raw : (H.toHistory.event j).PresentedStaticCap q.fixed fp.modelRadius fp.modelOrder
          fp.modelAccuracy b'),
        HEq b b' ∧ raw.hasCanonicalWindow ∧ raw.delta = (FR.static b).delta ∧
        raw.order = (FR.static b).order ∧ HEq raw.neck (FR.static b).neck ∧
        raw.witness.windowMetric = (FR.static b).witness.windowMetric ∧
        raw.neck.scale = (R.static b').neck.scale ∧
        (∀ z : ThreeBall, raw.inclusion (raw.witness.cap z) =
          (R.static b').inclusion ((R.static b').witness.cap z)))
    (hlink : ∀ b, linkedCanonicalWindow_C11E (FR.static b))
    {D ζ : ℝ} {m : ℕ} (hD : 0 < D) (hcap : StandardCap.transitionEnd < D + 1)
    (hDfp : D ≤ fp.modelRadius) (hm : m ≤ fp.modelOrder) (hζ : fp.modelAccuracy ≤ ζ) :
    ∃ R' : GeometricCutoffRecord H.toHistory j
        (q.withModelWindow D m ζ hD (fp.modelAccuracy_pos.trans_le hζ)),
      (∀ b', linkedCanonicalWindow_C11E (R'.static b')) ∧
        R'.nominalRadius =
          R.nominalRadius ∧
        R'.delta =
          R.delta ∧
        R'.order =
          R.order ∧
        (∀ α, HEq (R'.neck α) (R.neck α)) ∧
        (∀ b, (R'.static b).neck.scale =
          (R.static b).neck.scale) ∧
        ∀ (b) (z : ThreeBall),
          (R'.static b).inclusion
              ((R'.static b).witness.cap z) =
            (R.static b).inclusion
              ((R.static b).witness.cap z) := by
  obtain ⟨hP, hQ, hD₀, hN₀, hX, hU, hh⟩ := native_tower_components_C12X hsame
  choose bf raw hb hcan hrd hro hrn hrw hrs hri using hraw
  have ht := fun b' => p5l_recenter_transport_P6NI hP hQ hD₀ hN₀ hX hU hh hδ ho hN (bf b') b'
    (hb b') (hrd b') (hro b') (hrn b') q.recenterConstant
  have horder : ∀ α, m + 6 ≤ R.order α :=
    p5l_order_transport_P6NI hP hQ hD₀ hN₀ hX ho (m + 6) fun α =>
      (Nat.add_le_add_right hm 6).trans ((le_max_left _ _).trans (FR.order_lower α))
  let S' : ∀ b', (H.toHistory.event j).PresentedStaticCap q.fixed D m ζ b' := fun b' =>
    (raw b').restrictCanonicalWindow (hcan b') hD hDfp hm hζ
  refine ⟨{ R with
      order_lower := fun α => max_le (horder α) ((le_max_right _ _).trans (R.order_lower α))
      static := S'
      recenter_scale := fun b' => (S' b').neck.scale_scalar
      recenter_mark := fun b' => (ht b').2.1 (FR.recenter_mark (bf b'))
      recenter_delta := fun b' => (ht b').2.2.1 (by
        rw [← hrc]
        exact FR.recenter_delta (bf b'))
      recenter_scale_comparison := fun b' => (ht b').2.2.2.1 (by
        rw [← hrc]
        exact FR.recenter_scale_comparison (bf b'))
      recenter_chart := fun b' => (ht b').2.2.2.2.1 (FR.recenter_chart (bf b'))
      recenter_in_buffer := fun b' => (ht b').2.2.2.2.2 (FR.recenter_in_buffer (bf b')) }, ?_,
    rfl, rfl, rfl, fun _ => HEq.rfl, fun b' => hrs b', fun b' z => hri b' z⟩
  intro b'
  exact linkedCanonicalWindow_restrictCanonicalWindow_C12X (raw b') (hcan b') hD hDfp hm hζ hcap
    (linkedCanonicalWindow_of_terminal_heq_C12X hP hU hh hfixed (FR.static (bf b')) (raw b')
      (hcan b') (hrd b') (ht b').1 (hrw b') (hlink (bf b')))

/-- **S14 P5Linked 供给**：astra 链 + retention + outer 子句的子合取 + 共尾 fine 窗口 + 晚期 fine
linked windows ⇒ `LateLinkedRecordsSupply_C11E F q` 的 reparameterization 追踪版（`_P6NI`：每个 late
record 是底 record `records n i` 的 reparameterization——tube 数据、static neck scale、cap 嵌入同）。
`hblock` 的 raw 子句比原版多 `raw.neck.scale = …`、cap 嵌入两项（outer 的 `hblockOuter` 已含）。 -/
theorem lateLinkedRecordsSupplyNom_of_astra_P6NI {pBase : CutoffParameters}
    {C : GC.GeneralFlow.ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g) {εcut Dcut : ℕ → ℝ} {mcut : ℕ → ℕ}
    (W : ∀ n, GC.GeneralFlow.PreparedSpatialStepRetention (S.state n) (S.state (n + 1))
      (S.accuracy n) (1 / ((n : ℝ) + 2)) (εcut n) (Dcut n) (mcut n))
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
    (records : ∀ n, ∀ i : Fin (F.tower.history n).eventCount,
      GeometricCutoffRecord (F.tower.history n).toHistory i q)
    (hfixed : q.fixed = pBase.fixed) (hrc : q.recenterConstant = pBase.recenterConstant)
    (hmi : ∀ (m : ℕ) (i : Fin (S.state (m + 1)).native.eventCount) (n : ℕ),
      (S.state (m + 1)).native.time i.succ + (S.state (m + 1)).shift ≤ (n : ℝ) →
      ∃ j : Fin (F.tower.history n).eventCount,
        j.val = ((S.state (m + 1)).affine.eventIndex i).val ∧
        HEq (records n j).delta ((W m).fineRecords i).delta ∧
        HEq (records n j).order ((W m).fineRecords i).order ∧
        HEq (records n j).neck ((W m).fineRecords i).neck)
    (hblock : ∀ (n : ℕ) (j : Fin (F.tower.history n).eventCount),
      ∃ m : ℕ, ∃ i : Fin (S.state (m + 1)).native.eventCount,
        j.val = ((S.state (m + 1)).affine.eventIndex i).val ∧
        (F.tower.history n).time j.succ =
          (S.state (m + 1)).native.time i.succ + (S.state (m + 1)).shift ∧
        (F.tower.history n).time j.succ ≤ (3 : ℝ) ^ m ∧
        MetricCutCapEvent.SamePresentation
          (GC.GeneralFlow.translate_retained_event ((S.state (m + 1)).native.coreEvent i)
            (S.state (m + 1)).shift).toMetricCutCapEvent
          ((F.tower.history n).toHistory.event j) ∧
        ∀ b' : ((F.tower.history n).toHistory.event j).RetainedBoundaryIndex,
          ∃ (b : ((S.state (m + 1)).native.toHistory.event i).RetainedBoundaryIndex)
            (raw : ((F.tower.history n).toHistory.event j).PresentedStaticCap q.fixed
              (W m).fineParameters.modelRadius (W m).fineParameters.modelOrder
              (W m).fineParameters.modelAccuracy b'),
            HEq b b' ∧ raw.hasCanonicalWindow ∧
            raw.delta = (((W m).fineRecords i).static b).delta ∧
            raw.order = (((W m).fineRecords i).static b).order ∧
            HEq raw.neck (((W m).fineRecords i).static b).neck ∧
            raw.witness.windowMetric = (((W m).fineRecords i).static b).witness.windowMetric ∧
            raw.neck.scale = ((records n j).static b').neck.scale ∧
            (∀ z : ThreeBall, raw.inclusion (raw.witness.cap z) =
              ((records n j).static b').inclusion (((records n j).static b').witness.cap z)))
    (hcof : ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      D ≤ (W k).fineParameters.modelRadius ∧ (W k).fineParameters.modelAccuracy ≤ ζ ∧
        m ≤ (W k).fineParameters.modelOrder)
    (hlink : ∃ k₁ : ℕ, ∀ k, k₁ ≤ k → ∀ (i : Fin (S.state (k + 1)).native.eventCount) b,
      linkedCanonicalWindow_C11E (((W k).fineRecords i).static b)) :
    ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T : ℝ, ∀ n, ∃ p : CutoffParameters,
    p.delta = q.delta ∧ p.neckRadius = q.neckRadius ∧
    p.fixed = q.fixed ∧ p.recenterConstant = q.recenterConstant ∧
    D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
    ∃ records' : ∀ i : Fin (F.tower.history n).eventCount,
        T ≤ (F.tower.history n).time i.succ →
        GeometricCutoffRecord (F.tower.history n).toHistory i p,
      (∀ i hi b, linkedCanonicalWindow_C11E ((records' i hi).static b)) ∧
      ∀ i hi, (records' i hi).nominalRadius =
          (records n i).nominalRadius ∧
        (records' i hi).delta =
          (records n i).delta ∧
        (records' i hi).order =
          (records n i).order ∧
        (∀ α, HEq ((records' i hi).neck α) ((records n i).neck α)) ∧
        (∀ b, ((records' i hi).static b).neck.scale =
          ((records n i).static b).neck.scale) ∧
        ∀ (b) (z : ThreeBall),
          ((records' i hi).static b).inclusion
              (((records' i hi).static b).witness.cap z) =
            ((records n i).static b).inclusion
              (((records n i).static b).witness.cap z) := by
  intro D ζ m hζ
  obtain ⟨k₁, hk₁⟩ := hlink
  have hD'pos : 0 < max D (StandardCap.transitionEnd + 1) :=
    lt_max_of_lt_right (by linarith [StandardCap.transitionEnd_pos])
  have hcap : StandardCap.transitionEnd < max D (StandardCap.transitionEnd + 1) + 1 := by
    linarith [le_max_right D (StandardCap.transitionEnd + 1)]
  obtain ⟨k₀, hk₀⟩ := hcof (max D (StandardCap.transitionEnd + 1)) ζ m hζ
  refine ⟨(3 : ℝ) ^ max k₀ k₁, fun n => ⟨q.withModelWindow
    (max D (StandardCap.transitionEnd + 1)) m ζ hD'pos hζ, rfl, rfl, rfl, rfl,
    le_max_left _ _, le_rfl, le_rfl, ?_⟩⟩
  have hev : ∀ j : Fin (F.tower.history n).eventCount,
      (3 : ℝ) ^ max k₀ k₁ ≤ (F.tower.history n).time j.succ →
      ∃ R' : GeometricCutoffRecord (F.tower.history n).toHistory j
          (q.withModelWindow (max D (StandardCap.transitionEnd + 1)) m ζ hD'pos hζ),
        (∀ b, linkedCanonicalWindow_C11E (R'.static b)) ∧
        R'.nominalRadius =
          (records n j).nominalRadius ∧
        R'.delta =
          (records n j).delta ∧
        R'.order =
          (records n j).order ∧
        (∀ α, HEq (R'.neck α) ((records n j).neck α)) ∧
        (∀ b, (R'.static b).neck.scale =
          ((records n j).static b).neck.scale) ∧
        ∀ (b) (z : ThreeBall),
          (R'.static b).inclusion
              ((R'.static b).witness.cap z) =
            ((records n j).static b).inclusion
              (((records n j).static b).witness.cap z) := by
    intro j hj
    obtain ⟨mb, ib, hidx, htime, hle, hsame, hraw⟩ := hblock n j
    have hmb : max k₀ k₁ ≤ mb :=
      (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).mp (hj.trans hle)
    have hs : (S.state (mb + 1)).native.time ib.succ + (S.state (mb + 1)).shift ≤ (n : ℝ) := by
      rw [← htime]
      exact ((F.tower.history n).toHistory.time_le_horizon_at j.succ).trans_eq
        (F.tower.horizon_eq n)
    obtain ⟨j', hj', hδ, ho, hN⟩ := hmi mb ib n hs
    obtain rfl : j' = j := Fin.ext (hj'.trans hidx.symm)
    obtain ⟨hR, hA, hO⟩ := hk₀ mb (le_of_max_le_left hmb)
    exact exists_rewindowed_linked_record_nominal_P6NI (records n j') ((W mb).fineRecords ib) hsame
      hδ ho hN ((W mb).fine_fixed.trans hfixed.symm) ((W mb).fine_recenter.trans hrc.symm) hraw
      (hk₁ mb (le_of_max_le_right hmb) ib) hD'pos hcap hR hO hA
  choose R' hR' hrp using hev
  exact ⟨R', hR', hrp⟩

section Outer

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Neck GC.GeneralFlow
open scoped Manifold ContDiff

/-- **adapter（reparameterization 追踪版，`_P6NI`）**：同 `lateLinkedRecordsSupplyNom_of_astra_P6NI`，
`hmi / hblock` 换成 outer tuple
（`SH/PreparedSpatialPhysicalVolumeEvent:65` 的结论）里 m-i 子句（l.375–397）与 block 子句
（l.410–470）的全文（只重排换行）；outer 的消费者直接喂两个合取项。 -/
theorem lateLinkedRecordsSupplyNom_of_outer_P6NI {pBase : CutoffParameters}
    {C : ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g) {εcut Dcut : ℕ → ℝ} {mcut : ℕ → ℕ}
    (W : ∀ n, PreparedSpatialStepRetention (S.state n) (S.state (n + 1))
      (S.accuracy n) (1 / ((n : ℝ) + 2)) (εcut n) (Dcut n) (mcut n))
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
    (records : ∀ n, ∀ i : Fin (F.tower.history n).eventCount,
      GeometricCutoffRecord (F.tower.history n).toHistory i q)
    (hfixed : q.fixed = pBase.fixed) (hrc : q.recenterConstant = pBase.recenterConstant)
    (hmiOuter :
      (∀ m : ℕ, ∀ i : Fin (S.state (m + 1)).native.eventCount,
        let s := (S.state (m + 1)).native.time i.succ + (S.state (m + 1)).shift;
        s ∈ Ioc (preparedSpatialHorizon m) ((3 : ℝ) ^ m) ∧
        q.delta s = S.accuracy m ∧
        (∀ u : ℝ, s ≤ u → q.delta u ≤ S.accuracy m) ∧
        (∀ T : ℝ, T ∈ Icc s (2 * s) →
          (S.state (m + 1)).radius ≤ q.neckRadius T) ∧
        (∀ A : ℝ, 0 < A → q.delta s < S.diagonalLargerBallAccuracy A s →
          A < 12 * (3 : ℝ) ^ m) ∧
        ∀ n : ℕ, s ≤ (n : ℝ) →
        ∃ j : Fin (F.tower.history n).eventCount,
          j.val = ((S.state (m + 1)).affine.eventIndex i).val ∧
          (F.tower.history n).time j.succ = s ∧
          HEq (records n j).nominalRadius ((W m).fineRecords i).nominalRadius ∧
          HEq (records n j).delta ((W m).fineRecords i).delta ∧
          HEq (records n j).order ((W m).fineRecords i).order ∧
          HEq (records n j).neck ((W m).fineRecords i).neck ∧
          HEq (records n j).static
            (fun z => translate_presented_static_cap
              ((S.state (m + 1)).native.coreEvent i) (S.state (m + 1)).shift
              ((((W m).fineRecords i).restrictModelWindow ((W m).fineWindows i)
                (S.state m).parameters.modelRadius_pos
                (W m).full_radius (W m).full_order (W m).full_accuracy).static z))))
    (hblockOuter :
      (∀ (n : ℕ) (j : Fin (F.tower.history n).eventCount),
        ∃ m : ℕ, m ≤ n ∧ ∃ i : Fin (S.state (m + 1)).native.eventCount,
          (S.state m).history.eventCount ≤ j.val ∧
          j.val < (S.state (m + 1)).history.eventCount ∧
          j.val = ((S.state (m + 1)).affine.eventIndex i).val ∧
          (F.tower.history n).time j.succ =
            (S.state (m + 1)).native.time i.succ + (S.state (m + 1)).shift ∧
          (F.tower.history n).time j.succ ∈
            Ioc (preparedSpatialHorizon m) ((3 : ℝ) ^ m) ∧
          ((translate_retained_event ((S.state (m + 1)).native.coreEvent i)
            (S.state (m + 1)).shift).toMetricCutCapEvent).SamePresentation
              ((F.tower.history n).toHistory.event j) ∧
          q.delta ((F.tower.history n).time j.succ) = S.accuracy m ∧
          Dcut m ≤ (W m).fineParameters.modelRadius ∧
          mcut m ≤ (W m).fineParameters.modelOrder ∧
          (W m).fineParameters.modelAccuracy ≤ εcut m ∧
          ∀ b' : ((F.tower.history n).toHistory.event j).RetainedBoundaryIndex,
            ∃ (b : ((S.state (m + 1)).native.toHistory.event i).RetainedBoundaryIndex)
              (raw : ((F.tower.history n).toHistory.event j).PresentedStaticCap q.fixed
                (W m).fineParameters.modelRadius (W m).fineParameters.modelOrder
                  (W m).fineParameters.modelAccuracy b'),
              HEq b b' ∧ raw.hasCanonicalWindow ∧
              raw.delta = (((W m).fineRecords i).static b).delta ∧ raw.order =
                (((W m).fineRecords i).static b).order ∧
              HEq raw.neck (((W m).fineRecords i).static b).neck ∧
              HEq raw.witness (((W m).fineRecords i).static b).witness ∧
              raw.witness.Output = (((W m).fineRecords i).static b).witness.Output ∧
              HEq raw.witness.metric (((W m).fineRecords i).static b).witness.metric ∧
              HEq raw.inclusion (((W m).fineRecords i).static b).inclusion ∧
              HEq raw.witness.cap (((W m).fineRecords i).static b).witness.cap ∧
              HEq raw.witness.retained (((W m).fineRecords i).static b).witness.retained ∧
              HEq raw.witness.collapse (((W m).fineRecords i).static b).witness.collapse ∧
              raw.witness.windowMetric = (((W m).fineRecords i).static b).witness.windowMetric ∧
              (∀ x : standardCapWindow (W m).fineParameters.modelRadius,
                HEq (raw.window x) ((((W m).fineRecords i).static b).window x)) ∧
              raw.neck.scale = ((records n j).static b').neck.scale ∧
              (∀ z : ThreeBall,
                raw.inclusion (raw.witness.cap z) =
                  ((records n j).static b').inclusion (((records n j).static b').witness.cap z)) ∧
              (∀ (z : ThreeBall) (y : ((F.tower.history n).stage j.succ).Carrier),
                ((F.tower.history n).toHistory.event j).transition.trace.presentation
                  (((F.tower.history n).toHistory.event j).transition.trace.capping.cap b'.val z) =
                    Sum.inl y →
                raw.inclusion (raw.witness.cap z) = y) ∧
              (∀ x (v z : TangentSpace ThreeModel x), raw.witness.metric.inner x v z =
                ((F.tower.history n).initialMetric j.succ).inner (raw.inclusion x)
                  (mfderiv ThreeModel ThreeModel raw.inclusion x v)
                  (mfderiv ThreeModel ThreeModel raw.inclusion x z)) ∧
              ∃ (x₀ : ((S.state (m + 1)).native.toHistory.event i).incoming.terminalRegularOpen)
                (δ : ℝ) (k : ℕ)
                (d : normalizedDatum ((S.state (m + 1)).native.toHistory.event i).terminal.metric
                  x₀ δ k)
                (w : StandardCap.CanonicalStaticInsertionWitness d
                  (W m).fineParameters.fixed.collarLength (W m).fineParameters.fixed.collar_pos
                  (W m).fineParameters.modelRadius (W m).fineParameters.modelOrder
                    (W m).fineParameters.modelAccuracy),
                metricScalarAt ((S.state (m + 1)).native.toHistory.event i).terminal.metric x₀ =
                  raw.neck.scale ∧
                (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
                  raw.neck.scale * ((S.state (m + 1)).native.toHistory.event i).outputMetric.inner
                    ((((W m).fineRecords i).static b).window x)
                    (mfderiv ThreeModel ThreeModel (((W m).fineRecords i).static b).window x v)
                    (mfderiv ThreeModel ThreeModel (((W m).fineRecords i).static b).window x z)) ∧
                (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
                  raw.neck.scale * ((F.tower.history n).initialMetric j.succ).inner (raw.window x)
                    (mfderiv ThreeModel ThreeModel raw.window x v)
                    (mfderiv ThreeModel ThreeModel raw.window x z)) ∧
                ∀ z : ThreeBall, ∃ x : standardCapWindow (W m).fineParameters.modelRadius,
                  ‖x.val‖ ≤ StandardCap.transitionEnd ∧
                  raw.window x = raw.inclusion (raw.witness.cap z)))
    (hcof : ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      D ≤ (W k).fineParameters.modelRadius ∧ (W k).fineParameters.modelAccuracy ≤ ζ ∧
        m ≤ (W k).fineParameters.modelOrder)
    (hlink : ∃ k₁ : ℕ, ∀ k, k₁ ≤ k → ∀ (i : Fin (S.state (k + 1)).native.eventCount) b,
      linkedCanonicalWindow_C11E (((W k).fineRecords i).static b)) :
    ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T : ℝ, ∀ n, ∃ p : CutoffParameters,
    p.delta = q.delta ∧ p.neckRadius = q.neckRadius ∧
    p.fixed = q.fixed ∧ p.recenterConstant = q.recenterConstant ∧
    D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
    ∃ records' : ∀ i : Fin (F.tower.history n).eventCount,
        T ≤ (F.tower.history n).time i.succ →
        GeometricCutoffRecord (F.tower.history n).toHistory i p,
      (∀ i hi b, linkedCanonicalWindow_C11E ((records' i hi).static b)) ∧
      ∀ i hi, (records' i hi).nominalRadius =
          (records n i).nominalRadius ∧
        (records' i hi).delta =
          (records n i).delta ∧
        (records' i hi).order =
          (records n i).order ∧
        (∀ α, HEq ((records' i hi).neck α) ((records n i).neck α)) ∧
        (∀ b, ((records' i hi).static b).neck.scale =
          ((records n i).static b).neck.scale) ∧
        ∀ (b) (z : ThreeBall),
          ((records' i hi).static b).inclusion
              (((records' i hi).static b).witness.cap z) =
            ((records n i).static b).inclusion
              (((records n i).static b).witness.cap z) := by
  refine lateLinkedRecordsSupplyNom_of_astra_P6NI S W F q records hfixed hrc ?_ ?_ hcof hlink
  · intro m i n hs
    obtain ⟨-, -, -, -, -, h⟩ := hmiOuter m i
    obtain ⟨j, hj, -, -, hδ, ho, hN, -⟩ := h n hs
    exact ⟨j, hj, hδ, ho, hN⟩
  · intro n j
    obtain ⟨m, -, i, -, -, hidx, htime, hIoc, hsame, -, -, -, -, hraw⟩ := hblockOuter n j
    refine ⟨m, i, hidx, htime, hIoc.2, hsame, fun b' => ?_⟩
    obtain ⟨b, raw, hb, hcan, hd, ho, hn, -, -, -, -, -, -, -, hwm, -, hsc, hci, -⟩ := hraw b'
    exact ⟨b, raw, hb, hcan, hd, ho, hn, hwm, hsc, hci⟩

end Outer

end GC.LongTime.Ch11
