import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GuardNeckedRayCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ConeEndRayScalarBound
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Nonnegative

/-!
# SPINE-A1 G1：guard 分支 necked missing ray → punctured cone end

CODEX-C §3.3 路线 1。G60 `exists_guard_necked_missing_ray_CXSP` 的十条合取（`Pl` 曲率算子
非负、有限缺端 isometric ray、沿 ray scalar → ∞、末端 `SpatialNeck (1/4000000)`）经树内
`exists_punctured_cone_end_of_spatial_necks_with_ray_scalar_bound`
（`Surgery/Topology/ConeEndRayScalarBound.lean`，即 `Geometry/Neck/FiniteEnd.lean:1078` 加 ray
scalar 比较）产 punctured cone end。binder 对照：
* `hsec` ← 曲率算子非负经树内 iff
  `metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff_sectional`
  （`DimensionThree/CurvatureOperator/Nonnegative.lean:13`；(A-1) 不发生）；
* `[MetricSpace Pl.M]` = `EMetricSpace.toMetricSpace`（有限性由 radial 界 + 三角不等式），
  `hmetric` 为 `rfl`（模板 `BoundedCurvatureAtDistanceBoundedThreshold.lean:858–867`）；
* completion endpoint ← `exists_completion_endpoint_of_isometry`。
输出改写成 `RetainedCoreHistory.final_slab_punctured_cone_end_exclusion_of_trace_chains_P6L`
（`Local/BoundedCurvatureAtDistanceTracedCone_P6L.lean:575`）的 `W` / scalar 形（SPINE-A2 消费）。
不消费 TimeCore / hw / Budget / SCRS⁺；不经 RegularSlice。
-/

set_option autoImplicit false
noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

/-- 与 P6L 同款：pointed limit 的 `RegularSpace`（W 形 `MetricSpace.ofT0PseudoMetricSpace` 需要）。 -/
private local instance pointedLimitRegular_C11SP
    (L : PointedRiemannianManifold.{u, 0, 0} ThreeModel) : RegularSpace L.M := by
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace ThreeSpace L.M
  infer_instance

/-- 泛型 bridge：曲率算子非负 + isometric necked ray（scalar → ∞）⇒ completion endpoint 与
punctured cone end（含 ray scalar ratio）。 -/
theorem coneEnd_of_operatorNonneg_neckedRay_C11SP
    {M : Type u} [MetricSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (metric : SmoothRiemannianMetric ThreeModel M)
    (hmetric : ∀ a b : M, edist a b = riemannianEDistOf metric a b)
    (hnonnegative : ∀ z : M, metricAlgebraicCurvatureTensorAt metric z ∈
      algebraicCurvatureOperatorNonnegativeCone)
    {b : ℝ} (hb : 0 < b) (ray : C(Ico (0 : ℝ) b, M)) (hray : Isometry ray)
    (hblow : Tendsto (fun v => metricScalarAt metric (ray v))
      (comap (Subtype.val : Ico (0 : ℝ) b → ℝ) (𝓝 b)) atTop)
    (hnecks : ∀ᶠ v : Ico (0 : ℝ) b in
        comap (Subtype.val : Ico (0 : ℝ) b → ℝ) (𝓝 b),
      Nonempty (SpatialNeck metric (1 / 4000000) (ray v))) :
    ∃ qc : UniformSpace.Completion M,
      Tendsto (fun v => (ray v : UniformSpace.Completion M))
        (comap (Subtype.val : Ico (0 : ℝ) b → ℝ) (𝓝 b)) (𝓝 qc) ∧
    ∃ W : TopologicalSpace.Opens M, ∃ hW : PathConnectedSpace W,
      let _ : PathConnectedSpace W := hW
      let mW : MetricSpace W :=
        let _ : PseudoMetricSpace W := (metric.restrictOpen W).toPseudoMetricSpace
        MetricSpace.ofT0PseudoMetricSpace W
      let _ : MetricSpace W := mW
      let _ : PseudoMetricSpace W := mW.toPseudoMetricSpace
      let _ : UniformSpace W := mW.toPseudoMetricSpace.toUniformSpace
      let eW : PseudoEMetricSpace W :=
        @PseudoMetricSpace.toPseudoEMetricSpace W mW.toPseudoMetricSpace
      let _ : WeakPseudoEMetricSpace W :=
        @PseudoEMetricSpace.toWeakPseudoEMetricSpace W eW
      ∃ qW : UniformSpace.Completion W, ∃ delta : ℝ, 0 < delta ∧
        qW ∉ range (fun x : W => (x : UniformSpace.Completion W)) ∧
        UniformSpace.Completion.map (Subtype.val : W → M) qW = qc ∧
        IsCompact (Metric.closedBall qW delta) ∧
        Metric.closedBall qW delta ⊆ insert qW
          (range (fun x : W => (x : UniformSpace.Completion W))) ∧
        ∃ x : ℕ → W, ∃ times : ℕ → Ico 0 b,
          (∀ n, (x n : M) = ray (times n)) ∧
          Tendsto (fun n => (times n : ℝ)) atTop (𝓝 b) ∧
          Tendsto (fun n => (x n : UniformSpace.Completion W)) atTop (𝓝 qW) ∧
          (∀ n, dist (x n : UniformSpace.Completion W) qW = b - times n) ∧
          Tendsto (fun n => metricScalarAt (metric.restrictOpen W) (x n)) atTop atTop ∧
          (∀ n, ((2 * (1 / 4000000 : ℝ))⁻¹) ^ 2 / 8 ≤
            metricScalarAt (metric.restrictOpen W) (x n) *
              dist (x n : UniformSpace.Completion W) qW ^ 2) ∧
          (∃ B : ℝ, 0 < B ∧ ∀ᶠ n in atTop,
            metricScalarAt (metric.restrictOpen W) (x n) *
              dist (x n : UniformSpace.Completion W) qW ^ 2 ≤ B) ∧
          Nonempty (DifferentialGeometry.Toponogov.PuncturedConeApproximation qW delta) ∧
          ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ n in atTop, ∀ s : Ico 0 b, (s : ℝ) ≤ times n →
            metricScalarAt metric (ray s) ≤ K * metricScalarAt metric (ray (times n)) := by
  have hsec : ∀ (z : M) (v w : TangentSpace ThreeModel z),
      0 ≤ metricRm04StandardAt metric z v w w v := by
    intro z v w
    exact (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff_sectional
      metric z (by simp [ThreeSpace])).mp (hnonnegative z) v w
  obtain ⟨qc, hqc, _⟩ := Geometry.exists_completion_endpoint_of_isometry hb hray
  exact ⟨qc, hqc,
    exists_punctured_cone_end_of_spatial_necks_with_ray_scalar_bound metric hmetric hb
      (by norm_num) (by norm_num) hsec ray hray hblow qc hqc hnecks⟩

/-- **SPINE-A1 G1**（SPINE-A2 的 (III) 形）：G60 的十条合取 ⇒ `Pl` 上的 punctured cone end，
写成 P6L:575 的 `W` / `Pl.metric` scalar 形。 -/
theorem guard_puncturedConeEnd_C11SP :
    ∀ (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel) (rho : ℝ) (hrho : 0 < rho)
      (ray : C(Ico (0 : ℝ) rho, Pl.M)),
      (let _ : EMetricSpace Pl.M := Pl.emetricSpace;
        metricScalarAt Pl.metric Pl.basepoint = 1 ∧
        (∀ z : Pl.M, metricAlgebraicCurvatureTensorAt Pl.metric z ∈
          algebraicCurvatureOperatorNonnegativeCone) ∧
        (∀ y : Pl.M, riemannianEDistOf Pl.metric Pl.basepoint y < ENNReal.ofReal rho) ∧
        (∀ R : ℝ, 0 ≤ R → R < rho →
          IsCompact (riemannianClosedBallOf Pl.metric Pl.basepoint R)) ∧
        Isometry ray ∧ ray ⟨0, le_rfl, hrho⟩ = Pl.basepoint ∧
        Tendsto ray (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho))
          (cocompact Pl.M) ∧
        (∀ y : Pl.M, ¬ Tendsto ray
          (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho)) (𝓝 y)) ∧
        Tendsto (fun v => metricScalarAt Pl.metric (ray v))
          (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho)) atTop ∧
        ∀ᶠ v : Ico (0 : ℝ) rho in
            comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho),
          Nonempty (SpatialNeck Pl.metric (1 / 4000000) (ray v))) →
    ∃ W : TopologicalSpace.Opens Pl.M, ∃ hWc : PathConnectedSpace W,
      let _ : PathConnectedSpace W := hWc
      let _ : PseudoMetricSpace W := (Pl.metric.restrictOpen W).toPseudoMetricSpace
      let _ : MetricSpace W := MetricSpace.ofT0PseudoMetricSpace W
      ∃ (qW : UniformSpace.Completion W) (delta : ℝ), 0 < delta ∧
        IsCompact (Metric.closedBall qW delta) ∧
        Metric.closedBall qW delta ⊆
          insert qW (range (fun z : W => (z : UniformSpace.Completion W))) ∧
        Nonempty (DifferentialGeometry.Toponogov.PuncturedConeApproximation qW delta) ∧
        ∃ xW : ℕ → W, Tendsto (fun n => (xW n : UniformSpace.Completion W)) atTop (𝓝 qW) ∧
          Tendsto (fun n => metricScalarAt Pl.metric (xW n : Pl.M)) atTop atTop ∧
          ∃ c : ℝ, 0 < c ∧
            (∀ᶠ n in atTop, c ≤ metricScalarAt Pl.metric (xW n : Pl.M) *
              dist (xW n : UniformSpace.Completion W) qW ^ 2) ∧
            ∃ B : ℝ, ∀ᶠ n in atTop, metricScalarAt Pl.metric (xW n : Pl.M) *
              dist (xW n : UniformSpace.Completion W) qW ^ 2 ≤ B := by
  intro Pl rho hrho ray h
  let _ : EMetricSpace Pl.M := Pl.emetricSpace
  obtain ⟨_hbase, hnonneg, hradial, _hcompact, hray, _hray0, _hcoc, _hmiss, hblow,
    hnecks⟩ := h
  have hfin : ∀ a b : Pl.M, edist a b ≠ ⊤ := by
    intro a b
    apply ne_top_of_le_ne_top _ (edist_triangle_left a b Pl.basepoint)
    exact ENNReal.add_ne_top.mpr ⟨(hradial a).ne_top, (hradial b).ne_top⟩
  let _ : MetricSpace Pl.M := EMetricSpace.toMetricSpace hfin
  obtain ⟨_qc, _hqc, W, hWc, hrest⟩ := coneEnd_of_operatorNonneg_neckedRay_C11SP Pl.metric
    (fun _ _ => rfl) hnonneg hrho ray hray hblow hnecks
  let _ : PathConnectedSpace W := hWc
  let mW : MetricSpace W :=
    let _ : PseudoMetricSpace W := (Pl.metric.restrictOpen W).toPseudoMetricSpace
    MetricSpace.ofT0PseudoMetricSpace W
  let _ : MetricSpace W := mW
  let _ : PseudoMetricSpace W := mW.toPseudoMetricSpace
  let _ : UniformSpace W := mW.toPseudoMetricSpace.toUniformSpace
  let eW : PseudoEMetricSpace W :=
    @PseudoMetricSpace.toPseudoEMetricSpace W mW.toPseudoMetricSpace
  let _ : WeakPseudoEMetricSpace W :=
    @PseudoEMetricSpace.toWeakPseudoEMetricSpace W eW
  obtain ⟨qW, delta, hdelta, _, _, hK, hcover, xW, _, _, _, hxW, _, hQW, hlowerW, hupperW,
    hcone, _⟩ := hrest
  have hQW' : Tendsto (fun n => metricScalarAt Pl.metric (xW n : Pl.M)) atTop atTop := by
    simpa only [metricScalarAt_restrictOpen] using hQW
  have hlower' : ∀ᶠ n in atTop, ((2 * (1 / 4000000 : ℝ))⁻¹) ^ 2 / 8 ≤
      metricScalarAt Pl.metric (xW n : Pl.M) *
        dist (xW n : UniformSpace.Completion W) qW ^ 2 :=
    Eventually.of_forall fun n => by simpa only [metricScalarAt_restrictOpen] using hlowerW n
  have hupper' : ∃ B : ℝ, ∀ᶠ n in atTop, metricScalarAt Pl.metric (xW n : Pl.M) *
      dist (xW n : UniformSpace.Completion W) qW ^ 2 ≤ B := by
    obtain ⟨B, _, hB⟩ := hupperW
    exact ⟨B, by simpa only [metricScalarAt_restrictOpen] using hB⟩
  exact ⟨W, hWc, qW, delta, hdelta, hK, hcover, hcone, xW, hxW, hQW',
    ((2 * (1 / 4000000 : ℝ))⁻¹) ^ 2 / 8, by norm_num, hlower', hupper'⟩

/-- G1 的 SPINE-A2 v2 形（`hconeA1`，`P6GuardExcludeC11SP.lean:314–349`）：ray 在前件里存在量化，
W 形结论在 `EMetricSpace` let 之外。 -/
theorem guard_puncturedConeEnd_v2_C11SP :
    ∀ (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel) (rho : ℝ)
      (hrho : 0 < rho),
      (let _ : EMetricSpace Pl.M := Pl.emetricSpace
       ∃ ray : C(Ico (0 : ℝ) rho, Pl.M),
        metricScalarAt Pl.metric Pl.basepoint = 1 ∧
        (∀ z : Pl.M, metricAlgebraicCurvatureTensorAt Pl.metric z ∈
          algebraicCurvatureOperatorNonnegativeCone) ∧
        (∀ y : Pl.M, riemannianEDistOf Pl.metric Pl.basepoint y < ENNReal.ofReal rho) ∧
        (∀ R : ℝ, 0 ≤ R → R < rho →
          IsCompact (riemannianClosedBallOf Pl.metric Pl.basepoint R)) ∧
        Isometry ray ∧ ray ⟨0, le_rfl, hrho⟩ = Pl.basepoint ∧
        Tendsto ray (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho))
          (cocompact Pl.M) ∧
        (∀ y : Pl.M, ¬ Tendsto ray
          (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho)) (𝓝 y)) ∧
        Tendsto (fun v => metricScalarAt Pl.metric (ray v))
          (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho)) atTop ∧
        ∀ᶠ v : Ico (0 : ℝ) rho in
            comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho),
          Nonempty (SpatialNeck Pl.metric (1 / 4000000) (ray v))) →
      ∃ W : TopologicalSpace.Opens Pl.M, ∃ hWc : PathConnectedSpace W,
        let _ : PathConnectedSpace W := hWc
        let _ : PseudoMetricSpace W := (Pl.metric.restrictOpen W).toPseudoMetricSpace
        let _ : MetricSpace W := MetricSpace.ofT0PseudoMetricSpace W
        ∃ (qW : UniformSpace.Completion W) (delta : ℝ), 0 < delta ∧
          IsCompact (Metric.closedBall qW delta) ∧
          Metric.closedBall qW delta ⊆
            insert qW (range (fun z : W => (z : UniformSpace.Completion W))) ∧
          Nonempty (DifferentialGeometry.Toponogov.PuncturedConeApproximation qW delta) ∧
          ∃ xW : ℕ → W, Tendsto (fun n => (xW n : UniformSpace.Completion W)) atTop (𝓝 qW) ∧
            Tendsto (fun n => metricScalarAt Pl.metric (xW n : Pl.M)) atTop atTop ∧
            ∃ c : ℝ, 0 < c ∧
              (∀ᶠ n in atTop, c ≤ metricScalarAt Pl.metric (xW n : Pl.M) *
                dist (xW n : UniformSpace.Completion W) qW ^ 2) ∧
              ∃ B : ℝ, ∀ᶠ n in atTop, metricScalarAt Pl.metric (xW n : Pl.M) *
                dist (xW n : UniformSpace.Completion W) qW ^ 2 ≤ B := by
  intro Pl rho hrho h
  obtain ⟨ray, hten⟩ := h
  exact guard_puncturedConeEnd_C11SP Pl rho hrho ray hten

/-- G1 consumer（序列级）：原 guard 坏序列（G60 前提）⇒ 同一 `Pl` 上 necked ray 的十条合取与
punctured cone end（G1 的 W 形）。`ε₀`、`Hbase` 原样取自 G60。 -/
theorem guard_neckedRay_coneEnd_C11SP
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder → CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
        ε ≤ coneAccuracy →
      ∀ A : ℝ, 0 < A → ∃ Hbase : ℝ, 4 ≤ Hbase ∧
      ∀ idx : ℕ → ℕ,
      let H : ℕ → ObservedHistory.{u} := fun i => (F.tower.history (idx i)).toHistory
      ∀ (t : ∀ i, Icc (0 : ℝ) (H i).horizon)
        (p x : ∀ i, ((H i).stageAt (t i)).Carrier) (r : ℕ → ℝ),
        (∀ i, 2 * r i ^ 2 < (t i : ℝ)) →
        (∀ i, hasSmallParabolicCurvature (H i) (t i) (p i) (r i)) →
        (∀ i, ENNReal.ofReal (A⁻¹ * r i ^ 3) ≤
          ballVolume ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (r i)) →
        (∀ i, x i ∈ riemannianBallOf
          ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (A * r i)) →
        Tendsto (fun i => (t i : ℝ)) atTop atTop →
        Tendsto (fun i => metricScalarAt
          ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (x i) * r i ^ 2) atTop atTop →
        (∀ i, q.neckRadius (t i) ≤ r i) →
        Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0) →
      ∃ (rho : ℝ) (hrho : 0 < rho), rho + 2 ≤ A * Real.sqrt Hbase + 3 ∧
        ∃ Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel,
        ∃ ray : C(Ico (0 : ℝ) rho, Pl.M),
          (let _ : EMetricSpace Pl.M := Pl.emetricSpace;
          metricScalarAt Pl.metric Pl.basepoint = 1 ∧
          (∀ z : Pl.M, metricAlgebraicCurvatureTensorAt Pl.metric z ∈
            algebraicCurvatureOperatorNonnegativeCone) ∧
          (∀ y : Pl.M, riemannianEDistOf Pl.metric Pl.basepoint y < ENNReal.ofReal rho) ∧
          (∀ R : ℝ, 0 ≤ R → R < rho →
            IsCompact (riemannianClosedBallOf Pl.metric Pl.basepoint R)) ∧
          Isometry ray ∧ ray ⟨0, le_rfl, hrho⟩ = Pl.basepoint ∧
          Tendsto ray (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho))
            (cocompact Pl.M) ∧
          (∀ y : Pl.M, ¬ Tendsto ray
            (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho)) (𝓝 y)) ∧
          Tendsto (fun v => metricScalarAt Pl.metric (ray v))
            (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho)) atTop ∧
          ∀ᶠ v : Ico (0 : ℝ) rho in
              comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho),
            Nonempty (SpatialNeck Pl.metric (1 / 4000000) (ray v))) ∧
          ∃ W : TopologicalSpace.Opens Pl.M, ∃ hWc : PathConnectedSpace W,
            let _ : PathConnectedSpace W := hWc
            let _ : PseudoMetricSpace W := (Pl.metric.restrictOpen W).toPseudoMetricSpace
            let _ : MetricSpace W := MetricSpace.ofT0PseudoMetricSpace W
            ∃ (qW : UniformSpace.Completion W) (delta : ℝ), 0 < delta ∧
              IsCompact (Metric.closedBall qW delta) ∧
              Metric.closedBall qW delta ⊆
                insert qW (range (fun z : W => (z : UniformSpace.Completion W))) ∧
              Nonempty (DifferentialGeometry.Toponogov.PuncturedConeApproximation qW delta) ∧
              ∃ xW : ℕ → W,
                Tendsto (fun n => (xW n : UniformSpace.Completion W)) atTop (𝓝 qW) ∧
                Tendsto (fun n => metricScalarAt Pl.metric (xW n : Pl.M)) atTop atTop ∧
                ∃ c : ℝ, 0 < c ∧
                  (∀ᶠ n in atTop, c ≤ metricScalarAt Pl.metric (xW n : Pl.M) *
                    dist (xW n : UniformSpace.Completion W) qW ^ 2) ∧
                  ∃ B : ℝ, ∀ᶠ n in atTop, metricScalarAt Pl.metric (xW n : Pl.M) *
                    dist (xW n : UniformSpace.Completion W) qW ^ 2 ≤ B := by
  obtain ⟨ε₀, hε₀, hray⟩ := exists_guard_necked_missing_ray_CXSP P g
  refine ⟨ε₀, hε₀, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hb hε A hA
  obtain ⟨Hbase, hHbase, hseq⟩ := hray S F q hTower hdiag hacc hrad hord hb hε A hA
  refine ⟨Hbase, hHbase, ?_⟩
  intro idx H t p x r htime hsmall hvol hx htlim hbad hguard hratio
  obtain ⟨rho, hrho, hbound, Pl, ray, hten⟩ :=
    hseq idx t p x r htime hsmall hvol hx htlim hbad hguard hratio
  exact ⟨rho, hrho, hbound, Pl, ray, hten, guard_puncturedConeEnd_C11SP Pl rho hrho ray hten⟩

end GC.LongTime.Ch11
