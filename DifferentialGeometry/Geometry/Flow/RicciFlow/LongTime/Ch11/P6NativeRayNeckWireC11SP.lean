import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeRayNeckSegC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeRayNeckBridgeC11SP

set_option autoImplicit false

/-!
# G4：ray neck 接线（O-CH11-NATIVE-RAYNECK，后缀 `_C11SP`）

G3 把 G1 桥合同对任意 tower 号证掉之后：
* `rayNeck_of_segment_slices_C11SP`：G2 主定理只剩 hseg（G56 段数据）+ slices + `nr⁻² ≤ Q`。
* `hneckRaySeg_C11SP`（**PROVED**）：NATIVE-NJ `hneckRay` 的孪生 `hneckRay′`（加 `s` 与段数据前提）。
  NJ 链在 `hneckRay` 的唯一调用处（A2 `guard_flowAtConePoints_C11SP` 体末 `filter_upwards`）
  改喂 `hneckRay′`：`s` 沿 `idx ∘ φ ∘ ind` 带过来，段数据 = 同处 G56 obtain（注意 G56 的 ray
  收敛在 `ψ` 子列，Phi 取 `maps0.compSubseq ψ`）。
* `hPlN'_of_PlSegSlices_C11SP` / `native_hnzero_of_PlSegSlices_C11SP`：G4 `hPlN′` 的 (b)
  只剩 slices + 段数据。
-/

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

/-- **G4a（PROVISIONAL[hseg, slices, hQnr]）**：G2 主定理去掉 G1 桥合同（G3 对任意 tower 号支付）。 -/
theorem rayNeck_of_segment_slices_C11SP
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {pBase : CutoffParameters} {Γf : ClosedBirthConstants} {C1 C2 : ℝ}
    (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
    (hTower : F.tower = S.tower) (q : CutoffParameters)
    (hdiag : ∀ t : ℝ, 0 ≤ t → q.neckRadius t = (chainDiagonal_C11A S).neckRadius t)
    (hC1 : C1ceil_C11SC.{u} Γf ≤ C1) (hC2 : C2ceil_C11SC.{u} Γf ≤ C2)
    (idx : ℕ → ℕ) (t : ∀ i, Icc (0 : ℝ) (F.tower.history (idx i)).toHistory.horizon)
    (anchor : ∀ i, ((F.tower.history (idx i)).toHistory.stageAt (t i)).Carrier)
    (htlim : Tendsto (fun i => (t i : ℝ)) atTop atTop)
    (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i) (hQnr : ∀ i, (q.neckRadius (t i) ^ 2)⁻¹ ≤ Q i)
    (sl : ℕ → RegularSlice F.observation) (hsl : ∀ i, (sl i).time = (t i : ℝ))
    (f : ℕ → ℕ) (hf : StrictMono f) (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (Phi : PointedRiemannianConvergenceMaps
      ({ obj := fun i =>
          { M := ((F.tower.history (idx i)).toHistory.stageAt (t i)).Carrier
            basepoint := anchor i
            metric := scaleMetric (Q i) (hQ i)
              ((F.tower.history (idx i)).toHistory.stageMetric
                ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) } } :
        PointedRiemannianSeq.{u, 0, 0} ThreeModel) Pl f)
    (M : MetricConvergenceData Phi)
    (hcanonical : ∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData Phi n)
    {rho : ℝ} (hrho : 0 < rho) (ray : Ico (0 : ℝ) rho → Pl.M)
    (hblow : Tendsto (fun v => metricScalarAt Pl.metric (ray v))
      (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho)) atTop)
    (ell : ℕ → ℝ)
    (γ : ∀ n, ℝ → ((F.tower.history (idx (f n))).toHistory.stageAt (t (f n))).Carrier)
    (hell : Tendsto ell atTop (𝓝 rho))
    (hmin : ∀ n, ∀ v ∈ Icc (0 : ℝ) (ell n), ∀ w ∈ Icc (0 : ℝ) (ell n),
      riemannianEDistOf (scaleMetric (Q (f n)) (hQ (f n))
        ((F.tower.history (idx (f n))).toHistory.stageMetric
          ((F.tower.history (idx (f n))).toHistory.activeStage (t (f n))) (t (f n))))
        (γ n v) (γ n w) = ENNReal.ofReal |v - w|)
    (hstay : ∀ v : Ico (0 : ℝ) rho, ∀ᶠ n in atTop, γ n v ∈ Phi.target n)
    (hconv : ∀ v : Ico (0 : ℝ) rho,
      Tendsto (fun n => (Phi.partialDiffeomorph n).symm (γ n v)) atTop (𝓝 (ray v)))
    (hhigh : Tendsto (fun n => metricScalarAt
      ((F.tower.history (idx (f n))).toHistory.stageMetric
        ((F.tower.history (idx (f n))).toHistory.activeStage (t (f n))) (t (f n)))
      (γ n (ell n)) / Q (f n)) atTop atTop) :
    ∀ times : ℕ → Ico (0 : ℝ) rho, Tendsto (fun n => (times n : ℝ)) atTop (𝓝 rho) →
      ∀ᶠ m in atTop, ∀ᶠ i in atTop,
        (F.tower.history (idx (f i))).toHistory.isTracedRegion (t (f i))
          (Phi.map i (ray (times m)))
          (1 / (2 * Real.sqrt (metricScalarAt
            ((F.tower.history (idx (f i))).toHistory.stageMetric
              ((F.tower.history (idx (f i))).toHistory.activeStage (t (f i))) (t (f i)))
            (Phi.map i (ray (times m))))))
          (metricScalarAt ((F.tower.history (idx (f i))).toHistory.stageMetric
              ((F.tower.history (idx (f i))).toHistory.activeStage (t (f i))) (t (f i)))
            (Phi.map i (ray (times m))))⁻¹
          (1200 * metricScalarAt ((F.tower.history (idx (f i))).toHistory.stageMetric
              ((F.tower.history (idx (f i))).toHistory.activeStage (t (f i))) (t (f i)))
            (Phi.map i (ray (times m)))) :=
  rayNeck_of_segment_C11SP S F hTower q hdiag hC1 hC2 idx t anchor htlim Q hQ hQnr sl hsl
    (sliceTowerTraceAt_seq_C11SP F idx t sl hsl) f hf Pl Phi M hcanonical hrho ray hblow ell γ hell
    hmin hstay hconv hhigh

/-- **G4b（PROVED）**：NATIVE-NJ `hneckRay`（`P6NativeFlowProduceC11SP.lean:88–144`）的孪生 `hneckRay′`：
前提加 slice `s`（`(s i).time = t i`）与该 ray 的 G56 段数据（沿 `Phi` 指标），结论逐字。
不再有 binder：桥由 G3、near-G33 + G47 由 G2、`nr⁻² ≤ Q` 由 `r < nr` 与 `4 ≤ Hbase`。 -/
theorem hneckRaySeg_C11SP (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧
        ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
          {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
          (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
          (q : CutoffParameters), F.tower = S.tower →
          (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
            q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
          pBase.modelAccuracy ≤ ε₁ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
          2 ≤ pBase.modelOrder → CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
        ∀ A : ℝ, 0 < A → ∀ Hbase : ℝ, 4 ≤ Hbase → ∀ rho : ℝ, 0 < rho →
          rho + 2 ≤ A * Real.sqrt Hbase + 3 →
        ∀ (idx : ℕ → ℕ)
          (t : ∀ i, Icc (0 : ℝ) (F.tower.history (idx i)).toHistory.horizon)
          (s : ℕ → RegularSlice F.observation)
          (p anchor : ∀ i, ((F.tower.history (idx i)).toHistory.stageAt (t i)).Carrier)
          (r : ℕ → ℝ), (∀ i, (s i).time = (t i : ℝ)) → (∀ i, 0 < r i) →
          Tendsto (fun i => (t i : ℝ)) atTop atTop →
          (∀ i, 2 * r i ^ 2 < (t i : ℝ)) →
          (∀ i, hasSmallParabolicCurvature (F.tower.history (idx i)).toHistory (t i) (p i) (r i)) →
          (∀ i, ENNReal.ofReal (A⁻¹ * r i ^ 3) ≤
            ballVolume ((F.tower.history (idx i)).toHistory.stageMetric
              ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (p i) (r i)) →
          (∀ i, r i < q.neckRadius (t i)) →
          (∀ i, riemannianEDistOf ((F.tower.history (idx i)).toHistory.stageMetric
              ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (p i) (anchor i) ≤
            ENNReal.ofReal (A * r i)) →
        ∀ (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i), (∀ i, Q i = Hbase * (r i ^ 2)⁻¹) →
        ∀ (f : ℕ → ℕ), StrictMono f →
        ∀ (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
          (Phi : PointedRiemannianConvergenceMaps
            ({ obj := fun i =>
                { M := ((F.tower.history (idx i)).toHistory.stageAt (t i)).Carrier
                  basepoint := anchor i
                  metric := scaleMetric (Q i) (hQ i)
                    ((F.tower.history (idx i)).toHistory.stageMetric
                      ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) } } :
              PointedRiemannianSeq.{u, 0, 0} ThreeModel) Pl f)
          (M : MetricConvergenceData Phi),
          (∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData Phi n) →
          (∀ y : Pl.M, riemannianEDistOf Pl.metric Pl.basepoint y < ENNReal.ofReal rho) →
        let _ : EMetricSpace Pl.M := Pl.emetricSpace
        ∀ ray : C(Ico (0 : ℝ) rho, Pl.M), Isometry ray →
          Tendsto (fun v => metricScalarAt Pl.metric (ray v))
            (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho)) atTop →
        ∀ (ell : ℕ → ℝ) (γ : ∀ n, ℝ →
            ((F.tower.history (idx (f n))).toHistory.stageAt (t (f n))).Carrier),
          Tendsto ell atTop (𝓝 rho) →
          (∀ n, ∀ v ∈ Icc (0 : ℝ) (ell n), ∀ w ∈ Icc (0 : ℝ) (ell n),
            riemannianEDistOf (scaleMetric (Q (f n)) (hQ (f n))
              ((F.tower.history (idx (f n))).toHistory.stageMetric
                ((F.tower.history (idx (f n))).toHistory.activeStage (t (f n))) (t (f n))))
              (γ n v) (γ n w) = ENNReal.ofReal |v - w|) →
          (∀ v : Ico (0 : ℝ) rho, ∀ᶠ n in atTop, γ n v ∈ Phi.target n) →
          (∀ v : Ico (0 : ℝ) rho, Tendsto (fun n => (Phi.partialDiffeomorph n).symm (γ n v))
            atTop (𝓝 (ray v))) →
          Tendsto (fun n => metricScalarAt
            ((F.tower.history (idx (f n))).toHistory.stageMetric
              ((F.tower.history (idx (f n))).toHistory.activeStage (t (f n))) (t (f n)))
            (γ n (ell n)) / Q (f n)) atTop atTop →
        ∀ times : ℕ → Ico (0 : ℝ) rho, Tendsto (fun n => (times n : ℝ)) atTop (𝓝 rho) →
          ∀ᶠ m in atTop, ∀ᶠ i in atTop,
            (F.tower.history (idx (f i))).toHistory.isTracedRegion (t (f i))
              (Phi.map i (ray (times m)))
              (1 / (2 * Real.sqrt (metricScalarAt
                ((F.tower.history (idx (f i))).toHistory.stageMetric
                  ((F.tower.history (idx (f i))).toHistory.activeStage (t (f i))) (t (f i)))
                (Phi.map i (ray (times m))))))
              (metricScalarAt ((F.tower.history (idx (f i))).toHistory.stageMetric
                  ((F.tower.history (idx (f i))).toHistory.activeStage (t (f i))) (t (f i)))
                (Phi.map i (ray (times m))))⁻¹
              (1200 * metricScalarAt ((F.tower.history (idx (f i))).toHistory.stageMetric
                  ((F.tower.history (idx (f i))).toHistory.activeStage (t (f i))) (t (f i)))
                (Phi.map i (ray (times m)))) := by
  refine ⟨1, one_pos, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag _hacc _hrad _hord _hcore A _hA Hbase hHbase rho
    hrho _hfit idx t s p anchor r hs hr htlim _htime _hsmall _hvol hrnr _hanchor Q hQ hQdef f hf
    Pl Phi M hcan _hrad' _em ray _hiso hblow ell γ hell hmin hstay hconv hhigh
  have hQnr (i : ℕ) : (q.neckRadius (t i) ^ 2)⁻¹ ≤ Q i := by
    rw [hQdef i]
    have hr0 := hr i
    have hlt : r i ^ 2 < q.neckRadius (t i) ^ 2 := by
      have := hrnr i
      nlinarith
    have h1 : (q.neckRadius (t i) ^ 2)⁻¹ ≤ (r i ^ 2)⁻¹ := inv_anti₀ (by positivity) hlt.le
    have h2 : (r i ^ 2)⁻¹ ≤ Hbase * (r i ^ 2)⁻¹ :=
      le_mul_of_one_le_left (by positivity) (by linarith)
    exact h1.trans h2
  exact rayNeck_of_segment_slices_C11SP S F hTower q (fun t ht => (hdiag t ht).2)
    (le_refl (C1ceil_C11SC.{u} Γf)) (le_refl (C2ceil_C11SC.{u} Γf)) idx t anchor htlim Q hQ hQnr
    s hs f hf Pl Phi M hcan hrho ray hblow ell γ hell hmin hstay hconv hhigh

/-- **G4c（PROVISIONAL[hPlSeg 去桥]）**：G2 的 `hPlSeg` 去掉桥合同（G3 已证）⇒ `hPlN′`
（NATIVE-NJ G4 binder 逐字）；只剩 `t'` 是 RegularSlice 时刻 + G56 段数据 + `r' < nr`。 -/
theorem hPlN'_of_PlSegSlices_C11SP
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hPlSeg :
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
          C1ceil_C11SC.{u} Γf ≤ C1 → C2ceil_C11SC.{u} Γf ≤ C2 →
        ∀ A : ℝ, 0 < A →
        ∀ idx : ℕ → ℕ,
        let H : ℕ → ObservedHistory.{u} := fun i => (F.tower.history (idx i)).toHistory
        ∀ (t : ∀ i, Icc (0 : ℝ) (H i).horizon) (s : ℕ → RegularSlice F.observation),
          (∀ i, (s i).time = (t i : ℝ)) →
        ∀ (p x : ∀ i, ((H i).stageAt (t i)).Carrier) (r : ℕ → ℝ),
          (∀ i, 2 * r i ^ 2 < (t i : ℝ)) →
          (∀ i, hasSmallParabolicCurvature (H i) (t i) (p i) (r i)) →
          (∀ i, ENNReal.ofReal (A⁻¹ * r i ^ 3) ≤
            ballVolume ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (r i)) →
          (∀ i, x i ∈ riemannianBallOf
            ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (A * r i)) →
          Tendsto (fun i => (t i : ℝ)) atTop atTop →
          Tendsto (fun i => metricScalarAt
            ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (x i) * r i ^ 2) atTop atTop →
          (∀ i, r i < q.neckRadius (t i)) →
          Tendsto (fun i => r i / q.neckRadius (t i)) atTop (𝓝 0) →
          Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0) →
        ∃ (rho : ℝ) (hrho : 0 < rho),
          ∃ Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel,
          let _ : EMetricSpace Pl.M := Pl.emetricSpace
          ∃ ray : C(Ico (0 : ℝ) rho, Pl.M),
            (metricScalarAt Pl.metric Pl.basepoint = 1 ∧
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
            ∃ (A' : ℝ) (_ : 0 < A') (Hbase : ℝ) (_ : 4 ≤ Hbase)
              (_ : rho + 2 ≤ A' * Real.sqrt Hbase + 3) (idx' : ℕ → ℕ)
              (t' : ∀ i, Icc (0 : ℝ) (F.tower.history (idx' i)).toHistory.horizon)
              (p' anchor : ∀ i, ((F.tower.history (idx' i)).toHistory.stageAt (t' i)).Carrier)
              (r' : ℕ → ℝ) (_ : ∀ i, 0 < r' i) (_ : Tendsto (fun i => (t' i : ℝ)) atTop atTop)
              (_ : ∀ i, 2 * r' i ^ 2 < (t' i : ℝ))
              (_ : ∀ i, hasSmallParabolicCurvature (F.tower.history (idx' i)).toHistory (t' i)
                (p' i) (r' i))
              (_ : ∀ i, ENNReal.ofReal (A'⁻¹ * r' i ^ 3) ≤
                ballVolume ((F.tower.history (idx' i)).toHistory.stageMetric
                  ((F.tower.history (idx' i)).toHistory.activeStage (t' i)) (t' i)) (p' i) (r' i))
              (_ : ∀ i, riemannianEDistOf ((F.tower.history (idx' i)).toHistory.stageMetric
                  ((F.tower.history (idx' i)).toHistory.activeStage (t' i)) (t' i)) (p' i)
                  (anchor i) ≤ ENNReal.ofReal (A' * r' i))
              (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i) (_ : ∀ i, Q i = Hbase * (r' i ^ 2)⁻¹)
              (f : ℕ → ℕ) (_ : StrictMono f)
              (Phi : PointedRiemannianConvergenceMaps
                ({ obj := fun i =>
                    { M := ((F.tower.history (idx' i)).toHistory.stageAt (t' i)).Carrier
                      basepoint := anchor i
                      metric := scaleMetric (Q i) (hQ i)
                        ((F.tower.history (idx' i)).toHistory.stageMetric
                          ((F.tower.history (idx' i)).toHistory.activeStage (t' i)) (t' i)) } } :
                  PointedRiemannianSeq.{u, 0, 0} ThreeModel) Pl f)
              (M : MetricConvergenceData Phi),
              (∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData Phi n) ∧
              (∀ i, r' i < q.neckRadius (t' i)) ∧
              (∃ sl : ℕ → RegularSlice F.observation, ∀ i, (sl i).time = (t' i : ℝ)) ∧
              ∃ (ell : ℕ → ℝ) (γ : ∀ n, ℝ →
                  ((F.tower.history (idx' (f n))).toHistory.stageAt (t' (f n))).Carrier),
                Tendsto ell atTop (𝓝 rho) ∧
                (∀ n, ∀ v ∈ Icc (0 : ℝ) (ell n), ∀ w ∈ Icc (0 : ℝ) (ell n),
                  riemannianEDistOf (scaleMetric (Q (f n)) (hQ (f n))
                    ((F.tower.history (idx' (f n))).toHistory.stageMetric
                      ((F.tower.history (idx' (f n))).toHistory.activeStage (t' (f n)))
                      (t' (f n)))) (γ n v) (γ n w) = ENNReal.ofReal |v - w|) ∧
                (∀ v : Ico (0 : ℝ) rho, ∀ᶠ n in atTop, γ n v ∈ Phi.target n) ∧
                (∀ v : Ico (0 : ℝ) rho, Tendsto (fun n => (Phi.partialDiffeomorph n).symm (γ n v))
                  atTop (𝓝 (ray v))) ∧
                Tendsto (fun n => metricScalarAt
                  ((F.tower.history (idx' (f n))).toHistory.stageMetric
                    ((F.tower.history (idx' (f n))).toHistory.activeStage (t' (f n))) (t' (f n)))
                  (γ n (ell n)) / Q (f n)) atTop atTop) :
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
          C1ceil_C11SC.{u} Γf ≤ C1 → C2ceil_C11SC.{u} Γf ≤ C2 →
        ∀ A : ℝ, 0 < A →
        ∀ idx : ℕ → ℕ,
        let H : ℕ → ObservedHistory.{u} := fun i => (F.tower.history (idx i)).toHistory
        ∀ (t : ∀ i, Icc (0 : ℝ) (H i).horizon) (s : ℕ → RegularSlice F.observation),
          (∀ i, (s i).time = (t i : ℝ)) →
        ∀ (p x : ∀ i, ((H i).stageAt (t i)).Carrier) (r : ℕ → ℝ),
          (∀ i, 2 * r i ^ 2 < (t i : ℝ)) →
          (∀ i, hasSmallParabolicCurvature (H i) (t i) (p i) (r i)) →
          (∀ i, ENNReal.ofReal (A⁻¹ * r i ^ 3) ≤
            ballVolume ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (r i)) →
          (∀ i, x i ∈ riemannianBallOf
            ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (A * r i)) →
          Tendsto (fun i => (t i : ℝ)) atTop atTop →
          Tendsto (fun i => metricScalarAt
            ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (x i) * r i ^ 2) atTop atTop →
          (∀ i, r i < q.neckRadius (t i)) →
          Tendsto (fun i => r i / q.neckRadius (t i)) atTop (𝓝 0) →
          Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0) →
        ∃ (rho : ℝ) (hrho : 0 < rho),
          ∃ Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel,
          let _ : EMetricSpace Pl.M := Pl.emetricSpace
          ∃ ray : C(Ico (0 : ℝ) rho, Pl.M),
            (metricScalarAt Pl.metric Pl.basepoint = 1 ∧
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
            ∃ (A' : ℝ) (_ : 0 < A') (Hbase : ℝ) (_ : 4 ≤ Hbase)
              (_ : rho + 2 ≤ A' * Real.sqrt Hbase + 3) (idx' : ℕ → ℕ)
              (t' : ∀ i, Icc (0 : ℝ) (F.tower.history (idx' i)).toHistory.horizon)
              (p' anchor : ∀ i, ((F.tower.history (idx' i)).toHistory.stageAt (t' i)).Carrier)
              (r' : ℕ → ℝ) (_ : ∀ i, 0 < r' i) (_ : Tendsto (fun i => (t' i : ℝ)) atTop atTop)
              (_ : ∀ i, 2 * r' i ^ 2 < (t' i : ℝ))
              (_ : ∀ i, hasSmallParabolicCurvature (F.tower.history (idx' i)).toHistory (t' i)
                (p' i) (r' i))
              (_ : ∀ i, ENNReal.ofReal (A'⁻¹ * r' i ^ 3) ≤
                ballVolume ((F.tower.history (idx' i)).toHistory.stageMetric
                  ((F.tower.history (idx' i)).toHistory.activeStage (t' i)) (t' i)) (p' i) (r' i))
              (_ : ∀ i, riemannianEDistOf ((F.tower.history (idx' i)).toHistory.stageMetric
                  ((F.tower.history (idx' i)).toHistory.activeStage (t' i)) (t' i)) (p' i)
                  (anchor i) ≤ ENNReal.ofReal (A' * r' i))
              (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i) (_ : ∀ i, Q i = Hbase * (r' i ^ 2)⁻¹)
              (f : ℕ → ℕ) (_ : StrictMono f)
              (Phi : PointedRiemannianConvergenceMaps
                ({ obj := fun i =>
                    { M := ((F.tower.history (idx' i)).toHistory.stageAt (t' i)).Carrier
                      basepoint := anchor i
                      metric := scaleMetric (Q i) (hQ i)
                        ((F.tower.history (idx' i)).toHistory.stageMetric
                          ((F.tower.history (idx' i)).toHistory.activeStage (t' i)) (t' i)) } } :
                  PointedRiemannianSeq.{u, 0, 0} ThreeModel) Pl f)
              (M : MetricConvergenceData Phi),
              (∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData Phi n) ∧
              ∀ times : ℕ → Ico (0 : ℝ) rho, Tendsto (fun n => (times n : ℝ)) atTop (𝓝 rho) →
                ∀ᶠ m in atTop, ∀ᶠ i in atTop,
                  (F.tower.history (idx' (f i))).toHistory.isTracedRegion (t' (f i))
                    (Phi.map i (ray (times m)))
                    (1 / (2 * Real.sqrt (metricScalarAt
                      ((F.tower.history (idx' (f i))).toHistory.stageMetric
                        ((F.tower.history (idx' (f i))).toHistory.activeStage (t' (f i)))
                        (t' (f i))) (Phi.map i (ray (times m))))))
                    (metricScalarAt ((F.tower.history (idx' (f i))).toHistory.stageMetric
                        ((F.tower.history (idx' (f i))).toHistory.activeStage (t' (f i)))
                        (t' (f i))) (Phi.map i (ray (times m))))⁻¹
                    (1200 * metricScalarAt ((F.tower.history (idx' (f i))).toHistory.stageMetric
                        ((F.tower.history (idx' (f i))).toHistory.activeStage (t' (f i)))
                        (t' (f i))) (Phi.map i (ray (times m)))) := by
  apply hPlN'_of_PlSeg_C11SP P g
  obtain ⟨ε₀, hε₀, h⟩ := hPlSeg
  refine ⟨ε₀, hε₀, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hcore hε hC1 hC2 A hA idx H t s hs
    p x r htime hsmall hvol hx htlim hblowx hnr hrnr hrt
  obtain ⟨rho, hrho, Pl, ray, hten, A', hA', Hbase, hHbase, hfit, idx', t', p', anchor, r', hr',
    ht', htime', hsmall', hvol', hanchor', Q, hQ, hQdef, f, hf, Phi, M, hcan, hnr', ⟨sl, hsl⟩,
    hseg⟩ := h S F q hTower hdiag hacc hrad hord hcore hε hC1 hC2 A hA idx t s hs p x r htime
    hsmall hvol hx htlim hblowx hnr hrnr hrt
  exact ⟨rho, hrho, Pl, ray, hten, A', hA', Hbase, hHbase, hfit, idx', t', p', anchor, r', hr',
    ht', htime', hsmall', hvol', hanchor', Q, hQ, hQdef, f, hf, Phi, M, hcan, hnr',
    ⟨sl, hsl, sliceTowerTraceAt_seq_C11SP F idx' t' sl hsl⟩, hseg⟩

/-- consumer：去桥的 `hPlSeg` ⇒ `hnzero`（经 NATIVE-NJ G4 `native_hnzero_of_PlData_C11SP`）。 -/
theorem native_hnzero_of_PlSegSlices_C11SP
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hPlSeg :
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
          C1ceil_C11SC.{u} Γf ≤ C1 → C2ceil_C11SC.{u} Γf ≤ C2 →
        ∀ A : ℝ, 0 < A →
        ∀ idx : ℕ → ℕ,
        let H : ℕ → ObservedHistory.{u} := fun i => (F.tower.history (idx i)).toHistory
        ∀ (t : ∀ i, Icc (0 : ℝ) (H i).horizon) (s : ℕ → RegularSlice F.observation),
          (∀ i, (s i).time = (t i : ℝ)) →
        ∀ (p x : ∀ i, ((H i).stageAt (t i)).Carrier) (r : ℕ → ℝ),
          (∀ i, 2 * r i ^ 2 < (t i : ℝ)) →
          (∀ i, hasSmallParabolicCurvature (H i) (t i) (p i) (r i)) →
          (∀ i, ENNReal.ofReal (A⁻¹ * r i ^ 3) ≤
            ballVolume ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (r i)) →
          (∀ i, x i ∈ riemannianBallOf
            ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (A * r i)) →
          Tendsto (fun i => (t i : ℝ)) atTop atTop →
          Tendsto (fun i => metricScalarAt
            ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (x i) * r i ^ 2) atTop atTop →
          (∀ i, r i < q.neckRadius (t i)) →
          Tendsto (fun i => r i / q.neckRadius (t i)) atTop (𝓝 0) →
          Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0) →
        ∃ (rho : ℝ) (hrho : 0 < rho),
          ∃ Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel,
          let _ : EMetricSpace Pl.M := Pl.emetricSpace
          ∃ ray : C(Ico (0 : ℝ) rho, Pl.M),
            (metricScalarAt Pl.metric Pl.basepoint = 1 ∧
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
            ∃ (A' : ℝ) (_ : 0 < A') (Hbase : ℝ) (_ : 4 ≤ Hbase)
              (_ : rho + 2 ≤ A' * Real.sqrt Hbase + 3) (idx' : ℕ → ℕ)
              (t' : ∀ i, Icc (0 : ℝ) (F.tower.history (idx' i)).toHistory.horizon)
              (p' anchor : ∀ i, ((F.tower.history (idx' i)).toHistory.stageAt (t' i)).Carrier)
              (r' : ℕ → ℝ) (_ : ∀ i, 0 < r' i) (_ : Tendsto (fun i => (t' i : ℝ)) atTop atTop)
              (_ : ∀ i, 2 * r' i ^ 2 < (t' i : ℝ))
              (_ : ∀ i, hasSmallParabolicCurvature (F.tower.history (idx' i)).toHistory (t' i)
                (p' i) (r' i))
              (_ : ∀ i, ENNReal.ofReal (A'⁻¹ * r' i ^ 3) ≤
                ballVolume ((F.tower.history (idx' i)).toHistory.stageMetric
                  ((F.tower.history (idx' i)).toHistory.activeStage (t' i)) (t' i)) (p' i) (r' i))
              (_ : ∀ i, riemannianEDistOf ((F.tower.history (idx' i)).toHistory.stageMetric
                  ((F.tower.history (idx' i)).toHistory.activeStage (t' i)) (t' i)) (p' i)
                  (anchor i) ≤ ENNReal.ofReal (A' * r' i))
              (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i) (_ : ∀ i, Q i = Hbase * (r' i ^ 2)⁻¹)
              (f : ℕ → ℕ) (_ : StrictMono f)
              (Phi : PointedRiemannianConvergenceMaps
                ({ obj := fun i =>
                    { M := ((F.tower.history (idx' i)).toHistory.stageAt (t' i)).Carrier
                      basepoint := anchor i
                      metric := scaleMetric (Q i) (hQ i)
                        ((F.tower.history (idx' i)).toHistory.stageMetric
                          ((F.tower.history (idx' i)).toHistory.activeStage (t' i)) (t' i)) } } :
                  PointedRiemannianSeq.{u, 0, 0} ThreeModel) Pl f)
              (M : MetricConvergenceData Phi),
              (∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData Phi n) ∧
              (∀ i, r' i < q.neckRadius (t' i)) ∧
              (∃ sl : ℕ → RegularSlice F.observation, ∀ i, (sl i).time = (t' i : ℝ)) ∧
              ∃ (ell : ℕ → ℝ) (γ : ∀ n, ℝ →
                  ((F.tower.history (idx' (f n))).toHistory.stageAt (t' (f n))).Carrier),
                Tendsto ell atTop (𝓝 rho) ∧
                (∀ n, ∀ v ∈ Icc (0 : ℝ) (ell n), ∀ w ∈ Icc (0 : ℝ) (ell n),
                  riemannianEDistOf (scaleMetric (Q (f n)) (hQ (f n))
                    ((F.tower.history (idx' (f n))).toHistory.stageMetric
                      ((F.tower.history (idx' (f n))).toHistory.activeStage (t' (f n)))
                      (t' (f n)))) (γ n v) (γ n w) = ENNReal.ofReal |v - w|) ∧
                (∀ v : Ico (0 : ℝ) rho, ∀ᶠ n in atTop, γ n v ∈ Phi.target n) ∧
                (∀ v : Ico (0 : ℝ) rho, Tendsto (fun n => (Phi.partialDiffeomorph n).symm (γ n v))
                  atTop (𝓝 (ray v))) ∧
                Tendsto (fun n => metricScalarAt
                  ((F.tower.history (idx' (f n))).toHistory.stageMetric
                    ((F.tower.history (idx' (f n))).toHistory.activeStage (t' (f n))) (t' (f n)))
                  (γ n (ell n)) / Q (f n)) atTop atTop) :
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
        C1ceil_C11SC.{u} Γf ≤ C1 → C2ceil_C11SC.{u} Γf ≤ C2 →
      ∀ A : ℝ, 0 < A →
      ∀ idx : ℕ → ℕ,
      let H : ℕ → ObservedHistory.{u} := fun i => (F.tower.history (idx i)).toHistory
      ∀ (t : ∀ i, Icc (0 : ℝ) (H i).horizon) (s : ℕ → RegularSlice F.observation),
        (∀ i, (s i).time = (t i : ℝ)) →
      ∀ (p x : ∀ i, ((H i).stageAt (t i)).Carrier) (r : ℕ → ℝ),
        (∀ i, 2 * r i ^ 2 < (t i : ℝ)) →
        (∀ i, hasSmallParabolicCurvature (H i) (t i) (p i) (r i)) →
        (∀ i, ENNReal.ofReal (A⁻¹ * r i ^ 3) ≤
          ballVolume ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (r i)) →
        (∀ i, x i ∈ riemannianBallOf
          ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (A * r i)) →
        Tendsto (fun i => (t i : ℝ)) atTop atTop →
        Tendsto (fun i => metricScalarAt
          ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (x i) * r i ^ 2) atTop atTop →
        (∀ i, r i < q.neckRadius (t i)) →
        Tendsto (fun i => r i / q.neckRadius (t i)) atTop (𝓝 0) →
        Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0) →
      False :=
  native_hnzero_of_PlData_C11SP P g (hPlN'_of_PlSegSlices_C11SP P g hPlSeg)

end GC.LongTime.Ch11

end
