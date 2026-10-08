import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeConeFlowC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeFlowRayC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HSpineNativeOnlyC11SP

set_option autoImplicit false

/-!
# G4：`hflowN′` 装配（O-CH11-NATIVE-NJ，后缀 `_C11SP`）

* `hflowNRay_of_PlData_C11SP`（PROVED 归约）：binder `hPlN′`（native 第一层 Pl 生产的扩输出：G60 十条 +
  G3 kernel 所需的第一层数据 `A' Hbase idx' t' p' anchor r' Q f Phi M` + ray 映射点的 S16 neck traced
  region 子句）⇒ G9′ 的 `hflowN′`。flow 子句由 G3 `native_coneFlow_of_neckTraced_C11SP` 付。
* `native_hnzero_of_PlData_C11SP`（PROVISIONAL[hPlN′]）：`native_hnzero_of_flowRay_C11SP P g (…)`。
* `hspineTwoLevelTime_of_PlData_C11SP`（PROVISIONAL[hPlN′]）：经 SPINE-B G8 + SPINE-C 喂 hspine。
`hPlN′` 的 repair：十条 + 第一层数据 = native 版 G48 / G55 / G60 扩输出（G2：G46 bounded-ball traced region
换 NJ；NJ ⇐ hSL1，G1）；ray neck 子句 = G33（实际最短段双端 scalar gap ⇒ neck）+ G47 + slice↔tower
桥（state §G3 repair target）。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

/-- **G4a（PROVED 归约）**：native 第一层扩输出 `hPlN′` ⇒ G9′ 的 `hflowN′`（flow 子句 = G3）。 -/
theorem hflowNRay_of_PlData_C11SP
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hPlN' :
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
                        (t' (f i))) (Phi.map i (ray (times m))))) :
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
          ∀ W : TopologicalSpace.Opens Pl.M,
          ∀ (xW : ℕ → W),
            (∃ times : ℕ → Ico (0 : ℝ) rho, (∀ n, (xW n : Pl.M) = ray (times n)) ∧
              Tendsto (fun n => (times n : ℝ)) atTop (𝓝 rho)) →
          ∀ (R₀ : ℝ), 0 < R₀ →
            (∀ n, 2 ≤ metricScalarAt Pl.metric (xW n : Pl.M)) →
            Tendsto (fun n => metricScalarAt Pl.metric (xW n : Pl.M)) atTop atTop →
            (∀ n, IsCompact (riemannianClosedBallOf (Pl.metric.restrictOpen W) (xW n)
              (4 * R₀ / Real.sqrt (metricScalarAt Pl.metric (xW n : Pl.M))))) →
            ∃ (j : ℕ → ℕ) (_ : StrictMono j) (A₂ : ℕ → ℝ) (hA₂ : ∀ n, 0 < A₂ n),
              Tendsto (fun n => A₂ n / metricScalarAt Pl.metric (xW (j n) : Pl.M)) atTop (𝓝 1) ∧
              ∃ (P₂ : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
                (V : TopologicalSpace.Opens P₂.M)
                (hp : P₂.basepoint ∈ V) (_ : PathConnectedSpace V) (tau : ℝ) (htau : 0 < tau)
                (g : ℝ → SmoothRiemannianMetric ThreeModel V),
                g 0 = P₂.metric.restrictOpen V ∧
                IsSolutionOn ({ base.metric := g } : SolutionOn (I := ThreeModel) (M := V)
                  (RealTimeInterval.closed (-tau) 0 (by linarith))) ∧
                (∀ t ∈ Icc (-tau) 0, ∀ y : V, metricAlgebraicCurvatureTensorAt (g t) y ∈
                  algebraicCurvatureOperatorNonnegativeCone (I := ThreeModel)) ∧
                metricScalarAt P₂.metric P₂.basepoint = 1 ∧
                ∃ C : ℕ → PartialDiffeomorph ThreeModel ThreeModel V W ∞,
                  (∀ n, C n ⟨P₂.basepoint, hp⟩ = xW (j n)) ∧
                  ∃ r : ℝ, 0 < r ∧ IsCompact (riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r) ∧
                  (∀ᶠ n in atTop,
                    riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r ⊆ (C n).source ∧
                    riemannianClosedBallOf (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W))
                      (xW (j n)) (r / 4) ⊆
                        (C n) '' riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r) ∧
                  ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
                    ∀ a ∈ riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r,
                    ∀ b ∈ riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r,
                      |(riemannianEDistOf
                          (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W))
                          (C n a) (C n b)).toReal -
                        (riemannianEDistOf (g 0) a b).toReal| < eta := by
  obtain ⟨ε₁, hε₁, hpl⟩ := hPlN'
  refine ⟨ε₁, hε₁, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hb hε hC1 hC2 A hA idx H
    t s hs p x r htime hsmall hvol hx htlim hbad hnat hzero hratio
  obtain ⟨rho, hrho, Pl, ray, hten, A', hA', Hbase, hHbase, hrhoB, idx', t', p', anchor, r', hr',
    htlim', htime', hsmall', hvol', hanchor', Q, hQ, hQeq, f, hf, Phi, M, hcan, hneckR⟩ :=
    hpl S F q hTower hdiag hacc hrad hord hb hε hC1 hC2 A hA idx t s hs p x r htime hsmall hvol
      hx htlim hbad hnat hzero hratio
  refine ⟨rho, hrho, Pl, ray, hten, ?_⟩
  intro W xW hadm R₀ hR₀ hQW hQWlim hcompactW
  obtain ⟨times, hxt, htimes⟩ := hadm
  refine native_coneFlow_of_neckTraced_C11SP S F hTower hb A' hA' Hbase hHbase rho hrhoB idx' t'
    p' anchor r' hr' htlim' htime' hsmall' hvol' hanchor' Q hQ hQeq f hf Pl Phi M hcan
    hten.2.2.1 W xW R₀ hR₀ hQW hQWlim hcompactW ?_
  filter_upwards [hneckR times htimes] with m hm
  rw [hxt m]
  exact hm

/-- **G4b（PROVISIONAL[hPlN′]）**：`hnzero` ⇐ `hPlN′`（经 G9′）。 -/
theorem native_hnzero_of_PlData_C11SP
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hPlN' :
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
                        (t' (f i))) (Phi.map i (ray (times m))))) :
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
  native_hnzero_of_flowRay_C11SP P g (hflowNRay_of_PlData_C11SP P g hPlN')

/-- **G4c（PROVISIONAL[hPlN′]）**：hspine 合同经 SPINE-B G8 `native_hnreg_of_hnzero_C11SP` + SPINE-C
`hspineTwoLevelTime_of_hnreg_C11SP`。 -/
theorem hspineTwoLevelTime_of_PlData_C11SP
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hPlN' :
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
                        (t' (f i))) (Phi.map i (ray (times m))))) :
    HSpineTwoLevelTime_C11G7B.{u} P g :=
  hspineTwoLevelTime_of_hnreg_C11SP P g
    (native_hnreg_of_hnzero_C11SP P g (native_hnzero_of_PlData_C11SP P g hPlN'))

end GC.LongTime.Ch11
