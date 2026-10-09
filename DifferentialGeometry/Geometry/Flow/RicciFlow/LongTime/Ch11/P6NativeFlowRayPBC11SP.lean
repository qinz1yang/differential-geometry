import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeFlowRayC11SP

set_option autoImplicit false

/-!
# PB-twin of `native_hnzero_of_flowRay_C11SP`（O-CH11-NRPRIME-WIRE G3 层 L6，后缀 `_PB_C11SP`）

生成器 `build-logs/scratch/O-CH11-NRPRIME-WIRE/gen/gen_twin.py`；
源 `P6NativeFlowRayC11SP.lean`（tracked，不改）。
PB 合取 `(Rmod ≤ ·.modelRadius ∧ mmod ≤ ·.modelOrder)`（lead 统一形，与 HPBASE-V8 对齐）只加在 PB 透传
binder 与结论；冻结 binder 不动；其余逐字。
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

/-- **PB-twin（O-CH11-NRPRIME-WIRE G3）** of `native_hnzero_of_flowRay_C11SP`：
binder `hflowN'` 与结论在 `2 ≤ ·.modelOrder →` 后加 PB 合取；证明逐字 + `hPB` 透传。 -/
theorem native_hnzero_of_flowRay_PB_C11SP
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (Rmod : ℝ) (mmod : ℕ)
    (hflowN' :
      ∃ ε₀ : ℝ, 0 < ε₀ ∧
        ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
          {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
          (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
          (q : CutoffParameters), F.tower = S.tower →
          (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
            q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
          pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
          2 ≤ pBase.modelOrder → (Rmod ≤ pBase.modelRadius ∧ mmod ≤ pBase.modelOrder) →
          CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
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
                          (riemannianEDistOf (g 0) a b).toReal| < eta) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder → (Rmod ≤ pBase.modelRadius ∧ mmod ≤ pBase.modelOrder) →
        CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
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
      False := by
  obtain ⟨ε₁, hε₁, hflow⟩ := hflowN'
  refine ⟨ε₁, hε₁, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hPB hb hε hC1 hC2 A hA idx H
    t s hs p x r htime hsmall hvol hx htlim hbad hnat hzero hratio
  obtain ⟨rho, hrho, Pl, ray, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, hflowPl⟩ :=
    hflow S F q hTower hdiag hacc hrad hord hPB hb hε hC1 hC2 A hA idx t s hs p x r htime hsmall
      hvol
      hx htlim hbad hnat hzero hratio
  obtain ⟨W, hWc, qW, delta, hdelta, hK, hcover, hcone, xW, hxt, hxW, hQW, c, hc, hlower, B,
    hB⟩ := puncturedConeEnd_ray_C11SP Pl rho hrho ray ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  exact cone_flow_exclusion_adm_C11SP Pl W hWc
    (fun xW => ∃ times : ℕ → Ico (0 : ℝ) rho, (∀ n, (xW n : Pl.M) = ray (times n)) ∧
      Tendsto (fun n => (times n : ℝ)) atTop (𝓝 rho))
    (fun xW N h => by
      obtain ⟨times, ht, hlim⟩ := h
      exact ⟨fun n => times (n + N), fun n => ht (n + N), hlim.comp (tendsto_add_atTop_nat N)⟩)
    (hflowPl W) qW delta hdelta hK hcover hcone xW hxt hxW hQW c hc hlower ⟨B, hB⟩

end GC.LongTime.Ch11
