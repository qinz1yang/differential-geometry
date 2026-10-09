import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeOnlyNzeroC11SP

set_option autoImplicit false

/-!
# `hnzero` 的骨架：native 版 necked ray + cone 点 flow ⇒ `hnzero`（O-CH11-SPINE-B G9，后缀 `_C11SP`）

**`native_hnzero_of_flow_C11SP (P) (g) (hflowN)`**：结论 = G8 的 `hnzero` 体（`NZERObody.txt` 逐字）。
唯一 binder `hflowN` = SPINE-A1 `guard_regime_false_bdd_C11SP` 的 `hflowA1` 结论块（G60 十条性质的 Pl + ray，
外加任意 W 上 cone 端点点列的二次 blow-up 反向 flow）**原样**，前提换成 `hnzero` 的 native 前提（RegularSlice、
`ρ < nr`、`ρ/nr → 0`，带 `hC1 hC2`，无 Λ）。证明 = A1 G1b 同款：`hflowN` 出 Pl / ray / flow，
`guard_puncturedConeEnd_v2_C11SP`（A1，PROVED）出 cone end，A2 `guard_cone_flow_exclusion_C11SP` 收尾。
所以 **`hnzero` ⇐ `hflowN`**，而 `hflowN` 的 repair = native-route §N1 / §R-C11-19：
NJ（Q1 hdisj、Q2 hshort、Q3 crossing 计数、
SL2 已齐）⇒ native 版 G48 / G55 / G60（把 G46 bounded-ball traced region 换成 NJ）⇒ Pl；cone 点 flow 由 S16 neck
（G47 traced region）+ A1 史无关 kernel `secondBlowup_flow_of_traced_C11SP`。块标 PROVISIONAL[hflowN]。
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

/-- **G9（PROVISIONAL[hflowN]）**：`hnzero` ⇐ native 版 necked ray + cone 点 flow。 -/
theorem native_hnzero_of_flow_C11SP
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hflowN :
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
            ∀ (xW : ℕ → W) (R₀ : ℝ), 0 < R₀ →
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
      False := by
  obtain ⟨ε₁, hε₁, hflow⟩ := hflowN
  refine ⟨ε₁, hε₁, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hb hε hC1 hC2 A hA idx H
    t s hs p x r htime hsmall hvol hx htlim hbad hnat hzero hratio
  obtain ⟨rho, hrho, Pl, ray, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, hflowPl⟩ :=
    hflow S F q hTower hdiag hacc hrad hord hb hε hC1 hC2 A hA idx t s hs p x r htime hsmall hvol
      hx htlim hbad hnat hzero hratio
  obtain ⟨W, hWc, qW, delta, hdelta, hK, hcover, hcone, xW, hxW, hQW, c, hc, hlower, B, hB⟩ :=
    guard_puncturedConeEnd_v2_C11SP Pl rho hrho ⟨ray, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  exact guard_cone_flow_exclusion_C11SP Pl W hWc (hflowPl W) qW delta hdelta hK hcover hcone
    xW hxW hQW c hc hlower ⟨B, hB⟩

end GC.LongTime.Ch11
