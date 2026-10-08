import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeFlowProduceC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeNJSlotV2C11SP

set_option autoImplicit false

/-!
# hnzero / hspine / §2.3 主链 rev2（O-CH11-NATIVE-NJ G5 rev2，后缀 `_C11SP`）

与 G5 / G5b 同链，只把 G2b 换成 rev2 `native_NJslot_of_SL1_v2_C11SP`（hSL1 rev2：footprint 第一行乘性
`d_v < C_buf^{2n₀}·(d0+Δ)·r`，`Cbuf` 以 `let` 写出）。`hflowNRay_of_NJ_C11SP`（G5，与 hSL1 无关）原样复用。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
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

/-- **G4′（PROVISIONAL[hSL1 rev2, hBorn, hneckRay]）**：`hnzero` ⇐ hSL1 ∧ hBorn ∧ hneckRay
（G2b ⇒ hNJ，G2d ⇒ hflowN′，G3b ⇒ hnzero）。 -/
theorem native_hnzero_of_SL1_v2_C11SP (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hSL1 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ n₀ : ℕ,
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
        CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
      ∀ (params : CutoffParameters)
        (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
          GeometricCutoffRecord (F.tower.history n).toHistory e params),
        params.modelRadius = pBase.modelRadius → params.modelOrder = pBase.modelOrder →
        params.modelAccuracy = pBase.modelAccuracy →
        (∀ t : ℝ, 0 ≤ t → params.delta t = q.delta t ∧
          params.neckRadius t = q.neckRadius t) →
        (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
        (∀ n e, ((F.tower.history n).toHistory.event e).old =
          ((F.tower.history n).toHistory.event e).transition.trace.retainedCore) →
        Tendsto params.delta atTop (𝓝 0) →
        (∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
          ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
            (F.tower.history n).time e.succ ∈ Icc (t / 2) t →
            ∀ h, (records n e).nominalRadius h ≤ η * params.neckRadius t) →
      let Cbuf : ℝ := max (1 + 4 * (22 / min (1 / (2 * (StandardCap.transitionEnd + 11)))
          ((params.modelRadius - (StandardCap.transitionEnd + 10)) /
            (StandardCap.transitionEnd + 11) ^ 2)))
        (4 * (StandardCap.transitionEnd + 11) * (StandardCap.transitionEnd + 13))
      ∀ Afac : ℝ, 1 < Afac → ∃ H0 : ℝ, 4 ≤ H0 ∧
        ∀ d0 Δ γ : ℝ, 0 ≤ d0 → 0 < Δ → 0 < γ → d0 + Δ + γ ≤ Afac →
        ∃ lam0 β0 : ℝ, 0 < lam0 ∧ 0 < β0 ∧
        ∀ m : ℝ, 1 / 2 ≤ m → ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        let Q := H0 * (r ^ 2)⁻¹
        let ell := (lam0 / (m + 1)) / Real.sqrt Q
        let β := β0 / (m + 1)
        T₀ ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (Afac⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        r < q.neckRadius t →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ x : (H.stageAt t).Carrier,
          metricScalarAt (H.stageMetric (H.activeStage t) t) x ≤ m * Q →
          riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x ≤ ENNReal.ofReal (d0 * r) →
        (∃ (a : Icc (0 : ℝ) H.horizon) (haa : aSeed ≤ a) (hat : a ≤ t),
          (a : ℝ) = (t : ℝ) - β / Q ∧ Q * ((t : ℝ) - a) = β ∧
          ∃ B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
            (H.activeStage_mono hat) x,
          let A := seedTrace.restrictFirst (H.activeStage_mono haa) (H.activeStage_mono hat)
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
            A.pairEDist_CXSP (hat := hat) B v hav hvt <
                ENNReal.ofReal (Cbuf ^ (2 * n₀) * ((d0 + Δ) * r)) ∧
              A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
                ENNReal.ofReal Cbuf ^ (2 * n₀) *
                  (A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
                    ENNReal.ofReal ((8 / ell) * ((t : ℝ) - v)))) ∨
        ∃ (u : Icc (0 : ℝ) H.horizon) (hau : aSeed ≤ u) (hut : u ≤ t),
          (t : ℝ) - β / Q < u ∧
          ∃ e : Fin H.eventCount, H.time e.succ = (u : ℝ) ∧ e.succ = H.activeStage u ∧
          ∃ B : BackwardPointTrace H (H.activeStage u) (H.activeStage t)
            (H.activeStage_mono hut) x,
          (let A := seedTrace.restrictFirst (H.activeStage_mono hau) (H.activeStage_mono hut)
           ∀ (v : Icc (0 : ℝ) H.horizon) (huv : u ≤ v) (hvt : v ≤ t),
            A.pairEDist_CXSP (hat := hut) B v huv hvt <
              ENNReal.ofReal (Cbuf ^ (2 * n₀) * ((d0 + Δ) * r))) ∧
          ∃ (b : (H.event e).RetainedBoundaryIndex) (z : standardCapWindow params.modelRadius),
            ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
            HEq (((records n e).static b).window z)
              (B.point (H.activeStage u) le_rfl (H.activeStage_mono hut)) ∧
            ((records n e).static b).neck.scale ≤ 4 * (m * Q))
    (hBorn :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
        CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
      ∀ (params : CutoffParameters)
        (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
          GeometricCutoffRecord (F.tower.history n).toHistory e params),
        params.modelRadius = pBase.modelRadius → params.modelOrder = pBase.modelOrder →
        params.modelAccuracy = pBase.modelAccuracy →
        (∀ t : ℝ, 0 ≤ t → params.delta t = q.delta t ∧
          params.neckRadius t = q.neckRadius t) →
        (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
        (∀ n e, ((F.tower.history n).toHistory.event e).old =
          ((F.tower.history n).toHistory.event e).transition.trace.retainedCore) →
        Tendsto params.delta atTop (𝓝 0) →
        (∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
          ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
            (F.tower.history n).time e.succ ∈ Icc (t / 2) t →
            ∀ h, (records n e).nominalRadius h ≤ η * params.neckRadius t) →
      ∀ (R Rwide θ K c : ℝ), 0 < R → R < Rwide → 0 < θ → 0 < K → 0 < c → ∀ k : ℕ,
      ∃ J T : ℝ, 0 ≤ J ∧ ∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        ∀ (t : Icc (0 : ℝ) H.horizon) (y : (H.stageAt t).Carrier) (Q : ℝ) (hQ : 0 < Q)
          (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t), T ≤ (t : ℝ) →
          (a : ℝ) = (t : ℝ) - θ / Q →
        let Born : (H.stageAt t).Carrier → Prop := fun x =>
          ∃ (u : Icc (0 : ℝ) H.horizon) (hut : u ≤ t), a < u ∧
            ∃ e : Fin H.eventCount, H.time e.succ = (u : ℝ) ∧ e.succ = H.activeStage u ∧
            ∃ B : BackwardPointTrace H (H.activeStage u) (H.activeStage t)
                (H.activeStage_mono hut) x,
              B.isRmBoundedBy (hat := hut) (K * Q) ∧
              ∃ (b : (H.event e).RetainedBoundaryIndex)
                (z : standardCapWindow params.modelRadius),
                ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
                HEq (((records n e).static b).window z)
                  (B.point (H.activeStage u) le_rfl (H.activeStage_mono hut)) ∧
                ((records n e).static b).neck.scale ≤ c * Q
        (∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) y (Rwide / Real.sqrt Q),
          (∃ B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
              (H.activeStage_mono hat) x, B.isRmBoundedBy (hat := hat) (K * Q)) ∨ Born x) →
        (∃ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) y (Rwide / Real.sqrt Q),
          Born x) →
        ∀ w ∈ riemannianClosedBallOf
            (scaleMetric Q hQ (H.stageMetric (H.activeStage t) t)) y R,
          curvDerivNorm k (scaleMetric Q hQ (H.stageMetric (H.activeStage t) t)) w ≤ J)
    (hneckRay : ∃ ε₁ : ℝ, 0 < ε₁ ∧
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
          (p anchor : ∀ i, ((F.tower.history (idx i)).toHistory.stageAt (t i)).Carrier)
          (r : ℕ → ℝ), (∀ i, 0 < r i) →
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
                (Phi.map i (ray (times m))))) :
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
  native_hnzero_of_flowRay_C11SP P g
    (hflowNRay_of_NJ_C11SP P g (native_NJslot_of_SL1_v2_C11SP P g hSL1 hBorn) hneckRay)

/-- **G4′ consumer（PROVISIONAL[hSL1 rev2, hBorn, hneckRay]）**：hspine 合同经 SPINE-B G8 + SPINE-C。 -/
theorem hspineTwoLevelTime_of_SL1_v2_C11SP (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hSL1 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ n₀ : ℕ,
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
        CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
      ∀ (params : CutoffParameters)
        (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
          GeometricCutoffRecord (F.tower.history n).toHistory e params),
        params.modelRadius = pBase.modelRadius → params.modelOrder = pBase.modelOrder →
        params.modelAccuracy = pBase.modelAccuracy →
        (∀ t : ℝ, 0 ≤ t → params.delta t = q.delta t ∧
          params.neckRadius t = q.neckRadius t) →
        (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
        (∀ n e, ((F.tower.history n).toHistory.event e).old =
          ((F.tower.history n).toHistory.event e).transition.trace.retainedCore) →
        Tendsto params.delta atTop (𝓝 0) →
        (∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
          ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
            (F.tower.history n).time e.succ ∈ Icc (t / 2) t →
            ∀ h, (records n e).nominalRadius h ≤ η * params.neckRadius t) →
      let Cbuf : ℝ := max (1 + 4 * (22 / min (1 / (2 * (StandardCap.transitionEnd + 11)))
          ((params.modelRadius - (StandardCap.transitionEnd + 10)) /
            (StandardCap.transitionEnd + 11) ^ 2)))
        (4 * (StandardCap.transitionEnd + 11) * (StandardCap.transitionEnd + 13))
      ∀ Afac : ℝ, 1 < Afac → ∃ H0 : ℝ, 4 ≤ H0 ∧
        ∀ d0 Δ γ : ℝ, 0 ≤ d0 → 0 < Δ → 0 < γ → d0 + Δ + γ ≤ Afac →
        ∃ lam0 β0 : ℝ, 0 < lam0 ∧ 0 < β0 ∧
        ∀ m : ℝ, 1 / 2 ≤ m → ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        let Q := H0 * (r ^ 2)⁻¹
        let ell := (lam0 / (m + 1)) / Real.sqrt Q
        let β := β0 / (m + 1)
        T₀ ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (Afac⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        r < q.neckRadius t →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ x : (H.stageAt t).Carrier,
          metricScalarAt (H.stageMetric (H.activeStage t) t) x ≤ m * Q →
          riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x ≤ ENNReal.ofReal (d0 * r) →
        (∃ (a : Icc (0 : ℝ) H.horizon) (haa : aSeed ≤ a) (hat : a ≤ t),
          (a : ℝ) = (t : ℝ) - β / Q ∧ Q * ((t : ℝ) - a) = β ∧
          ∃ B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
            (H.activeStage_mono hat) x,
          let A := seedTrace.restrictFirst (H.activeStage_mono haa) (H.activeStage_mono hat)
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
            A.pairEDist_CXSP (hat := hat) B v hav hvt <
                ENNReal.ofReal (Cbuf ^ (2 * n₀) * ((d0 + Δ) * r)) ∧
              A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
                ENNReal.ofReal Cbuf ^ (2 * n₀) *
                  (A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
                    ENNReal.ofReal ((8 / ell) * ((t : ℝ) - v)))) ∨
        ∃ (u : Icc (0 : ℝ) H.horizon) (hau : aSeed ≤ u) (hut : u ≤ t),
          (t : ℝ) - β / Q < u ∧
          ∃ e : Fin H.eventCount, H.time e.succ = (u : ℝ) ∧ e.succ = H.activeStage u ∧
          ∃ B : BackwardPointTrace H (H.activeStage u) (H.activeStage t)
            (H.activeStage_mono hut) x,
          (let A := seedTrace.restrictFirst (H.activeStage_mono hau) (H.activeStage_mono hut)
           ∀ (v : Icc (0 : ℝ) H.horizon) (huv : u ≤ v) (hvt : v ≤ t),
            A.pairEDist_CXSP (hat := hut) B v huv hvt <
              ENNReal.ofReal (Cbuf ^ (2 * n₀) * ((d0 + Δ) * r))) ∧
          ∃ (b : (H.event e).RetainedBoundaryIndex) (z : standardCapWindow params.modelRadius),
            ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
            HEq (((records n e).static b).window z)
              (B.point (H.activeStage u) le_rfl (H.activeStage_mono hut)) ∧
            ((records n e).static b).neck.scale ≤ 4 * (m * Q))
    (hBorn :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
        CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
      ∀ (params : CutoffParameters)
        (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
          GeometricCutoffRecord (F.tower.history n).toHistory e params),
        params.modelRadius = pBase.modelRadius → params.modelOrder = pBase.modelOrder →
        params.modelAccuracy = pBase.modelAccuracy →
        (∀ t : ℝ, 0 ≤ t → params.delta t = q.delta t ∧
          params.neckRadius t = q.neckRadius t) →
        (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
        (∀ n e, ((F.tower.history n).toHistory.event e).old =
          ((F.tower.history n).toHistory.event e).transition.trace.retainedCore) →
        Tendsto params.delta atTop (𝓝 0) →
        (∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
          ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
            (F.tower.history n).time e.succ ∈ Icc (t / 2) t →
            ∀ h, (records n e).nominalRadius h ≤ η * params.neckRadius t) →
      ∀ (R Rwide θ K c : ℝ), 0 < R → R < Rwide → 0 < θ → 0 < K → 0 < c → ∀ k : ℕ,
      ∃ J T : ℝ, 0 ≤ J ∧ ∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        ∀ (t : Icc (0 : ℝ) H.horizon) (y : (H.stageAt t).Carrier) (Q : ℝ) (hQ : 0 < Q)
          (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t), T ≤ (t : ℝ) →
          (a : ℝ) = (t : ℝ) - θ / Q →
        let Born : (H.stageAt t).Carrier → Prop := fun x =>
          ∃ (u : Icc (0 : ℝ) H.horizon) (hut : u ≤ t), a < u ∧
            ∃ e : Fin H.eventCount, H.time e.succ = (u : ℝ) ∧ e.succ = H.activeStage u ∧
            ∃ B : BackwardPointTrace H (H.activeStage u) (H.activeStage t)
                (H.activeStage_mono hut) x,
              B.isRmBoundedBy (hat := hut) (K * Q) ∧
              ∃ (b : (H.event e).RetainedBoundaryIndex)
                (z : standardCapWindow params.modelRadius),
                ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
                HEq (((records n e).static b).window z)
                  (B.point (H.activeStage u) le_rfl (H.activeStage_mono hut)) ∧
                ((records n e).static b).neck.scale ≤ c * Q
        (∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) y (Rwide / Real.sqrt Q),
          (∃ B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
              (H.activeStage_mono hat) x, B.isRmBoundedBy (hat := hat) (K * Q)) ∨ Born x) →
        (∃ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) y (Rwide / Real.sqrt Q),
          Born x) →
        ∀ w ∈ riemannianClosedBallOf
            (scaleMetric Q hQ (H.stageMetric (H.activeStage t) t)) y R,
          curvDerivNorm k (scaleMetric Q hQ (H.stageMetric (H.activeStage t) t)) w ≤ J)
    (hneckRay : ∃ ε₁ : ℝ, 0 < ε₁ ∧
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
          (p anchor : ∀ i, ((F.tower.history (idx i)).toHistory.stageAt (t i)).Carrier)
          (r : ℕ → ℝ), (∀ i, 0 < r i) →
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
                (Phi.map i (ray (times m))))) :
    HSpineTwoLevelTime_C11G7B.{u} P g :=
  hspineTwoLevelTime_of_hnreg_C11SP P g
    (native_hnreg_of_hnzero_C11SP P g (native_hnzero_of_SL1_v2_C11SP P g hSL1 hBorn hneckRay))

/-- **G5b（PROVISIONAL[hSL1 rev2, hBorn, hneckRay]）**：§2.3 验收形 ⇐ native 三 binder + `hp`。 -/
theorem a12EnhancedFull_of_SL1_v2_C11SP (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hSL1 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ n₀ : ℕ,
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
        CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
      ∀ (params : CutoffParameters)
        (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
          GeometricCutoffRecord (F.tower.history n).toHistory e params),
        params.modelRadius = pBase.modelRadius → params.modelOrder = pBase.modelOrder →
        params.modelAccuracy = pBase.modelAccuracy →
        (∀ t : ℝ, 0 ≤ t → params.delta t = q.delta t ∧
          params.neckRadius t = q.neckRadius t) →
        (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
        (∀ n e, ((F.tower.history n).toHistory.event e).old =
          ((F.tower.history n).toHistory.event e).transition.trace.retainedCore) →
        Tendsto params.delta atTop (𝓝 0) →
        (∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
          ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
            (F.tower.history n).time e.succ ∈ Icc (t / 2) t →
            ∀ h, (records n e).nominalRadius h ≤ η * params.neckRadius t) →
      let Cbuf : ℝ := max (1 + 4 * (22 / min (1 / (2 * (StandardCap.transitionEnd + 11)))
          ((params.modelRadius - (StandardCap.transitionEnd + 10)) /
            (StandardCap.transitionEnd + 11) ^ 2)))
        (4 * (StandardCap.transitionEnd + 11) * (StandardCap.transitionEnd + 13))
      ∀ Afac : ℝ, 1 < Afac → ∃ H0 : ℝ, 4 ≤ H0 ∧
        ∀ d0 Δ γ : ℝ, 0 ≤ d0 → 0 < Δ → 0 < γ → d0 + Δ + γ ≤ Afac →
        ∃ lam0 β0 : ℝ, 0 < lam0 ∧ 0 < β0 ∧
        ∀ m : ℝ, 1 / 2 ≤ m → ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        let Q := H0 * (r ^ 2)⁻¹
        let ell := (lam0 / (m + 1)) / Real.sqrt Q
        let β := β0 / (m + 1)
        T₀ ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (Afac⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        r < q.neckRadius t →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ x : (H.stageAt t).Carrier,
          metricScalarAt (H.stageMetric (H.activeStage t) t) x ≤ m * Q →
          riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x ≤ ENNReal.ofReal (d0 * r) →
        (∃ (a : Icc (0 : ℝ) H.horizon) (haa : aSeed ≤ a) (hat : a ≤ t),
          (a : ℝ) = (t : ℝ) - β / Q ∧ Q * ((t : ℝ) - a) = β ∧
          ∃ B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
            (H.activeStage_mono hat) x,
          let A := seedTrace.restrictFirst (H.activeStage_mono haa) (H.activeStage_mono hat)
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
            A.pairEDist_CXSP (hat := hat) B v hav hvt <
                ENNReal.ofReal (Cbuf ^ (2 * n₀) * ((d0 + Δ) * r)) ∧
              A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
                ENNReal.ofReal Cbuf ^ (2 * n₀) *
                  (A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
                    ENNReal.ofReal ((8 / ell) * ((t : ℝ) - v)))) ∨
        ∃ (u : Icc (0 : ℝ) H.horizon) (hau : aSeed ≤ u) (hut : u ≤ t),
          (t : ℝ) - β / Q < u ∧
          ∃ e : Fin H.eventCount, H.time e.succ = (u : ℝ) ∧ e.succ = H.activeStage u ∧
          ∃ B : BackwardPointTrace H (H.activeStage u) (H.activeStage t)
            (H.activeStage_mono hut) x,
          (let A := seedTrace.restrictFirst (H.activeStage_mono hau) (H.activeStage_mono hut)
           ∀ (v : Icc (0 : ℝ) H.horizon) (huv : u ≤ v) (hvt : v ≤ t),
            A.pairEDist_CXSP (hat := hut) B v huv hvt <
              ENNReal.ofReal (Cbuf ^ (2 * n₀) * ((d0 + Δ) * r))) ∧
          ∃ (b : (H.event e).RetainedBoundaryIndex) (z : standardCapWindow params.modelRadius),
            ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
            HEq (((records n e).static b).window z)
              (B.point (H.activeStage u) le_rfl (H.activeStage_mono hut)) ∧
            ((records n e).static b).neck.scale ≤ 4 * (m * Q))
    (hBorn :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
        CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
      ∀ (params : CutoffParameters)
        (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
          GeometricCutoffRecord (F.tower.history n).toHistory e params),
        params.modelRadius = pBase.modelRadius → params.modelOrder = pBase.modelOrder →
        params.modelAccuracy = pBase.modelAccuracy →
        (∀ t : ℝ, 0 ≤ t → params.delta t = q.delta t ∧
          params.neckRadius t = q.neckRadius t) →
        (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
        (∀ n e, ((F.tower.history n).toHistory.event e).old =
          ((F.tower.history n).toHistory.event e).transition.trace.retainedCore) →
        Tendsto params.delta atTop (𝓝 0) →
        (∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
          ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
            (F.tower.history n).time e.succ ∈ Icc (t / 2) t →
            ∀ h, (records n e).nominalRadius h ≤ η * params.neckRadius t) →
      ∀ (R Rwide θ K c : ℝ), 0 < R → R < Rwide → 0 < θ → 0 < K → 0 < c → ∀ k : ℕ,
      ∃ J T : ℝ, 0 ≤ J ∧ ∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        ∀ (t : Icc (0 : ℝ) H.horizon) (y : (H.stageAt t).Carrier) (Q : ℝ) (hQ : 0 < Q)
          (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t), T ≤ (t : ℝ) →
          (a : ℝ) = (t : ℝ) - θ / Q →
        let Born : (H.stageAt t).Carrier → Prop := fun x =>
          ∃ (u : Icc (0 : ℝ) H.horizon) (hut : u ≤ t), a < u ∧
            ∃ e : Fin H.eventCount, H.time e.succ = (u : ℝ) ∧ e.succ = H.activeStage u ∧
            ∃ B : BackwardPointTrace H (H.activeStage u) (H.activeStage t)
                (H.activeStage_mono hut) x,
              B.isRmBoundedBy (hat := hut) (K * Q) ∧
              ∃ (b : (H.event e).RetainedBoundaryIndex)
                (z : standardCapWindow params.modelRadius),
                ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
                HEq (((records n e).static b).window z)
                  (B.point (H.activeStage u) le_rfl (H.activeStage_mono hut)) ∧
                ((records n e).static b).neck.scale ≤ c * Q
        (∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) y (Rwide / Real.sqrt Q),
          (∃ B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
              (H.activeStage_mono hat) x, B.isRmBoundedBy (hat := hat) (K * Q)) ∨ Born x) →
        (∃ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) y (Rwide / Real.sqrt Q),
          Born x) →
        ∀ w ∈ riemannianClosedBallOf
            (scaleMetric Q hQ (H.stageMetric (H.activeStage t) t)) y R,
          curvDerivNorm k (scaleMetric Q hQ (H.stageMetric (H.activeStage t) t)) w ≤ J)
    (hneckRay : ∃ ε₁ : ℝ, 0 < ε₁ ∧
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
          (p anchor : ∀ i, ((F.tower.history (idx i)).toHistory.stageAt (t i)).Carrier)
          (r : ℕ → ℝ), (∀ i, 0 < r i) →
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
                (Phi.map i (ray (times m)))))
    (hp : HP6bTwoLevelTime_C11G7B.{u} P g) :
    A12EnhancedFullConclusion_C11F P g :=
  a12EnhancedFull_of_hnreg_C11SP P g
    (native_hnreg_of_hnzero_C11SP P g (native_hnzero_of_SL1_v2_C11SP P g hSL1 hBorn hneckRay)) hp

/-- consumer：G5 的 hspine（`HSpineTwoLevelTime_C11G7B`）直接喂 v7 两合同装配。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hSL1 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ n₀ : ℕ,
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
        CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
      ∀ (params : CutoffParameters)
        (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
          GeometricCutoffRecord (F.tower.history n).toHistory e params),
        params.modelRadius = pBase.modelRadius → params.modelOrder = pBase.modelOrder →
        params.modelAccuracy = pBase.modelAccuracy →
        (∀ t : ℝ, 0 ≤ t → params.delta t = q.delta t ∧
          params.neckRadius t = q.neckRadius t) →
        (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
        (∀ n e, ((F.tower.history n).toHistory.event e).old =
          ((F.tower.history n).toHistory.event e).transition.trace.retainedCore) →
        Tendsto params.delta atTop (𝓝 0) →
        (∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
          ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
            (F.tower.history n).time e.succ ∈ Icc (t / 2) t →
            ∀ h, (records n e).nominalRadius h ≤ η * params.neckRadius t) →
      let Cbuf : ℝ := max (1 + 4 * (22 / min (1 / (2 * (StandardCap.transitionEnd + 11)))
          ((params.modelRadius - (StandardCap.transitionEnd + 10)) /
            (StandardCap.transitionEnd + 11) ^ 2)))
        (4 * (StandardCap.transitionEnd + 11) * (StandardCap.transitionEnd + 13))
      ∀ Afac : ℝ, 1 < Afac → ∃ H0 : ℝ, 4 ≤ H0 ∧
        ∀ d0 Δ γ : ℝ, 0 ≤ d0 → 0 < Δ → 0 < γ → d0 + Δ + γ ≤ Afac →
        ∃ lam0 β0 : ℝ, 0 < lam0 ∧ 0 < β0 ∧
        ∀ m : ℝ, 1 / 2 ≤ m → ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        let Q := H0 * (r ^ 2)⁻¹
        let ell := (lam0 / (m + 1)) / Real.sqrt Q
        let β := β0 / (m + 1)
        T₀ ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (Afac⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        r < q.neckRadius t →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ x : (H.stageAt t).Carrier,
          metricScalarAt (H.stageMetric (H.activeStage t) t) x ≤ m * Q →
          riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x ≤ ENNReal.ofReal (d0 * r) →
        (∃ (a : Icc (0 : ℝ) H.horizon) (haa : aSeed ≤ a) (hat : a ≤ t),
          (a : ℝ) = (t : ℝ) - β / Q ∧ Q * ((t : ℝ) - a) = β ∧
          ∃ B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
            (H.activeStage_mono hat) x,
          let A := seedTrace.restrictFirst (H.activeStage_mono haa) (H.activeStage_mono hat)
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
            A.pairEDist_CXSP (hat := hat) B v hav hvt <
                ENNReal.ofReal (Cbuf ^ (2 * n₀) * ((d0 + Δ) * r)) ∧
              A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
                ENNReal.ofReal Cbuf ^ (2 * n₀) *
                  (A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
                    ENNReal.ofReal ((8 / ell) * ((t : ℝ) - v)))) ∨
        ∃ (u : Icc (0 : ℝ) H.horizon) (hau : aSeed ≤ u) (hut : u ≤ t),
          (t : ℝ) - β / Q < u ∧
          ∃ e : Fin H.eventCount, H.time e.succ = (u : ℝ) ∧ e.succ = H.activeStage u ∧
          ∃ B : BackwardPointTrace H (H.activeStage u) (H.activeStage t)
            (H.activeStage_mono hut) x,
          (let A := seedTrace.restrictFirst (H.activeStage_mono hau) (H.activeStage_mono hut)
           ∀ (v : Icc (0 : ℝ) H.horizon) (huv : u ≤ v) (hvt : v ≤ t),
            A.pairEDist_CXSP (hat := hut) B v huv hvt <
              ENNReal.ofReal (Cbuf ^ (2 * n₀) * ((d0 + Δ) * r))) ∧
          ∃ (b : (H.event e).RetainedBoundaryIndex) (z : standardCapWindow params.modelRadius),
            ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
            HEq (((records n e).static b).window z)
              (B.point (H.activeStage u) le_rfl (H.activeStage_mono hut)) ∧
            ((records n e).static b).neck.scale ≤ 4 * (m * Q))
    (hBorn :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
        CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
      ∀ (params : CutoffParameters)
        (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
          GeometricCutoffRecord (F.tower.history n).toHistory e params),
        params.modelRadius = pBase.modelRadius → params.modelOrder = pBase.modelOrder →
        params.modelAccuracy = pBase.modelAccuracy →
        (∀ t : ℝ, 0 ≤ t → params.delta t = q.delta t ∧
          params.neckRadius t = q.neckRadius t) →
        (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
        (∀ n e, ((F.tower.history n).toHistory.event e).old =
          ((F.tower.history n).toHistory.event e).transition.trace.retainedCore) →
        Tendsto params.delta atTop (𝓝 0) →
        (∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
          ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
            (F.tower.history n).time e.succ ∈ Icc (t / 2) t →
            ∀ h, (records n e).nominalRadius h ≤ η * params.neckRadius t) →
      ∀ (R Rwide θ K c : ℝ), 0 < R → R < Rwide → 0 < θ → 0 < K → 0 < c → ∀ k : ℕ,
      ∃ J T : ℝ, 0 ≤ J ∧ ∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        ∀ (t : Icc (0 : ℝ) H.horizon) (y : (H.stageAt t).Carrier) (Q : ℝ) (hQ : 0 < Q)
          (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t), T ≤ (t : ℝ) →
          (a : ℝ) = (t : ℝ) - θ / Q →
        let Born : (H.stageAt t).Carrier → Prop := fun x =>
          ∃ (u : Icc (0 : ℝ) H.horizon) (hut : u ≤ t), a < u ∧
            ∃ e : Fin H.eventCount, H.time e.succ = (u : ℝ) ∧ e.succ = H.activeStage u ∧
            ∃ B : BackwardPointTrace H (H.activeStage u) (H.activeStage t)
                (H.activeStage_mono hut) x,
              B.isRmBoundedBy (hat := hut) (K * Q) ∧
              ∃ (b : (H.event e).RetainedBoundaryIndex)
                (z : standardCapWindow params.modelRadius),
                ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
                HEq (((records n e).static b).window z)
                  (B.point (H.activeStage u) le_rfl (H.activeStage_mono hut)) ∧
                ((records n e).static b).neck.scale ≤ c * Q
        (∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) y (Rwide / Real.sqrt Q),
          (∃ B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
              (H.activeStage_mono hat) x, B.isRmBoundedBy (hat := hat) (K * Q)) ∨ Born x) →
        (∃ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) y (Rwide / Real.sqrt Q),
          Born x) →
        ∀ w ∈ riemannianClosedBallOf
            (scaleMetric Q hQ (H.stageMetric (H.activeStage t) t)) y R,
          curvDerivNorm k (scaleMetric Q hQ (H.stageMetric (H.activeStage t) t)) w ≤ J)
    (hneckRay : ∃ ε₁ : ℝ, 0 < ε₁ ∧
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
          (p anchor : ∀ i, ((F.tower.history (idx i)).toHistory.stageAt (t i)).Carrier)
          (r : ℕ → ℝ), (∀ i, 0 < r i) →
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
                (Phi.map i (ray (times m)))))
    (hp : HP6bTwoLevelTime_C11G7B.{u} P g) :
    A12EnhancedFullConclusion_C11F P g :=
  a12EnhancedFull_of_v7two_contracts_C11G7B P g
    (hspineTwoLevelTime_of_SL1_v2_C11SP P g hSL1 hBorn hneckRay) hp


end GC.LongTime.Ch11
