import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6RegimeGlueC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GuardNeckedRayCXSP

/-!
# SPINE-C0 (c)：合同 binder 形下 G60 的实例化（CODEX-C §3.2 (c)，后缀 `_C11SP`，INTEGRATION-ONLY）

`exists_twoLevel_guard_necked_ray_C11SP`：前缀逐字取 `HSpineTwoLevelTime_C11G7B`
（`A12GapTopV7TwoC11G7B.lean:282–314`）——`εsp := fun _ _ => ε₀`（G60 的实际 ε₀，在 `∀ A` 之前）、
`FineOf`、链在细 `Γf`、hdiag、`modelAccuracy ≤ εsp Γ Γf`、`∀ A, 1 < A`、原 `hw(A)` binder、
TimeCore 在粗 `Γ` 的 `(Γ.epsilon, C1P6 std, C2P6 std, p6Ctime Γ)`；结论 = G60 的 guard necked ray。
证明只是 `obtain` + `exact`：`ε ≤ coneAccuracy` 由 `Γ.epsilon_cone` 付，`0 < A` 由 `1 < A` 付。
`hw` 保留 binder、不消费（CODEX-C §1 H7：替代物是 G45 的 canonical-base volume；无 hw(Awork)）。
本文件不 import GapTop：合同 def 的逐字对齐 `example` 放在审计文件里。
-/

set_option autoImplicit false
noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

/-- **(c)**：完整合同前缀（粗 Γ 的 TimeCore 常数、细 Γf 的链）实际消费 G60；结论是 guard
necked missing ray，不是 hspine。 -/
theorem exists_twoLevel_guard_necked_ray_C11SP
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ εsp : ClosedBirthConstants → ClosedBirthConstants → ℝ,
      (∀ Γ Γf, 0 < εsp Γ Γf) ∧
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      ∀ (S : PreparedSpatialChain pB Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pB.modelAccuracy ≤ εsp Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
        2 ≤ pB.modelOrder →
      ∀ A : ℝ, 1 < A →
        (∃ κ'' : ℝ, 0 < κ'' ∧ ∃ T : ℝ, 0 < T ∧
          ∀ n, let H := (F.tower.history n).toHistory;
          ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
            T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
            ENNReal.ofReal (A⁻¹ * r ^ 3) ≤
              ballVolume (H.stageMetric (H.activeStage t) t) p r →
            q.neckRadius t ≤ r →
            ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
              (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
            ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
              (H.activeStage_mono haT) p,
            ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
              (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
            ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
              (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
                (H.activeStage_mono hvt)) (A * r),
            ∀ ρ' : ℝ, 0 ≤ ρ' → ρ' < r / 100 → H.isParabolicallyRmControlledBall v x ρ' →
              ENNReal.ofReal (κ'' * ρ' ^ 3) ≤
                ballVolume (H.stageMetric (H.activeStage v) v) x ρ') →
        CanonicalLateTimeCore_P6X F Γ.epsilon
          (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ)
          (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ) (p6Ctime_C11G7B.{u} Γ) →
      ∃ Hbase : ℝ, 4 ≤ Hbase ∧
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
        let _ : EMetricSpace Pl.M := Pl.emetricSpace
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
            Nonempty (SpatialNeck Pl.metric (1 / 4000000) (ray v)) := by
  obtain ⟨ε₀, hε₀, hguard⟩ := exists_guard_necked_missing_ray_CXSP P g
  refine ⟨fun _ _ => ε₀, fun _ _ => hε₀, ?_⟩
  intro pB Γ Γf _hfine S F q hTower hdiag hacc hrad hord A hA _hw hcore
  exact hguard S F q hTower hdiag hacc hrad hord hcore Γ.epsilon_cone A
    (zero_lt_one.trans hA)

/-- consumer（(a) + (c) 端到端）：合同前缀 + `¬ LargerBallScalarAt` ⇒ 原坏序列的 guard 子列
逐项 `exact` 喂进 (c)，得到非负曲率归一化极限；否则得到全项 native 的原坏序列。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ εsp : ClosedBirthConstants → ClosedBirthConstants → ℝ,
      (∀ Γ Γf, 0 < εsp Γ Γf) ∧
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      ∀ (S : PreparedSpatialChain pB Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pB.modelAccuracy ≤ εsp Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
        2 ≤ pB.modelOrder →
      ∀ A : ℝ, 1 < A →
        CanonicalLateTimeCore_P6X F Γ.epsilon
          (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ)
          (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ) (p6Ctime_C11G7B.{u} Γ) →
        ¬ LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A →
        (∃ Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel,
          metricScalarAt Pl.metric Pl.basepoint = 1 ∧
          ∀ z : Pl.M, metricAlgebraicCurvatureTensorAt Pl.metric z ∈
            algebraicCurvatureOperatorNonnegativeCone) ∨
        ∃ (idx : ℕ → ℕ) (t : ∀ i, Icc (0 : ℝ) (F.tower.history (idx i)).horizon)
          (r : ℕ → ℝ), ∀ i, r i < q.neckRadius (t i) := by
  obtain ⟨ε₀, hε₀, hguard⟩ := exists_guard_necked_missing_ray_CXSP P g
  refine ⟨fun _ _ => ε₀, fun _ _ => hε₀, ?_⟩
  intro pB Γ Γf _hfine S F q hTower hdiag hacc hrad hord A hA hcore hnot
  have hA0 : 0 < A := zero_lt_one.trans hA
  obtain ⟨idx, t, p, x, r, -, -, htime, -, hsmall, hvol, -, hx, -, hratio, hescape,
    hlate, hsplit⟩ :=
    exists_prepared_guard_or_native_bad_sequence_C11SP S F q hTower hdiag hA0 hnot
  rcases hsplit with hg | hn
  · left
    obtain ⟨Hbase, -, hray⟩ :=
      hguard S F q hTower hdiag hacc hrad hord hcore Γ.epsilon_cone A hA0
    obtain ⟨rho, hrho, -, Pl, ray, hbase, hcone, -⟩ :=
      hray idx t p x r htime hsmall hvol hx hlate hescape hg hratio
    exact ⟨Pl, hbase, hcone⟩
  · exact Or.inr ⟨idx, t, r, hn⟩

end GC.LongTime.Ch11
