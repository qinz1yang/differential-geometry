import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HSpineTwoLevelTimePBC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HSpineTwoLevelTimeSupFnP6XS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilHnDefsCH2

set_option autoImplicit false

/-!
[CEILHN2：自 `P6HSpineSupFnCHN.lean` 机械克隆]
# CHN G4c：hspine SupFn（HN ceiling）

CEIL-HN 孪生（O-CH11-CEILHN，后缀 `_CHN`）：自 `P6HSpineTwoLevelTimeSupFnP6XS.lean` 机械克隆
（生成器 `build-logs/scratch/CEILHN/gen/clone.py`），ceiling 常数换 HN 扩展。
-/

noncomputable section
open Set Filter DifferentialGeometry MeasureTheory DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped NNReal Topology ContDiff Manifold ENNReal
namespace GC.LongTime.Ch11
universe u
open GC.LongTime.Ch11 (p6CoarseCH2_CH2 one_le_p6CoarseCH2_CH2 p6CoarseC_le_p6CoarseCH2_CH2)

/-- **XSUP2 supply-threaded fn twin** of `hspineTwoLevelTime_PB_C11SP`：
PB 透传 binder 与结论经 (a) `hdiag` 后加供给前提 (b) `ε₀` 函数化 (c) `Rn Γf / mn Γf`；
冻结 binder 不动；证明逐字 + `hSUP` 透传。 -/
theorem hspineTwoLevelTime_SupFn_P6XS_CH2 (P : OrientedThreeStage.{u}) (g : P.Metric)
    (Rn : ClosedBirthConstants → ℝ) (mn : ClosedBirthConstants → ℕ)
    (hglue : ∀ {pB : CutoffParameters} {Γf : ClosedBirthConstants}
      (S : PreparedSpatialChain pB Γf P g) (F : GC.Interface.RawSurgery P g)
      (q : CutoffParameters), F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      ∀ A : ℝ, 0 < A →
      ¬ LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A →
      ∃ idx : ℕ → ℕ,
      let H : ℕ → ObservedHistory.{u} := fun i => (F.tower.history (idx i)).toHistory
      ∃ (t : ∀ i, Icc (0 : ℝ) (H i).horizon)
        (p x : ∀ i, ((H i).stageAt (t i)).Carrier) (r : ℕ → ℝ),
        (∀ i, 2 * r i ^ 2 < (t i : ℝ)) ∧
        (∀ i, hasSmallParabolicCurvature (H i) (t i) (p i) (r i)) ∧
        (∀ i, ENNReal.ofReal (A⁻¹ * r i ^ 3) ≤
          ballVolume ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (r i)) ∧
        (∀ i, x i ∈ riemannianBallOf
          ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (A * r i)) ∧
        Tendsto (fun i => (t i : ℝ)) atTop atTop ∧
        Tendsto (fun i => metricScalarAt
          ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (x i) * r i ^ 2) atTop atTop ∧
        ((∀ i, q.neckRadius (t i) ≤ r i) ∨ (∀ i, r i < q.neckRadius (t i))) ∧
        Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0))
    (hguard :
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
        ∀ A : ℝ, 0 < A →
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
        False)
    (hnative :
      ∃ ε₀ : ClosedBirthConstants → ℝ, (∀ Γf, 0 < ε₀ Γf) ∧
        ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
          {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
          (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
          (q : CutoffParameters), F.tower = S.tower →
          (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
            q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
          TimeDerivativeSupply_C11E F q.neckRadius Γf.Ctime →
          pBase.modelAccuracy ≤ ε₀ Γf → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
          2 ≤ pBase.modelOrder → (Rn Γf ≤ pBase.modelRadius ∧ mn Γf ≤ pBase.modelOrder) →
          CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
          ε ≤ coneAccuracy →
          C1ceil_C11SC.{u} Γf ≤ C1 → C2ceil_C11SC.{u} Γf ≤ C2 →
        ∀ A : ℝ, 0 < A →
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
          (∀ i, r i < q.neckRadius (t i)) →
          Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0) →
        False) :
    ∃ εsp : ClosedBirthConstants → ClosedBirthConstants → ℝ,
      (∀ Γ Γf, 0 < εsp Γ Γf) ∧
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ → ∀
      (S : PreparedSpatialChain pB Γf P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      TimeDerivativeSupply_C11E F q.neckRadius Γf.Ctime →
      pB.modelAccuracy ≤ εsp Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder → (Rn Γf ≤ pB.modelRadius ∧ mn Γf ≤ pB.modelOrder) →
      ∀ A : ℝ, 1 < A →
      (∃ κ'' : ℝ, 0 < κ'' ∧ ∃ T : ℝ, 0 < T ∧
        ∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
          T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
          ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
          q.neckRadius t ≤ r →
          ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
            (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
          ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
            (H.activeStage_mono haT) p,
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
            (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
          ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
            (A * r),
          ∀ ρ' : ℝ, 0 ≤ ρ' → ρ' < r / 100 → H.isParabolicallyRmControlledBall v x ρ' →
            ENNReal.ofReal (κ'' * ρ' ^ 3) ≤
              ballVolume (H.stageMetric (H.activeStage v) v) x ρ') →
        CanonicalLateTimeCore_P6X F Γ.epsilon (C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ)
          (C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ) (p6CtimeHN_CH2.{u} Γ) →
        LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A := by
  obtain ⟨ε₀g, hε₀g, hg⟩ := hguard
  obtain ⟨ε₀n, hε₀n, hn⟩ := hnative
  refine ⟨fun _ Γf => min ε₀g (ε₀n Γf), fun _ Γf => lt_min hε₀g (hε₀n Γf), ?_⟩
  intro pB Γ Γf hFine S F q hTower hdiag hSUP hacc hrad hord hPB A hA _hw hcore
  have hA0 : 0 < A := zero_lt_one.trans hA
  have haccg : pB.modelAccuracy ≤ ε₀g := hacc.trans (min_le_left _ _)
  have haccn : pB.modelAccuracy ≤ ε₀n Γf := hacc.trans (min_le_right _ _)
  have hC1 : C1ceil_C11SC.{u} Γf ≤ C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ :=
    hFine.2.1.trans (C1ceil_le_C1P6_C11GT6 _ Γ)
  have hC2 : C2ceil_C11SC.{u} Γf ≤ C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ :=
    hFine.2.2.1.trans (C2ceil_le_C2P6_C11GT6 _ Γ)
  by_contra hnot
  obtain ⟨idx, t, p, x, r, h2r, hsmall, hvol, hx, htime, hesc, hreg, hratio⟩ :=
    hglue S F q hTower hdiag A hA0 hnot
  rcases hreg with hgd | hnat
  · exact hg S F q hTower hdiag haccg hrad hord hcore Γ.epsilon_cone A hA0 idx t p x r
      h2r hsmall hvol hx htime hesc hgd hratio
  · exact hn S F q hTower hdiag hSUP haccn hrad hord hPB hcore Γ.epsilon_cone hC1 hC2 A hA0 idx t p
        x r
      h2r hsmall hvol hx htime hesc hnat hratio
end GC.LongTime.Ch11
