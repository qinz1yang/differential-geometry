import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PreparedRecordsCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PinchingP6A
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedTimeArithmeticCXSP

set_option autoImplicit false

/-!
# Prepared original-stage limit pinching / 原 stage 极限的实际 pinching consumer

同一 chain 与 tower identity 实际支付 F 的 cutoff records。原 seed ratio r/sqrt(t)趋零，
给 Q=Hbase/r² 下的 tQ→∞，不要求 Q 本身发散。P6PinchingP6A 直接消费原
historySliceSeq 上的 canonical metric convergence，无需 flow convergence。

同源 records 从任意 prepared chain 取出；不假设 HI、Good 或 ClosedSlab。
量词保留同一 idx/time/anchor/Q 与 compactness 子列，便于 scalar-escape 的 ind/f 接线。
这里只完成已有 metric limit 的非负曲率算子结论，不宣称整个 Claim 2 已闭合。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch11

universe u

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

private theorem exists_actual_cutoff_records_of_chain_CXSP
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {pBase : CutoffParameters} {Γ : ClosedBirthConstants}
    (S : PreparedSpatialChain pBase Γ P g) (F : GC.Interface.RawSurgery P g)
    (hTower : F.tower = S.tower) :
    ∃ params : CutoffParameters, Nonempty (CutoffRecords_C11S F params) := by
  obtain ⟨F₀, params, _κ, records, hTower₀, -⟩ :=
    S.exists_surgery_with_spatial_control_and_decay
  have hF : F₀ = F := by
    have hT := hTower₀.trans hTower.symm
    cases F₀
    cases F
    congr 1
  subst F₀
  exact ⟨params, ⟨records⟩⟩

private theorem tendsto_seed_scaled_age_CXSP
    {Hbase : ℝ} (hHbase : 0 < Hbase) {t r Q : ℕ → ℝ}
    (ht : ∀ i, 0 < t i) (hr : ∀ i, 0 < r i)
    (hscale : ∀ i, Q i = Hbase / r i ^ 2)
    (hratio : Tendsto (fun i => r i / Real.sqrt (t i)) atTop (𝓝 0)) :
    Tendsto (fun i => t i * Q i) atTop atTop := by
  have hsq : Tendsto (fun i => (r i / Real.sqrt (t i)) ^ 2) atTop (𝓝 0) := by
    simpa using hratio.pow 2
  have hwithin : Tendsto (fun i => (r i / Real.sqrt (t i)) ^ 2)
      atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hsq, Eventually.of_forall fun i =>
      sq_pos_of_pos (div_pos (hr i) (Real.sqrt_pos.mpr (ht i)))⟩
  have hinv := tendsto_inv_nhdsGT_zero.comp hwithin
  have hprod := hinv.const_mul_atTop hHbase
  have heq (i : ℕ) : t i * Q i = Hbase * ((r i / Real.sqrt (t i)) ^ 2)⁻¹ := by
    rw [hscale i, div_pow, inv_div, Real.sq_sqrt (ht i).le]
    ring
  exact hprod.congr (fun i => (heq i).symm)

/-- 同一 chain 的实际 records 与 seed ratio 支付原 stage metric limit 的非负曲率；
不要求原尺度 Q→∞。 -/
theorem curvatureOperator_nonnegative_of_prepared_stage_limit_CXSP
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {pBase : CutoffParameters} {Γ : ClosedBirthConstants}
    (S : PreparedSpatialChain pBase Γ P g) (F : GC.Interface.RawSurgery P g)
    (hTower : F.tower = S.tower) (Hbase : ℝ) (hHbase : 0 < Hbase)
    (idx : ℕ → ℕ)
    (t : ∀ i, Icc (0 : ℝ) (F.tower.history (idx i)).toHistory.horizon)
    (x : ∀ i, ((F.tower.history (idx i)).toHistory.stageAt (t i)).Carrier)
    (r Q : ℕ → ℝ) (ht : ∀ i, 0 < (t i : ℝ)) (hr : ∀ i, 0 < r i)
    (hQ : ∀ i, 0 < Q i) (hscale : ∀ i, Q i = Hbase / r i ^ 2)
    (hratio : Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0))
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (L : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (maps : PointedRiemannianConvergenceMaps (historySliceSeq_P6A F idx t x Q hQ) L σ)
    (Mconv : MetricConvergenceData maps)
    (hcanonical : ∀ i, Mconv.domain i = CanonicalMetricCompactness.canonicalSourceData maps i) :
    ∀ z : L.M, metricAlgebraicCurvatureTensorAt L.metric z ∈
      algebraicCurvatureOperatorNonnegativeCone := by
  obtain ⟨params, ⟨records⟩⟩ := exists_actual_cutoff_records_of_chain_CXSP S F hTower
  exact curvatureOperator_nonnegative_of_history_slice_limit_of_age_P6A
    F records idx t x Q hQ σ hσ L maps Mconv hcanonical
    (tendsto_seed_scaled_age_CXSP hHbase ht hr hscale hratio)

end GC.LongTime.Ch11

end
