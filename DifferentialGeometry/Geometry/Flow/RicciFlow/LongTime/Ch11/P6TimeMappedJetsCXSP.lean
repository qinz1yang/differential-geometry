import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6StagePointedSeedCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TracedSecondaryJetsCXSP

set_option autoImplicit false

/-!
# CX-SPINE：原 history 的 pointed mapped center 实际生产 secondary jets

草稿，仅 chat workspace，未编译。H0/L0 由实际 producer 选择，保留 L0。
theta/K0/J 先于极限点；固定 z 后才取 L=chi*Rlimit(z) 及其晚时阈值。
primary scale 为 Qbase=(chi*H0)/r²；scalar 精度 1/chi 给 auxiliary 宽度 1。
空间余量与 seed volume 使用同一 Afac。原 history 包括 birth/horizon；
只有 nr(t)≤r，没有 ratio 上界，也没有 Good、trace 或目标导数输入。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

/-- 固定高 level 的 limit 点产生原 history 的 traced region 与 normalized jets。 -/
theorem exists_prepared_time_mapped_jets_CXSP
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
      ∀ Afac : ℝ, 1 < Afac → ∃ H0 L0 : ℝ, 4 ≤ H0 ∧ 3 ≤ L0 ∧
        ∀ d0 Δ γ : ℝ, 0 ≤ d0 → 0 < Δ → 0 < γ → d0 + Δ + γ ≤ Afac →
        ∃ θ K0 : ℝ, ∃ J : ℕ → ℝ, 0 < θ ∧ 0 < K0 ∧ (∀ m, 1 ≤ J m) ∧
        ∀ χ : ℝ, 0 < χ → ∀ rho dAnchor : ℝ, 0 < rho → 0 ≤ dAnchor →
          dAnchor + rho / Real.sqrt (χ * H0) + 1 / Real.sqrt H0 ≤ d0 →
        ∀ idx : ℕ → ℕ,
        let H := fun i => (F.tower.history (idx i)).toHistory
        ∀ (t : ∀ i, Icc (0 : ℝ) (H i).horizon)
          (p : ∀ i, ((H i).stageAt (t i)).Carrier) (r : ℕ → ℝ),
          (∀ i, 0 < r i) → Tendsto (fun i => (t i : ℝ)) atTop atTop →
          (∀ i, 2 * r i ^ 2 < (t i : ℝ)) →
          (∀ i, hasSmallParabolicCurvature (H i) (t i) (p i) (r i)) →
          (∀ i, ENNReal.ofReal (Afac⁻¹ * r i ^ 3) ≤
            ballVolume ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (r i)) →
          (∀ i, q.neckRadius (t i) ≤ r i) →
        ∀ anchor : ∀ i, ((H i).stageAt (t i)).Carrier,
          (∀ i, riemannianEDistOf ((H i).stageMetric ((H i).activeStage (t i)) (t i))
            (p i) (anchor i) ≤ ENNReal.ofReal (dAnchor * r i)) →
        ∀ (Qbase : ℕ → ℝ) (hQbase : ∀ i, 0 < Qbase i),
          (∀ i, Qbase i = (χ * H0) * (r i ^ 2)⁻¹) →
        let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
          { obj := fun i =>
              { M := ((H i).stageAt (t i)).Carrier
                basepoint := anchor i
                metric := scaleMetric (Qbase i) (hQbase i)
                  ((H i).stageMetric ((H i).activeStage (t i)) (t i)) } }
        ∀ (f : ℕ → ℕ), StrictMono f →
        ∀ (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
          (Phi : PointedRiemannianConvergenceMaps X Pl f) (M : MetricConvergenceData Phi),
          (∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData Phi n) →
        ∀ z : Pl.M,
          riemannianEDistOf Pl.metric Pl.basepoint z < ENNReal.ofReal rho →
          L0 ≤ χ * metricScalarAt Pl.metric z →
        ∀ᶠ n in atTop,
          let Hn := H (f n)
          let tn := t (f n)
          let y := Phi.map n z
          let Rn := metricScalarAt (Hn.stageMetric (Hn.activeStage tn) tn) y
          0 < Rn ∧ Hn.isTracedRegion tn y (Real.sqrt Rn)⁻¹ (θ / Rn) (K0 * Rn) ∧
            ∀ (hRn : 0 < Rn) (m : ℕ),
            ∀ w ∈ riemannianBallOf (Hn.stageMetric (Hn.activeStage tn) tn) y
              (1 / (2 * Real.sqrt Rn)),
              curvDerivNorm m
                (scaleMetric Rn hRn (Hn.stageMetric (Hn.activeStage tn) tn)) w ≤ J m := by
  obtain ⟨ε₀, hε₀, hmain⟩ := exists_prepared_time_secondary_jets_CXSP P g
  refine ⟨ε₀, hε₀, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hb Afac hA
  obtain ⟨H0, L0, hH0, hL0, hmainA⟩ :=
    hmain S F q hTower hdiag hacc hrad hord hb Afac hA
  refine ⟨H0, L0, hH0, hL0, ?_⟩
  intro d0 Δ γ hd0 hΔ hγ hbuffer
  obtain ⟨θ, K0, J, hθ, hK0, hJ, hmainL⟩ := hmainA d0 Δ γ hd0 hΔ hγ hbuffer
  refine ⟨θ, K0, J, hθ, hK0, hJ, ?_⟩
  intro χ hχ rho dAnchor hrho hdAnchor hfit idx H t p r hr htendsto htime hsmall
    hvol hguard anchor hanchor Qbase hQbase hscale X f hf Pl Phi M hcanonical z hz hlevel
  have hHpos : 0 < H0 := by linarith only [hH0]
  let Ps := fun i => (H i).stageAt (t i)
  let gs : ∀ i, (Ps i).Metric :=
    fun i => (H i).stageMetric ((H i).activeStage (t i)) (t i)
  let L : ℝ := χ * metricScalarAt Pl.metric z
  have hL : L0 ≤ L := hlevel
  have hL3 : 3 ≤ L := hL0.trans hL
  obtain ⟨T₀, _hT₀, hmainN⟩ := hmainL L hL
  have hdist := eventually_stage_pointed_seed_distance_CXSP
    (P := Ps) (g := gs) (Qbase := Qbase) (hQbase := hQbase)
    (anchor := anchor) (f := f) (Pl := Pl) (F := Phi)
    (M := M) (hcanonical := hcanonical) (p := p) (r := r) (hr := hr)
    (Hbase := χ * H0) (dAnchor := dAnchor) (rho := rho)
    (hHbase := mul_pos hχ hHpos) (hdAnchor := hdAnchor)
    (hscale := hscale) (hanchor := hanchor) (z := z) (hz := hz)
  have hband := eventually_stage_pointed_auxiliary_scalar_band_CXSP
    (P := Ps) (g := gs) (Qbase := Qbase) (hQbase := hQbase)
    (anchor := anchor) (f := f) (Pl := Pl) (F := Phi)
    (M := M) (hcanonical := hcanonical) (χ := χ) (hχ := hχ) (z := z)
  have htSub : Tendsto (fun n => (t (f n) : ℝ)) atTop atTop :=
    htendsto.comp hf.tendsto_atTop
  have hdCenter : 0 ≤ dAnchor + rho / Real.sqrt (χ * H0) :=
    add_nonneg hdAnchor (div_nonneg hrho.le (Real.sqrt_nonneg _))
  filter_upwards [hdist, hband, htSub.eventually_ge_atTop T₀] with n hdn hbn htn
  change (Qbase (f n) / χ) * (L - 1) < metricScalarAt (gs (f n)) (Phi.map n z) ∧
    metricScalarAt (gs (f n)) (Phi.map n z) < (Qbase (f n) / χ) * (L + 1) at hbn
  have haux : Qbase (f n) / χ = H0 * (r (f n) ^ 2)⁻¹ := by
    rw [hscale (f n)]
    field_simp [hχ.ne', (hr (f n)).ne']
  rw [haux] at hbn
  have hQ : 0 < H0 * (r (f n) ^ 2)⁻¹ :=
    mul_pos hHpos (inv_pos.mpr (sq_pos_of_pos (hr (f n))))
  have hRn : 0 < metricScalarAt (gs (f n)) (Phi.map n z) :=
    (mul_pos hQ (by linarith only [hL3] : 0 < L - 1)).trans hbn.1
  refine ⟨hRn, ?_⟩
  exact hmainN (idx (f n)) (t (f n)) (p (f n)) (r (f n)) htn
    (htime (f n)) (hsmall (f n)) (hvol (f n)) (hguard (f n))
    (Phi.map n z) (dAnchor + rho / Real.sqrt (χ * H0)) hdCenter hfit hdn hbn.1 hbn.2

end GC.LongTime.Ch11

end
