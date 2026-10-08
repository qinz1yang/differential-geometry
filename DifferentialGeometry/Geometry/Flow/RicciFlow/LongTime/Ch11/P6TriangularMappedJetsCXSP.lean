import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TimeMappedJetsCXSP
import DifferentialGeometry.Analysis.Calculus.Compactness.DiagonalSubsequence

/-!
# CX-SPINE：实际 mapped jets 的三角形预对角

逐个 z_m 调用实际 G53 producer，才选严格递增 psi。第 n 行在同一原 history 查询
f(psi n) 同时支付所有 m≤n 的 positive scalar、traced region 与全部 normalized jets。
模型精度在 A 前，H0/L0 在空间余量前，theta/K0/J 在点序列前；不新增目标供给前提。

后续 ScalarRescaling 应对 Phi.compSubseq psi 运行。无论它再选哪个严格 k，
m≤k(m) 都使第 k(m) 行支付 z_m；实际查询是 f(psi(k(m)))。这里不假定
ScalarRescaling 的私选子列预先知道任何 N_m。
-/

set_option autoImplicit false
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

/-- exists_strictMono_ge 的前缀 sup 构造同时支配先前各项的 eventual threshold。 -/
private theorem exists_triangular_subsequence_CXSP (Paid : ℕ → ℕ → Prop)
    (hPaid : ∀ m, ∀ᶠ n in atTop, Paid m n) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ n m : ℕ, m ≤ n → Paid m (ψ n) := by
  classical
  choose N hN using fun m => eventually_atTop.mp (hPaid m)
  obtain ⟨ψ, hψ, hψN⟩ := exists_strictMono_ge N
  refine ⟨ψ, hψ, ?_⟩
  intro n m hmn
  exact hN m (ψ n) ((hψN m).trans (hψ.monotone hmn))

/-- 同一真实 first-level maps 上的三角形付款；最后一项是任意严格后续子列的实际 consumer。 -/
theorem exists_prepared_time_triangular_mapped_jets_CXSP
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
        ∀ z : ℕ → Pl.M,
          (∀ m, riemannianEDistOf Pl.metric Pl.basepoint (z m) < ENNReal.ofReal rho) →
          (∀ m, L0 ≤ χ * metricScalarAt Pl.metric (z m)) →
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          (∀ n m : ℕ, m ≤ n →
            let Hn := H (f (ψ n))
            let tn := t (f (ψ n))
            let y := Phi.map (ψ n) (z m)
            let Rn := metricScalarAt (Hn.stageMetric (Hn.activeStage tn) tn) y
            0 < Rn ∧ Hn.isTracedRegion tn y (Real.sqrt Rn)⁻¹ (θ / Rn) (K0 * Rn) ∧
              ∀ (hRn : 0 < Rn) (j : ℕ),
              ∀ w ∈ riemannianBallOf (Hn.stageMetric (Hn.activeStage tn) tn) y
                (1 / (2 * Real.sqrt Rn)),
                curvDerivNorm j
                  (scaleMetric Rn hRn (Hn.stageMetric (Hn.activeStage tn) tn)) w ≤ J j) ∧
          ∀ k : ℕ → ℕ, StrictMono k → ∀ m : ℕ,
            let Hm := H (f (ψ (k m)))
            let tm := t (f (ψ (k m)))
            let y := Phi.map (ψ (k m)) (z m)
            let Rm := metricScalarAt (Hm.stageMetric (Hm.activeStage tm) tm) y
            0 < Rm ∧ Hm.isTracedRegion tm y (Real.sqrt Rm)⁻¹ (θ / Rm) (K0 * Rm) ∧
              ∀ (hRm : 0 < Rm) (j : ℕ),
              ∀ w ∈ riemannianBallOf (Hm.stageMetric (Hm.activeStage tm) tm) y
                (1 / (2 * Real.sqrt Rm)),
                curvDerivNorm j
                  (scaleMetric Rm hRm (Hm.stageMetric (Hm.activeStage tm) tm)) w ≤ J j := by
  obtain ⟨ε₀, hε₀, hmain⟩ := exists_prepared_time_mapped_jets_CXSP P g
  refine ⟨ε₀, hε₀, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hb Afac hA
  obtain ⟨H0, L0, hH0, hL0, hmainA⟩ :=
    hmain S F q hTower hdiag hacc hrad hord hb Afac hA
  refine ⟨H0, L0, hH0, hL0, ?_⟩
  intro d0 Δ γ hd0 hΔ hγ hbuffer
  obtain ⟨θ, K0, J, hθ, hK0, hJ, hpoint⟩ := hmainA d0 Δ γ hd0 hΔ hγ hbuffer
  refine ⟨θ, K0, J, hθ, hK0, hJ, ?_⟩
  intro χ hχ rho dAnchor hrho hdAnchor hfit idx H t p r hr htlim htime hsmall
    hvol hguard anchor hanchor Qbase hQbase hscale X f hf Pl Phi M hcanonical z hz hlevel
  have hpaid := fun m => hpoint χ hχ rho dAnchor hrho hdAnchor hfit idx t p r hr htlim
    htime hsmall hvol hguard anchor hanchor Qbase hQbase hscale
    f hf Pl Phi M hcanonical (z m) (hz m) (hlevel m)
  obtain ⟨ψ, hψ, htriangle⟩ := exists_triangular_subsequence_CXSP _ hpaid
  refine ⟨ψ, hψ, htriangle, ?_⟩
  intro k hk m
  exact htriangle (k m) m (hk.id_le m)

end GC.LongTime.Ch11
