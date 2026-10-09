import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckScaleStability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedParabolicComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedShiTerminal
import DifferentialGeometry.Geometry.Metric.Distance.Topology
import Mathlib.Topology.MetricSpace.Bounded

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem StrongNeck.exists_windowed_transport_tolerance_on_compact
    {P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval}
    {alpha : ℝ} {y : P.M}
    (nk : StrongNeck P.S (neckModelTolerance alpha) y 0)
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11)
    (U : TopologicalSpace.Opens P.M) (hUc : IsCompact (closure (U : Set P.M)))
    {K : Set P.M} (hK : IsCompact K) (hKU : K ⊆ U)
    (houter : ∀ z ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹, nk.map z ∈ K)
    {R : ℝ} (hR : 0 < R)
    (hUR : (U : Set P.M) ⊆ riemannianClosedBallOf (P.S.base.metric 0) P.basepoint R) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D)
        (delta kappa : ℝ) (x : M) (t : ℝ)
        (W : WindowedModelWitness delta kappa S x t), delta ≤ delta₀ →
        IsSolutionOn S → Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
        ∀ hmodel : W.model = P,
          ∃ nk' : StrongNeck S (2 * alpha) (W.embedding (hmodel.symm ▸ y)) t,
            nk'.map = (hmodel.symm ▸ nk.map).trans W.embedding := by
  obtain ⟨eta, beta, heta, hbeta, htransport⟩ :=
    nk.exists_rescaled_transport_tolerances_of_ancient P.isSolution ha hsmall U hUc hK hKU houter
  let n := ⌈(2 * alpha)⁻¹⌉₊
  let H := Real.sqrt (P.rmNormSq 0 y) + 1
  let B := 243 * (1 + 3 * H)
  let F := (max 1 (Real.sqrt (2 / P.S.scalar 0 y))) ^ n
  let radius := R + 1
  have hH : 0 < H := by dsimp only [H]; positivity
  have hB : 0 < B := by dsimp only [B]; positivity
  have hF : 0 < F := pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
  have hradius : 0 < radius := by dsimp only [radius]; linarith
  let delta₀ := min (1 / 4) (min (2 * alpha)
    (min (radius⁻¹ ^ 2) (min (beta / F)
      (min (min eta (P.S.scalar 0 y / 4) / (2 * B)) (P.S.scalar 0 y / 4)))))
  have hd0 : 0 < delta₀ := lt_min (by norm_num)
    (lt_min (by positivity)
      (lt_min (sq_pos_of_pos (inv_pos.mpr hradius)) (lt_min (div_pos hbeta hF)
        (lt_min (div_pos (lt_min heta (by linarith [nk.Q_pos])) (by positivity))
          (by linarith [nk.Q_pos])))))
  refine ⟨delta₀, hd0, ?_⟩
  intro M _ _ _ _ _ D S delta kappa x t W hd hS hreg hmodel
  subst P
  have hd4 : delta ≤ 1 / 4 := hd.trans (min_le_left _ _)
  have hdrest := hd.trans (min_le_right _ _)
  have hdalpha : delta ≤ 2 * alpha := hdrest.trans (min_le_left _ _)
  have hdrest' := hdrest.trans (min_le_right _ _)
  have hdradius : delta ≤ radius⁻¹ ^ 2 := hdrest'.trans (min_le_left _ _)
  have hdrest'' := hdrest'.trans (min_le_right _ _)
  have hdF : delta ≤ beta / F := hdrest''.trans (min_le_left _ _)
  have hdrest''' := hdrest''.trans (min_le_right _ _)
  have hdB : delta ≤ min eta (W.model.S.scalar 0 y / 4) / (2 * B) :=
    hdrest'''.trans (min_le_left _ _)
  have hdq : delta ≤ W.model.S.scalar 0 y / 4 :=
    hdrest'''.trans (min_le_right _ _)
  have hrad : radius ≤ modelRadius delta := by
    have hh := modelRadius_anti W.eps_pos hdradius
    rwa [modelRadius, Real.sqrt_sq (inv_nonneg.mpr hradius.le), inv_inv] at hh
  have hUball : (U : Set W.model.M) ⊆ riemannianClosedBallOf (W.model.S.base.metric 0)
      W.model.basepoint (modelRadius delta) :=
    hUR.trans (riemannianClosedBallOf_mono _ _ (by
      dsimp only [radius] at hrad
      linarith))
  have hn : n ≤ modelOrder delta :=
    (Nat.ceil_mono (inv_anti₀ W.eps_pos hdalpha)).trans (Nat.le_add_right _ 1)
  have hyU : y ∈ U := by
    have hyK := houter (nk.center, 0)
      ⟨mem_univ _, neg_lt_zero.mpr (inv_pos.mpr ha), inv_pos.mpr ha⟩
    rw [nk.center_eq] at hyK
    exact hKU hyK
  have hrm : W.model.rmNormSq 0 y ≤ H ^ 2 := by
    have hh := Real.sq_sqrt (pointedFlow_rmNormSq_nonneg W.model 0 y)
    dsimp only [H]
    nlinarith [Real.sqrt_nonneg (W.model.rmNormSq 0 y)]
  have hcomp := W.scalar_sub_le_of_model_curvature_bound hH.le
    (show (0 : ℝ) ∈ Icc (-modelDepth delta) 0 from
      ⟨neg_nonpos.mpr (inv_nonneg.mpr W.eps_pos.le), le_rfl⟩) (hUball hyU) hrm
  have hnorm : metricScalarAt (rescaledMetric S t (S.scalar t x) W.scalar_pos 0)
      (W.embedding y) = (S.scalar t x)⁻¹ * S.scalar t (W.embedding y) := by
    simp only [rescaledMetric, parabolicTime, zero_div, add_zero, metricScalarAt_scaleMetric,
      SolutionOn.scalar, SolutionFamily.scalar]
  rw [hnorm] at hcomp
  have hconstant := scalarComparisonC_le (n := 3) W.eps_pos.le hd4
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hH.le)
  norm_num only [Nat.cast_ofNat, Nat.cast_pow, Nat.cast_mul, Nat.cast_add] at hconstant
  let c := S.scalar t (W.embedding y) / S.scalar t x
  have hnear_bound : |c - W.model.S.scalar 0 y| ≤ B * delta := by
    have hh : c = (S.scalar t x)⁻¹ * S.scalar t (W.embedding y) := by
      dsimp only [c]
      rw [div_eq_mul_inv, mul_comm]
    rw [hh]
    apply hcomp.trans
    dsimp only [B]
    nlinarith
  have hnear : |c - W.model.S.scalar 0 y| < min eta (W.model.S.scalar 0 y / 4) := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * B)).mp hdB
    have hm : 0 < min eta (W.model.S.scalar 0 y / 4) :=
      lt_min heta (by linarith [nk.Q_pos])
    nlinarith
  have hdc : delta < c := by
    have hh := (abs_lt.mp (hnear.trans_le (min_le_right _ _))).1
    linarith [nk.Q_pos]
  have hc : 0 < c := W.eps_pos.trans hdc
  have hcQ : c * S.scalar t x = S.scalar t (W.embedding y) :=
    div_mul_cancel₀ _ W.scalar_pos.ne'
  have hQ : 0 < S.scalar t (W.embedding y) := by
    rw [← hcQ]
    exact mul_pos hc W.scalar_pos
  have hclower : W.model.S.scalar 0 y / 2 ≤ c := by
    have hh := (abs_lt.mp (hnear.trans_le (min_le_right _ _))).1
    linarith [nk.Q_pos]
  have hcinv : c⁻¹ ≤ 2 / W.model.S.scalar 0 y := by
    have hh := inv_anti₀ (div_pos nk.Q_pos (by norm_num : (0 : ℝ) < 2)) hclower
    simpa only [inv_div] using hh
  have hsqrt : (Real.sqrt c)⁻¹ ≤ Real.sqrt (2 / W.model.S.scalar 0 y) := by
    rw [← Real.sqrt_inv]
    exact Real.sqrt_le_sqrt hcinv
  have hloss : (max 1 (Real.sqrt c)⁻¹) ^ n * delta ≤ F * delta :=
    mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _)) (max_le_max_left _ hsqrt) n)
      W.eps_pos.le
  have hbudget : F * delta ≤ beta := by
    have hh := (le_div_iff₀ hF).mp hdF
    rwa [mul_comm]
  let cmp := W.parabolicComparison hS
    (fun s hs => (W.normalized_window hreg).2 hs) c hdc n hn
  have hg : rescaledMetric S t (c * S.scalar t x) (mul_pos hc W.scalar_pos) =
      rescaledMetric S t (S.scalar t (W.embedding y)) hQ := by
    congr 1
  have C : MetricComparisonOn (rescaledMetric W.model.S 0 c hc)
      (rescaledMetric S t (S.scalar t (W.embedding y)) hQ) W.embedding
      U (Icc (-1 : ℝ) 0) n beta := by
    rw [← hg]
    exact cmp.mono hUball le_rfl (hloss.trans hbudget)
  have hFsource : (U : Set W.model.M) ⊆ W.embedding.source :=
    hUball.trans ((riemannianClosedBallOf_mono _ _
      (le_add_of_nonneg_right zero_le_one)).trans W.buffered_ball)
  have hb : -(c / delta) < -1 := by
    have hh : 1 < c / delta := (lt_div_iff₀ W.eps_pos).mpr (by simpa only [one_mul] using hdc)
    linarith
  have hscale : (delta * S.scalar t x)⁻¹ * S.scalar t (W.embedding y) = c / delta := by
    dsimp only [c]
    field_simp [W.eps_pos.ne', W.scalar_pos.ne']
  have hdomain : MapsTo (parabolicTime t (S.scalar t (W.embedding y)))
      (Icc (-(c / delta)) 0) D.carrier := by
    intro s hs
    apply W.window_mem
    dsimp only [parabolicTime]
    constructor
    · have hh : -(delta * S.scalar t x)⁻¹ ≤ s / S.scalar t (W.embedding y) := by
        apply (le_div_iff₀ hQ).mpr
        simpa only [neg_mul, hscale] using hs.1
      linarith
    · exact add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hs.2 hQ.le)
  have hregular : MapsTo (parabolicTime t (S.scalar t (W.embedding y)))
      (Ioo (-(c / delta)) 0) D.regular := by
    intro s hs
    apply hreg
    dsimp only [parabolicTime]
    constructor
    · have hh : -(delta * S.scalar t x)⁻¹ < s / S.scalar t (W.embedding y) := by
        apply (lt_div_iff₀ hQ).mpr
        simpa only [neg_mul, hscale] using hs.1
      linarith
    · exact add_lt_of_neg_right _ (div_neg_of_neg_of_pos hs.2 hQ)
  obtain ⟨nk', hnk⟩ := htransport c hc (hnear.trans_le (min_le_left _ _)) M S hS hQ
    hb hdomain hregular W.embedding hFsource rfl C
  exact ⟨nk', hnk⟩

theorem StrongNeck.exists_windowed_transport_tolerance
    {P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval}
    [PreconnectedSpace P.M]
    {alpha : ℝ} {y : P.M}
    (nk : StrongNeck P.S (neckModelTolerance alpha) y 0)
    (ha : 0 < alpha) (hsmall : alpha < 1 / 32) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D)
        (delta kappa : ℝ) (x : M) (t : ℝ)
        (W : WindowedModelWitness delta kappa S x t), delta ≤ delta₀ →
        IsSolutionOn S → Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
        ∀ hmodel : W.model = P,
          ∃ nk' : StrongNeck S (2 * alpha) (W.embedding (hmodel.symm ▸ y)) t,
            nk'.map = (hmodel.symm ▸ nk.map).trans W.embedding := by
  let _ : LocallyCompactSpace P.M := Manifold.locallyCompact_of_finiteDimensional I3
  let _ : RegularSpace P.M := inferInstance
  let _ : PseudoMetricSpace P.M := (P.S.base.metric 0).toPseudoMetricSpace
  have hba : neckModelTolerance alpha < alpha :=
    (neckModelTolerance_le_smallness alpha).trans_lt
      (backgroundJetSmallness_ceil_lt_self _ ha hsmall)
  let A : Set Cylinder := univ ×ˢ Icc (-alpha⁻¹) alpha⁻¹
  have hA : IsCompact A := isCompact_univ.prod isCompact_Icc
  have hsource : A ⊆ nk.map.source := by
    apply Subset.trans ?_ nk.domain
    intro z hz
    have hr := inv_strictAnti₀ (neckModelTolerance_pos ha) hba
    exact ⟨hz.1, (neg_lt_neg hr).trans_le hz.2.1, hz.2.2.trans_lt hr⟩
  let K := nk.map '' A
  have hK : IsCompact K := hA.image_of_continuousOn
    (nk.map.contMDiffOn_toFun.continuousOn.mono hsource)
  obtain ⟨V, hVo, hKV, hVc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  obtain ⟨R, hR, hVR⟩ := hVc.isBounded.subset_closedBall_lt 0 P.basepoint
  let U : TopologicalSpace.Opens P.M := ⟨V, hVo⟩
  have hUR : (U : Set P.M) ⊆ riemannianClosedBallOf
      (P.S.base.metric 0) P.basepoint R := by
    intro z hz
    have hd := hVR (subset_closure hz)
    change riemannianEDistOf (P.S.base.metric 0) P.basepoint z ≤ ENNReal.ofReal R
    rw [← SmoothRiemannianMetric.toPseudoMetricSpace_edist, edist_dist]
    exact ENNReal.ofReal_le_ofReal (by simpa only [Metric.mem_closedBall, dist_comm] using hd)
  exact nk.exists_windowed_transport_tolerance_on_compact ha (by linarith) U hVc hK hKV
    (by intro z hz; exact ⟨z, ⟨hz.1, hz.2.1.le, hz.2.2.le⟩, rfl⟩) hR hUR

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
