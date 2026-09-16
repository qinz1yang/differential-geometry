import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureModels
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalCapTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RoundModelCoveringBall

noncomputable section
open Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Filter
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {o : TangentOrientationSection M} {kappa : ℝ} {x : ℕ → M} {t : ℕ → ℝ}

omit [SigmaCompactSpace M] in
theorem BlowupLimit.eventually_deep_image
    (L : BlowupLimit S o kappa x t)
    {K : Set L.model.M} (hK : IsCompact K) {H : ℝ}
    (hdeep : ∀ y ∈ K,
      2 * H ≤ metricDistance (L.model.S.base.metric 0) L.model.basepoint y) :
    ∀ᶠ i in atTop, ∀ y ∈ (L.map i) '' K,
      H / Real.sqrt (S.scalar (t (L.subseq i)) (x (L.subseq i))) ≤
        metricDistance (S.base.metric (t (L.subseq i))) (x (L.subseq i)) y := by
  let g := L.model.S.base.metric 0
  let p := L.model.basepoint
  let _ : ConnectedSpace L.model.M := L.ancient.connected
  have hfinite (y : L.model.M) : riemannianEDistOf g p y ≠ ⊤ :=
    riemannianEDistOf_ne_top g p y
  have hcont : Continuous (fun y : L.model.M => metricDistance g p y) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (ENNReal.continuousAt_toReal (hfinite y)).comp
      (continuous_riemannianEDist g p).continuousAt
  obtain ⟨B, hB⟩ := hK.bddAbove_image hcont.continuousOn
  let rho := max B 0 + 1
  have hrho : 0 < rho := by dsimp [rho]; linarith [le_max_right B 0]
  have hKrho : K ⊆ riemannianClosedBallOf g p rho := by
    intro y hy
    have hyB : metricDistance g p y ≤ B := hB ⟨y, hy, rfl⟩
    have hyrho : metricDistance g p y ≤ rho := by
      dsimp [rho]
      linarith [le_max_left B 0]
    change riemannianEDistOf g p y ≤ ENNReal.ofReal rho
    rw [← ENNReal.ofReal_toReal (hfinite y)]
    exact ENNReal.ofReal_le_ofReal hyrho
  let R := 8 * rho
  have hR : 0 < R := by dsimp [R]; positivity
  have hcomplete : RiemannianMetricComplete g :=
    ⟨MetricComplete.complete (L.model.atTime 0) (L.ancient.complete 0 (by simp))⟩
  have hc : IsCompact (riemannianClosedBallOf g p R) :=
    RiemannianMetricComplete.closedEBall_isCompact hcomplete p R
  have hsqrt : 1 / 2 ≤ Real.sqrt (1 - (1 / 4 : ℝ)) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hroom : Real.sqrt (1 + (1 / 4 : ℝ)) * (3 * rho) <
      Real.sqrt (1 - (1 / 4 : ℝ)) * R := by
    have hsqrtstrong : 3 / 4 ≤ Real.sqrt (1 - (1 / 4 : ℝ)) := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    have hsqrtupper' : Real.sqrt (1 + (1 / 4 : ℝ)) < 3 / 2 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    dsimp [R]
    nlinarith
  have hp : p ∈ riemannianClosedBallOf g p rho := by
    change riemannianEDistOf g p p ≤ ENNReal.ofReal rho
    rw [riemannianEDistOf_self]
    exact bot_le
  filter_upwards [L.convergence (riemannianClosedBallOf g p R) hc 1 one_pos 0
    (1 / 4) (by norm_num)] with i hi
  obtain ⟨_, hsource, ⟨cmp⟩⟩ := hi
  let gi := rescaledMetric S (t (L.subseq i))
    (S.scalar (t (L.subseq i)) (x (L.subseq i))) (L.scale_pos i) 0
  have hequiv : ∀ y ∈ riemannianClosedBallOf g p R, ∀ v : TangentSpace I3 y,
      (1 - (1 / 4 : ℝ)) * g.inner y v v ≤
        gi.inner (L.map i y) (mfderiv I3 I3 (L.map i) y v) (mfderiv I3 I3 (L.map i) y v) ∧
      gi.inner (L.map i y) (mfderiv I3 I3 (L.map i) y v) (mfderiv I3 I3 (L.map i) y v) ≤
        (1 + (1 / 4 : ℝ)) * g.inner y v v := by
    intro y hy v
    have hh := cmp.equivalence 0 (by norm_num) y hy v
    rw [cmp.pullback_eq 0 y hy (fun _ => v)] at hh
    exact hh
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hy
  have hd := (crossModel_metricDistance_transfer g gi (L.map i) p hR
    (by norm_num) (by norm_num) hrho.le hc hsource hequiv hroom p hp z (hKrho hz)).1
  have hdpos : 0 ≤ metricDistance g p z := ENNReal.toReal_nonneg
  have htwo : 2 * H ≤ metricDistance g p z := hdeep z hz
  have hnormalized : H ≤ metricDistance gi (L.map i p) (L.map i z) := by
    nlinarith
  have hscale : metricDistance gi (L.map i p) (L.map i z) =
      Real.sqrt (S.scalar (t (L.subseq i)) (x (L.subseq i))) *
        metricDistance (S.base.metric (t (L.subseq i))) (x (L.subseq i)) (L.map i z) := by
    dsimp [gi]
    simp only [rescaledMetric, parabolicTime_zero, metricDistance_scaleMetric, p, L.base_eq]
  rw [hscale] at hnormalized
  exact (div_le_iff₀ (Real.sqrt_pos.mpr (L.scale_pos i))).2 (by
    simpa [mul_comm] using hnormalized)

theorem BlowupLimit.eventually_canonicalAlternative_cap
    (L : BlowupLimit S o kappa x t)
    {eps C : ℝ} {U : Set L.model.M}
    (cap : LocalCap L.model.S eps L.model.basepoint 0 U)
    (hdeep : ∀ y ∈ cap.tube,
      20000 ≤ metricDistance (L.model.S.base.metric 0) L.model.basepoint y) :
    ∀ᶠ i in atTop,
      OrderedNeckChain S eps (t (L.subseq i)) ((L.map i) '' cap.tube) →
        Nonempty (CanonicalAlternative S eps C (x (L.subseq i)) (t (L.subseq i))
          ((L.map i) '' U)) := by
  have htube : IsCompact cap.tube := by
    rw [← cap.tube_eq]
    exact (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
      (cap.tube_map.contMDiffOn_toFun.continuousOn.mono cap.tube_domain)
  have hU : IsCompact U := cap.union_eq ▸ cap.core.compact.union htube
  have hd := L.eventually_deep_image htube (H := 10000) (by
    intro y hy
    norm_num at ⊢
    exact hdeep y hy)
  filter_upwards [hd, L.convergence U hU 1 one_pos 0 1 one_pos] with i hdi hi
  intro chain
  exact canonicalAlternative_transport_cap cap (L.map i) hi.2.1 chain (L.base_eq i) hdi

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
