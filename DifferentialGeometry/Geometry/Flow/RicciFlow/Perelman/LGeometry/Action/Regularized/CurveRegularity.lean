import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.EndpointVariation
import DifferentialGeometry.Analysis.Calculus.Cutoff.Clamp.RadialBump
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open scoped ContDiff Manifold _root_.Topology

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] {D : RealTimeInterval}

theorem contDiffAt_lRegularizedAction_lRegularizedCurve
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (x : M) {Z : E} {b : ℝ}
    (hb0 : 0 < b) (hb : b ∈ lRegularizedDomain S T x Z) :
    ContDiffAt ℝ ∞
      (fun q : E × ℝ => lRegularizedAction S T (lRegularizedCurve S T x q.1) 0 q.2)
      (Z, b) := by
  obtain ⟨J, hJopen, hJconn, h0J, hbJ, hchosen⟩ :=
    lRegularizedChosen_spec S T x Z hb
  obtain ⟨V, hVopen, hZV, K, hKopen, hKconn, h0K, hbK,
      alpha, _halpha, hcurves⟩ :=
    lRegularizedFamily_extend S hS T hJopen hJconn h0J hbJ hchosen
  obtain ⟨rho, a, d, ha0, hbd, hrho, hrho_id, _hrhoDeriv, hrhoK⟩ :=
    DifferentialGeometry.exists_smooth_time_clamp_range_subset
      hKopen hb0 (hKconn.ordConnected.out h0K hbK)
  let z : E × ℝ := (Z, b)
  let O : Set (E × ℝ) := V ×ˢ Ioo 0 d
  have hO : IsOpen O := hVopen.prod isOpen_Ioo
  have hzO : z ∈ O := ⟨hZV, hb0, hbd⟩
  obtain ⟨eps, heps, hball⟩ := (Metric.isOpen_iff.mp hO) z hzO
  let bump : ContDiffBump (0 : E × ℝ) :=
    { rIn := eps / 2
      rOut := eps
      rIn_pos := half_pos heps
      rIn_lt_rOut := half_lt_self heps }
  let phi : E × ℝ → E × ℝ := fun q => z + bump.radial (q - z)
  have hphi : ContDiff ℝ ∞ phi :=
    contDiff_const.add (bump.radial_contDiff.comp (contDiff_id.sub contDiff_const))
  have hphiO : ∀ q : E × ℝ, phi q ∈ O := by
    intro q
    apply hball
    have hq := bump.radial_mapsTo (Set.mem_univ (q - z))
    rw [Metric.mem_ball] at hq ⊢
    change dist (z + bump.radial (q - z)) z < eps
    simpa only [dist_eq_norm, add_sub_cancel_left, sub_zero] using hq
  have hVK : V ×ˢ K ⊆ lRegularizedJointDom S T x := by
    intro q hq
    change q.2 ∈ lRegularizedDomain S T x q.1
    exact ⟨fun s => alpha (q.1, s), K, hKopen, hKconn, h0K, hq.2,
      hcurves q.1 hq.1⟩
  have hlag := (contDiffOn_lRegularizedLagrangian_lRegularizedCurve S hS T x).mono hVK
  let G : (E × ℝ) → ℝ → ℝ := fun q u =>
    (phi q).2 * lRegularizedLagrangian S T
      (lRegularizedCurve S T x (phi q).1) (rho ((phi q).2 * u))
  have hG : ContDiffOn ℝ ∞
      (fun q : (E × ℝ) × ℝ => G q.1 q.2) Set.univ := by
    intro q _hq
    have hp : ContDiffAt ℝ ∞ (fun r : (E × ℝ) × ℝ => phi r.1) q :=
      hphi.contDiffAt.comp q contDiffAt_fst
    have ht : ContDiffAt ℝ ∞
        (fun r : (E × ℝ) × ℝ => rho ((phi r.1).2 * r.2)) q :=
      hrho.contDiffAt.comp q (hp.snd.mul contDiffAt_snd)
    have hpair := hp.fst.prodMk ht
    have hmem : ((phi q.1).1, rho ((phi q.1).2 * q.2)) ∈ V ×ˢ K :=
      ⟨(hphiO q.1).1, hrhoK _⟩
    have hc := (hlag.contDiffAt
      ((hVopen.prod hKopen).mem_nhds hmem)).comp q hpair
    exact (hp.snd.mul hc).contDiffWithinAt
  let A : E × ℝ → ℝ := fun q => ∫ u in (0 : ℝ)..1, G q u
  have hA : ContDiffOn ℝ ∞ A Set.univ :=
    DifferentialGeometry.Analysis.Calculus.contDiffOn_paramIntervalIntegral
      (E₀ := E × ℝ) G hG
  let U : Set (E × ℝ) := Metric.ball z (eps / 2)
  have hU : IsOpen U := Metric.isOpen_ball
  have hzU : z ∈ U := by
    change z ∈ Metric.ball z (eps / 2)
    simpa only [Metric.mem_ball, dist_self] using half_pos heps
  have heq : A =ᶠ[𝓝 z] fun q =>
      lRegularizedAction S T (lRegularizedCurve S T x q.1) 0 q.2 := by
    filter_upwards [hU.mem_nhds hzU] with q hq
    have hrad : bump.radial (q - z) = q - z := by
      apply bump.radial_eq_self
      rw [Metric.mem_closedBall, dist_zero_right]
      simpa only [Metric.mem_ball, dist_eq_norm] using
        (Metric.mem_ball.mp hq).le
    have hphiq : phi q = q := by
      change z + bump.radial (q - z) = q
      rw [hrad]
      abel
    have hqO : q ∈ O := by simpa only [hphiq] using hphiO q
    have hclamp : Set.EqOn (fun u : ℝ => rho (q.2 * u))
        (fun u : ℝ => q.2 * u) (Icc 0 1) := by
      intro u hu
      apply hrho_id
      exact ⟨ha0.le.trans (mul_nonneg hqO.2.1.le hu.1),
        (mul_le_of_le_one_right hqO.2.1.le hu.2).trans hqO.2.2.le⟩
    have hcongr : A q = ∫ u in (0 : ℝ)..1,
        q.2 * lRegularizedLagrangian S T (lRegularizedCurve S T x q.1) (q.2 * u) := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : u ∈ Icc (0 : ℝ) 1 := by
        simpa only [Set.uIcc_of_le zero_le_one] using hu
      simp only [G, hphiq, hclamp hu']
    rw [hcongr]
    simp only [lRegularizedAction]
    simpa only [smul_eq_mul, zero_mul, one_mul, mul_zero, mul_one,
      intervalIntegral.integral_const_mul] using
      (intervalIntegral.smul_integral_comp_mul_left
        (a := (0 : ℝ)) (b := (1 : ℝ))
        (fun r => lRegularizedLagrangian S T (lRegularizedCurve S T x q.1) r) q.2)
  exact ((hA z (Set.mem_univ z)).contDiffAt Filter.univ_mem).congr_of_eventuallyEq heq.symm

theorem contDiffAt_lRegularizedAction_lRegularizedCurve_sqrt
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (x : M) {Z : E} {tau : ℝ}
    (hdom : (Z, tau) ∈ lExpPosDom S T x) :
    ContDiffAt ℝ ∞
      (fun q : E × ℝ => lRegularizedAction S T (lRegularizedCurve S T x q.1)
        0 (Real.sqrt q.2)) (Z, tau) := by
  have htau := ((mem_lExpPosDom S T x Z tau).mp hdom).1
  have hb := ((mem_lExpPosDom S T x Z tau).mp hdom).2.2
  have hA := contDiffAt_lRegularizedAction_lRegularizedCurve
    S hS T x (Real.sqrt_pos.mpr htau) hb
  have hpair : ContDiffAt ℝ ∞ (fun q : E × ℝ => (q.1, Real.sqrt q.2)) (Z, tau) :=
    contDiffAt_fst.prodMk ((Real.contDiffAt_sqrt htau.ne').comp (Z, tau) contDiffAt_snd)
  exact hA.comp (Z, tau) hpair

end DifferentialGeometry.PDE.RicciFlow.Perelman
