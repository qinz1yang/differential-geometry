import DifferentialGeometry.Geometry.Metric.Convergence.Metric.Parameter
import DifferentialGeometry.Geometry.Metric.Family.JointSmoothness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.JointRegularity
import DifferentialGeometry.Geometry.Metric.PullbackScaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StaticMetricApproximation
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.OfMetricDerivNorm
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Continuity
import DifferentialGeometry.Geometry.Metric.Convergence.Time.Lipschitz

noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N] [T2Space N]

private theorem scaled_metric_deriv_sup_continuousOn
    (g : ℝ → SmoothRiemannianMetric I N) (A : Set ℝ)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × N => (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (A ×ˢ (univ : Set N)))
    (k : SmoothRiemannianMetric I N) {K : Set N} (hK : IsCompact K) (n : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => metricDerivNormSupOn K n
      (scaleMetric (Real.exp p.1) (Real.exp_pos _) (g p.2)) k k)
      (univ ×ˢ A) := by
  apply metricDerivNormSupOn_continuousOn
    (fun p : ℝ × ℝ => scaleMetric (Real.exp p.1) (Real.exp_pos _) (g p.2))
    (fun _ => k) (fun _ => k) (U := univ) _ hK (subset_univ _) n
  intro x _
  refine ⟨(extChartAt I x).target, isOpen_extChartAt_target x, mem_extChartAt_target x,
    Subset.rfl, ?_⟩
  intro i j
  have harg : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × E => (z.1.2, z.2)) :=
    contDiff_fst.snd.prodMk contDiff_snd
  have hgram : ContDiffOn ℝ ∞ (fun z : (ℝ × ℝ) × E =>
      chartGramOnE (g z.1.2) x i j z.2) ((univ ×ˢ A) ×ˢ (extChartAt I x).target) :=
    (chartGramOnE_joint_contDiffOn g A hg x i j).comp harg.contDiffOn
      (fun _ hz => ⟨hz.1.2, hz.2⟩)
  have hexp : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × E => Real.exp z.1.1) :=
    Real.contDiff_exp.comp contDiff_fst.fst
  have hscaled := hexp.contDiffOn.mul hgram
  have hfixed : ContDiffOn ℝ ∞ (fun z : (ℝ × ℝ) × E => chartGramOnE k x i j z.2)
      ((univ ×ˢ A) ×ˢ (extChartAt I x).target) :=
    (chartGramOnE_contDiffOn k x i j).comp contDiffOn_snd (fun _ hz => hz.2)
  refine ⟨?_, hfixed, hfixed⟩
  apply hscaled.congr
  intro z _
  simp only [chartGramOnE, chartGramMatrix_apply, scaleMetric_inner]

end DifferentialGeometry.CheegerGromovCompactness

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N] [T2Space N]
  {D : RealTimeInterval}

private theorem pullback_metric_joint_contMDiffOn
    (S : SolutionOn (I := ThreeModel) (M := M) D) (hS : IsSolutionOn S)
    (Phi : N → M) (hPhi : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Phi) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
      (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
      (fun p : ℝ × N => (⟨p.2, (localPullMetric (S.base.metric p.1) Phi hPhi).inner p.2⟩ :
        TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
          (fun x => TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel x →L[ℝ] ℝ)))
      (D.regular ×ˢ (univ : Set N)) := by
  let _ : IsManifold ThreeModel 1 N := IsManifold.of_le (n := ∞) (by decide)
  let _ : IsManifold ThreeModel 1 M := IsManifold.of_le (n := ∞) (by decide)
  apply metricCLMSection_jointContMDiffOn_of_chartGram_on
    (fun t => localPullMetric (S.base.metric t) Phi hPhi) D.regular
  intro x i j
  exact chartGramMatrix_joint_contMDiffOn_of_pullback S.base.metric D.regular
    (hS.smoothMetric.metricCLMSection_contMDiffOn Subset.rfl)
    (fun t => localPullMetric (S.base.metric t) Phi hPhi) Phi hPhi.contMDiff
    (fun _ _ _ _ _ => localPullMetric_inner _ _ _ _ _ _) x i j

private theorem scaled_pullback_deriv_sup_continuousAt
    (S : SolutionOn (I := ThreeModel) (M := M) D) (hS : IsSolutionOn S)
    (Phi : N → M) (hPhi : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Phi)
    (k : SmoothRiemannianMetric ThreeModel N) {K : Set N} (hK : IsCompact K)
    (n : ℕ) {t r : ℝ} (ht : t ∈ D.regular) :
    ContinuousAt (fun p : ℝ × ℝ => metricDerivNormSupOn K n
      (scaleMetric (Real.exp p.1) (Real.exp_pos _)
        (localPullMetric (S.base.metric p.2) Phi hPhi)) k k) (r, t) := by
  have hmetric := pullback_metric_joint_contMDiffOn S hS Phi hPhi
  have hc := CheegerGromovCompactness.scaled_metric_deriv_sup_continuousOn
    (fun u => localPullMetric (S.base.metric u) Phi hPhi) D.regular hmetric k hK n
  exact hc.continuousAt ((isOpen_univ.prod D.regular_isOpen).mem_nhds ⟨mem_univ r, ht⟩)

private theorem continuousAt_comp_two {X : Type*} [TopologicalSpace X]
    {f : ℝ × ℝ → ℝ} {g : X → ℝ × ℝ} {x : X}
    (hf : ContinuousAt f (g x)) (hg : ContinuousAt g x) :
    ContinuousAt (fun z => f (g z)) x := hf.comp hg

private theorem normalized_pullback_deriv_sup_continuousAt
    (S : SolutionOn (I := ThreeModel) (M := M) D) (hS : IsSolutionOn S)
    (Phi : N → M) (hPhi : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Phi)
    (k : SmoothRiemannianMetric ThreeModel N) {K : Set N} (hK : IsCompact K)
    (n : ℕ) {t : ℝ} {x : M} (ht : t ∈ D.regular) (hQ : 0 < S.scalar t x) :
    ContinuousAt (fun z : ℝ × M => metricDerivNormSupOn K n
      (scaleMetric (Real.exp (Real.log (S.scalar z.1 z.2))) (Real.exp_pos _)
        (localPullMetric (S.base.metric z.1) Phi hPhi)) k k) (t, x) := by
  have hscalar : ContinuousAt (fun z : ℝ × M => S.scalar z.1 z.2) (t, x) :=
    (scalar_joint S hS).continuousOn.continuousAt
      ((D.regular_isOpen.prod isOpen_univ).mem_nhds ⟨ht, mem_univ _⟩)
  have hparam : ContinuousAt (fun z : ℝ × M => (Real.log (S.scalar z.1 z.2), z.1)) (t, x) :=
    (hscalar.log hQ.ne').prodMk continuousAt_fst
  have hAt := scaled_pullback_deriv_sup_continuousAt S hS Phi hPhi k hK n
    (r := Real.log (S.scalar t x)) ht
  exact continuousAt_comp_two
    (f := fun p : ℝ × ℝ => metricDerivNormSupOn K n
      (scaleMetric (Real.exp p.1) (Real.exp_pos _)
        (localPullMetric (S.base.metric p.2) Phi hPhi)) k k)
    (g := fun z : ℝ × M => (Real.log (S.scalar z.1 z.2), z.1)) hAt hparam

private theorem eventually_normalized_pullback_metric_deriv_sup_lt
    (S : SolutionOn (I := ThreeModel) (M := M) D) (hS : IsSolutionOn S)
    (Phi : N → M) (hPhi : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Phi)
    (k : SmoothRiemannianMetric ThreeModel N) {K : Set N} (hK : IsCompact K)
    (n : ℕ) {t eps : ℝ} {x : M} (ht : t ∈ D.regular) (hQ : 0 < S.scalar t x)
    (hclose : metricDerivNormSupOn K n
      (localPullMetric (scaleMetric (S.scalar t x) hQ (S.base.metric t)) Phi hPhi) k k < eps) :
    ∀ᶠ z : ℝ × M in 𝓝 (t, x), z.1 ∈ D.regular ∧
      ∃ hq : 0 < S.scalar z.1 z.2, metricDerivNormSupOn K n
        (localPullMetric (scaleMetric (S.scalar z.1 z.2) hq (S.base.metric z.1)) Phi hPhi) k k < eps := by
  have hcomp := normalized_pullback_deriv_sup_continuousAt S hS Phi hPhi k hK n ht hQ
  have hscalar : ContinuousAt (fun z : ℝ × M => S.scalar z.1 z.2) (t, x) :=
    (scalar_joint S hS).continuousOn.continuousAt
      ((D.regular_isOpen.prod isOpen_univ).mem_nhds ⟨ht, mem_univ _⟩)
  have hevent := hcomp.eventually_lt_const (by
    simpa only [localPullMetric_scaleMetric, Real.exp_log hQ] using hclose)
  have htime : ∀ᶠ z : ℝ × M in 𝓝 (t, x), z.1 ∈ D.regular :=
    continuousAt_fst.eventually (D.regular_isOpen.mem_nhds ht)
  filter_upwards [hevent, htime, hscalar.eventually (Ioi_mem_nhds hQ)] with z hz hzt hzq
  refine ⟨hzt, hzq, ?_⟩
  simpa only [localPullMetric_scaleMetric, Real.exp_log hzq] using hz

end DifferentialGeometry.PDE.RicciFlow

end

end

noncomputable section
open Set Function Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

attribute [local instance] RoundComponent.topology RoundComponent.charted RoundComponent.smooth
  RoundComponent.t2 RoundComponent.compact RoundComponent.connected

omit [T2Space M] [SigmaCompactSpace M] in
theorem RoundComponent.map_isLocalDiffeomorph
    {eps : ℝ} {x : M} {t : ℝ} {U : Set M} (R : RoundComponent S eps x t U) :
    IsLocalDiffeomorph I3 I3 ∞ R.map := by
  intro z
  exact R.map.isLocalDiffeomorphAt I3 I3 ∞ (by rw [R.source_eq]; trivial)

omit [T2Space M] [SigmaCompactSpace M] in
private theorem RoundComponent.exists_of_metric_deriv_reserve
    {eps0 eps eta : ℝ} {x y : M} {t u : ℝ} {U : Set M}
    (R : RoundComponent S eps0 x t U) (heps : 0 < eps) (hepshalf : eps ≤ 1 / 2)
    (heta : eta < eps) (hy : y ∈ U) (hq : 0 < S.scalar u y)
    (hsmall : metricDerivNormSupOn univ ⌈eps⁻¹⌉₊
      (localPullMetric (scaleMetric (S.scalar u y) hq (S.base.metric u)) R.map R.map_isLocalDiffeomorph)
      R.metric R.metric < eta) :
    ∃ R' : RoundComponent S eps y u U,
      R'.Z = R.Z ∧ HEq R'.metric R.metric ∧ HEq R'.map R.map ∧
      HEq R'.p (R.map.symm y) ∧
      metricDerivNormSupOn univ ⌈eps⁻¹⌉₊
        (localPullMetric (scaleMetric (S.scalar u y) R'.Q_pos (S.base.metric u))
          R'.map R'.map_isLocalDiffeomorph) R'.metric R'.metric < eta := by
  let _ : SigmaCompactSpace R.Z := inferInstance
  let g := localPullMetric (scaleMetric (S.scalar u y) hq (S.base.metric u))
    R.map R.map_isLocalDiffeomorph
  have hb : ∀ j ≤ ⌈eps⁻¹⌉₊, ∀ z ∈ (univ : Set R.Z),
      metricDerivNorm j g R.metric R.metric z ≤ eps := by
    intro j hj z hz
    exact ((derivNorm_le_sup isCompact_univ hj g R.metric R.metric hz).trans_lt hsmall).le.trans heta.le
  let A := MapMetricApproximationOn.ofMetricDerivNorm (K := univ) (p := ⌈eps⁻¹⌉₊)
    (F := (R.map : R.Z → M)) g R.metric
    (scaleMetric (S.scalar u y) hq (S.base.metric u)) heps (by linarith)
    (R.map.contMDiffOn_toFun.mono (by rw [R.source_eq]))
    (by intro z _ v; rw [metricTensorField_apply, localPullMetric_inner]) hb
  let cmp := MetricComparisonOn.ofMapMetricApproximation A ({0} : Set ℝ)
  let R' : RoundComponent S eps y u U := {
    Z := R.Z
    topology := R.topology
    charted := R.charted
    smooth := R.smooth
    t2 := R.t2
    compact := R.compact
    connected := R.connected
    metric := R.metric
    p := R.map.symm y
    scalar_one := R.scalar_one
    constant_curvature := R.constant_curvature
    map := R.map
    source_eq := R.source_eq
    target_eq := R.target_eq
    center_eq := R.map.right_inv' (R.target_eq.symm ▸ hy)
    Q_pos := hq
    comparison := cmp
    metric_bounds := by
      intro z v
      have hh := cmp.equivalence 0 (mem_singleton 0) z (mem_univ z) v
      have heq := cmp.pullback_eq 0 z (mem_univ z) (fun _ => v)
      rw [heq, scaleMetric_inner] at hh
      have hn := metric_inner_self_nonneg R.metric z v
      constructor
      · exact (mul_le_mul_of_nonneg_right (by linarith : (1 / 2 : ℝ) ≤ 1 - eps) hn).trans hh.1
      · exact hh.2.trans (mul_le_mul_of_nonneg_right (by linarith : 1 + eps ≤ (2 : ℝ)) hn) }
  exact ⟨R', rfl, HEq.rfl, HEq.rfl, HEq.rfl, hsmall⟩

omit [T2Space M] [SigmaCompactSpace M] in
private theorem RoundComponent.bilinear_bounds_of_metric_deriv_reserve
    {eps eta : ℝ} {n : ℕ} {x y : M} {t u : ℝ} {U : Set M}
    (R : RoundComponent S eps x t U) (hq : 0 < S.scalar u y)
    (hsmall : metricDerivNormSupOn univ n
      (localPullMetric (scaleMetric (S.scalar u y) hq (S.base.metric u)) R.map R.map_isLocalDiffeomorph)
      R.metric R.metric < eta) :
    ∀ z (v : TangentSpace I3 z),
      (1 - eta) * R.metric.inner z v v ≤ S.scalar u y * (S.base.metric u).inner (R.map z)
        (mfderiv I3 I3 R.map z v) (mfderiv I3 I3 R.map z v) ∧
      S.scalar u y * (S.base.metric u).inner (R.map z)
        (mfderiv I3 I3 R.map z v) (mfderiv I3 I3 R.map z v) ≤
          (1 + eta) * R.metric.inner z v v := by
  intro z v
  let g := localPullMetric (scaleMetric (S.scalar u y) hq (S.base.metric u))
    R.map R.map_isLocalDiffeomorph
  have hn : metricTensorErrorNorm (metricTensorField g) R.metric z ≤ eta :=
    ((derivNorm_le_sup isCompact_univ (Nat.zero_le _) g R.metric R.metric (mem_univ z)).trans_lt hsmall).le
  have h := tensor_apply_bounds_of_metricTensorErrorNorm_le (metricTensorField g) R.metric hn v
  simpa only [metricTensorField_apply, localPullMetric_inner, scaleMetric_inner, g] using h

omit [T2Space M] [SigmaCompactSpace M] in
private theorem RoundComponent.metric_deriv_sup_le
    {eps : ℝ} {x : M} {t : ℝ} {U : Set M} (R : RoundComponent S eps x t U)
    (heps : 0 ≤ eps) {n : ℕ} (hn : n ≤ ⌈eps⁻¹⌉₊) :
    metricDerivNormSupOn univ n
      (localPullMetric (scaleMetric (S.scalar t x) R.Q_pos (S.base.metric t))
        R.map R.map_isLocalDiffeomorph) R.metric R.metric ≤ eps := by
  let g := localPullMetric (scaleMetric (S.scalar t x) R.Q_pos (S.base.metric t))
    R.map R.map_isLocalDiffeomorph
  have hjet : R.comparison.jet 0 0 = metricTensorField g - metricTensorField R.metric := by
    ext z v
    rw [R.comparison.jet_zero, R.comparison.pullback_eq 0 z (mem_univ z)]
    simp only [ContMDiffSection.coe_sub, Pi.sub_apply, Tensor0SSpace.sub_apply,
      metricTensorField_apply, g, localPullMetric_inner]
  apply metricDerivNormSupOn_le_of_forall univ n g R.metric R.metric eps heps
  intro j hj z _
  have h := R.comparison.close j 0 (by simpa using hj.trans hn) 0 (mem_singleton 0) z (mem_univ z)
  rw [hjet, tensor02CovDerivNormWith_metricTensorField_sub_eq_metricDerivNorm] at h
  exact h

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

noncomputable section
open Set Filter Function Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

attribute [local instance] RoundComponent.topology RoundComponent.charted RoundComponent.smooth
  RoundComponent.t2 RoundComponent.compact RoundComponent.connected

omit [SigmaCompactSpace M] in
theorem RoundComponent.eventually_exists_of_strict_metric_deriv_bound
    (hS : IsSolutionOn S) {eps0 eps : ℝ} {x : M} {t : ℝ} {U : Set M}
    (R : RoundComponent S eps0 x t U) (hwhole : U = connectedComponent x)
    (ht : t ∈ D.regular) (heps : 0 < eps) (hepshalf : eps ≤ 1 / 2)
    (hsmall : metricDerivNormSupOn univ ⌈eps⁻¹⌉₊
      (localPullMetric (scaleMetric (S.scalar t x) R.Q_pos (S.base.metric t))
        R.map R.map_isLocalDiffeomorph) R.metric R.metric < eps) :
    ∃ eta : ℝ, 0 < eta ∧ eta < eps ∧
      ∀ᶠ z : ℝ × M in 𝓝 (t, x), z.1 ∈ D.regular ∧ U = connectedComponent z.2 ∧
        ∃ hq : 0 < S.scalar z.1 z.2,
          metricDerivNormSupOn univ ⌈eps⁻¹⌉₊
            (localPullMetric (scaleMetric (S.scalar z.1 z.2) hq (S.base.metric z.1))
              R.map R.map_isLocalDiffeomorph) R.metric R.metric < eta ∧
          (∀ p (v : TangentSpace I3 p),
            (1 - eta) * R.metric.inner p v v ≤ S.scalar z.1 z.2 * (S.base.metric z.1).inner (R.map p)
              (mfderiv I3 I3 R.map p v) (mfderiv I3 I3 R.map p v) ∧
            S.scalar z.1 z.2 * (S.base.metric z.1).inner (R.map p)
              (mfderiv I3 I3 R.map p v) (mfderiv I3 I3 R.map p v) ≤
                (1 + eta) * R.metric.inner p v v) ∧
          ∃ R' : RoundComponent S eps z.2 z.1 U,
            R'.Z = R.Z ∧ HEq R'.metric R.metric ∧ HEq R'.map R.map ∧
              HEq R'.p (R.map.symm z.2) ∧
              metricDerivNormSupOn univ ⌈eps⁻¹⌉₊
                (localPullMetric (scaleMetric (S.scalar z.1 z.2) R'.Q_pos (S.base.metric z.1))
                  R'.map R'.map_isLocalDiffeomorph) R'.metric R'.metric < eta := by
  obtain ⟨eta, heta, hetaeps⟩ := exists_between (max_lt heps hsmall)
  have hetapos : 0 < eta := (le_max_left _ _).trans_lt heta
  have hnorm : metricDerivNormSupOn univ ⌈eps⁻¹⌉₊
      (localPullMetric (scaleMetric (S.scalar t x) R.Q_pos (S.base.metric t))
        R.map R.map_isLocalDiffeomorph) R.metric R.metric < eta :=
    (le_max_right _ _).trans_lt heta
  have hnear := DifferentialGeometry.PDE.RicciFlow.eventually_normalized_pullback_metric_deriv_sup_lt S hS
    R.map R.map_isLocalDiffeomorph R.metric isCompact_univ ⌈eps⁻¹⌉₊ ht R.Q_pos hnorm
  have hxU : x ∈ U := by rw [hwhole]; exact mem_connectedComponent
  have hUopen : IsOpen U := R.target_eq ▸ R.map.open_target
  have hpoints : ∀ᶠ z : ℝ × M in 𝓝 (t, x), z.2 ∈ U :=
    continuousAt_snd.eventually (hUopen.mem_nhds hxU)
  refine ⟨eta, hetapos, hetaeps, ?_⟩
  filter_upwards [hnear, hpoints] with z hz hzu
  obtain ⟨hztime, hq, hclose⟩ := hz
  refine ⟨hztime, hwhole.trans (connectedComponent_eq (hwhole ▸ hzu)), hq, hclose,
    RoundComponent.bilinear_bounds_of_metric_deriv_reserve R hq hclose, ?_⟩
  exact RoundComponent.exists_of_metric_deriv_reserve R heps hepshalf hetaeps hzu hq hclose

omit [SigmaCompactSpace M] in
theorem RoundComponent.eventually_exists_of_lt_tolerance
    (hS : IsSolutionOn S) {eps0 eps : ℝ} {x : M} {t : ℝ} {U : Set M}
    (R : RoundComponent S eps0 x t U) (hwhole : U = connectedComponent x)
    (ht : t ∈ D.regular) (heps0 : 0 < eps0) (heps0eps : eps0 < eps)
    (hepshalf : eps ≤ 1 / 2) :
    ∃ eta : ℝ, 0 < eta ∧ eta < eps ∧
      ∀ᶠ z : ℝ × M in 𝓝 (t, x), z.1 ∈ D.regular ∧ U = connectedComponent z.2 ∧
        ∃ hq : 0 < S.scalar z.1 z.2,
          metricDerivNormSupOn univ ⌈eps⁻¹⌉₊
            (localPullMetric (scaleMetric (S.scalar z.1 z.2) hq (S.base.metric z.1))
              R.map R.map_isLocalDiffeomorph) R.metric R.metric < eta ∧
          (∀ p (v : TangentSpace I3 p),
            (1 - eta) * R.metric.inner p v v ≤ S.scalar z.1 z.2 * (S.base.metric z.1).inner (R.map p)
              (mfderiv I3 I3 R.map p v) (mfderiv I3 I3 R.map p v) ∧
            S.scalar z.1 z.2 * (S.base.metric z.1).inner (R.map p)
              (mfderiv I3 I3 R.map p v) (mfderiv I3 I3 R.map p v) ≤
                (1 + eta) * R.metric.inner p v v) ∧
          ∃ R' : RoundComponent S eps z.2 z.1 U,
            R'.Z = R.Z ∧ HEq R'.metric R.metric ∧ HEq R'.map R.map ∧
              HEq R'.p (R.map.symm z.2) ∧
              metricDerivNormSupOn univ ⌈eps⁻¹⌉₊
                (localPullMetric (scaleMetric (S.scalar z.1 z.2) R'.Q_pos (S.base.metric z.1))
                  R'.map R'.map_isLocalDiffeomorph) R'.metric R'.metric < eta := by
  exact R.eventually_exists_of_strict_metric_deriv_bound hS hwhole ht
    (heps0.trans heps0eps) hepshalf
    ((RoundComponent.metric_deriv_sup_le R heps0.le
      (Nat.ceil_mono (inv_anti₀ heps0 heps0eps.le))).trans_lt heps0eps)

omit [SigmaCompactSpace M] in
theorem isOpen_setOf_roundComponent_with_strict_metric_deriv_bound
    (hS : IsSolutionOn S) {eps : ℝ} (heps : 0 < eps) (hepshalf : eps ≤ 1 / 2) :
    IsOpen {z : ℝ × M | z.1 ∈ D.regular ∧
      ∃ R : RoundComponent S eps z.2 z.1 (connectedComponent z.2),
        metricDerivNormSupOn univ ⌈eps⁻¹⌉₊
          (localPullMetric (scaleMetric (S.scalar z.1 z.2) R.Q_pos (S.base.metric z.1))
            R.map R.map_isLocalDiffeomorph) R.metric R.metric < eps} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro z ⟨ht, R, hsmall⟩
  obtain ⟨eta, _, hetaeps, hnear⟩ :=
    R.eventually_exists_of_strict_metric_deriv_bound hS rfl ht heps hepshalf hsmall
  filter_upwards [hnear] with w hw
  obtain ⟨hwreg, hwhole, hq, hnorm, hbilin, R', hZ, hmetric, hmap, hp, hnorm'⟩ := hw
  refine ⟨hwreg, ?_⟩
  have hR : ∃ Rw : RoundComponent S eps w.2 w.1 (connectedComponent z.2),
      metricDerivNormSupOn univ ⌈eps⁻¹⌉₊
        (localPullMetric (scaleMetric (S.scalar w.1 w.2) Rw.Q_pos (S.base.metric w.1))
          Rw.map Rw.map_isLocalDiffeomorph) Rw.metric Rw.metric < eps :=
    ⟨R', hnorm'.trans hetaeps⟩
  rw [hwhole] at hR
  exact hR

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
