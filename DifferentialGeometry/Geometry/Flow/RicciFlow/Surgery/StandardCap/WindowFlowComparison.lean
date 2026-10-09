import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.InitialMetricTimeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Curvature.MovingShi
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.CurvatureMetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardMetricControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardUniformExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowFlowConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWindowRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.LocalPullbackCurvature
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.Parameter
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardLifetime

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology ENNReal BigOperators
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
universe u
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance (V : Opens ThreeSpace) : SigmaCompactSpace V :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel V.isOpen)

private theorem window_inclusion_localDiffeomorph {r R : ℝ} (h : r ≤ R) :
    IsLocalDiffeomorph ThreeModel ThreeModel ∞
      (Opens.inclusion (show standardCapWindow r ≤ standardCapWindow R from
        fun _ hx => hx.trans_le (add_le_add h (le_refl 1)))) := by
  apply DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv
    _ (contMDiff_inclusion _) _ rfl
  intro y
  rw [mfderiv_opens_incl]
  exact Function.injective_id

private theorem window_localPullback_metric {r R : ℝ} (h : r ≤ R) {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := standardCapWindow R) D) (t : ℝ) :
    (S.localPullback
      (Opens.inclusion (fun _ hx => hx.trans_le (add_le_add h (le_refl 1)) :
        standardCapWindow r ≤ standardCapWindow R))
      (window_inclusion_localDiffeomorph h)).base.metric t =
      (S.base.metric t).restrictOpenOfSubset
        (fun _ hx => hx.trans_le (add_le_add h (le_refl 1)) :
          standardCapWindow r ≤ standardCapWindow R) := by
  apply SmoothRiemannianMetric.ext_inner
  intro y v z
  change (localPullMetric (S.base.metric t) _ (window_inclusion_localDiffeomorph h)).inner y v z = _
  rw [localPullMetric_inner]
  simp only [mfderiv_opens_incl]
  rfl

private theorem restrict_metric_eq_of_index_eq
    {radius : ℕ → ℝ} (g : ∀ i, SmoothRiemannianMetric ThreeModel (standardCapWindow (radius i)))
    {i j : ℕ} (hij : i = j) {U : Opens ThreeSpace}
    (hi : U ≤ standardCapWindow (radius i)) (hj : U ≤ standardCapWindow (radius j)) :
    (g i).restrictOpenOfSubset hi = (g j).restrictOpenOfSubset hj := by
  subst j
  rfl

private theorem restrict_metric_trans {U V W : Opens ThreeSpace}
    (g : SmoothRiemannianMetric ThreeModel W) (hUV : U ≤ V) (hVW : V ≤ W) :
    (g.restrictOpenOfSubset hVW).restrictOpenOfSubset hUV =
      g.restrictOpenOfSubset (hUV.trans hVW) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rfl

private theorem exists_standard_solution_limit_of_growing_insertion_window_flows
    (P : ℕ → Type u) [∀ i, TopologicalSpace (P i)] [∀ i, ChartedSpace H (P i)]
    [∀ i, IsManifold I ∞ (P i)] [∀ i, T2Space (P i)]
    (g : ∀ i, SmoothRiemannianMetric I (P i)) (x : ∀ i, P i)
    (delta : ℕ → ℝ) (order m : ℕ → ℕ)
    (datum : ∀ i, normalizedDatum (g i) (x i) (delta i) (order i))
    (A radius error : ℕ → ℝ) (hA : ∀ i, 0 < A i)
    (w : ∀ i, CanonicalStaticInsertionWitness (datum i) (A i) (hA i)
      (radius i) (m i) (error i))
    (hm : Tendsto m atTop atTop) (herror : Tendsto error atTop (𝓝 0))
    (hradius : ∀ i : ℕ, (i : ℝ) + 1 ≤ radius i)
    {D : RealTimeInterval}
    (S : ∀ i, SolutionOn (I := ThreeModel) (M := standardCapWindow (radius i)) D)
    (hS : ∀ i, IsSolutionOn (S i))
    {T : ℝ} (hT : 0 < T) (hslab : Icc 0 T ⊆ D.carrier) (hreg : Ioo 0 T ⊆ D.regular)
    (hzero : ∀ i, (S i).base.metric 0 = (w i).windowMetric)
    (hgram : ∀ k (p : standardCapWindow (radius k)) (i j : Fin (Module.finrank ℝ ThreeSpace)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
        (fun z : ℝ × standardCapWindow (radius k) =>
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix ((S k).base.metric z.1) p z.2 i j)
        (Icc 0 T ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet))
    {K : ℝ}
    (hcurv : ∀ i, ∀ t ∈ Icc 0 T, ∀ y : standardCapWindow (radius i),
      nablaKRm04NormSqIntrinsic (S i) 0 t y ≤ K) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∃ Q : StandardSolution,
      ENNReal.ofReal T ≤ Q.val.lifetime ∧
      ∀ n : ℕ, ∀ L : Set (standardCapWindow ((n : ℝ) + 1)), IsCompact L →
        ∀ p : ℕ, ∀ e : ℝ, 0 < e → ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Ico 0 T,
          ∃ hn : (n : ℝ) + 1 ≤ radius (rho i),
          metricDerivNormSupOn L p
            (((S (rho i)).base.metric t).restrictOpenOfSubset
              (fun _ hx => hx.trans_le (add_le_add hn (le_refl 1)) :
                standardCapWindow ((n : ℝ) + 1) ≤ standardCapWindow (radius (rho i))))
            ((Q.val.metric t).restrictOpen (standardCapWindow ((n : ℝ) + 1)))
            (metric.restrictOpen (standardCapWindow ((n : ℝ) + 1))) < e := by
  let R : ℕ → ℝ := fun n => (n : ℝ) + 1
  have hR (n : ℕ) : 0 < R n := by dsimp only [R]; positivity
  have hsub (n i : ℕ) : R n ≤ radius (n + i) := by
    have hh := hradius (n+i)
    dsimp only [R] at *
    push_cast at hh ⊢
    linarith
  have hsubOpen (n i : ℕ) : standardCapWindow (R n) ≤ standardCapWindow (radius (n+i)) :=
    fun _ hx => hx.trans_le (add_le_add (hsub n i) (le_refl 1))
  let inc (n i : ℕ) : standardCapWindow (R n) → standardCapWindow (radius (n+i)) :=
    Opens.inclusion (hsubOpen n i)
  let hi (n i : ℕ) : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (inc n i) :=
    window_inclusion_localDiffeomorph (hsub n i)
  let F (n i : ℕ) := (S (n+i)).localPullback (inc n i) (hi n i)
  let W (n i : ℕ) := (w (n+i)).restrictWindow (hR n) (hsub n i)
  have hF (n i : ℕ) : IsSolutionOn (F n i) := (hS (n+i)).localPullback (inc n i) (hi n i)
  have hFeq (n i : ℕ) (t : ℝ) : (F n i).base.metric t =
      ((S (n+i)).base.metric t).restrictOpenOfSubset (hsubOpen n i) :=
    window_localPullback_metric (hsub n i) (S (n+i)) t
  have hFzero (n i : ℕ) : (F n i).base.metric 0 = (W n i).windowMetric := by
    rw [hFeq, hzero, CanonicalStaticInsertionWitness.restrictWindow_windowMetric]
  have hFm (n : ℕ) : Tendsto (fun i => m (n+i)) atTop atTop :=
    by simpa only [Function.comp_def, Nat.add_comm] using hm.comp (tendsto_add_atTop_nat n)
  have hFerr (n : ℕ) : Tendsto (fun i => error (n+i)) atTop (𝓝 0) :=
    by simpa only [Function.comp_def, Nat.add_comm] using herror.comp (tendsto_add_atTop_nat n)
  have hFradius : Tendsto R atTop atTop := by
    apply tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    change (n : ℝ) ≤ (n : ℝ)+1
    linarith
  have hFgram (n k : ℕ) :=
    (S (n+k)).localPullback_chartGramMatrix_joint_contMDiffOn (inc n k) (hi n k)
      (Icc 0 T) (hgram (n+k))
  have hFcompat : ∀ n l, ∀ᶠ i in atTop, ∀ t ∈ Icc 0 T,
      ((F n (i-n)).base.metric t).restrictOpenOfSubset
        (inf_le_left : standardCapWindow (R n) ⊓ standardCapWindow (R l) ≤ _) =
      ((F l (i-l)).base.metric t).restrictOpenOfSubset
        (inf_le_right : standardCapWindow (R n) ⊓ standardCapWindow (R l) ≤ _) := by
    intro n l
    filter_upwards [eventually_ge_atTop (max n l)] with i hidx
    intro t _
    rw [hFeq, hFeq, restrict_metric_trans, restrict_metric_trans]
    apply restrict_metric_eq_of_index_eq (fun k => (S k).base.metric t)
    omega
  have hFcurv : ∀ n, ∀ᶠ i in atTop, ∀ t ∈ Icc 0 T, ∀ y : standardCapWindow (R n),
      nablaKRm04NormSqIntrinsic (F n i) 0 t y ≤ K := by
    intro n
    exact Eventually.of_forall fun i t ht y => by
      have he : nablaKRm04NormSqIntrinsic (F n i) 0 t y =
          nablaKRm04NormSqIntrinsic (S (n+i)) 0 t (inc n i y) := by
        simp only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero]
        exact normSq0S_metricRm04At_localPullMetric ((S (n+i)).base.metric t) (inc n i) (hi n i) y
      rw [he]
      exact hcurv (n+i) t ht (inc n i y)
  obtain ⟨rho, hrho, Q, hQ, hconv⟩ :=
    exists_standard_solution_limit_of_compatible_insertion_window_flows
      (fun n i => P (n+i)) (fun n i => g (n+i)) (fun n i => x (n+i))
      (fun n i => delta (n+i)) (fun n i => order (n+i)) (fun n i => m (n+i))
      (fun n i => datum (n+i)) (fun n i => A (n+i)) (fun n i => error (n+i))
      (fun n i => hA (n+i)) R hFradius W hFm hFerr F hF hT hslab hreg
      hFzero hFgram id hFcompat hFcurv
  refine ⟨rho, hrho, Q, hQ, ?_⟩
  intro n L hL p e he
  obtain ⟨j, hj⟩ := hconv n L hL p e he
  refine ⟨max j n, fun i hidx t ht => ?_⟩
  have hnidx : n ≤ rho i := ((le_max_right _ _).trans hidx).trans (hrho.id_le i)
  have hn : (n : ℝ)+1 ≤ radius (rho i) := by
    have hcast : (n : ℝ) ≤ (rho i : ℕ) := Nat.cast_le.mpr hnidx
    linarith [hradius (rho i)]
  refine ⟨hn, ?_⟩
  have hh := hj i ((le_max_left _ _).trans hidx) t ht
  rw [hFeq] at hh
  have heq : (((S (n+(rho i-n))).base.metric t).restrictOpenOfSubset
      (show standardCapWindow (R n) ≤ standardCapWindow (radius (n+(rho i-n))) from
        fun _ hx => hx.trans_le (add_le_add (hsub n (rho i-n)) (le_refl 1)))) =
      ((S (rho i)).base.metric t).restrictOpenOfSubset
        (show standardCapWindow (R n) ≤ standardCapWindow (radius (rho i)) from
          fun _ hx => hx.trans_le (add_le_add hn (le_refl 1))) :=
    restrict_metric_eq_of_index_eq (fun k => (S k).base.metric t) (Nat.add_sub_of_le hnidx) _ _
  exact heq ▸ hh


theorem exists_uniform_standard_cap_comparison_of_curvature_bound
    (T K r ε : ℝ) (hT : 0 < T) (hε : 0 < ε) (p : ℕ) :
    ∃ R : ℝ, 0 < R ∧ r < R ∧ ∃ m₀ : ℕ, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
        [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A}
        {D : ℝ} {m : ℕ} {ζ : ℝ}
        (w : CanonicalStaticInsertionWitness d A hA D m ζ),
      R ≤ D → m₀ ≤ m → ζ ≤ ε₀ →
      ∀ S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
          (RealTimeInterval.closed 0 T hT.le),
        IsSolutionOn S → S.base.metric 0 = w.windowMetric →
        (∀ (y : standardCapWindow D) (i j : Fin (Module.finrank ℝ ThreeSpace)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
            (fun z : ℝ × standardCapWindow D =>
              DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric z.1) y z.2 i j)
            (Icc 0 T ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) y).baseSet)) →
        (∀ t ∈ Icc 0 T, ∀ y : standardCapWindow D,
          nablaKRm04NormSqIntrinsic S 0 t y ≤ K) →
        ∃ Q : StandardSolution, ENNReal.ofReal T ≤ Q.val.lifetime ∧
          ∀ t ∈ Ico 0 T,
            metricDerivNormSupOn {y : standardCapWindow D | ‖y.val‖ ≤ r} p
              (S.base.metric t) ((Q.val.metric t).restrictOpen (standardCapWindow D))
              (metric.restrictOpen (standardCapWindow D)) < ε := by
  classical
  by_contra! hfail
  have hbad (n : ℕ) := hfail (max (max 1 (r+1)) ((n : ℝ)+1)) (by positivity)
    (lt_of_lt_of_le (by linarith [le_max_right 1 (r+1)] : r < max 1 (r+1)) (le_max_left _ _)) n
    (((n : ℝ)+1)⁻¹) (by positivity)
  choose P htop hchart hman hsep g x delta order datum A hA radius m error w
    hRadius hm herror S hS hzero hgram hcurv hbad using hbad
  let (n : ℕ) : TopologicalSpace (P n) := htop n
  let (n : ℕ) : ChartedSpace H (P n) := hchart n
  let (n : ℕ) : IsManifold I ∞ (P n) := hman n
  let (n : ℕ) : T2Space (P n) := hsep n
  have hmLimit : Tendsto m atTop atTop := tendsto_atTop_mono hm tendsto_id
  have herrorLimit : Tendsto error atTop (𝓝 0) := by
    apply squeeze_zero (fun n => (w n).accuracy_pos.le) herror
    simpa only [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ)/((n : ℝ)+1)) atTop (𝓝 0))
  have hRadiusLower (n : ℕ) : (n : ℝ)+1 ≤ radius n :=
    (le_max_right _ _).trans (hRadius n)
  obtain ⟨rho, hrho, Q, hQ, hconv⟩ :=
    exists_standard_solution_limit_of_growing_insertion_window_flows
      P g x delta order m datum A radius error hA w hmLimit herrorLimit hRadiusLower S hS
      hT Subset.rfl Subset.rfl hzero hgram hcurv
  obtain ⟨n, hn⟩ := exists_nat_gt r
  let L : Set (standardCapWindow ((n : ℝ)+1)) := {y | ‖y.val‖ ≤ r}
  have hL : IsCompact L := by
    have hc : IsCompact {y : ThreeSpace | ‖y‖ ≤ r} := by
      simpa only [Metric.closedBall, dist_zero_right] using isCompact_closedBall (0 : ThreeSpace) r
    exact _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hc (by
      intro y hy
      refine ⟨⟨y, ?_⟩, rfl⟩
      change ‖y‖ < (n : ℝ)+1+1
      change ‖y‖ ≤ r at hy
      linarith)
  obtain ⟨j, hj⟩ := hconv n L hL p (ε/2) (by positivity)
  obtain ⟨t, ht, hbad⟩ := hbad (rho j) Q hQ
  obtain ⟨hnradius, hclose⟩ := hj j le_rfl t ht
  let hsub : standardCapWindow ((n : ℝ)+1) ≤ standardCapWindow (radius (rho j)) :=
    fun _ hy => hy.trans_le (add_le_add hnradius (le_refl 1))
  have hbound : metricDerivNormSupOn {y : standardCapWindow (radius (rho j)) | ‖y.val‖ ≤ r}
      p ((S (rho j)).base.metric t)
      ((Q.val.metric t).restrictOpen (standardCapWindow (radius (rho j))))
      (metric.restrictOpen (standardCapWindow (radius (rho j)))) ≤ ε/2 := by
    apply metricDerivNormSupOn_le_of_forall _ _ _ _ _ _ (by positivity)
    intro l hl y hy
    let z : standardCapWindow ((n : ℝ)+1) := ⟨y.val, by
      change ‖y.val‖ < (n : ℝ)+1+1
      change ‖y.val‖ ≤ r at hy
      linarith⟩
    have hz : z ∈ L := hy
    have hpoint := (derivNorm_le_sup hL hl _ _ _ hz).trans_lt hclose
    have heq := metricDerivNorm_flat hsub ((S (rho j)).base.metric t)
      ((Q.val.metric t).restrictOpen (standardCapWindow (radius (rho j))))
      (metric.restrictOpen (standardCapWindow (radius (rho j)))) l z
    rw [SmoothRiemannianMetric.restrictOpen_flat, SmoothRiemannianMetric.restrictOpen_flat] at heq
    exact (heq ▸ hpoint).le
  linarith


private theorem exists_standard_cap_comparison_on_closed_interval_at_fixed_time
    (T K r ε : ℝ) (hT : 0 < T) (hT1 : T < 1) (hε : 0 < ε) (p : ℕ) :
    ∃ R : ℝ, 0 < R ∧ r < R ∧ ∃ m₀ : ℕ, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
        [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A}
        {D : ℝ} {m : ℕ} {ζ : ℝ}
        (w : CanonicalStaticInsertionWitness d A hA D m ζ),
      R ≤ D → m₀ ≤ m → ζ ≤ ε₀ →
      ∀ S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
          (RealTimeInterval.closed 0 T hT.le),
        IsSolutionOn S → S.base.metric 0 = w.windowMetric →
        (∀ (y : standardCapWindow D) (i j : Fin (Module.finrank ℝ ThreeSpace)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
            (fun z : ℝ × standardCapWindow D =>
              DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric z.1) y z.2 i j)
            (Icc 0 T ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) y).baseSet)) →
        (∀ t ∈ Icc 0 T, ∀ y : standardCapWindow D,
          nablaKRm04NormSqIntrinsic S 0 t y ≤ K) →
        ∃ Q : StandardSolution, ENNReal.ofReal T < Q.val.lifetime ∧
          ∀ t ∈ Icc 0 T,
            metricDerivNormSupOn {y : standardCapWindow D | ‖y.val‖ ≤ r} p
              (S.base.metric t) ((Q.val.metric t).restrictOpen (standardCapWindow D))
              (metric.restrictOpen (standardCapWindow D)) < ε := by
  obtain ⟨R, hR, hrR, m₀, ε₀, hε₀, hcompare⟩ :=
    exists_uniform_standard_cap_comparison_of_curvature_bound (I := I) T K r (ε/2) hT
      (by positivity) p
  refine ⟨R, hR, hrR, m₀, ε₀, hε₀, ?_⟩
  intro M _ _ _ _ g x₀ δ k d A hA D m ζ w hRD hm hζ S hS hzero hgram hcurv
  obtain ⟨Q, _, hclose⟩ := hcompare w hRD hm hζ S hS hzero hgram hcurv
  have hQlife : ENNReal.ofReal T < Q.val.lifetime := by
    rw [Q.lifetime_eq_one]
    exact ENNReal.ofReal_lt_one.mpr hT1
  have hQslab : Icc 0 T ⊆ Q.val.domain :=
    (Icc_subset_lifetimeInterval_iff Q.val.lifetime Q.val.lifetime_pos T hT.le).mpr hQlife
  let gQ := fun t => (Q.val.metric t).restrictOpen (standardCapWindow D)
  let gRef := metric.restrictOpen (standardCapWindow D)
  have hQgram := chartGram_contMDiffOn_of_cartesian Q.val.metric (Icc 0 T)
    (Q.val.smooth.mono (prod_mono hQslab Subset.rfl))
  have hQjoint := metricCLMSection_jointContMDiffOn_of_chartGram_on Q.val.metric (Icc 0 T) hQgram
  have hQrestricted := chartGramMatrix_joint_contMDiffOn_of_pullback
    Q.val.metric (Icc 0 T) hQjoint gQ
    (Subtype.val : standardCapWindow D → ThreeSpace) (contMDiff_subtype_val (U := standardCapWindow D))
    (fun t _ y v z => by
      rw [mfderiv_subtype_val_apply, mfderiv_subtype_val_apply]
      rfl)
  have hQrestrictedJoint := metricCLMSection_jointContMDiffOn_of_chartGram_on gQ (Icc 0 T) hQrestricted
  have hSjoint := metricCLMSection_jointContMDiffOn_of_chartGram_on S.base.metric (Icc 0 T) hgram
  let L : Set (standardCapWindow D) := {y | ‖y.val‖ ≤ r}
  have hL : IsCompact L := by
    have hc : IsCompact {y : ThreeSpace | ‖y‖ ≤ r} := by
      simpa only [Metric.closedBall, dist_zero_right] using isCompact_closedBall (0 : ThreeSpace) r
    exact _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hc (by
      intro y hy
      refine ⟨⟨y, ?_⟩, rfl⟩
      change ‖y‖ < D+1
      change ‖y‖ ≤ r at hy
      linarith)
  have hcont : ContinuousOn
      (fun t => metricDerivNormSupOn L p (S.base.metric t) (gQ t) gRef) (Icc 0 T) := by
    apply metricDerivNormSupOn_continuousOn S.base.metric gQ (fun _ => gRef)
      (U := univ) _ hL (subset_univ _) p
    intro y _
    refine ⟨(extChartAt ThreeModel y).target, isOpen_extChartAt_target y,
      (extChartAt ThreeModel y).map_source (mem_extChartAt_source y), Subset.rfl, ?_⟩
    intro i j
    refine ⟨chartGramOnE_joint_contDiffOn S.base.metric (Icc 0 T) hSjoint y i j,
      chartGramOnE_joint_contDiffOn gQ (Icc 0 T) hQrestrictedJoint y i j, ?_⟩
    exact (DifferentialGeometry.Geometry.Operator.chartGramOnE_contDiffOn gRef y i j).comp
      contDiffOn_snd (fun z hz => hz.2)
  refine ⟨Q, hQlife, fun t ht => ?_⟩
  have hbound : metricDerivNormSupOn L p (S.base.metric t) (gQ t) gRef ≤ ε/2 := by
    change metricDerivNormSupOn {y : standardCapWindow D | ‖y.val‖ ≤ r} p (S.base.metric t)
      ((Q.val.metric t).restrictOpen (standardCapWindow D))
      (metric.restrictOpen (standardCapWindow D)) ≤ ε/2
    apply le_on_closure (fun s hs => (hclose s hs).le)
      (by
        rw [closure_Ico (a := (0 : ℝ)) (b := T) hT.ne]
        exact hcont) continuousOn_const
    rw [closure_Ico (a := (0 : ℝ)) (b := T) hT.ne]
    exact ht
  exact hbound.trans_lt (by linarith)

private theorem exists_uniform_window_flow_metric_time_lipschitz
    (p : ℕ) (D r T K : ℝ) (hr : 0 < r) (hfit : 32 * r < D) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {m : ℕ} {ζ : ℝ}
        (w : CanonicalStaticInsertionWitness d A hA D m ζ),
      ζ ≤ 1/2 → p+2 ≤ m →
      ∀ (J : RealTimeInterval) (θ : ℝ), 0 < θ → θ ≤ T →
        Icc 0 θ ⊆ J.carrier → Ioo 0 θ ⊆ J.regular →
        ∀ S : SolutionOn (I := ThreeModel) (M := standardCapWindow D) J,
          IsSolutionOn S → S.base.metric 0 = w.windowMetric →
          (∀ (y : standardCapWindow D) (i j : Fin (Module.finrank ℝ ThreeSpace)),
            ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
              (fun z : ℝ × standardCapWindow D =>
                DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric z.1) y z.2 i j)
              (Icc 0 θ ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) y).baseSet)) →
          (∀ t ∈ Icc 0 θ, ∀ y : standardCapWindow D, ‖y.val‖ ≤ 32 * r →
            nablaKRm04NormSqIntrinsic S 0 t y ≤ K) →
          ∀ V : Set (standardCapWindow D), V ⊆ {y | ‖y.val‖ < r} →
            ∀ s ∈ Icc 0 θ, ∀ t ∈ Icc 0 θ,
              metricDerivNormSupOn V p (S.base.metric s) (S.base.metric t)
                (metric.restrictOpen (standardCapWindow D)) ≤ L*|s-t| := by
  let U : Set (standardCapWindow D) := {y | ‖y.val‖ < r}
  let gRef := metric.restrictOpen (standardCapWindow D)
  have hU : IsOpen U := isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const
  obtain ⟨B, hB, hjets⟩ :=
    exists_uniform_window_flow_curvature_derivative_bound_of_local_curvature_bounded_horizon
      p (32 * r) T K (by positivity)
  obtain ⟨C, hC, hRic⟩ := exists_movingShiBoundOn_constant_of_curvature_derivative_bounds
    (I := ThreeModel) (M := standardCapWindow D) p (fun _ => Real.sqrt B)
  let Λ := 2*Real.exp (18*Real.sqrt K*max T 0)
  have hΛ : 1 ≤ Λ := by
    have hh : 1 ≤ Real.exp (18*Real.sqrt K*max T 0) := Real.one_le_exp (by positivity)
    dsimp only [Λ]
    linarith
  obtain ⟨L, hL, hbound⟩ := exists_metricDerivNormSupOn_time_lipschitz_of_finite_ricci_bounds
    U hU gRef p T Λ C hΛ hC (fun _ => 1/2) (by intros; norm_num)
  refine ⟨L, hL, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA m ζ w hζ hm
    J θ hθ hθT hslab hreg S hS hzero hgram hcurv
  have hjet := hjets w hζ hm hfit J θ hθ hθT hslab hreg S hS hzero hgram hcurv
  have hShi : MovingShiBoundOn U 0 θ (fun _ t => S.base.metric t) p C := by
    apply hRic
    intro j hj _ t ht y hy
    have hh := hjet j hj t ht y (by
      change ‖y.val‖ < r at hy
      have heq : (32 * r)/32 = r := by ring
      rw [heq]
      exact hy.le)
    rw [← curvNormSq_eq] at hh
    exact Real.sqrt_le_sqrt hh
  have hinit : ∀ j, 1 ≤ j → j ≤ p → ∀ y ∈ U,
      metricCovDerivNorm j (S.base.metric 0) gRef y ≤ 1/2 := by
    intro j hj hjp y hy
    rw [hzero]
    change ‖y.val‖ < r at hy
    have hh := w.window_metricCovDerivNorm_le (by omega : j ≤ m) (by linarith : ‖y.val‖ < D)
    rw [standardCapMetric_eq_metric] at hh
    simp only [ite_eq_right (by omega : j ≠ 0), zero_add] at hh
    exact hh.trans hζ
  have hequiv : ∀ t ∈ Icc 0 θ, MetricUniformEquivalentOn U gRef (S.base.metric t) Λ := by
    intro t ht
    refine ⟨hΛ, ?_⟩
    intro y hy v
    change ‖y.val‖ < r at hy
    have hsq : ∀ u ∈ Icc 0 θ, normSq0S (S.base.metric u) y 4 (S.base.rm04 u y) ≤ K := by
      intro u hu
      simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero] using
        hcurv u hu y (by linarith)
    have hb := metric_inner_exp_bounds_of_curvature_bound S hS hslab hreg y hsq ht
      ⟨le_rfl, hθ.le⟩ v
    rw [hzero, sub_zero, abs_of_nonneg ht.1] at hb
    have hdim : (Module.finrank ℝ ThreeSpace : ℝ) = 3 := by simp [ThreeSpace]
    rw [hdim, show 2*(3:ℝ)^2=18 by norm_num] at hb
    have hi := w.window_inner_bounds hζ (by linarith : ‖y.val‖ < D) v
    rw [standardCapMetric_eq_metric] at hi
    change (1/2:ℝ)*gRef.inner y v v ≤ w.windowMetric.inner y v v ∧
      w.windowMetric.inner y v v ≤ (3/2:ℝ)*gRef.inner y v v at hi
    have hn := metric_inner_self_nonneg gRef y v
    have htT : t ≤ max T 0 := (ht.2.trans hθT).trans (le_max_left _ _)
    have he : Real.exp (18*Real.sqrt K*t) ≤ Real.exp (18*Real.sqrt K*max T 0) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htT (by positivity))
    have hne : Real.exp (-(18*Real.sqrt K*max T 0)) ≤ Real.exp (-(18*Real.sqrt K*t)) :=
      Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left htT (by positivity)))
    constructor
    · have hl := (mul_le_mul hne hi.1 (mul_nonneg (by norm_num) hn) (Real.exp_nonneg _)).trans hb.1
      have heq : Λ⁻¹ = Real.exp (-(18*Real.sqrt K*max T 0))*(1/2) := by
        simp only [Λ, mul_inv_rev, ← Real.exp_neg]
        norm_num
      rw [heq, mul_assoc]
      exact hl
    · have hu := hb.2.trans (mul_le_mul he hi.2 (metric_inner_self_nonneg _ _ _) (Real.exp_nonneg _))
      dsimp only [Λ]
      nlinarith [mul_nonneg (Real.exp_nonneg (18*Real.sqrt K*max T 0)) hn]
  exact hbound J θ hθ.le hθT hreg S hS hgram hequiv hinit hShi

private theorem exists_uniform_window_flow_metric_time_lipschitz_of_radius_lower_bound
    (p : ℕ) (r T K : ℝ) :
    ∃ R L : ℝ, 0 < R ∧ r < R ∧ 0 ≤ L ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A}
        {D : ℝ} {m : ℕ} {ζ : ℝ} (w : CanonicalStaticInsertionWitness d A hA D m ζ),
      R ≤ D → ζ ≤ 1/2 → p+2 ≤ m →
      ∀ (J : RealTimeInterval) (θ : ℝ), 0 < θ → θ ≤ T →
        Icc 0 θ ⊆ J.carrier → Ioo 0 θ ⊆ J.regular →
        ∀ S : SolutionOn (I := ThreeModel) (M := standardCapWindow D) J,
          IsSolutionOn S → S.base.metric 0 = w.windowMetric →
          (∀ (y : standardCapWindow D) (i j : Fin (Module.finrank ℝ ThreeSpace)),
            ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
              (fun z : ℝ × standardCapWindow D =>
                DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric z.1) y z.2 i j)
              (Icc 0 θ ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) y).baseSet)) →
          (∀ t ∈ Icc 0 θ, ∀ y : standardCapWindow D,
            nablaKRm04NormSqIntrinsic S 0 t y ≤ K) →
          ∀ s ∈ Icc 0 θ, ∀ t ∈ Icc 0 θ, ∀ j ≤ p,
            ∀ y : standardCapWindow D, ‖y.val‖ ≤ r →
              metricDerivNorm j (S.base.metric s) (S.base.metric t)
                (metric.restrictOpen (standardCapWindow D)) y ≤ L*|s-t| := by
  let a := max 1 (r+1)
  let R := 32*a+1
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hr : r < a := by dsimp only [a]; linarith [le_max_right 1 (r+1)]
  have hR : 0 < R := by dsimp only [R]; positivity
  have haR : 32*a < R := by dsimp only [R]; linarith
  obtain ⟨L, hL, hbound⟩ := exists_uniform_window_flow_metric_time_lipschitz p R a T K ha haR
  refine ⟨R, L, hR, by linarith, hL, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA D m ζ w hRD hζ hm
    J θ hθ hθT hslab hreg S hS hzero hgram hcurv s hs t ht j hj y hy
  let hsub : standardCapWindow R ≤ standardCapWindow D :=
    fun _ hx => hx.trans_le (add_le_add hRD (le_refl 1))
  let inc : standardCapWindow R → standardCapWindow D := TopologicalSpace.Opens.inclusion hsub
  have hi : IsLocalDiffeomorph ThreeModel ThreeModel ∞ inc :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv
      inc (contMDiff_inclusion hsub) (fun z => by
        change Function.Injective (mfderiv ThreeModel ThreeModel (TopologicalSpace.Opens.inclusion hsub) z)
        rw [mfderiv_opens_incl]
        exact Function.injective_id) rfl
  let F := S.localPullback inc hi
  have heq (u : ℝ) : F.base.metric u = (S.base.metric u).restrictOpenOfSubset hsub := by
    apply SmoothRiemannianMetric.ext_inner
    intro z v q
    change (localPullMetric (S.base.metric u) inc hi).inner z v q = _
    rw [localPullMetric_inner]
    simp only [inc, mfderiv_opens_incl]
    rfl
  have hFzero : F.base.metric 0 = (w.restrictWindow hR hRD).windowMetric := by
    rw [heq, hzero, CanonicalStaticInsertionWitness.restrictWindow_windowMetric]
  have hFgram := S.localPullback_chartGramMatrix_joint_contMDiffOn inc hi (Icc 0 θ) hgram
  have hFcurv : ∀ u ∈ Icc 0 θ, ∀ z : standardCapWindow R, ‖z.val‖ ≤ 32*a →
      nablaKRm04NormSqIntrinsic F 0 u z ≤ K := by
    intro u hu z _
    have hh := hcurv u hu (inc z)
    have he : nablaKRm04NormSqIntrinsic F 0 u z = nablaKRm04NormSqIntrinsic S 0 u (inc z) := by
      simp only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero]
      exact normSq0S_metricRm04At_localPullMetric (S.base.metric u) inc hi z
    exact he.trans_le hh
  let z : standardCapWindow R := ⟨y.val, by change ‖y.val‖ < R+1; linarith⟩
  have hz : ({z} : Set (standardCapWindow R)) ⊆ {x | ‖x.val‖ < a} := by
    intro x hx
    rw [mem_singleton_iff] at hx
    subst x
    exact hy.trans_lt hr
  have hb := hbound (w.restrictWindow hR hRD) hζ hm J θ hθ hθT hslab hreg F
    (hS.localPullback inc hi) hFzero hFgram hFcurv {z} hz s hs t ht
  have hp := (derivNorm_le_sup isCompact_singleton hj _ _ _ (mem_singleton z)).trans hb
  rw [heq, heq] at hp
  have hn := metricDerivNorm_flat hsub (S.base.metric s) (S.base.metric t)
    (metric.restrictOpen (standardCapWindow D)) j z
  rw [SmoothRiemannianMetric.restrictOpen_flat] at hn
  exact hn ▸ hp

theorem exists_uniform_standard_cap_comparison_on_bounded_intervals_of_curvature_bound
    (Θ K r ε : ℝ) (hΘ : 0 < Θ) (hΘ1 : Θ < 1) (hε : 0 < ε) (p : ℕ) :
    ∃ R : ℝ, 0 < R ∧ r < R ∧ ∃ m₀ : ℕ, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
        [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A}
        {D : ℝ} {m : ℕ} {ζ : ℝ}
        (w : CanonicalStaticInsertionWitness d A hA D m ζ),
      R ≤ D → m₀ ≤ m → ζ ≤ ε₀ →
      ∀ (T : ℝ) (hT : 0 < T), T ≤ Θ →
      ∀ S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
          (RealTimeInterval.closed 0 T hT.le),
        IsSolutionOn S → S.base.metric 0 = w.windowMetric →
        (∀ (y : standardCapWindow D) (i j : Fin (Module.finrank ℝ ThreeSpace)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
            (fun z : ℝ × standardCapWindow D =>
              DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric z.1) y z.2 i j)
            (Icc 0 T ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) y).baseSet)) →
        (∀ t ∈ Icc 0 T, ∀ y : standardCapWindow D,
          nablaKRm04NormSqIntrinsic S 0 t y ≤ K) →
        ∃ Q : StandardSolution, ENNReal.ofReal T < Q.val.lifetime ∧
          ∀ t ∈ Icc 0 T,
            metricDerivNormSupOn {y : standardCapWindow D | ‖y.val‖ ≤ r} p
              (S.base.metric t) ((Q.val.metric t).restrictOpen (standardCapWindow D))
              (metric.restrictOpen (standardCapWindow D)) < ε := by
  classical
  obtain ⟨R₁, L, hR₁, hrR₁, hL, hLip⟩ :=
    exists_uniform_window_flow_metric_time_lipschitz_of_radius_lower_bound p r Θ K
  have hΘlife : ENNReal.ofReal Θ < uniformStandardLifetime := by
    rw [uniformStandardLifetime_eq_one]
    exact ENNReal.ofReal_lt_one.mpr hΘ1
  obtain ⟨hlife, Kstd, hKstd, hKbound⟩ := uniformStandardLifetime_slab Θ hΘ.le hΘlife
  obtain ⟨Λ, hΛ, Cstd, Lstd, hCstd, hLstd, hstd⟩ :=
    standard_metric_bounds_on_shorter_windows Θ Kstd hΘ.le hKstd
  let Lsum := ∑ k ∈ Finset.range (p+1), Lstd k
  have hLsum : 0 ≤ Lsum := Finset.sum_nonneg (fun k _ => hLstd k)
  have hStdLip : ∀ Q : StandardSolution, ∀ s ∈ Icc 0 Θ, ∀ t ∈ Icc 0 Θ,
      ∀ j ≤ p, ∀ x : ThreeSpace,
        metricDerivNorm j (Q.val.metric s) (Q.val.metric t) metric x ≤ Lsum*|s-t| := by
    intro Q s hs t ht j hj x
    have hh := (hstd Q.val Θ hΘ.le le_rfl (hlife Q) (hKbound Q)).2.2 j s hs t ht x
    have hjsum : Lstd j ≤ Lsum := Finset.single_le_sum (fun k _ => hLstd k)
      (Finset.mem_range.mpr (by omega))
    exact hh.trans (mul_le_mul_of_nonneg_right hjsum (abs_nonneg _))
  by_contra! hfail
  have hbad (n : ℕ) := hfail (max R₁ ((n : ℝ)+1))
    (hR₁.trans_le (le_max_left _ _)) (hrR₁.trans_le (le_max_left _ _)) (n+p+2)
    (min (1/2) ((n : ℝ)+1)⁻¹) (by positivity)
  choose P htop hchart hman hsep g x delta order datum A hA radius m error w
    hRadius hm herror T hT hTΘ S hS hzero hgram hcurv hbad using hbad
  let (n : ℕ) : TopologicalSpace (P n) := htop n
  let (n : ℕ) : ChartedSpace H (P n) := hchart n
  let (n : ℕ) : IsManifold I ∞ (P n) := hman n
  let (n : ℕ) : T2Space (P n) := hsep n
  have herrorHalf (n : ℕ) : error n ≤ 1/2 := (herror n).trans (min_le_left _ _)
  have herrorLimit : Tendsto error atTop (𝓝 0) := by
    apply squeeze_zero (fun n => (w n).accuracy_pos.le)
      (fun n => (herror n).trans (min_le_right _ _))
    simpa only [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ)/((n : ℝ)+1)) atTop (𝓝 0))
  have hRadiusLimit : Tendsto radius atTop atTop := by
    apply tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    have hh := (le_max_right _ _).trans (hRadius n)
    linarith
  have hmLimit : Tendsto m atTop atTop := tendsto_atTop_mono (fun n => by change n ≤ m n; have := hm n; omega) tendsto_id
  have hSourceLip (n : ℕ) := hLip (w n) ((le_max_left _ _).trans (hRadius n))
    (herrorHalf n) (by have := hm n; omega) _ (T n) (hT n) (hTΘ n)
    Subset.rfl Subset.rfl (S n) (hS n) (hzero n) (hgram n) (hcurv n)
  obtain ⟨a, ha, rho, hrho, htime⟩ := isCompact_Icc.isSeqCompact
    (show ∀ n : ℕ, T n ∈ Icc 0 Θ from fun n => ⟨(hT n).le, hTΘ n⟩)
  have hSourceInitial (n : ℕ) (j : ℕ) (hj : j ≤ p)
      (y : standardCapWindow (radius n)) (hy : ‖y.val‖ ≤ r) :
      metricDerivNorm j ((S n).base.metric 0) (metric.restrictOpen (standardCapWindow (radius n)))
        (metric.restrictOpen (standardCapWindow (radius n))) y < error n := by
    rw [hzero]
    have hc := (w n).properties.window_close
    change metricDerivENormSupOn
      {z : standardCapWindow (radius n) | (riemannianEDistOf metric 0 z.val).toReal < radius n}
      (m n) (w n).windowMetric (metric.restrictOpen (standardCapWindow (radius n)))
        (metric.restrictOpen (standardCapWindow (radius n))) < ENNReal.ofReal (error n) at hc
    simp only [distance_zero] at hc
    exact metricDerivNorm_lt_of_sup_lt _ _ _ _ _ hc (by have := hm n; omega)
      (hy.trans_lt (hrR₁.trans_le ((le_max_left _ _).trans (hRadius n))))
  by_cases ha0 : a = 0
  · obtain ⟨Q⟩ := standard_solution_nonempty
    have hlim : Tendsto (fun i => (L+Lsum)*T (rho i)+error (rho i)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, ha0, mul_zero, zero_add] using
        ((htime.const_mul (L+Lsum)).add (herrorLimit.comp hrho.tendsto_atTop))
    obtain ⟨i, hi⟩ := (hlim.eventually (Iio_mem_nhds (by linarith : (0 : ℝ)<ε/2))).exists
    obtain ⟨t, ht, hbad⟩ := hbad (rho i) Q
      ((ENNReal.ofReal_le_ofReal (hTΘ (rho i))).trans_lt (hlife Q))
    have hb : metricDerivNormSupOn {y : standardCapWindow (radius (rho i)) | ‖y.val‖ ≤ r}
        p ((S (rho i)).base.metric t)
        ((Q.val.metric t).restrictOpen (standardCapWindow (radius (rho i))))
        (metric.restrictOpen (standardCapWindow (radius (rho i)))) ≤ ε/2 := by
      apply metricDerivNormSupOn_le_of_forall _ _ _ _ _ _ (by positivity)
      intro j hj y hy
      have h1 := hSourceLip (rho i) t ht 0 ⟨le_rfl,(hT (rho i)).le⟩ j hj y hy
      have h2 := hSourceInitial (rho i) j hj y hy
      have h3 := hStdLip Q 0 ⟨le_rfl,hΘ.le⟩ t ⟨ht.1,ht.2.trans (hTΘ (rho i))⟩ j hj y.val
      rw [Q.val.initial, zero_sub, abs_neg, abs_of_nonneg ht.1] at h3
      rw [sub_zero, abs_of_nonneg ht.1] at h1
      have h3' : metricDerivNorm j (metric.restrictOpen (standardCapWindow (radius (rho i))))
          ((Q.val.metric t).restrictOpen (standardCapWindow (radius (rho i))))
          (metric.restrictOpen (standardCapWindow (radius (rho i)))) y ≤ Lsum*t := by
        rw [metricDerivNorm_restrictOpen]
        exact h3
      have htri1 := metricDerivNorm_triangle j ((S (rho i)).base.metric t)
        ((S (rho i)).base.metric 0)
        ((Q.val.metric t).restrictOpen (standardCapWindow (radius (rho i))))
        (metric.restrictOpen (standardCapWindow (radius (rho i)))) y
      have htri2 := metricDerivNorm_triangle j ((S (rho i)).base.metric 0)
        (metric.restrictOpen (standardCapWindow (radius (rho i))))
        ((Q.val.metric t).restrictOpen (standardCapWindow (radius (rho i))))
        (metric.restrictOpen (standardCapWindow (radius (rho i)))) y
      have htimele := mul_le_mul_of_nonneg_left ht.2 (add_nonneg hL hLsum)
      linarith
    linarith
  · have haPos : 0 < a := lt_of_le_of_ne ha.1 (Ne.symm ha0)
    let gap := min (a/2) (ε/(16*(L+Lsum+1)))
    have hgap : 0 < gap := lt_min (by positivity) (by positivity)
    have hgapA : gap ≤ a/2 := min_le_left _ _
    have hgapε : gap ≤ ε/(16*(L+Lsum+1)) := min_le_right _ _
    let τ := a-gap
    have hτ : 0 < τ := by dsimp only [τ]; linarith
    have hτa : τ < a := by dsimp only [τ]; linarith
    have hτΘ : τ ≤ Θ := hτa.le.trans ha.2
    have hτ1 : τ < 1 := hτΘ.trans_lt hΘ1
    obtain ⟨R₀, _, _, m₀, ε₀, hε₀, hcompare⟩ :=
      exists_standard_cap_comparison_on_closed_interval_at_fixed_time
        (I := I) τ K r (ε/4) hτ hτ1 (by positivity) p
    have htimes : ∀ᶠ i in atTop, τ < T (rho i) ∧ T (rho i) < a+gap :=
      (htime.eventually (Ioi_mem_nhds hτa)).and (htime.eventually (Iio_mem_nhds (by linarith)))
    have hRs := (hRadiusLimit.comp hrho.tendsto_atTop).eventually_ge_atTop R₀
    have hms := (hmLimit.comp hrho.tendsto_atTop).eventually_ge_atTop m₀
    have hes := (herrorLimit.comp hrho.tendsto_atTop).eventually (Iio_mem_nhds hε₀)
    obtain ⟨i, hti, hRi, hmi, hei⟩ := (htimes.and (hRs.and (hms.and hes))).exists
    let F := (S (rho i)).timeRestrict (RealTimeInterval.closed 0 τ hτ.le)
    have hF : IsSolutionOn F := isSolutionOn_timeRestrict (hS (rho i))
      (Icc_subset_Icc le_rfl hti.1.le) (Ioo_subset_Ioo le_rfl hti.1.le)
    have hFgram (y : standardCapWindow (radius (rho i)))
        (j k : Fin (Module.finrank ℝ ThreeSpace)) :=
      (hgram (rho i) y j k).mono (prod_mono (Icc_subset_Icc le_rfl hti.1.le) Subset.rfl)
    have hFcurv : ∀ s ∈ Icc 0 τ, ∀ y : standardCapWindow (radius (rho i)),
        nablaKRm04NormSqIntrinsic F 0 s y ≤ K := by
      intro s hs y
      exact hcurv (rho i) s ⟨hs.1,hs.2.trans hti.1.le⟩ y
    obtain ⟨Q, _, hclose⟩ := hcompare (w (rho i)) hRi hmi hei.le F hF (hzero (rho i)) hFgram hFcurv
    obtain ⟨t, ht, hbad⟩ := hbad (rho i) Q
      ((ENNReal.ofReal_le_ofReal (hTΘ (rho i))).trans_lt (hlife Q))
    by_cases htτ : t ≤ τ
    · have hh := hclose t ⟨ht.1,htτ⟩
      change metricDerivNormSupOn _ _ ((S (rho i)).base.metric t) _ _ < ε/4 at hh
      linarith
    · have hτt : τ < t := lt_of_not_ge htτ
      have hdiff : 0 ≤ t-τ := sub_nonneg.mpr hτt.le
      have hdiffgap : t-τ ≤ 2*gap := by dsimp only [τ] at *; linarith [ht.2]
      have hprod : (L+Lsum)*(t-τ) < ε/4 := by
        have hden : 0 < 16*(L+Lsum+1) := by positivity
        have hh := (le_div_iff₀ hden).mp hgapε
        have hmul := mul_le_mul_of_nonneg_left hdiffgap (add_nonneg hL hLsum)
        nlinarith
      have hLcompact : IsCompact {y : standardCapWindow (radius (rho i)) | ‖y.val‖ ≤ r} := by
        have hc : IsCompact {y : ThreeSpace | ‖y‖ ≤ r} := by
          simpa only [Metric.closedBall,dist_zero_right] using isCompact_closedBall (0 : ThreeSpace) r
        exact _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hc (by
          intro y hy
          refine ⟨⟨y, ?_⟩, rfl⟩
          change ‖y‖ < radius (rho i)+1
          change ‖y‖ ≤ r at hy
          have hh := hrR₁.trans_le ((le_max_left _ _).trans (hRadius (rho i)))
          linarith)
      have hb : metricDerivNormSupOn {y : standardCapWindow (radius (rho i)) | ‖y.val‖ ≤ r}
          p ((S (rho i)).base.metric t)
          ((Q.val.metric t).restrictOpen (standardCapWindow (radius (rho i))))
          (metric.restrictOpen (standardCapWindow (radius (rho i)))) ≤ ε/2 := by
        apply metricDerivNormSupOn_le_of_forall _ _ _ _ _ _ (by positivity)
        intro j hj y hy
        have h1 := hSourceLip (rho i) t ht τ ⟨hτ.le, hti.1.le⟩ j hj y hy
        have h2 := (derivNorm_le_sup hLcompact hj _ _ _ hy).trans_lt (hclose τ ⟨hτ.le,le_rfl⟩)
        have h3 := hStdLip Q τ ⟨hτ.le,hτΘ⟩ t ⟨ht.1,ht.2.trans (hTΘ (rho i))⟩ j hj y.val
        rw [abs_of_nonneg hdiff] at h1
        rw [abs_sub_comm τ t, abs_of_nonneg hdiff] at h3
        have h3' : metricDerivNorm j
            ((Q.val.metric τ).restrictOpen (standardCapWindow (radius (rho i))))
            ((Q.val.metric t).restrictOpen (standardCapWindow (radius (rho i))))
            (metric.restrictOpen (standardCapWindow (radius (rho i)))) y ≤ Lsum*(t-τ) := by
          rw [metricDerivNorm_restrictOpen]
          exact h3
        change metricDerivNorm j ((S (rho i)).base.metric τ) _ _ y < ε/4 at h2
        have htri1 := metricDerivNorm_triangle j ((S (rho i)).base.metric t)
          ((S (rho i)).base.metric τ)
          ((Q.val.metric t).restrictOpen (standardCapWindow (radius (rho i))))
          (metric.restrictOpen (standardCapWindow (radius (rho i)))) y
        have htri2 := metricDerivNorm_triangle j ((S (rho i)).base.metric τ)
          ((Q.val.metric τ).restrictOpen (standardCapWindow (radius (rho i))))
          ((Q.val.metric t).restrictOpen (standardCapWindow (radius (rho i))))
          (metric.restrictOpen (standardCapWindow (radius (rho i)))) y
        linarith
      linarith

theorem exists_uniform_standard_cap_comparison_on_closed_interval_of_curvature_bound
    (T K r ε : ℝ) (hT : 0 < T) (hT1 : T < 1) (hε : 0 < ε) (p : ℕ) :
    ∃ R : ℝ, 0 < R ∧ r < R ∧ ∃ m₀ : ℕ, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
        [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A}
        {D : ℝ} {m : ℕ} {ζ : ℝ}
        (w : CanonicalStaticInsertionWitness d A hA D m ζ),
      R ≤ D → m₀ ≤ m → ζ ≤ ε₀ →
      ∀ S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
          (RealTimeInterval.closed 0 T hT.le),
        IsSolutionOn S → S.base.metric 0 = w.windowMetric →
        (∀ (y : standardCapWindow D) (i j : Fin (Module.finrank ℝ ThreeSpace)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
            (fun z : ℝ × standardCapWindow D =>
              DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric z.1) y z.2 i j)
            (Icc 0 T ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) y).baseSet)) →
        (∀ t ∈ Icc 0 T, ∀ y : standardCapWindow D,
          nablaKRm04NormSqIntrinsic S 0 t y ≤ K) →
        ∃ Q : StandardSolution, ENNReal.ofReal T < Q.val.lifetime ∧
          ∀ t ∈ Icc 0 T,
            metricDerivNormSupOn {y : standardCapWindow D | ‖y.val‖ ≤ r} p
              (S.base.metric t) ((Q.val.metric t).restrictOpen (standardCapWindow D))
              (metric.restrictOpen (standardCapWindow D)) < ε := by
  obtain ⟨R, hR, hrR, m₀, ε₀, hε₀, hcompare⟩ :=
    exists_uniform_standard_cap_comparison_on_bounded_intervals_of_curvature_bound
      (I := I) T K r ε hT hT1 hε p
  refine ⟨R, hR, hrR, m₀, ε₀, hε₀, ?_⟩
  intro M _ _ _ _ g x₀ δ k d A hA D m ζ w hRD hm hζ S hS hzero hgram hcurv
  exact hcompare w hRD hm hζ T hT le_rfl S hS hzero hgram hcurv

end DifferentialGeometry.PDE.RicciFlow.StandardCap
