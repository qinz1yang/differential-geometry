import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.InitialMetricLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.LocalWindowCurvatureHorizon
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.LocalPullback

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold TopologicalSpace
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
universe u
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance (V : Opens ThreeSpace) : SigmaCompactSpace V :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel V.isOpen)

theorem exists_curvature_derivative_bounds_on_compatible_window_flows
    (P : ℕ → ℕ → Type u) [∀ n i, TopologicalSpace (P n i)] [∀ n i, ChartedSpace H (P n i)]
    [∀ n i, IsManifold I ∞ (P n i)] [∀ n i, T2Space (P n i)]
    (g : ∀ n i, SmoothRiemannianMetric I (P n i)) (x : ∀ n i, P n i)
    (delta : ℕ → ℕ → ℝ) (order m : ℕ → ℕ → ℕ)
    (datum : ∀ n i, normalizedDatum (g n i) (x n i) (delta n i) (order n i))
    (A error : ℕ → ℕ → ℝ) (hA : ∀ n i, 0 < A n i)
    (radius : ℕ → ℝ) (hradius : Tendsto radius atTop atTop)
    (w : ∀ n i, CanonicalStaticInsertionWitness (datum n i) (A n i) (hA n i)
      (radius n) (m n i) (error n i))
    (hm : ∀ n, Tendsto (m n) atTop atTop)
    (herror : ∀ n, ∀ᶠ i in atTop, error n i ≤ 1 / 2)
    {D : RealTimeInterval}
    (S : ∀ n, ℕ → SolutionOn (I := ThreeModel) (M := standardCapWindow (radius n)) D)
    (hS : ∀ n i, IsSolutionOn (S n i))
    {T : ℝ} (hT : 0 < T) (hslab : Icc 0 T ⊆ D.carrier) (hreg : Ioo 0 T ⊆ D.regular)
    (hzero : ∀ n i, (S n i).base.metric 0 = (w n i).windowMetric)
    (hgram : ∀ n k (p : standardCapWindow (radius n)) (i j : Fin (Module.finrank ℝ ThreeSpace)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
        (fun z : ℝ × standardCapWindow (radius n) =>
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix ((S n k).base.metric z.1) p z.2 i j)
        (Icc 0 T ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet))
    (N : ℕ → ℕ)
    (hcompat : ∀ n l, ∀ᶠ i in atTop, ∀ t ∈ Icc 0 T,
      ((S n (i - N n)).base.metric t).restrictOpenOfSubset
        (inf_le_left : standardCapWindow (radius n) ⊓ standardCapWindow (radius l) ≤ _) =
      ((S l (i - N l)).base.metric t).restrictOpenOfSubset
        (inf_le_right : standardCapWindow (radius n) ⊓ standardCapWindow (radius l) ≤ _))
    (K : ℕ → ℝ)
    (hcurv : ∀ n, ∀ᶠ i in atTop, ∀ t ∈ Icc 0 T, ∀ y : standardCapWindow (radius n),
      nablaKRm04NormSqIntrinsic (S n i) 0 t y ≤ K n) :
    ∀ n q, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ i in atTop,
      ∀ t ∈ Icc 0 T, ∀ y : standardCapWindow (radius n),
        curvDerivNorm q ((S n i).base.metric t) y ≤ B := by
  intro n q
  let r := max 1 (radius n + 1)
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨l, hl⟩ := (hradius.eventually_gt_atTop (32 * r)).exists
  have hsub : standardCapWindow (radius n) ≤ standardCapWindow (radius l) := by
    intro y hy
    change ‖y‖ < radius l + 1
    change ‖y‖ < radius n + 1 at hy
    have hnr : radius n + 1 ≤ r := le_max_right _ _
    linarith
  obtain ⟨B, hB, hjet⟩ :=
    exists_uniform_window_flow_curvature_derivative_bound_of_local_curvature_bounded_horizon
      q (32 * r) T (K l) (by positivity)
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp
    (((hm l).eventually_ge_atTop (q + 2)).and ((herror l).and (hcurv l)))
  obtain ⟨j₁, hj₁⟩ := eventually_atTop.mp (hcompat n l)
  refine ⟨Real.sqrt B, Real.sqrt_nonneg _, ?_⟩
  filter_upwards [eventually_ge_atTop (j₀ + j₁ + N l)] with i hi
  intro t ht y
  let k := i + N n - N l
  have hk : j₀ ≤ k := by dsimp only [k]; omega
  have heq := hj₁ (i + N n) (by omega) t ht
  rw [Nat.add_sub_cancel] at heq
  let y' : (standardCapWindow (radius n) ⊓ standardCapWindow (radius l) : Opens ThreeSpace) :=
    ⟨y.val, y.property, hsub y.property⟩
  have hnorm : curvDerivNorm q ((S n i).base.metric t) y =
      curvDerivNorm q ((S l k).base.metric t) (Opens.inclusion hsub y) := by
    have hh := congrArg (fun G => curvDerivNorm q G y') heq
    rw [curvDerivNorm_restrictOpenOfSubset,
      curvDerivNorm_restrictOpenOfSubset] at hh
    exact hh
  rw [hnorm]
  have hh := hjet (w l k) (hj₀ k hk).2.1 (hj₀ k hk).1 hl D T hT le_rfl hslab hreg
    (S l k) (hS l k) (hzero l k) (hgram l k)
    (fun t ht y _ => (hj₀ k hk).2.2 t ht y)
    q le_rfl t ht (Opens.inclusion hsub y) (by
      change ‖y.val‖ ≤ (32 * r) / 32
      have hy := y.property
      change ‖y.val‖ < radius n + 1 at hy
      have hnr := le_max_right 1 (radius n + 1)
      dsimp only [r]
      nlinarith)
  rw [← curvNormSq_eq] at hh
  exact Real.sqrt_le_sqrt hh

theorem exists_standard_solution_limit_of_compatible_insertion_window_flows
    (P : ℕ → ℕ → Type u) [∀ n i, TopologicalSpace (P n i)] [∀ n i, ChartedSpace H (P n i)]
    [∀ n i, IsManifold I ∞ (P n i)] [∀ n i, T2Space (P n i)]
    (g : ∀ n i, SmoothRiemannianMetric I (P n i)) (x : ∀ n i, P n i)
    (delta : ℕ → ℕ → ℝ) (order m : ℕ → ℕ → ℕ)
    (datum : ∀ n i, normalizedDatum (g n i) (x n i) (delta n i) (order n i))
    (A error : ℕ → ℕ → ℝ) (hA : ∀ n i, 0 < A n i)
    (radius : ℕ → ℝ) (hradius : Tendsto radius atTop atTop)
    (w : ∀ n i, CanonicalStaticInsertionWitness (datum n i) (A n i) (hA n i)
      (radius n) (m n i) (error n i))
    (hm : ∀ n, Tendsto (m n) atTop atTop)
    (herror : ∀ n, Tendsto (error n) atTop (𝓝 0))
    {D : RealTimeInterval}
    (S : ∀ n, ℕ → SolutionOn (I := ThreeModel) (M := standardCapWindow (radius n)) D)
    (hS : ∀ n i, IsSolutionOn (S n i))
    {T : ℝ} (hT : 0 < T) (hslab : Icc 0 T ⊆ D.carrier) (hreg : Ioo 0 T ⊆ D.regular)
    (hzero : ∀ n i, (S n i).base.metric 0 = (w n i).windowMetric)
    (hgram : ∀ n k (p : standardCapWindow (radius n)) (i j : Fin (Module.finrank ℝ ThreeSpace)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
        (fun z : ℝ × standardCapWindow (radius n) =>
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix ((S n k).base.metric z.1) p z.2 i j)
        (Icc 0 T ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet))
    (N : ℕ → ℕ)
    (hcompat : ∀ n l, ∀ᶠ i in atTop, ∀ t ∈ Icc 0 T,
      ((S n (i - N n)).base.metric t).restrictOpenOfSubset
        (inf_le_left : standardCapWindow (radius n) ⊓ standardCapWindow (radius l) ≤ _) =
      ((S l (i - N l)).base.metric t).restrictOpenOfSubset
        (inf_le_right : standardCapWindow (radius n) ⊓ standardCapWindow (radius l) ≤ _))
    {K : ℝ}
    (hcurv : ∀ n, ∀ᶠ i in atTop, ∀ t ∈ Icc 0 T, ∀ y : standardCapWindow (radius n),
      nablaKRm04NormSqIntrinsic (S n i) 0 t y ≤ K) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∃ Q : StandardSolution,
      ENNReal.ofReal T ≤ Q.val.lifetime ∧
      ∀ n, ∀ L : Set (standardCapWindow (radius n)), IsCompact L → ∀ p : ℕ, ∀ e : ℝ, 0 < e →
        ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Ico 0 T,
          metricDerivNormSupOn L p ((S n (rho i - N n)).base.metric t)
            ((Q.val.metric t).restrictOpen (standardCapWindow (radius n)))
            (metric.restrictOpen (standardCapWindow (radius n))) < e := by
  have hcover : ∀ y : ThreeSpace, ∃ n, y ∈ standardCapWindow (radius n) := by
    intro y
    obtain ⟨n, hn⟩ := (hradius.eventually_gt_atTop ‖y‖).exists
    exact ⟨n, by change ‖y‖ < radius n + 1; linarith⟩
  have hcompat₀ : ∀ n l, ∀ᶠ i in atTop,
      ((w n (i - N n)).windowMetric).restrictOpenOfSubset
        (inf_le_left : standardCapWindow (radius n) ⊓ standardCapWindow (radius l) ≤ _) =
      ((w l (i - N l)).windowMetric).restrictOpenOfSubset
        (inf_le_right : standardCapWindow (radius n) ⊓ standardCapWindow (radius l) ≤ _) := by
    intro n l
    filter_upwards [hcompat n l] with i hi
    simpa only [hzero] using hi 0 ⟨le_rfl, hT.le⟩
  have hinitial := metricCInfConvergenceOnCompacts_of_compatible_insertion_windows
    P g x delta order m datum A error hA radius hradius w hm herror N hcompat₀
  have hjets := exists_curvature_derivative_bounds_on_compatible_window_flows
    P g x delta order m datum A error hA radius hradius w hm
    (fun n => ((herror n).eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono
      (fun _ h => h.le)) S hS hT hslab hreg hzero hgram N hcompat (fun _ => K) hcurv
  apply exists_standard_solution_limit_of_initial_convergence_on_open_cover (C := Real.sqrt K)
    (fun n => standardCapWindow (radius n)) hcover S hS hT hslab hreg hgram
  · intro n
    simpa only [hzero] using hinitial n
  · intro n L _ q
    obtain ⟨B, hB, hbound⟩ := hjets n q
    exact ⟨B, hB, hbound.mono fun i hi t ht y _ => hi t ht y⟩
  · intro n l t ht
    exact (hcompat n l).mono fun i hi => hi t ht
  · intro n y
    exact (hcurv n).mono fun i hi t ht => by
      have hh := hi t ht y
      rw [← curvNormSq_eq] at hh
      exact Real.sqrt_le_sqrt hh

end DifferentialGeometry.PDE.RicciFlow.StandardCap
