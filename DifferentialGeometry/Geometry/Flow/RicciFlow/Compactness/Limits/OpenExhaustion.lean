import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Solution.CountableInitialConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Solution.CountableTerminalConvergence
import DifferentialGeometry.Geometry.Metric.Convergence.Restriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.OpenCover

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]

theorem exists_common_compatible_solution_subsequence_on_open_sets_of_terminal_convergence
    (U : ℕ → TopologicalSpace.Opens M) {D : RealTimeInterval}
    (S : ∀ n : ℕ, ℕ → SolutionOn (I := I) (M := U n) D)
    (hS : ∀ n i, IsSolutionOn (S n i))
    (R : ∀ n : ℕ, SmoothRiemannianMetric I (U n))
    {a b : ℝ} (hab : a < b)
    (hslab : Icc a b ⊆ D.carrier) (hreg : Ico a b ⊆ D.regular)
    (hterminal : ∀ n, MetricCInfConvergenceOnCompacts
      (fun i => (S n i).base.metric b) (R n) (R n))
    (hcurv : ∀ n, ∀ K : Set (U n), IsCompact K → ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in atTop,
        ∀ t ∈ Icc a b, ∀ x ∈ K, curvDerivNorm q ((S n i).base.metric t) x ≤ C)
    (N : ℕ → ℕ)
    (hcompat : ∀ n m t, t ∈ Icc a b →
      (fun i => ((S n (i - N n)).base.metric t).restrictOpenOfSubset
        (inf_le_left : U n ⊓ U m ≤ U n)) =ᶠ[atTop]
      (fun i => ((S m (i - N m)).base.metric t).restrictOpenOfSubset
        (inf_le_right : U n ⊓ U m ≤ U m))) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧
      ∃ g : ∀ n, ℝ → SmoothRiemannianMetric I (U n),
        (∀ n, g n b = R n) ∧
        (∀ n, IsSolutionOn ({ base.metric := g n } : SolutionOn (I := I) (M := U n)
          (RealTimeInterval.closed a b hab.le))) ∧
        (∀ n, ∀ K : Set (U n), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
          ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc a b,
            metricDerivNormSupOn K p ((S n (rho i - N n)).base.metric t)
              (g n t) (R n) < η) ∧
        ∀ n m t, t ∈ Icc a b →
          (g n t).restrictOpenOfSubset (inf_le_left : U n ⊓ U m ≤ U n) =
            (g m t).restrictOpenOfSubset (inf_le_right : U n ⊓ U m ≤ U m) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ (n : ℕ) : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
  obtain ⟨rho, hrho, hG⟩ :=
    exists_common_solution_subsequence_on_open_sets_of_terminal_convergence
      U (fun _ => D) S hS R (fun _ => a) (fun _ => b)
      (fun _ => hab) (fun _ => hslab) (fun _ => hreg) hterminal hcurv N
  choose g hg hflow hconv using hG
  refine ⟨rho, hrho, g, hg, hflow, hconv, ?_⟩
  intro n m t ht
  have hn : MetricCInfConvergenceOnCompacts
      (fun i => (S n (rho i - N n)).base.metric t) (g n t) (R n) := by
    intro K hK p η hη
    obtain ⟨j, hj⟩ := hconv n K hK p η hη
    exact ⟨j, fun i hi => hj i hi t ht⟩
  have hm : MetricCInfConvergenceOnCompacts
      (fun i => (S m (rho i - N m)).base.metric t) (g m t) (R m) := by
    intro K hK p η hη
    obtain ⟨j, hj⟩ := hconv m K hK p η hη
    exact ⟨j, fun i hi => hj i hi t ht⟩
  exact metricCInf_unique_restrictOpenOfSubset_of_eventuallyEq inf_le_left inf_le_right hn hm
    (hrho.tendsto_atTop.eventually (hcompat n m t ht))

theorem exists_global_solution_subsequence_of_terminal_convergence_on_open_cover
    (U : ℕ → TopologicalSpace.Opens M) (hcover : ∀ x : M, ∃ n, x ∈ U n)
    {D : RealTimeInterval} (S : ∀ n : ℕ, ℕ → SolutionOn (I := I) (M := U n) D)
    (hS : ∀ n i, IsSolutionOn (S n i)) (R : SmoothRiemannianMetric I M)
    {a b : ℝ} (hab : a < b)
    (hslab : Icc a b ⊆ D.carrier) (hreg : Ico a b ⊆ D.regular)
    (hterminal : ∀ n, MetricCInfConvergenceOnCompacts
      (fun i => (S n i).base.metric b) (R.restrictOpen (U n)) (R.restrictOpen (U n)))
    (hcurv : ∀ n, ∀ K : Set (U n), IsCompact K → ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in atTop,
        ∀ t ∈ Icc a b, ∀ x ∈ K, curvDerivNorm q ((S n i).base.metric t) x ≤ C)
    (N : ℕ → ℕ)
    (hcompat : ∀ n m t, t ∈ Icc a b →
      (fun i => ((S n (i - N n)).base.metric t).restrictOpenOfSubset
        (inf_le_left : U n ⊓ U m ≤ U n)) =ᶠ[atTop]
      (fun i => ((S m (i - N m)).base.metric t).restrictOpenOfSubset
        (inf_le_right : U n ⊓ U m ≤ U m))) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧
      ∃ G : ℝ → SmoothRiemannianMetric I M,
        G b = R ∧
        IsSolutionOn ({ base.metric := G } : SolutionOn (I := I) (M := M)
          (RealTimeInterval.closed a b hab.le)) ∧
        ∀ n, ∀ K : Set (U n), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
          ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc a b,
            metricDerivNormSupOn K p ((S n (rho i - N n)).base.metric t)
              ((G t).restrictOpen (U n)) (R.restrictOpen (U n)) < η := by
  obtain ⟨rho, hrho, g, hgb, hgsol, hconv, hoverlap⟩ :=
    exists_common_compatible_solution_subsequence_on_open_sets_of_terminal_convergence
      U S hS (fun n => R.restrictOpen (U n)) hab hslab hreg hterminal hcurv N hcompat
  obtain ⟨G, hGsol, hG⟩ := exists_solution_of_compatible_open_cover U hcover g hgsol hoverlap
  have hGb : G b = R := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    obtain ⟨n, hxn⟩ := hcover x
    have heq := (hG n b ⟨hab.le, le_rfl⟩).trans (hgb n)
    exact congrArg (fun h : SmoothRiemannianMetric I (U n) => h.inner ⟨x, hxn⟩ v w) heq
  refine ⟨rho, hrho, G, hGb, hGsol, ?_⟩
  intro n K hK p η hη
  obtain ⟨j, hj⟩ := hconv n K hK p η hη
  refine ⟨j, fun i hi t ht => ?_⟩
  rw [hG n t ht]
  exact hj i hi t ht

omit [NeZero (Module.finrank ℝ E)]

theorem exists_common_compatible_solution_subsequence_on_open_sets_of_initial_convergence
    (U : ℕ → TopologicalSpace.Opens M) {D : RealTimeInterval}
    (S : ∀ n : ℕ, ℕ → SolutionOn (I := I) (M := U n) D)
    (hS : ∀ n i, IsSolutionOn (S n i))
    (R : ∀ n : ℕ, SmoothRiemannianMetric I (U n))
    {a b : ℝ} (hab : a < b)
    (hslab : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular)
    (hgram : ∀ n k (x : U n) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × U n => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          ((S n k).base.metric p.1) x p.2 i j)
        (Icc a b ×ˢ (trivializationAt E (TangentSpace I) x).baseSet))
    (hinitial : ∀ n, MetricCInfConvergenceOnCompacts
      (fun i => (S n i).base.metric a) (R n) (R n))
    (hcurv : ∀ n, ∀ K : Set (U n), IsCompact K → ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in atTop,
        ∀ t ∈ Icc a b, ∀ x ∈ K, curvDerivNorm q ((S n i).base.metric t) x ≤ C)
    (N : ℕ → ℕ)
    (hcompat : ∀ n m t, t ∈ Icc a b →
      (fun i => ((S n (i - N n)).base.metric t).restrictOpenOfSubset
        (inf_le_left : U n ⊓ U m ≤ U n)) =ᶠ[atTop]
      (fun i => ((S m (i - N m)).base.metric t).restrictOpenOfSubset
        (inf_le_right : U n ⊓ U m ≤ U m))) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧
      ∃ g : ∀ n, ℝ → SmoothRiemannianMetric I (U n),
        (∀ n, g n a = R n) ∧
        (∀ n, IsSolutionOn ({ base.metric := g n } : SolutionOn (I := I) (M := U n)
          (RealTimeInterval.closed a b hab.le))) ∧
        (∀ n (x : U n) (i j : Fin (Module.finrank ℝ E)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
            (fun p : ℝ × U n => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
              (g n p.1) x p.2 i j)
            (Icc a b ×ˢ (trivializationAt E (TangentSpace I) x).baseSet)) ∧
        (∀ n, ∀ K : Set (U n), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
          ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc a b,
            metricDerivNormSupOn K p ((S n (rho i - N n)).base.metric t)
              (g n t) (R n) < η) ∧
        ∀ n m t, t ∈ Icc a b →
          (g n t).restrictOpenOfSubset (inf_le_left : U n ⊓ U m ≤ U n) =
            (g m t).restrictOpenOfSubset (inf_le_right : U n ⊓ U m ≤ U m) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ (n : ℕ) : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
  obtain ⟨rho, hrho, hG⟩ :=
    exists_common_solution_subsequence_on_open_sets_of_initial_convergence
      U (fun _ => D) S hS R (fun _ => a) (fun _ => b)
      (fun _ => hab) (fun _ => hslab) (fun _ => hreg) hgram hinitial hcurv N
  choose g hg hflow hggram hconv using hG
  refine ⟨rho, hrho, g, hg, hflow, hggram, hconv, ?_⟩
  intro n m t ht
  have hn : MetricCInfConvergenceOnCompacts
      (fun i => (S n (rho i - N n)).base.metric t) (g n t) (R n) := by
    intro K hK p η hη
    obtain ⟨j, hj⟩ := hconv n K hK p η hη
    exact ⟨j, fun i hi => hj i hi t ht⟩
  have hm : MetricCInfConvergenceOnCompacts
      (fun i => (S m (rho i - N m)).base.metric t) (g m t) (R m) := by
    intro K hK p η hη
    obtain ⟨j, hj⟩ := hconv m K hK p η hη
    exact ⟨j, fun i hi => hj i hi t ht⟩
  exact metricCInf_unique_restrictOpenOfSubset_of_eventuallyEq inf_le_left inf_le_right hn hm
    (hrho.tendsto_atTop.eventually (hcompat n m t ht))

theorem exists_global_solution_subsequence_of_initial_convergence_on_open_cover
    (U : ℕ → TopologicalSpace.Opens M) (hcover : ∀ x : M, ∃ n, x ∈ U n)
    {D : RealTimeInterval} (S : ∀ n : ℕ, ℕ → SolutionOn (I := I) (M := U n) D)
    (hS : ∀ n i, IsSolutionOn (S n i)) (R : SmoothRiemannianMetric I M)
    {a b : ℝ} (hab : a < b)
    (hslab : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular)
    (hgram : ∀ n k (x : U n) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × U n => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          ((S n k).base.metric p.1) x p.2 i j)
        (Icc a b ×ˢ (trivializationAt E (TangentSpace I) x).baseSet))
    (hinitial : ∀ n, MetricCInfConvergenceOnCompacts
      (fun i => (S n i).base.metric a) (R.restrictOpen (U n)) (R.restrictOpen (U n)))
    (hcurv : ∀ n, ∀ K : Set (U n), IsCompact K → ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in atTop,
        ∀ t ∈ Icc a b, ∀ x ∈ K, curvDerivNorm q ((S n i).base.metric t) x ≤ C)
    (N : ℕ → ℕ)
    (hcompat : ∀ n m t, t ∈ Icc a b →
      (fun i => ((S n (i - N n)).base.metric t).restrictOpenOfSubset
        (inf_le_left : U n ⊓ U m ≤ U n)) =ᶠ[atTop]
      (fun i => ((S m (i - N m)).base.metric t).restrictOpenOfSubset
        (inf_le_right : U n ⊓ U m ≤ U m))) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧
      ∃ G : ℝ → SmoothRiemannianMetric I M,
        G a = R ∧
        IsSolutionOn ({ base.metric := G } : SolutionOn (I := I) (M := M)
          (RealTimeInterval.closed a b hab.le)) ∧
        (∀ (x : M) (i j : Fin (Module.finrank ℝ E)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
            (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
              (G p.1) x p.2 i j)
            (Icc a b ×ˢ (trivializationAt E (TangentSpace I) x).baseSet)) ∧
        ∀ n, ∀ K : Set (U n), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
          ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc a b,
            metricDerivNormSupOn K p ((S n (rho i - N n)).base.metric t)
              ((G t).restrictOpen (U n)) (R.restrictOpen (U n)) < η := by
  obtain ⟨rho, hrho, g, hga, hgsol, hggram, hconv, hoverlap⟩ :=
    exists_common_compatible_solution_subsequence_on_open_sets_of_initial_convergence
      U S hS (fun n => R.restrictOpen (U n)) hab hslab hreg hgram hinitial hcurv N hcompat
  obtain ⟨G, hGsol, hG⟩ := exists_solution_of_compatible_open_cover U hcover g hgsol hoverlap
  have hGa : G a = R := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    obtain ⟨n, hxn⟩ := hcover x
    have heq := (hG n a ⟨le_rfl, hab.le⟩).trans (hga n)
    exact congrArg (fun h : SmoothRiemannianMetric I (U n) => h.inner ⟨x, hxn⟩ v w) heq
  have hGgram := chartGramMatrix_joint_contMDiffOn_of_restrict_open_cover G (Icc a b)
    U hcover (fun n x i j => (hggram n x i j).congr (fun p hp => by rw [hG n p.1 hp.1]))
  refine ⟨rho, hrho, G, hGa, hGsol, hGgram, ?_⟩
  intro n K hK p η hη
  obtain ⟨j, hj⟩ := hconv n K hK p η hη
  refine ⟨j, fun i hi t ht => ?_⟩
  rw [hG n t ht]
  exact hj i hi t ht

end DifferentialGeometry.PDE.RicciFlow
