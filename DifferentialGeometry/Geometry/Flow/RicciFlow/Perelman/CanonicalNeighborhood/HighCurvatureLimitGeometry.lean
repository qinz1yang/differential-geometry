import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureSequenceEstimates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PointedPinchingLimit
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.OpenPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M]

theorem highCurvatureFlowSequence_pullback_limit_curvature
    {T theta : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    (hmax : ∀ i s, s ∈ Icc 0 (t i) → ∀ y : M,
      S.scalar s y ≤ S.scalar (t i) (x i))
    (htheta : 0 < theta) (htlower : ∀ᶠ i in atTop, theta ≤ t i)
    (hscalar : Tendsto (fun i => S.scalar (t i) (x i)) atTop atTop)
    (P : MetricCompactLimit
      ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).atTime 0))
    (U : TopologicalSpace.Opens P.limit.M) (hpU : P.limit.basepoint ∈ U)
    (N : ℕ) (rho : ℕ → ℕ) (hrho : StrictMono rho)
    (s : ℝ) (hs : s ≤ 0)
    (G : ℕ → SmoothRiemannianMetric I3 U) (g r : SmoothRiemannianMetric I3 U)
    (hsource : ∀ j, (U : Set P.limit.M) ⊆
      (P.maps.partialDiffeomorph (j + N)).source)
    (hmetric : ∀ j (y : U) (v w : TangentSpace I3 y),
      (G j).inner y v w =
        (((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term
          (P.subseq (j + N))).S.base.metric s).inner
          (P.maps.partialDiffeomorph (j + N) y)
          (mfderiv I3 I3 (P.maps.partialDiffeomorph (j + N)) y v)
          (mfderiv I3 I3 (P.maps.partialDiffeomorph (j + N)) y w))
    (hconv : MetricCInfConvergenceOnCompacts (fun i => G (rho i - N)) g r) :
    (∀ (y : U) (v w : TangentSpace I3 y), 0 ≤ metricRm04StandardAt g y v w w v) ∧
      ∀ y : U, metricScalarAt g y ∈ Icc (0 : ℝ) 1 := by
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let X := highCurvatureFlowSequence hT S hS x t htmem htpos hpos
  let f : ℕ → ℕ := fun i => P.subseq (rho i - N + N)
  let F (i : ℕ) := P.maps.partialDiffeomorph (rho i - N + N)
  obtain ⟨Psi, _hPsi, C, hcanonical⟩ :=
    exists_pointed_metric_convergence_of_pullback_on_open
      (X.atTime s) P.limit f F U hpU
      (fun i => hsource (rho i - N)) (fun i => P.maps.basepoint_map (rho i - N + N))
      (fun i => G (rho i - N)) g r (fun i => hmetric (rho i - N)) hconv
  have hf : Tendsto f atTop atTop := by
    have heq : f =ᶠ[atTop] fun i => P.subseq (rho i) := by
      filter_upwards [eventually_ge_atTop N] with i hi
      dsimp only [f]
      rw [Nat.sub_add_cancel (hi.trans (hrho.id_le i))]
    exact (P.strictMono.tendsto_atTop.comp hrho.tendsto_atTop).congr' heq.symm
  have htime : ∀ᶠ i in atTop, s ∈ (X.interval (f i)).carrier := by
    have hw := high_curvature_interval_eventually_contains_closed_window
      hT S x t htpos hpos htheta htlower hscalar (-s)
    filter_upwards [hf.eventually hw] with i hi
    exact hi.1 ⟨by simp, hs⟩
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  obtain ⟨Phi, hPhi, hpinching⟩ :=
    exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen hT S hS hdim
  have hpin : ∀ᶠ i in atTop, ∀ y : (X.term (f i)).M,
      curvatureOperatorLowerBoundAt ((X.term (f i)).S.base.metric s) y
        (metricAlgebraicCurvatureTensorAt ((X.term (f i)).S.base.metric s) y)
        (rescalePinchingFunction (S.scalar (t (f i)) (x (f i))) Phi
          (metricScalarAt ((X.term (f i)).S.base.metric s) y)) := by
    filter_upwards [htime] with i hi
    intro y
    exact phiAlmostNonnegative_paraSolution S (hpos (f i)) (htmem (f i)) hpinching s
      (highCurvatureInterval_carrier_subset hT S x t htpos hpos htmem (f i) hi) y
  have hsec := sectional_nonnegative_of_pointed_admissible_pinching_eventually
    C hcanonical hPhi (fun i => S.scalar (t i) (x i)) hpos (hscalar.comp hf) hpin
  refine ⟨hsec, fun y => ⟨?_, ?_⟩⟩
  · classical
    obtain ⟨b, hb⟩ := Tensor0SBundle.exists_orthonormal_basis g y
    rw [KappaSolutions.metricScalarAt_eq_sum_sum_rm04_of_orthonormal g b hb]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hsec y (b j) (b i)
  · apply le_of_tendsto (KappaSolutions.pointedScalar_tendsto_of_metricCG_canonical_domains
      C hcanonical y)
    filter_upwards [htime] with i hi
    exact highCurvatureFlowSequence_scalar_le_one_of_pastMaximum
      hT S hS x t htmem htpos hpos hmax (f i) s hi (Psi.map i y)

theorem highCurvatureFlowSequence_ancient_limit_geometry
    {T theta : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    (hmax : ∀ i s, s ∈ Icc 0 (t i) → ∀ y : M,
      S.scalar s y ≤ S.scalar (t i) (x i))
    (htheta : 0 < theta) (htlower : ∀ᶠ i in atTop, theta ≤ t i)
    (hscalar : Tendsto (fun i => S.scalar (t i) (x i)) atTop atTop)
    (P : MetricCompactLimit
      ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).atTime 0))
    (N : ℕ → ℕ)
    (F : ∀ n, ℕ → ℝ → SmoothRiemannianMetric I3 (metricSourceOpenSubset P.maps n))
    (hsource : ∀ n i, (metricSourceOpenSubset P.maps n : Set P.limit.M) ⊆
      (P.maps.partialDiffeomorph (i + N n)).source)
    (hmetric : ∀ n i s (y : metricSourceOpenSubset P.maps n) (v w : TangentSpace I3 y),
      (F n i s).inner y v w =
        (((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term
          (P.subseq (i + N n))).S.base.metric s).inner
          (P.maps.partialDiffeomorph (i + N n) y)
          (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N n)) y v)
          (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N n)) y w))
    (rho : ℕ → ℕ) (hrho : StrictMono rho)
    (G : ℝ → SmoothRiemannianMetric I3 P.limit.M)
    (hG0 : G 0 = P.limit.metric)
    (hGsol : IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := P.limit.M)
      (RealTimeInterval.infiniteClosed 0 0 le_rfl)))
    (hconv : ∀ n, ∀ K : Set (metricSourceOpenSubset P.maps n), IsCompact K →
      ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon → ∃ j : ℕ, ∀ i ≥ j,
        ∀ s ∈ Icc (-((n + 1 : ℕ) : ℝ)) 0,
          metricDerivNormSupOn K p (F n (rho i - N n) s)
            ((G s).restrictOpen (metricSourceOpenSubset P.maps n))
            (P.limit.metric.restrictOpen (metricSourceOpenSubset P.maps n)) < epsilon) :
    ∀ s ≤ 0,
      (∀ (y : P.limit.M) (v w : TangentSpace I3 y),
        0 ≤ metricRm04StandardAt (G s) y v w w v) ∧
      (∀ y : P.limit.M, metricScalarAt (G s) y ∈ Icc (0 : ℝ) 1) ∧
      RiemannianMetricComplete (G s) := by
  let U := metricSourceOpenSubset P.maps
  have hcurv : ∀ s ≤ 0, ∀ y : P.limit.M,
      (∀ v w : TangentSpace I3 y, 0 ≤ metricRm04StandardAt (G s) y v w w v) ∧
        metricScalarAt (G s) y ∈ Icc (0 : ℝ) 1 := by
    intro s hs y
    obtain ⟨ny, hny⟩ := P.maps.source_exhausts.subset {y} isCompact_singleton
    obtain ⟨nt, hnt⟩ := exists_nat_ge (-s)
    let n := max ny nt
    have hyn : y ∈ U n := hny n (le_max_left _ _) (mem_singleton y)
    have hsn : s ∈ Icc (-((n + 1 : ℕ) : ℝ)) 0 := by
      have hntn : (nt : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr (le_max_right _ _)
      rw [Nat.cast_add, Nat.cast_one]
      exact ⟨by linarith, hs⟩
    have hc := highCurvatureFlowSequence_pullback_limit_curvature
      hT S hS x t htmem htpos hpos hmax htheta htlower hscalar P (U n) (P.maps.base_mem n)
      (N n) rho hrho s hs (fun i => F n i s) ((G s).restrictOpen (U n))
      (P.limit.metric.restrictOpen (U n)) (hsource n) (fun i => hmetric n i s) (by
        intro K hK p epsilon hepsilon
        obtain ⟨j, hj⟩ := hconv n K hK p epsilon hepsilon
        exact ⟨j, fun i hi => hj i hi s hsn⟩)
    constructor
    · intro v w
      have hc' := hc.1 (⟨y, hyn⟩ : U n) v w
      rw [metricRm04StandardAt_restrictOpen (I := I3) (G s) (U n)
        (⟨y, hyn⟩ : U n) v w w v, mfderiv_subtype_val (I := I3) (U n) (⟨y, hyn⟩ : U n)] at hc'
      exact hc'
    · simpa only [metricScalarAt_restrictOpen] using hc.2 (⟨y, hyn⟩ : U n)
  intro s hs
  refine ⟨fun y => (hcurv s hs y).1, fun y => (hcurv s hs y).2, ?_⟩
  apply complete_at_earlier_time_of_ricci_nonnegative
    ({ base.metric := G } : SolutionOn (I := I3) (M := P.limit.M)
      (RealTimeInterval.infiniteClosed 0 0 le_rfl)) hGsol
    (a := s) (b := 0) (fun _ ht => ht.2) (fun _ ht => ht.2)
  · intro r hr y v
    change 0 ≤ metricRicciAt (G r) y (vec2 v v)
    rw [metricRicciAt_apply_eq_ricciTensor (I := I3) (G r) y v v]
    exact DifferentialGeometry.Geometry.Riemannian.BonnetMyers.ricci_nonneg_of_sec
      (G r) y ((metricRm04At_mem_tensor04SectionalNonnegativeCone_iff (G r) y).mpr
        (hcurv r hr.2.le y).1) v
  · change RiemannianMetricComplete (G 0)
    rw [hG0]
    exact ⟨P.limit_complete.complete⟩
  · exact ⟨le_rfl, hs⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

