import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureLocalBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureSequence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.BallImage
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalCommonExtraction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.LocalPullback
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.FixedDomain
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.PartialDiffeomorph
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.AncientGluing

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
  [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [T2Space (TangentBundle I3 M)]

theorem exists_highCurvatureFlowSequence_local_pullback_solutions
    {T A : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    (hscalar : Tendsto (fun i => S.scalar (t i) (x i)) atTop atTop)
    (P : MetricCompactLimit
      ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).atTime 0))
    (hcanonical : ∀ i, P.convergence.metrics.domain i =
      CanonicalMetricCompactness.canonicalSourceData P.maps i)
    (hconn : ConnectedSpace P.limit.M)
    (U : TopologicalSpace.Opens P.limit.M) (hU : IsCompact (closure (U : Set P.limit.M)))
    (hA : 0 < A) :
    ∃ N : ℕ, ∃ F : ℕ → SolutionOn (I := I3) (M := U)
        (RealTimeInterval.closed (-A) 0 (by linarith)),
      (∀ i, IsSolutionOn (F i)) ∧
      (∀ i, (U : Set P.limit.M) ⊆ (P.maps.partialDiffeomorph (i + N)).source) ∧
      (∀ i s (y : U) (v w : TangentSpace I3 y),
        ((F i).base.metric s).inner y v w =
          (((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term
            (P.subseq (i + N))).S.base.metric s).inner
            (P.maps.partialDiffeomorph (i + N) y)
            (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N)) y v)
            (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N)) y w)) ∧
      MetricCInfConvergenceOnCompacts (fun i => (F i).base.metric 0)
        (P.limit.metric.restrictOpen U) (P.limit.metric.restrictOpen U) ∧
      ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧ ∀ i m s, s ∈ Icc (-A) 0 → ∀ y : U,
        curvDerivNorm m ((F i).base.metric s) y ≤ C m := by
  let X := highCurvatureFlowSequence hT S hS x t htmem htpos hpos
  let _ : ConnectedSpace P.limit.M := hconn
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)
  have href : ∀ i, (P.convergence.metrics.domain i).referenceMetric =
      (P.convergence.metrics.domain i).limitMetric := by
    intro i
    rw [hcanonical i]
    rfl
  obtain ⟨R, hR, himage⟩ := P.maps.exists_eventually_image_compact_subset_ball
    P.convergence.metrics href P.limit_complete hU
  obtain ⟨C, hC, hbounds⟩ := exists_high_curvature_rescaled_curvature_derivative_bounds.{u}
  obtain ⟨Q0, hQ0, hbound⟩ := hbounds M T hT S hS o R A hR hA.le
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((P.strictMono.tendsto_atTop.eventually (hscalar.eventually_ge_atTop Q0)).and himage)
  have hsource (i : ℕ) : (U : Set P.limit.M) ⊆
      (P.maps.partialDiffeomorph (i + N)).source :=
    subset_closure.trans (hN (i + N) (by omega)).2.1
  have hleft (i : ℕ) : -(t (P.subseq (i + N)) *
      S.scalar (t (P.subseq (i + N))) (x (P.subseq (i + N)))) ≤ -A := by
    have ht := (hbound (x (P.subseq (i + N))) (t (P.subseq (i + N)))
      (htmem _) (hN (i + N) (by omega)).1).1 (-A) ⟨le_rfl, by linarith⟩
    have hlo : -t (P.subseq (i + N)) ≤ -A /
        S.scalar (t (P.subseq (i + N))) (x (P.subseq (i + N))) := by
      have := ht.1
      dsimp only [parabolicTime] at this
      linarith
    simpa only [neg_mul] using (le_div_iff₀ (hpos _)).mp hlo
  let D := RealTimeInterval.closed (-A) 0 (by linarith : -A ≤ 0)
  have hpull (i : ℕ) : ∃ F : SolutionOn (I := I3) (M := U) D,
      IsSolutionOn F ∧ ∀ s (y : U) (v w : TangentSpace I3 y),
        (F.base.metric s).inner y v w =
          ((X.term (P.subseq (i + N))).S.base.metric s).inner
            (P.maps.partialDiffeomorph (i + N) y)
            (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N)) y v)
            (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N)) y w) := by
    obtain ⟨S', hS', hmetric⟩ := KappaSolutions.exists_local_solution_of_partialDiffeomorph
      (X.term (P.subseq (i + N))).S (X.term (P.subseq (i + N))).isSolution
      (P.maps.partialDiffeomorph (i + N)) U (hsource i)
    exact ⟨S'.timeRestrict D, isSolutionOn_timeRestrict hS'
      (Icc_subset_Icc (hleft i) le_rfl) (Ioo_subset_Ioo (hleft i) le_rfl), hmetric⟩
  choose F hF hmetric using hpull
  refine ⟨N, F, hF, hsource, hmetric, ?_, C R, fun m => (hC R m).le, ?_⟩
  · exact metricCInfConvergenceOnCompacts_of_pointed_pullback
      P.maps P.convergence.metrics hcanonical U N hsource
      (fun i => (F i).base.metric 0) (fun i => hmetric i 0)
  · intro i m s hsi y
    have he := @curvDerivNorm_eq_of_partialDiffeomorph_restriction ThreeSpace ThreeSpace
      P.limit.M (X.term (P.subseq (i + N))).M _ _ _ _ I3
      P.limit.topology P.limit.charted P.limit.smooth P.limit.t2
      (X.term (P.subseq (i + N))).topology (X.term (P.subseq (i + N))).charted
      (X.term (P.subseq (i + N))).smooth (X.term (P.subseq (i + N))).t2
      (P.maps.partialDiffeomorph (i + N)) U (hsource i) ((F i).base.metric s)
      ((X.term (P.subseq (i + N))).S.base.metric s) (hmetric i s) m y
    apply he.trans_le
    exact (hbound (x (P.subseq (i + N))) (t (P.subseq (i + N)))
      (htmem _) (hN (i + N) (by omega)).1).2 0 ⟨by linarith, le_rfl⟩ s hsi _
      ((hN (i + N) (by omega)).2.2 ⟨y, subset_closure y.property, rfl⟩) m

theorem exists_highCurvatureFlowSequence_compatible_local_backward_flows_of_closed_oriented
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    (hscalar : Tendsto (fun i => S.scalar (t i) (x i)) atTop atTop)
    (P : MetricCompactLimit
      ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).atTime 0))
    (hcanonical : ∀ i, P.convergence.metrics.domain i =
      CanonicalMetricCompactness.canonicalSourceData P.maps i)
    (hconn : ConnectedSpace P.limit.M)
    (U : ℕ → TopologicalSpace.Opens P.limit.M)
    (hpU : ∀ n, P.limit.basepoint ∈ U n)
    (hU : ∀ n, IsCompact (closure (U n : Set P.limit.M)))
    (A : ℕ → ℝ) (hA : ∀ n, 0 < A n) :
    ∃ N : ℕ → ℕ,
      ∃ F : ∀ n, ℕ → SolutionOn (I := I3) (M := U n)
          (RealTimeInterval.closed (-(A n + 1)) 0 (by have := hA n; linarith)),
        (∀ n i, IsSolutionOn (F n i)) ∧
        (∀ n i, (U n : Set P.limit.M) ⊆ (P.maps.partialDiffeomorph (i + N n)).source) ∧
        (∀ n i s (y : U n) (v w : TangentSpace I3 y),
          ((F n i).base.metric s).inner y v w =
            (((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term
              (P.subseq (i + N n))).S.base.metric s).inner
              (P.maps.partialDiffeomorph (i + N n) y)
              (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N n)) y v)
              (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N n)) y w)) ∧
        ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∃ g : ∀ n, ℝ → SmoothRiemannianMetric I3 (U n),
          (∀ n, g n 0 = P.limit.metric.restrictOpen (U n)) ∧
          (∀ n, IsSolutionOn ({ base.metric := g n } : SolutionOn (I := I3) (M := U n)
            (RealTimeInterval.closed (-A n) 0 (by have := hA n; linarith)))) ∧
          (∀ n, ∀ K : Set (U n), IsCompact K → ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
            ∃ j : ℕ, ∀ i ≥ j, ∀ s ∈ Icc (-A n) 0,
              metricDerivNormSupOn K p ((F n (rho i - N n)).base.metric s)
                (g n s) (P.limit.metric.restrictOpen (U n)) < epsilon) ∧
          ∀ n m, ∀ W : TopologicalSpace.Opens P.limit.M,
            (hWn : W ≤ U n) → (hWm : W ≤ U m) →
            ∀ s, s ∈ Icc (-A n) 0 → s ∈ Icc (-A m) 0 →
              (g n s).restrictOpenOfSubset hWn = (g m s).restrictOpenOfSubset hWm := by
  let X := highCurvatureFlowSequence hT S hS x t htmem htpos hpos
  let _ (n : ℕ) : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 (U n).isOpen)
  have hlocal (n : ℕ) := exists_highCurvatureFlowSequence_local_pullback_solutions
    hT S hS o x t htmem htpos hpos hscalar P hcanonical hconn (U n) (hU n)
      (by have := hA n; linarith : 0 < A n + 1)
  choose N F hF hsource hmetric hterminal C hC hjets using hlocal
  have hslab (n : ℕ) : Icc (-A n) 0 ⊆
      (RealTimeInterval.closed (-(A n + 1)) 0 (by have := hA n; linarith)).carrier := by
    intro s hs
    exact ⟨by linarith [hs.1], hs.2⟩
  have hreg (n : ℕ) : Ico (-A n) 0 ⊆
      (RealTimeInterval.closed (-(A n + 1)) 0 (by have := hA n; linarith)).regular := by
    intro s hs
    exact ⟨by linarith [hs.1], hs.2⟩
  obtain ⟨rho, hrho, g, hg0, hgsol, hconv, hoverlap⟩ :=
    exists_common_solution_subsequence_on_terminal_maps_of_terminal_convergence X P U hpU
      (fun n => RealTimeInterval.closed (-(A n + 1)) 0 (by have := hA n; linarith))
      F hF (fun n => P.limit.metric.restrictOpen (U n))
      (fun n => -A n) (fun _ => 0) (fun n => neg_neg_of_pos (hA n))
      hslab hreg hterminal (by
        intro n K _hK q
        refine ⟨C n q, hC n q, ?_⟩
        exact Eventually.of_forall fun i s hs y _ =>
          hjets n i q s ⟨by linarith [hs.1], hs.2⟩ y)
      N hsource (fun n i s y v w _ _ => hmetric n i s y v w)
  exact ⟨N, F, hF, hsource, hmetric, rho, hrho, g, hg0, hgsol, hconv, hoverlap⟩

theorem exists_highCurvatureFlowSequence_ancient_metric_limit_of_closed_oriented
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    (hscalar : Tendsto (fun i => S.scalar (t i) (x i)) atTop atTop)
    (P : MetricCompactLimit
      ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).atTime 0))
    (hcanonical : ∀ i, P.convergence.metrics.domain i =
      CanonicalMetricCompactness.canonicalSourceData P.maps i)
    (hconn : ConnectedSpace P.limit.M)
    (hcompact : ∀ n, IsCompact (closure (P.maps.source n))) :
    let U := metricSourceOpenSubset P.maps
    ∃ N : ℕ → ℕ,
      ∃ F : ∀ n, ℕ → SolutionOn (I := I3) (M := U n)
          (RealTimeInterval.closed (-(((n + 1 : ℕ) : ℝ) + 1)) 0 (by
            have := Nat.cast_nonneg (α := ℝ) (n + 1); linarith)),
        (∀ n i, IsSolutionOn (F n i)) ∧
        (∀ n i, (U n : Set P.limit.M) ⊆ (P.maps.partialDiffeomorph (i + N n)).source) ∧
        (∀ n i s (y : U n) (v w : TangentSpace I3 y),
          ((F n i).base.metric s).inner y v w =
            (((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term
              (P.subseq (i + N n))).S.base.metric s).inner
              (P.maps.partialDiffeomorph (i + N n) y)
              (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N n)) y v)
              (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N n)) y w)) ∧
        ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∃ G : ℝ → SmoothRiemannianMetric I3 P.limit.M,
          G 0 = P.limit.metric ∧
          IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := P.limit.M)
            (RealTimeInterval.infiniteClosed 0 0 le_rfl)) ∧
          ∀ n, ∀ K : Set (U n), IsCompact K → ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
            ∃ j : ℕ, ∀ i ≥ j, ∀ s ∈ Icc (-((n + 1 : ℕ) : ℝ)) 0,
              metricDerivNormSupOn K p ((F n (rho i - N n)).base.metric s)
                ((G s).restrictOpen (U n)) (P.limit.metric.restrictOpen (U n)) < epsilon := by
  let U := metricSourceOpenSubset P.maps
  have hcover : ∀ y : P.limit.M, ∃ n, y ∈ U n := by
    intro y
    obtain ⟨n, hn⟩ := P.maps.source_exhausts.subset {y} isCompact_singleton
    exact ⟨n, hn n le_rfl (mem_singleton y)⟩
  have hmono : Monotone U := P.maps.source_exhausts.monotone
  obtain ⟨N, F, hF, hsource, hmetric, rho, hrho, g, hg0, hgsol, hconv, hoverlap⟩ :=
    exists_highCurvatureFlowSequence_compatible_local_backward_flows_of_closed_oriented
      hT S hS o x t htmem htpos hpos hscalar P hcanonical hconn U
      (fun n => P.maps.base_mem n) hcompact (fun n => ((n + 1 : ℕ) : ℝ))
      (fun n => Nat.cast_pos.mpr (Nat.succ_pos n))
  obtain ⟨G, hGsol, hG⟩ := exists_ancient_solution_of_compatible_open_cover
    U hmono hcover g hgsol (fun n m s hn hm =>
      hoverlap n m (U n ⊓ U m) inf_le_left inf_le_right s hn hm)
  refine ⟨N, F, hF, hsource, hmetric, rho, hrho, G, ?_, hGsol, ?_⟩
  · apply SmoothRiemannianMetric.ext_inner
    intro y v w
    obtain ⟨n, hyn⟩ := hcover y
    have heq := (hG n 0 ⟨neg_nonpos.mpr (Nat.cast_nonneg _), le_rfl⟩).trans (hg0 n)
    exact congrArg (fun k : SmoothRiemannianMetric I3 (U n) => k.inner ⟨y, hyn⟩ v w) heq
  · intro n K hK p epsilon hepsilon
    obtain ⟨j, hj⟩ := hconv n K hK p epsilon hepsilon
    refine ⟨j, fun i hi s hs => ?_⟩
    rw [hG n s hs]
    exact hj i hi s hs


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
