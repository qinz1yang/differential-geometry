import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureMetricLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalCommonExtraction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.LocalPullback
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.FixedDomain
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.PartialDiffeomorph
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.FixedDomain

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

private theorem exists_highCurvatureFlowSequence_local_pullbacks
    {T theta A : ℝ} (hT : 0 < T)
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
    (hcanonical : ∀ i, P.convergence.metrics.domain i =
      CanonicalMetricCompactness.canonicalSourceData P.maps i)
    (U : TopologicalSpace.Opens P.limit.M) (hU : IsCompact (closure (U : Set P.limit.M)))
    (hA : 0 < A) :
    ∃ N : ℕ, ∃ F : ℕ → SolutionOn (I := I3) (M := U)
        (RealTimeInterval.closed (-(A + 1)) 0 (by linarith)),
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
      ∀ i m s, s ∈ Icc (-(A + 1)) 0 → ∀ y : U,
        curvDerivNorm m ((F i).base.metric s) y ≤ shiLocalUniformBound 3 m 16 4 * 16 := by
  let X := highCurvatureFlowSequence hT S hS x t htmem htpos hpos
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)
  have hwindow := high_curvature_interval_eventually_contains_closed_window
    hT S x t htpos hpos htheta htlower hscalar (A + 1)
  have hjets := highCurvatureFlowSequence_curvDerivNorm_eventually_le_on_closed_window
    hT S hS x t htmem htpos hpos hmax htheta htlower hscalar (A + 1)
  obtain ⟨Ns, hs⟩ := P.maps.source_subset hU
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((P.strictMono.tendsto_atTop.eventually (hwindow.and hjets)).and
      (eventually_ge_atTop Ns))
  have hsource (i : ℕ) : (U : Set P.limit.M) ⊆
      (P.maps.partialDiffeomorph (i + N)).source :=
    subset_closure.trans (hs (i + N) (hN (i + N) (by omega)).2)
  let D := RealTimeInterval.closed (-(A + 1)) 0 (by linarith : -(A + 1) ≤ 0)
  have hpull (i : ℕ) : ∃ F : SolutionOn (I := I3) (M := U) D,
      IsSolutionOn F ∧ ∀ s (y : U) (v w : TangentSpace I3 y),
        (F.base.metric s).inner y v w =
          ((X.term (P.subseq (i + N))).S.base.metric s).inner
            (P.maps.partialDiffeomorph (i + N) y)
            (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N)) y v)
            (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N)) y w) := by
    let f := P.maps.partialDiffeomorph (i + N)
    let V : TopologicalSpace.Opens (X.term (P.subseq (i + N))).M :=
      ⟨f '' (U : Set P.limit.M), image_opens_isOpen f (hsource i)⟩
    let _ : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 V.isOpen)
    let e : U ≃ₘ⟮I3, I3⟯ V := PartialDiffeomorph.toOpensDiffeo f (hsource i)
    let F := solutionOnPullback
      (solutionOnRestrictOpen (X.term (P.subseq (i + N))).S V) e
    have hF : IsSolutionOn F := isSolutionOn_pullback _
      (isSolutionOn_restrictOpen _ (X.term (P.subseq (i + N))).isSolution V) e
    refine ⟨F.timeRestrict D,
      isSolutionOn_timeRestrict hF (hN (i + N) (by omega)).1.1.1
        (hN (i + N) (by omega)).1.1.2, ?_⟩
    intro s y v w
    change (Diffeomorph.pullbackMetric
      (((X.term (P.subseq (i + N))).S.base.metric s).restrictOpen V) e).inner y v w = _
    rw [Diffeomorph.pullbackMetric_inner, SmoothRiemannianMetric.restrictOpen_inner]
    exact congrArg₂
      (fun v' w' => ((X.term (P.subseq (i + N))).S.base.metric s).inner (f y) v' w')
      (PartialDiffeomorph.mfderiv_toOpensDiffeo f (hsource i) y v)
      (PartialDiffeomorph.mfderiv_toOpensDiffeo f (hsource i) y w)
  choose F hF hmetric using hpull
  refine ⟨N, F, hF, hsource, hmetric, ?_, ?_⟩
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
    exact he.trans_le ((hN (i + N) (by omega)).1.2 m s hsi _)


theorem exists_highCurvatureFlowSequence_compatible_local_backward_flows
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
    (hcanonical : ∀ i, P.convergence.metrics.domain i =
      CanonicalMetricCompactness.canonicalSourceData P.maps i)
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
  have hlocal (n : ℕ) := exists_highCurvatureFlowSequence_local_pullbacks
    hT S hS x t htmem htpos hpos hmax htheta htlower hscalar P hcanonical (U n) (hU n) (hA n)
  choose N F hF hsource hmetric hterminal hjets using hlocal
  have hslab (n : ℕ) : Icc (-A n) 0 ⊆
      (RealTimeInterval.closed (-(A n + 1)) 0 (by have := hA n; linarith)).carrier := by
    intro s hs
    exact ⟨by linarith [hs.1], hs.2⟩
  have hreg (n : ℕ) : Ico (-A n) 0 ⊆
      (RealTimeInterval.closed (-(A n + 1)) 0 (by have := hA n; linarith)).regular := by
    intro s hs
    exact ⟨by linarith [hs.1], hs.2⟩
  obtain ⟨rho, hrho, g, hg0, hconv, hoverlap⟩ :=
    exists_common_metric_subsequence_on_terminal_maps_of_terminal_convergence X P U
      (fun n => RealTimeInterval.closed (-(A n + 1)) 0 (by have := hA n; linarith))
      F hF (fun n => P.limit.metric.restrictOpen (U n))
      (fun n => -A n) (fun _ => 0) (fun n => neg_neg_of_pos (hA n))
      hslab hreg hterminal (by
        intro n K _hK q
        refine ⟨shiLocalUniformBound 3 q 16 4 * 16,
          mul_nonneg (shiLocalUniformBound_nonneg _ _ _ _) (by norm_num), ?_⟩
        exact Eventually.of_forall fun i s hs y _ =>
          hjets n i q s ⟨by linarith [hs.1], hs.2⟩ y)
      N hsource (fun n i s y v w _ _ => hmetric n i s y v w)
  refine ⟨N, F, hF, hsource, hmetric, rho, hrho, g, hg0, ?_, hconv, hoverlap⟩
  intro n
  let Q : PointedRiemannianManifold (I := I3) := {
    M := U n
    topology := inferInstance
    charted := inferInstance
    smooth := inferInstance
    sigmaCompact := inferInstance
    t2 := inferInstance
    t2TangentBundle := inferInstance
    basepoint := ⟨P.limit.basepoint, hpU n⟩
    metric := P.limit.metric.restrictOpen (U n) }
  exact isSolutionOn_of_fixed_domain_metric_convergence Q
    (fun i => F n (rho i - N n)) (fun i => hF n (rho i - N n))
    (neg_neg_of_pos (hA n)) (hslab n) (Ioo_subset_Ico_self.trans (hreg n))
    id strictMono_id (g n) (hconv n) (by
      intro K hK p
      exact Eventually.of_forall fun i => by
        obtain ⟨L, _hL, hb⟩ := exists_metric_time_lipschitz_constant_on_compact_of_solution
          (F n (rho i - N n)) (hF n (rho i - N n)) (neg_neg_of_pos (hA n))
          (hslab n) (hreg n) Q.metric hK p
        exact ⟨L, fun s hs r hr q hq y hy => hb q hq s hs r hr y hy⟩)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
