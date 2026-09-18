import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalLocalBackwardFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalCommonExtraction
import DifferentialGeometry.Geometry.Metric.Distance.Finiteness

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff _root_.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_compatible_local_backward_flows_of_terminal_scalar_bound
    {kappa : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, 0 < sigma → ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
        ∀ A : ℝ, ∃ delta : ℝ, ∃ hd : 0 < delta,
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
          ∀ P : MetricCompactLimit (X.toFlowSequence.atTime 0),
            (∀ i, P.convergence.metrics.domain i =
              CanonicalMetricCompactness.canonicalSourceData P.maps i) →
            (∀ x : P.limit.M, metricScalarAt P.limit.metric x ≤ A) →
            ∀ U : ℕ → TopologicalSpace.Opens P.limit.M,
              (∀ n, P.limit.basepoint ∈ U n) →
              (∀ n, (U n : Set P.limit.M) ⊆
                riemannianClosedBallOf (I := I3) P.limit.metric P.limit.basepoint ((n : ℝ) + 1)) →
              ∃ N : ℕ → ℕ,
                ∃ S : ∀ n, ℕ → SolutionOn (I := I3) (M := U n)
                  (RealTimeInterval.closed (-delta) 0 (by linarith)),
                  (∀ n i, IsSolutionOn (S n i)) ∧
                  (∀ n i, (U n : Set P.limit.M) ⊆
                    (P.maps.partialDiffeomorph (i + N n)).source) ∧
                  (∀ n i t (x : U n) (v w : TangentSpace I3 x),
                    ((S n i).base.metric t).inner x v w =
                      ((X.term (P.subseq (i + N n))).S.base.metric t).inner
                        (P.maps.partialDiffeomorph (i + N n) x)
                        (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N n)) x v)
                        (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N n)) x w)) ∧
                  ∃ rho : ℕ → ℕ, StrictMono rho ∧
                    ∃ g : ∀ n, ℝ → SmoothRiemannianMetric I3 (U n),
                      (∀ n, g n 0 = P.limit.metric.restrictOpen (U n)) ∧
                      (∀ n, IsSolutionOn ({ base.metric := g n } :
                        SolutionOn (I := I3) (M := U n)
                          (RealTimeInterval.closed (-delta / 2) 0
                            (by linarith)))) ∧
                      (∀ n, ∀ K : Set (U n), IsCompact K → ∀ p : ℕ,
                        ∀ epsilon : ℝ, 0 < epsilon → ∃ j : ℕ, ∀ i ≥ j,
                          ∀ t ∈ Icc (-delta / 2) 0,
                            metricDerivNormSupOn K p ((S n (rho i - N n)).base.metric t)
                              (g n t) (P.limit.metric.restrictOpen (U n)) < epsilon) ∧
                      (∀ n m, ∀ W : TopologicalSpace.Opens P.limit.M,
                        (hWn : W ≤ U n) → (hWm : W ≤ U m) →
                        ∀ t, t ∈ Icc (-delta / 2) 0 →
                          (g n t).restrictOpenOfSubset hWn =
                            (g m t).restrictOpenOfSubset hWm) := by
  obtain ⟨epsStar, hepsStar, hlocal⟩ :=
    exists_local_pullback_solutions_of_terminal_scalar_bound hmod
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi A
  obtain ⟨delta, hd, hlocalA⟩ := hlocal eps heps hle sigma hsigma Phi hPhi A
  refine ⟨delta, hd, ?_⟩
  intro X P hcanonical hscalar U hpU hU
  let _ (n : ℕ) : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 (U n).isOpen)
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hlocalU (n : ℕ) :=
    hlocalA X P hcanonical hscalar
      P.limit.basepoint ((n : ℝ) + 1) (by positivity) (U n) (hU n)
  choose N S hS hsource hmetric hterminal C hC hjet using hlocalU
  have hslab : Icc (-delta / 2) 0 ⊆
      (RealTimeInterval.closed (-delta) 0 (by linarith)).carrier := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hreg : Ico (-delta / 2) 0 ⊆
      (RealTimeInterval.closed (-delta) 0 (by linarith)).regular := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  obtain ⟨rho, hrho, g, hg0, hconv, hoverlap⟩ :=
    exists_common_metric_subsequence_on_terminal_maps_of_terminal_convergence
      X.toFlowSequence P U
      (fun _ => RealTimeInterval.closed (-delta) 0 (by linarith))
      S hS (fun n => P.limit.metric.restrictOpen (U n))
      (fun _ => -delta / 2) (fun _ => 0) (fun _ => by linarith)
      (fun _ => hslab) (fun _ => hreg) hterminal (by
        intro n K _hK q
        exact ⟨C n q, hC n q, Eventually.of_forall fun i t ht x _ =>
          hjet n i q t ⟨by linarith [ht.1], ht.2⟩ x⟩)
      N hsource (fun n i t x v w _ht _hx => hmetric n i t x v w)
  refine ⟨N, S, hS, hsource, hmetric, rho, hrho, g, hg0, ?_, hconv,
    fun n m W hn hm t ht => hoverlap n m W hn hm t ht ht⟩
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
    (fun i => S n (rho i - N n)) (fun i => hS n (rho i - N n))
    (show -delta / 2 < 0 by linarith)
    hslab (Ioo_subset_Ico_self.trans hreg) id strictMono_id (g n)
    (hconv n) (by
      intro K hK p
      exact Eventually.of_forall fun i => by
        obtain ⟨L, _hL, hb⟩ := exists_metric_time_lipschitz_constant_on_compact_of_solution
          (S n (rho i - N n)) (hS n (rho i - N n))
          (show -delta / 2 < 0 by linarith)
          hslab hreg Q.metric hK p
        exact ⟨L, fun s hs t ht q hq x hx => hb q hq s hs t ht x hx⟩)

private theorem compatible_backward_flows_on_bounded_open_sets
    {kappa : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, 0 < sigma → ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
          ∀ P : MetricCompactLimit (X.toFlowSequence.atTime 0),
            (∀ i, P.convergence.metrics.domain i =
              CanonicalMetricCompactness.canonicalSourceData P.maps i) →
            ∀ U : ℕ → TopologicalSpace.Opens P.limit.M,
              (∀ n, P.limit.basepoint ∈ U n) →
              (∀ n, (U n : Set P.limit.M) ⊆
                riemannianClosedBallOf (I := I3) P.limit.metric P.limit.basepoint ((n : ℝ) + 1)) →
              ∃ delta : ℕ → ℝ, ∃ hd : ∀ n, 0 < delta n, ∃ N : ℕ → ℕ,
                ∃ S : ∀ n, ℕ → SolutionOn (I := I3) (M := U n)
                  (RealTimeInterval.closed (-delta n) 0 (by have := hd n; linarith)),
                  (∀ n i, IsSolutionOn (S n i)) ∧
                  (∀ n i, (U n : Set P.limit.M) ⊆
                    (P.maps.partialDiffeomorph (i + N n)).source) ∧
                  (∀ n i t (x : U n) (v w : TangentSpace I3 x),
                    ((S n i).base.metric t).inner x v w =
                      ((X.term (P.subseq (i + N n))).S.base.metric t).inner
                        (P.maps.partialDiffeomorph (i + N n) x)
                        (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N n)) x v)
                        (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N n)) x w)) ∧
                  ∃ rho : ℕ → ℕ, StrictMono rho ∧
                    ∃ g : ∀ n, ℝ → SmoothRiemannianMetric I3 (U n),
                      (∀ n, g n 0 = P.limit.metric.restrictOpen (U n)) ∧
                      (∀ n, IsSolutionOn ({ base.metric := g n } :
                        SolutionOn (I := I3) (M := U n)
                          (RealTimeInterval.closed (-delta n / 2) 0
                            (by have := hd n; linarith)))) ∧
                      (∀ n, ∀ K : Set (U n), IsCompact K → ∀ p : ℕ,
                        ∀ epsilon : ℝ, 0 < epsilon → ∃ j : ℕ, ∀ i ≥ j,
                          ∀ t ∈ Icc (-delta n / 2) 0,
                            metricDerivNormSupOn K p ((S n (rho i - N n)).base.metric t)
                              (g n t) (P.limit.metric.restrictOpen (U n)) < epsilon) ∧
                      (∀ n m, ∀ W : TopologicalSpace.Opens P.limit.M,
                        (hWn : W ≤ U n) → (hWm : W ≤ U m) →
                        ∀ t, t ∈ Icc (-delta n / 2) 0 → t ∈ Icc (-delta m / 2) 0 →
                          (g n t).restrictOpenOfSubset hWn =
                            (g m t).restrictOpenOfSubset hWm) := by
  obtain ⟨epsStar, hepsStar, hlocal⟩ :=
    exists_local_pullback_curvature_bounds_of_terminal_metric_convergence hmod
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X P hcanonical U hpU hU
  let _ (n : ℕ) : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 (U n).isOpen)
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hlocalU (n : ℕ) :=
    hlocal eps heps hle sigma hsigma Phi hPhi X P hcanonical
      P.limit.basepoint ((n : ℝ) + 1) (by positivity) (U n) (hU n)
  choose delta hd N S hS hsource hmetric hterminal C hC hjet using hlocalU
  have hslab (n : ℕ) : Icc (-delta n / 2) 0 ⊆
      (RealTimeInterval.closed (-delta n) 0 (by have := hd n; linarith)).carrier := by
    intro t ht
    exact ⟨by have := hd n; linarith [ht.1], ht.2⟩
  have hreg (n : ℕ) : Ico (-delta n / 2) 0 ⊆
      (RealTimeInterval.closed (-delta n) 0 (by have := hd n; linarith)).regular := by
    intro t ht
    exact ⟨by have := hd n; linarith [ht.1], ht.2⟩
  obtain ⟨rho, hrho, g, hg0, hconv, hoverlap⟩ :=
    exists_common_metric_subsequence_on_terminal_maps_of_terminal_convergence
      X.toFlowSequence P U
      (fun n => RealTimeInterval.closed (-delta n) 0 (by have := hd n; linarith))
      S hS (fun n => P.limit.metric.restrictOpen (U n))
      (fun n => -delta n / 2) (fun _ => 0) (fun n => by have := hd n; linarith)
      hslab hreg hterminal (by
        intro n K _hK q
        exact ⟨C n q, hC n q, Eventually.of_forall fun i t ht x _ =>
          hjet n i q t ⟨by have := hd n; linarith [ht.1], ht.2⟩ x⟩)
      N hsource (fun n i t x v w _ht _hx => hmetric n i t x v w)
  refine ⟨delta, hd, N, S, hS, hsource, hmetric, rho, hrho, g, hg0, ?_, hconv, hoverlap⟩
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
    (fun i => S n (rho i - N n)) (fun i => hS n (rho i - N n))
    (show -delta n / 2 < 0 by have := hd n; linarith)
    (hslab n) (Ioo_subset_Ico_self.trans (hreg n)) id strictMono_id (g n)
    (hconv n) (by
      intro K hK p
      exact Eventually.of_forall fun i => by
        obtain ⟨L, _hL, hb⟩ := exists_metric_time_lipschitz_constant_on_compact_of_solution
          (S n (rho i - N n)) (hS n (rho i - N n))
          (show -delta n / 2 < 0 by have := hd n; linarith)
          (hslab n) (hreg n) Q.metric hK p
        exact ⟨L, fun s hs t ht q hq x hx => hb q hq s hs t ht x hx⟩)

theorem exists_compatible_local_backward_flows_on_exhaustion_of_terminal_metric_convergence
    {kappa : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, 0 < sigma → ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
          ∀ P : MetricCompactLimit (X.toFlowSequence.atTime 0),
            (∀ i, P.convergence.metrics.domain i =
              CanonicalMetricCompactness.canonicalSourceData P.maps i) →
            ConnectedSpace P.limit.M →
            ∃ U : ℕ → TopologicalSpace.Opens P.limit.M,
              (∀ n, (U n : Set P.limit.M) =
                riemannianBallOf (I := I3) P.limit.metric P.limit.basepoint ((n : ℝ) + 1)) ∧
              ExhaustsByOpen (fun n => (U n : Set P.limit.M)) ∧
              (∀ n, IsCompact (closure (U n : Set P.limit.M))) ∧
              ∃ delta : ℕ → ℝ, ∃ hd : ∀ n, 0 < delta n, ∃ N : ℕ → ℕ,
                ∃ S : ∀ n, ℕ → SolutionOn (I := I3) (M := U n)
                  (RealTimeInterval.closed (-delta n) 0 (by have := hd n; linarith)),
                  (∀ n i, IsSolutionOn (S n i)) ∧
                  (∀ n i, (U n : Set P.limit.M) ⊆
                    (P.maps.partialDiffeomorph (i + N n)).source) ∧
                  (∀ n i t (x : U n) (v w : TangentSpace I3 x),
                    ((S n i).base.metric t).inner x v w =
                      ((X.term (P.subseq (i + N n))).S.base.metric t).inner
                        (P.maps.partialDiffeomorph (i + N n) x)
                        (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N n)) x v)
                        (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N n)) x w)) ∧
                  ∃ rho : ℕ → ℕ, StrictMono rho ∧
                    ∃ g : ∀ n, ℝ → SmoothRiemannianMetric I3 (U n),
                      (∀ n, g n 0 = P.limit.metric.restrictOpen (U n)) ∧
                      (∀ n, IsSolutionOn ({ base.metric := g n } :
                        SolutionOn (I := I3) (M := U n)
                          (RealTimeInterval.closed (-delta n / 2) 0
                            (by have := hd n; linarith)))) ∧
                      (∀ n, ∀ K : Set (U n), IsCompact K → ∀ p : ℕ,
                        ∀ epsilon : ℝ, 0 < epsilon → ∃ j : ℕ, ∀ i ≥ j,
                          ∀ t ∈ Icc (-delta n / 2) 0,
                            metricDerivNormSupOn K p ((S n (rho i - N n)).base.metric t)
                              (g n t) (P.limit.metric.restrictOpen (U n)) < epsilon) ∧
                      (∀ n m, ∀ W : TopologicalSpace.Opens P.limit.M,
                        (hWn : W ≤ U n) → (hWm : W ≤ U m) →
                        ∀ t, t ∈ Icc (-delta n / 2) 0 → t ∈ Icc (-delta m / 2) 0 →
                          (g n t).restrictOpenOfSubset hWn =
                            (g m t).restrictOpenOfSubset hWm) := by
  obtain ⟨epsStar, hepsStar, hlocal⟩ :=
    compatible_backward_flows_on_bounded_open_sets hmod
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X P hcanonical hconn
  let _ : ConnectedSpace P.limit.M := hconn
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let _ : EMetricSpace P.limit.M := P.limit.emetricSpace
  let U : ℕ → TopologicalSpace.Opens P.limit.M := fun n =>
    ⟨riemannianBallOf (I := I3) P.limit.metric P.limit.basepoint ((n : ℝ) + 1), by
      change IsOpen {x : P.limit.M | edist P.limit.basepoint x < ENNReal.ofReal ((n : ℝ) + 1)}
      exact isOpen_lt (continuous_const.edist continuous_id) continuous_const⟩
  have hbounded (n : ℕ) : (U n : Set P.limit.M) ⊆
      riemannianClosedBallOf (I := I3) P.limit.metric P.limit.basepoint ((n : ℝ) + 1) :=
    fun x hx => (show riemannianEDistOf (I := I3) P.limit.metric
      P.limit.basepoint x < ENNReal.ofReal ((n : ℝ) + 1) from hx).le
  have hbase (n : ℕ) : P.limit.basepoint ∈ U n := by
    change riemannianEDistOf (I := I3) P.limit.metric P.limit.basepoint P.limit.basepoint < _
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hmono : Monotone (fun n => (U n : Set P.limit.M)) := by
    intro n m hnm
    exact riemannianBallOf_mono _ _ (by exact_mod_cast Nat.add_le_add_right hnm 1)
  have hcover : (⋃ n, (U n : Set P.limit.M)) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨n, hn⟩ := exists_nat_gt (riemannianEDistOf (I := I3)
      P.limit.metric P.limit.basepoint x).toReal
    refine mem_iUnion.mpr ⟨n, ?_⟩
    exact (ENNReal.lt_ofReal_iff_toReal_lt
      (riemannianEDistOf_ne_top P.limit.metric _ _)).mpr (by linarith)
  have hexhausts : ExhaustsByOpen (fun n => (U n : Set P.limit.M)) := by
    refine ⟨fun n => (U n).isOpen, fun n => hmono (Nat.le_succ n), ?_⟩
    intro K hK
    obtain ⟨n, hn⟩ := hK.elim_directed_cover (fun n => (U n : Set P.limit.M))
      (fun n => (U n).isOpen) (by rw [hcover]; exact subset_univ K)
      (fun n m => ⟨max n m, hmono (le_max_left n m), hmono (le_max_right n m)⟩)
    exact ⟨n, fun m hnm => hn.trans (hmono hnm)⟩
  have hcomplete : RiemannianMetricComplete (I := I3) P.limit.metric :=
    ⟨MetricComplete.complete (I := I3) P.limit P.limit_complete⟩
  have hcompact (n : ℕ) : IsCompact (closure (U n : Set P.limit.M)) := by
    have hK := hcomplete.closedEBall_isCompact P.limit.basepoint ((n : ℝ) + 1)
    exact hK.of_isClosed_subset isClosed_closure
      (closure_minimal (hbounded n) hK.isClosed)
  exact ⟨U, fun _ => rfl, hexhausts, hcompact,
    hlocal eps heps hle sigma hsigma Phi hPhi X P hcanonical U hbase hbounded⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
