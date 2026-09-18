import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalCompatibleBackwardFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.OpenCover
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalNonnegativeCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison

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

theorem exists_backward_metric_limit_of_terminal_scalar_bound
    {kappa : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, 0 < sigma → ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
        ∀ A : ℝ, ∃ delta : ℝ, ∃ hd : 0 < delta,
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            ∀ P : MetricCompactLimit (X.toFlowSequence.atTime 0),
              (∀ i, P.convergence.metrics.domain i =
                CanonicalMetricCompactness.canonicalSourceData P.maps i) →
              ConnectedSpace P.limit.M →
              (∀ x : P.limit.M, metricScalarAt P.limit.metric x ≤ A) →
              ∃ U : ℕ → TopologicalSpace.Opens P.limit.M,
                (∀ n, (U n : Set P.limit.M) =
                  riemannianBallOf (I := I3) P.limit.metric P.limit.basepoint ((n : ℝ) + 1)) ∧
                ExhaustsByOpen (fun n => (U n : Set P.limit.M)) ∧
                (∀ n, IsCompact (closure (U n : Set P.limit.M))) ∧
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
                      ∃ G : ℝ → SmoothRiemannianMetric I3 P.limit.M,
                        G 0 = P.limit.metric ∧
                        IsSolutionOn ({ base.metric := G } :
                          SolutionOn (I := I3) (M := P.limit.M)
                            (RealTimeInterval.closed (-delta / 2) 0 (by linarith))) ∧
                        (∀ t ∈ Icc (-delta / 2) 0, SecLower (G t) 0 univ) ∧
                        (∀ t ∈ Icc (-delta / 2) 0, RiemannianMetricComplete (G t)) ∧
                        ∀ n, ∀ K : Set (U n), IsCompact K → ∀ p : ℕ,
                          ∀ epsilon : ℝ, 0 < epsilon → ∃ j : ℕ, ∀ i ≥ j,
                            ∀ t ∈ Icc (-delta / 2) 0,
                              metricDerivNormSupOn K p ((S n (rho i - N n)).base.metric t)
                                ((G t).restrictOpen (U n)) (P.limit.metric.restrictOpen (U n)) <
                                  epsilon := by
  obtain ⟨epsStar, hepsStar, hlocal⟩ :=
    exists_compatible_local_backward_flows_of_terminal_scalar_bound hmod
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi A
  obtain ⟨delta, hd, hlocalA⟩ := hlocal eps heps hle sigma hsigma Phi hPhi A
  refine ⟨delta, hd, ?_⟩
  intro X P hcanonical hconn hscalar
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
  obtain ⟨N, S, hS, hsource, hmetric, rho, hrho, g, hg0, hgsol, hconv, hoverlap⟩ :=
    hlocalA X P hcanonical hscalar U hbase hbounded
  have hUcover : ∀ y : P.limit.M, ∃ n, y ∈ U n := by
    intro y
    have hy : y ∈ (⋃ n, (U n : Set P.limit.M)) := by rw [hcover]; trivial
    exact mem_iUnion.mp hy
  obtain ⟨G, hGsol, hG⟩ := exists_solution_of_compatible_open_cover U hUcover g hgsol
    (fun n m t ht => hoverlap n m (U n ⊓ U m) inf_le_left inf_le_right t ht)
  have hG0 : G 0 = P.limit.metric := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    obtain ⟨n, hyn⟩ := hUcover y
    have heq := (hG n 0 ⟨by linarith, le_rfl⟩).trans (hg0 n)
    exact congrArg (fun k : SmoothRiemannianMetric I3 (U n) => k.inner ⟨y, hyn⟩ v w) heq
  have hsectional : ∀ t ∈ Icc (-delta / 2) 0, ∀ y : P.limit.M,
      ∀ v w : TangentSpace I3 y, 0 ≤ metricRm04StandardAt (G t) y v w w v := by
    intro t ht y v w
    obtain ⟨n, hyn⟩ := hUcover y
    have hn := secLower_zero_of_normalized_pullback_metric_convergence X hPhi P
      (U n) (hbase n) (N n) rho hrho t ht.2
      (fun i => (S n i).base.metric t) (g n t) (P.limit.metric.restrictOpen (U n))
      (hsource n) (fun i => hmetric n i t) (by
        intro K hK p epsilon hepsilon
        obtain ⟨j, hj⟩ := hconv n K hK p epsilon hepsilon
        exact ⟨j, fun i hi => hj i hi t ht⟩)
    have hn' (x : U n) (v w : TangentSpace I3 x) :
        0 ≤ metricRm04StandardAt (g n t) x v w w v := by
      have hvec : (fun i => ![v, w, w, v] i) = vec4 (I := I3) v w w v := by
        funext i
        fin_cases i <;> simp [vec4]
      simpa only [zero_mul, metricRm04StandardAt_apply, hvec] using hn x (mem_univ _) v w
    have hh' := hn' ⟨y, hyn⟩ v w
    rw [← hG n t ht, metricRm04StandardAt_restrictOpen (I := I3) (G t) (U n)
      (⟨y, hyn⟩ : U n) v w w v,
      mfderiv_subtype_val (I := I3) (U n) (⟨y, hyn⟩ : U n)] at hh'
    exact hh'
  refine ⟨U, fun _ => rfl, hexhausts, hcompact,
    N, S, hS, hsource, hmetric, rho, hrho, G, hG0, hGsol, ?_, ?_, ?_⟩
  · intro t ht y _hy v w
    have hvec : (fun i => ![v, w, w, v] i) = vec4 (I := I3) v w w v := by
      funext i
      fin_cases i <;> simp [vec4]
    simpa only [zero_mul, metricRm04StandardAt_apply, hvec] using hsectional t ht y v w
  · intro t ht
    apply complete_at_earlier_time_of_ricci_nonnegative
      ({ base.metric := G } : SolutionOn (I := I3) (M := P.limit.M)
        (RealTimeInterval.closed (-delta / 2) 0 (by linarith))) hGsol
      (a := -delta / 2) (b := 0) (fun _ h => h) (fun _ h => h)
    · intro r hr y v
      change 0 ≤ metricRicciAt (G r) y (vec2 v v)
      rw [metricRicciAt_apply_eq_ricciTensor (I := I3) (G r) y v v]
      exact DifferentialGeometry.Geometry.Riemannian.BonnetMyers.ricci_nonneg_of_sec
        (G r) y ((metricRm04At_mem_tensor04SectionalNonnegativeCone_iff (G r) y).mpr
          (hsectional r ⟨hr.1.le, hr.2.le⟩ y)) v
    · change RiemannianMetricComplete (G 0)
      rw [hG0]
      exact hcomplete
    · exact ht
  · intro n K hK p epsilon hepsilon
    obtain ⟨j, hj⟩ := hconv n K hK p epsilon hepsilon
    refine ⟨j, fun i hi t ht => ?_⟩
    rw [hG n t ht]
    exact hj i hi t ht

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
