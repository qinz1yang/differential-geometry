import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalCommonExtraction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Source.TerminalScalarCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.ScalarTerminalBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.MetricPinchingLimit
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Restriction
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciUpper
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff _root_.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_ancient_solution_subsequence_on_terminal_maps_of_scalar_deriv_nonneg_above
    (X : FlowSequence.{u}) (P : MetricCompactLimit (X.atTime 0))
    (U : ℕ → TopologicalSpace.Opens P.limit.M) (hU : Monotone U)
    (hcover : ∀ x : P.limit.M, ∃ n, x ∈ U n)
    (hpU : ∀ n, P.limit.basepoint ∈ U n)
    (D : ℕ → RealTimeInterval)
    (S : ∀ n : ℕ, ℕ → SolutionOn (I := I3) (M := U n) (D n))
    (hS : ∀ n i, IsSolutionOn (S n i))
    (hslab : ∀ n, Icc (-(2 * ((n + 1 : ℕ) : ℝ))) 0 ⊆ (D n).carrier)
    (hreg : ∀ n, Ioo (-(2 * ((n + 1 : ℕ) : ℝ))) 0 ⊆ (D n).regular)
    (hterminal : ∀ n, MetricCInfConvergenceOnCompacts
      (fun i => (S n i).base.metric 0)
      (P.limit.metric.restrictOpen (U n)) (P.limit.metric.restrictOpen (U n)))
    (N : ℕ → ℕ) {q scale : ℕ → ℝ} {q0 : ℕ → ℝ}
    (hq : ∀ n, ∀ᶠ i in atTop, q i ≤ q0 n)
    (hscale : Tendsto scale atTop atTop)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : ∀ n, ∀ᶠ j in atTop, PhiAlmostNonnegative (S n j)
      (Icc (-(2 * ((n + 1 : ℕ) : ℝ))) 0)
      (rescalePinchingFunction (scale (j + N n)) Phi))
    (hsign : ∀ n, ∀ K : Set (U n), IsCompact K → ∀ᶠ j in atTop,
      ∀ x ∈ K, ∀ t ∈ Ioo (-(2 * ((n + 1 : ℕ) : ℝ))) 0,
        q (j + N n) < (S n j).scalar t x →
          0 ≤ derivWithin (fun r => (S n j).scalar r x) (Iic t) t)
    (hsource : ∀ n i, (U n : Set P.limit.M) ⊆
      (P.maps.partialDiffeomorph (i + N n)).source)
    (hmetric : ∀ n j t (x : U n) (v w : TangentSpace I3 x),
      t ∈ Icc (-(2 * ((n + 1 : ℕ) : ℝ))) 0 →
      (x : P.limit.M) ∈ (P.maps.partialDiffeomorph (j + N n)).source →
      ((S n j).base.metric t).inner x v w =
        ((X.term (P.subseq (j + N n))).S.base.metric t).inner
          (P.maps.partialDiffeomorph (j + N n) x)
          (mfderiv I3 I3 (P.maps.partialDiffeomorph (j + N n)) x v)
          (mfderiv I3 I3 (P.maps.partialDiffeomorph (j + N n)) x w)) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∃ G : ℝ → SmoothRiemannianMetric I3 P.limit.M,
      G 0 = P.limit.metric ∧
      IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := P.limit.M)
        (RealTimeInterval.infiniteClosed 0 0 le_rfl)) ∧
      ∀ n, ∀ K : Set (U n), IsCompact K → ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
        ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc (-((n + 1 : ℕ) : ℝ)) 0,
          metricDerivNormSupOn K p ((S n (rho i - N n)).base.metric t)
            ((G t).restrictOpen (U n)) (P.limit.metric.restrictOpen (U n)) < epsilon := by
  let _ (n : ℕ) : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I3 (U n).isOpen)
  have hshort (n : ℕ) : Icc (-((n + 1 : ℕ) : ℝ)) 0 ⊆
      Icc (-(2 * ((n + 1 : ℕ) : ℝ))) 0 := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2, Nat.cast_nonneg (α := ℝ) (n + 1)]
  have hshortReg (n : ℕ) : Ico (-((n + 1 : ℕ) : ℝ)) 0 ⊆
      Ioo (-(2 * ((n + 1 : ℕ) : ℝ))) 0 := by
    intro t ht
    have hn : 0 < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
    constructor <;> linarith [ht.1,ht.2]
  apply exists_ancient_solution_subsequence_on_terminal_maps_of_terminal_convergence
    X P U hU hcover hpU D S hS (fun n => (hshort n).trans (hslab n))
    (fun n => (hshortReg n).trans (hreg n)) hterminal ?_ N hsource ?_
  · intro n K hK m
    have hn : 0 < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
    obtain ⟨C, hC, hbound⟩ :=
      exists_eventually_curvDerivNorm_bound_of_terminal_convergence_of_deriv_nonneg_above
        (S n) (hS n) (P.limit.metric.restrictOpen (U n))
        (by simp [ThreeSpace]) (by linarith : -(2 * ((n + 1 : ℕ) : ℝ)) < 0)
        (Eventually.of_forall fun _ => hslab n) (Eventually.of_forall fun _ => hreg n)
        (fun L hL => hterminal n L hL 2)
        ((tendsto_add_atTop_nat (N n)).eventually (hq n)) (hsign n) hPhi
        (hscale.comp (tendsto_add_atTop_nat (N n))) (hpinch n) K hK
    refine ⟨C m, hC m, hbound.mono fun j hj t ht x hx => ?_⟩
    apply hj m t ?_ x hx
    have heq : (-(2 * ((n + 1 : ℕ) : ℝ)) + 0) / 2 = -((n + 1 : ℕ) : ℝ) := by ring
    rwa [heq]
  · intro n j t x v w ht hx
    exact hmetric n j t x v w (hshort n ht) hx

theorem exists_ancient_solution_subsequence_on_terminal_maps_of_strongNeck_above
    (X : FlowSequence.{u}) (P : MetricCompactLimit (X.atTime 0))
    (U : ℕ → TopologicalSpace.Opens P.limit.M) (hU : Monotone U)
    (hcover : ∀ x : P.limit.M, ∃ n, x ∈ U n)
    (hpU : ∀ n, P.limit.basepoint ∈ U n)
    (D : ℕ → RealTimeInterval)
    (S : ∀ n : ℕ, ℕ → SolutionOn (I := I3) (M := U n) (D n))
    (hS : ∀ n i, IsSolutionOn (S n i))
    (hslab : ∀ n, Icc (-(2 * ((n + 1 : ℕ) : ℝ))) 0 ⊆ (D n).carrier)
    (hreg : ∀ n, Ioo (-(2 * ((n + 1 : ℕ) : ℝ))) 0 ⊆ (D n).regular)
    (hterminal : ∀ n, MetricCInfConvergenceOnCompacts
      (fun i => (S n i).base.metric 0)
      (P.limit.metric.restrictOpen (U n)) (P.limit.metric.restrictOpen (U n)))
    (N : ℕ → ℕ) {q scale : ℕ → ℝ} {q0 : ℕ → ℝ}
    (hq : ∀ n, ∀ᶠ i in atTop, q i ≤ q0 n)
    (hscale : Tendsto scale atTop atTop)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : ∀ n, ∀ᶠ j in atTop, PhiAlmostNonnegative (S n j)
      (Icc (-(2 * ((n + 1 : ℕ) : ℝ))) 0)
      (rescalePinchingFunction (scale (j + N n)) Phi))
    (hneck : ∀ n, ∀ K : Set (U n), IsCompact K → ∀ᶠ j in atTop,
      ∀ x ∈ K, ∀ t ∈ Ioo (-(2 * ((n + 1 : ℕ) : ℝ))) 0,
        q (j + N n) < (S n j).scalar t x →
          ∃ eps : ℝ, Nonempty (StrongNeck (S n j) eps x t))
    (hneckRegular : ∀ n, ∀ K : Set (U n), IsCompact K → ∀ᶠ j in atTop,
      ∀ x ∈ K, ∀ t ∈ Ioo (-(2 * ((n + 1 : ℕ) : ℝ))) 0,
        q (j + N n) < (S n j).scalar t x → ∀ s ∈ Ioo (-1 : ℝ) 0,
          parabolicTime t ((S n j).scalar t x) s ∈ (D n).regular)
    (hsource : ∀ n i, (U n : Set P.limit.M) ⊆
      (P.maps.partialDiffeomorph (i + N n)).source)
    (hmetric : ∀ n j t (x : U n) (v w : TangentSpace I3 x),
      t ∈ Icc (-(2 * ((n + 1 : ℕ) : ℝ))) 0 →
      (x : P.limit.M) ∈ (P.maps.partialDiffeomorph (j + N n)).source →
      ((S n j).base.metric t).inner x v w =
        ((X.term (P.subseq (j + N n))).S.base.metric t).inner
          (P.maps.partialDiffeomorph (j + N n) x)
          (mfderiv I3 I3 (P.maps.partialDiffeomorph (j + N n)) x v)
          (mfderiv I3 I3 (P.maps.partialDiffeomorph (j + N n)) x w)) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∃ G : ℝ → SmoothRiemannianMetric I3 P.limit.M,
      G 0 = P.limit.metric ∧
      IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := P.limit.M)
        (RealTimeInterval.infiniteClosed 0 0 le_rfl)) ∧
      ∀ n, ∀ K : Set (U n), IsCompact K → ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
        ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc (-((n + 1 : ℕ) : ℝ)) 0,
          metricDerivNormSupOn K p ((S n (rho i - N n)).base.metric t)
            ((G t).restrictOpen (U n)) (P.limit.metric.restrictOpen (U n)) < epsilon := by
  let _ (n : ℕ) : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I3 (U n).isOpen)
  apply exists_ancient_solution_subsequence_on_terminal_maps_of_scalar_deriv_nonneg_above
    X P U hU hcover hpU D S hS hslab hreg hterminal N hq hscale hPhi hpinch ?_ hsource hmetric
  intro n K hK
  filter_upwards [hneck n K hK, hneckRegular n K hK] with j hj hjreg
  intro x hx t ht hhigh
  obtain ⟨eps, ⟨nk⟩⟩ := hj x hx t ht hhigh
  exact (nk.scalar_derivWithin_pos (hS n j) (hjreg x hx t ht hhigh)).le

private theorem metricScalarAt_le_max_terminal_of_supplied_ancient_limits
    (X : FlowSequence.{u}) (P : MetricCompactLimit (X.atTime 0))
    (U : ℕ → TopologicalSpace.Opens P.limit.M) (hU : Monotone U)
    (hcover : ∀ x : P.limit.M, ∃ n, x ∈ U n)
    (D : ℕ → RealTimeInterval)
    (S : ∀ n : ℕ, ℕ → SolutionOn (I := I3) (M := U n) (D n))
    (hS : ∀ n i, IsSolutionOn (S n i))
    (hslab : ∀ n, Icc (-(2 * ((n + 1 : ℕ) : ℝ))) 0 ⊆ (D n).carrier)
    (N rho : ℕ → ℕ) (hrho : StrictMono rho)
    (G : ℝ → SmoothRiemannianMetric I3 P.limit.M) (hG0 : G 0 = P.limit.metric)
    (hconv : ∀ n, ∀ K : Set (U n), IsCompact K → ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc (-((n + 1 : ℕ) : ℝ)) 0,
        metricDerivNormSupOn K p ((S n (rho i - N n)).base.metric t)
          ((G t).restrictOpen (U n)) (P.limit.metric.restrictOpen (U n)) < epsilon)
    {q : ℕ → ℝ} {q0 : ℝ} (hq : ∀ᶠ i in atTop, q i ≤ q0)
    (hsign : ∀ n, ∀ K : Set (U n), IsCompact K → ∀ᶠ j in atTop,
      ∀ x ∈ K, ∀ t ∈ Ioo (-(2 * ((n + 1 : ℕ) : ℝ))) 0,
        q (j + N n) < (S n j).scalar t x →
          0 ≤ derivWithin (fun r => (S n j).scalar r x) (Iic t) t) :
    ∀ t ≤ 0, ∀ x : P.limit.M,
      metricScalarAt (G t) x ≤ max q0 (metricScalarAt P.limit.metric x) := by
  intro t ht x
  obtain ⟨k,hxk⟩ := hcover x
  obtain ⟨l,hl⟩ := exists_nat_ge (-t)
  let n := max k l
  have hxn : x ∈ U n := hU (le_max_left k l) hxk
  have htn : t ∈ Icc (-((n + 1 : ℕ) : ℝ)) 0 := by
    refine ⟨?_,ht⟩
    have hh : (l : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr (le_max_right k l)
    rw [Nat.cast_add,Nat.cast_one]
    linarith
  let _ : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I3 (U n).isOpen)
  let y : U n := ⟨x,hxn⟩
  let j : ℕ → ℕ := fun i => rho i - N n
  have hj : Tendsto j atTop atTop := (tendsto_sub_atTop_nat (N n)).comp hrho.tendsto_atTop
  have hshort : Icc (-((n + 1 : ℕ) : ℝ)) 0 ⊆ (D n).carrier := by
    intro s hs
    apply hslab n
    constructor <;> linarith [hs.1,hs.2,Nat.cast_nonneg (α := ℝ) (n + 1)]
  have hslope : ∀ᶠ i in atTop, ∀ s ∈ Ioo (-((n + 1 : ℕ) : ℝ)) 0,
      q (j i + N n) < (S n (j i)).scalar s y →
        0 ≤ deriv (fun r => (S n (j i)).scalar r y) s := by
    filter_upwards [hj.eventually (hsign n {y} isCompact_singleton)] with i hi
    intro s hs hhigh
    have hlong : s ∈ Ioo (-(2 * ((n + 1 : ℕ) : ℝ))) 0 := by
      constructor <;> linarith [hs.1,hs.2,Nat.cast_nonneg (α := ℝ) (n + 1)]
    have hd := ((hS n (j i)).scalarTime hs (Ioo_subset_Icc_self.trans hshort) y).differentiableAt
      (Ioo_mem_nhds hs.1 hs.2)
    simpa only [hd.derivWithin (uniqueDiffWithinAt_Iic s)] using
      hi y (mem_singleton y) s hlong hhigh
  have hcp (s : ℝ) (hs : s ∈ Icc (-((n + 1 : ℕ) : ℝ)) 0) :
      MetricCPConvergenceOn {y} 2 (fun i => (S n (j i)).base.metric s)
        ((G s).restrictOpen (U n)) (P.limit.metric.restrictOpen (U n)) := by
    intro epsilon hepsilon
    obtain ⟨i0,hi0⟩ := hconv n {y} isCompact_singleton 2 epsilon hepsilon
    exact ⟨i0,fun i hi => hi0 i hi s hs⟩
  have hh := metricScalarAt_le_max_terminal_of_deriv_nonneg_above (fun i => S n (j i))
    ((G t).restrictOpen (U n)) ((G 0).restrictOpen (U n))
    (P.limit.metric.restrictOpen (U n)) (P.limit.metric.restrictOpen (U n)) y htn
    (fun i => q (j i + N n)) (Eventually.of_forall fun i => hS n (j i))
    (Eventually.of_forall fun _ => hshort)
    (((tendsto_add_atTop_nat (N n)).comp hj).eventually hq) hslope
    (hcp t htn) (hcp 0 ⟨neg_nonpos.mpr (Nat.cast_nonneg _),le_rfl⟩)
  simpa only [metricScalarAt_restrictOpen, hG0] using hh

private theorem curvatureOperator_nonnegative_of_supplied_ancient_limits
    (X : FlowSequence.{u}) (P : MetricCompactLimit (X.atTime 0))
    (U : ℕ → TopologicalSpace.Opens P.limit.M) (hU : Monotone U)
    (hcover : ∀ x : P.limit.M, ∃ n, x ∈ U n)
    (D : ℕ → RealTimeInterval)
    (S : ∀ n : ℕ, ℕ → SolutionOn (I := I3) (M := U n) (D n))
    (N rho : ℕ → ℕ) (hrho : StrictMono rho)
    (G : ℝ → SmoothRiemannianMetric I3 P.limit.M)
    (hconv : ∀ n, ∀ K : Set (U n), IsCompact K → ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc (-((n + 1 : ℕ) : ℝ)) 0,
        metricDerivNormSupOn K p ((S n (rho i - N n)).base.metric t)
          ((G t).restrictOpen (U n)) (P.limit.metric.restrictOpen (U n)) < epsilon)
    {scale : ℕ → ℝ} (hscale : Tendsto scale atTop atTop)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : ∀ n, ∀ᶠ j in atTop, PhiAlmostNonnegative (S n j)
      (Icc (-(2 * ((n + 1 : ℕ) : ℝ))) 0)
      (rescalePinchingFunction (scale (j + N n)) Phi)) :
    ∀ t ≤ 0, ∀ x : P.limit.M, metricAlgebraicCurvatureTensorAt (G t) x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I3) := by
  intro t ht x
  obtain ⟨k, hxk⟩ := hcover x
  obtain ⟨l, hl⟩ := exists_nat_ge (-t)
  let n := max k l
  have hxn : x ∈ U n := hU (le_max_left k l) hxk
  have htn : t ∈ Icc (-((n + 1 : ℕ) : ℝ)) 0 := by
    refine ⟨?_, ht⟩
    have hh : (l : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr (le_max_right k l)
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  have htlong : t ∈ Icc (-(2 * ((n + 1 : ℕ) : ℝ))) 0 :=
    ⟨by linarith [htn.1,Nat.cast_nonneg (α := ℝ) (n + 1)], ht⟩
  let _ : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I3 (U n).isOpen)
  let j : ℕ → ℕ := fun i => rho i - N n
  have hj : Tendsto j atTop atTop := (tendsto_sub_atTop_nat (N n)).comp hrho.tendsto_atTop
  let Q : ℕ → ℝ := fun i => scale (j i + N n)
  have hQ : Tendsto Q atTop atTop := hscale.comp ((tendsto_add_atTop_nat (N n)).comp hj)
  obtain ⟨i0, hi0⟩ := eventually_atTop.mp (hQ.eventually (eventually_gt_atTop (0 : ℝ)))
  have hQshift : Tendsto (fun i => Q (i + i0)) atTop atTop := hQ.comp (tendsto_add_atTop_nat i0)
  have hconvU : MetricCInfConvergenceOnCompacts
      (fun i => (S n (j (i + i0))).base.metric t)
      ((G t).restrictOpen (U n)) (P.limit.metric.restrictOpen (U n)) := by
    intro K hK p epsilon hepsilon
    obtain ⟨i1, hi1⟩ := hconv n K hK p epsilon hepsilon
    exact ⟨i1, fun i hi => hi1 (i + i0) (by omega) t htn⟩
  have hpinchU : ∀ᶠ i in atTop, ∀ y : U n,
      curvatureOperatorLowerBoundAt ((S n (j (i + i0))).base.metric t) y
        (metricAlgebraicCurvatureTensorAt ((S n (j (i + i0))).base.metric t) y)
        (rescalePinchingFunction (Q (i + i0)) Phi
          (metricScalarAt ((S n (j (i + i0))).base.metric t) y)) := by
    filter_upwards [((hj.comp (tendsto_add_atTop_nat i0)).eventually (hpinch n))] with i hi
    exact hi t htlong
  have hnonneg := curvatureOperator_nonnegative_of_metricCInf_admissible_pinching
    (fun i => (S n (j (i + i0))).base.metric t) ((G t).restrictOpen (U n))
    (P.limit.metric.restrictOpen (U n)) hconvU hPhi (fun i => Q (i + i0))
    (fun i => hi0 (i + i0) (by omega)) hQshift hpinchU ⟨x,hxn⟩
  exact (metricAlgebraicCurvatureTensorAt_restrictOpen_mem_curvatureOperatorNonnegativeCone_iff
    (G t) (U n) ⟨x,hxn⟩).mp hnonneg

theorem exists_complete_nonnegative_ancient_limit_of_scalar_deriv_nonneg_above
    (X : FlowSequence.{u}) (P : MetricCompactLimit (X.atTime 0))
    (U : ℕ → TopologicalSpace.Opens P.limit.M) (hU : Monotone U)
    (hcover : ∀ x : P.limit.M, ∃ n, x ∈ U n)
    (hpU : ∀ n, P.limit.basepoint ∈ U n)
    (D : ℕ → RealTimeInterval)
    (S : ∀ n : ℕ, ℕ → SolutionOn (I := I3) (M := U n) (D n))
    (hS : ∀ n i, IsSolutionOn (S n i))
    (hslab : ∀ n, Icc (-(2 * ((n + 1 : ℕ) : ℝ))) 0 ⊆ (D n).carrier)
    (hreg : ∀ n, Ioo (-(2 * ((n + 1 : ℕ) : ℝ))) 0 ⊆ (D n).regular)
    (hterminal : ∀ n, MetricCInfConvergenceOnCompacts
      (fun i => (S n i).base.metric 0)
      (P.limit.metric.restrictOpen (U n)) (P.limit.metric.restrictOpen (U n)))
    (N : ℕ → ℕ) {q scale : ℕ → ℝ} {q0 : ℕ → ℝ}
    (hq : ∀ n, ∀ᶠ i in atTop, q i ≤ q0 n)
    (hscale : Tendsto scale atTop atTop)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : ∀ n, ∀ᶠ j in atTop, PhiAlmostNonnegative (S n j)
      (Icc (-(2 * ((n + 1 : ℕ) : ℝ))) 0)
      (rescalePinchingFunction (scale (j + N n)) Phi))
    (hsign : ∀ n, ∀ K : Set (U n), IsCompact K → ∀ᶠ j in atTop,
      ∀ x ∈ K, ∀ t ∈ Ioo (-(2 * ((n + 1 : ℕ) : ℝ))) 0,
        q (j + N n) < (S n j).scalar t x →
          0 ≤ derivWithin (fun r => (S n j).scalar r x) (Iic t) t)
    (hsource : ∀ n i, (U n : Set P.limit.M) ⊆
      (P.maps.partialDiffeomorph (i + N n)).source)
    (hmetric : ∀ n j t (x : U n) (v w : TangentSpace I3 x),
      t ∈ Icc (-(2 * ((n + 1 : ℕ) : ℝ))) 0 →
      (x : P.limit.M) ∈ (P.maps.partialDiffeomorph (j + N n)).source →
      ((S n j).base.metric t).inner x v w =
        ((X.term (P.subseq (j + N n))).S.base.metric t).inner
          (P.maps.partialDiffeomorph (j + N n) x)
          (mfderiv I3 I3 (P.maps.partialDiffeomorph (j + N n)) x v)
          (mfderiv I3 I3 (P.maps.partialDiffeomorph (j + N n)) x w)) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∃ G : ℝ → SmoothRiemannianMetric I3 P.limit.M,
      G 0 = P.limit.metric ∧
      IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := P.limit.M)
        (RealTimeInterval.infiniteClosed 0 0 le_rfl)) ∧
      (∀ t ≤ 0, ∀ x : P.limit.M, metricAlgebraicCurvatureTensorAt (G t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I3)) ∧
      (∀ t ≤ 0, RiemannianMetricComplete (G t)) ∧
      ∀ n, ∀ K : Set (U n), IsCompact K → ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
        ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc (-((n + 1 : ℕ) : ℝ)) 0,
          metricDerivNormSupOn K p ((S n (rho i - N n)).base.metric t)
            ((G t).restrictOpen (U n)) (P.limit.metric.restrictOpen (U n)) < epsilon := by
  obtain ⟨rho, hrho, G, hG0, hGsol, hconv⟩ :=
    exists_ancient_solution_subsequence_on_terminal_maps_of_scalar_deriv_nonneg_above
      X P U hU hcover hpU D S hS hslab hreg hterminal N hq hscale hPhi hpinch
      hsign hsource hmetric
  have hcone := curvatureOperator_nonnegative_of_supplied_ancient_limits
    X P U hU hcover D S N rho hrho G hconv hscale hPhi hpinch
  refine ⟨rho,hrho,G,hG0,hGsol,hcone,?_,hconv⟩
  intro t ht
  apply complete_at_earlier_time_of_ricci_nonnegative
    ({ base.metric := G } : SolutionOn (I := I3) (M := P.limit.M)
      (RealTimeInterval.infiniteClosed 0 0 le_rfl)) hGsol
    (a := t) (b := 0) (fun _ hs => hs.2) (fun _ hs => hs.2)
  · intro r hr x v
    exact metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
      (G r) x (hcone r hr.2.le x) v
  · change RiemannianMetricComplete (G 0)
    rw [hG0]
    exact ⟨P.limit_complete.complete⟩
  · exact ⟨le_rfl,ht⟩

theorem
  exists_complete_nonnegative_ancient_solution_subsequence_on_terminal_maps_of_strongNeck_above
    (X : FlowSequence.{u}) (P : MetricCompactLimit (X.atTime 0))
    (U : ℕ → TopologicalSpace.Opens P.limit.M) (hU : Monotone U)
    (hcover : ∀ x : P.limit.M, ∃ n, x ∈ U n)
    (hpU : ∀ n, P.limit.basepoint ∈ U n)
    (D : ℕ → RealTimeInterval)
    (S : ∀ n : ℕ, ℕ → SolutionOn (I := I3) (M := U n) (D n))
    (hS : ∀ n i, IsSolutionOn (S n i))
    (hslab : ∀ n, Icc (-(2 * ((n + 1 : ℕ) : ℝ))) 0 ⊆ (D n).carrier)
    (hreg : ∀ n, Ioo (-(2 * ((n + 1 : ℕ) : ℝ))) 0 ⊆ (D n).regular)
    (hterminal : ∀ n, MetricCInfConvergenceOnCompacts
      (fun i => (S n i).base.metric 0)
      (P.limit.metric.restrictOpen (U n)) (P.limit.metric.restrictOpen (U n)))
    (N : ℕ → ℕ) {q scale : ℕ → ℝ} {q0 : ℕ → ℝ}
    (hq : ∀ n, ∀ᶠ i in atTop, q i ≤ q0 n)
    (hscale : Tendsto scale atTop atTop)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : ∀ n, ∀ᶠ j in atTop, PhiAlmostNonnegative (S n j)
      (Icc (-(2 * ((n + 1 : ℕ) : ℝ))) 0)
      (rescalePinchingFunction (scale (j + N n)) Phi))
    (hneck : ∀ n, ∀ K : Set (U n), IsCompact K → ∀ᶠ j in atTop,
      ∀ x ∈ K, ∀ t ∈ Ioo (-(2 * ((n + 1 : ℕ) : ℝ))) 0,
        q (j + N n) < (S n j).scalar t x →
          ∃ eps : ℝ, Nonempty (StrongNeck (S n j) eps x t))
    (hneckRegular : ∀ n, ∀ K : Set (U n), IsCompact K → ∀ᶠ j in atTop,
      ∀ x ∈ K, ∀ t ∈ Ioo (-(2 * ((n + 1 : ℕ) : ℝ))) 0,
        q (j + N n) < (S n j).scalar t x → ∀ s ∈ Ioo (-1 : ℝ) 0,
          parabolicTime t ((S n j).scalar t x) s ∈ (D n).regular)
    (hsource : ∀ n i, (U n : Set P.limit.M) ⊆
      (P.maps.partialDiffeomorph (i + N n)).source)
    (hmetric : ∀ n j t (x : U n) (v w : TangentSpace I3 x),
      t ∈ Icc (-(2 * ((n + 1 : ℕ) : ℝ))) 0 →
      (x : P.limit.M) ∈ (P.maps.partialDiffeomorph (j + N n)).source →
      ((S n j).base.metric t).inner x v w =
        ((X.term (P.subseq (j + N n))).S.base.metric t).inner
          (P.maps.partialDiffeomorph (j + N n) x)
          (mfderiv I3 I3 (P.maps.partialDiffeomorph (j + N n)) x v)
          (mfderiv I3 I3 (P.maps.partialDiffeomorph (j + N n)) x w)) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∃ G : ℝ → SmoothRiemannianMetric I3 P.limit.M,
      G 0 = P.limit.metric ∧
      IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := P.limit.M)
        (RealTimeInterval.infiniteClosed 0 0 le_rfl)) ∧
      (∀ t ≤ 0, ∀ x : P.limit.M, metricAlgebraicCurvatureTensorAt (G t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I3)) ∧
      (∀ t ≤ 0, RiemannianMetricComplete (G t)) ∧
      ∀ n, ∀ K : Set (U n), IsCompact K → ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
        ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc (-((n + 1 : ℕ) : ℝ)) 0,
          metricDerivNormSupOn K p ((S n (rho i - N n)).base.metric t)
            ((G t).restrictOpen (U n)) (P.limit.metric.restrictOpen (U n)) < epsilon := by
  let _ (n : ℕ) : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I3 (U n).isOpen)
  apply exists_complete_nonnegative_ancient_limit_of_scalar_deriv_nonneg_above
    X P U hU hcover hpU D S hS hslab hreg hterminal N hq hscale hPhi hpinch ?_ hsource hmetric
  intro n K hK
  filter_upwards [hneck n K hK, hneckRegular n K hK] with j hj hjreg
  intro x hx t ht hhigh
  obtain ⟨eps, ⟨nk⟩⟩ := hj x hx t ht hhigh
  exact (nk.scalar_derivWithin_pos (hS n j) (hjreg x hx t ht hhigh)).le

theorem exists_complete_nonnegative_bounded_ancient_limit_of_scalar_deriv_nonneg_above
    (X : FlowSequence.{u}) (P : MetricCompactLimit (X.atTime 0))
    (U : ℕ → TopologicalSpace.Opens P.limit.M) (hU : Monotone U)
    (hcover : ∀ x : P.limit.M, ∃ n, x ∈ U n)
    (hpU : ∀ n, P.limit.basepoint ∈ U n)
    (D : ℕ → RealTimeInterval)
    (S : ∀ n : ℕ, ℕ → SolutionOn (I := I3) (M := U n) (D n))
    (hS : ∀ n i, IsSolutionOn (S n i))
    (hslab : ∀ n, Icc (-(2 * ((n + 1 : ℕ) : ℝ))) 0 ⊆ (D n).carrier)
    (hreg : ∀ n, Ioo (-(2 * ((n + 1 : ℕ) : ℝ))) 0 ⊆ (D n).regular)
    (hterminal : ∀ n, MetricCInfConvergenceOnCompacts
      (fun i => (S n i).base.metric 0)
      (P.limit.metric.restrictOpen (U n)) (P.limit.metric.restrictOpen (U n)))
    (N : ℕ → ℕ) {q scale : ℕ → ℝ} {q0 B : ℝ}
    (hq : ∀ᶠ i in atTop, q i ≤ q0)
    (hterminalBound : ∀ x : P.limit.M, metricScalarAt P.limit.metric x ≤ B)
    (hscale : Tendsto scale atTop atTop)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : ∀ n, ∀ᶠ j in atTop, PhiAlmostNonnegative (S n j)
      (Icc (-(2 * ((n + 1 : ℕ) : ℝ))) 0)
      (rescalePinchingFunction (scale (j + N n)) Phi))
    (hsign : ∀ n, ∀ K : Set (U n), IsCompact K → ∀ᶠ j in atTop,
      ∀ x ∈ K, ∀ t ∈ Ioo (-(2 * ((n + 1 : ℕ) : ℝ))) 0,
        q (j + N n) < (S n j).scalar t x →
          0 ≤ derivWithin (fun r => (S n j).scalar r x) (Iic t) t)
    (hsource : ∀ n i, (U n : Set P.limit.M) ⊆
      (P.maps.partialDiffeomorph (i + N n)).source)
    (hmetric : ∀ n j t (x : U n) (v w : TangentSpace I3 x),
      t ∈ Icc (-(2 * ((n + 1 : ℕ) : ℝ))) 0 →
      (x : P.limit.M) ∈ (P.maps.partialDiffeomorph (j + N n)).source →
      ((S n j).base.metric t).inner x v w =
        ((X.term (P.subseq (j + N n))).S.base.metric t).inner
          (P.maps.partialDiffeomorph (j + N n) x)
          (mfderiv I3 I3 (P.maps.partialDiffeomorph (j + N n)) x v)
          (mfderiv I3 I3 (P.maps.partialDiffeomorph (j + N n)) x w)) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∃ G : ℝ → SmoothRiemannianMetric I3 P.limit.M,
      G 0 = P.limit.metric ∧
      IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := P.limit.M)
        (RealTimeInterval.infiniteClosed 0 0 le_rfl)) ∧
      (∀ t ≤ 0, ∀ x : P.limit.M, metricAlgebraicCurvatureTensorAt (G t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I3)) ∧
      (∀ t ≤ 0, RiemannianMetricComplete (G t)) ∧
      (∀ t ≤ 0, ∀ x : P.limit.M,
        Real.sqrt (Tensor0SBundle.normSq0S (G t) x 4 (metricRm04At (G t) x)) ≤
          Real.sqrt 3 * max q0 B) ∧
      ∀ n, ∀ K : Set (U n), IsCompact K → ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
        ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc (-((n + 1 : ℕ) : ℝ)) 0,
          metricDerivNormSupOn K p ((S n (rho i - N n)).base.metric t)
            ((G t).restrictOpen (U n)) (P.limit.metric.restrictOpen (U n)) < epsilon := by
  let _ (n : ℕ) : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I3 (U n).isOpen)
  obtain ⟨rho,hrho,G,hG0,hGsol,hcone,hcomplete,hconv⟩ :=
    exists_complete_nonnegative_ancient_limit_of_scalar_deriv_nonneg_above
      X P U hU hcover hpU D S hS hslab hreg hterminal N (q0 := fun _ => q0)
      (fun _ => hq) hscale hPhi hpinch hsign hsource hmetric
  have hscalar := metricScalarAt_le_max_terminal_of_supplied_ancient_limits
    X P U hU hcover D S hS hslab N rho hrho G hG0 hconv hq hsign
  refine ⟨rho,hrho,G,hG0,hGsol,hcone,hcomplete,?_,hconv⟩
  intro t ht x
  let L : SolutionOn (I := I3) (M := P.limit.M)
      (RealTimeInterval.infiniteClosed 0 0 le_rfl) := {base.metric := G}
  have hn : curvatureOperatorLowerBoundAt (G t) x (metricAlgebraicCurvatureTensorAt (G t) x) 0 := by
    simpa only [curvatureOperatorLowerBoundAt, zero_mul, add_zero] using
      (mem_algebraicCurvatureOperatorNonnegativeCone.mp (hcone t ht x))
  have hrm :=
    CanonicalNeighborhood.sqrt_rmNormSq_le_sqrt_three_mul_scalar_of_curvatureOperatorNonneg
      L (by simp [ThreeSpace]) t x hn
  apply hrm.trans
  exact mul_le_mul_of_nonneg_left ((hscalar t ht x).trans
    (max_le_max le_rfl (hterminalBound x))) (Real.sqrt_nonneg 3)

theorem exists_complete_nonnegative_bounded_ancient_limit_of_strongNeck_above
    (X : FlowSequence.{u}) (P : MetricCompactLimit (X.atTime 0))
    (U : ℕ → TopologicalSpace.Opens P.limit.M) (hU : Monotone U)
    (hcover : ∀ x : P.limit.M, ∃ n, x ∈ U n)
    (hpU : ∀ n, P.limit.basepoint ∈ U n)
    (D : ℕ → RealTimeInterval)
    (S : ∀ n : ℕ, ℕ → SolutionOn (I := I3) (M := U n) (D n))
    (hS : ∀ n i, IsSolutionOn (S n i))
    (hslab : ∀ n, Icc (-(2 * ((n + 1 : ℕ) : ℝ))) 0 ⊆ (D n).carrier)
    (hreg : ∀ n, Ioo (-(2 * ((n + 1 : ℕ) : ℝ))) 0 ⊆ (D n).regular)
    (hterminal : ∀ n, MetricCInfConvergenceOnCompacts
      (fun i => (S n i).base.metric 0)
      (P.limit.metric.restrictOpen (U n)) (P.limit.metric.restrictOpen (U n)))
    (N : ℕ → ℕ) {q scale : ℕ → ℝ} {q0 B : ℝ}
    (hq : ∀ᶠ i in atTop, q i ≤ q0)
    (hterminalBound : ∀ x : P.limit.M, metricScalarAt P.limit.metric x ≤ B)
    (hscale : Tendsto scale atTop atTop)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : ∀ n, ∀ᶠ j in atTop, PhiAlmostNonnegative (S n j)
      (Icc (-(2 * ((n + 1 : ℕ) : ℝ))) 0)
      (rescalePinchingFunction (scale (j + N n)) Phi))
    (hneck : ∀ n, ∀ K : Set (U n), IsCompact K → ∀ᶠ j in atTop,
      ∀ x ∈ K, ∀ t ∈ Ioo (-(2 * ((n + 1 : ℕ) : ℝ))) 0,
        q (j + N n) < (S n j).scalar t x →
          ∃ eps : ℝ, Nonempty (StrongNeck (S n j) eps x t))
    (hneckRegular : ∀ n, ∀ K : Set (U n), IsCompact K → ∀ᶠ j in atTop,
      ∀ x ∈ K, ∀ t ∈ Ioo (-(2 * ((n + 1 : ℕ) : ℝ))) 0,
        q (j + N n) < (S n j).scalar t x → ∀ s ∈ Ioo (-1 : ℝ) 0,
          parabolicTime t ((S n j).scalar t x) s ∈ (D n).regular)
    (hsource : ∀ n i, (U n : Set P.limit.M) ⊆
      (P.maps.partialDiffeomorph (i + N n)).source)
    (hmetric : ∀ n j t (x : U n) (v w : TangentSpace I3 x),
      t ∈ Icc (-(2 * ((n + 1 : ℕ) : ℝ))) 0 →
      (x : P.limit.M) ∈ (P.maps.partialDiffeomorph (j + N n)).source →
      ((S n j).base.metric t).inner x v w =
        ((X.term (P.subseq (j + N n))).S.base.metric t).inner
          (P.maps.partialDiffeomorph (j + N n) x)
          (mfderiv I3 I3 (P.maps.partialDiffeomorph (j + N n)) x v)
          (mfderiv I3 I3 (P.maps.partialDiffeomorph (j + N n)) x w)) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∃ G : ℝ → SmoothRiemannianMetric I3 P.limit.M,
      G 0 = P.limit.metric ∧
      IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := P.limit.M)
        (RealTimeInterval.infiniteClosed 0 0 le_rfl)) ∧
      (∀ t ≤ 0, ∀ x : P.limit.M, metricAlgebraicCurvatureTensorAt (G t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I3)) ∧
      (∀ t ≤ 0, RiemannianMetricComplete (G t)) ∧
      (∀ t ≤ 0, ∀ x : P.limit.M,
        Real.sqrt (Tensor0SBundle.normSq0S (G t) x 4 (metricRm04At (G t) x)) ≤
          Real.sqrt 3 * max q0 B) ∧
      ∀ n, ∀ K : Set (U n), IsCompact K → ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
        ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc (-((n + 1 : ℕ) : ℝ)) 0,
          metricDerivNormSupOn K p ((S n (rho i - N n)).base.metric t)
            ((G t).restrictOpen (U n)) (P.limit.metric.restrictOpen (U n)) < epsilon := by
  let _ (n : ℕ) : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I3 (U n).isOpen)
  apply exists_complete_nonnegative_bounded_ancient_limit_of_scalar_deriv_nonneg_above
    X P U hU hcover hpU D S hS hslab hreg hterminal N hq hterminalBound hscale hPhi hpinch
    ?_ hsource hmetric
  intro n K hK
  filter_upwards [hneck n K hK,hneckRegular n K hK] with j hj hjreg
  intro x hx t ht hhigh
  obtain ⟨eps,⟨nk⟩⟩ := hj x hx t ht hhigh
  exact (nk.scalar_derivWithin_pos (hS n j) (hjreg x hx t ht hhigh)).le

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
