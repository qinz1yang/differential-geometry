import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelCurvaturePropagation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalSliceScalarTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BackwardTimeConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalLocalBackwardFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.OpenPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalCommonExtraction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.OpenCover
import DifferentialGeometry.Geometry.Metric.Distance.Finiteness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactTimeComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonRestriction
import DifferentialGeometry.Geometry.Curvature.ScalarControlsRm
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Nonnegative
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_eventually_curvature_bound_of_scalar_le {kappa : ℝ}
    (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, 0 < sigma → ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
        ∀ A : ℝ, ∃ radius delta C : ℝ, 0 < radius ∧ 0 < delta ∧ 0 < C ∧
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ᶠ i in atTop,
            ∀ s ∈ Icc (-(X.depth i / 2)) 0, ∀ z : (X.term i).M,
              (X.term i).S.scalar s z ≤ A →
              Icc (s - delta) s ⊆ (X.interval i).carrier ∧
              ∀ t ∈ Icc (s - delta) s,
                ∀ y ∈ riemannianClosedBallOf (I := I3) ((X.term i).S.base.metric s) z radius,
                  curvDerivNormSq (I := I3) 0 ((X.term i).S.base.metric t) y ≤ C := by
  obtain ⟨epsStar, c, C, hepsStar, hc, hC, hprop⟩ := local_propagation_of_modelBound hmod
  refine ⟨epsStar, hepsStar, fun eps heps hle sigma hsigma Phi hPhi A => ?_⟩
  let B : ℝ := 1 + max A (6 * Phi 0)
  have hPhi0 : 0 < Phi 0 := hPhi.pos 0
  have hB : 0 < B := by
    dsimp [B]
    linarith [le_max_right A (6 * Phi 0)]
  refine ⟨c / Real.sqrt B, c / B, (C * (B + 1)) ^ 2,
    div_pos hc (Real.sqrt_pos.mpr hB), div_pos hc hB, by positivity, fun X => ?_⟩
  filter_upwards [hprop eps heps hle sigma hsigma Phi hPhi X,
    X.scale_tendsto.eventually (eventually_ge_atTop (1 : ℝ)),
    X.pinching_error_eventually hPhi (L0 := B) (eta := 1) one_pos]
    with i hcyl hscale hpinch
  intro s hs z hz
  have htime : s ∈ (X.interval i).carrier := by
    rw [X.carrier_eq i]
    exact ⟨by linarith [X.depth_pos i, hs.1], hs.2⟩
  have hlow : -6 * Phi 0 ≤ (X.term i).S.scalar s z := by
    have h := neg_six_mul_phi_zero_le_scalar (hPhi.rescale (X.scale_pos i))
      (X.pinching i) (by simp [ThreeSpace]) htime z
    have hres : rescalePinchingFunction (X.scale i) Phi 0 = (X.scale i)⁻¹ * Phi 0 := by
      simp only [rescalePinchingFunction, mul_zero]
    rw [hres] at h
    have hinv : (X.scale i)⁻¹ * Phi 0 ≤ Phi 0 := by
      have h1 : (X.scale i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hscale
      nlinarith
    linarith
  let L : ℝ := 1 + |(X.term i).S.scalar s z|
  have hL1 : 1 ≤ L := by
    dsimp [L]
    linarith [abs_nonneg ((X.term i).S.scalar s z)]
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have hLB : L ≤ B := by
    have habs : |(X.term i).S.scalar s z| ≤ max A (6 * Phi 0) :=
      abs_le.mpr ⟨by linarith [le_max_right A (6 * Phi 0)],
        hz.trans (le_max_left A (6 * Phi 0))⟩
    dsimp [L, B]
    linarith
  have hdelta : c / B ≤ c / L := div_le_div_of_nonneg_left hc.le hL hLB
  have hradius : c / Real.sqrt B ≤ c / Real.sqrt L :=
    div_le_div_of_nonneg_left hc.le (Real.sqrt_pos.mpr hL) (Real.sqrt_le_sqrt hLB)
  obtain ⟨hcarrier, hcurv⟩ := hcyl s hs z
  have hsub : Icc (s - c / B) s ⊆ Icc (s - c / L) s :=
    Icc_subset_Icc (by linarith) le_rfl
  refine ⟨hsub.trans hcarrier, fun t ht y hy => ?_⟩
  have hmem : (y, t) ∈ frozenBackwardCylinder (X.term i).S z s c c L := by
    refine ⟨?_, hsub ht⟩
    exact hy.trans (ENNReal.ofReal_le_ofReal hradius)
  have herror : (Phi (4 * X.scale i * L) + Phi 0) / X.scale i < 1 :=
    hpinch L ⟨hL1, hLB⟩
  have hbound := (hcurv y t hmem).2.2
  have hrm : Real.sqrt (FlowMetricBall.rmNormSq (X.term i).S t y) ≤ C * (B + 1) := by
    refine hbound.trans ?_
    apply mul_le_mul_of_nonneg_left _ hC.le
    change L + (Phi (4 * X.scale i * L) + Phi 0) / X.scale i ≤ B + 1
    linarith
  exact (Real.sqrt_le_iff.mp hrm).2

theorem exists_source_curvature_bound_before_time_of_scalar_le
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa)
    (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
        ∀ A : ℝ, ∃ radius delta C : ℝ, 0 < radius ∧ 0 < delta ∧ 0 < C ∧
          ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
            (J : RealTimeInterval) (B : BackwardExtension L J) (s : ℝ), s ∈ J.carrier →
            (∀ x : L.space.M, B.solution.scalar s x ≤ A) →
            ∀ K : Set L.space.M, IsCompact K → ∀ᶠ i in atTop,
              K ⊆ (L.maps.partialDiffeomorph (B.subseq i)).source ∧
              Icc (s - delta) s ⊆ (X.interval (L.subseq (B.subseq i))).carrier ∧
              Ioo (s - delta) s ⊆ (X.interval (L.subseq (B.subseq i))).regular ∧
              ∀ t ∈ Icc (s - delta) s, ∀ x ∈ K,
                ∀ y ∈ riemannianClosedBallOf (I := I3)
                  ((X.term (L.subseq (B.subseq i))).S.base.metric s)
                  (L.maps.partialDiffeomorph (B.subseq i) x) radius,
                  curvDerivNormSq (I := I3) 0
                    ((X.term (L.subseq (B.subseq i))).S.base.metric t) y ≤ C := by
  obtain ⟨epsStar, hepsStar, hprop⟩ := exists_eventually_curvature_bound_of_scalar_le hmod
  obtain ⟨epsTransfer, hepsTransfer, htransfer⟩ :=
    terminal_slice_scalar_transfer (kappa := kappa) (sigma := sigma) (Phi := Phi)
  refine ⟨min epsStar epsTransfer, lt_min hepsStar hepsTransfer, ?_⟩
  intro eps heps hle A
  obtain ⟨radius, delta, C, hradius, hdelta, hC, hcurv⟩ :=
    hprop eps heps (hle.trans (min_le_left _ _)) sigma hsigma Phi hPhi (A + 1)
  refine ⟨radius, delta, C, hradius, hdelta, hC, ?_⟩
  intro X L J B s hs hscalar
  have hf := L.strictMono.comp B.strictMono
  have hwindow := eventually_mem_backwardWindow B hs
  have hs0 : s ≤ 0 := by
    obtain ⟨i, hi⟩ := hwindow.exists
    exact hi.2
  intro K hK
  have hcomp := B.convergence K hK s s le_rfl
    (by simpa only [Icc_self, singleton_subset_iff] using hs) 0 1 one_pos
  obtain ⟨eta, heta0, heta1, hscalarTransfer⟩ :=
    htransfer eps heps (hle.trans (min_le_right _ _))
  filter_upwards [hscalarTransfer X L J B s hs K hK,
    hf.tendsto_atTop.eventually (hcurv X), hwindow,
    (X.depth_tendsto.comp hf.tendsto_atTop).eventually_ge_atTop (delta - s + 1), hcomp]
    with i htr hci hwi hdi hco
  have hdi' : delta - s + 1 ≤ X.depth (L.subseq (B.subseq i)) := hdi
  refine ⟨hco.2.1, ?_, ?_, fun t ht x hx y hy => ?_⟩
  · intro t ht
    rw [X.carrier_eq]
    exact ⟨by linarith [ht.1, X.depth_pos (L.subseq (B.subseq i))], ht.2.trans hs0⟩
  · intro t ht
    rw [X.regular_eq]
    exact ⟨by linarith [ht.1, X.depth_pos (L.subseq (B.subseq i))], ht.2.trans_le hs0⟩
  · have hsource : (X.term (L.subseq (B.subseq i))).S.scalar s
        (L.maps.partialDiffeomorph (B.subseq i) x) ≤ A + 1 := by
      have he := (abs_le.mp (htr x hx)).1
      have hh := hscalar x
      linarith
    exact (hci s hwi (L.maps.partialDiffeomorph (B.subseq i) x) hsource).2 t ht y hy



theorem exists_source_curvature_bound_before_time_of_model_curvature_bound
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa)
    (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
        ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
          (J : RealTimeInterval) (B : BackwardExtension L J) (s : ℝ), s ∈ J.carrier →
          ∃ radius delta C : ℝ, 0 < radius ∧ 0 < delta ∧ 0 < C ∧
            ∀ K : Set L.space.M, IsCompact K → ∀ᶠ i in atTop,
              K ⊆ (L.maps.partialDiffeomorph (B.subseq i)).source ∧
              Icc (s - delta) s ⊆ (X.interval (L.subseq (B.subseq i))).carrier ∧
              Ioo (s - delta) s ⊆ (X.interval (L.subseq (B.subseq i))).regular ∧
              ∀ t ∈ Icc (s - delta) s, ∀ x ∈ K,
                ∀ y ∈ riemannianClosedBallOf (I := I3)
                  ((X.term (L.subseq (B.subseq i))).S.base.metric s)
                  (L.maps.partialDiffeomorph (B.subseq i) x) radius,
                  curvDerivNormSq (I := I3) 0
                    ((X.term (L.subseq (B.subseq i))).S.base.metric t) y ≤ C := by
  obtain ⟨epsStar, hepsStar, hflow⟩ :=
    exists_source_curvature_bound_before_time_of_scalar_le hmod hsigma hPhi
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle X L J B s hs
  obtain ⟨C, hC⟩ := B.compact_time_bound s s le_rfl
    (by simpa only [Icc_self, singleton_subset_iff] using hs)
  let A : ℝ := (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt C
  have hscalar : ∀ x : L.space.M, B.solution.scalar s x ≤ A := by
    intro x
    exact (le_abs_self _).trans ((scalar_abs_le_rm (B.solution.base.metric s) x).trans
      (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (hC s ⟨le_rfl, le_rfl⟩ x)) (by positivity)))
  obtain ⟨radius, depth, C₀, hradius, hdepth, hC₀, hbound⟩ := hflow eps heps hle A
  exact ⟨radius, depth, C₀, hradius, hdepth, hC₀, hbound X L J B s hs hscalar⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

set_option autoImplicit false
noncomputable section
open scoped Topology
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff ENNReal
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_local_pullback_solutions_before_time_of_scalar_le
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa)
    (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ A : ℝ, ∃ delta : ℝ, ∃ hd : 0 < delta,
        ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
          (J : RealTimeInterval) (B : BackwardExtension L J) (s : ℝ), s ∈ J.carrier →
          (∀ x : L.space.M, B.solution.scalar s x ≤ A) →
          ∀ p : L.space.M, ∀ radius : ℝ, 0 ≤ radius →
            ∀ U : TopologicalSpace.Opens L.space.M,
              (U : Set L.space.M) ⊆
                riemannianClosedBallOf (I := I3) (B.solution.base.metric s) p radius →
              ∃ N : ℕ, ∃ S : ℕ → SolutionOn (I := I3) (M := U)
                (RealTimeInterval.closed (-delta) 0 (by linarith)),
                (∀ i, IsSolutionOn (S i)) ∧
                (∀ i, (U : Set L.space.M) ⊆
                  (L.maps.partialDiffeomorph (B.subseq (i + N))).source) ∧
                (∀ i t (x : U) (v w : TangentSpace I3 x),
                  ((S i).base.metric t).inner x v w =
                    ((X.term (L.subseq (B.subseq (i + N)))).S.base.metric (t + s)).inner
                      (L.maps.partialDiffeomorph (B.subseq (i + N)) x)
                      (mfderiv I3 I3 (L.maps.partialDiffeomorph (B.subseq (i + N))) x v)
                      (mfderiv I3 I3 (L.maps.partialDiffeomorph (B.subseq (i + N))) x w)) ∧
                MetricCInfConvergenceOnCompacts (fun i => (S i).base.metric 0)
                  ((B.solution.base.metric s).restrictOpen U)
                  ((B.solution.base.metric s).restrictOpen U) ∧
                ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
                  ∀ i m t, t ∈ Icc (-delta) 0 → ∀ x : U,
                    curvDerivNorm m ((S i).base.metric t) x ≤ C m := by
  obtain ⟨epsStar, hepsStar, hcurv⟩ :=
    exists_source_curvature_bound_before_time_of_scalar_le hmod hsigma hPhi
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle A
  obtain ⟨sourceRadius, depth, C₀, _hsourceRadius, hdepth, _hC₀, hboundA⟩ :=
    hcurv eps heps hle A
  refine ⟨depth / 2, half_pos hdepth, ?_⟩
  intro X L J B s hs hscalar
  have hbound := hboundA X L J B s hs hscalar
  obtain ⟨C, hcanonical⟩ := B.convergence.exists_canonical_metric_convergence
    (t := 0 + s) (by simpa only [zero_add] using hs)
  let P : MetricCompactLimit ((X.toFlowSequence.timeShift s).atTime 0) := {
    subseq := L.subseq ∘ B.subseq
    strictMono := L.strictMono.comp B.strictMono
    limit := { L.space with metric := B.solution.base.metric (0 + s) }
    limit_complete := by simpa only [zero_add] using B.complete s hs
    maps := X.toFlowSequence.sliceMaps
      (subsequenceMaps L.maps B.subseq B.strictMono) B.solution.base.metric (0 + s)
    convergence := { metrics := C } }
  intro p radius hradius U hU
  have hcomplete : RiemannianMetricComplete (I := I3) (B.solution.base.metric s) :=
    ⟨MetricComplete.complete { L.space with metric := B.solution.base.metric s }
      (B.complete s hs)⟩
  have hslab : ∀ᶠ i in atTop,
      Icc (-depth) 0 ⊆ ((X.toFlowSequence.timeShift s).interval (P.subseq i)).carrier ∧
      Ioo (-depth) 0 ⊆ ((X.toFlowSequence.timeShift s).interval (P.subseq i)).regular ∧
      ∀ t ∈ Icc (-depth) 0,
        ∀ x ∈ riemannianClosedBallOf (I := I3) P.limit.metric p (radius + 1),
          PointedFlowData.rmNormSq ((X.toFlowSequence.timeShift s).term (P.subseq i)) t
            (P.maps.partialDiffeomorph i x) ≤ C₀ := by
    filter_upwards [hbound _ (hcomplete.closedEBall_isCompact p (radius + 1))] with i hi
    refine ⟨?_, ?_, ?_⟩
    · intro t ht
      exact hi.2.1 ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · intro t ht
      exact hi.2.2.1 ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · intro t ht x hx
      have hx' : x ∈ riemannianClosedBallOf (I := I3)
          (B.solution.base.metric s) p (radius + 1) := by
        simpa only [P, zero_add] using hx
      have hc := hi.2.2.2 (t + s) ⟨by linarith [ht.1], by linarith [ht.2]⟩ x hx'
        (L.maps.partialDiffeomorph (B.subseq i) x) (by
          change riemannianEDistOf (I := I3) _ _ _ ≤ _
          erw [riemannianEDistOf_self]
          exact bot_le)
      exact (rmNormSq_eq_curvDerivNormSq X (L.subseq (B.subseq i)) (t + s)
        (L.maps.partialDiffeomorph (B.subseq i) x)).le.trans hc
  have hpU : (U : Set P.limit.M) ⊆
      riemannianClosedBallOf (I := I3) P.limit.metric p radius := by
    simpa only [P, zero_add] using hU
  obtain ⟨N, S, hS, hsource, hmetric, hterminal, C', hC', hjets⟩ :=
    exists_local_pullback_solutions_of_slab_curvature_bound P hcanonical
      (half_pos hdepth) (half_lt_self hdepth) p hradius hslab U hpU
  refine ⟨N, S, hS, hsource, hmetric, ?_, C', hC', hjets⟩
  simpa only [P, zero_add] using hterminal

theorem exists_local_pullback_solutions_before_time_of_model_curvature_bound
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa)
    (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
        (J : RealTimeInterval) (B : BackwardExtension L J) (s : ℝ), s ∈ J.carrier →
        ∃ delta : ℝ, ∃ hd : 0 < delta,
          ∀ p : L.space.M, ∀ radius : ℝ, 0 ≤ radius →
            ∀ U : TopologicalSpace.Opens L.space.M,
              (U : Set L.space.M) ⊆
                riemannianClosedBallOf (I := I3) (B.solution.base.metric s) p radius →
              ∃ N : ℕ, ∃ S : ℕ → SolutionOn (I := I3) (M := U)
                (RealTimeInterval.closed (-delta) 0 (by linarith)),
                (∀ i, IsSolutionOn (S i)) ∧
                (∀ i, (U : Set L.space.M) ⊆
                  (L.maps.partialDiffeomorph (B.subseq (i + N))).source) ∧
                (∀ i t (x : U) (v w : TangentSpace I3 x),
                  ((S i).base.metric t).inner x v w =
                    ((X.term (L.subseq (B.subseq (i + N)))).S.base.metric (t + s)).inner
                      (L.maps.partialDiffeomorph (B.subseq (i + N)) x)
                      (mfderiv I3 I3 (L.maps.partialDiffeomorph (B.subseq (i + N))) x v)
                      (mfderiv I3 I3 (L.maps.partialDiffeomorph (B.subseq (i + N))) x w)) ∧
                MetricCInfConvergenceOnCompacts (fun i => (S i).base.metric 0)
                  ((B.solution.base.metric s).restrictOpen U)
                  ((B.solution.base.metric s).restrictOpen U) ∧
                ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
                  ∀ i m t, t ∈ Icc (-delta) 0 → ∀ x : U,
                    curvDerivNorm m ((S i).base.metric t) x ≤ C m := by
  obtain ⟨epsStar, hepsStar, hflow⟩ :=
    exists_local_pullback_solutions_before_time_of_scalar_le hmod hsigma hPhi
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle X L J B s hs
  obtain ⟨C, hC⟩ := B.compact_time_bound s s le_rfl
    (by simpa only [Icc_self, singleton_subset_iff] using hs)
  let A : ℝ := (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt C
  have hscalar : ∀ x : L.space.M, B.solution.scalar s x ≤ A := by
    intro x
    exact (le_abs_self _).trans ((scalar_abs_le_rm (B.solution.base.metric s) x).trans
      (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (hC s ⟨le_rfl, le_rfl⟩ x)) (by positivity)))
  obtain ⟨width, hw, hwidth⟩ := hflow eps heps hle A
  exact ⟨width, hw, hwidth X L J B s hs hscalar⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff _root_.Topology
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem NormalizedSequence.secLower_zero_of_slice_convergence
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (hPhi : AdmissiblePinchingFunction Phi)
    {t : ℝ} (ht : t ≤ 0) {P : PointedRiemannianManifold.{u, 0, 0} I3}
    {f : ℕ → ℕ} (hf : Tendsto f atTop atTop)
    {F : PointedRiemannianConvergenceMaps (X.toFlowSequence.atTime t) P f}
    (C : MetricConvergenceData F)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData F i) :
    SecLower P.metric 0 univ := by
  have htime : ∀ᶠ i in atTop, t ∈ (X.interval (f i)).carrier := by
    filter_upwards [(X.depth_tendsto.comp hf).eventually_ge_atTop (-t)] with i hi
    change -t ≤ X.depth (f i) at hi
    rw [X.carrier_eq]
    exact ⟨by linarith [X.depth_pos (f i)], ht⟩
  have hpinching : ∀ᶠ i in atTop, ∀ y : (X.term (f i)).M,
      curvatureOperatorLowerBoundAt ((X.term (f i)).S.base.metric t) y
        (metricAlgebraicCurvatureTensorAt ((X.term (f i)).S.base.metric t) y)
        (rescalePinchingFunction (X.scale (f i)) Phi
          (metricScalarAt ((X.term (f i)).S.base.metric t) y)) := by
    filter_upwards [htime] with i hi
    intro y
    have h := X.pinching (f i) t hi y
    have hval : ((X.term (f i)).S.base.rm04 t) y =
        metricRm04At ((X.term (f i)).S.base.metric t) y := by
      simp only [SolutionFamily.rm04]
      exact metricRm04_apply _ _
    have hK : (X.term (f i)).S.scalar t y =
        metricScalarAt ((X.term (f i)).S.base.metric t) y := by
      simp only [SolutionOn.scalar, SolutionFamily.scalar]
    intro n c v w
    have hh := h n c v w
    simp only [algebraicCurvatureOperatorQuadraticEval, algebraicCurvatureIdentityQuadraticEval,
      hval, hK] at hh ⊢
    exact hh
  have hmain := sectional_nonnegative_of_pointed_admissible_pinching_eventually
    (X := X.toFlowSequence.atTime t) (L := P) (F := F) C hcanonical hPhi X.scale
    X.scale_pos (X.scale_tendsto.comp hf) hpinching
  intro x _ v w
  have hvec : (fun i => ![v, w, w, v] i) = vec4 (I := I3) v w w v := by
    funext i
    fin_cases i <;> simp [vec4]
  simpa only [SecLower, zero_mul, metricRm04StandardAt_apply, hvec] using hmain x v w

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

set_option autoImplicit false
noncomputable section
open scoped Topology
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff ENNReal
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_complete_nonnegative_backward_metric_limit_before_time_of_scalar_le
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa)
    (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ A : ℝ, ∃ delta : ℝ, ∃ hd : 0 < delta,
        ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
          (J : RealTimeInterval) (B : BackwardExtension L J) (s : ℝ), s ∈ J.carrier →
          (∀ x : L.space.M, B.solution.scalar s x ≤ A) →
          ∃ U : ℕ → TopologicalSpace.Opens L.space.M,
            (∀ n, (U n : Set L.space.M) = riemannianBallOf (I := I3)
              (B.solution.base.metric s) L.space.basepoint ((n : ℝ) + 1)) ∧
            ExhaustsByOpen (fun n => (U n : Set L.space.M)) ∧
            ∃ N : ℕ → ℕ, ∃ S : ∀ n, ℕ → SolutionOn (I := I3) (M := U n)
              (RealTimeInterval.closed (-delta) 0 (by linarith)),
              (∀ n i, IsSolutionOn (S n i)) ∧
              (∀ n i, (U n : Set L.space.M) ⊆
                (L.maps.partialDiffeomorph (B.subseq (i + N n))).source) ∧
              (∀ n i t (x : U n) (v w : TangentSpace I3 x),
                ((S n i).base.metric t).inner x v w =
                  ((X.term (L.subseq (B.subseq (i + N n)))).S.base.metric (t + s)).inner
                    (L.maps.partialDiffeomorph (B.subseq (i + N n)) x)
                    (mfderiv I3 I3 (L.maps.partialDiffeomorph (B.subseq (i + N n))) x v)
                    (mfderiv I3 I3 (L.maps.partialDiffeomorph (B.subseq (i + N n))) x w)) ∧
              ∃ rho : ℕ → ℕ, StrictMono rho ∧
                ∃ G : ℝ → SmoothRiemannianMetric I3 L.space.M,
                  G 0 = B.solution.base.metric s ∧
                  IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := L.space.M)
                    (RealTimeInterval.closed (-delta / 2) 0 (by linarith))) ∧
                  (∀ t ∈ Icc (-delta / 2) 0, SecLower (G t) 0 univ) ∧
                  (∀ t ∈ Icc (-delta / 2) 0, RiemannianMetricComplete (G t)) ∧
                  (∀ n, ∀ K : Set (U n), IsCompact K → ∀ order : ℕ,
                    ∀ epsilon : ℝ, 0 < epsilon → ∃ j : ℕ,
                      ∀ i ≥ j, ∀ t ∈ Icc (-delta / 2) 0,
                        metricDerivNormSupOn K order ((S n (rho i - N n)).base.metric t)
                          ((G t).restrictOpen (U n))
                          ((B.solution.base.metric s).restrictOpen (U n)) < epsilon) ∧
                  ∀ t ∈ Icc (-delta / 2) 0, t + s ∈ J.carrier →
                    G t = B.solution.base.metric (t + s) := by
  obtain ⟨epsStar, hepsStar, hlocal⟩ :=
    exists_local_pullback_solutions_before_time_of_scalar_le hmod hsigma hPhi
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle A
  obtain ⟨delta, hd, hdeltaA⟩ := hlocal eps heps hle A
  refine ⟨delta, hd, ?_⟩
  intro X L J B s hs hscalar
  have hdelta := hdeltaA X L J B s hs hscalar
  let _ : ConnectedSpace L.space.M := L.connected
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let U : ℕ → TopologicalSpace.Opens L.space.M := fun n =>
    ⟨riemannianBallOf (I := I3) (B.solution.base.metric s) L.space.basepoint ((n : ℝ) + 1),
      isOpen_riemannianBallOf (I := I3) (B.solution.base.metric s) L.space.basepoint _⟩
  have hbase (n : ℕ) : L.space.basepoint ∈ U n := by
    change riemannianEDistOf (I := I3) (B.solution.base.metric s)
      L.space.basepoint L.space.basepoint < ENNReal.ofReal ((n : ℝ) + 1)
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hbounded (n : ℕ) : (U n : Set L.space.M) ⊆
      riemannianClosedBallOf (I := I3) (B.solution.base.metric s)
        L.space.basepoint ((n : ℝ) + 1) := by
    intro x hx
    exact (show riemannianEDistOf (I := I3) (B.solution.base.metric s)
      L.space.basepoint x < ENNReal.ofReal ((n : ℝ) + 1) from hx).le
  have hmono : Monotone (fun n => (U n : Set L.space.M)) := by
    intro n m hnm
    exact riemannianBallOf_mono _ _ (by exact_mod_cast Nat.add_le_add_right hnm 1)
  have hcover : (⋃ n, (U n : Set L.space.M)) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨n, hn⟩ := exists_nat_gt (riemannianEDistOf (I := I3)
      (B.solution.base.metric s) L.space.basepoint x).toReal
    refine mem_iUnion.mpr ⟨n, ?_⟩
    exact (ENNReal.lt_ofReal_iff_toReal_lt
      (riemannianEDistOf_ne_top (B.solution.base.metric s) _ _)).mpr (by linarith)
  have hexhausts : ExhaustsByOpen (fun n => (U n : Set L.space.M)) := by
    refine ⟨fun n => (U n).isOpen, fun n => hmono (Nat.le_succ n), ?_⟩
    intro K hK
    obtain ⟨n, hn⟩ := hK.elim_directed_cover (fun n => (U n : Set L.space.M))
      (fun n => (U n).isOpen) (by rw [hcover]; exact subset_univ K)
      (fun n m => ⟨max n m, hmono (le_max_left n m), hmono (le_max_right n m)⟩)
    exact ⟨n, fun m hnm => hn.trans (hmono hnm)⟩
  have hUcover : ∀ x : L.space.M, ∃ n, x ∈ U n := by
    intro x
    have hx : x ∈ ⋃ n, (U n : Set L.space.M) := by rw [hcover]; trivial
    exact mem_iUnion.mp hx
  let _ (n : ℕ) : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 (U n).isOpen)
  have hlocalU (n : ℕ) :=
    hdelta L.space.basepoint ((n : ℝ) + 1) (by positivity) (U n) (hbounded n)
  choose N S hS hsource hmetric hterminal C hC hjet using hlocalU
  obtain ⟨conv, hcanonical⟩ := B.convergence.exists_canonical_metric_convergence
    (t := 0 + s) (by simpa only [zero_add] using hs)
  let P : MetricCompactLimit ((X.toFlowSequence.timeShift s).atTime 0) := {
    subseq := L.subseq ∘ B.subseq
    strictMono := L.strictMono.comp B.strictMono
    limit := { L.space with metric := B.solution.base.metric (0 + s) }
    limit_complete := by simpa only [zero_add] using B.complete s hs
    maps := X.toFlowSequence.sliceMaps
      (subsequenceMaps L.maps B.subseq B.strictMono) B.solution.base.metric (0 + s)
    convergence := { metrics := conv } }
  have hslab : Icc (-delta / 2) 0 ⊆
      (RealTimeInterval.closed (-delta) 0 (by linarith)).carrier := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hreg : Ico (-delta / 2) 0 ⊆
      (RealTimeInterval.closed (-delta) 0 (by linarith)).regular := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  obtain ⟨rho, hrho, g, hg0, hgsol, hconv, hoverlap⟩ :=
    exists_common_solution_subsequence_on_terminal_maps_of_terminal_convergence
      (X.toFlowSequence.timeShift s) P U hbase
      (fun _ => RealTimeInterval.closed (-delta) 0 (by linarith))
      S hS (fun n => (B.solution.base.metric s).restrictOpen (U n))
      (fun _ => -delta / 2) (fun _ => 0) (fun _ => by linarith)
      (fun _ => hslab) (fun _ => hreg) hterminal (by
        intro n K _hK q
        exact ⟨C n q, hC n q, Eventually.of_forall fun i t ht x _ =>
          hjet n i q t ⟨by linarith [ht.1], ht.2⟩ x⟩)
      N hsource (fun n i t x v w _ht _hx => hmetric n i t x v w)
  obtain ⟨G, hGsol, hG⟩ := exists_solution_of_compatible_open_cover U hUcover g hgsol
    (fun n m t ht => hoverlap n m (U n ⊓ U m) inf_le_left inf_le_right t ht ht)
  have hG0 : G 0 = B.solution.base.metric s := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    obtain ⟨n, hxn⟩ := hUcover x
    have heq := (hG n 0 ⟨by linarith, le_rfl⟩).trans (hg0 n)
    exact congrArg (fun k : SmoothRiemannianMetric I3 (U n) => k.inner ⟨x, hxn⟩ v w) heq
  have hs0 : s ≤ 0 := by
    obtain ⟨i, hi⟩ := (eventually_mem_backwardWindow B hs).exists
    exact hi.2
  have hsec : ∀ t ∈ Icc (-delta / 2) 0, SecLower (G t) 0 univ := by
    intro t ht x _hx v w
    obtain ⟨n, hxn⟩ := hUcover x
    let f : ℕ → ℕ := fun i => L.subseq (B.subseq (rho i - N n + N n))
    let F (i : ℕ) := L.maps.partialDiffeomorph (B.subseq (rho i - N n + N n))
    obtain ⟨Psi, _hPsi, Ct, hcanonicalt⟩ :=
      exists_pointed_metric_convergence_of_pullback_on_open
        (X.toFlowSequence.atTime (t + s)) L.space f F (U n) (hbase n)
        (fun i => hsource n (rho i - N n))
        (fun i => L.maps.basepoint_map (B.subseq (rho i - N n + N n)))
        (fun i => (S n (rho i - N n)).base.metric t)
        ((G t).restrictOpen (U n)) ((B.solution.base.metric s).restrictOpen (U n))
        (fun i => hmetric n (rho i - N n) t) (by
          intro K hK order epsilon hepsilon
          obtain ⟨j, hj⟩ := hconv n K hK order epsilon hepsilon
          exact ⟨j, fun i hi => by rw [hG n t ht]; exact hj i hi t ht⟩)
    have hf : Tendsto f atTop atTop := by
      have heq : f =ᶠ[atTop] fun i => L.subseq (B.subseq (rho i)) := by
        filter_upwards [eventually_ge_atTop (N n)] with i hi
        dsimp only [f]
        rw [Nat.sub_add_cancel (hi.trans (hrho.id_le i))]
      exact (L.strictMono.tendsto_atTop.comp
        (B.strictMono.tendsto_atTop.comp hrho.tendsto_atTop)).congr' heq.symm
    have hn := X.secLower_zero_of_slice_convergence hPhi
      (show t + s ≤ 0 by linarith [ht.2]) hf Ct hcanonicalt
    have hn' := hn (⟨x, hxn⟩ : U n) (mem_univ _) v w
    have hvec : (fun i => ![v, w, w, v] i) = vec4 (I := I3) v w w v := by
      funext i
      fin_cases i <;> simp [vec4]
    have hcurv : 0 ≤ metricRm04StandardAt ((G t).restrictOpen (U n))
        (⟨x, hxn⟩ : U n) v w w v := by
      simp only [zero_mul] at hn'
      change 0 ≤ metricRm04At ((G t).restrictOpen (U n)) (⟨x, hxn⟩ : U n)
        (fun i : Fin 4 => ![v, w, w, v] i) at hn'
      erw [metricRm04StandardAt_apply]
      rw [hvec] at hn'
      exact hn'
    rw [metricRm04StandardAt_restrictOpen (I := I3) (G t) (U n)
      (⟨x, hxn⟩ : U n) v w w v, mfderiv_subtype_val (I := I3) (U n) (⟨x, hxn⟩ : U n)]
      at hcurv
    change 0 ≤ metricRm04At (G t) x (vec4 (I := I3) v w w v) at hcurv
    simpa only [zero_mul, hvec] using hcurv
  have hcomplete : ∀ t ∈ Icc (-delta / 2) 0, RiemannianMetricComplete (G t) := by
    intro t ht
    apply complete_at_earlier_time_of_ricci_nonnegative
      ({ base.metric := G } : SolutionOn (I := I3) (M := L.space.M)
        (RealTimeInterval.closed (-delta / 2) 0 (by linarith))) hGsol
      (a := -delta / 2) (b := 0) (fun _ h => h) (fun _ h => h)
    · intro r hr y v
      change 0 ≤ metricRicciAt (G r) y (vec2 v v)
      rw [metricRicciAt_apply_eq_ricciTensor (I := I3) (G r) y v v]
      apply DifferentialGeometry.Geometry.Riemannian.BonnetMyers.ricci_nonneg_of_sec
        (G r) y
      apply (metricRm04At_mem_tensor04SectionalNonnegativeCone_iff (G r) y).mpr
      intro a b
      have hh := hsec r ⟨hr.1.le, hr.2.le⟩ y (mem_univ _) a b
      have hvec : (fun i => ![a, b, b, a] i) = vec4 (I := I3) a b b a := by
        funext i
        fin_cases i <;> simp [vec4]
      simpa only [zero_mul, metricRm04StandardAt_apply, hvec] using hh
    · change RiemannianMetricComplete (G 0)
      rw [hG0]
      exact ⟨MetricComplete.complete { L.space with metric := B.solution.base.metric s }
        (B.complete s hs)⟩
    · exact ht
  refine ⟨U, fun _ => rfl, hexhausts, N, S, hS, hsource, hmetric,
    rho, hrho, G, hG0, hGsol, hsec, hcomplete, ?_, ?_⟩
  · intro n K hK order epsilon hepsilon
    obtain ⟨j, hj⟩ := hconv n K hK order epsilon hepsilon
    refine ⟨j, fun i hi t ht => ?_⟩
    rw [hG n t ht]
    exact hj i hi t ht
  · intro t ht hts
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    obtain ⟨n, hxn⟩ := hUcover x
    have hconvT : MetricCInfConvergenceOnCompacts
        (fun i => (S n (rho i - N n)).base.metric t) (g n t)
        ((B.solution.base.metric s).restrictOpen (U n)) := by
      intro K hK order epsilon hepsilon
      obtain ⟨j, hj⟩ := hconv n K hK order epsilon hepsilon
      exact ⟨j, fun i hi => hj i hi t ht⟩
    have hnew := metricCInf_inner (fun i => (S n (rho i - N n)).base.metric t) (g n t)
      ((B.solution.base.metric s).restrictOpen (U n)) hconvT (⟨x, hxn⟩ : U n) v w
    have hold := (B.convergence.tendsto_metric_inner hts x v w).comp hrho.tendsto_atTop
    have heq : (fun i => ((S n (rho i - N n)).base.metric t).inner (⟨x, hxn⟩ : U n) v w)
        =ᶠ[atTop] (fun i =>
          ((X.term (L.subseq (B.subseq (rho i)))).S.base.metric (t + s)).inner
            (L.maps.partialDiffeomorph (B.subseq (rho i)) x)
            (mfderiv I3 I3 (L.maps.partialDiffeomorph (B.subseq (rho i))) x v)
            (mfderiv I3 I3 (L.maps.partialDiffeomorph (B.subseq (rho i))) x w)) := by
      filter_upwards [eventually_ge_atTop (N n)] with i hi
      have hh := hmetric n (rho i - N n) t (⟨x, hxn⟩ : U n) v w
      rw [Nat.sub_add_cancel (hi.trans (hrho.id_le i))] at hh
      exact hh
    have hinner := tendsto_nhds_unique (hnew.congr' heq) hold
    have hrestrict := congrArg
      (fun k : SmoothRiemannianMetric I3 (U n) => k.inner (⟨x, hxn⟩ : U n) v w)
      (hG n t ht)
    exact hrestrict.trans hinner

theorem exists_complete_nonnegative_backward_metric_limit_before_time_of_model_curvature_bound
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa)
    (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
        (J : RealTimeInterval) (B : BackwardExtension L J) (s : ℝ), s ∈ J.carrier →
        ∃ delta : ℝ, ∃ hd : 0 < delta,
          ∃ U : ℕ → TopologicalSpace.Opens L.space.M,
            (∀ n, (U n : Set L.space.M) = riemannianBallOf (I := I3)
              (B.solution.base.metric s) L.space.basepoint ((n : ℝ) + 1)) ∧
            ExhaustsByOpen (fun n => (U n : Set L.space.M)) ∧
            ∃ N : ℕ → ℕ, ∃ S : ∀ n, ℕ → SolutionOn (I := I3) (M := U n)
              (RealTimeInterval.closed (-delta) 0 (by linarith)),
              (∀ n i, IsSolutionOn (S n i)) ∧
              (∀ n i, (U n : Set L.space.M) ⊆
                (L.maps.partialDiffeomorph (B.subseq (i + N n))).source) ∧
              (∀ n i t (x : U n) (v w : TangentSpace I3 x),
                ((S n i).base.metric t).inner x v w =
                  ((X.term (L.subseq (B.subseq (i + N n)))).S.base.metric (t + s)).inner
                    (L.maps.partialDiffeomorph (B.subseq (i + N n)) x)
                    (mfderiv I3 I3 (L.maps.partialDiffeomorph (B.subseq (i + N n))) x v)
                    (mfderiv I3 I3 (L.maps.partialDiffeomorph (B.subseq (i + N n))) x w)) ∧
              ∃ rho : ℕ → ℕ, StrictMono rho ∧
                ∃ G : ℝ → SmoothRiemannianMetric I3 L.space.M,
                  G 0 = B.solution.base.metric s ∧
                  IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := L.space.M)
                    (RealTimeInterval.closed (-delta / 2) 0 (by linarith))) ∧
                  (∀ t ∈ Icc (-delta / 2) 0, SecLower (G t) 0 univ) ∧
                  (∀ t ∈ Icc (-delta / 2) 0, RiemannianMetricComplete (G t)) ∧
                  (∀ n, ∀ K : Set (U n), IsCompact K → ∀ order : ℕ,
                    ∀ epsilon : ℝ, 0 < epsilon → ∃ j : ℕ,
                      ∀ i ≥ j, ∀ t ∈ Icc (-delta / 2) 0,
                        metricDerivNormSupOn K order ((S n (rho i - N n)).base.metric t)
                          ((G t).restrictOpen (U n))
                          ((B.solution.base.metric s).restrictOpen (U n)) < epsilon) ∧
                  ∀ t ∈ Icc (-delta / 2) 0, t + s ∈ J.carrier →
                    G t = B.solution.base.metric (t + s) := by
  obtain ⟨epsStar, hepsStar, hflow⟩ :=
    exists_complete_nonnegative_backward_metric_limit_before_time_of_scalar_le hmod hsigma hPhi
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle X L J B s hs
  obtain ⟨C, hC⟩ := B.compact_time_bound s s le_rfl
    (by simpa only [Icc_self, singleton_subset_iff] using hs)
  let A : ℝ := (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt C
  have hscalar : ∀ x : L.space.M, B.solution.scalar s x ≤ A := by
    intro x
    exact (le_abs_self _).trans ((scalar_abs_le_rm (B.solution.base.metric s) x).trans
      (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (hC s ⟨le_rfl, le_rfl⟩ x)) (by positivity)))
  obtain ⟨width, hw, hwidth⟩ := hflow eps heps hle A
  exact ⟨width, hw, hwidth X L J B s hs hscalar⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

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

theorem exists_convergent_backward_flow_before_time_of_scalar_le
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa)
    (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ A : ℝ, ∃ width : ℝ, ∃ hw : 0 < width,
        ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
          (J : RealTimeInterval) (B : BackwardExtension L J) (s : ℝ), s ∈ J.carrier →
          (∀ x : L.space.M, B.solution.scalar s x ≤ A) →
          ∃ rho : ℕ → ℕ, ∃ hrho : StrictMono rho,
          ∃ T : SolutionOn (I := I3) (M := L.space.M)
            (RealTimeInterval.closed (s - width) s (by linarith)),
            IsSolutionOn T ∧ T.base.metric s = B.solution.base.metric s ∧
            (∀ t ∈ Icc (s - width) s, SecLower (T.base.metric t) 0 univ) ∧
            (∀ t ∈ Icc (s - width) s, RiemannianMetricComplete (T.base.metric t)) ∧
            ConvergesOn (subsequenceMaps L.maps (B.subseq ∘ rho)
              (B.strictMono.comp hrho)) T ∧
            (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (s - width) s, ∀ x : L.space.M,
              FlowMetricBall.rmNormSq T t x ≤ C) ∧
            ∀ t ∈ Icc (s - width) s, t ∈ J.carrier →
              T.base.metric t = B.solution.base.metric t := by
  obtain ⟨epsFlow, hepsFlow, hflow⟩ :=
    exists_complete_nonnegative_backward_metric_limit_before_time_of_scalar_le
      hmod hsigma hPhi
  obtain ⟨epsBound, hepsBound, hbound⟩ :=
    exists_source_curvature_bound_before_time_of_scalar_le hmod hsigma hPhi
  refine ⟨min epsFlow epsBound, lt_min hepsFlow hepsBound, ?_⟩
  intro eps heps hle A
  obtain ⟨delta, hd, hflowA⟩ := hflow eps heps (hle.trans (min_le_left _ _)) A
  obtain ⟨radius, depth, C₀, _hradius, hdepth, hC₀, hsourceBoundA⟩ :=
    hbound eps heps (hle.trans (min_le_right _ _)) A
  let width := min (delta / 4) depth
  have hw : 0 < width := lt_min (by positivity) hdepth
  have hwd : width ≤ delta / 4 := min_le_left _ _
  have hwb : width ≤ depth := min_le_right _ _
  refine ⟨width, hw, ?_⟩
  intro X L J B s hs hscalarA
  obtain ⟨U, _hUeq, hexhausts, N, S, hS, hsource, hmetric,
    rho, hrho, G, hG0, hG, hsec, hcomplete, hconv, hoverlap⟩ :=
      hflowA X L J B s hs hscalarA
  have hsourceBound := hsourceBoundA X L J B s hs hscalarA
  let D := RealTimeInterval.closed (s - delta / 2) s (by linarith : s - delta / 2 ≤ s)
  let V : SolutionOn (I := I3) (M := L.space.M) D :=
    { base.metric := fun t => G (t - s) }
  have hV : IsSolutionOn V := by
    have ht := isSolutionOn_timeShift hG (-s)
    apply isSolutionOn_timeRestrict ht
    · intro t ht
      change t + -s ∈ Icc (-delta / 2) 0
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · intro t ht
      change t + -s ∈ Ioo (-delta / 2) 0
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  let T := V.timeRestrict (RealTimeInterval.closed (s - width) s (by linarith))
  have htimes : Icc (s - width) s ⊆ Icc (s - delta / 2) s := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hT : IsSolutionOn T := isSolutionOn_timeRestrict hV htimes
    (Ioo_subset_Ioo (by linarith) le_rfl)
  have hcompare : ∀ K : Set L.space.M, IsCompact K → ∀ a b : ℝ, a ≤ b →
      Icc a b ⊆ Icc (s - width) s → ∀ order : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ i in atTop, K ⊆ (L.maps.partialDiffeomorph (B.subseq (rho i))).source ∧
          Nonempty (MetricComparisonOn T.base.metric
            ((X.term (L.subseq (B.subseq (rho i)))).S.base.metric)
            (L.maps.partialDiffeomorph (B.subseq (rho i))) K (Icc a b) order epsilon) := by
    intro K hK a b hab hsub order epsilon hepsilon
    obtain ⟨n, hn⟩ := hexhausts.subset K hK
    have hKn : K ⊆ U n := hn n le_rfl
    let S' (i : ℕ) := ((S n (rho i - N n)).timeShift (-s)).timeRestrict D
    have hS' (i : ℕ) : IsSolutionOn (S' i) := by
      apply isSolutionOn_timeRestrict (isSolutionOn_timeShift (hS n (rho i - N n)) (-s))
      · intro t ht
        change t + -s ∈ Icc (-delta) 0
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
      · intro t ht
        change t + -s ∈ Ioo (-delta) 0
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hconv' : ∀ K : Set (U n), IsCompact K → ∀ p : ℕ,
        ∀ eta : ℝ, 0 < eta → ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc (s - width) s,
          metricDerivNormSupOn K p ((S' i).base.metric t)
            ((V.base.metric t).restrictOpen (U n))
            ((B.solution.base.metric s).restrictOpen (U n)) < eta := by
      intro K hK p eta heta
      obtain ⟨j, hj⟩ := hconv n K hK p eta heta
      refine ⟨j, fun i hi t ht => ?_⟩
      exact hj i hi (t - s) ⟨by linarith [ht.1],
        sub_nonpos.mpr ht.2⟩
    have hpair : ∀ i t (x : U n) (v w : TangentSpace I3 x),
        ((S' i).base.metric t).inner x v w =
          ((X.term (L.subseq (B.subseq (rho i - N n + N n)))).S.base.metric t).inner
            (L.maps.partialDiffeomorph (B.subseq (rho i - N n + N n)) x)
            (mfderiv I3 I3 (L.maps.partialDiffeomorph
              (B.subseq (rho i - N n + N n))) x v)
            (mfderiv I3 I3 (L.maps.partialDiffeomorph
              (B.subseq (rho i - N n + N n))) x w) := by
      intro i t x v w
      change (((S n (rho i - N n)).base.metric (t + -s)).inner x v) w = _
      simpa only [neg_add_cancel_right] using
        hmetric n (rho i - N n) (t + -s) x v w
    have hcomp (Q : Set ℝ) (hQ : UniqueDiffOn ℝ Q) (hQsub : Q ⊆ Icc (s - width) s) :=
      eventually_metricComparisonOn_of_local_flow_convergence (U n) S' hS' V hV
        (show s - delta / 2 < s - width by linarith)
        (sub_lt_self s hw) rfl Subset.rfl
        ((B.solution.base.metric s).restrictOpen (U n)) hconv'
        (fun i => (X.term (L.subseq (B.subseq (rho i - N n + N n)))).S.base.metric)
        (fun i => L.maps.partialDiffeomorph (B.subseq (rho i - N n + N n)))
        hpair hQ hQsub hK hKn order hepsilon
    have hcomp' : ∀ᶠ i in atTop,
        Nonempty (MetricComparisonOn V.base.metric
          ((X.term (L.subseq (B.subseq (rho i - N n + N n)))).S.base.metric)
          (L.maps.partialDiffeomorph (B.subseq (rho i - N n + N n)))
          K (Icc a b) order epsilon) := by
      rcases lt_or_eq_of_le hab with hab' | rfl
      · exact hcomp _ (uniqueDiffOn_Icc hab') hsub
      · filter_upwards [hcomp (Icc (s - width) s)
          (uniqueDiffOn_Icc (sub_lt_self s hw)) Subset.rfl] with i hi
        obtain ⟨Ci⟩ := hi
        rw [Icc_self]
        exact ⟨Ci.restrictTimeSingleton (hsub (by simp)) hepsilon.le⟩
    filter_upwards [hcomp', eventually_ge_atTop (N n)] with i hi hiN
    have heq : rho i - N n + N n = rho i := Nat.sub_add_cancel (hiN.trans (hrho.id_le i))
    have hsrc := hsource n (rho i - N n)
    rw [heq] at hi hsrc
    exact ⟨hKn.trans hsrc, hi⟩
  have hconvergence : ConvergesOn (subsequenceMaps L.maps (B.subseq ∘ rho)
      (B.strictMono.comp hrho)) T := by
    intro K hK a b hab hsub order epsilon hepsilon
    have hf := L.strictMono.comp (B.strictMono.comp hrho)
    have hdepth := (X.depth_tendsto.comp hf.tendsto_atTop).eventually_ge_atTop (width - s)
    have hs0 : s ≤ 0 := by
      obtain ⟨i, hi⟩ := (eventually_mem_backwardWindow B hs).exists
      exact hi.2
    filter_upwards [hcompare K hK a b hab hsub order epsilon hepsilon, hdepth]
      with i hi hdi
    refine ⟨?_, hi.1, hi.2⟩
    intro t ht
    rw [X.carrier_eq]
    have htt := hsub ht
    change width - s ≤ X.depth (L.subseq (B.subseq (rho i))) at hdi
    change t ∈ Icc (-(2 * X.depth (L.subseq (B.subseq (rho i))))) 0
    exact ⟨by linarith [htt.1, X.depth_pos (L.subseq (B.subseq (rho i)))],
      htt.2.trans hs0⟩
  let C : ℝ := (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt C₀
  have hC : 0 ≤ C := by positivity
  have hscalar : ∀ t ∈ Icc (s - width) s, ∀ x : L.space.M,
      |metricScalarAt (T.base.metric t) x| ≤ C := by
    intro t ht x
    obtain ⟨Ct, hcanonical⟩ := hconvergence.exists_canonical_metric_convergence ht
    have hlimit := (KappaSolutions.pointedScalar_tendsto_of_metricCG_canonical_domains
      Ct hcanonical x).abs
    apply le_of_tendsto hlimit
    filter_upwards [hrho.tendsto_atTop.eventually
      (hsourceBound {x} isCompact_singleton)] with i hi
    have hrm := hi.2.2.2 t ⟨by linarith [ht.1], ht.2⟩ x (mem_singleton x)
      (L.maps.partialDiffeomorph (B.subseq (rho i)) x) (by
        change riemannianEDistOf (I := I3) _ _ _ ≤ _
        erw [riemannianEDistOf_self]
        exact bot_le)
    have hrm' : FlowMetricBall.rmNormSq (X.term (L.subseq (B.subseq (rho i)))).S t
        (L.maps.partialDiffeomorph (B.subseq (rho i)) x) ≤ C₀ :=
      (rmNormSq_eq_curvDerivNormSq X (L.subseq (B.subseq (rho i))) t
        (L.maps.partialDiffeomorph (B.subseq (rho i)) x)).le.trans hrm
    exact (scalar_abs_le_rm ((X.term (L.subseq (B.subseq (rho i)))).S.base.metric t)
      (L.maps.partialDiffeomorph (B.subseq (rho i)) x)).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrm') (by positivity))
  have hrm : ∀ t ∈ Icc (s - width) s, ∀ x : L.space.M,
      FlowMetricBall.rmNormSq T t x ≤ 100 ^ 2 * C ^ 2 := by
    intro t ht x
    have hnonneg : metricAlgebraicCurvatureTensorAt (T.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone := by
      apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff_sectional
        (T.base.metric t) x (by simp [ThreeSpace])).mpr
      intro v w
      have hvec : (fun i => ![v, w, w, v] i) = vec4 (I := I3) v w w v := by
        funext i
        fin_cases i <;> simp [vec4]
      change 0 ≤ metricRm04StandardAt (G (t - s)) x v w w v
      simpa only [zero_mul, metricRm04StandardAt_apply, hvec] using
        hsec (t - s) ⟨by linarith [ht.1], sub_nonpos.mpr ht.2⟩ x (mem_univ x) v w
    have hnorm := normSq_metricRm04_le_scalar_sq_of_curvatureOperator_nonnegative
      (T.base.metric t) x (by simp [ThreeSpace]) hnonneg
    have hsquare : (metricScalarAt (T.base.metric t) x) ^ 2 ≤ C ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr (hscalar t ht x)
    exact hnorm.trans (mul_le_mul_of_nonneg_left hsquare (by positivity))
  refine ⟨rho, hrho, T, hT, ?_, ?_, ?_, hconvergence,
    ⟨100 ^ 2 * C ^ 2, by positivity, hrm⟩, ?_⟩
  · change G (s - s) = _
    simpa only [sub_self] using hG0
  · intro t ht
    exact hsec (t - s) ⟨by linarith [ht.1], sub_nonpos.mpr ht.2⟩
  · intro t ht
    exact hcomplete (t - s) ⟨by linarith [ht.1], sub_nonpos.mpr ht.2⟩
  · intro t ht htJ
    have h := hoverlap (t - s)
      ⟨by linarith [ht.1], sub_nonpos.mpr ht.2⟩
      (by simpa only [sub_add_cancel] using htJ)
    change G (t - s) = B.solution.base.metric t
    simpa only [sub_add_cancel] using h

theorem exists_convergent_backward_flow_before_time_of_model_curvature_bound
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa)
    (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
        (J : RealTimeInterval) (B : BackwardExtension L J) (s : ℝ), s ∈ J.carrier →
        ∃ width : ℝ, ∃ hw : 0 < width, ∃ rho : ℕ → ℕ, ∃ hrho : StrictMono rho,
          ∃ T : SolutionOn (I := I3) (M := L.space.M)
            (RealTimeInterval.closed (s - width) s (by linarith)),
            IsSolutionOn T ∧ T.base.metric s = B.solution.base.metric s ∧
            (∀ t ∈ Icc (s - width) s, SecLower (T.base.metric t) 0 univ) ∧
            (∀ t ∈ Icc (s - width) s, RiemannianMetricComplete (T.base.metric t)) ∧
            ConvergesOn (subsequenceMaps L.maps (B.subseq ∘ rho)
              (B.strictMono.comp hrho)) T ∧
            (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (s - width) s, ∀ x : L.space.M,
              FlowMetricBall.rmNormSq T t x ≤ C) ∧
            ∀ t ∈ Icc (s - width) s, t ∈ J.carrier →
              T.base.metric t = B.solution.base.metric t := by
  obtain ⟨epsStar, hepsStar, hflow⟩ :=
    exists_convergent_backward_flow_before_time_of_scalar_le hmod hsigma hPhi
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle X L J B s hs
  obtain ⟨C, hC⟩ := B.compact_time_bound s s le_rfl
    (by simpa only [Icc_self, singleton_subset_iff] using hs)
  let A : ℝ := (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt C
  have hscalar : ∀ x : L.space.M, B.solution.scalar s x ≤ A := by
    intro x
    exact (le_abs_self _).trans ((scalar_abs_le_rm (B.solution.base.metric s) x).trans
      (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (hC s ⟨le_rfl, le_rfl⟩ x)) (by positivity)))
  obtain ⟨width, hw, hwidth⟩ := hflow eps heps hle A
  exact ⟨width, hw, hwidth X L J B s hs hscalar⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
