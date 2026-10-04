import DifferentialGeometry.Geometry.Geodesic.Convergence.BufferedOpenCompact
import DifferentialGeometry.Geometry.Geodesic.Convergence.BufferedLengthConvergence
import DifferentialGeometry.Geometry.Geodesic.Convergence.UnitBufferedFlow
import DifferentialGeometry.Geometry.Geodesic.Convergence.MovingTimeFlowConvergence
import DifferentialGeometry.Geometry.Metric.Convergence.Time.Lipschitz

/-!
# Original inward minimizing directions under buffered metric convergence

The actual inverse unit vectors converge in the native open-source tangent bundle. Common
flow domains and moving endpoint times identify their limit with an original inward direction.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [SigmaCompactSpace N]
  [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]
  [CompleteSpace N] [IsContinuousRiemannianBundle E (fun x : N => TangentSpace I x)]
  {M : ℕ → Type*} [∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)] [∀ i, SigmaCompactSpace (M i)]
  [∀ i, RiemannianBundle (fun x : M i => TangentSpace I x)]
  [∀ i, IsRiemannianManifold I (M i)] [∀ i, CompleteSpace (M i)]
  [∀ i, IsContinuousRiemannianBundle E (fun x : M i => TangentSpace I x)]

theorem exists_subseq_inward_direction_limit
    (g : SmoothRiemannianMetric I N) (hNorm : IsMetricNorm g)
    (U : TopologicalSpace.Opens N) (n : U)
    (hbuffer : Metric.closedBall (n : N) 10 ⊆ U)
    (hSeq : ℕ → SmoothRiemannianMetric I U)
    (gSeq : ∀ i, SmoothRiemannianMetric I (M i))
    (hSeqNorm : ∀ i, IsMetricNorm (gSeq i))
    (j : ∀ i, PartialDiffeomorph I I U (M i) ∞)
    (hj : ∀ i, (j i).source = univ)
    (hmetric : ∀ i, ∀ x : U, ∀ v w : TangentSpace I x,
      (hSeq i).inner x v w = (gSeq i).inner (j i x)
        (mfderiv I I (j i : U → M i) x v) (mfderiv I I (j i : U → M i) x w))
    (hconv : ∀ C : Set U, IsCompact C →
      MetricCPConvergenceOn C 1 hSeq (g.restrictOpen U) (g.restrictOpen U))
    {C : Set U} (hC : IsCompact C)
    (hCnear : ∀ q ∈ C, (q : N) ∈ Metric.ball (n : N) 3)
    (hCaway : ∀ q ∈ C, (q : N) ≠ (n : N))
    (qSeq : ℕ → U) (hqSeq : ∀ i, qSeq i ∈ C)
    (wSeq : ∀ i, TangentSpace I (j i (qSeq i)))
    (hwSeq : ∀ i, wSeq i ∈ inwardMinimizingDirections (gSeq i) (hSeqNorm i)
      (j i n) (j i (qSeq i))) :
    ∃ xInf : TangentBundle I U, xInf.proj ∈ C ∧
      (xInf.snd : E) ∈ inwardMinimizingDirections g hNorm (n : N) (xInf.proj : N) ∧
      ∃ phi : ℕ → ℕ, StrictMono phi ∧ Tendsto
        (fun i => (⟨qSeq (phi i), mfderiv I I ((j (phi i)).symm : M (phi i) → U)
          (j (phi i) (qSeq (phi i))) (wSeq (phi i))⟩ : TangentBundle I U))
        atTop (𝓝 xInf) := by
  let hInf := g.restrictOpen U
  let : RiemannianBundle (fun x : U => TangentSpace I x) := ⟨hInf.toRiemannianMetric⟩
  let hNativeNorm : IsMetricNorm hInf := isMetricNorm_of_riemannianBundle hInf
  let : IsContinuousRiemannianBundle E (fun x : U => TangentSpace I x) :=
    hNativeNorm.isContinuousRiemannianBundle
  let : SecondCountableTopology H := I.secondCountableTopology
  let : SecondCountableTopology N := ChartedSpace.secondCountable_of_sigmaCompact H N
  let : LocallyCompactSpace U := Manifold.locallyCompact_of_finiteDimensional (M := U) I
  let : SigmaCompactSpace U := inferInstance
  have hconv0 (D : Set U) (hD : IsCompact D) :
      MetricCPConvergenceOn D 0 hSeq hInf hInf := by
    intro epsilon hepsilon
    obtain ⟨i0, hi0⟩ := hconv D hD (epsilon / 2) (half_pos hepsilon)
    refine ⟨i0, fun i hi => lt_of_le_of_lt ?_ (half_lt_self hepsilon)⟩
    apply metricDerivNormSupOn_le_of_forall D 0 (hSeq i) hInf hInf
      (epsilon / 2) (half_pos hepsilon).le
    intro a ha x hx
    exact (derivNorm_le_sup hD (by omega : a ≤ 1) (hSeq i) hInf hInf hx).trans
      (hi0 i hi).le
  have hsource (i : ℕ) (x : U) : x ∈ (j i).source := hj i ▸ mem_univ x
  obtain ⟨xInf, hxC, hxUnit, phi, hphi, hlim⟩ :=
    exists_inverse_metricUnit_tangent_subsequence hSeq hInf hNativeNorm hC (hconv0 C hC)
      gSeq j qSeq wSeq hqSeq (fun i => hsource i (qSeq i))
      (fun i x _hx v w => hmetric i x v w) (fun i => (hwSeq i).1)
  have hcpt := bufferedOpen_native_closedBall_compact g hNorm U n hbuffer
  have hbounds := (hconv0 (riemannianClosedBallOf hInf n 10) hcpt).eventually_quadratic_bounds
    hcpt (by norm_num : (0 : ℝ) < 1 / 100)
  obtain ⟨i0, hi0⟩ := eventually_atTop.1 hbounds
  have hshift : StrictMono (fun i : ℕ => i + i0) :=
    fun a b hab => Nat.add_lt_add_right hab i0
  let psi (i : ℕ) := phi (i + i0)
  have hpsi : StrictMono psi := hphi.comp hshift
  have hlimPsi : Tendsto
      (fun i => (⟨qSeq (psi i), mfderiv I I ((j (psi i)).symm : M (psi i) → U)
        (j (psi i) (qSeq (psi i))) (wSeq (psi i))⟩ : TangentBundle I U))
      atTop (𝓝 xInf) := hlim.comp hshift.tendsto_atTop
  let p (i : ℕ) : TangentBundle I U :=
    ⟨qSeq (psi i), mfderiv I I ((j (psi i)).symm : M (psi i) → U)
      (j (psi i) (qSeq (psi i))) (wSeq (psi i))⟩
  have hquad (i : ℕ) (x : U) (hx : x ∈ riemannianClosedBallOf hInf n 10)
      (v : TangentSpace I x) :
      (1 - (1 / 10 : ℝ)) ^ 2 * hInf.inner x v v ≤ (hSeq (psi i)).inner x v v ∧
      (hSeq (psi i)).inner x v v ≤ (1 + (1 / 10 : ℝ)) ^ 2 * hInf.inner x v v := by
    have hh := hi0 (psi i) (by
      have hh : i + i0 ≤ phi (i + i0) := hphi.le_apply
      dsimp only [psi]
      omega) x hx v
    have hn : 0 ≤ hInf.inner x v v := by
      by_cases hv : v = 0
      · simp [hv]
      · exact (hInf.pos x v hv).le
    constructor <;> nlinarith [hh.1, hh.2]
  have hdom (i : ℕ) (t : ℝ) (ht : t ∈ Icc 0 4) :
      (p i, t) ∈ (hSeq (psi i)).geodesicFlowDomain := by
    have hflow := bufferedUnitLift_eq_geodesicFlow hInf (hSeq (psi i)) (gSeq (psi i))
      (hSeqNorm (psi i)) (j (psi i)) n (lam := 1 / 10) (by norm_num) le_rfl
      hcpt (fun x _hx => hsource (psi i) x)
      (fun x hx v => by rw [← hmetric]; exact (hquad i x hx v).1)
      (fun x hx v => by rw [← hmetric]; exact (hquad i x hx v).2)
      (fun x _hx v w => hmetric (psi i) x v w)
      (bufferedOpen_native_near g hNorm U n (qSeq (psi i)) hbuffer
        (hCnear _ (hqSeq _))) (hwSeq (psi i)).1
    exact (hflow t ht).1
  have hdomInf (t : ℝ) (ht : t ∈ Icc 0 4) :
      (xInf, t) ∈ hInf.geodesicFlowDomain :=
    (bufferedOpenLimit_geodesicFlow_domain g hNorm U (n : N)
      (fun x hx => hbuffer (Metric.ball_subset_closedBall hx)) xInf.proj
      (hCnear _ hxC) xInf.snd hxUnit (by norm_num) (by norm_num) t ht).1
  have hconvPsi (D : Set U) (hD : IsCompact D) :
      MetricCPConvergenceOn D 1 (fun i => hSeq (psi i)) hInf hInf := by
    intro epsilon hepsilon
    obtain ⟨i0, hi0⟩ := hconv D hD epsilon hepsilon
    exact ⟨i0, fun i hi => hi0 (psi i) (hi.trans (show i ≤ psi i from hpsi.le_apply))⟩
  have hconvPsi0 : MetricCPConvergenceOn (riemannianClosedBallOf hInf n 10) 0
      (fun i => hSeq (psi i)) hInf hInf := by
    intro epsilon hepsilon
    obtain ⟨i1, hi1⟩ := hconv0 (riemannianClosedBallOf hInf n 10) hcpt epsilon hepsilon
    exact ⟨i1, fun i hi => hi1 (psi i) (hi.trans (show i ≤ psi i from hpsi.le_apply))⟩
  have hbase := (FiberBundle.continuous_proj E (TangentSpace I)).tendsto xInf
    |>.comp hlimPsi
  let ell (i : ℕ) := dist (j (psi i) n) (j (psi i) (qSeq (psi i)))
  let ellInf := dist (n : N) (xInf.proj : N)
  have hlength : Tendsto ell atTop (𝓝 ellInf) := by
    have hh := bufferedPullback_lengths_tendsto (fun i => hSeq (psi i)) hInf hInf
      (fun i => gSeq (psi i)) (fun i => j (psi i)) n hcpt hconvPsi0
      (Eventually.of_forall (fun i x _hx => hsource (psi i) x))
      (Eventually.of_forall (fun i x _hx v => hmetric (psi i) x v v))
      (fun i => qSeq (psi i))
      (bufferedOpen_native_near g hNorm U n xInf.proj hbuffer (hCnear _ hxC)) hbase
    have hd (i : ℕ) : riemannianEDistOf (gSeq i) (j i n) (j i (qSeq i)) =
        edist (j i n) (j i (qSeq i)) := by
      rw [riemannianEDistOf_eq_riemannianEDist (gSeq i) (hSeqNorm i),
        ← IsRiemannianManifold.out (I := I)]
    have hdistEq : riemannianEDistOf hInf n xInf.proj = edist (n : N) (xInf.proj : N) :=
      bufferedOpen_restricted_edist_eq g hNorm U n xInf.proj hbuffer (hCnear _ hxC)
    rw [hdistEq] at hh
    simpa only [hd, edist_dist, ENNReal.toReal_ofReal dist_nonneg] using hh
  have hell : ellInf ∈ Ioo (0 : ℝ) 4 := by
    refine ⟨dist_pos.mpr (hCaway _ hxC).symm, ?_⟩
    have hh := hCnear _ hxC
    rw [Metric.mem_ball, dist_comm] at hh
    exact hh.trans (by norm_num)
  have hinit : Tendsto (fun i => (hSeq (psi i)).geodesicFlow (p i) 0)
      atTop (𝓝 (hInf.geodesicFlow xInf 0)) := by
    have hz (i : ℕ) : (hSeq (psi i)).geodesicFlow (p i) 0 = p i :=
      (hSeq (psi i)).geodesicFlow_zero (r := ⊤) le_top (p i)
    have hzInf : hInf.geodesicFlow xInf 0 = xInf :=
      hInf.geodesicFlow_zero (r := ⊤) le_top xInf
    rw [hzInf]
    exact hlimPsi.congr' (Eventually.of_forall (fun i => (hz i).symm))
  have hflowLimit := geodesicFlow_tendsto_at_moving_time_of_metricCP
    (fun i => hSeq (psi i)) hInf hInf hconvPsi p xInf hell hdom hdomInf hinit ell hlength
  have hendpoint : ∀ᶠ i in atTop, ((hSeq (psi i)).geodesicFlow (p i) (ell i)).proj = n := by
    apply Eventually.of_forall
    intro i
    have hflow := bufferedReferenceLift_eq_geodesicFlow hInf (hSeq (psi i)) (gSeq (psi i))
      (hSeqNorm (psi i)) (j (psi i)) n (lam := 1 / 10) (by norm_num) le_rfl
      hcpt (fun x _hx => hsource (psi i) x)
      (fun x hx v => by rw [← hmetric]; exact (hquad i x hx v).1)
      (fun x hx v => by rw [← hmetric]; exact (hquad i x hx v).2)
      (fun x _hx v w => hmetric (psi i) x v w)
      (bufferedOpen_native_near g hNorm U n (qSeq (psi i)) hbuffer
        (hCnear _ (hqSeq _))) (hwSeq (psi i))
    have hh := congrArg TotalSpace.proj ((hflow (ell i) ⟨dist_nonneg, le_rfl⟩).2)
    change ((hSeq (psi i)).geodesicFlow (p i) (ell i)).proj =
      (j (psi i)).symm (intrinsicGeodesic (gSeq (psi i)) (hSeqNorm (psi i))
        (j (psi i) (qSeq (psi i))) (wSeq (psi i)) (ell i)) at hh
    rw [(hwSeq (psi i)).2] at hh
    exact hh.trans ((j (psi i)).left_inv (hsource (psi i) n))
  have hlimitEndpoint : (hInf.geodesicFlow xInf ellInf).proj = n := by
    have hh := (FiberBundle.continuous_proj E (TangentSpace I)).tendsto
      (hInf.geodesicFlow xInf ellInf) |>.comp hflowLimit
    exact tendsto_nhds_unique hh (tendsto_const_nhds.congr' (hendpoint.mono (fun _i hi => hi.symm)))
  have hambient := (bufferedOpenLimit_geodesicFlow_domain g hNorm U (n : N)
    (fun x hx => hbuffer (Metric.ball_subset_closedBall hx)) xInf.proj (hCnear _ hxC)
    xInf.snd hxUnit (by norm_num) (by norm_num) ellInf (Ioo_subset_Icc_self hell)).2
  have hunit : g.inner (xInf.proj : N) (xInf.snd : E) (xInf.snd : E) = 1 := hxUnit
  refine ⟨xInf, hxC, ⟨hunit, ?_⟩, psi, hpsi, hlimPsi⟩
  exact hambient.symm.trans (congrArg Subtype.val hlimitEndpoint)

private instance realFinrankPositive : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem realMetricNorm : IsMetricNorm (euclideanMetric (E := ℝ)) := by
  intro x v
  rw [← ofReal_norm, euclideanMetric_inner, real_inner_self_eq_norm_sq,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg v)]

private instance realRiemannianContinuous :
    IsContinuousRiemannianBundle ℝ (fun x : ℝ => TangentSpace 𝓘(ℝ, ℝ) x) :=
  realMetricNorm.isContinuousRiemannianBundle

theorem realOpen_inward_direction_limit
    (w : TangentSpace 𝓘(ℝ, ℝ) (1 : ℝ))
    (hw : w ∈ inwardMinimizingDirections (euclideanMetric (E := ℝ)) realMetricNorm 0 1) :
    let U : TopologicalSpace.Opens ℝ := ⟨Ioo (-11) 11, isOpen_Ioo⟩
    let q : U := ⟨1, by constructor <;> norm_num⟩
    let j := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := 𝓘(ℝ, ℝ)) U ⟨q⟩
    ∃ xInf : TangentBundle 𝓘(ℝ, ℝ) U, xInf.proj = q ∧
      (xInf.snd : ℝ) ∈ inwardMinimizingDirections (euclideanMetric (E := ℝ))
        realMetricNorm 0 (xInf.proj : ℝ) ∧
      ∃ phi : ℕ → ℕ, StrictMono phi ∧ Tendsto
        (fun _i : ℕ => (⟨q, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (j.symm : ℝ → U) 1 w⟩ :
          TangentBundle 𝓘(ℝ, ℝ) U)) atTop (𝓝 xInf) := by
  let g := euclideanMetric (E := ℝ)
  let U : TopologicalSpace.Opens ℝ := ⟨Ioo (-11) 11, isOpen_Ioo⟩
  let n : U := ⟨0, by constructor <;> norm_num⟩
  let q : U := ⟨1, by constructor <;> norm_num⟩
  let j := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := 𝓘(ℝ, ℝ)) U ⟨q⟩
  have hbuffer : Metric.closedBall (n : ℝ) 10 ⊆ U := by
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  obtain ⟨xInf, hxC, hxDir, phi, hphi, hlim⟩ := exists_subseq_inward_direction_limit
    (M := fun _i : ℕ => ℝ) g realMetricNorm U n hbuffer
    (fun _i : ℕ => g.restrictOpen U) (fun _i : ℕ => g) (fun _i : ℕ => realMetricNorm)
    (fun _i : ℕ => j) (fun _i : ℕ => rfl) (fun _i x v u => by
      change g.inner (x : ℝ) v u = g.inner (x : ℝ)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (Subtype.val : U → ℝ) x v)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (Subtype.val : U → ℝ) x u)
      rw [DifferentialGeometry.mfderiv_subtype_val_apply,
        DifferentialGeometry.mfderiv_subtype_val_apply])
    (fun C _hC epsilon hepsilon => ⟨0, fun _i _hi => by
      rw [metricDerivNormSupOn_self]; exact hepsilon⟩)
    (C := {q}) (isCompact_singleton : IsCompact {q})
    (fun x hx => by rw [mem_singleton_iff] at hx; subst x; norm_num [Metric.mem_ball, n, q])
    (fun x hx => by rw [mem_singleton_iff] at hx; subst x; norm_num [n, q])
    (fun _i : ℕ => q) (fun _i : ℕ => mem_singleton q) (fun _i : ℕ => w)
    (fun _i : ℕ => by
      change w ∈ inwardMinimizingDirections g realMetricNorm 0 1
      exact hw)
  refine ⟨xInf, mem_singleton_iff.mp hxC, hxDir, phi, hphi, ?_⟩
  change Tendsto (fun _i : ℕ => (⟨q,
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (j.symm : ℝ → U) 1 w⟩ :
      TangentBundle 𝓘(ℝ, ℝ) U)) atTop (𝓝 xInf) at hlim
  exact hlim

theorem realOpen_exists_inward_direction_limit :
    ∃ w : TangentSpace 𝓘(ℝ, ℝ) (1 : ℝ),
      w ∈ inwardMinimizingDirections (euclideanMetric (E := ℝ)) realMetricNorm 0 1 ∧
    let U : TopologicalSpace.Opens ℝ := ⟨Ioo (-11) 11, isOpen_Ioo⟩
    let q : U := ⟨1, by constructor <;> norm_num⟩
    let j := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := 𝓘(ℝ, ℝ)) U ⟨q⟩
    ∃ xInf : TangentBundle 𝓘(ℝ, ℝ) U, xInf.proj = q ∧
      (xInf.snd : ℝ) ∈ inwardMinimizingDirections (euclideanMetric (E := ℝ))
        realMetricNorm 0 (xInf.proj : ℝ) ∧
      ∃ phi : ℕ → ℕ, StrictMono phi ∧ Tendsto
        (fun _i : ℕ => (⟨q, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (j.symm : ℝ → U) 1 w⟩ :
          TangentBundle 𝓘(ℝ, ℝ) U)) atTop (𝓝 xInf) := by
  obtain ⟨w, hw⟩ := inwardMinimizingDirections_nonempty (euclideanMetric (E := ℝ))
    realMetricNorm (by norm_num : (0 : ℝ) ≠ 1)
  exact ⟨w, hw, realOpen_inward_direction_limit w hw⟩

end DifferentialGeometry.Geometry.Riemannian.Geodesic
