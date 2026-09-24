import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RecenteredScalarBoundReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedWitnessTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ScalarComparison
import DifferentialGeometry.Geometry.Metric.Convergence.Scalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Estimate.QuadraticForm
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Canonical.ReferenceChange
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.NoncollapseLocalization

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

section SliceBridge

variable {M N : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
  [T2Space N] [SigmaCompactSpace N]

private local instance sliceBridgeSourceC1 : IsManifold I3 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

private local instance sliceBridgeLimitC1 : IsManifold I3 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

omit [SigmaCompactSpace M] in
theorem metricDerivNorm_zero_le_of_equiv_pointwise
    (gk g₀ : SmoothRiemannianMetric I3 M) {C : ℝ} (hCge : 1 ≤ C) {y : M}
    (hbounds : ∀ v : TangentSpace I3 y,
      C⁻¹ * g₀.inner y v v ≤ gk.inner y v v ∧ gk.inner y v v ≤ C * g₀.inner y v v) :
    metricDerivNorm (I := I3) 0 gk g₀ g₀ y ≤
      4 * (Module.finrank ℝ (TangentSpace I3 y) : ℝ) * (C - 1) := by
  classical
  set nE : ℕ := Module.finrank ℝ (TangentSpace I3 y) with hnE
  obtain ⟨basis, hON⟩ := Tensor0SBundle.exists_orthonormal_basis (I := I3) g₀ y
  have hinv : Tensor0SBundle.MetricInverseInBasis (I := I3) g₀ y basis
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank ℝ (TangentSpace I3 y)))) := by
    have h := Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I3) g₀ basis hON
    intro i j
    simpa [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric] using h i j
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hCge
  have hq : ∀ v : TangentSpace I3 y,
      |gk.inner y v v - g₀.inner y v v| ≤ (C - 1) * g₀.inner y v v := by
    intro v
    have hgnn : 0 ≤ g₀.inner y v v := metric_inner_self_nonneg (I := I3) g₀ y v
    obtain ⟨hlow, hhigh⟩ := hbounds v
    have hCC : C⁻¹ * C = 1 := inv_mul_cancel₀ (ne_of_gt hCpos)
    have hinvnn : 0 ≤ C⁻¹ * g₀.inner y v v :=
      mul_nonneg (le_of_lt (inv_pos.mpr hCpos)) hgnn
    rw [abs_le]
    constructor <;> nlinarith [hlow, hhigh, hgnn, hCC, hinvnn, hCge,
      mul_nonneg hgnn hgnn]
  have hcomp := metricDifference_comp_le (I := I3) gk g₀ hCge y basis hON hq
  have hnsq : Tensor0SBundle.normSq0S (I := I3) g₀ y 2
        (metricDiffCovDerivAt (I := I3) 0 gk g₀ g₀ y) ≤
      (nE : ℝ) ^ 2 * (4 * (C - 1)) ^ 2 := by
    rw [Tensor0SBundle.normSq0S_identity_eq_sum_sq (I := I3) g₀ y 2 basis hinv _]
    have hterm : ∀ slots : Fin 2 → Fin nE,
        (Tensor0SBundle.component0S (I := I3) basis
          (metricDiffCovDerivAt (I := I3) 0 gk g₀ g₀ y) slots) ^ 2
          ≤ (4 * (C - 1)) ^ 2 := by
      intro slots
      have heq : Tensor0SBundle.component0S (I := I3) basis
            (metricDiffCovDerivAt (I := I3) 0 gk g₀ g₀ y) slots
          = gk.inner y (basis (slots 0)) (basis (slots 1))
            - g₀.inner y (basis (slots 0)) (basis (slots 1)) := by
        rw [Tensor0SBundle.component0S_apply]
        rw [show (fun a => basis (slots a))
            = vec2 (I := I3) (basis (slots 0)) (basis (slots 1)) from by
          funext a; fin_cases a <;> rfl]
        exact metricDiffCovDerivAt_zero_apply (I := I3) gk g₀ g₀ y _ _
      rw [heq, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hcomp (slots 0) (slots 1)) 2
    calc ∑ slots : Fin 2 → Fin nE,
            (Tensor0SBundle.component0S (I := I3) basis
              (metricDiffCovDerivAt (I := I3) 0 gk g₀ g₀ y) slots) ^ 2
        ≤ ∑ _slots : Fin 2 → Fin nE, (4 * (C - 1)) ^ 2 :=
          Finset.sum_le_sum (fun slots _ => hterm slots)
      _ = (nE : ℝ) ^ 2 * (4 * (C - 1)) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  have hCnn : 0 ≤ C - 1 := by linarith
  rw [metricDerivNorm]
  have hbnn : 0 ≤ 4 * (nE : ℝ) * (C - 1) := by positivity
  calc Real.sqrt (Tensor0SBundle.normSq0S (I := I3) g₀ y 2
          (metricDiffCovDerivAt (I := I3) 0 gk g₀ g₀ y))
      ≤ Real.sqrt ((nE : ℝ) ^ 2 * (4 * (C - 1)) ^ 2) := Real.sqrt_le_sqrt hnsq
    _ = 4 * (nE : ℝ) * (C - 1) := by
        rw [show (nE : ℝ) ^ 2 * (4 * (C - 1)) ^ 2 = (4 * (nE : ℝ) * (C - 1)) ^ 2
          from by ring, Real.sqrt_sq hbnn]

theorem metricComparisonOn_scalar_sub_le_of_ball
    {g₀ : SmoothRiemannianMetric I3 N} (hg₀ : RiemannianMetricComplete g₀)
    {p : N} {R : ℝ} (hR : 0 < R)
    {order : ℕ} {eps : ℝ} (heps0 : 0 ≤ eps) (heps1 : eps < 1) (horder : 2 ≤ order)
    {h : ℝ → SmoothRiemannianMetric I3 N} {g : ℝ → SmoothRiemannianMetric I3 M}
    {F : PartialDiffeomorph I3 I3 N M ∞} {J : Set ℝ}
    (C : MetricComparisonOn h g F (riemannianClosedBallOf (I := I3) g₀ p R) J order eps)
    {s : ℝ} (hs : s ∈ J) {Kb delta : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hsmall : (Module.finrank ℝ ThreeSpace : ℝ) * delta ≤ 1 / 2)
    (hepsd : eps ≤ delta)
    (hlambda : 4 * (Module.finrank ℝ ThreeSpace : ℝ) * (witnessLambda eps - 1) ≤ delta)
    (hKb : ∀ y ∈ riemannianClosedBallOf (I := I3) g₀ p R, ∀ v : TangentSpace I3 y,
      |ricciTensor (I := I3) (h s) y v v| ≤ Kb * (h s).inner y v v) :
    ∀ xu : sourceOpen F, (xu : N) ∈ riemannianClosedBallOf (I := I3) g₀ p R →
      |metricScalarAt (I := I3) (g s) (F xu) - metricScalarAt (I := I3) (h s) (xu : N)| ≤
        (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * (864 + 2 * Kb) * delta := by
  let _ : SigmaCompactSpace (sourceOpen F) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I3 (sourceOpen F).isOpen)
  intro xu hxu
  have hxuK : xu ∈
      (Subtype.val ⁻¹' riemannianClosedBallOf (I := I3) g₀ p R : Set (sourceOpen F)) := hxu
  have hEq := C.metricUniformEquivalentOn heps0 heps1 hs
  have hcov1 := C.metricCovDerivOrderBoundOn g₀ hg₀ p hR hs (a := 1) le_rfl (by omega)
  have hcov2 := C.metricCovDerivOrderBoundOn g₀ hg₀ p hR hs (a := 2) (by omega) horder
  have hjet : ∀ a : ℕ, a ≤ 2 →
      metricDerivNorm (I := I3) a (witnessPullbackMetric F g s) (witnessModelMetric F h s)
        (witnessModelMetric F h s) xu ≤ delta := by
    intro a ha
    interval_cases a
    · have hzero := metricDerivNorm_zero_le_of_equiv_pointwise
        (witnessPullbackMetric F g s) (witnessModelMetric F h s) hEq.1
        (fun v => hEq.2 xu hxuK v)
      have hfin : (Module.finrank ℝ (TangentSpace I3 xu) : ℝ) =
          (Module.finrank ℝ ThreeSpace : ℝ) := rfl
      have hstep : metricDerivNorm (I := I3) 0 (witnessPullbackMetric F g s)
          (witnessModelMetric F h s) (witnessModelMetric F h s) xu ≤
          4 * (Module.finrank ℝ ThreeSpace : ℝ) * (witnessLambda eps - 1) := by
        simpa only [hfin] using hzero
      exact hstep.trans hlambda
    · rw [metricDerivNorm_succ_self_reference (I := I3)
        (A := witnessPullbackMetric F g s) (gRef := witnessModelMetric F h s) 0 xu]
      exact (hcov1 xu hxuK).trans hepsd
    · rw [metricDerivNorm_succ_self_reference (I := I3)
        (A := witnessPullbackMetric F g s) (gRef := witnessModelMetric F h s) 1 xu]
      exact (hcov2 xu hxuK).trans hepsd
  have hKbU : ∀ v : TangentSpace I3 xu,
      |ricciTensor (I := I3) (witnessModelMetric F h s) xu v v| ≤
        Kb * (witnessModelMetric F h s).inner xu v v := by
    intro v
    have hv : mfderiv I3 I3 (Subtype.val : sourceOpen F → N) xu v = v :=
      mfderiv_subtype_val_apply (I := I3) (sourceOpen F) xu v
    change |ricciTensor (I := I3) ((h s).restrictOpen (sourceOpen F)) xu v v| ≤
      Kb * ((h s).restrictOpen (sourceOpen F)).inner xu v v
    rw [DifferentialGeometry.CheegerGromovCompactness.ricciTensor_restrictOpen, SmoothRiemannianMetric.restrictOpen_inner, hv]
    exact hKb (xu : N) hxu v
  have hmain := metricScalar_difference_le_relative_two_jets (I := I3)
    (g := witnessModelMetric F h s) (h := witnessPullbackMetric F g s) xu
    hdelta0 hdelta1 hsmall hjet hKbU
  simp only [witnessPullbackMetric, witnessModelMetric, openPullbackMetric_scalar,
    metricScalarAt_restrictOpen] at hmain
  exact hmain

end SliceBridge

theorem ricci_quadratic_form_bound_of_slice_rm_bound
    {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
    [T2Space N]
    {D : RealTimeInterval} (S : SolutionOn (I := I3) (M := N) D) {t C : ℝ}
    (hC : ∀ x : N, FlowMetricBall.rmNormSq S t x ≤ C) :
    ∀ (y : N) (v : TangentSpace I3 y),
      |ricciTensor (I := I3) (S.base.metric t) y v v| ≤
        (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt C *
          (S.base.metric t).inner y v v := by
  intro y v
  exact ricci_quadratic_form_bound_of_solution_curvature_bound (I := I3) S y v
    (by simpa only [FlowMetricBall.rmNormSq] using hC y)

theorem terminal_slice_scalar_transfer {kappa sigma : ℝ} {Phi : ℝ → ℝ} :
    TerminalSliceScalarTransfer.{u} kappa sigma Phi := by
  refine ⟨1, one_pos, ?_⟩
  intro eps heps hle
  refine ⟨1 / 4, by norm_num, by norm_num, ?_⟩
  intro X L J B s hs K hK
  have hIcc : Set.Icc s s ⊆ J.carrier := by
    simpa only [Set.Icc_self, Set.singleton_subset_iff] using hs
  have hrs : RiemannianMetricComplete (I := I3) (B.solution.base.metric s) :=
    ⟨MetricComplete.complete { L.space with metric := B.solution.base.metric s }
      (B.complete s hs)⟩
  obtain ⟨C, hC⟩ := B.compact_time_bound s s le_rfl hIcc
  have hC' : ∀ x : L.space.M,
      FlowMetricBall.rmNormSq B.solution s x ≤ max C 0 := fun x =>
    (hC s (Set.left_mem_Icc.mpr le_rfl) x).trans (le_max_left _ _)
  set Kb : ℝ := (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt (max C 0) with hKbdef
  have hKb : ∀ (y : L.space.M) (v : TangentSpace I3 y),
      |ricciTensor (I := I3) (B.solution.base.metric s) y v v| ≤
        Kb * (B.solution.base.metric s).inner y v v := by
    intro y v
    rw [hKbdef]
    exact ricci_quadratic_form_bound_of_slice_rm_bound B.solution hC' y v
  set nR : ℝ := (Module.finrank ℝ ThreeSpace : ℝ) with hnR
  have hnR0 : 0 ≤ nR := Nat.cast_nonneg _
  set delta : ℝ := min 1 (min (1 / (2 * (nR + 1)))
    (1 / (4 * (nR ^ 2 * (864 + 2 * Kb) + 1)))) with hdeltadef
  have hdelta_pos : 0 < delta := by
    rw [hdeltadef]
    exact lt_min one_pos (lt_min (by positivity) (by positivity))
  have hdelta_le_one : delta ≤ 1 := by rw [hdeltadef]; exact min_le_left _ _
  have hsmall : nR * delta ≤ 1 / 2 := by
    have h1 : delta ≤ 1 / (2 * (nR + 1)) := (min_le_right _ _).trans (min_le_left _ _)
    have h2 : (0 : ℝ) < 2 * (nR + 1) := by positivity
    have hm := (le_div_iff₀ h2).mp h1
    nlinarith [hnR0, hdelta_pos.le]
  have hnum : nR ^ 2 * (864 + 2 * Kb) * delta ≤ 1 / 4 := by
    have h1 : delta ≤ 1 / (4 * (nR ^ 2 * (864 + 2 * Kb) + 1)) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have h2 : (0 : ℝ) < 4 * (nR ^ 2 * (864 + 2 * Kb) + 1) := by positivity
    have hm := (le_div_iff₀ h2).mp h1
    have hpos : 0 ≤ nR ^ 2 * (864 + 2 * Kb) := by positivity
    nlinarith [hm, hpos]
  set eps' : ℝ := min 1 (min delta (delta / (8 * nR + 8))) with heps'def
  have heps'_pos : 0 < eps' := by
    rw [heps'def]
    exact lt_min one_pos (lt_min hdelta_pos (by positivity))
  have heps'_le_delta : eps' ≤ delta := (min_le_right _ _).trans (min_le_left _ _)
  have hdelta_le_half : delta ≤ 1 / 2 := by
    have h1 : delta ≤ 1 / (2 * (nR + 1)) := (min_le_right _ _).trans (min_le_left _ _)
    have h2 : (1 : ℝ) / (2 * (nR + 1)) ≤ 1 / 2 := by
      apply div_le_div_of_nonneg_left <;> linarith
    linarith
  have heps'_le_half : eps' ≤ 1 / 2 := heps'_le_delta.trans hdelta_le_half
  have heps'_lambda : 4 * nR * (witnessLambda eps' - 1) ≤ delta := by
    have hlam := witnessLambda_sub_one_le heps'_pos.le heps'_le_half
    have h1 : eps' ≤ delta / (8 * nR + 8) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have h2 : (0 : ℝ) < 8 * nR + 8 := by positivity
    have hm := (le_div_iff₀ h2).mp h1
    nlinarith [hlam, hm, hnR0]
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (ι := ↥K)
    (fun p : ↥K => riemannianBallOf (I := I3) (B.solution.base.metric s) (p : L.space.M) 1)
    (fun p => isOpen_riemannianBallOf (I := I3) (B.solution.base.metric s) (p : L.space.M) 1)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, by
      change riemannianEDistOf (I := I3) (B.solution.base.metric s) x x < ENNReal.ofReal 1
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr one_pos⟩)
  have hev : ∀ᶠ i in Filter.atTop, ∀ p ∈ t,
      riemannianClosedBallOf (I := I3) (B.solution.base.metric s) (p : L.space.M) 1 ⊆
          (L.maps.partialDiffeomorph (B.subseq i)).source ∧
        Nonempty (MetricComparisonOn (fun t => B.solution.base.metric t)
          (fun t => (X.term (L.subseq (B.subseq i))).S.base.metric t)
          (L.maps.partialDiffeomorph (B.subseq i))
          (riemannianClosedBallOf (I := I3) (B.solution.base.metric s) (p : L.space.M) 1)
          (Set.Icc s s) 2 eps') := by
    rw [Filter.eventually_all_finset]
    intro p _
    have hball : IsCompact (riemannianClosedBallOf (I := I3) (B.solution.base.metric s)
        (p : L.space.M) 1) :=
      RiemannianMetricComplete.closedEBall_isCompact hrs (p : L.space.M) 1
    filter_upwards [B.convergence (riemannianClosedBallOf (I := I3)
      (B.solution.base.metric s) (p : L.space.M) 1) hball s s le_rfl hIcc 2 eps'
      heps'_pos] with i hi
    exact ⟨hi.2.1, hi.2.2⟩
  filter_upwards [hev] with i hi
  intro y hy
  obtain ⟨p, hp, hyp⟩ := by
    simpa only [Set.mem_iUnion] using ht hy
  obtain ⟨hp_mem, hne⟩ := hi p hp
  have hyc : y ∈ riemannianClosedBallOf (I := I3) (B.solution.base.metric s)
      (p : L.space.M) 1 := by
    change riemannianEDistOf (I := I3) (B.solution.base.metric s) (p : L.space.M) y ≤
      ENNReal.ofReal 1
    exact le_of_lt hyp
  have hsrc : y ∈ (L.maps.partialDiffeomorph (B.subseq i)).source := hp_mem hyc
  obtain ⟨Cm⟩ := hne
  have hb := metricComparisonOn_scalar_sub_le_of_ball hrs (p := (p : L.space.M))
    (R := 1) one_pos (eps := eps') (heps0 := heps'_pos.le) (heps1 := by linarith)
    (horder := by norm_num) (order := 2) Cm (Set.left_mem_Icc.mpr le_rfl)
    (hdelta0 := hdelta_pos.le) (hdelta1 := hdelta_le_one) (hsmall := hsmall)
    (hepsd := heps'_le_delta) (hlambda := heps'_lambda)
    (hKb := fun y' _ v => hKb y' v) ⟨y, hsrc⟩ hyc
  rw [abs_sub_comm]
  exact hb.trans hnum

theorem uniform_moving_slice_propagation_of_recenteredSourceBound
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hsrc : RecenteredSourceBound.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ A D : ℝ, 0 ≤ D → ∃ C : ℝ,
        ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
          (J : RealTimeInterval) (B : BackwardExtension L J),
          ∀ s ∈ J.carrier, ∀ z y : L.space.M,
            B.solution.scalar s z ≤ A →
            metricDistance (B.solution.base.metric s) z y ≤ D →
              B.solution.scalar s y ≤ C :=
  uniform_moving_slice_propagation_of_recenteredSourceBound_and_scalarTransfer hsrc
    terminal_slice_scalar_transfer

theorem uniform_moving_slice_propagation_of_canonical_beyondRadius
    {kappa sigma c : ℝ} {Phi : ℝ → ℝ}
    (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) (hc : 0 < c)
    (hlocal : TerminalLocalPropagationBound.{u} kappa c)
    (hfar : RecenteredScalarBoundBeyondRadius.{u} kappa sigma Phi 1) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ A D : ℝ, 0 ≤ D → ∃ C : ℝ,
        ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
          (J : RealTimeInterval) (B : BackwardExtension L J),
          ∀ s ∈ J.carrier, ∀ z y : L.space.M,
            B.solution.scalar s z ≤ A →
            metricDistance (B.solution.base.metric s) z y ≤ D →
              B.solution.scalar s y ≤ C :=
  uniform_moving_slice_propagation_of_canonical_beyondRadius_and_scalarTransfer
    hsigma hPhi hc hlocal hfar terminal_slice_scalar_transfer

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
