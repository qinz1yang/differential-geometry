import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.MetricCurvatureDifference
import DifferentialGeometry.Geometry.Curvature.Bochner.OrthonormalFrameTrace
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Continuity
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Compactification.OnePoint.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff _root_.Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M]

local instance compactScalarConvergenceOne : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

local instance compactScalarConvergenceTopSucc :
    IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
  change IsManifold I ∞ M
  infer_instance

omit [CompleteSpace E] [T2Space M] [BoundarylessManifold I M] in
private theorem compactScalar_inner_abs (g : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    |g.inner x v w| ≤ Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) := by
  let D := (tangentMetricDataGen (I := I) g x).metric
  let _ : InnerProductSpace.Core ℝ (TangentSpace I x) := D.toCore
  let _ : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ (TangentSpace I x) _ _ _ D.toCore
  let _ : InnerProductSpace ℝ (TangentSpace I x) :=
    @InnerProductSpace.ofCore ℝ (TangentSpace I x) _ _ _ D.toCore.toCore
  have hi (a b : TangentSpace I x) : g.inner x a b = inner ℝ a b := by
    rw [← TangentMetricDataGen.inner_eq_gen (tangentMetricDataGen (I := I) g x) a b]
    exact (MetricFiberData.toCore_inner D a b).symm
  simp only [hi, real_inner_self_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_norm]
  exact abs_real_inner_le_norm v w

private theorem compactScalar_diagonal_sum {Idx : Type*} [Fintype Idx]
    [DecidableEq Idx] (mu : Idx → ℝ) (i : Idx) (f : Idx → ℝ) :
    (∑ j, diagonalInvMetric mu i j * f j) = mu i * f i := by
  simp [diagonalInvMetric]

private theorem compactScalar_trace_diagonal {Idx : Type*} [Fintype Idx]
    [DecidableEq Idx] (g : SmoothRiemannianMetric I M) {x : M}
    (b : Module.Basis Idx ℝ (TangentSpace I x)) (mu : Idx → ℝ)
    (hi : MetricInverseInBasis (I := I) g x b (diagonalInvMetric mu)) :
    metricScalarAt (I := I) g x = ∑ i, mu i * ricciTensor (I := I) g x (b i) (b i) := by
  rw [metricScalarAt_def,
    metricTracePair0SAt_eq_sum_basis (I := I) g b (diagonalInvMetric mu) hi
      (metricRicciAt (I := I) g x)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [metricRicciAt_apply_eq_ricciTensor]
  exact compactScalar_diagonal_sum mu i (fun j => ricciTensor (I := I) g x (b i) (b j))

omit [BoundarylessManifold I M] in
private theorem compactScalar_equivalent_two
    (g h : SmoothRiemannianMetric I M) (x : M) {delta : ℝ}
    (hsmall : (Module.finrank ℝ E : ℝ) * delta ≤ 1 / 2)
    (hzero : metricDerivNorm (I := I) 0 h g g x ≤ delta) :
    MetricUniformEquivalentOn (I := I) {x} g h 2 := by
  have hquad (v : TangentSpace I x) :
      |h.inner x v v - g.inner x v v| ≤ (1 / 2 : ℝ) * g.inner x v v := by
    have ht := metricQuadFormDiff_le_metricDerivNorm (I := I) h g g x v
    have hc : (Module.finrank ℝ E : ℝ) * metricDerivNorm (I := I) 0 h g g x ≤
        1 / 2 :=
      (mul_le_mul_of_nonneg_left hzero (Nat.cast_nonneg _)).trans hsmall
    exact ht.trans (mul_le_mul_of_nonneg_right hc
      (DifferentialGeometry.metric_inner_self_nonneg g x v))
  have ht := metricUniformEquivalentOn_of_quadFormDiff (I := I)
    (K := {x}) (g := g) (h := h) (δ := 1 / 2) (by norm_num) (by norm_num)
    (fun y hy v => by
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact hquad v)
  norm_num at ht
  exact ht

omit [BoundarylessManifold I M] in
private theorem compactScalar_derivNorm_succ
    (g h : SmoothRiemannianMetric I M) (x : M) (a : ℕ) :
    metricDerivNorm (I := I) (a + 1) h g g x =
      metricCovDerivNorm (I := I) (a + 1) h g x := by
  unfold metricDerivNorm metricDiffCovDerivAt
  rw [covDeriv_self_succ]
  change Real.sqrt (normSq0S (I := I) g x (a + 1 + 2)
    (CheegerGromovCompactness.metricCovDeriv (I := I) h g (a + 1) x - 0)) = _
  rw [sub_zero]
  rfl

private theorem compactScalar_ricci_unit_difference
    (g h : SmoothRiemannianMetric I M) (x : M) {delta : ℝ}
    (heq : MetricUniformEquivalentOn (I := I) {x} g h 2)
    (hjet : ∀ a : ℕ, a ≤ 2 → metricDerivNorm (I := I) a h g g x ≤ delta)
    (v : TangentSpace I x) (hv : g.inner x v v = 1) :
    |ricciTensor (I := I) h x v v - ricciTensor (I := I) g x v v| ≤
      (Module.finrank ℝ E : ℝ) * (48 * delta + 384 * delta ^ 2) := by
  classical
  obtain ⟨b, hb⟩ := exists_orthonormal_basis (I := I) g x
  have hdim : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
  have h1 : metricCovDerivNorm (I := I) 1 h g x ≤ delta := by
    rw [← compactScalar_derivNorm_succ g h x 0]
    exact hjet 1 (by norm_num)
  have h2 : metricCovDerivNorm (I := I) 2 h g x ≤ delta := by
    rw [← compactScalar_derivNorm_succ g h x 1]
    exact hjet 2 (by norm_num)
  have hsplit : ricciTensor (I := I) h x v v - ricciTensor (I := I) g x v v =
      ∑ i : Fin (Module.finrank ℝ (TangentSpace I x)),
        g.inner x ((ricciEndo (I := I) h x v v - ricciEndo (I := I) g x v v) (b i))
          (b i) := by
    with_unfolding_all
      rw [ricciTensor_apply, ricciTensor_apply,
        ← map_sub (LinearMap.trace ℝ (TangentSpace I x)),
        trace_eq_ortho_sum (I := I) g x _ b hb]
      rfl
  have hterm (i : Fin (Module.finrank ℝ (TangentSpace I x))) :
      |g.inner x ((ricciEndo (I := I) h x v v - ricciEndo (I := I) g x v v) (b i))
        (b i)| ≤ 48 * delta + 384 * delta ^ 2 := by
    have hbi : g.inner x (b i) (b i) = 1 := by simpa only [ite_true] using hb i i
    have hr := riemannOp_difference_le_metric_jets heq h1 h2 (b i) v v
    simp only [hbi, hv, Real.sqrt_one, mul_one] at hr
    have hc := compactScalar_inner_abs g x
      ((ricciEndo (I := I) h x v v - ricciEndo (I := I) g x v v) (b i)) (b i)
    rw [hbi, Real.sqrt_one, mul_one] at hc
    change |g.inner x
      (riemannOp (cov := LeviCivita (I := I) h) x (b i) v v -
        riemannOp (cov := LeviCivita (I := I) g) x (b i) v v) (b i)| ≤ _ at hc
    exact hc.trans hr
  rw [hsplit]
  calc
    _ ≤ ∑ i : Fin (Module.finrank ℝ (TangentSpace I x)),
        |g.inner x ((ricciEndo (I := I) h x v v - ricciEndo (I := I) g x v v)
          (b i)) (b i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace I x)),
        (48 * delta + 384 * delta ^ 2) :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = _ := by
      simp [hdim]
      ring

theorem metricScalar_difference_le_relative_two_jets
    (g h : SmoothRiemannianMetric I M) (x : M) {delta Kb : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hsmall : (Module.finrank ℝ E : ℝ) * delta ≤ 1 / 2)
    (hjet : ∀ a : ℕ, a ≤ 2 → metricDerivNorm (I := I) a h g g x ≤ delta)
    (hKb : ∀ v : TangentSpace I x,
      |ricciTensor (I := I) g x v v| ≤ Kb * g.inner x v v) :
    |metricScalarAt (I := I) h x - metricScalarAt (I := I) g x| ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * (864 + 2 * Kb) * delta := by
  classical
  let n : ℝ := Module.finrank ℝ E
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hdim : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
  have heq := compactScalar_equivalent_two g h x hsmall (hjet 0 (by norm_num))
  obtain ⟨mu, b, hginv, hhinv, hmu0, hmu2⟩ :=
    exists_diagInv_of_metricUniformEquivalentOn (I := I) heq (Set.mem_singleton x)
  have hgi : MetricInverseInBasis (I := I) g x b
      (diagonalInvMetric (fun _ => (1 : ℝ))) := hginv
  have hhi : MetricInverseInBasis (I := I) h x b (diagonalInvMetric mu) := hhinv
  have hb (i j : Fin (Module.finrank ℝ (TangentSpace I x))) :
      g.inner x (b i) (b j) = if i = j then (1 : ℝ) else 0 := by
    have ht := (hgi i j).1
    rw [compactScalar_diagonal_sum] at ht
    simpa using ht
  have hbii (i : Fin (Module.finrank ℝ (TangentSpace I x))) :
      g.inner x (b i) (b i) = 1 := by
    simpa only [ite_true] using hb i i
  have hmu (i : Fin (Module.finrank ℝ (TangentSpace I x))) :
      mu i * h.inner x (b i) (b i) = 1 := by
    have ht := (hhi i i).1
    rw [compactScalar_diagonal_sum] at ht
    simpa using ht
  have hmuerr (i : Fin (Module.finrank ℝ (TangentSpace I x))) :
      |mu i - 1| ≤ 2 * n * delta := by
    have hq := metricQuadFormDiff_le_metricDerivNorm (I := I) h g g x (b i)
    rw [hbii, mul_one] at hq
    conv at hq => rhs; rw [hdim]
    have hqd : |h.inner x (b i) (b i) - 1| ≤ n * delta :=
      hq.trans (mul_le_mul_of_nonneg_left (hjet 0 (by norm_num)) hn)
    calc
      |mu i - 1| = |mu i * (1 - h.inner x (b i) (b i))| := by
        congr 1
        nlinarith [hmu i]
      _ = mu i * |h.inner x (b i) (b i) - 1| := by
        rw [abs_mul, abs_of_nonneg (hmu0 i), abs_sub_comm]
      _ ≤ 2 * (n * delta) :=
        mul_le_mul (hmu2 i) hqd (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  have hsG := compactScalar_trace_diagonal g b (fun _ => (1 : ℝ)) hgi
  have hsH := compactScalar_trace_diagonal h b mu hhi
  have hsplit : metricScalarAt (I := I) h x - metricScalarAt (I := I) g x =
      ∑ i : Fin (Module.finrank ℝ (TangentSpace I x)),
        (mu i * (ricciTensor (I := I) h x (b i) (b i) -
          ricciTensor (I := I) g x (b i) (b i)) +
        (mu i - 1) * ricciTensor (I := I) g x (b i) (b i)) := by
    rw [hsH, hsG, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hdd : delta ^ 2 ≤ delta := by nlinarith
  have hterm (i : Fin (Module.finrank ℝ (TangentSpace I x))) :
      |mu i * (ricciTensor (I := I) h x (b i) (b i) -
        ricciTensor (I := I) g x (b i) (b i)) +
        (mu i - 1) * ricciTensor (I := I) g x (b i) (b i)| ≤
      n * (864 + 2 * Kb) * delta := by
    have hr := compactScalar_ricci_unit_difference g h x heq hjet (b i) (hbii i)
    have hg := hKb (b i)
    rw [hbii, mul_one] at hg
    have hfirst : |mu i * (ricciTensor (I := I) h x (b i) (b i) -
        ricciTensor (I := I) g x (b i) (b i))| ≤
        2 * (n * (48 * delta + 384 * delta ^ 2)) := by
      rw [abs_mul, abs_of_nonneg (hmu0 i)]
      exact mul_le_mul (hmu2 i) hr (abs_nonneg _) (by norm_num)
    have hsecond : |(mu i - 1) * ricciTensor (I := I) g x (b i) (b i)| ≤
        (2 * n * delta) * Kb := by
      rw [abs_mul]
      exact mul_le_mul (hmuerr i) hg (abs_nonneg _) (by positivity)
    refine (abs_add_le _ _).trans ((add_le_add hfirst hsecond).trans ?_)
    have hc : 48 * delta + 384 * delta ^ 2 ≤ 432 * delta := by linarith
    have hh := mul_le_mul_of_nonneg_left hc (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hn)
    nlinarith
  rw [hsplit]
  calc
    _ ≤ ∑ i : Fin (Module.finrank ℝ (TangentSpace I x)),
        |mu i * (ricciTensor (I := I) h x (b i) (b i) -
          ricciTensor (I := I) g x (b i) (b i)) +
          (mu i - 1) * ricciTensor (I := I) g x (b i) (b i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace I x)), n * (864 + 2 * Kb) * delta :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = _ := by simp [n, hdim]; ring

theorem metricScalar_uniform_convergence_of_relative_two_jets [CompactSpace M]
    (gSeq : ℕ → SmoothRiemannianMetric I M) (g : SmoothRiemannianMetric I M)
    (hconv : ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∀ a : ℕ, a ≤ 2 → ∀ x : M,
        metricDerivNorm (I := I) a (gSeq k) g g x < eps) :
    ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ x : M,
      |metricScalarAt (I := I) (gSeq k) x - metricScalarAt (I := I) g x| < eps := by
  obtain ⟨Kb, hKb0, hKb⟩ := exists_ricci_bound (I := I) g
  let n : ℝ := Module.finrank ℝ E
  let C : ℝ := n ^ 2 * (864 + 2 * Kb)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  intro eps heps
  let delta : ℝ := min 1 (min (1 / (2 * (n + 1))) (eps / (C + 1)))
  have hd0 : 0 < delta := by dsimp only [delta]; positivity
  have hd1 : delta ≤ 1 := min_le_left _ _
  have hdn : delta ≤ 1 / (2 * (n + 1)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hde : delta ≤ eps / (C + 1) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hsmall : n * delta ≤ 1 / 2 := by
    have hden : 0 < 2 * (n + 1) := by positivity
    have ht := (le_div_iff₀ hden).mp hdn
    nlinarith [hd0.le]
  obtain ⟨k0, hk0⟩ := hconv delta hd0
  refine ⟨k0, fun k hk x => ?_⟩
  have ht := metricScalar_difference_le_relative_two_jets g (gSeq k) x hd0.le hd1
    hsmall (fun a ha => (hk0 k hk a ha x).le) (hKb x)
  have hfrac : C * (eps / (C + 1)) < eps := by
    have hden : 0 < C + 1 := by positivity
    have hid : (eps / (C + 1)) * (C + 1) = eps := div_mul_cancel₀ eps hden.ne'
    have hpos : 0 < eps / (C + 1) := by positivity
    nlinarith
  exact ht.trans_lt ((mul_le_mul_of_nonneg_left hde hC).trans_lt hfrac)

theorem metricScalar_uniform_convergence_of_metricCInf [CompactSpace M]
    (gSeq : ℕ → SmoothRiemannianMetric I M) (g : SmoothRiemannianMetric I M)
    (hconv : MetricCInfConvergenceOnCompacts (I := I) gSeq g g) :
    ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ x : M,
      |metricScalarAt (I := I) (gSeq k) x - metricScalarAt (I := I) g x| < eps := by
  apply metricScalar_uniform_convergence_of_relative_two_jets gSeq g
  intro eps heps
  obtain ⟨k0, hk0⟩ := hconv Set.univ isCompact_univ 2 eps heps
  refine ⟨k0, fun k hk a ha x => ?_⟩
  exact (derivNorm_le_sup (I := I) isCompact_univ ha (gSeq k) g g
    (Set.mem_univ x)).trans_lt (hk0 k hk)

theorem metricScalar_joint_continuous_onePoint [CompactSpace M]
    (gSeq : ℕ → SmoothRiemannianMetric I M) (g : SmoothRiemannianMetric I M)
    (hconv : MetricCInfConvergenceOnCompacts (I := I) gSeq g g) :
    Continuous (fun p : OnePoint ℕ × M =>
      metricScalarAt (I := I) (p.1.elim g gSeq) p.2) := by
  let Rseq : ℕ → C(M, ℝ) := fun k =>
    ⟨fun x => metricScalarAt (I := I) (gSeq k) x, (metricScalar_smooth (gSeq k)).continuous⟩
  let Rinf : C(M, ℝ) :=
    ⟨fun x => metricScalarAt (I := I) g x, (metricScalar_smooth g).continuous⟩
  have hR : Tendsto Rseq atTop (𝓝 Rinf) := by
    rw [Metric.tendsto_atTop]
    intro eps heps
    obtain ⟨k0, hk0⟩ := metricScalar_uniform_convergence_of_metricCInf gSeq g hconv
      (eps / 2) (half_pos heps)
    refine ⟨k0, fun k hk => ?_⟩
    have hb : dist (Rseq k) Rinf ≤ eps / 2 := by
      apply (ContinuousMap.dist_le (half_pos heps).le).mpr
      intro x
      rw [Real.dist_eq]
      exact (hk0 k hk x).le
    exact hb.trans_lt (half_lt_self heps)
  let R : C(OnePoint ℕ, C(M, ℝ)) := OnePoint.continuousMapMkNat Rseq Rinf hR
  have hc := ContinuousMap.continuous_uncurry_of_continuous R
  refine hc.congr ?_
  intro p
  obtain ⟨t, x⟩ := p
  induction t using OnePoint.rec with
  | infty => rfl
  | coe k => rfl

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
