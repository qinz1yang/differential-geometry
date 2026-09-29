import DifferentialGeometry.Geometry.Metric.Coordinates.InverseGramPerturbation
import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.CoordinateBounds
import DifferentialGeometry.Geometry.Connection.ChartBridge.Curvature.BasisIdentityOffCenter
import DifferentialGeometry.Geometry.Curvature.Coordinates.ScalarTrace
import Mathlib.Topology.Compactness.LocallyFinite
import DifferentialGeometry.Geometry.Curvature.MetricDifference
import DifferentialGeometry.Geometry.Curvature.Bochner.OrthonormalFrameTrace
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Continuity
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Compactification.OnePoint.Basic

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open scoped Manifold ContDiff Topology BigOperators Matrix

open CheegerGromovCompactness Geometry.Operator Geometry.Connection Tensor.Coordinates
open Analysis.Spectral.DeTurckCoefficients
open Integral.DivergenceTheorem Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]

private theorem abs_metricScalarAt_sub_bound_on_chart
    (gRef : SmoothRiemannianMetric I M) (α : M)
    {K : Set M} (hK : IsCompact K)
    (hKchart : K ⊆ (chartAt H α).source)
    (lam B : Real) (hlam : 0 < lam) :
    ∃ C : Real, 0 < C ∧ ∀ u u' : SmoothRiemannianMetric I M,
      (∀ y ∈ K, ∀ ξ : TangentSpace I y,
        lam * gRef.inner y ξ ξ ≤ u.inner y ξ ξ) →
      (∀ y ∈ K, ∀ ξ : TangentSpace I y,
        lam * gRef.inner y ξ ξ ≤ u'.inner y ξ ξ) →
      (∀ y ∈ K, ∀ a : ℕ, a ≤ 2 →
        metricCovDerivNorm (I := I) a u gRef y ≤ B) →
      (∀ y ∈ K, ∀ a : ℕ, a ≤ 2 →
        metricCovDerivNorm (I := I) a u' gRef y ≤ B) →
      ∀ y ∈ K,
        |metricScalarAt (I := I) u y - metricScalarAt (I := I) u' y| ≤
          C * ∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y := by
  classical
  obtain ⟨Cric, hCric0, hCric⟩ :=
    exists_abs_chartRicciTensor_sub_le (I := I) gRef α hK hKchart lam B hlam
  obtain ⟨Cari, hCari0, hCari⟩ :=
    exists_abs_chartRicciTensor_le (I := I) gRef α hK hKchart lam B hlam
  obtain ⟨Minv, hMinv0, hMinv⟩ :=
    exists_abs_chartInvGramMatrix_le_of_lower_bound (I := I) gRef α hK
      (by rwa [trivializationAt_baseSet_eq_chartAt_source]) lam hlam
  obtain ⟨CJ, hCJ0, hCJ⟩ := exists_chartMetricJet2DiffSum_le (I := I) gRef α hK hKchart
  set nR : Real := (Module.finrank Real E : Real) with hnR
  have hnR0 : 0 ≤ nR := Nat.cast_nonneg _
  set Cinv : Real := nR ^ 2 * Minv ^ 2 with hCinv
  have hCinv0 : 0 ≤ Cinv := by rw [hCinv]; positivity
  set Ci : Real := Cinv * CJ with hCi
  have hCi0 : 0 ≤ Ci := by rw [hCi]; positivity
  set Ct : Real := Ci * Cari + Minv * Cric with hCt
  have hCt0 : 0 ≤ Ct := by rw [hCt]; positivity
  refine ⟨nR ^ 2 * Ct + 1, by positivity, ?_⟩
  intro u u' hlowu hlowu' hcovu hcovu' y hy
  set z : E := extChartAt I α y with hz
  set S : Real := ∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have hψ : (extChartAt I α).symm z = y := by
    rw [hz]
    exact (extChartAt I α).left_inv (by rw [extChartAt_source]; exact hKchart hy)
  have hybase : y ∈ (trivializationAt E (TangentSpace I : M → Type _) α).baseSet := by
    rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]
    exact hKchart hy
  have hyg : y ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α, extChartAt_source]
    exact hKchart hy
  have hMinvu' : ∀ i j : Fin (Module.finrank Real E),
      |chartInvGramOnE (I := I) u' α i j z| ≤ Minv := by
    intro i j
    rw [chartInvGramOnE_def, hψ]
    exact hMinv y hy u' (hlowu' y hy) i j
  have hInv : ∀ i j : Fin (Module.finrank Real E),
      |chartInvGramOnE (I := I) u α i j z - chartInvGramOnE (I := I) u' α i j z| ≤
        Ci * S := by
    intro i j
    have hmatrix := chartInvGramMatrix_entry_sub_abs_le_chartGramDiffSum (I := I) (M := M)
      u u' α hybase
      (fun p q => hMinv y hy u (hlowu y hy) p q)
      (fun p q => hMinv y hy u' (hlowu' y hy) p q) i j
    have hgram : DifferentialGeometry.Tensor.Coordinates.chartGramDiffSum (I := I) (M := M) u u' α y ≤
        DifferentialGeometry.Tensor.Coordinates.chartMetricJet2DiffSum (I := I) (M := M) u u' α z := by
      rw [← hψ]
      exact (DifferentialGeometry.Tensor.Coordinates.chartGramDiffSum_le_chartMetricJet1DiffSum (I := I) (M := M) u u' α z).trans
        (DifferentialGeometry.Tensor.Coordinates.chartMetricJet1DiffSum_le_chartMetricJet2DiffSum (I := I) (M := M) u u' α z)
    have hjet : DifferentialGeometry.Tensor.Coordinates.chartMetricJet2DiffSum (I := I) (M := M) u u' α z ≤ CJ * S := by
      rw [hz, hS]
      exact hCJ u u' y hy
    rw [chartInvGramOnE_def, chartInvGramOnE_def, hψ]
    calc
      |chartInvGramMatrix (I := I) u α y i j - chartInvGramMatrix (I := I) u' α y i j|
          ≤ Cinv * DifferentialGeometry.Tensor.Coordinates.chartGramDiffSum (I := I) (M := M) u u' α y := by
            rw [hCinv, hnR]
            exact hmatrix
      _ ≤ Cinv * DifferentialGeometry.Tensor.Coordinates.chartMetricJet2DiffSum (I := I) (M := M) u u' α z :=
        mul_le_mul_of_nonneg_left hgram hCinv0
      _ ≤ Cinv * (CJ * S) := mul_le_mul_of_nonneg_left hjet hCinv0
      _ = Ci * S := by rw [hCi]; ring
  have hscalar (w : SmoothRiemannianMetric I M) :
      metricScalarAt (I := I) w y =
        ∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
          chartInvGramOnE (I := I) w α i j z * chartRicciTensor (I := I) w α i j z := by
    rw [DifferentialGeometry.PDE.RicciFlow.metricScalar_chartTrace_eq (I := I) w α hyg]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [ricciTensor_chartBasisVec_alpha_eq (I := I) w α i j hyg, hz]
  rw [hscalar u, hscalar u']
  have hdiff :
      (∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
          chartInvGramOnE (I := I) u α i j z * chartRicciTensor (I := I) u α i j z) -
        (∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
          chartInvGramOnE (I := I) u' α i j z * chartRicciTensor (I := I) u' α i j z) =
      ∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
        ((chartInvGramOnE (I := I) u α i j z - chartInvGramOnE (I := I) u' α i j z) *
            chartRicciTensor (I := I) u α i j z +
          chartInvGramOnE (I := I) u' α i j z *
            (chartRicciTensor (I := I) u α i j z - chartRicciTensor (I := I) u' α i j z)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hdiff]
  have hterm : ∀ i j : Fin (Module.finrank Real E),
      |(chartInvGramOnE (I := I) u α i j z - chartInvGramOnE (I := I) u' α i j z) *
          chartRicciTensor (I := I) u α i j z +
        chartInvGramOnE (I := I) u' α i j z *
          (chartRicciTensor (I := I) u α i j z - chartRicciTensor (I := I) u' α i j z)| ≤
        Ct * S := by
    intro i j
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have hA := hCari u hlowu hcovu y hy i j
    have hR := hCric u u' hlowu hlowu' hcovu hcovu' y hy i j
    have h1 := mul_le_mul (hInv i j) hA (abs_nonneg _) (mul_nonneg hCi0 hS0)
    have h2 := mul_le_mul (hMinvu' i j) hR (abs_nonneg _) hMinv0
    rw [hCt]
    nlinarith
  calc
    |∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
        ((chartInvGramOnE (I := I) u α i j z - chartInvGramOnE (I := I) u' α i j z) *
            chartRicciTensor (I := I) u α i j z +
          chartInvGramOnE (I := I) u' α i j z *
            (chartRicciTensor (I := I) u α i j z - chartRicciTensor (I := I) u' α i j z))|
        ≤ ∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E), Ct * S := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          refine Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
          exact Finset.sum_le_sum fun j _ => hterm i j
    _ = nR ^ 2 * Ct * S := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [hnR]
      ring
    _ ≤ (nR ^ 2 * Ct + 1) * S := by nlinarith


theorem exists_abs_metricScalarAt_sub_le
    (gRef : SmoothRiemannianMetric I M)
    {K : Set M} (hK : IsCompact K)
    (lam B : Real) (hlam : 0 < lam) :
    ∃ C : Real, 0 < C ∧ ∀ u u' : SmoothRiemannianMetric I M,
      (∀ y ∈ K, ∀ ξ : TangentSpace I y,
        lam * gRef.inner y ξ ξ ≤ u.inner y ξ ξ) →
      (∀ y ∈ K, ∀ ξ : TangentSpace I y,
        lam * gRef.inner y ξ ξ ≤ u'.inner y ξ ξ) →
      (∀ y ∈ K, ∀ a : ℕ, a ≤ 2 →
        metricCovDerivNorm (I := I) a u gRef y ≤ B) →
      (∀ y ∈ K, ∀ a : ℕ, a ≤ 2 →
        metricCovDerivNorm (I := I) a u' gRef y ≤ B) →
      ∀ y ∈ K,
        |metricScalarAt (I := I) u y - metricScalarAt (I := I) u' y| ≤
          C * ∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y := by
  classical
  let ρ := chartAtlasPOU I M
  have hKα : ∀ α : M, IsCompact
      (K ∩ tsupport (fun y : M => (ρ α : M → Real) y)) := fun α =>
    hK.inter_right (isClosed_tsupport (fun y : M => (ρ α : M → Real) y))
  have hKchart : ∀ α : M,
      K ∩ tsupport (fun y : M => (ρ α : M → Real) y) ⊆ (chartAt H α).source := by
    intro α y hy
    exact (chartAtlasPOU_isSubordinate I M) α hy.2
  choose Cα hCα0 hCα using fun α : M =>
    abs_metricScalarAt_sub_bound_on_chart (I := I) gRef α (hKα α) (hKchart α) lam B hlam
  let A : Set M := {α : M | (Function.support (fun y : M => (ρ α : M → Real) y) ∩ K).Nonempty}
  have hA : A.Finite := by
    dsimp [A]
    exact ρ.locallyFinite.finite_nonempty_inter_compact hK
  let active : Finset M := hA.toFinset
  have hactive (α : M) : α ∈ active ↔
      (Function.support (fun y : M => (ρ α : M → Real) y) ∩ K).Nonempty := by
    change α ∈ hA.toFinset ↔
      (Function.support (fun y : M => (ρ α : M → Real) y) ∩ K).Nonempty
    rw [Set.Finite.mem_toFinset]
    rfl
  have hsum0 : 0 ≤ ∑ α ∈ active, Cα α :=
    Finset.sum_nonneg fun α _ => (hCα0 α).le
  refine ⟨(∑ α ∈ active, Cα α) + 1, by linarith, ?_⟩
  intro u u' hlowu hlowu' hcovu hcovu' y hy
  obtain ⟨α, hαpos⟩ := ρ.exists_pos_of_mem (Set.mem_univ y)
  have hysupp : y ∈ Function.support (fun z : M => (ρ α : M → Real) z) := ne_of_gt hαpos
  have hαS : α ∈ active := hactive α |>.2 ⟨y, hysupp, hy⟩
  have hyKα : y ∈ K ∩ tsupport (fun z : M => (ρ α : M → Real) z) :=
    ⟨hy, subset_closure hysupp⟩
  have hloc := hCα α u u'
    (fun z hz ξ => hlowu z hz.1 ξ)
    (fun z hz ξ => hlowu' z hz.1 ξ)
    (fun z hz a ha => hcovu z hz.1 a ha)
    (fun z hz a ha => hcovu' z hz.1 a ha)
    y hyKα
  have hCαle : Cα α ≤ ∑ β ∈ active, Cα β :=
    Finset.single_le_sum (fun β _ => (hCα0 β).le) hαS
  have hD0 : 0 ≤ ∑ q ∈ Finset.range 3,
      metricDerivNorm (I := I) q u u' gRef y :=
    Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  exact hloc.trans <| mul_le_mul_of_nonneg_right
    (hCαle.trans (le_add_of_nonneg_right zero_le_one)) hD0


end DifferentialGeometry.Geometry.Curvature

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
  let D := (tangentMetricData (I := I) g x).metric
  let _ : InnerProductSpace.Core ℝ (TangentSpace I x) := D.toCore
  let _ : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ (TangentSpace I x) _ _ _ D.toCore
  let _ : InnerProductSpace ℝ (TangentSpace I x) :=
    @InnerProductSpace.ofCore ℝ (TangentSpace I x) _ _ _ D.toCore.toCore
  have hi (a b : TangentSpace I x) : g.inner x a b = inner ℝ a b := by
    rw [← TangentMetricData.inner_eq (tangentMetricData (I := I) g x) a b]
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
