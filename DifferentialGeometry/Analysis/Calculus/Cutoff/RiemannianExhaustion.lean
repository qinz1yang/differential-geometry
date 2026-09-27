import DifferentialGeometry.Geometry.Metric.Distance.Cutoff
import DifferentialGeometry.Geometry.Metric.Distance.Approximation
import Mathlib.Topology.Compactness.SigmaCompact
import DifferentialGeometry.Geometry.Curvature.Bochner.Scalar.Basic
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Analysis

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

variable [I.Boundaryless]

omit [T2Space M] [SigmaCompactSpace M] [I.Boundaryless] in
theorem exists_sublevelCutoff_compactExhaustion
    (ρ : C^∞⟮I, M; ℝ⟯) (hsub : ∀ R : ℝ, IsCompact {x : M | ρ x ≤ R})
    (g : SmoothRiemannianMetric I M) {C : ℝ} (hC : 0 ≤ C)
    (hρ : ∀ x, ∀ v : TangentSpace I x,
      |mvfderiv I ρ x v| ≤ C * Real.sqrt (g.inner x v v))
    (Kex : CompactExhaustion M) :
    ∃ χ : ℕ → C^∞⟮I, M; ℝ⟯,
      (∀ n, HasCompactSupport (χ n)) ∧
      (∀ n x, χ n x ∈ Set.Icc 0 1) ∧
      (∀ n, ∀ x ∈ Kex n, χ n x = 1) ∧
      (∀ n x v, |mvfderiv I (χ n) x v| ≤
        CutoffProfile.derivBound * C * Real.sqrt (g.inner x v v)) ∧
      (∀ n x, Real.sqrt (g.inner x (Geometry.Operator.gradFun g (χ n) x)
        (Geometry.Operator.gradFun g (χ n) x)) ≤ CutoffProfile.derivBound * C) := by
  classical
  let B : ℕ → ℝ := fun n => Classical.choose
    ((Kex.isCompact n).bddAbove_image ρ.contMDiff.continuous.continuousOn)
  have hB : ∀ n, ∀ x ∈ Kex n, ρ x ≤ B n := by
    intro n x hx
    exact (Classical.choose_spec
      ((Kex.isCompact n).bddAbove_image ρ.contMDiff.continuous.continuousOn))
      (Set.mem_image_of_mem ρ hx)
  let R : ℕ → ℝ := fun n => max (n + 1 : ℝ) (B n)
  have hRpos : ∀ n, 0 < R n := by
    intro n
    exact lt_of_lt_of_le (by positivity : (0 : ℝ) < n + 1) (le_max_left _ _)
  have hRone : ∀ n, (1 : ℝ) ≤ R n := by
    intro n
    exact le_trans (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith : (1 : ℝ) ≤ n + 1)
      (le_max_left _ _)
  let χ : ℕ → C^∞⟮I, M; ℝ⟯ := fun n => sublevelCutoff ρ (R n)
  refine ⟨χ, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact hasCompactSupport_sublevelCutoff ρ (hRpos n) (hsub (2 * R n))
  · intro n x
    exact sublevelCutoff_mem_Icc ρ (R n) x
  · intro n x hx
    apply sublevelCutoff_eq_one ρ (hRpos n)
    exact (hB n x hx).trans (le_max_right _ _)
  · intro n x v
    have h := abs_mvfderiv_sublevelCutoff_le g ρ (hRpos n) hρ x v
    calc
      |mvfderiv I (χ n) x v| ≤ CutoffProfile.derivBound * C / R n *
          Real.sqrt (g.inner x v v) := by simpa [χ] using h
      _ ≤ CutoffProfile.derivBound * C * Real.sqrt (g.inner x v v) := by
        gcongr
        · exact div_le_self (mul_nonneg CutoffProfile.derivBound_nonneg hC)
            (hRone n)
  · intro n x
    have h := grad_norm_sublevelCutoff_le g ρ (hRpos n) hC hρ x
    calc
      Real.sqrt (g.inner x (Geometry.Operator.gradFun g (χ n) x)
          (Geometry.Operator.gradFun g (χ n) x)) ≤ CutoffProfile.derivBound * C / R n := by
            simpa [χ] using h
      _ ≤ CutoffProfile.derivBound * C := by
        exact div_le_self (mul_nonneg CutoffProfile.derivBound_nonneg hC)
          (hRone n)

end DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [PreconnectedSpace M]
  [NeZero (Module.finrank ℝ E)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_contMDiff_compactExhaustion_cutoff (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete g) (p : M) (Kex : CompactExhaustion M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ χ : ℕ → C^∞⟮I, M; ℝ⟯,
      (∀ n, HasCompactSupport (χ n)) ∧
      (∀ n x, |χ n x| ≤ 1) ∧
      (∀ n, ∀ x ∈ Kex n, χ n x = 1) ∧
      (∀ n x v, |mvfderiv I (χ n) x v| ≤ C * Real.sqrt (g.inner x v v)) ∧
      ∀ n x, Real.sqrt (g.inner x (Operator.gradFun g (χ n) x)
        (Operator.gradFun g (χ n) x)) ≤ C := by
  obtain ⟨ρ, _, hd, _, hc⟩ :=
    exists_contMDiff_riemannianDistance_approx_isCompact_sublevel g hg p (by norm_num : (0 : ℝ) < 1)
  obtain ⟨χ, hs, hr, hone, hdiff, hgrad⟩ :=
    Analysis.exists_sublevelCutoff_compactExhaustion ρ hc g (by norm_num) hd Kex
  refine ⟨Analysis.CutoffProfile.derivBound * 3,
    mul_nonneg Analysis.CutoffProfile.derivBound_nonneg (by norm_num),
    χ, hs, ?_, hone, hdiff, hgrad⟩
  intro n x
  rw [abs_of_nonneg (hr n x).1]
  exact (hr n x).2

end DifferentialGeometry.Geometry.Metric

end

noncomputable section

open Set
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry.Metric

open Tensor0SBundle Operator

variable {E H M T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [PreconnectedSpace M]
  [NeZero (Module.finrank ℝ E)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_contMDiff_compactExhaustion_cutoff_of_uniformEquivalent
    (g₀ : SmoothRiemannianMetric I M) (hg₀ : RiemannianMetricComplete g₀)
    (p : M) (Kex : CompactExhaustion M) (g : T → SmoothRiemannianMetric I M)
    (S : Set T) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hequiv : ∀ t ∈ S, ∀ x, ∀ v : TangentSpace I x,
      Λ⁻¹ * g₀.inner x v v ≤ (g t).inner x v v ∧
        (g t).inner x v v ≤ Λ * g₀.inner x v v) :
    ∃ L : ℝ, 0 ≤ L ∧ ∃ χ : ℕ → C^∞⟮I, M; ℝ⟯,
      (∀ n, HasCompactSupport (χ n)) ∧
      (∀ n x, |χ n x| ≤ 1) ∧
      (∀ n, ∀ x ∈ Kex n, χ n x = 1) ∧
      ∀ n, ∀ t ∈ S, ∀ x,
        normSq0S (g t) x 1 (differential1FormFun (χ n) x) ≤ L := by
  obtain ⟨C, _, χ, hs, hr, hone, _, hgrad⟩ :=
    exists_contMDiff_compactExhaustion_cutoff g₀ hg₀ p Kex
  refine ⟨Λ * C ^ 2, mul_nonneg (zero_le_one.trans hΛ) (sq_nonneg C),
    χ, hs, hr, hone, ?_⟩
  intro n t ht x
  have hbase : normSq0S g₀ x 1 (differential1FormFun (χ n) x) ≤ C ^ 2 := by
    rw [normSq0S_eq_inner, Curvature.inner0S_differential1FormFun_pair_eq_grad_inner]
    exact (Real.sqrt_le_iff.mp (hgrad n x)).2
  have h := normSq0S_upper_le_of_equiv g₀ (g t) x 1 hΛ (hequiv t ht x)
    (differential1FormFun (χ n) x)
  rw [pow_one] at h
  exact h.trans (mul_le_mul_of_nonneg_left hbase (zero_le_one.trans hΛ))

end DifferentialGeometry.Geometry.Metric
