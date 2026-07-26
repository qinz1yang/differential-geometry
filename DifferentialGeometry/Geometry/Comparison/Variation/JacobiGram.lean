import DifferentialGeometry.Analysis.Integration.Measure.JacobiFormula
import DifferentialGeometry.Geometry.Comparison.Variation.JacobiField

/-!
# Gram determinants of Jacobi families

This file differentiates the Gram matrix of a finite family of vector fields
along a curve.  Metric compatibility supplies the entry derivatives, Jacobi's
determinant formula supplies the density derivative, and vanishing pairwise
Wronskians reduce that derivative to the mixed Gram trace used in comparison
geometry.
-/

noncomputable section

open Matrix Set
open scoped Matrix Manifold ContDiff Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

section Gram

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Gram matrix of a finite family of vector fields along a curve. -/
def curveGram (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => g.inner (γ t) (V i t) (V j t)

/-- Entrywise derivative of `curveGram`, written using covariant derivatives
along the curve. -/
def curveGramDeriv (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j =>
    g.inner (γ t) (covDerivAlong (I := I) g γ (V i) t) (V j t) +
      g.inner (γ t) (V i t) (covDerivAlong (I := I) g γ (V j) t)

/-- Mixed Gram matrix pairing each covariant derivative with a field. -/
def curveMixedGram (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j =>
    g.inner (γ t) (covDerivAlong (I := I) g γ (V i) t) (V j t)

/-- Entrywise derivative of `curveMixedGram`. -/
def curveMixedDeriv (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j =>
    g.inner (γ t)
        (covDerivAlong (I := I) g γ
          (fun s => covDerivAlong (I := I) g γ (V i) s) t)
        (V j t) +
      g.inner (γ t) (covDerivAlong (I := I) g γ (V i) t)
        (covDerivAlong (I := I) g γ (V j) t)

/-- Square-root Gram determinant of a finite family along a curve. -/
def curveDensity (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ) : ℝ :=
  Real.sqrt (curveGram (I := I) g γ V t).det

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] [Fintype ι] [DecidableEq ι] in
/-- The Gram matrix of a finite tangent family is Hermitian. -/
theorem curveGram_herm
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ) :
    (curveGram (I := I) g γ V t).IsHermitian := by
  refine Matrix.IsHermitian.ext ?_
  intro i j
  simp only [star_trivial, curveGram, Matrix.of_apply]
  exact g.symm (γ t) (V j t) (V i t)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] [DecidableEq ι] in
/-- The Gram quadratic form is the metric norm-square of the corresponding
linear combination. -/
theorem curveGram_dotVec
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ) (c : ι → ℝ) :
    star c ⬝ᵥ (curveGram (I := I) g γ V t).mulVec c =
      g.inner (γ t) (∑ i, c i • V i t) (∑ j, c j • V j t) := by
  have hexpand :
      g.inner (γ t) (∑ i, c i • V i t) (∑ j, c j • V j t) =
        ∑ i, ∑ j, c i * c j * g.inner (γ t) (V i t) (V j t) := by
    have hleft :
        g.inner (γ t) (∑ i, c i • V i t) =
          ∑ i, c i • g.inner (γ t) (V i t) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => ContinuousLinearMap.map_smul _ _ _
    rw [hleft, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.smul_apply, map_sum, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
    ring
  rw [hexpand]
  simp only [dotProduct, Matrix.mulVec, curveGram, Matrix.of_apply,
    Pi.star_apply, star_trivial]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] [Fintype ι] [DecidableEq ι] in
/-- A Gram matrix is positive definite when the tangent family is linearly
independent. -/
theorem curveGram_posDef
    [Finite ι]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (hLI : LinearIndependent ℝ fun i => V i t) :
    (curveGram (I := I) g γ V t).PosDef := by
  classical
  letI := Fintype.ofFinite ι
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (curveGram_herm (I := I) g γ V t) ?_
  intro c hc
  rw [curveGram_dotVec (I := I) g γ V t c]
  have hv_ne : (∑ i, c i • V i t) ≠ 0 := by
    intro hv
    rw [Fintype.linearIndependent_iff] at hLI
    exact hc (funext (hLI c hv))
  exact g.pos (γ t) _ hv_ne

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
/-- Linear independence makes the Gram determinant strictly positive. -/
theorem curveGram_det_pos
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (hLI : LinearIndependent ℝ fun i => V i t) :
    0 < (curveGram (I := I) g γ V t).det :=
  (curveGram_posDef (I := I) g γ V t hLI).det_pos

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
/-- Linear independence makes the square-root Gram density strictly positive. -/
theorem curveDensity_pos
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (hLI : LinearIndependent ℝ fun i => V i t) :
    0 < curveDensity (I := I) g γ V t := by
  exact Real.sqrt_pos.mpr (curveGram_det_pos (I := I) g γ V t hLI)

omit [Fintype ι] [DecidableEq ι] in
/-- Metric compatibility differentiates each entry of the Gram matrix. -/
theorem hasDerivAt_gram
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hVdiff : ∀ i,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (V i) t) t)
    (i j : ι) :
    HasDerivAt (fun s => curveGram (I := I) g γ V s i j)
      (curveGramDeriv (I := I) g γ V t i j) t := by
  simpa only [curveGram, curveGramDeriv, Matrix.of_apply] using
    inner_deriv_at (I := I) hn g γ (V i) (V j) t hγ
      (hVdiff i) (hVdiff j)

omit [Fintype ι] [DecidableEq ι] in
/-- Metric compatibility differentiates each entry of the mixed Gram matrix. -/
theorem hasDerivAt_mixed
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hVdiff : ∀ j,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (V j) t) t)
    (hDVdiff : ∀ i,
      DifferentiableAt ℝ
        (chartRepAt (I := I) γ
          (fun s => covDerivAlong (I := I) g γ (V i) s) t) t)
    (i j : ι) :
    HasDerivAt (fun s => curveMixedGram (I := I) g γ V s i j)
      (curveMixedDeriv (I := I) g γ V t i j) t := by
  simpa only [curveMixedGram, curveMixedDeriv, Matrix.of_apply] using
    inner_deriv_at (I := I) hn g γ
      (fun s => covDerivAlong (I := I) g γ (V i) s) (V j) t hγ
      (hDVdiff i) (hVdiff j)

/-- Jacobi's formula for the square-root Gram determinant. -/
theorem hasDerivAt_curveDen
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hVdiff : ∀ i,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (V i) t) t)
    (hpos : 0 < (curveGram (I := I) g γ V t).det) :
    HasDerivAt (curveDensity (I := I) g γ V)
      ((1 / 2) * trace
          ((curveGram (I := I) g γ V t)⁻¹ *
            curveGramDeriv (I := I) g γ V t) *
        curveDensity (I := I) g γ V t) t := by
  apply DifferentialGeometry.Integral.Measure.hasDerivAt_sqrt_det_eq_half_trace_inv_mul
  · intro i j
    exact hasDerivAt_gram (I := I) hn g γ V t hγ hVdiff i j
  · exact hpos

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [Fintype ι] [DecidableEq ι] in
/-- Vanishing pairwise Wronskians identify the Gram derivative with twice the
mixed Gram matrix. -/
theorem gramDeriv_eq_two
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (hW : ∀ i j, jacobiWronskian g γ (V i) (V j) t = 0) :
    curveGramDeriv (I := I) g γ V t =
      (2 : ℝ) • curveMixedGram (I := I) g γ V t := by
  ext i j
  have hw := hW i j
  simp only [jacobiWronskian] at hw
  simp only [curveGramDeriv, curveMixedGram, Matrix.of_apply,
    Matrix.smul_apply, smul_eq_mul]
  linarith

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [Fintype ι] [DecidableEq ι] in
/-- Vanishing pairwise Wronskians make the mixed Gram matrix symmetric. -/
theorem mixedGram_symm
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (hW : ∀ i j, jacobiWronskian g γ (V i) (V j) t = 0) :
    (curveMixedGram (I := I) g γ V t).IsSymm := by
  refine Matrix.IsSymm.ext ?_
  intro i j
  have hw := sub_eq_zero.mp (hW i j)
  simp only [curveMixedGram, Matrix.of_apply]
  calc
    g.inner (γ t) (covDerivAlong (I := I) g γ (V j) t) (V i t) =
        g.inner (γ t) (V i t) (covDerivAlong (I := I) g γ (V j) t) :=
      g.symm (γ t) _ _
    _ = g.inner (γ t) (covDerivAlong (I := I) g γ (V i) t) (V j t) := hw.symm

/-- Wronskian symmetry simplifies the density derivative to the mixed Gram
trace. -/
theorem hasDerivAt_symmDen
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hVdiff : ∀ i,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (V i) t) t)
    (hpos : 0 < (curveGram (I := I) g γ V t).det)
    (hW : ∀ i j, jacobiWronskian g γ (V i) (V j) t = 0) :
    HasDerivAt (curveDensity (I := I) g γ V)
      (trace ((curveGram (I := I) g γ V t)⁻¹ *
          curveMixedGram (I := I) g γ V t) *
        curveDensity (I := I) g γ V t) t := by
  refine (hasDerivAt_curveDen (I := I) hn g γ V t hγ hVdiff hpos).congr_deriv ?_
  rw [gramDeriv_eq_two (I := I) g γ V t hW, Matrix.mul_smul,
    Matrix.trace_smul]
  simp only [smul_eq_mul]
  ring

end Gram

end Variation
end Riemannian
end Geometry
end DifferentialGeometry

end
