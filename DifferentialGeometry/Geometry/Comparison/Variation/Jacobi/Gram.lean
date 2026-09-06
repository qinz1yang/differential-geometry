import DifferentialGeometry.Analysis.Integration.Measure.Jacobian.Derivative
import DifferentialGeometry.Geometry.Comparison.Variation.Jacobi.Basic

open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Matrix Set
open scoped Matrix Manifold ContDiff Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

section Gram

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def curveGram (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => g.inner (γ t) (V i t) (V j t)

def curveGramDeriv (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j =>
    g.inner (γ t) (covDerivAlong (I := I) g γ (V i) t) (V j t) +
      g.inner (γ t) (V i t) (covDerivAlong (I := I) g γ (V j) t)

def curveMixedGram (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j =>
    g.inner (γ t) (covDerivAlong (I := I) g γ (V i) t) (V j t)

def curveMixedDeriv (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j =>
    g.inner (γ t)
        (covDerivAlong (I := I) g γ
          (fun s => covDerivAlong (I := I) g γ (V i) s) t)
        (V j t) +
      g.inner (γ t) (covDerivAlong (I := I) g γ (V i) t)
        (covDerivAlong (I := I) g γ (V j) t)

def curveDensity (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ) : ℝ :=
  Real.sqrt (curveGram (I := I) g γ V t).det

omit [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] [DecidableEq ι] in
theorem curveGram_rect
    {κ : Type*}
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t))
    (V' : κ → ∀ t, TangentSpace I (γ t)) (t : ℝ) (C : Matrix ι κ ℝ)
    (h : ∀ j, V' j t = ∑ i, C i j • V i t) :
    curveGram (I := I) g γ V' t =
      Cᵀ * curveGram (I := I) g γ V t * C := by
  ext i j
  have hexp :
      g.inner (γ t) (V' i t) (V' j t) =
        ∑ k, ∑ l, C k i * C l j * g.inner (γ t) (V k t) (V l t) := by
    rw [h i, h j]
    have hL :
        g.inner (γ t) (∑ k, C k i • V k t) =
          ∑ k, C k i • g.inner (γ t) (V k t) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun k _ =>
        ContinuousLinearMap.map_smul _ _ _
    rw [hL, _root_.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [_root_.smul_apply]
    have hR :
        g.inner (γ t) (V k t) (∑ l, C l j • V l t) =
          ∑ l, C l j * g.inner (γ t) (V k t) (V l t) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun l _ => by
        rw [map_smul, smul_eq_mul]
    rw [hR, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [curveGram, Matrix.of_apply, Matrix.mul_apply,
    Matrix.transpose_apply]
  rw [hexp, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

omit [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] [Fintype ι] [DecidableEq ι] in
theorem curveGram_herm
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ) :
    (curveGram (I := I) g γ V t).IsHermitian := by
  refine Matrix.IsHermitian.ext ?_
  intro i j
  simp only [star_trivial, curveGram, Matrix.of_apply]
  exact g.symm (γ t) (V j t) (V i t)

omit [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] [DecidableEq ι] in
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
    rw [hleft, _root_.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [_root_.smul_apply, map_sum, smul_eq_mul, Finset.mul_sum]
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

omit [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] [Fintype ι] [DecidableEq ι] in
theorem curveGram_posDef
    [Finite ι]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (hLI : LinearIndependent ℝ fun i => V i t) :
    (curveGram (I := I) g γ V t).PosDef := by
  classical
  let := Fintype.ofFinite ι
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (curveGram_herm (I := I) g γ V t) ?_
  intro c hc
  rw [curveGram_dotVec (I := I) g γ V t c]
  have hv_ne : (∑ i, c i • V i t) ≠ 0 := by
    intro hv
    rw [Fintype.linearIndependent_iff] at hLI
    exact hc (funext (hLI c hv))
  exact g.pos (γ t) _ hv_ne

omit [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
theorem curveGram_det_pos
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (hLI : LinearIndependent ℝ fun i => V i t) :
    0 < (curveGram (I := I) g γ V t).det :=
  (curveGram_posDef (I := I) g γ V t hLI).det_pos

omit [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
theorem curveDensity_pos
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (hLI : LinearIndependent ℝ fun i => V i t) :
    0 < curveDensity (I := I) g γ V t := by
  exact Real.sqrt_pos.mpr (curveGram_det_pos (I := I) g γ V t hLI)

omit [Fintype ι] [DecidableEq ι] in
omit [NeZero (Module.finrank ℝ E)]
  [T2Space M]
  [SigmaCompactSpace M] in
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

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
theorem curveDensity_cont
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hVdiff : ∀ i,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (V i) t) t) :
    ContinuousAt (curveDensity (I := I) g γ V) t := by
  apply Real.continuous_sqrt.continuousAt.comp
  apply (continuous_id.matrix_det).continuousAt.comp
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  exact (hasDerivAt_gram (I := I) hn g γ V t hγ hVdiff i j).continuousAt

omit [Fintype ι] [DecidableEq ι] in
omit [NeZero (Module.finrank ℝ E)]
  [T2Space M]
  [SigmaCompactSpace M] in
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

omit [NeZero (Module.finrank ℝ E)]
  [T2Space M]
  [SigmaCompactSpace M] in
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

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [Fintype ι] [DecidableEq ι] in
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

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [Fintype ι] [DecidableEq ι] in
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

omit [NeZero (Module.finrank ℝ E)]
  [T2Space M]
  [SigmaCompactSpace M] in
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

namespace VolumeComparison

open Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem curveGram_recomb
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V V' : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ) (C : Matrix ι ι ℝ)
    (h : ∀ i, V' i t = ∑ k, C k i • V k t) :
    curveGram (I := I) g γ V' t = Cᵀ * curveGram (I := I) g γ V t * C := by
  exact Variation.curveGram_rect (I := I) g γ V V' t C h

theorem curveDensity_reindex
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : κ → ∀ t, TangentSpace I (γ t)) (t : ℝ) (e : ι ≃ κ) :
    curveDensity (I := I) g γ (fun i => V (e i)) t
      = curveDensity (I := I) g γ V t := by
  rw [curveDensity, curveDensity]
  congr 1
  have hsub : curveGram (I := I) g γ (fun i => V (e i)) t
      = (curveGram (I := I) g γ V t).submatrix e e := by
    ext i j; simp only [curveGram, Matrix.of_apply, Matrix.submatrix_apply]
  rw [hsub, Matrix.det_submatrix_equiv_self]

theorem curveDensity_recomb
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V V' : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ) (C : Matrix ι ι ℝ)
    (h : ∀ i, V' i t = ∑ k, C k i • V k t) :
    curveDensity (I := I) g γ V' t = |C.det| * curveDensity (I := I) g γ V t := by
  rw [curveDensity, curveDensity, curveGram_recomb (I := I) g γ V V' t C h,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    show C.det * (curveGram (I := I) g γ V t).det * C.det
        = C.det ^ 2 * (curveGram (I := I) g γ V t).det from by ring,
    Real.sqrt_mul (sq_nonneg C.det), Real.sqrt_sq_eq_abs]

theorem curveGram_det_option
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : Option ι → ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (hperp : ∀ i, g.inner (γ t) (V none t) (V (some i) t) = 0) :
    (curveGram (I := I) g γ V t).det =
      g.inner (γ t) (V none t) (V none t) *
        (curveGram (I := I) g γ (fun i => V (some i)) t).det := by
  let e : Option ι ≃ ι ⊕ PUnit.{1} := Equiv.optionEquivSumPUnit ι
  let T := curveGram (I := I) g γ (fun i => V (some i)) t
  let D : Matrix PUnit.{1} PUnit.{1} ℝ :=
    Matrix.of fun _ _ => g.inner (γ t) (V none t) (V none t)
  have hblock : Matrix.reindex e e (curveGram (I := I) g γ V t) =
      Matrix.fromBlocks T 0 0 D := by
    ext a b
    rcases a with i | a
    · rcases b with j | b
      · rfl
      · cases b
        change g.inner (γ t) (V (some i) t) (V none t) = 0
        rw [g.symm]
        exact hperp i
    · cases a
      rcases b with j | b
      · exact hperp j
      · cases b
        rfl
  rw [← Matrix.det_reindex_self e, hblock, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_unique D]
  exact mul_comm _ _

theorem curveDensity_option
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : Option ι → ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (hperp : ∀ i, g.inner (γ t) (V none t) (V (some i) t) = 0) :
    curveDensity (I := I) g γ V t =
      Real.sqrt (g.inner (γ t) (V none t) (V none t)) *
        curveDensity (I := I) g γ (fun i => V (some i)) t := by
  rw [curveDensity, curveDensity, curveGram_det_option (I := I) g γ V t hperp,
    Real.sqrt_mul (metric_inner_self_nonneg (I := I) g (γ t) (V none t))]

theorem curveDensity_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t c : ℝ) :
    curveDensity (I := I) g γ (fun i => c • V i) t =
      |c| ^ Fintype.card ι * curveDensity (I := I) g γ V t := by
  have h := VolumeComparison.curveDensity_recomb (I := I) g γ V
    (fun i => c • V i) t (Matrix.diagonal fun _ => c) (fun i => by
      simp only [Matrix.diagonal_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hki
        simp [hki]
      · simp)
  simpa only [Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, abs_pow] using h


end VolumeComparison

end Riemannian
end Geometry
end DifferentialGeometry

end
