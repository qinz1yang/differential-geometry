import DifferentialGeometry.Analysis.Calculus.MatrixRiccati
import DifferentialGeometry.Geometry.Comparison.Variation.JacobiGram

/-!
# Shape matrices of Jacobi families

This file packages the shape matrix of a linearly independent Jacobi family
and derives its trace Riccati equation.  The remaining geometric projection
identity is kept as an explicit hypothesis of the final theorem.
-/

noncomputable section

open Matrix
open scoped Matrix Manifold ContDiff Topology Matrix.Norms.Operator

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

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Gram matrix of the covariant derivatives of a finite field family. -/
def curveDerivGram (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j =>
    g.inner (γ t) (covDerivAlong (I := I) g γ (V i) t)
      (covDerivAlong (I := I) g γ (V j) t)

/-- Curvature matrix of a finite family along a curve. -/
def curveCurvGram (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j =>
    g.inner (γ t)
      ((DifferentialGeometry.Integral.Connection.riemannOp
        (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t))
        (V i t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t))
      (V j t)

/-- Shape matrix of a linearly independent field family. -/
def curveShape (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ) : Matrix ι ι ℝ :=
  (curveGram (I := I) g γ V t)⁻¹ * curveMixedGram (I := I) g γ V t

/-- Mean-curvature trace of a linearly independent field family. -/
def curveMean (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ) : ℝ :=
  trace (curveShape (I := I) g γ V t)

omit [Fintype ι] [DecidableEq ι] in
/-- For pointwise Jacobi fields, the mixed Gram derivative is curvature plus
the derivative-field Gram matrix. -/
theorem mixedDeriv_eq
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (hJ : ∀ i, IsJacobiAt (I := I) g γ (V i) t) :
    curveMixedDeriv (I := I) g γ V t =
      -curveCurvGram (I := I) g γ V t + curveDerivGram (I := I) g γ V t := by
  ext i j
  rw [curveMixedDeriv, curveCurvGram, curveDerivGram]
  simp only [Matrix.of_apply, Matrix.neg_apply, Matrix.add_apply]
  rw [jacobi_d2_eq (I := I) g γ (V i) (hJ i)]
  simp only [map_neg, ContinuousLinearMap.neg_apply]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [DecidableEq ι] in
/-- If the covariant derivatives have coefficient matrix `a`, Wronskian
symmetry identifies the mixed Gram matrix with `G * aᵀ`. -/
theorem mixed_eq_gram_mul
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (a : Matrix ι ι ℝ)
    (hDV : ∀ i, covDerivAlong (I := I) g γ (V i) t =
      ∑ k, a i k • V k t)
    (hW : ∀ i j, jacobiWronskian g γ (V i) (V j) t = 0) :
    curveMixedGram (I := I) g γ V t =
      curveGram (I := I) g γ V t * aᵀ := by
  classical
  ext i j
  have hw := sub_eq_zero.mp (hW i j)
  simp only [curveMixedGram, curveGram, Matrix.of_apply,
    Matrix.mul_apply, Matrix.transpose_apply]
  rw [hw, hDV j, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ContinuousLinearMap.map_smul, smul_eq_mul]
  ring

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
/-- The shape matrix is the transpose of any coefficient matrix expanding the
covariant derivatives in a linearly independent Wronskian-symmetric family. -/
theorem shape_eq_coeff
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (a : Matrix ι ι ℝ)
    (hDV : ∀ i, covDerivAlong (I := I) g γ (V i) t =
      ∑ k, a i k • V k t)
    (hLI : LinearIndependent ℝ fun i => V i t)
    (hW : ∀ i j, jacobiWronskian g γ (V i) (V j) t = 0) :
    curveShape (I := I) g γ V t = aᵀ := by
  have hdet : IsUnit (curveGram (I := I) g γ V t).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (curveGram_det_pos (I := I) g γ V t hLI))
  rw [curveShape, mixed_eq_gram_mul (I := I) g γ V t a hDV hW]
  exact Matrix.nonsing_inv_mul_cancel_left _ _ hdet

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
/-- If the covariant derivatives remain in the span of a linearly independent
Wronskian-symmetric family, their Gram matrix is the shape projection
`M G⁻¹ M`. -/
theorem derivGram_eq_proj
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (a : Matrix ι ι ℝ)
    (hDV : ∀ i, covDerivAlong (I := I) g γ (V i) t =
      ∑ k, a i k • V k t)
    (hLI : LinearIndependent ℝ fun i => V i t)
    (hW : ∀ i j, jacobiWronskian g γ (V i) (V j) t = 0) :
    curveDerivGram (I := I) g γ V t =
      curveMixedGram (I := I) g γ V t *
        (curveGram (I := I) g γ V t)⁻¹ *
          curveMixedGram (I := I) g γ V t := by
  classical
  let G := curveGram (I := I) g γ V t
  let Mx := curveMixedGram (I := I) g γ V t
  have hD : curveDerivGram (I := I) g γ V t = Mx * aᵀ := by
    ext i j
    simp only [curveDerivGram, Mx, curveMixedGram, Matrix.of_apply,
      Matrix.mul_apply, Matrix.transpose_apply]
    rw [hDV j, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
    ring
  have hM : Mx = G * aᵀ :=
    mixed_eq_gram_mul (I := I) g γ V t a hDV hW
  have hdet : IsUnit G.det := by
    exact isUnit_iff_ne_zero.mpr
      (ne_of_gt (curveGram_det_pos (I := I) g γ V t hLI))
  calc
    curveDerivGram (I := I) g γ V t = Mx * aᵀ := hD
    _ = Mx * G⁻¹ * (G * aᵀ) := by
      symm
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left G aᵀ hdet]
    _ = Mx * G⁻¹ * Mx := by rw [hM]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [DecidableEq ι] in
/-- A maximal linearly independent family in the orthogonal complement of a
nonzero vector spans every vector perpendicular to that vector. -/
theorem exists_perp_coeff
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (Z : ι → TangentSpace I (γ t))
    (u : TangentSpace I (γ t))
    (hcard : Fintype.card ι = Module.finrank ℝ E - 1)
    (hu : 0 < g.inner (γ t) u u)
    (hVperp : ∀ i, g.inner (γ t) u (V i t) = 0)
    (hZperp : ∀ i, g.inner (γ t) u (Z i) = 0)
    (hLI : LinearIndependent ℝ fun i => V i t) :
    ∃ a : Matrix ι ι ℝ, ∀ i,
      Z i = ∑ k, a i k • V k t := by
  classical
  let φ : E →ₗ[ℝ] ℝ := (g.inner (γ t) u).toLinearMap
  let W : Submodule ℝ E := LinearMap.ker φ
  have hφu : 0 < φ u := hu
  have hφsurj : Function.Surjective φ := by
    intro c
    refine ⟨(c / φ u) • u, ?_⟩
    calc
      φ ((c / φ u) • u) = (c / φ u) • φ u := φ.map_smul (c / φ u) u
      _ = c := by
        rw [smul_eq_mul]
        exact div_mul_cancel₀ c hφu.ne'
  have hrange : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hφsurj
  have hfrange : Module.finrank ℝ ↥(LinearMap.range φ) = 1 := by
    rw [hrange]
    simp
  have hfinrankW : Module.finrank ℝ ↥W = Module.finrank ℝ E - 1 := by
    have hsum := LinearMap.finrank_range_add_finrank_ker φ
    rw [hfrange] at hsum
    have : Module.finrank ℝ ↥W = Module.finrank ℝ ↥(LinearMap.ker φ) := rfl
    rw [this]
    omega
  let vW : ι → W := fun i => ⟨V i t, hVperp i⟩
  let zW : ι → W := fun i => ⟨Z i, hZperp i⟩
  have hLIW : LinearIndependent ℝ vW := by
    apply LinearIndependent.of_comp W.subtype
    simpa only [Function.comp_apply, vW] using hLI
  have hcardW : Fintype.card ι = Module.finrank ℝ W :=
    hcard.trans hfinrankW.symm
  have hspan : Submodule.span ℝ (Set.range vW) = ⊤ :=
    hLIW.span_eq_top_of_card_eq_finrank' hcardW
  let bW : Module.Basis ι ℝ W := Module.Basis.mk hLIW hspan.ge
  have hbW (i : ι) : bW i = vW i := by
    simp only [bW, Module.Basis.coe_mk]
  let a : Matrix ι ι ℝ := fun i k => bW.repr (zW i) k
  refine ⟨a, ?_⟩
  intro i
  have hsum := bW.sum_repr (zW i)
  have hco := congrArg (fun z : W => (z : E)) hsum
  symm at hco
  simpa only [a, zW, vW, hbW, Submodule.coe_sum, Submodule.coe_smul_of_tower] using hco

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [DecidableEq ι] in
/-- Covariant-derivative specialization of `exists_perp_coeff`. -/
theorem exists_deriv_coeff
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (u : TangentSpace I (γ t))
    (hcard : Fintype.card ι = Module.finrank ℝ E - 1)
    (hu : 0 < g.inner (γ t) u u)
    (hVperp : ∀ i, g.inner (γ t) u (V i t) = 0)
    (hDVperp : ∀ i,
      g.inner (γ t) u (covDerivAlong (I := I) g γ (V i) t) = 0)
    (hLI : LinearIndependent ℝ fun i => V i t) :
    ∃ a : Matrix ι ι ℝ, ∀ i,
      covDerivAlong (I := I) g γ (V i) t = ∑ k, a i k • V k t :=
  exists_perp_coeff (I := I) g γ V t
    (fun i => covDerivAlong (I := I) g γ (V i) t) u
    hcard hu hVperp hDVperp hLI

/-- Trace Riccati equation for a Jacobi family, conditional only on the exact
projection identity for its derivative-field Gram matrix. -/
theorem hasDerivAt_mean
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hVdiff : ∀ i,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (V i) t) t)
    (hDVdiff : ∀ i,
      DifferentiableAt ℝ
        (chartRepAt (I := I) γ
          (fun s => covDerivAlong (I := I) g γ (V i) s) t) t)
    (hLI : LinearIndependent ℝ fun i => V i t)
    (hW : ∀ i j, jacobiWronskian g γ (V i) (V j) t = 0)
    (hJ : ∀ i, IsJacobiAt (I := I) g γ (V i) t)
    (hproj : curveDerivGram (I := I) g γ V t =
      curveMixedGram (I := I) g γ V t *
        (curveGram (I := I) g γ V t)⁻¹ *
          curveMixedGram (I := I) g γ V t) :
    HasDerivAt (curveMean (I := I) g γ V)
      (-trace ((curveGram (I := I) g γ V t)⁻¹ *
          curveCurvGram (I := I) g γ V t) -
        trace ((curveShape (I := I) g γ V t) ^ 2)) t := by
  have hGram :
      HasDerivAt (fun s => curveGram (I := I) g γ V s)
        ((2 : ℝ) • curveMixedGram (I := I) g γ V t) t := by
    refine (DifferentialGeometry.Analysis.hasDerivAt_matrix _ _ t fun i j =>
      hasDerivAt_gram (I := I) hn g γ V t hγ hVdiff i j).congr_deriv ?_
    exact gramDeriv_eq_two (I := I) g γ V t hW
  have hMixed :
      HasDerivAt (fun s => curveMixedGram (I := I) g γ V s)
        (-curveCurvGram (I := I) g γ V t +
          curveMixedGram (I := I) g γ V t *
            (curveGram (I := I) g γ V t)⁻¹ *
              curveMixedGram (I := I) g γ V t) t := by
    refine (DifferentialGeometry.Analysis.hasDerivAt_matrix _ _ t fun i j =>
      hasDerivAt_mixed (I := I) hn g γ V t hγ hVdiff hDVdiff i j).congr_deriv ?_
    rw [mixedDeriv_eq (I := I) g γ V t hJ, hproj]
  have hunit : IsUnit (curveGram (I := I) g γ V t) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr
      (ne_of_gt (curveGram_det_pos (I := I) g γ V t hLI))
  have hric := DifferentialGeometry.Analysis.hasDerivAt_riccati
    (fun s => curveGram (I := I) g γ V s)
    (fun s => curveMixedGram (I := I) g γ V s)
    (-curveCurvGram (I := I) g γ V t) t hGram hMixed hunit
  simpa only [curveMean, curveShape, Matrix.mul_neg, Matrix.trace_neg] using hric

/-- Trace Riccati equation when the Jacobi family and its covariant derivative
fill the orthogonal complement of a nonzero vector. -/
theorem hasDerivAt_mean_perp
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (u : TangentSpace I (γ t))
    (hcard : Fintype.card ι = Module.finrank ℝ E - 1)
    (hu : 0 < g.inner (γ t) u u)
    (hVperp : ∀ i, g.inner (γ t) u (V i t) = 0)
    (hDVperp : ∀ i,
      g.inner (γ t) u (covDerivAlong (I := I) g γ (V i) t) = 0)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hVdiff : ∀ i,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (V i) t) t)
    (hDVdiff : ∀ i,
      DifferentiableAt ℝ
        (chartRepAt (I := I) γ
          (fun s => covDerivAlong (I := I) g γ (V i) s) t) t)
    (hLI : LinearIndependent ℝ fun i => V i t)
    (hW : ∀ i j, jacobiWronskian g γ (V i) (V j) t = 0)
    (hJ : ∀ i, IsJacobiAt (I := I) g γ (V i) t) :
    HasDerivAt (curveMean (I := I) g γ V)
      (-trace ((curveGram (I := I) g γ V t)⁻¹ *
          curveCurvGram (I := I) g γ V t) -
        trace ((curveShape (I := I) g γ V t) ^ 2)) t := by
  obtain ⟨a, hDV⟩ := exists_deriv_coeff (I := I) g γ V t u hcard hu
    hVperp hDVperp hLI
  have hproj := derivGram_eq_proj (I := I) g γ V t a hDV hLI hW
  exact hasDerivAt_mean (I := I) hn g γ V t hγ hVdiff hDVdiff hLI hW hJ hproj

end Variation
end Riemannian
end Geometry
end DifferentialGeometry

end
