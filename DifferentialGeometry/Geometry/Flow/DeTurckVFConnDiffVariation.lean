import DifferentialGeometry.Geometry.Flow.VectorField
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciIdentitySmoothFrame
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini

/-!
# The DeTurck vector-field difference via the connection-difference trace

For a fixed background metric `g_bg` and two metrics `g₀`, `g₁` on a smooth manifold `M`,
the DeTurck vector fields `deTurckVF g₁ g_bg` and `deTurckVF g₀ g_bg` differ by an
expression governed by

* the **Christoffel variation** between the two perturbed metrics, encoded as the
  connection-difference tensor `connDiff g₁ g₀` traced against the cometric `g₁⁻¹`, and
* the **cometric difference** `g₁⁻¹ − g₀⁻¹` traced against the fixed background
  connection-difference `connDiff g₀ g_bg`.

This is the Lie-arm structural input to the Ricci–DeTurck linearization: it isolates the
dependence of the DeTurck vector field on a metric perturbation into the connection
variation `connDiff g₁ g₀` plus the inverse-metric variation, both linear-difference
objects.

The algebraic engine is the **cocycle identity** for the connection-difference tensor:
since `connDiff g g'` is the difference `∇^{LC}(g) − ∇^{LC}(g')` of Levi-Civita covariant
derivatives, it is additive in the telescoping sense
`connDiff g₁ g_bg = connDiff g₁ g₀ + connDiff g₀ g_bg`.

## Main results

* `connDiff_cocycle` — the telescoping additivity
  `connDiff g₁ g₂ x w v = connDiff g₁ g₀ x w v + connDiff g₀ g₂ x w v`.
* `deTurckVF_sub_eq_connDiff_trace` — the DeTurck vector-field difference decomposed into
  the cometric-`g₁⁻¹` trace of the Christoffel variation `connDiff g₁ g₀` plus the
  cometric-difference trace of the background connection difference `connDiff g₀ g_bg`.
* `deTurckVF_eq_orthoFrame_trace` — the **intrinsic** (chart-free) form of the DeTurck
  vector field: its value at `x` is the diagonal `g_x`-orthonormal-frame trace
  `∑ᵢ connDiff g g_bg x (Bᵢ x) (Bᵢ x)` of the connection-difference tensor, with
  `Bᵢ = smoothOrthoFrame g x i` the smooth `g`-orthonormal frame centred at `x`.  This
  lifts the chart-coordinate trace `deTurckVF_apply_eq` to a coordinate-free
  `g`-cometric contraction `tr_g(connDiff g g_bg)` — the intrinsic shape the Lie-arm
  grading consumes.
* `connDiff_symm` — the connection-difference tensor is **symmetric** in its two lower
  slots (the difference of two torsion-free Levi-Civita connections), the discharge
  partner of `cometric_skew_core` for the moving-frame correction.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace PDE
namespace DeTurck

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **Cocycle (telescoping additivity) for the connection-difference tensor.**

Since `connDiff g g'` is the difference `∇^{LC}(g) − ∇^{LC}(g')` of the two Levi-Civita
covariant derivatives, it telescopes through any intermediate metric `g₀`:
$$
  (\nabla_1 - \nabla_2) \;=\; (\nabla_1 - \nabla_0) + (\nabla_0 - \nabla_2).
$$
The proof realises the bilinear-map argument `w` as the value `σ x` of a smooth tangent
vector field `σ` (via `ContMDiffSection.exists_eq_at`) and applies the evaluation formula
`connDiff_apply` to each of the three connection differences; the Levi-Civita derivatives
of `σ` cancel telescopically. -/
theorem connDiff_cocycle (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (w v : TangentSpace I x) :
    connDiff (I := I) g₁ g₂ x w v =
      connDiff (I := I) g₁ g₀ x w v + connDiff (I := I) g₀ g₂ x w v := by
  classical
  obtain ⟨σ, hσx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x w
  have hσ : MDiffAt (T% fun y => σ y) x := σ.mdifferentiableAt
  have h12 := connDiff_apply (I := I) g₁ g₂ hσ v
  have h10 := connDiff_apply (I := I) g₁ g₀ hσ v
  have h02 := connDiff_apply (I := I) g₀ g₂ hσ v
  rw [hσx] at h12 h10 h02
  rw [h12, h10, h02]
  abel

/-- **The DeTurck vector-field difference via the connection-difference trace.**

For a fixed background metric `g_bg` and two metrics `g₀`, `g₁`, the difference of the
DeTurck vector fields decomposes, at each point `x`, as the sum of

* the cometric-`g₁⁻¹` trace of the **Christoffel variation** `connDiff g₁ g₀` between the
  two perturbed metrics, and
* the **cometric-difference** `g₁⁻¹ − g₀⁻¹` trace of the fixed background
  connection-difference `connDiff g₀ g_bg`,

both expressed in the chart-`x` coordinate frame `e_j = chartBasisVecFiber x j` with
inverse Gram matrices `G_∙^{jk} = chartInvGramMatrix g_∙ x x`:
$$
  W(g_1) - W(g_0)
    \;=\; \sum_{j,k} G_1^{jk}\, A_{10}(e_j, e_k)
        \;+\; \sum_{j,k} \bigl(G_1^{jk} - G_0^{jk}\bigr)\, A_{0,bg}(e_j, e_k),
$$
where `A_{10} = connDiff g₁ g₀ x` and `A_{0,bg} = connDiff g₀ g_bg x`.

This is the Lie-arm linearization input: the metric-perturbation dependence of the DeTurck
vector field is isolated into the connection variation `connDiff g₁ g₀` and the
inverse-metric variation `G₁ − G₀`.  The chart-trace formula `deTurckVF_apply_eq` supplies
each DeTurck vector field as the `g`-trace of its connection difference, and
`connDiff_cocycle` rewrites `connDiff g₁ g_bg = connDiff g₁ g₀ + connDiff g₀ g_bg`. -/
theorem deTurckVF_sub_eq_connDiff_trace
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (deTurckVF (I := I) g₁ g_bg :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x -
      (deTurckVF (I := I) g₀ g_bg :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
      (∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g₁ x x j k •
            connDiff (I := I) g₁ g₀ x
              (chartBasisVecFiber (I := I) x j x)
              (chartBasisVecFiber (I := I) x k x)) +
        ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) g₁ x x j k -
              chartInvGramMatrix (I := I) g₀ x x j k) •
            connDiff (I := I) g₀ g_bg x
              (chartBasisVecFiber (I := I) x j x)
              (chartBasisVecFiber (I := I) x k x) := by
  classical
  rw [deTurckVF_apply_eq (I := I) g₁ g_bg x, deTurckVF_apply_eq (I := I) g₀ g_bg x]
  rw [← Finset.sum_sub_distrib]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_sub_distrib]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [connDiff_cocycle (I := I) g₀ g₁ g_bg x
      (chartBasisVecFiber (I := I) x j x) (chartBasisVecFiber (I := I) x k x)]
  rw [smul_add]
  rw [sub_smul]
  abel

/-! ## The intrinsic (chart-free) DeTurck-VF trace -/

/-- The coordinate matrix, in the chart-`x` coordinate frame at `x`, of an arbitrary
tangent family `F : Fin n → T_x M`: the `m`-th model-basis component of the
trivialization extraction of `F i`. -/
private def famCoord (x : M) (F : Fin (Module.finrank ℝ E) → TangentSpace I x) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i m =>
    ((chartModelBasis E).repr
      ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x (F i))) m

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
/-- **Orthonormal coordinate matrix is Gram-orthogonal.**  For a `g_x`-orthonormal tangent
family `F` at `x`, its chart-`x` coordinate matrix `C = famCoord x F` satisfies
`C · G · Cᵀ = 1`, where `G = chartGramMatrix g x x`.  This is the orthonormality
`g(F i, F j) = δᵢⱼ` read through the chart-Gram bilinear expansion `g_inner_eq_chart_sum`. -/
private theorem famCoord_gram_eq_one (g : SmoothRiemannianMetric I M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet)
    (hxsrc : x ∈ (extChartAt I x).source)
    (F : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hF : ∀ i j, g.inner x (F i) (F j) = if i = j then 1 else 0) :
    famCoord (I := I) x F * chartGramMatrix (I := I) g x x *
        (famCoord (I := I) x F)ᵀ = 1 := by
  classical
  ext i j
  rw [Matrix.one_apply]
  have hexp := g_inner_eq_chart_sum (I := I) g x hx hxsrc (F i) (F j)
  rw [hF i j] at hexp
  have hchart : ∀ a b : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g x a b (extChartAt I x x) =
        chartGramMatrix (I := I) g x x a b := by
    intro a b; unfold chartGramOnE; rw [(extChartAt I x).left_inv hxsrc]
  rw [Matrix.mul_apply]
  rw [show (∑ a, (famCoord (I := I) x F * chartGramMatrix (I := I) g x x) i a *
        (famCoord (I := I) x F)ᵀ a j) =
      ∑ a, ∑ b, famCoord (I := I) x F i a * famCoord (I := I) x F j b *
        chartGramMatrix (I := I) g x x a b from by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Matrix.transpose_apply]; ring]
  rw [hexp]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [hchart a b]; rfl

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
/-- **The coordinate-matrix Gram identity** `(Cᵀ · C)ₘₙ = G^{mn}`.  For a `g_x`-orthonormal
tangent family `F` at `x` with chart-`x` coordinate matrix `C = famCoord x F`, the column
inner product `∑ᵢ Cᵢₘ Cᵢₙ` equals the inverse Gram matrix `chartInvGramMatrix g x x m n`.
This is the matrix inversion `C G Cᵀ = 1 ⟹ Cᵀ C = G⁻¹` (`famCoord_gram_eq_one` +
`Matrix.inv_eq_right_inv`); it carries an orthonormal-frame diagonal trace to the
`g⁻¹`-weighted chart trace. -/
private theorem sum_famCoord_eq_chartInvGram (g : SmoothRiemannianMetric I M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet)
    (hxsrc : x ∈ (extChartAt I x).source)
    (F : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hF : ∀ i j, g.inner x (F i) (F j) = if i = j then 1 else 0)
    (m n : Fin (Module.finrank ℝ E)) :
    (∑ i : Fin (Module.finrank ℝ E),
        famCoord (I := I) x F i m * famCoord (I := I) x F i n) =
      chartInvGramMatrix (I := I) g x x m n := by
  classical
  have h1 := famCoord_gram_eq_one (I := I) g hx hxsrc F hF
  have hC : famCoord (I := I) x F * (chartGramMatrix (I := I) g x x *
        (famCoord (I := I) x F)ᵀ) = 1 := by rw [← Matrix.mul_assoc]; exact h1
  have h2 : (chartGramMatrix (I := I) g x x * (famCoord (I := I) x F)ᵀ) *
        famCoord (I := I) x F = 1 := mul_eq_one_comm.mp hC
  rw [Matrix.mul_assoc] at h2
  have hinv : (famCoord (I := I) x F)ᵀ * famCoord (I := I) x F =
      (chartGramMatrix (I := I) g x x)⁻¹ := (Matrix.inv_eq_right_inv h2).symm
  have hmn := congrFun (congrFun hinv m) n
  rw [Matrix.mul_apply] at hmn
  rw [chartInvGramMatrix, ← hmn]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.transpose_apply]

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
/-- **Orthonormal-frame diagonal trace equals the chart-Gram trace.**  For a `g_x`-orthonormal
tangent family `F` at `x` and any continuous bilinear map `A : T_x M → T_x M → T_x M`, the
diagonal frame sum `∑ᵢ A(F i, F i)` equals the inverse-Gram chart trace
`∑_{m,n} G^{mn} • A(e_m, e_n)`, where `e = chartBasisVecFiber x`.  This is the linear-algebra
core converting a coordinate-free `g⁻¹`-contraction to its chart-coordinate form: each `F i`
recomposes in the chart basis (`chartBasisVecFiber_recompose`), bilinearity expands `A(F i, F i)`,
and the coordinate-matrix Gram identity `sum_famCoord_eq_chartInvGram` contracts the frame index. -/
private theorem bilin_ortho_family_diag_eq_chartGram_trace
    (g : SmoothRiemannianMetric I M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet)
    (hxsrc : x ∈ (extChartAt I x).source)
    (F : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hF : ∀ i j, g.inner x (F i) (F j) = if i = j then 1 else 0)
    (A : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) :
    (∑ i : Fin (Module.finrank ℝ E), A (F i) (F i)) =
      ∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x m n •
          A (chartBasisVecFiber (I := I) x m x) (chartBasisVecFiber (I := I) x n x) := by
  classical
  have hrec : ∀ i, F i =
      ∑ m, famCoord (I := I) x F i m • chartBasisVecFiber (I := I) x m x :=
    fun i => chartBasisVecFiber_recompose (I := I) x hx (F i)
  have hsummand : ∀ i, A (F i) (F i) =
      ∑ m, ∑ n, (famCoord (I := I) x F i m * famCoord (I := I) x F i n) •
        A (chartBasisVecFiber (I := I) x m x) (chartBasisVecFiber (I := I) x n x) := by
    intro i
    conv_lhs => rw [hrec i]
    have hfirst : A (∑ m, famCoord (I := I) x F i m • chartBasisVecFiber (I := I) x m x) =
        ∑ m, famCoord (I := I) x F i m • A (chartBasisVecFiber (I := I) x m x) := by
      rw [map_sum]; refine Finset.sum_congr rfl (fun m _ => ?_); rw [map_smul]
    rw [hfirst, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [ContinuousLinearMap.smul_apply, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [map_smul, smul_smul]
  rw [Finset.sum_congr rfl (fun i _ => hsummand i)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [← Finset.sum_smul]
  rw [sum_famCoord_eq_chartInvGram (I := I) g hx hxsrc F hF m n]

/-- **The DeTurck vector field as the intrinsic `g`-orthonormal-frame trace of the
connection difference.**

At each point `x`, the value of the bundled DeTurck vector field `deTurckVF g g_bg` is the
diagonal `g_x`-orthonormal-frame trace of the connection-difference tensor:
$$
  (\mathrm{deTurckVF}\,g\,g_{bg})\,x \;=\; \sum_i A\bigl(B_i(x), B_i(x)\bigr),
  \qquad A = \mathrm{connDiff}\,g\,g_{bg}\,x,
$$
where `Bᵢ = smoothOrthoFrame g x i` is the smooth `g`-orthonormal frame centred at `x`
(`g_x`-orthonormal by `smoothOrthoFrame_orthonormal_at_center`).

This is the **coordinate-free** form of the chart-trace formula `deTurckVF_apply_eq`: the
diagonal sum over a `g`-orthonormal frame is exactly the `g`-cometric (`g⁻¹`) contraction
`tr_g(connDiff g g_bg)` of the connection-difference tensor's two lower slots, with no chart
inverse-Gram matrix.  It is the intrinsic shape the Lie-arm `appCc` grading consumes — the
DeTurck vector field as `g^{jk}(Γ(g) − Γ̄(g_bg))^i_{jk}` read intrinsically.

The proof rewrites the chart-trace `deTurckVF_apply_eq` and applies the orthonormal-frame
collapse `bilin_ortho_family_diag_eq_chartGram_trace` (in reverse) to the
connection-difference bilinear map `connDiff g g_bg x`, with the orthonormal family
`Bᵢ x = smoothOrthoFrame g x i x`. -/
theorem deTurckVF_eq_orthoFrame_trace
    (g g_bg : SmoothRiemannianMetric I M) (x : M) :
    (deTurckVF (I := I) g g_bg :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
      ∑ i : Fin (Module.finrank ℝ E),
        connDiff (I := I) g g_bg x
          (smoothOrthoFrame (I := I) g x i x)
          (smoothOrthoFrame (I := I) g x i x) := by
  classical
  have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have hxsrc : x ∈ (extChartAt I x).source := mem_extChartAt_source x
  rw [deTurckVF_apply_eq (I := I) g g_bg x]
  rw [bilin_ortho_family_diag_eq_chartGram_trace (I := I) g hx hxsrc
    (fun i => smoothOrthoFrame (I := I) g x i x)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j)
    (connDiff (I := I) g g_bg x)]

/-- **The connection-difference tensor is symmetric in its two lower slots.**

For any two smooth Riemannian metrics `g`, `g'` and fibre vectors `w, v ∈ T_x M`,
$$
  \mathrm{connDiff}\,g\,g'\,x\,(w, v) \;=\; \mathrm{connDiff}\,g\,g'\,x\,(v, w).
$$
The connection difference `A = ∇^{LC}(g) − ∇^{LC}(g')` is the difference of two
**torsion-free** Levi-Civita connections (`LeviCivita_torsion_eq_zero`); the
non-tensorial Lie bracket `[·, ·]` cancels in the difference, so the antisymmetric part of
`A` vanishes.  The proof realises `w, v` as values of smooth sections
(`ContMDiffSection.exists_eq_at`), reduces `connDiff` to the Levi-Civita difference via
`connDiff_apply`, and applies the torsion-free identity `∇_X Y − ∇_Y X = [X, Y]` to each
connection (`CovariantDerivative.torsion_eq_zero_iff`); the brackets coincide and cancel.

This is the symmetry that, paired with the cometric skew core `cometric_skew_core`,
discharges the moving-frame correction in the covariant differentiation of the intrinsic
trace. -/
theorem connDiff_symm (g g' : SmoothRiemannianMetric I M) (x : M) (w v : TangentSpace I x) :
    connDiff (I := I) g g' x w v = connDiff (I := I) g g' x v w := by
  classical
  obtain ⟨σ, hσx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x w
  obtain ⟨τ, hτx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x v
  have hσ : MDiffAt (T% fun y => σ y) x := σ.mdifferentiableAt
  have hτ : MDiffAt (T% fun y => τ y) x := τ.mdifferentiableAt
  have hστ := connDiff_apply (I := I) g g' (σ := fun y => σ y) hσ (τ x)
  have hτσ := connDiff_apply (I := I) g g' (σ := fun y => τ y) hτ (σ x)
  have htor1 := (CovariantDerivative.torsion_eq_zero_iff (cov := LeviCivita (I := I) g)).mp
    (LeviCivita_torsion_eq_zero (I := I) g) (X := fun y => τ y) (Y := fun y => σ y) hτ hσ
  have htor0 := (CovariantDerivative.torsion_eq_zero_iff (cov := LeviCivita (I := I) g')).mp
    (LeviCivita_torsion_eq_zero (I := I) g') (X := fun y => τ y) (Y := fun y => σ y) hτ hσ
  rw [← hσx, ← hτx, hστ, hτσ]
  have hkey : (LeviCivita (I := I) g).toFun (fun y => σ y) x (τ x)
        - (LeviCivita (I := I) g).toFun (fun y => τ y) x (σ x)
      = (LeviCivita (I := I) g').toFun (fun y => σ y) x (τ x)
        - (LeviCivita (I := I) g').toFun (fun y => τ y) x (σ x) := by
    rw [htor1, htor0]
  have := hkey
  abel_nf
  abel_nf at this
  linear_combination (norm := abel) this

/-! ## The outer-`g` (minuend-connection) covariant derivative of `connDiff` -/

/-- **The minuend-connection covariant derivative of the connection-difference tensor differs
from the subtrahend-connection one by the connection-difference quadratic action.**

Write `A = connDiff g g_bg = ∇^{g} - ∇^{g_bg}` (the difference of the two Levi-Civita
connections, with `∇^{g}` the minuend and `∇^{g_bg}` the subtrahend).  The directional
covariant derivative of the `(1,2)`-tensor `A` along `X` taken with respect to the **minuend**
connection `∇^{g}` — the connection the Lie/Killing form `g(∇^{g}_v\,X, \cdot)` differentiates
with — written in the standard coordinate-free `(1,2)`-tensor form
`(∇^{g}_X A)(Y, Z) = ∇^{g}_X(A(Y, Z)) - A(∇^{g}_X Y, Z) - A(Y, ∇^{g}_X Z)`, equals the
**subtrahend** derivative `(∇^{g_bg}_X A)(Y, Z) = covDerivConnDiff g_bg g X Y Z x` plus the
connection-difference quadratic action of `A` on the three slots:
$$
  (\nabla^{g}_X A)(Y, Z)
    = (\nabla^{g_{bg}}_X A)(Y, Z)
      + A\bigl(A(Y, Z), X\bigr)
      - A\bigl(Z, A(Y, X)\bigr)
      - A\bigl(A(Z, X), Y\bigr),
$$
read in the project's `connDiff x · ·` argument convention (first argument the differentiated
section value, second the direction).  The slot signs were fixed by unfolding the `covDerivDiff`
structure and confirmed by a dimension-3/4 numeric check.

Since `∇^{g} = ∇^{g_bg} + A` on vector fields, the three differences in the `(1,2)`-tensor
covariant-derivative formula are each a single application of the connection-difference one-form:
the outer derivative contributes `A(A(Y, Z), X)` (`diff_eval` on the smooth section `A(Y, Z)`),
and the two slot-corrections contribute `-A(Z, A(Y, X))` and `-A(A(Z, X), Y)`
(`covApply_cov1_eq` rewriting `∇^{g}_X Y - ∇^{g_bg}_X Y = A(Y, X)` and likewise for `Z`,
followed by linearity of the bilinear `A`).  This is the outer-`g` differentiation bridge the
Lie-arm grading consumes to convert `∇^{g}(\mathrm{deTurckVF}\,g\,g_{bg})` into the
subtrahend-connection differentiated trace `covDerivConnDiff` plus a quadratic remainder. -/
theorem connDiff_outerCovDeriv_eq (g g_bg : SmoothRiemannianMetric I M)
    {X Y Z : Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z)) (x : M) :
    (LeviCivita (I := I) g).toFun
          (diffSec (LeviCivita (I := I) g_bg) (LeviCivita (I := I) g) Y Z) x (X x)
        - connDiff (I := I) g g_bg x (Z x) (covApply (LeviCivita (I := I) g) X Y x)
        - connDiff (I := I) g g_bg x (covApply (LeviCivita (I := I) g) X Z x) (Y x) =
      covDerivConnDiff (I := I) g_bg g X Y Z x
        + (connDiff (I := I) g g_bg x (connDiff (I := I) g g_bg x (Z x) (Y x)) (X x)
            - connDiff (I := I) g g_bg x (Z x) (connDiff (I := I) g g_bg x (Y x) (X x))
            - connDiff (I := I) g g_bg x (connDiff (I := I) g g_bg x (Z x) (X x)) (Y x)) := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  set cov₀ := LeviCivita (I := I) g_bg with hcov₀
  set cov₁ := LeviCivita (I := I) g with hcov₁
  have hAeq : connDiff (I := I) g g_bg =
      CovariantDerivative.difference cov₁ cov₀ := connDiff_eq_difference (I := I) g_bg g
  have hYx : MDiffAt (T% Y) x := (hY x).mdifferentiableAt (by simp)
  have hZx : MDiffAt (T% Z) x := (hZ x).mdifferentiableAt (by simp)
  have hZ1 : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% Z) := by simpa using hZ
  have hdiffYZ_at : MDiffAt (T% (diffSec cov₀ cov₁ Y Z)) x :=
    ((diffSec_contMDiff cov₀ cov₁ hY hZ1) x).mdifferentiableAt (by simp)
  rw [covDerivConnDiff_eq (I := I) g_bg g X Y Z x]
  unfold covDerivDiff
  rw [← hcov₀, ← hcov₁]
  have hT1 : cov₁.toFun (diffSec cov₀ cov₁ Y Z) x (X x)
        - cov₀.toFun (diffSec cov₀ cov₁ Y Z) x (X x) =
      connDiff (I := I) g g_bg x (connDiff (I := I) g g_bg x (Z x) (Y x)) (X x) := by
    rw [← diff_eval cov₀ cov₁ hdiffYZ_at (X x), hAeq]
    rfl
  have hcA1 : covApply cov₁ X Y x = covApply cov₀ X Y x + connDiff (I := I) g g_bg x (Y x) (X x) := by
    rw [covApply_cov1_eq cov₀ cov₁ hYx, hAeq]; rfl
  have hcA2 : covApply cov₁ X Z x = covApply cov₀ X Z x + connDiff (I := I) g g_bg x (Z x) (X x) := by
    rw [covApply_cov1_eq cov₀ cov₁ hZx, hAeq]; rfl
  have hT1' : cov₁.toFun (diffSec cov₀ cov₁ Y Z) x (X x) =
      cov₀.toFun (diffSec cov₀ cov₁ Y Z) x (X x)
        + connDiff (I := I) g g_bg x (connDiff (I := I) g g_bg x (Z x) (Y x)) (X x) := by
    rw [← hT1]; abel
  rw [hcA1, hcA2, hT1', ← hAeq, map_add, map_add, ContinuousLinearMap.add_apply]
  abel

end DeTurck
end PDE
end DifferentialGeometry
