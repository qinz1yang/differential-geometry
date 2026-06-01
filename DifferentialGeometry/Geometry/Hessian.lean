import DifferentialGeometry.Geometry.Gradient
import DifferentialGeometry.Geometry.Laplacian
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Hessian of a smooth function on a Riemannian manifold

For a smooth Riemannian metric `g` on a smooth manifold `M` and a smooth scalar
function `f : M → ℝ`, the Hessian of `f` is a symmetric `(0,2)`-tensor on the
tangent bundle. Its pointwise definition reads
$$\operatorname{Hess} f(x)(X, Y) = X(Y(f)) - (\nabla_X Y)(f)$$
where `∇` is the Levi-Civita connection. Equivalently it is the second
covariant derivative of `f`.

This file packages the pieces of the Hessian story that are downstream of the
metric and orthogonal to a particular concrete construction of `∇`. They take
the form of a *bilinear-form* viewpoint:

* a definition `pointwiseBilin` that records a pointwise bilinear form on the
  tangent space, parameterised by the data the user supplies (typically the
  second covariant derivative of `f` along the chosen Levi-Civita connection);
* a basis-bound `bilinForm_trace_sq_le_dim_mul_frobenius_sq` proving the
  pure linear-algebra Frobenius/trace Cauchy-Schwarz inequality
  $$\Bigl(\sum_i B(b_i, b_i)\Bigr)^2 \;\le\;
      n \cdot \sum_{i,j} \bigl(B(b_i, b_j)\bigr)^2$$
  for any basis `b` of a finite-dimensional ℝ-vector space (this is the
  inequality used downstream of the Bochner identity to bound `(Δf)²` by
  `n · |Hess f|²`);
* a packaged `pointwiseBilin` carrier together with its Frobenius-norm-squared
  function `frobeniusSqFun` and trace function `traceFun`, both computed against
  the canonical chosen basis `chartModelBasis E` on the model fibre, and the
  pointwise bound `traceFun_sq_le_dim_mul_frobeniusSqFun` that follows
  immediately from the basis-bound above.

The bound and the carrier are designed to be re-used by clients that supply
their own concrete Hessian. A typical client constructs the bilinear form from
the chart-Christoffel formula
$$\bigl(\operatorname{Hess} f\bigr)_{ij}(x) =
    \partial_i \partial_j (f \circ \varphi^{-1})(\varphi x) -
      \Gamma^k{}_{ij}(g)(\varphi x)\,\partial_k(f \circ \varphi^{-1})(\varphi x)$$
or from `CovariantDerivative` applied twice to the differential of `f`. The
identification of the trace with the Laplace–Beltrami operator and of the
Frobenius norm with the metric Frobenius norm is part of that downstream
construction (it requires either an orthonormal frame of the tangent space
under `g.inner x` or the chart-Christoffel formula tracking the Gram matrix of
the chosen basis); both reduce to the bound proved here.

## Main definitions

* `pointwiseBilin I` : the type abbreviation `∀ x : M, TangentSpace I x →ₗ[ℝ]
  TangentSpace I x →ₗ[ℝ] ℝ` of a pointwise real-valued bilinear form on the
  tangent bundle of `M`. A downstream client constructs a value of this type
  from their concrete Hessian; symmetry is recorded separately by the predicate
  `IsPointwiseSymm`.
* `frobeniusSqFun B x` : the Frobenius norm squared
  `∑ i j, (B x (b i) (b j))²` of a pointwise bilinear form `B`, computed
  against the canonical chosen basis `b := chartModelBasis E`.
* `traceFun B x` : the trace `∑ i, B x (b i) (b i)`, computed against the
  same basis.

## Main theorems

* `bilinForm_trace_sq_le_dim_mul_frobenius_sq` : the pure Cauchy-Schwarz
  Frobenius inequality `(∑ B (b i) (b i))² ≤ n · ∑ (B (b i) (b j))²` for any
  basis `b` indexed by `Fin n`. (The inequality holds for any basis of any
  finite-dimensional vector space; orthonormality is not needed for the
  inequality itself, only for the basis-independent identification of trace
  and Frobenius norm with their geometric counterparts.)
* `traceFun_sq_le_dim_mul_frobeniusSqFun` : the pointwise specialisation
  `(traceFun B x)² ≤ n · frobeniusSqFun B x`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

/-- Frobenius–trace Cauchy-Schwarz: for any bilinear form `B` and any indexing
type `ι` (finite), the squared sum of "diagonal" entries `B(v i)(v i)` is
controlled by the cardinality of `ι` times the sum of squares of all "matrix"
entries `B(v i)(v j)`. -/
theorem bilinForm_trace_sq_le_card_mul_frobenius_sq
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {ι : Type*} [Fintype ι]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (v : ι → V) :
    (∑ i : ι, B (v i) (v i))^2 ≤
      (Fintype.card ι : ℝ) * ∑ i : ι, ∑ j : ι, (B (v i) (v j))^2 := by
  classical
  have h_diag :
      (∑ i : ι, B (v i) (v i))^2 ≤
        (Fintype.card ι : ℝ) * ∑ i : ι, (B (v i) (v i))^2 := by
    have h := sq_sum_le_card_mul_sum_sq (α := ℝ) (s := (Finset.univ : Finset ι))
      (f := fun i => B (v i) (v i))
    simpa [Finset.card_univ] using h
  have h_row : ∀ i : ι,
      (B (v i) (v i))^2 ≤ ∑ j : ι, (B (v i) (v j))^2 := by
    intro i
    have h_mem : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
    have h_nonneg : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ (B (v i) (v j))^2 :=
      fun j _ => sq_nonneg _
    exact Finset.single_le_sum (f := fun j => (B (v i) (v j))^2) h_nonneg h_mem
  have h_sum :
      ∑ i : ι, (B (v i) (v i))^2 ≤ ∑ i : ι, ∑ j : ι, (B (v i) (v j))^2 :=
    Finset.sum_le_sum (fun i _ => h_row i)
  have h_card_nonneg : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast Nat.zero_le _
  calc (∑ i : ι, B (v i) (v i))^2
      ≤ (Fintype.card ι : ℝ) * ∑ i : ι, (B (v i) (v i))^2 := h_diag
    _ ≤ (Fintype.card ι : ℝ) * ∑ i : ι, ∑ j : ι, (B (v i) (v j))^2 := by
        exact mul_le_mul_of_nonneg_left h_sum h_card_nonneg

/-- Specialisation of `bilinForm_trace_sq_le_card_mul_frobenius_sq` to the
basis `Module.finBasis ℝ V` indexed by `Fin (Module.finrank ℝ V)`. -/
theorem bilinForm_trace_sq_le_dim_mul_frobenius_sq
    {V : Type*} [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V) :
    (∑ i : Fin (Module.finrank ℝ V), B (b i) (b i))^2 ≤
      (Module.finrank ℝ V : ℝ) *
        ∑ i : Fin (Module.finrank ℝ V),
          ∑ j : Fin (Module.finrank ℝ V), (B (b i) (b j))^2 := by
  have h := bilinForm_trace_sq_le_card_mul_frobenius_sq (V := V)
    (ι := Fin (Module.finrank ℝ V)) B (fun i => b i)
  simpa [Fintype.card_fin] using h

variable (I) in
/-- A pointwise real-valued bilinear form on the tangent bundle of `M`. -/
abbrev pointwiseBilin :=
  ∀ x : M, TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ

/-- A pointwise bilinear form `B` is *pointwise symmetric* if `B x v w = B x w v`
for all `x`, `v`, `w`. -/
def IsPointwiseSymm (B : pointwiseBilin (M := M) I) : Prop :=
  ∀ x : M, ∀ v w : TangentSpace I x, B x v w = B x w v

/-- The Frobenius norm squared of a pointwise bilinear form `B`, computed
against the canonical basis `chartModelBasis E`:
`frobeniusSqFun B x = ∑ i, ∑ j, (B x (e i) (e j))²`
where `e := chartModelBasis E`. -/
def frobeniusSqFun (B : pointwiseBilin (M := M) I) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      (B x ((chartModelBasis E) i) ((chartModelBasis E) j))^2

@[simp] lemma frobeniusSqFun_def (B : pointwiseBilin (M := M) I) (x : M) :
    frobeniusSqFun (I := I) (M := M) B x =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (B x ((chartModelBasis E) i) ((chartModelBasis E) j))^2 := rfl

/-- The trace of a pointwise bilinear form `B`, computed against the
canonical basis `chartModelBasis E`:
`traceFun B x = ∑ i, B x (e i) (e i)` where `e := chartModelBasis E`. -/
def traceFun (B : pointwiseBilin (M := M) I) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    B x ((chartModelBasis E) i) ((chartModelBasis E) i)

@[simp] lemma traceFun_def (B : pointwiseBilin (M := M) I) (x : M) :
    traceFun (I := I) (M := M) B x =
      ∑ i : Fin (Module.finrank ℝ E),
        B x ((chartModelBasis E) i) ((chartModelBasis E) i) := rfl

/-- The Frobenius norm squared is non-negative. -/
lemma frobeniusSqFun_nonneg (B : pointwiseBilin (M := M) I) (x : M) :
    0 ≤ frobeniusSqFun (I := I) (M := M) B x := by
  unfold frobeniusSqFun
  exact Finset.sum_nonneg
    (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))

/-- **Pointwise trace–Frobenius Cauchy-Schwarz.**
For any pointwise bilinear form `B` and any point `x`, the square of the trace
is bounded by the dimension times the Frobenius norm squared:
`(traceFun B x)² ≤ (finrank ℝ E) · frobeniusSqFun B x`. -/
theorem traceFun_sq_le_dim_mul_frobeniusSqFun
    (B : pointwiseBilin (M := M) I) (x : M) :
    (traceFun (I := I) (M := M) B x)^2 ≤
      (Module.finrank ℝ E : ℝ) * frobeniusSqFun (I := I) (M := M) B x := by
  have h := bilinForm_trace_sq_le_dim_mul_frobenius_sq
    (V := TangentSpace I x) (B := B x) (b := chartModelBasis E)
  simp only [traceFun_def, frobeniusSqFun_def]
  exact h

/-- The trace square divided by the dimension is bounded above by the Frobenius
norm squared. This is the form usually quoted in the Bochner / Lichnerowicz
literature. -/
theorem traceFun_sq_div_dim_le_frobeniusSqFun
    (B : pointwiseBilin (M := M) I) (x : M) :
    (traceFun (I := I) (M := M) B x)^2 / (Module.finrank ℝ E : ℝ) ≤
      frobeniusSqFun (I := I) (M := M) B x := by
  have hne : (Module.finrank ℝ E : ℕ) ≠ 0 := NeZero.ne _
  have hpos : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by
    have : (0 : ℕ) < Module.finrank ℝ E := Nat.pos_of_ne_zero hne
    exact_mod_cast this
  have hbound := traceFun_sq_le_dim_mul_frobeniusSqFun (I := I) (M := M) B x
  exact (div_le_iff₀ hpos).mpr (by linarith [hbound])

/-- The chart Gram matrix entry `g_{ij}(α, ·)` pulled back to the chart target
`(extChartAt I α).target ⊆ E` via the chart inverse. -/
def chartGramOnE (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y => chartGramMatrix (I := I) g α ((extChartAt I α).symm y) i j

@[simp] lemma chartGramOnE_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartGramOnE (I := I) g α i j y =
      chartGramMatrix (I := I) g α ((extChartAt I α).symm y) i j := rfl

/-- Symmetry of the chart Gram matrix entries pulled back to `E`. -/
lemma chartGramOnE_symm
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartGramOnE (I := I) g α i j y = chartGramOnE (I := I) g α j i y := by
  unfold chartGramOnE
  rw [chartGramMatrix_apply, chartGramMatrix_apply]
  exact g.symm _ _ _

/-- The Christoffel symbol of the second kind associated to the chart at `α`.
This is the pointwise scalar
$$\Gamma^k{}_{ij}(g, \alpha)(y) = \tfrac12 \sum_l G^{kl}(\alpha, x_y)\,
    \bigl(\partial_i G_{lj}(\alpha, \cdot)(y) + \partial_j G_{li}(\alpha, \cdot)(y)
        - \partial_l G_{ij}(\alpha, \cdot)(y)\bigr),$$
evaluated at the chart-coordinate point `y ∈ E`, where `x_y := (extChartAt I α).symm y`
is the corresponding manifold point. -/
def chartChristoffel (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
    chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y) k l *
      (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
       partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
       partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y)

@[simp] lemma chartChristoffel_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartChristoffel (I := I) g α i j k y =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y) k l *
          (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
           partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
           partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y) := rfl

/-- **Symmetry of the Christoffel symbol** in the lower indices: this is the
torsion-free property of the Levi-Civita connection encoded directly in the
chart-coordinate formula. -/
theorem chartChristoffel_symm
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartChristoffel (I := I) g α i j k y =
      chartChristoffel (I := I) g α j i k y := by
  classical
  rw [chartChristoffel_def, chartChristoffel_def]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro l _
  congr 1
  have hsym : chartGramOnE (I := I) g α i j =
      chartGramOnE (I := I) g α j i :=
    funext (fun y' => chartGramOnE_symm (I := I) g α i j y')
  rw [show partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y =
        partialDeriv (E := E) l (chartGramOnE (I := I) g α j i) y from by
    rw [hsym]]
  ring

/-- The iterated partial derivative `∂_i (∂_j f̃)(y)` of the chart pullback
`f̃ := scalarOnE α f`, where `e_j` is the inner direction and `e_i` is the outer
direction. -/
def chartIteratedPartialDeriv
    (α : M) (f : M → ℝ) (i j : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  partialDeriv (E := E) i (partialDeriv (E := E) j (scalarOnE (I := I) α f)) y

@[simp] lemma chartIteratedPartialDeriv_def
    (α : M) (f : M → ℝ) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartIteratedPartialDeriv (I := I) α f i j y =
      partialDeriv (E := E) i
        (partialDeriv (E := E) j (scalarOnE (I := I) α f)) y := rfl

/-- The chart-coordinate Hessian of `f` in the chart at `α`, evaluated at the
manifold point `x`:
$$(\operatorname{Hess} f)_{ij}(\alpha, x) =
    \partial_i \partial_j f̃(\varphi(x)) - \sum_k \Gamma^k{}_{ij}\,\partial_k f̃(\varphi(x)).$$ -/
def chartHessianTensor (g : SmoothRiemannianMetric I M)
    (α : M) (f : M → ℝ) (i j : Fin (Module.finrank ℝ E)) (x : M) : ℝ :=
  chartIteratedPartialDeriv (I := I) α f i j (extChartAt I α x) -
    ∑ k : Fin (Module.finrank ℝ E),
      chartChristoffel (I := I) g α i j k (extChartAt I α x) *
        partialDeriv (E := E) k (scalarOnE (I := I) α f) (extChartAt I α x)

@[simp] lemma chartHessianTensor_def
    (g : SmoothRiemannianMetric I M)
    (α : M) (f : M → ℝ) (i j : Fin (Module.finrank ℝ E)) (x : M) :
    chartHessianTensor (I := I) g α f i j x =
      chartIteratedPartialDeriv (I := I) α f i j (extChartAt I α x) -
        ∑ k : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α i j k (extChartAt I α x) *
            partialDeriv (E := E) k (scalarOnE (I := I) α f) (extChartAt I α x) := rfl

/-- Mixed partials of a smooth function on `E` are symmetric *at points in the
interior of the chart target*. This is Schwarz's theorem applied to the chart
pullback `scalarOnE α f`. The hypothesis `y ∈ interior (extChartAt I α).target`
is automatic under `[I.Boundaryless]` for `y = extChartAt I α x` with `x` in the
chart source. -/
lemma chartIteratedPartialDeriv_symm_of_contDiff
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    chartIteratedPartialDeriv (I := I) α f i j y =
      chartIteratedPartialDeriv (I := I) α f j i y := by
  classical
  unfold chartIteratedPartialDeriv partialDeriv
  have hsmooth_target : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f)
      (extChartAt I α).target :=
    scalarOnE_contDiffOn (I := I) α hf
  have hsmooth_int : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f)
      (interior (extChartAt I α).target) := hsmooth_target.mono interior_subset
  have hopen_int : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hcontDiffAt : ContDiffAt ℝ ∞ (scalarOnE (I := I) α f) y :=
    hsmooth_int.contDiffAt (hopen_int.mem_nhds hy)
  have hsymm_2 :
      IsSymmSndFDerivAt ℝ (scalarOnE (I := I) α f) y := by
    refine ContDiffAt.isSymmSndFDerivAt hcontDiffAt ?_
    rw [minSmoothness_of_isRCLikeNormedField]
    decide
  have hg_diff : DifferentiableAt ℝ (fderiv ℝ (scalarOnE (I := I) α f)) y := by
    have hfderiv_smooth : ContDiffOn ℝ ∞
        (fderiv ℝ (scalarOnE (I := I) α f))
        (interior (extChartAt I α).target) :=
      hsmooth_int.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
    have hcontDiff_at_fderiv :
        ContDiffAt ℝ ∞ (fderiv ℝ (scalarOnE (I := I) α f)) y :=
      hfderiv_smooth.contDiffAt (hopen_int.mem_nhds hy)
    exact hcontDiff_at_fderiv.differentiableAt (by simp)
  have hkey : ∀ a b : Fin (Module.finrank ℝ E),
      fderiv ℝ
          (fun z => fderiv ℝ (scalarOnE (I := I) α f) z ((chartModelBasis E) b))
          y ((chartModelBasis E) a) =
        (fderiv ℝ (fderiv ℝ (scalarOnE (I := I) α f)) y
          ((chartModelBasis E) a)) ((chartModelBasis E) b) := by
    intro a b
    set L : (E →L[ℝ] ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.apply ℝ ℝ ((chartModelBasis E) b)
    have hcomp_eq : (fun z : E =>
          fderiv ℝ (scalarOnE (I := I) α f) z ((chartModelBasis E) b)) =
        L ∘ (fderiv ℝ (scalarOnE (I := I) α f)) := by
      funext z; rfl
    rw [hcomp_eq, fderiv_comp y L.differentiableAt hg_diff]
    rw [L.fderiv]
    rfl
  rw [hkey i j, hkey j i]
  exact hsymm_2 _ _

/-- **Symmetry of the chart Hessian** at points where the chart image lies in the
interior of the chart target. -/
theorem chartHessianTensor_symm
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (i j : Fin (Module.finrank ℝ E))
    {x : M} (hx_int : extChartAt I α x ∈ interior (extChartAt I α).target) :
    chartHessianTensor (I := I) g α f i j x =
      chartHessianTensor (I := I) g α f j i x := by
  classical
  rw [chartHessianTensor_def, chartHessianTensor_def]
  rw [chartIteratedPartialDeriv_symm_of_contDiff (I := I) α hf i j hx_int]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [chartChristoffel_symm (I := I) g α i j k]

/-- **Symmetry of the chart Hessian** under `[I.Boundaryless]`, requiring only
that `x` is in the chart source (the interior condition is automatic). -/
theorem chartHessianTensor_symm_of_boundaryless [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (i j : Fin (Module.finrank ℝ E))
    {x : M} (hx : x ∈ (chartAt H α).source) :
    chartHessianTensor (I := I) g α f i j x =
      chartHessianTensor (I := I) g α f j i x := by
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  have hx_target : extChartAt I α x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxsrc
  have hx_int : extChartAt I α x ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α hx_target
  exact chartHessianTensor_symm (I := I) g α hf i j hx_int

/-- The pointwise Hessian of a function `f` on a Riemannian manifold `(M, g)`,
packaged as a `pointwiseBilin I`. At each point `x` the value
`hessFun g f x v w` is `∑ i j, vᵢ wⱼ (chartHessianTensor g x f i j x)`, where the
components `vᵢ, wⱼ` are read off in the canonical model basis `chartModelBasis E`
of `TangentSpace I x` and the matrix entries `chartHessianTensor g x f i j x` are
the chart-coordinate Hessian (iterated partial derivatives minus the chart
Christoffel correction), evaluated in the chart at `x`. The bilinearity fields
record additivity and homogeneity in each argument. -/
def hessFun (g : SmoothRiemannianMetric I M) (f : M → ℝ) :
    pointwiseBilin (M := M) I :=
  fun x => LinearMap.mk₂ ℝ
    (fun v w =>
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr v) i *
            ((chartModelBasis E).repr w) j *
            chartHessianTensor (I := I) g x f i j x)
    (fun v₁ v₂ w => by
      classical
      dsimp only
      have hrepr : (chartModelBasis E).repr (v₁ + v₂) =
          (chartModelBasis E).repr v₁ + (chartModelBasis E).repr v₂ := map_add _ _ _
      rw [hrepr]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      simp only [Finsupp.coe_add, Pi.add_apply]
      ring)
    (fun c v w => by
      classical
      dsimp only
      have hrepr : (chartModelBasis E).repr (c • v) =
          c • (chartModelBasis E).repr v := map_smul _ _ _
      rw [hrepr]
      simp only [smul_eq_mul, Finsupp.coe_smul, Pi.smul_apply]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring)
    (fun v w₁ w₂ => by
      classical
      dsimp only
      have hrepr : (chartModelBasis E).repr (w₁ + w₂) =
          (chartModelBasis E).repr w₁ + (chartModelBasis E).repr w₂ := map_add _ _ _
      rw [hrepr]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      simp only [Finsupp.coe_add, Pi.add_apply]
      ring)
    (fun c v w => by
      classical
      dsimp only
      have hrepr : (chartModelBasis E).repr (c • w) =
          c • (chartModelBasis E).repr w := map_smul _ _ _
      rw [hrepr]
      simp only [smul_eq_mul, Finsupp.coe_smul, Pi.smul_apply]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring)

/-- Pointwise expansion of `hessFun`: applied to two tangent vectors, it sums
the chart Hessian matrix entries weighted by the model-basis coordinates. -/
lemma hessFun_apply (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (v w : TangentSpace I x) :
    hessFun (I := I) g f x v w =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr v) i *
            ((chartModelBasis E).repr w) j *
            chartHessianTensor (I := I) g x f i j x := by
  rfl

/-- **Symmetry of `hessFun`.** For a smooth scalar `f` on a boundaryless
manifold, the pointwise Hessian bilinear form `hessFun g f` is symmetric:
`hessFun g f x v w = hessFun g f x w v` for every point `x` and tangent vectors
`v`, `w`. The proof reduces to the symmetry of the chart Hessian matrix in its
two indices, which holds at any chart-source point under `[I.Boundaryless]`. -/
theorem hessFun_symm_of_boundaryless [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    IsPointwiseSymm (hessFun (I := I) (M := M) g f) := by
  intro x v w
  classical
  rw [hessFun_apply, hessFun_apply]
  have hxsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hsymm : ∀ i j, chartHessianTensor (I := I) g x f i j x =
      chartHessianTensor (I := I) g x f j i x := fun i j =>
    chartHessianTensor_symm_of_boundaryless (I := I) g x hf i j hxsrc
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [hsymm j i]
  ring

/-- The metric chart Frobenius norm squared of the chart Hessian matrix: this is
the basis-independent "tensor" norm
$$|\operatorname{Hess} f|^2_g(x) = \sum_{i,j,k,l} G^{ik}(x) G^{jl}(x)\,
    H_{ij}\,H_{kl},$$
where `H = chartHessianTensor g x f` and `G^{ij} = chartInvGramMatrix g x x`. -/
def chartHessFrobeniusSq (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
  ∑ j : Fin (Module.finrank ℝ E),
  ∑ k : Fin (Module.finrank ℝ E),
  ∑ l : Fin (Module.finrank ℝ E),
    chartInvGramMatrix (I := I) g x x i k *
      chartInvGramMatrix (I := I) g x x j l *
        chartHessianTensor (I := I) g x f i j x *
          chartHessianTensor (I := I) g x f k l x

@[simp] lemma chartHessFrobeniusSq_def (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) (x : M) :
    chartHessFrobeniusSq (I := I) g f x =
      ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
      ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x i k *
          chartInvGramMatrix (I := I) g x x j l *
            chartHessianTensor (I := I) g x f i j x *
              chartHessianTensor (I := I) g x f k l x := rfl

/-- The chart-coordinate trace of the Hessian against the inverse Gram matrix:
$$\operatorname{tr}_g \operatorname{Hess} f(x) := \sum_{i, j} G^{ij}(x)\,
    (\operatorname{Hess} f)_{ij}(x, x).$$ -/
def chartHessTrace (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
  ∑ j : Fin (Module.finrank ℝ E),
    chartInvGramMatrix (I := I) g x x i j *
      chartHessianTensor (I := I) g x f i j x

@[simp] lemma chartHessTrace_def (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) (x : M) :
    chartHessTrace (I := I) g f x =
      ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x i j *
          chartHessianTensor (I := I) g x f i j x := rfl

/-- The bilinear form `hessFun g f x` evaluated on the canonical basis vectors
`b i, b j` returns the chart Hessian tensor entry `H_{ij}(x, x)`. -/
lemma hessFun_basis_apply
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    hessFun (I := I) g f x
        ((chartModelBasis E) i) ((chartModelBasis E) j) =
      chartHessianTensor (I := I) g x f i j x := by
  classical
  rw [hessFun_apply]
  conv_lhs => rw [show
      (∑ i' : Fin (Module.finrank ℝ E),
        ∑ j' : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr ((chartModelBasis E) i)) i' *
            ((chartModelBasis E).repr ((chartModelBasis E) j)) j' *
            chartHessianTensor (I := I) g x f i' j' x) =
      (∑ i' : Fin (Module.finrank ℝ E),
        ∑ j' : Fin (Module.finrank ℝ E),
          (if i = i' then (1 : ℝ) else 0) *
            (if j = j' then (1 : ℝ) else 0) *
            chartHessianTensor (I := I) g x f i' j' x) from
      Finset.sum_congr rfl (fun i' _ => Finset.sum_congr rfl (fun j' _ => by
        rw [Module.Basis.repr_self_apply, Module.Basis.repr_self_apply]))]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj'_ne
      have hjj' : ¬ j = j' := fun h => hj'_ne h.symm
      simp [hjj']
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  · intro i' _ hi'_ne
    apply Finset.sum_eq_zero
    intro j' _
    have hii' : ¬ i = i' := fun h => hi'_ne h.symm
    simp [hii']
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The `traceFun` of `hessFun g f` in the canonical basis equals the simple sum
`∑ i, H_{ii}(x, x)` of the diagonal entries of the chart Hessian matrix. -/
lemma traceFun_hessFun
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    traceFun (I := I) (M := M) (hessFun (I := I) g f) x =
      ∑ i : Fin (Module.finrank ℝ E), chartHessianTensor (I := I) g x f i i x := by
  unfold traceFun
  refine Finset.sum_congr rfl ?_
  intro i _
  exact hessFun_basis_apply (I := I) g f x i i

/-- The `frobeniusSqFun` of `hessFun g f` in the canonical basis equals the
simple Frobenius squared `∑ i j, (H_{ij}(x, x))²`. -/
lemma frobeniusSqFun_hessFun
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    frobeniusSqFun (I := I) (M := M) (hessFun (I := I) g f) x =
      ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        (chartHessianTensor (I := I) g x f i j x)^2 := by
  unfold frobeniusSqFun
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [hessFun_basis_apply]

/-- **Pointwise Cauchy-Schwarz between the basis-naive trace and Frobenius of
the chart Hessian matrix**, derived from `traceFun_sq_le_dim_mul_frobeniusSqFun`.
This is the basis-naive version that holds without any orthonormality
assumption. -/
theorem chartHess_trace_sq_le_dim_mul_frobenius_sq
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    (∑ i : Fin (Module.finrank ℝ E), chartHessianTensor (I := I) g x f i i x)^2 ≤
      (Module.finrank ℝ E : ℝ) *
        ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (chartHessianTensor (I := I) g x f i j x)^2 := by
  classical
  have hbound :=
    traceFun_sq_le_dim_mul_frobeniusSqFun
      (I := I) (M := M) (hessFun (I := I) g f) x
  rw [traceFun_hessFun (I := I) g f x,
      frobeniusSqFun_hessFun (I := I) g f x] at hbound
  exact hbound

/-- **Bochner-Lichnerowicz dimension-Laplacian inequality, hypothesis-bearing form.**
Given the trace identity `(traceFun (hessFun g f) x = Δ_g f x)` as a hypothesis,
the inequality `(Δ_g f x)² ≤ n · ∑ i j, (H_{ij})²` follows immediately from
`chartHess_trace_sq_le_dim_mul_frobenius_sq`. -/
theorem laplacian_sq_le_dim_mul_frobenius_sq_of_trace_eq
    [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (htr : traceFun (I := I) (M := M) (hessFun (I := I) g f) x =
        Δ_g (I := I) g hf x) :
    (Δ_g (I := I) g hf x)^2 ≤
      (Module.finrank ℝ E : ℝ) *
        ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (chartHessianTensor (I := I) g x f i j x)^2 := by
  classical
  have hbound := chartHess_trace_sq_le_dim_mul_frobenius_sq (I := I) g f x
  rw [traceFun_hessFun (I := I) g f x] at htr
  rw [← htr]
  exact hbound

/-- **Pointwise dimension-Laplacian inequality, divided form.**
Hypothesis-bearing version giving `(Δ_g f x)² / n ≤ ∑ i j, (H_{ij})²`. -/
theorem laplacian_sq_div_dim_le_frobenius_sq_of_trace_eq
    [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (htr : traceFun (I := I) (M := M) (hessFun (I := I) g f) x =
        Δ_g (I := I) g hf x) :
    (Δ_g (I := I) g hf x)^2 / (Module.finrank ℝ E : ℝ) ≤
      ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        (chartHessianTensor (I := I) g x f i j x)^2 := by
  classical
  have hne : (Module.finrank ℝ E : ℕ) ≠ 0 := NeZero.ne _
  have hpos : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by
    have : (0 : ℕ) < Module.finrank ℝ E := Nat.pos_of_ne_zero hne
    exact_mod_cast this
  have hbound :=
    laplacian_sq_le_dim_mul_frobenius_sq_of_trace_eq (I := I) g hf x htr
  exact (div_le_iff₀ hpos).mpr (by linarith [hbound])

/-- **Cauchy-Schwarz inequality applied to `hessFun`.**
The bound on `traceFun (hessFun g f)` directly via the carrier's Cauchy-Schwarz. -/
theorem traceFun_hessFun_sq_le_dim_mul_frobeniusSqFun
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    (traceFun (I := I) (M := M) (hessFun (I := I) g f) x)^2 ≤
      (Module.finrank ℝ E : ℝ) *
        frobeniusSqFun (I := I) (M := M) (hessFun (I := I) g f) x :=
  traceFun_sq_le_dim_mul_frobeniusSqFun
    (I := I) (M := M) (hessFun (I := I) g f) x

end DivergenceTheorem
end Integral
end DifferentialGeometry