import DifferentialGeometry.Integral.Connection.Bochner

/-!
# Concrete pointwise Bochner-Weitzenböck identity, unconditional form

The companion `Connection.Bochner` derives the **fully unconditional** abstract pointwise
Bochner-Weitzenböck identity for a smooth scalar function on a smooth boundaryless
Riemannian manifold:
$$
  \tfrac{1}{2}\,\Delta_g\bigl(g(\nabla f, \nabla f)\bigr)(x) =
    g_x\bigl(\nabla(\Delta_g f)(x), \nabla f(x)\bigr)
    + \mathrm{Ric}_x\bigl(\nabla f(x), \nabla f(x)\bigr)
    + |\nabla^2 f|_g^2(x).
$$

This file produces the **concrete** pointwise Bochner-Weitzenböck identity in the
right-hand-side form expected by the Integral / Analysis / PDE layer, multiplying by `2`:
$$
  \Delta_g\bigl(g(\nabla f, \nabla f)\bigr)(x) =
    2\,|\nabla^2 f|_g^2(x) +
    2\,\mathrm{Ric}_x\bigl(\nabla f(x), \nabla f(x)\bigr) +
    2\,g_x\bigl(\nabla f(x), \nabla(\Delta_g f)(x)\bigr).
$$

The Frobenius norm squared is realised in two equivalent forms:

* `frobeniusSq_grad_vector g (∇f) x` — the orthonormal-frame trace produced by the
  abstract Bochner identity, summing `g(LC^∇(∇f) B_i, LC^∇(∇f) B_i)` over a
  `g_x`-orthonormal frame at `x`. This is the form natively output by
  `bochner_pointwise_abstract_unconditional`.
* `chartHessFrobeniusSq g f x` — the chart-coordinate metric Frobenius squared, which is
  the geometer's basis-independent expression `∑_{ijkl} G^{ik} G^{jl} H_{ij} H_{kl}`.

We prove these two are equal pointwise (`frobeniusSq_grad_vector_eq_chartHessFrobeniusSq`)
by combining the orthonormal-frame trace identity `orthonormal_basis_bilin_trace`
applied to the bilinear form `(z, w) ↦ g(LC z, LC w)` with the chart-Hessian-matrix
identity `chartHessianMatrixIdentity_holds` and a model-basis decomposition for the
Hessian carrier `LC e_l = ∑_n (b.repr (LC e_l) n) • e_n`.

The Ricci pairing is left in its abstract form `ricciTensor g x (∇f) (∇f)`. Identifying
this with the chart-coordinate metric Ricci pairing `chartRicciOnGradF g f x` requires a
basis-coordinate identification of the abstract Riemann CLM with the chart Riemann
tensor — itself a separate chart-Christoffel computation; in this file we keep
`ricciTensor` as the abstract carrier.

## Main results

* `frobeniusSq_grad_vector_eq_chartHessFrobeniusSq` — unconditional identity bridging the
  orthonormal-frame Frobenius squared `frobeniusSq_grad_vector g (∇f) x` to the
  chart-coordinate metric Frobenius squared `chartHessFrobeniusSq g f x`.
* `bochner_pointwise_grad_normSq_of_boundaryless` — unconditional pointwise Bochner identity,
  using the orthonormal-frame Frobenius squared and the abstract Ricci tensor.
* `bochner_pointwise_concrete_metric_unconditional` — unconditional metric form, using
  the chart-coordinate metric Frobenius squared and the abstract Ricci tensor.

Both unconditional theorems carry no hypotheses beyond `[I.Boundaryless]`,
`[T2Space M]`, and `[SigmaCompactSpace M]` (the closed-manifold standard package).
-/

noncomputable section

open Bundle Manifold Set FiberBundle NormedSpace Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-- For a continuous linear self-map `T : T_x M →L T_x M` and any `g_x`-orthonormal
frame `B`, the orthonormal-frame Hilbert-Schmidt norm squared equals the inverse Gram
contraction of `g(T(e_k), T(e_l))`:
$$
  \sum_i g_x(T(B_i), T(B_i)) =
    \sum_{kl} G^{kl}(x, x)\, g_x(T(e_k), T(e_l)).
$$
-/
private theorem sum_g_inner_T_self_eq_invGram_sum
    (g : SmoothRiemannianMetric I M) (x : M)
    (T : TangentSpace I x →L[ℝ] TangentSpace I x)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    ∑ i : Fin (Module.finrank ℝ E),
      g.inner x (T (B i)) (T (B i)) =
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x k l *
            g.inner x (T ((chartModelBasis E) k))
              (T ((chartModelBasis E) l)) := by
  classical
  set Hb : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
    (((g.inner x).comp T).flip.comp T).flip with hHb_def
  have hHb_apply : ∀ z w : TangentSpace I x,
      Hb z w = g.inner x (T z) (T w) := by
    intro z w
    change (((g.inner x).comp T).flip.comp T).flip z w =
      g.inner x (T z) (T w)
    rw [ContinuousLinearMap.flip_apply,
        ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.flip_apply,
        ContinuousLinearMap.comp_apply]
  have htrace := orthonormal_basis_bilin_trace (I := I) g x Hb B hB
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        g.inner x (T (B i)) (T (B i))) =
        ∑ i : Fin (Module.finrank ℝ E), Hb (B i) (B i) from
    Finset.sum_congr rfl (fun i _ => (hHb_apply (B i) (B i)).symm)]
  rw [htrace]
  refine Finset.sum_congr rfl ?_
  intro k _
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [hHb_apply]

/-- The metric inner product on the model basis equals the chart Gram matrix entry. -/
private lemma g_inner_modelBasis_eq_chartGram
    (g : SmoothRiemannianMetric I M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner x ((chartModelBasis E) i) ((chartModelBasis E) j) =
      chartGramMatrix (I := I) g x x i j := by
  classical
  rw [chartGramMatrix_apply]
  rw [chartBasisVecFiber_self (I := I) x i]
  rw [chartBasisVecFiber_self (I := I) x j]

/-- For any tangent vector `v ∈ T_x M`, decomposed in the model basis as
`v = ∑_p (b.repr v) p • b p`, the inner product `g.inner x v (b n)` equals
`∑_p (b.repr v) p * G_{pn}`. -/
private lemma g_inner_modelBasis_first_decomp
    (g : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) (n : Fin (Module.finrank ℝ E)) :
    g.inner x v ((chartModelBasis E) n) =
      ∑ p : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr v p *
          chartGramMatrix (I := I) g x x p n := by
  classical
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := chartModelBasis E with hb_def
  have hv_eq : v = ∑ p : Fin (Module.finrank ℝ E), b.repr v p • b p :=
    (Module.Basis.sum_repr b v).symm
  rw [show g.inner x v =
      g.inner x (∑ p : Fin (Module.finrank ℝ E), b.repr v p • b p) from
    congrArg (g.inner x) hv_eq]
  rw [map_sum]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [show g.inner x (b.repr v p • b p) =
      b.repr v p • g.inner x (b p) from
    (g.inner x).map_smul (b.repr v p) (b p)]
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [g_inner_modelBasis_eq_chartGram (I := I) g x p n]

/-- **Inverse-Gram formula for the model-basis component.** For any tangent vector
`v ∈ T_x M`, the model-basis component `b.repr v n` is recovered from inner products
against the model basis via the inverse Gram matrix:
$$
  (b.repr\,v)\,n = \sum_m G^{nm}(x, x)\, g_x(v, e_m).
$$
-/
private lemma modelBasis_repr_eq_invGram_sum
    (g : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) (n : Fin (Module.finrank ℝ E)) :
    (chartModelBasis E).repr v n =
      ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x n m *
          g.inner x v ((chartModelBasis E) m) := by
  classical
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := chartModelBasis E with hb_def
  have h_inner : ∀ m : Fin (Module.finrank ℝ E),
      g.inner x v (b m) =
        ∑ p : Fin (Module.finrank ℝ E),
          b.repr v p *
            chartGramMatrix (I := I) g x x p m :=
    g_inner_modelBasis_first_decomp (I := I) g x v
  rw [show (∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x n m *
          g.inner x v (b m)) =
      ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x n m *
          (∑ p : Fin (Module.finrank ℝ E),
            b.repr v p * chartGramMatrix (I := I) g x x p m) from by
    refine Finset.sum_congr rfl ?_
    intro m _
    rw [h_inner m]]
  rw [show (∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x n m *
          (∑ p : Fin (Module.finrank ℝ E),
            b.repr v p * chartGramMatrix (I := I) g x x p m)) =
      ∑ p : Fin (Module.finrank ℝ E),
        b.repr v p *
          (∑ m : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x n m *
              chartGramMatrix (I := I) g x x p m) from by
    rw [show (∑ m : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x n m *
              (∑ p : Fin (Module.finrank ℝ E),
                b.repr v p * chartGramMatrix (I := I) g x x p m)) =
        ∑ m : Fin (Module.finrank ℝ E),
          ∑ p : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x n m *
              (b.repr v p * chartGramMatrix (I := I) g x x p m) from by
      refine Finset.sum_congr rfl ?_
      intro m _
      rw [Finset.mul_sum]]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro p _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro m _
    ring]
  have h_inner_collapse : ∀ p : Fin (Module.finrank ℝ E),
      (∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x n m *
          chartGramMatrix (I := I) g x x p m) =
        (if n = p then (1 : ℝ) else 0) := by
    intro p
    have hsymm : ∀ m : Fin (Module.finrank ℝ E),
        chartGramMatrix (I := I) g x x p m =
          chartGramMatrix (I := I) g x x m p := by
      intro m
      rw [chartGramMatrix_apply, chartGramMatrix_apply]
      exact g.symm x _ _
    rw [show (∑ m : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x n m *
            chartGramMatrix (I := I) g x x p m) =
        ∑ m : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x n m *
            chartGramMatrix (I := I) g x x m p from by
      refine Finset.sum_congr rfl ?_
      intro m _
      rw [hsymm m]]
    have hxbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
      mem_baseSet_trivializationAt E (TangentSpace I) x
    have hidentity := chartInvGramMatrix_mul_chartGramMatrix
      (I := I) g x hxbase
    rw [show (∑ m : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x n m *
            chartGramMatrix (I := I) g x x m p) =
        (chartInvGramMatrix (I := I) g x x *
          chartGramMatrix (I := I) g x x) n p from by
      rw [Matrix.mul_apply]]
    rw [hidentity]
    rw [Matrix.one_apply]
  rw [show (∑ p : Fin (Module.finrank ℝ E),
        b.repr v p *
          (∑ m : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x n m *
              chartGramMatrix (I := I) g x x p m)) =
      ∑ p : Fin (Module.finrank ℝ E),
        b.repr v p * (if n = p then (1 : ℝ) else 0) from by
    refine Finset.sum_congr rfl ?_
    intro p _
    rw [h_inner_collapse p]]
  rw [Finset.sum_eq_single n]
  · rw [if_pos rfl, mul_one]
  · intro p _ hpn
    rw [if_neg (fun h => hpn h.symm), mul_zero]
  · intro hn
    exact absurd (Finset.mem_univ n) hn

/-- **Unconditional bridge: orthonormal-frame Frobenius equals chart-coordinate metric
Frobenius.** For a smooth scalar `f : M → ℝ` on a smooth boundaryless Riemannian
manifold, the orthonormal-frame Frobenius squared `frobeniusSq_grad_vector g (∇f) x`
equals the chart-coordinate metric Frobenius squared `chartHessFrobeniusSq g f x`. -/
theorem frobeniusSq_grad_vector_eq_chartHessFrobeniusSq
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M) :
    frobeniusSq_grad_vector (I := I) g
        (fun b : M => gradFun (I := I) g f b) x =
      chartHessFrobeniusSq (I := I) g f x := by
  classical
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := chartModelBasis E with hb_def
  set T : TangentSpace I x →L[ℝ] TangentSpace I x :=
    (LeviCivita (I := I) g).toFun
      (fun b => gradFun (I := I) g f b) x with hT_def
  set B : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x with hB_def
  have hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 := fun i j =>
    smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have hStep1 : frobeniusSq_grad_vector (I := I) g
        (fun b => gradFun (I := I) g f b) x =
      ∑ i : Fin (Module.finrank ℝ E),
        g.inner x (T (B i)) (T (B i)) := by
    rw [frobeniusSq_grad_vector_def]
  rw [hStep1]
  rw [sum_g_inner_T_self_eq_invGram_sum (I := I) g x T B hB_orth]
  have hM : chartHessianMatrixIdentity (I := I) g f x :=
    chartHessianMatrixIdentity_holds (I := I) g hf x
  have h_TE_eq : ∀ k n : Fin (Module.finrank ℝ E),
      g.inner x (T (b k)) (b n) =
        chartHessianTensor (I := I) g x f k n x := by
    intro k n
    have h1 : g.inner x (T (b k)) (b n) =
        g.inner x ((LeviCivita (I := I) g).toFun
            (fun b => gradFun (I := I) g f b) x (b k)) (b n) := rfl
    rw [h1]
    rw [abstractHessian_eq_inner_cov_gradFun_extend (I := I) g hf x (b k) (b n)]
    exact hM k n
  have h_g_TT : ∀ k l : Fin (Module.finrank ℝ E),
      g.inner x (T (b k)) (T (b l)) =
        ∑ n : Fin (Module.finrank ℝ E),
          b.repr (T (b l)) n *
            chartHessianTensor (I := I) g x f k n x := by
    intro k l
    have hTl_eq : T (b l) = ∑ n : Fin (Module.finrank ℝ E),
        b.repr (T (b l)) n • b n :=
      (Module.Basis.sum_repr b (T (b l))).symm
    rw [show g.inner x (T (b k)) (T (b l)) =
        g.inner x (T (b k))
          (∑ n : Fin (Module.finrank ℝ E),
            b.repr (T (b l)) n • b n) from
      congrArg (g.inner x (T (b k))) hTl_eq]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro n _
    rw [show g.inner x (T (b k)) (b.repr (T (b l)) n • b n) =
        b.repr (T (b l)) n • g.inner x (T (b k)) (b n) from
      (g.inner x (T (b k))).map_smul (b.repr (T (b l)) n) (b n)]
    rw [smul_eq_mul]
    rw [h_TE_eq k n]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x k l *
            g.inner x (T (b k)) (T (b l))) =
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x k l *
            (∑ n : Fin (Module.finrank ℝ E),
              b.repr (T (b l)) n *
                chartHessianTensor (I := I) g x f k n x) from by
    refine Finset.sum_congr rfl ?_
    intro k _
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [h_g_TT k l]]
  have h_repr_T_eq : ∀ l n : Fin (Module.finrank ℝ E),
      b.repr (T (b l)) n =
        ∑ m : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x n m *
            g.inner x (T (b l)) (b m) :=
    fun l n => modelBasis_repr_eq_invGram_sum (I := I) g x (T (b l)) n
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x k l *
            (∑ n : Fin (Module.finrank ℝ E),
              b.repr (T (b l)) n *
                chartHessianTensor (I := I) g x f k n x)) =
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x k l *
            (∑ n : Fin (Module.finrank ℝ E),
              (∑ m : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g x x n m *
                  chartHessianTensor (I := I) g x f l m x) *
                  chartHessianTensor (I := I) g x f k n x) from by
    refine Finset.sum_congr rfl ?_
    intro k _
    refine Finset.sum_congr rfl ?_
    intro l _
    refine congrArg (fun y => chartInvGramMatrix (I := I) g x x k l * y) ?_
    refine Finset.sum_congr rfl ?_
    intro n _
    rw [h_repr_T_eq l n]
    rw [show (∑ m : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x n m *
            g.inner x (T (b l)) (b m)) =
        ∑ m : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x n m *
            chartHessianTensor (I := I) g x f l m x from by
      refine Finset.sum_congr rfl ?_
      intro m _
      rw [h_TE_eq l m]]]
  rw [chartHessFrobeniusSq_def]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x k l *
            (∑ n : Fin (Module.finrank ℝ E),
              (∑ m : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g x x n m *
                  chartHessianTensor (I := I) g x f l m x) *
                  chartHessianTensor (I := I) g x f k n x)) =
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          ∑ n : Fin (Module.finrank ℝ E),
            ∑ m : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x k l *
                chartInvGramMatrix (I := I) g x x n m *
                chartHessianTensor (I := I) g x f l m x *
                chartHessianTensor (I := I) g x f k n x from by
    refine Finset.sum_congr rfl ?_
    intro k _
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro n _
    rw [Finset.sum_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro m _
    ring]
  have h_swap : (∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          ∑ n : Fin (Module.finrank ℝ E),
            ∑ m : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x k l *
                chartInvGramMatrix (I := I) g x x n m *
                chartHessianTensor (I := I) g x f l m x *
                chartHessianTensor (I := I) g x f k n x) =
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ n : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            ∑ m : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x k l *
                chartInvGramMatrix (I := I) g x x n m *
                chartHessianTensor (I := I) g x f l m x *
                chartHessianTensor (I := I) g x f k n x := by
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [Finset.sum_comm]
  rw [h_swap]
  refine Finset.sum_congr rfl ?_
  intro k _
  refine Finset.sum_congr rfl ?_
  intro n _
  refine Finset.sum_congr rfl ?_
  intro l _
  refine Finset.sum_congr rfl ?_
  intro m _
  ring

/-- **Bochner-Weitzenböck identity for `|∇f|²` (concrete form).** For a smooth
scalar `f : M → ℝ` on a boundaryless Riemannian manifold, the connection Laplacian
of the squared gradient norm satisfies, at every point `x : M`,
$$
  \Delta_g\bigl(g(\nabla f, \nabla f)\bigr)(x) =
    2\,|\nabla^2 f|_g^2(x) +
    2\,\mathrm{Ric}_x\bigl(\nabla f(x), \nabla f(x)\bigr) +
    2\,g_x\bigl(\nabla f(x), \nabla(\Delta_g f)(x)\bigr).
$$
Here `|\nabla^2 f|_g^2(x)` is realised as the orthonormal-frame Hessian-Frobenius
squared `frobeniusSq_grad_vector g (∇f) x` and `\mathrm{Ric}_x(\nabla f, \nabla f)`
as the abstract Ricci pairing `ricciTensor g x (∇f x) (∇f x)`. The proof multiplies
the abstract half-identity `bochner_pointwise_abstract_unconditional` by `2` and
symmetrises the gradient cross term. -/
theorem bochner_pointwise_grad_normSq_of_boundaryless
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    Δ_g (I := I) g (normGradSqFun_contMDiff (I := I) g hf) x =
      2 * frobeniusSq_grad_vector (I := I) g
            (fun b => gradFun (I := I) g f b) x +
        2 * ricciTensor (I := I) g x
              (gradFun (I := I) g f x) (gradFun (I := I) g f x) +
        2 * g.inner x (gradFun (I := I) g f x)
            (gradFun (I := I) g (Δ_g (I := I) g hf) x) := by
  have h := bochner_pointwise_abstract_unconditional (I := I) g hf x
  have hLHS_eq : Δ_g (I := I) g (normGradSq_contMDiff (I := I) g hf) x =
      Δ_g (I := I) g (normGradSqFun_contMDiff (I := I) g hf) x := rfl
  rw [hLHS_eq] at h
  have h' : Δ_g (I := I) g (normGradSqFun_contMDiff (I := I) g hf) x =
      2 * (g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x)
            (gradFun (I := I) g f x) +
          ricciTensor (I := I) g x (gradFun (I := I) g f x)
            (gradFun (I := I) g f x) +
          frobeniusSq_grad_vector (I := I) g
            (fun b => gradFun (I := I) g f b) x) := by
    linarith [h]
  rw [h']
  rw [show g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x)
          (gradFun (I := I) g f x) =
        g.inner x (gradFun (I := I) g f x)
          (gradFun (I := I) g (Δ_g (I := I) g hf) x) from
    g.symm x _ _]
  ring

/-- **Truly unconditional pointwise Bochner-Weitzenböck identity in concrete form
(metric-Frobenius variant).** Same identity as `bochner_pointwise_grad_normSq_of_boundaryless`
but with the orthonormal-frame Frobenius squared replaced by the chart-coordinate metric
Frobenius squared `chartHessFrobeniusSq g f x`. The two are equal by
`frobeniusSq_grad_vector_eq_chartHessFrobeniusSq`. -/
theorem bochner_pointwise_concrete_metric_unconditional
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    Δ_g (I := I) g (normGradSqFun_contMDiff (I := I) g hf) x =
      2 * chartHessFrobeniusSq (I := I) g f x +
        2 * ricciTensor (I := I) g x
              (gradFun (I := I) g f x) (gradFun (I := I) g f x) +
        2 * g.inner x (gradFun (I := I) g f x)
            (gradFun (I := I) g (Δ_g (I := I) g hf) x) := by
  rw [bochner_pointwise_grad_normSq_of_boundaryless (I := I) g hf x]
  rw [frobeniusSq_grad_vector_eq_chartHessFrobeniusSq (I := I) g hf x]

/-- **Non-negativity of the chart-coordinate metric Frobenius squared.** For any
smooth scalar `f : M → ℝ` on a smooth boundaryless Riemannian manifold, the
chart-coordinate metric Frobenius squared `chartHessFrobeniusSq g f x` is
non-negative at every point. Transported from
`frobeniusSq_grad_vector_nonneg` via the unconditional bridge
`frobeniusSq_grad_vector_eq_chartHessFrobeniusSq`. -/
theorem chartHessFrobeniusSq_nonneg
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M) :
    0 ≤ chartHessFrobeniusSq (I := I) g f x := by
  rw [← frobeniusSq_grad_vector_eq_chartHessFrobeniusSq (I := I) g hf x]
  exact frobeniusSq_grad_vector_nonneg (I := I) g
    (fun b : M => gradFun (I := I) g f b) x

/-- **Half-form Bochner-Weitzenböck identity for `|∇f|²` (chart-Frobenius form).**
For a smooth scalar `f : M → ℝ` on a boundaryless Riemannian manifold, at every
point `x : M`,
$$
  \tfrac{1}{2}\,\Delta_g\bigl(g(\nabla f, \nabla f)\bigr)(x) =
    |\nabla^2 f|_g^2(x) +
    \mathrm{Ric}_x\bigl(\nabla f(x), \nabla f(x)\bigr) +
    g_x\bigl(\nabla f(x), \nabla(\Delta_g f)(x)\bigr).
$$
The Hessian-Frobenius term `|\nabla^2 f|_g^2(x)` is taken in the chart-coordinate
metric form `chartHessFrobeniusSq g f x` and the Ricci pairing in its abstract form
`ricciTensor g x (∇f) (∇f)`. The proof divides
`bochner_pointwise_concrete_metric_unconditional` by `2`. -/
theorem bochner_pointwise_half_grad_normSq_of_boundaryless
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    (1 / 2 : ℝ) * Δ_g (I := I) g (normGradSqFun_contMDiff (I := I) g hf) x =
      chartHessFrobeniusSq (I := I) g f x +
        ricciTensor (I := I) g x
          (gradFun (I := I) g f x) (gradFun (I := I) g f x) +
        g.inner x (gradFun (I := I) g f x)
          (gradFun (I := I) g (Δ_g (I := I) g hf) x) := by
  rw [bochner_pointwise_concrete_metric_unconditional (I := I) g hf x]
  ring

end Connection
end Integral
end DifferentialGeometry
