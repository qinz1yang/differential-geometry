import DifferentialGeometry.PDE.DeTurck.ConnectionDifference
import DifferentialGeometry.Geometry.Gradient
import DifferentialGeometry.Integral.Connection.ChartBridge.Hessian

/-!
# The DeTurck vector field as the metric trace of the connection-difference tensor

Given two smooth Riemannian metrics `g` and `g'` on a smooth manifold `M`, the
connection-difference tensor `connDiff g g'` is a genuine `(1,2)`-tensor field
(see `ConnectionDifference.lean`).  The **DeTurck vector field** is its metric
`g`-trace: contracting the upper-`g` inverse metric `g(x)⁻¹ ∈ T_xM ⊗ T_xM` into
the two lower slots of `connDiff g g' x` produces a tangent vector at every point.

In any chart with coordinate frame `{e_j}` and inverse Gram matrix `G^{jk}` of `g`,
the DeTurck vector field reads
$$
  W(x) = \sum_{j,k} G^{jk}(x)\; A\bigl(e_j(x), e_k(x)\bigr),
$$
where `A = connDiff g g' x`.  Since `∑_{j,k} G^{jk} e_j ⊗ e_k` is the intrinsic
inverse metric `g(x)⁻¹` and `A` is a genuine (chart-free) tensor, the resulting
vector is independent of the chart.

This file defines `W` purely pointwise: a chart-at-a-fixed-basepoint version
`deTurckChartLocal`, the canonical chart-at-the-point version `deTurckFun`, and the
chart-independence theorem `deTurckChartLocal_eq_deTurckFun` linking them.  No
smoothness statements appear here — that is a separate development.

## Construction

For a fixed basepoint `α : M`, `deTurckChartLocal g g' α x` is the chart-`α`
coordinate sum displayed above, using the chart-`α` inverse Gram matrix
`chartInvGramMatrix g α x` and the chart-`α` coordinate frame
`chartBasisVecFiber α j x`.  The canonical `deTurckFun g g' x` specialises the
basepoint to `x` itself: `deTurckFun g g' x = deTurckChartLocal g g' x x`.

Chart-independence is proved by expanding the chart-`α` coordinate frame in the
fixed model basis through the change-of-basis matrix, and using the Gram-matrix
transformation law `Gα = P · Gx · Pᵀ` together with the algebraic identity
`Pᵀ · (P · Gx · Pᵀ)⁻¹ · P = Gx⁻¹`.  The outcome is that, for every chart-`α`
whose base set contains `x`, `deTurckChartLocal g g' α x` equals one and the same
expression in the model basis — the model-basis metric trace.

## Main definitions

* `deTurckChartLocal g g' α x` — the chart-`α` representative of the DeTurck
  vector field at `x`.
* `deTurckFun g g' x` — the canonical, chart-independent DeTurck vector field as a
  plain function `M → TangentSpace I x`, defined as `deTurckChartLocal g g' x x`.

## Main results

* `deTurckChartLocal_eq_deTurckFun` — chart-independence: at every point of the
  chart-`α` base set, `deTurckChartLocal g g' α x = deTurckFun g g' x`.
* `deTurckFun_self` — the DeTurck vector field of a metric with itself vanishes.
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

/-- The **DeTurck vector field**, computed in the chart at a fixed basepoint `α`.

At each point `x : M` this is the chart-`α` metric trace of the
connection-difference tensor `connDiff g g'`:
$$
  \sum_{j,k} G^{jk}(x)\; A\bigl(e_j(x), e_k(x)\bigr),
$$
where `G^{jk} = chartInvGramMatrix g α x` is the inverse Gram matrix of `g` in
the chart-`α` coordinate frame `e_j = chartBasisVecFiber α j` and
`A = connDiff g g' x`.  The chart-independence of this construction is the
content of `deTurckChartLocal_eq_deTurckFun`. -/
def deTurckChartLocal (g g' : SmoothRiemannianMetric I M) (α : M) (x : M) :
    TangentSpace I x :=
  ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
    chartInvGramMatrix (I := I) g α x j k •
      connDiff (I := I) g g' x
        (chartBasisVecFiber (I := I) α j x)
        (chartBasisVecFiber (I := I) α k x)

/-- Unfolding lemma for `deTurckChartLocal`. -/
lemma deTurckChartLocal_def (g g' : SmoothRiemannianMetric I M) (α : M) (x : M) :
    deTurckChartLocal (I := I) g g' α x =
      ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α x j k •
          connDiff (I := I) g g' x
            (chartBasisVecFiber (I := I) α j x)
            (chartBasisVecFiber (I := I) α k x) := rfl

/-- Expansion of a continuous bilinear map valued in a topological module over a
pair of finite sums of scaled vectors:
`B (∑ p, a_p • u_p) (∑ q, b_q • w_q) = ∑ p, ∑ q, (a_p * b_q) • B (u_p) (w_q)`. -/
private lemma clm_bilinear_expand_two_sums_vector
    {x : M}
    (B : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
    {n : ℕ} (a b : Fin n → ℝ) (u w : Fin n → TangentSpace I x) :
    B (∑ p : Fin n, a p • u p) (∑ q : Fin n, b q • w q) =
      ∑ p : Fin n, ∑ q : Fin n, (a p * b q) • B (u p) (w q) := by
  classical
  have houter : B (∑ p : Fin n, a p • u p) = ∑ p : Fin n, a p • B (u p) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro p _
    rw [map_smul]
  rw [houter, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [ContinuousLinearMap.smul_apply]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro q _
  rw [map_smul, smul_smul]

/-- Scalar-valued bilinear expansion against two finite sums, specialised to
`g.inner x`.  Used inside the Gram transformation law. -/
private lemma clm_bilinear_expand_two_sums_scalar
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (a b : Fin n → ℝ) (u w : Fin n → TangentSpace I x) :
    g.inner x (∑ p : Fin n, a p • u p) (∑ q : Fin n, b q • w q) =
      ∑ p : Fin n, ∑ q : Fin n, (a p * b q) * g.inner x (u p) (w q) := by
  classical
  have houter : g.inner x (∑ p : Fin n, a p • u p) =
      ∑ p : Fin n, a p • g.inner x (u p) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro p _
    rw [map_smul]
  rw [houter, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro q _
  rw [map_smul, smul_eq_mul]
  ring

/-- The change-of-basis matrix from the chart-`α` coordinate frame at `x` to the
fixed model basis: the `(i, k)` entry is the `e_k`-coordinate of
`chartBasisVecFiber α i x` in the basis `chartModelBasis E`. -/
private def deTurckCobMatrix (α : M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i k =>
    (chartModelBasis E).repr
      ((chartBasisVecFiber (I := I) α i x : TangentSpace I x)) k

/-- Recovery formula: `chartBasisVecFiber α i x = ∑ k, P_{ik} • (chartModelBasis E k)`,
where `P = deTurckCobMatrix α x`.  This is `Module.Basis.sum_repr` for the model
basis. -/
private lemma chartBasisVecFiber_eq_sum_model (α : M) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    (chartBasisVecFiber (I := I) α i x : TangentSpace I x) =
      ∑ k : Fin (Module.finrank ℝ E),
        deTurckCobMatrix (I := I) α x i k •
          ((chartModelBasis E) k : TangentSpace I x) := by
  classical
  unfold deTurckCobMatrix
  simp only [Matrix.of_apply]
  exact (((chartModelBasis E).sum_repr
    (chartBasisVecFiber (I := I) α i x : TangentSpace I x))).symm

/-- The change-of-basis matrix is the transpose of `Module.Basis.toMatrix`. -/
private lemma deTurckCobMatrix_eq_toMatrix_transpose (α : M) (x : M) :
    deTurckCobMatrix (I := I) α x =
      ((chartModelBasis E).toMatrix
        (fun i : Fin (Module.finrank ℝ E) =>
          chartBasisVecFiber (I := I) α i x))ᵀ := by
  classical
  unfold deTurckCobMatrix
  ext i k
  rw [Matrix.transpose_apply, Module.Basis.toMatrix_apply, Matrix.of_apply]

/-- The change-of-basis matrix is invertible at chart-`α` base-set points. -/
private lemma deTurckCobMatrix_isUnit (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    IsUnit (deTurckCobMatrix (I := I) α x) := by
  classical
  rw [deTurckCobMatrix_eq_toMatrix_transpose]
  set chartBasis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    chartBasisFamily (I := I) α hx with hCB_def
  have hfam_eq : (fun i : Fin (Module.finrank ℝ E) =>
      chartBasisVecFiber (I := I) α i x)
      = (chartBasis : Fin (Module.finrank ℝ E) → TangentSpace I x) := by
    funext i
    rw [hCB_def]
    exact (chartBasisFamily_apply (I := I) α hx i).symm
  rw [hfam_eq]
  have hbase_unit : IsUnit ((chartModelBasis E).toMatrix
      (chartBasis : Fin (Module.finrank ℝ E) → TangentSpace I x)) :=
    ⟨⟨_, chartBasis.toMatrix (chartModelBasis E),
        Module.Basis.toMatrix_mul_toMatrix_flip _ _,
        Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩, rfl⟩
  rw [Matrix.isUnit_iff_isUnit_det] at hbase_unit ⊢
  rwa [Matrix.det_transpose]

/-- The model Gram matrix `chartGramMatrix g x x` is the Gram matrix of `g.inner x`
in the fixed model basis. -/
private lemma chartGramMatrix_self_eq_model (g : SmoothRiemannianMetric I M) (x : M)
    (k l : Fin (Module.finrank ℝ E)) :
    chartGramMatrix (I := I) g x x k l =
      g.inner x ((chartModelBasis E) k : TangentSpace I x)
        ((chartModelBasis E) l : TangentSpace I x) := by
  rw [chartGramMatrix_apply, chartBasisVecFiber_self (I := I) x k,
    chartBasisVecFiber_self (I := I) x l]

/-- **Gram-matrix transformation law.** The chart-`α` Gram matrix at `x` is the
conjugate of the model Gram matrix `chartGramMatrix g x x` by the change-of-basis
matrix `P = deTurckCobMatrix α x`:
`Gα = P · Gx · Pᵀ`.  This holds for every `x`. -/
private lemma chartGramMatrix_eq_cob_conj (g : SmoothRiemannianMetric I M)
    (α : M) (x : M) :
    chartGramMatrix (I := I) g α x =
      deTurckCobMatrix (I := I) α x *
        chartGramMatrix (I := I) g x x *
        (deTurckCobMatrix (I := I) α x)ᵀ := by
  classical
  set P := deTurckCobMatrix (I := I) α x with hP_def
  ext i j
  rw [chartGramMatrix_apply]
  have hbilinear :
      g.inner x (chartBasisVecFiber (I := I) α i x)
          (chartBasisVecFiber (I := I) α j x)
        = ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            (P i k * P j l) *
              g.inner x ((chartModelBasis E) k : TangentSpace I x)
                ((chartModelBasis E) l : TangentSpace I x) := by
    rw [chartBasisVecFiber_eq_sum_model (I := I) α x i,
        chartBasisVecFiber_eq_sum_model (I := I) α x j]
    exact clm_bilinear_expand_two_sums_scalar (n := Module.finrank ℝ E) g x
      (fun k => P i k) (fun l => P j l)
      (fun k => ((chartModelBasis E) k : TangentSpace I x))
      (fun l => ((chartModelBasis E) l : TangentSpace I x))
  rw [hbilinear]
  rw [Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Matrix.transpose_apply, chartGramMatrix_self_eq_model (I := I) g x k l]
  ring

/-- The metric trace of `connDiff g g'` computed in the fixed model basis: the
sum `∑_{p,q} (Gx⁻¹)_{pq} • connDiff g g' x (e_p) (e_q)`, where `Gx⁻¹` is the
inverse model Gram matrix and `{e_p}` is the model basis.  This expression
depends only on `x` — it involves no chart basepoint. -/
private def deTurckModelTrace (g g' : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x :=
  ∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
    (chartGramMatrix (I := I) g x x)⁻¹ p q •
      connDiff (I := I) g g' x
        ((chartModelBasis E) p : TangentSpace I x)
        ((chartModelBasis E) q : TangentSpace I x)

/-- The conjugation identity `Pᵀ · (P · Gx · Pᵀ)⁻¹ · P = Gx⁻¹` for an invertible
matrix `P` and an arbitrary matrix `Gx`. -/
private lemma transpose_mul_conj_inv_mul
    {n : ℕ} (P Gx : Matrix (Fin n) (Fin n) ℝ)
    (hP : IsUnit P) :
    Pᵀ * (P * Gx * Pᵀ)⁻¹ * P = Gx⁻¹ := by
  classical
  have hPdet : IsUnit P.det := Matrix.isUnit_iff_isUnit_det _ |>.mp hP
  have hPtdet : IsUnit (Pᵀ).det := by rwa [Matrix.det_transpose]
  have hinv : (P * Gx * Pᵀ)⁻¹ = (Pᵀ)⁻¹ * (Gx⁻¹ * P⁻¹) := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  rw [hinv]
  rw [show Pᵀ * ((Pᵀ)⁻¹ * (Gx⁻¹ * P⁻¹)) * P
        = (Pᵀ * (Pᵀ)⁻¹) * Gx⁻¹ * (P⁻¹ * P) by
    simp only [Matrix.mul_assoc]]
  rw [Matrix.mul_nonsing_inv _ hPtdet, Matrix.nonsing_inv_mul _ hPdet,
    Matrix.one_mul, Matrix.mul_one]

/-- For `x` in the chart-`α` base set, the chart-`α` representative of the DeTurck
vector field equals the model-basis metric trace.

The proof expands each chart-`α` coordinate frame vector in the model basis,
collects the resulting double sum, and applies the Gram-transformation law
`Gα = P · Gx · Pᵀ` together with the conjugation identity
`Pᵀ · (Gα)⁻¹ · P = Gx⁻¹`. -/
private lemma deTurckChartLocal_eq_modelTrace (g g' : SmoothRiemannianMetric I M)
    (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    deTurckChartLocal (I := I) g g' α x = deTurckModelTrace (I := I) g g' x := by
  classical
  set n := Module.finrank ℝ E with hn_def
  set P := deTurckCobMatrix (I := I) α x with hP_def
  set Gx := chartGramMatrix (I := I) g x x with hGx_def
  set Gα := chartGramMatrix (I := I) g α x with hGα_def
  set A := connDiff (I := I) g g' x with hA_def
  set e := fun k : Fin n => ((chartModelBasis E) k : TangentSpace I x) with he_def
  have hP_unit : IsUnit P := deTurckCobMatrix_isUnit (I := I) α hx
  have hGα_eq : Gα = P * Gx * Pᵀ := chartGramMatrix_eq_cob_conj (I := I) g α x
  have hframe : ∀ j : Fin n,
      (chartBasisVecFiber (I := I) α j x : TangentSpace I x) =
        ∑ p : Fin n, P j p • e p := fun j =>
    chartBasisVecFiber_eq_sum_model (I := I) α x j
  rw [deTurckChartLocal_def]
  have hstep1 : ∀ j k : Fin n,
      A (chartBasisVecFiber (I := I) α j x)
          (chartBasisVecFiber (I := I) α k x) =
        ∑ p : Fin n, ∑ q : Fin n, (P j p * P k q) • A (e p) (e q) := by
    intro j k
    rw [hframe j, hframe k]
    exact clm_bilinear_expand_two_sums_vector A
      (fun p => P j p) (fun q => P k q) e e
  have hcoeff : ∀ j k : Fin n,
      chartInvGramMatrix (I := I) g α x j k = Gα⁻¹ j k := fun _ _ => rfl
  calc
    ∑ j : Fin n, ∑ k : Fin n,
        chartInvGramMatrix (I := I) g α x j k •
          A (chartBasisVecFiber (I := I) α j x)
            (chartBasisVecFiber (I := I) α k x)
        = ∑ j : Fin n, ∑ k : Fin n,
            Gα⁻¹ j k •
              ∑ p : Fin n, ∑ q : Fin n, (P j p * P k q) • A (e p) (e q) := by
          refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
          rw [hcoeff j k, hstep1 j k]
    _ = ∑ j : Fin n, ∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n,
            (Gα⁻¹ j k * (P j p * P k q)) • A (e p) (e q) := by
          refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl (fun p _ => ?_)
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl (fun q _ => ?_)
          rw [smul_smul]
    _ = ∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
            (Gα⁻¹ j k * (P j p * P k q)) • A (e p) (e q) := by
          rw [show (∑ j : Fin n, ∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n,
                (Gα⁻¹ j k * (P j p * P k q)) • A (e p) (e q))
              = ∑ jk : Fin n × Fin n, ∑ pq : Fin n × Fin n,
                  (Gα⁻¹ jk.1 jk.2 * (P jk.1 pq.1 * P jk.2 pq.2)) •
                    A (e pq.1) (e pq.2) by
            rw [← Finset.sum_product', Finset.univ_product_univ]
            refine Finset.sum_congr rfl (fun jk _ => ?_)
            rw [← Finset.sum_product', Finset.univ_product_univ]]
          rw [show (∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                (Gα⁻¹ j k * (P j p * P k q)) • A (e p) (e q))
              = ∑ pq : Fin n × Fin n, ∑ jk : Fin n × Fin n,
                  (Gα⁻¹ jk.1 jk.2 * (P jk.1 pq.1 * P jk.2 pq.2)) •
                    A (e pq.1) (e pq.2) by
            rw [← Finset.sum_product', Finset.univ_product_univ]
            refine Finset.sum_congr rfl (fun pq _ => ?_)
            rw [← Finset.sum_product', Finset.univ_product_univ]]
          rw [Finset.sum_comm]
    _ = ∑ p : Fin n, ∑ q : Fin n,
            (Pᵀ * Gα⁻¹ * P) p q • A (e p) (e q) := by
          refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
          have hpull : ∑ j : Fin n, ∑ k : Fin n,
                (Gα⁻¹ j k * (P j p * P k q)) • A (e p) (e q)
              = (∑ j : Fin n, ∑ k : Fin n, Gα⁻¹ j k * (P j p * P k q)) •
                  A (e p) (e q) := by
            rw [Finset.sum_smul]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [Finset.sum_smul]
          rw [hpull]
          congr 1
          rw [Matrix.mul_apply]
          rw [show (∑ a : Fin n, (Pᵀ * Gα⁻¹) p a * P a q)
                = ∑ a : Fin n, ∑ b : Fin n,
                    P b p * Gα⁻¹ b a * P a q from ?_]
          · rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            refine Finset.sum_congr rfl (fun k _ => ?_)
            ring
          · refine Finset.sum_congr rfl (fun a _ => ?_)
            rw [Matrix.mul_apply, Finset.sum_mul]
            refine Finset.sum_congr rfl (fun b _ => ?_)
            rw [Matrix.transpose_apply]
    _ = ∑ p : Fin n, ∑ q : Fin n, Gx⁻¹ p q • A (e p) (e q) := by
          have hconj : Pᵀ * Gα⁻¹ * P = Gx⁻¹ := by
            rw [hGα_eq]
            exact transpose_mul_conj_inv_mul P Gx hP_unit
          rw [hconj]
    _ = deTurckModelTrace (I := I) g g' x := rfl

/-- The **DeTurck vector field** of two smooth Riemannian metrics `g` and `g'`, as
a plain function `M → TangentSpace I x`.

It is the canonical, chart-independent metric `g`-trace of the
connection-difference tensor `connDiff g g'`, obtained by specialising the chart
basepoint to the evaluation point itself: `deTurckFun g g' x = deTurckChartLocal
g g' x x`.  Chart-independence — that this agrees with the chart-`α`
representative for *any* chart `α` whose base set contains `x` — is
`deTurckChartLocal_eq_deTurckFun`. -/
def deTurckFun (g g' : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x :=
  deTurckChartLocal (I := I) g g' x x

/-- Unfolding lemma for `deTurckFun`. -/
lemma deTurckFun_def (g g' : SmoothRiemannianMetric I M) (x : M) :
    deTurckFun (I := I) g g' x = deTurckChartLocal (I := I) g g' x x := rfl

/-- **Chart-independence of the DeTurck vector field.**

For every chart basepoint `α` and every point `x` in the chart-`α` base set, the
chart-`α` representative `deTurckChartLocal g g' α x` agrees with the canonical
DeTurck vector field `deTurckFun g g' x`.

Both sides equal the model-basis metric trace `deTurckModelTrace g g' x`: the
left side by `deTurckChartLocal_eq_modelTrace` applied to the chart at `α`, and
the right side by the same lemma applied to the chart at `x` itself (whose base
set always contains `x`).  This expresses that the metric trace
`∑_{j,k} G^{jk} e_j ⊗ e_k` contracted into the genuine tensor `connDiff g g'`
yields a chart-independent tangent vector. -/
theorem deTurckChartLocal_eq_deTurckFun (g g' : SmoothRiemannianMetric I M)
    (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    deTurckChartLocal (I := I) g g' α x = deTurckFun (I := I) g g' x := by
  have hbase_x : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact mem_chart_source H x
  rw [deTurckFun_def]
  rw [deTurckChartLocal_eq_modelTrace (I := I) g g' α hx,
    deTurckChartLocal_eq_modelTrace (I := I) g g' x hbase_x]

/-- Variant of `deTurckChartLocal_eq_deTurckFun` phrased with the chart-source
membership hypothesis `x ∈ (chartAt H α).source`, which is definitionally the
trivialization base set. -/
theorem deTurckChartLocal_eq_deTurckFun_of_mem_source
    (g g' : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    deTurckChartLocal (I := I) g g' α x = deTurckFun (I := I) g g' x := by
  refine deTurckChartLocal_eq_deTurckFun (I := I) g g' α ?_
  rwa [trivializationAt_baseSet_eq_chartAt_source]

/-- The chart-`α` representative of the DeTurck vector field of a metric with
itself vanishes identically: every term carries the factor
`connDiff g g x (·) (·) = 0`. -/
lemma deTurckChartLocal_self (g : SmoothRiemannianMetric I M) (α : M) (x : M) :
    deTurckChartLocal (I := I) g g α x = (0 : TangentSpace I x) := by
  classical
  rw [deTurckChartLocal_def]
  refine Finset.sum_eq_zero (fun j _ => Finset.sum_eq_zero (fun k _ => ?_))
  rw [connDiff_self (I := I) g]
  simp

/-- **The DeTurck vector field of a metric with itself vanishes identically.**

When `g = g'` the connection-difference tensor `connDiff g g` is the zero tensor,
so its metric trace is the zero vector. -/
@[simp]
theorem deTurckFun_self (g : SmoothRiemannianMetric I M) :
    deTurckFun (I := I) g g = fun x => (0 : TangentSpace I x) := by
  funext x
  rw [deTurckFun_def]
  exact deTurckChartLocal_self (I := I) g x x

/-- Pointwise form of `deTurckFun_self`. -/
theorem deTurckFun_self_apply (g : SmoothRiemannianMetric I M) (x : M) :
    deTurckFun (I := I) g g x = (0 : TangentSpace I x) := by
  rw [deTurckFun_self]

end DeTurck
end PDE
end DifferentialGeometry
