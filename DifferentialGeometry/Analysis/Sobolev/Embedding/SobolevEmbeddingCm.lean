import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingManifoldC0
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Defs

/-!
# The `C^m` tensor Sobolev embedding controlling iterated covariant derivatives

The `C⁰` embedding `tensorPouSobolevHilbert_embedding_Ck_gNorm` controls the
fibre norm `‖T.toSection x‖` of a smooth compactly-supported `(r, s)`-tensor by
its `H^{2k}` norm when `2k > dim M`.  Downstream, the metric-family lift needs
control of the *iterated covariant derivatives* `∇^j T` for `j ≤ m` — `C²`
control (`m = 2`) of the metric being what keeps positive-definiteness and lets
the solution be realised as a smooth metric.

The iterated covariant derivative is built here as the iterate of the
section-level covariant gradient
`covGrad g r s : SmoothCcTensor g r s → SmoothCcTensor g r (s + 1)`
(the extra covariant slot carries the differentiation direction).  Iterating
`j` times produces the `(r, s + j)`-tensor `iteratedCovGrad g r s j T = ∇^j T`,
itself a smooth compactly-supported section, so its Riemannian fibre norm and
its `H^•` norm are the standard ones for the higher-valence tensor.

## Main results

* `iteratedCovGrad` — the section-level `j`-fold covariant gradient
  `∇^j : SmoothCcTensor g r s → SmoothCcTensor g r (s + j)`.

* `iteratedCovGrad_toSobolev_embedding_Cm` — the **`C^m` embedding** controlling
  the iterated covariant derivatives.  For `2k > dim M + 2m` there is `C > 0`
  with, for every smooth compactly-supported `(r, s)`-tensor `T` and every
  `x ∈ M`,
  $$
    \sum_{j=0}^{m} \bigl\lVert (\nabla^j T)(x) \bigr\rVert
      \;\le\; C \cdot \sum_{j=0}^{m}
        \bigl\lVert \nabla^j T \bigr\rVert_{H^{2(k-j)}}.
  $$
  Each fibre norm is the Riemannian fibre norm of the `(r, s + j)`-tensor
  `∇^j T` (the bundle metric `tensorRS_riemannianBundle g r (s + j)`).  This is
  obtained by applying the `C⁰` embedding (its `m = 0` instance) to each
  higher-valence tensor `∇^j T` — for which the threshold `2(k - j) > dim M`
  holds, since `2k > dim M + 2m ≥ dim M + 2j` — and summing over `j ≤ m`.

* `iteratedCovGrad_toSobolev_embedding_C2` — the `C²`, `(0, 2)`-tensor instance
  the DeTurck metric family actually consumes (`r = 0`, `s = 2`, `m = 2`).

## The remaining order-reduction step

To convert the right-hand side into a single multiple of `‖T.toHs (2k)‖` one
needs the per-degree order-reduction bound
$$
  \bigl\lVert \nabla^j T \bigr\rVert_{H^{2(k-j)}}
    \;\le\; C_j \, \lVert T \rVert_{H^{2k}},
$$
i.e. *one covariant derivative consumes one full pair of Sobolev orders*.  In
the partition-of-unity chart-Sobolev norm `tensorPouSobolevHsNorm` this is the
statement that the raw chart components of `∇ T` (which read `∂(components) +
Γ·(components)`) have their order-`(2k - 2)` derivatives dominated by the
order-`(2k)` derivatives of the components of `T`, uniformly via the
bounded-derivative Christoffel data of the compact manifold.  That is a separate
coordinate computation; the assembly above is the part that is independent of it
and feeds directly into the metric-family lift through the iterated-derivative
norms.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Topology Metric Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- The **iterated section-level covariant gradient** `∇^j` of a smooth
compactly-supported `(r, s)`-tensor section, as a smooth compactly-supported
`(r, s + j)`-tensor section.

`∇^0 T = T`; `∇^{j+1} T = covGrad … (∇^j T)`.  The accumulated `j` extra
covariant slots carry the successive differentiation directions. -/
noncomputable def iteratedCovGrad
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∀ j : ℕ, SmoothCcTensor g r s → SmoothCcTensor g r (s + j)
  | 0 => fun T => T
  | (j + 1) => fun T =>
      covGrad (I := I) (M := M) g r (s + j)
        (iteratedCovGrad g r s j T)

@[simp] lemma iteratedCovGrad_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    iteratedCovGrad g r s 0 T = T := rfl

@[simp] lemma iteratedCovGrad_succ
    (g : SmoothRiemannianMetric I M) (r s j : ℕ) (T : SmoothCcTensor g r s) :
    iteratedCovGrad g r s (j + 1) T =
      covGrad (I := I) (M := M) g r (s + j)
        (iteratedCovGrad g r s j T) := rfl

/-- The intrinsic `H^{2(k - j)}` Sobolev norm of the iterated covariant
derivative `∇^j T` (an `(r, s + j)`-tensor).  Packaging it as a named real
number forces all implicit arguments of `SmoothCcTensor.toHs` to be resolved
from the concretely-typed argument `iteratedCovGrad g r s j T`, which avoids
implicit-argument elaboration ambiguity inside the embedding statement. -/
noncomputable def iteratedCovGradSobolevNorm
    (g : SmoothRiemannianMetric I M) (r s k j : ℕ) (T : SmoothCcTensor g r s) : ℝ :=
  ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s + j) (2 * (k - j))
    (iteratedCovGrad g r s j T)‖

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The `C^m` tensor Sobolev embedding.**

For a closed Riemannian manifold and `2k > dim M + 2m`, there is a constant
`C > 0` such that, for every smooth compactly-supported `(r, s)`-tensor `T` and
every base point `x`, the sum of the fibre norms of the iterated covariant
derivatives `∇^j T` (`0 ≤ j ≤ m`) is bounded by `C` times the sum of the
`H^{2(k - j)}` Sobolev norms of the same iterated derivatives.

Each norm `‖(∇^j T).toSection x‖` is taken in the Riemannian fibre norm of the
`(r, s + j)`-tensor bundle (`tensorRS_riemannianBundle g r (s + j)`); each
Sobolev norm `‖(∇^j T).toHs (2 (k - j))‖` is the intrinsic `H^{2(k-j)}` norm of
the `(r, s + j)`-tensor `∇^j T`.

The proof applies the `C⁰` embedding `tensorPouSobolevHilbert_embedding_Ck_gNorm`
(its `m = 0` instance) to each higher-valence tensor `∇^j T`, whose `C⁰`
threshold `2 (k - j) > dim M` holds because `2k > dim M + 2m ≥ dim M + 2j`; the
finite maximum of the per-degree constants is the global constant. -/
theorem iteratedCovGrad_toSobolev_embedding_Cm
    (g : SmoothRiemannianMetric I M) (r s k m : ℕ)
    (h_super : 2 * k > Module.finrank ℝ E + 2 * m) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : SmoothCcTensor g r s) (x : M),
        (∑ j ∈ Finset.range (m + 1),
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r (s + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r (s + j)
            ‖(iteratedCovGrad g r s j T).toSection x‖)) ≤
          C * ∑ j ∈ Finset.range (m + 1),
            iteratedCovGradSobolevNorm g r s k j T := by
  classical
  have h_perdeg : ∀ j : ℕ,
      ∃ Cj : ℝ, 0 < Cj ∧ (j ≤ m → ∀ (T : SmoothCcTensor g r s) (x : M),
        (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r (s + j) I b) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r (s + j)
        ‖(iteratedCovGrad g r s j T).toSection x‖) ≤
          Cj * iteratedCovGradSobolevNorm g r s k j T) := by
    intro j
    by_cases hjm : j ≤ m
    · have h_super_j : 2 * (k - j) > Module.finrank ℝ E + 2 * 0 := by omega
      obtain ⟨Cj, hCj_pos, hCj⟩ :=
        tensorPouSobolevHilbert_embedding_Ck_gNorm (I := I) (M := M)
          g r (s + j) (k - j) 0 h_super_j
      exact ⟨Cj, hCj_pos,
        fun _ T x => hCj (iteratedCovGrad g r s j T) x⟩
    · exact ⟨1, one_pos, fun h => absurd h hjm⟩
  choose Cfun hCfun_pos hCfun using h_perdeg
  have hne : (Finset.range (m + 1)).Nonempty :=
    Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero m)
  set j₀ : ℕ := hne.choose with hj₀_def
  have hj₀ : j₀ ∈ Finset.range (m + 1) := hne.choose_spec
  refine ⟨(Finset.range (m + 1)).sup' hne Cfun + 1, ?_, ?_⟩
  · have hpos : 0 < Cfun j₀ := hCfun_pos j₀
    have hle : Cfun j₀ ≤ (Finset.range (m + 1)).sup' hne Cfun :=
      Finset.le_sup' Cfun hj₀
    linarith
  · intro T x
    set Cmax : ℝ := (Finset.range (m + 1)).sup' hne Cfun with hCmax_def
    have hCmax_nn : 0 ≤ Cmax :=
      le_trans (le_of_lt (hCfun_pos j₀)) (Finset.le_sup' Cfun hj₀)
    calc (∑ j ∈ Finset.range (m + 1),
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r (s + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r (s + j)
            ‖(iteratedCovGrad g r s j T).toSection x‖))
        ≤ ∑ j ∈ Finset.range (m + 1),
            Cmax * iteratedCovGradSobolevNorm g r s k j T := by
          refine Finset.sum_le_sum ?_
          intro j hj
          have hjm : j ≤ m := by have := Finset.mem_range.mp hj; omega
          refine le_trans (hCfun j hjm T x) ?_
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          exact Finset.le_sup' Cfun hj
      _ = Cmax * ∑ j ∈ Finset.range (m + 1),
            iteratedCovGradSobolevNorm g r s k j T := by
          rw [Finset.mul_sum]
      _ ≤ (Cmax + 1) * ∑ j ∈ Finset.range (m + 1),
            iteratedCovGradSobolevNorm g r s k j T := by
          refine mul_le_mul_of_nonneg_right (by linarith) ?_
          refine Finset.sum_nonneg (fun j _ => ?_)
          unfold iteratedCovGradSobolevNorm
          exact norm_nonneg _

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The `C²`, `(0, 2)`-tensor instance.**

The instance of `iteratedCovGrad_toSobolev_embedding_Cm` the DeTurck metric
family consumes: `(0, 2)`-tensors (`r = 0`, `s = 2`), `m = 2`, controlling
`‖T(x)‖`, `‖(∇T)(x)‖`, `‖(∇²T)(x)‖` for `2k > dim M + 4`.  Here `∇²T` is the
iterated covariant gradient `iteratedCovGrad g 0 2 2 T`, the `(0, 4)`-tensor
agreeing with the second covariant derivative of `T`. -/
theorem iteratedCovGrad_toSobolev_embedding_C2
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    (h_super : 2 * k > Module.finrank ℝ E + 4) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : SmoothCcTensor g 0 2) (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 (2 + j)
            ‖(iteratedCovGrad g 0 2 j T).toSection x‖)) ≤
          C * ∑ j ∈ Finset.range 3,
            iteratedCovGradSobolevNorm g 0 2 k j T := by
  have h_super' : 2 * k > Module.finrank ℝ E + 2 * 2 := by omega
  simpa using
    iteratedCovGrad_toSobolev_embedding_Cm (I := I) (M := M) g 0 2 k 2 h_super'

end DifferentialGeometry.PDE.RicciFlow

end
