import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.PosDefPerturbation
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHSSection
import DifferentialGeometry.Tensor.Multilinear.BundleSmoothEval
import DifferentialGeometry.Geometry.Connection.TensorNabla.CotangentExtension
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Regularity.EigenvectorTensorHsToWtwokTwo
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.NonlinearitySpectral
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqRiemannOpVWFactorBound
import DifferentialGeometry.Geometry.Connection.SingleSlotOperatorFiberNormBound

/-!
# Realizing a smooth `(0,2)`-tensor section as a smooth Riemannian metric perturbation

This file builds the chart-locality-free realization of a smooth, compactly
supported covariant `(0,2)`-tensor section as a *symmetric smooth bilinear
`Hom`-bundle section* of the tangent bundle, and — when the section is small in
the `g`-Riemannian fibre norm — assembles `g + h` into a genuine
`SmoothRiemannianMetric I M` through the positive-definiteness machinery of
`PosDefPerturbation.lean`.

The input is a `SmoothCcTensor g 0 2` (the type produced, on finitely-supported
spectral data, by `tensorHsSmoothRepr` in the chart-locality-free
eigenbasis twin). Its underlying section is a smooth section of the mixed
`(0,2)`-tensor bundle. We extract from it a genuine smooth bilinear form
`h x : TₓM →L[ℝ] TₓM →L[ℝ] ℝ`, symmetrize it, and add it to the background
metric.

## The extraction bridge

The fibre of the mixed `(0,2)`-tensor bundle is
`Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x` (a `(0,0)`-tensor maps to a
`(0,2)`-tensor). Evaluating at the canonical unit `(0,0)`-tensor
`constOfIsEmpty 1` (`MixedSection.toMultilinearSection`) reduces the mixed
section to a smooth `(0,2)`-multilinear section
`Tensor0SField ∞ 2`. The pointwise model value of that field is a
`ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ`, identified with a bilinear
form `TₓM →L[ℝ] TₓM →L[ℝ] ℝ` by the inverse of the fibre isometry
`bilinFormToModel` (from `DeTurckRHSSection.lean`).

Smoothness of the resulting bilinear `Hom`-section is verified through the
`Hom`-bundle smoothness criterion `cotangentCov_clmSection_smooth_aux`, reducing
to the per-tangent-section scalar smoothness supplied by
`TensorMultilinear.contMDiff_section_apply`.

## Main definitions

* `ccTensorBilin T` — the bilinear form `x ↦ (h x : TₓM →L[ℝ] TₓM →L[ℝ] ℝ)`
  extracted from a smooth `(0,2)`-tensor section `T : SmoothCcTensor g 0 2`.
* `ccTensorBilinSymm T` — its fibrewise symmetrization
  `½ (h x v w + h x w v)`.
* `tensorSectionRealizeMetric g h_small T` — the assembled
  `SmoothRiemannianMetric I M` equal fibrewise to `g + ccTensorBilinSymm T`,
  under the `g`-fibre smallness hypothesis with constant `< 1`.

## Main results

* `ccTensorBilin_contMDiff` — `ccTensorBilin T` is a smooth bilinear
  `Hom`-section.
* `ccTensorBilinSymm_contMDiff` / `ccTensorBilinSymm_symm` — the symmetrized
  section is smooth and symmetric.
* `exists_smooth_metric_of_smooth_tensor_small` — the headline: a smooth
  `(0,2)`-tensor section whose symmetrization is uniformly `g`-fibre small with
  constant `< 1` yields a genuine `SmoothRiemannianMetric` realizing
  `g + h_sym`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle ContinuousLinearMap
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace MetricRealization

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- The smooth `(0,2)`-multilinear field obtained from a smooth `(0,2)`-tensor
section by evaluating its mixed-bundle fibre at the canonical unit
`(0,0)`-tensor. This is `MixedSection.toMultilinearSection` of the underlying
section. -/
def ccTensorMultilinear (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 2 :=
  MixedSection.toMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞ T.toSection

@[simp] theorem ccTensorMultilinear_apply (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (x : M) :
    ccTensorMultilinear (I := I) g T x =
      T.toSection x
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) :=
  rfl

/-- The model `(0,2)`-multilinear value of the smooth tensor section at `x`: the
`ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ` underlying
`ccTensorMultilinear T x`.  We name it separately so that the bilinear-form
extraction matches the inverse fibre isometry on a clean, syntactically explicit
term (over the model fibre `E`), avoiding the fragile re-elaboration through the
`TangentSpace I x = E` defeq. -/
def ccTensorModel (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (x : M) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ :=
  Tensor0SSpace.toModel
    (ccTensorMultilinear (I := I) g T x : Tensor0SSpace 2 I x)

/-- The bilinear form `TₓM →L[ℝ] TₓM →L[ℝ] ℝ` extracted, at the point `x`, from a
smooth `(0,2)`-tensor section `T`.  It is the inverse fibre isometry
`bilinFormToModel` (over the model fibre `E`, identified with `TₓM` by the
tangent-space defeq) applied to the model value `ccTensorModel T x`. -/
def ccTensorBilin (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (bilinFormToModel E).symm (ccTensorModel (I := I) g T x)

/-- The value of the extracted bilinear form: it recovers the `(0,2)`-tensor
evaluation `T(x)(v, w)` (via the model value on the tuple `![v, w]`). -/
theorem ccTensorBilin_apply (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (x : M) (v w : TangentSpace I x) :
    ccTensorBilin (I := I) g T x v w =
      ccTensorModel (I := I) g T x ![v, w] :=
  bilinFormToModel_symm_apply E (ccTensorModel (I := I) g T x) v w

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The pointwise tensor Cauchy–Schwarz bound for the extracted bilinear form.**

The bilinear evaluation `ccTensorBilin g₀ T x v w` (which recovers the `(0,2)`-tensor value
`T(x)(v, w)`) is controlled by the Riemannian fibre norm of the tensor at `x` times the
`g₀`-lengths of the two arguments:

  `|ccTensorBilin g₀ T x v w| ≤ ‖T.toSection x‖_g · √(g₀ x v v) · √(g₀ x w w)`,

where `‖·‖_g` is the fibre norm of the installed `RiemannianBundle` instance
`tensorRS_riemannianBundle g₀ 0 2`.  This is the textbook pointwise tensor Cauchy–Schwarz
inequality for a covariant `(0,2)`-tensor: pairing `T(x)` with the rank-one cotensor
`v♭ ⊗ w♭` (the metric duals of `v, w`) recovers `T(x)(v, w)`, the bilinear
metric-induced Cauchy–Schwarz `tensorInnerPointwise_sq_le_mul` bounds it by the fibre norms,
and `‖v♭ ⊗ w♭‖_g = √(g₀ x v v) · √(g₀ x w w)`.

This is the single named geometric leaf of the spectral `C⁰`-control bridge
`ccTensorBilinSymm_gFibreOpBound_le_spectral_lossy`: composed with the supercritical
Sobolev embedding `H^{2k} ↪ C⁰` and the PoU → spectral norm comparison, it turns a small
`H^σ` ball into the fibre operator-norm smallness `gFibreOpBound`. -/
theorem ccTensorBilin_abs_le_fibreNorm_mul_sqrt
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) (x : M)
    (v w : TangentSpace I x) :
    letI : Bundle.RiemannianBundle
        (fun b : M => Tensor0SBundle.TensorRSSpace 0 2 I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 2
    |ccTensorBilin (I := I) g₀ T x v w| ≤
      ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ *
        Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by
  classical
  letI instTens : Bundle.RiemannianBundle
      (fun b : M => Tensor0SBundle.TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 2

  obtain ⟨n, e, _hn, horth, hpars, hexpand, hrfns⟩ :=
    tangent_frame_expansion (I := I) (M := M) g₀ x
  set B : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
    ccTensorBilin (I := I) g₀ T x with hB_def

  set coef : Fin n × Fin n → ℝ :=
    fun p => g₀.inner x (e p.1) v * g₀.inner x (e p.2) w with hcoef_def
  set comp : Fin n × Fin n → ℝ := fun p => B (e p.1) (e p.2) with hcomp_def

  have hexpV : v = ∑ i : Fin n, g₀.inner x (e i) v • e i := hexpand v
  have hexpW : w = ∑ j : Fin n, g₀.inner x (e j) w • e j := hexpand w
  have hvalue : B v w = ∑ p : Fin n × Fin n, coef p * comp p := by
    have hBv : B v = ∑ i : Fin n, g₀.inner x (e i) v • B (e i) := by
      conv_lhs => rw [hexpV]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_smul]
    have hBvw : B v w =
        ∑ i : Fin n, g₀.inner x (e i) v • (B (e i) w) := by
      rw [hBv, ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [ContinuousLinearMap.smul_apply]
    have hBeiw : ∀ i : Fin n, B (e i) w =
        ∑ j : Fin n, g₀.inner x (e j) w • B (e i) (e j) := by
      intro i
      conv_lhs => rw [hexpW]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_smul]
    rw [hBvw]
    have hdouble : (∑ i : Fin n, g₀.inner x (e i) v • (B (e i) w)) =
        ∑ i : Fin n, ∑ j : Fin n,
          (g₀.inner x (e i) v * g₀.inner x (e j) w) • B (e i) (e j) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hBeiw i, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [smul_smul]
    rw [hdouble, ← Fintype.sum_prod_type'
      (f := fun (i j : Fin n) =>
        (g₀.inner x (e i) v * g₀.inner x (e j) w) • B (e i) (e j))]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [hcoef_def, hcomp_def, smul_eq_mul]

  have hCS : (∑ p : Fin n × Fin n, coef p * comp p) ^ 2 ≤
      (∑ p : Fin n × Fin n, coef p ^ 2) * ∑ p : Fin n × Fin n, comp p ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ coef comp

  have hcoefsq : (∑ p : Fin n × Fin n, coef p ^ 2) =
      g₀.inner x v v * g₀.inner x w w := by
    rw [Fintype.sum_prod_type (f := fun p : Fin n × Fin n => coef p ^ 2)]
    rw [show (∑ i : Fin n, ∑ j : Fin n, coef (i, j) ^ 2) =
          (∑ i : Fin n, g₀.inner x (e i) v ^ 2) *
            ∑ j : Fin n, g₀.inner x (e j) w ^ 2 from ?_]
    · rw [hpars v, hpars w]
    · rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [hcoef_def]
      ring

  have hcomp_fiber : ∀ (K : Fin 0 → Fin n) (i j : Fin n),
      comp (i, j) = fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
        (T.toSection x) n e K (![i, j] : Fin 2 → Fin n) := by
    intro K i j

    have hconst : ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k : Fin 0 => g₀.inner x (e (K k))) :
          Tensor0SBundle.Tensor0SSpace 0 I x) =
        ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ) := by
      apply Tensor0SBundle.tensor0SSpace_ext
      intro u
      change ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k : Fin 0 => g₀.inner x (e (K k)))) u =
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) u
      rw [show ((ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) u : ℝ) = 1 from rfl]
      change (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ)
          (fun k => g₀.inner x (e (K k)) (u k)) = 1
      rw [ContinuousMultilinearMap.mkPiAlgebra_apply]
      exact Finset.prod_of_isEmpty _

    have hcompij : comp (i, j) = ccTensorModel (I := I) g₀ T x ![e i, e j] := by
      rw [hcomp_def, hB_def]
      exact ccTensorBilin_apply (I := I) g₀ T x (e i) (e j)
    rw [hcompij]

    unfold fiberNormSqComponent
    rw [hconst]
    have htuple : (fun k => e ((![i, j] : Fin 2 → Fin n) k)) =
        (![e i, e j] : Fin 2 → TangentSpace I x) := by
      funext k; fin_cases k <;> rfl
    rw [htuple]

    change ccTensorModel (I := I) g₀ T x ![e i, e j] =
      ((T.toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
        ![e i, e j] : ℝ)
    unfold ccTensorModel
    rw [ccTensorMultilinear_apply]
    rfl
  have hcompsq : (∑ p : Fin n × Fin n, comp p ^ 2) =
      ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ ^ 2 := by
    rw [← riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 0 2 x
      (T.toSection x)]

    rw [hrfns (T.toSection x)]
    rw [Fintype.sum_unique (fun K : Fin 0 → Fin n =>
      ∑ J : Fin 2 → Fin n,
        fiberNormSqSummand (I := I) (M := M) g₀ x 0 2 (T.toSection x) n e K J)]

    refine (Fintype.sum_equiv (finTwoArrowEquiv (Fin n))
      (fun J : Fin 2 → Fin n =>
        fiberNormSqSummand (I := I) (M := M) g₀ x 0 2 (T.toSection x) n e
          (default : Fin 0 → Fin n) J)
      (fun p : Fin n × Fin n => comp p ^ 2) ?_).symm
    intro J
    have hJ : (![J 0, J 1] : Fin 2 → Fin n) = J := by
      funext k; fin_cases k <;> rfl
    simp only [finTwoArrowEquiv_apply, Equiv.toFun_as_coe, piFinTwoEquiv_apply]
    rw [fiberNormSqSummand_eq_component_sq,
      hcomp_fiber (default : Fin 0 → Fin n) (J 0) (J 1), hJ]

  have hnorm_nn : 0 ≤ ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ := norm_nonneg _
  have hvv_nn : 0 ≤ g₀.inner x v v :=
    DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g₀ x v
  have hww_nn : 0 ≤ g₀.inner x w w :=
    DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g₀ x w
  have habs_sq : |B v w| ^ 2 ≤
      ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ ^ 2 *
        (g₀.inner x v v * g₀.inner x w w) := by
    rw [sq_abs, hvalue]
    calc (∑ p : Fin n × Fin n, coef p * comp p) ^ 2
        ≤ (∑ p : Fin n × Fin n, coef p ^ 2) * ∑ p : Fin n × Fin n, comp p ^ 2 := hCS
      _ = (g₀.inner x v v * g₀.inner x w w) *
            ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ ^ 2 := by
            rw [hcoefsq, hcompsq]
      _ = ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ ^ 2 *
            (g₀.inner x v v * g₀.inner x w w) := by ring

  have hrhs_nn : 0 ≤ ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ *
      Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) :=
    mul_nonneg (mul_nonneg hnorm_nn (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  rw [← Real.sqrt_sq (abs_nonneg (B v w))]
  rw [show ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ *
        Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) =
      Real.sqrt (‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ ^ 2 *
        (g₀.inner x v v * g₀.inner x w w)) from ?_]
  · exact Real.sqrt_le_sqrt habs_sq
  · rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hnorm_nn,
      Real.sqrt_mul hvv_nn, mul_assoc]

/-- For two smooth tangent sections `Y, W`, the scalar
`x ↦ ccTensorBilin T x (Y x) (W x)` is `C^∞`.

The scalar equals the `(0,2)`-tensor evaluation
`x ↦ ccTensorModel T x ![Y x, W x]`, which is `C^∞` by
`TensorMultilinear.contMDiff_section_apply`, consuming the underlying smoothness
field `(ccTensorMultilinear T).contMDiff`. -/
theorem ccTensorBilin_scalar_contMDiff (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2)
    (Y W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => ccTensorBilin (I := I) g T x (Y x) (W x)) := by
  have h_eval : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M =>
        Tensor0SSpace.toModel (ccTensorMultilinear (I := I) g T b)
          (fun i : Fin 2 => (![fun b => Y b, fun b => W b] : Fin 2 → ∀ b : M,
            TangentSpace I b) i b)) :=
    TensorMultilinear.contMDiff_section_apply
      (n := 2) (ccTensorMultilinear (I := I) g T)
      (ccTensorMultilinear (I := I) g T).contMDiff
      (![fun b => Y b, fun b => W b])
      (by
        intro i
        fin_cases i
        · exact Y.contMDiff
        · exact W.contMDiff)
  refine h_eval.congr ?_
  intro x
  rw [ccTensorBilin_apply]
  change ccTensorModel (I := I) g T x ![Y x, W x] =
    ccTensorModel (I := I) g T x _
  congr 1
  funext i
  fin_cases i <;> rfl

/-- **The extracted bilinear form is a smooth bilinear `Hom`-section.** -/
theorem ccTensorBilin_contMDiff (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        b (ccTensorBilin (I := I) g T b)) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => ccTensorBilin (I := I) g T x)
  intro Y
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => ccTensorBilin (I := I) g T x (Y x))
  intro W
  have h_scalar := ccTensorBilin_scalar_contMDiff (I := I) g T Y W
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change ccTensorBilin (I := I) g T y (Y y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x
      ⟨y, ccTensorBilin (I := I) g T y (Y y) (W y)⟩).2
  rfl

/-- The fibrewise symmetrization `½ (h x v w + h x w v)` of the extracted bilinear
form. As a metric perturbation must be symmetric, we symmetrize the extracted
form, which preserves smoothness and does not increase the `g`-fibre operator
norm. -/
def ccTensorBilinSymm (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (ccTensorBilin (I := I) g T x +
    (ccTensorBilin (I := I) g T x).flip)

@[simp] theorem ccTensorBilinSymm_apply (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g T x v w =
      (1 / 2 : ℝ) *
        (ccTensorBilin (I := I) g T x v w +
          ccTensorBilin (I := I) g T x w v) := by
  simp only [ccTensorBilinSymm, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]

/-- The symmetrized form is symmetric. -/
theorem ccTensorBilinSymm_symm (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g T x v w =
      ccTensorBilinSymm (I := I) g T x w v := by
  rw [ccTensorBilinSymm_apply, ccTensorBilinSymm_apply, add_comm]

/-- The symmetrized bilinear `Hom`-section is smooth: it is the
constant-scalar multiple of the sum of `ccTensorBilin T` and its fibrewise flip,
both smooth `Hom`-sections. -/
theorem ccTensorBilinSymm_contMDiff (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        b (ccTensorBilinSymm (I := I) g T b)) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => ccTensorBilinSymm (I := I) g T x)
  intro Y
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => ccTensorBilinSymm (I := I) g T x (Y x))
  intro W
  have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => ccTensorBilinSymm (I := I) g T x (Y x) (W x)) := by
    have h_eq : (fun x : M => ccTensorBilinSymm (I := I) g T x (Y x) (W x))
        = fun x : M => (1 / 2 : ℝ) *
            (ccTensorBilin (I := I) g T x (Y x) (W x) +
              ccTensorBilin (I := I) g T x (W x) (Y x)) := by
      funext x; rw [ccTensorBilinSymm_apply]
    rw [h_eq]
    exact (contMDiff_const).mul
      ((ccTensorBilin_scalar_contMDiff (I := I) g T Y W).add
        (ccTensorBilin_scalar_contMDiff (I := I) g T W Y))
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change ccTensorBilinSymm (I := I) g T y (Y y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x
      ⟨y, ccTensorBilinSymm (I := I) g T y (Y y) (W y)⟩).2
  rfl

/-- **The realized smooth metric `g + h_sym`.**  For a smooth `(0,2)`-tensor
section `T` whose symmetrization `ccTensorBilinSymm T` satisfies the `g`-fibre
operator-norm bound `gFibreOpBound g (ccTensorBilinSymm T) δ` with `δ < 1`, the
fibrewise sum `g.inner x + ccTensorBilinSymm T x` assembles into a genuine
`SmoothRiemannianMetric I M`. -/
def tensorSectionRealizeMetric (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g (ccTensorBilinSymm (I := I) g T) δ) :
    SmoothRiemannianMetric I M :=
  perturbedMetric (I := I) (M := M) g (ccTensorBilinSymm (I := I) g T)
    (ccTensorBilinSymm_symm (I := I) g T)
    (ccTensorBilinSymm_contMDiff (I := I) g T) hδ_lt hδ

@[simp] theorem tensorSectionRealizeMetric_inner (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g (ccTensorBilinSymm (I := I) g T) δ)
    (x : M) (v w : TangentSpace I x) :
    (tensorSectionRealizeMetric (I := I) g T hδ_lt hδ).inner x v w =
      g.inner x v w + ccTensorBilinSymm (I := I) g T x v w := by
  unfold tensorSectionRealizeMetric
  rw [perturbedMetric_inner, perturbedInner_apply]

/-- **Realization of a smooth `(0,2)`-tensor section as a Riemannian metric
perturbation (headline).**

For a closed Riemannian manifold `(M, g)` and a smooth, compactly-supported
covariant `(0,2)`-tensor section `T` whose extracted-and-symmetrized bilinear
form is uniformly `g`-fibre small with some constant `δ' < 1`, there is a genuine
`SmoothRiemannianMetric I M` equal fibrewise to `g + h_sym`, where
`h_sym = ccTensorBilinSymm T` is the symmetric smooth bilinear `Hom`-section
extracted from `T`.

This is the substantive (non-vacuous) `tensorHs → SmoothRiemannianMetric`
realization on the smooth representatives: the positive-definiteness of
`g + h_sym` (its quadratic form is `≥ (1 - δ') · g x v v > 0`) makes it an honest
metric, and smoothness of `h_sym` makes the assembled object `C^∞`. -/
theorem exists_smooth_metric_of_smooth_tensor_small
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g (ccTensorBilinSymm (I := I) g T) δ') :
    ∃ g' : SmoothRiemannianMetric I M,
      ∀ (x : M) (v w : TangentSpace I x),
        g'.inner x v w =
          g.inner x v w + ccTensorBilinSymm (I := I) g T x v w :=
  ⟨tensorSectionRealizeMetric (I := I) g T hδ'_lt hδ',
    fun x v w => tensorSectionRealizeMetric_inner (I := I) g T hδ'_lt hδ' x v w⟩

/-- The underlying multilinear field `ccTensorMultilinear` is `ℝ`-homogeneous in
the tensor section. -/
theorem ccTensorMultilinear_smul (g : SmoothRiemannianMetric I M)
    (c : ℝ) (T : SmoothCcTensor g 0 2) (x : M) :
    (ccTensorMultilinear (I := I) g (c • T) x : Tensor0SSpace 2 I x)
      = c • (ccTensorMultilinear (I := I) g T x : Tensor0SSpace 2 I x) := by
  unfold ccTensorMultilinear
  rw [SmoothCcTensor.toSection_smul]
  change ((c • T.toSection) x)
      (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
    = c • ((T.toSection x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
  rw [ContMDiffSection.coe_smul, Pi.smul_apply, ContinuousLinearMap.smul_apply]

/-- The model value `ccTensorModel` is `ℝ`-homogeneous in the tensor section. -/
theorem ccTensorModel_smul (g : SmoothRiemannianMetric I M)
    (c : ℝ) (T : SmoothCcTensor g 0 2) (x : M) :
    ccTensorModel (I := I) g (c • T) x = c • ccTensorModel (I := I) g T x := by
  unfold ccTensorModel
  rw [ccTensorMultilinear_smul, Tensor0SSpace.toModel_smul]

/-- The symmetrized extraction is `ℝ`-homogeneous in the tensor section. -/
theorem ccTensorBilinSymm_smul (g : SmoothRiemannianMetric I M)
    (c : ℝ) (T : SmoothCcTensor g 0 2) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g (c • T) x v w =
      c * ccTensorBilinSymm (I := I) g T x v w := by
  simp only [ccTensorBilinSymm_apply, ccTensorBilin_apply, ccTensorModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

/-- **Scaling the smallness constant.** If `ccTensorBilinSymm T` is `g`-fibre
bounded by `δ`, then `ccTensorBilinSymm (c • T)` is `g`-fibre bounded by
`|c| · δ`. -/
theorem gFibreOpBound_ccTensorBilinSymm_smul (g : SmoothRiemannianMetric I M)
    (c : ℝ) (T : SmoothCcTensor g 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g (ccTensorBilinSymm (I := I) g T) δ) :
    gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (c • T)) (|c| * δ) := by
  intro x v w
  rw [ccTensorBilinSymm_smul, abs_mul]
  have hb := hδ x v w
  have hsqv : 0 ≤ Real.sqrt (g.inner x v v) := Real.sqrt_nonneg _
  have hsqw : 0 ≤ Real.sqrt (g.inner x w w) := Real.sqrt_nonneg _
  calc |c| * |ccTensorBilinSymm (I := I) g T x v w|
      ≤ |c| * (δ * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w)) :=
        mul_le_mul_of_nonneg_left hb (abs_nonneg c)
    _ = |c| * δ * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) := by ring

/-- The symmetric smooth bilinear `Hom`-section realized from a finitely-supported
spectral Sobolev `(0,2)` element `u`, via its chart-locality-free smooth
representative. -/
def tensorHsBilinSymm (g : SmoothRiemannianMetric I M) {σ : ℝ}
    (u : tensorHs (I := I) (M := M) g 0 2 σ)
    (hu_fs : (Function.support u.coeff).Finite) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  ccTensorBilinSymm (I := I) g
    (Analysis.Parabolic.TensorSpectral.tensorHsSmoothRepr
      (I := I) (M := M) u hu_fs) x

/-- **Realization of a finitely-supported spectral `(0,2)` element as a smooth
Riemannian metric perturbation.**

For a closed Riemannian manifold `(M, g_bg)` and a finitely-supported element
`u : tensorHs g_bg 0 2 σ`, with smooth representative `T = tensorHsSmoothRepr…`,
if the symmetric extracted form `tensorHsBilinSymm u hu_fs` is uniformly
`g_bg`-fibre small with constant `δ' < 1`, there is a genuine
`SmoothRiemannianMetric I M` equal fibrewise to `g_bg + h_sym`. This is the
HLCC-free `tensorHs → SmoothRiemannianMetric` realization on the smooth
representatives (the dense, smooth subspace of finitely-supported spectral data). -/
theorem exists_smooth_metric_of_tensorHs_small
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    (u : tensorHs (I := I) (M := M) g_bg 0 2 σ)
    (hu_fs : (Function.support u.coeff).Finite)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g_bg
      (tensorHsBilinSymm (I := I) g_bg u hu_fs) δ') :
    ∃ g' : SmoothRiemannianMetric I M,
      ∀ (x : M) (v w : TangentSpace I x),
        g'.inner x v w =
          g_bg.inner x v w + tensorHsBilinSymm (I := I) g_bg u hu_fs x v w :=
  exists_smooth_metric_of_smooth_tensor_small (I := I) g_bg
    (Analysis.Parabolic.TensorSpectral.tensorHsSmoothRepr
      (I := I) (M := M) u hu_fs) hδ'_lt hδ'

open scoped Classical in
/-- **The substantive realization map.**  Sends `u : H^{a+2}` to the genuine
smooth Riemannian metric `g_bg + h_sym(u)` whenever `u` is finitely supported
and its symmetric extracted form is `g_bg`-fibre small with constant `< 1`, and
to `g_bg` otherwise.  On its validity domain it produces an honest `C^∞` metric
realizing `g_bg + h`. -/
noncomputable def realizeMetricMap (g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2)) :
    SmoothRiemannianMetric I M :=
  if h : ∃ (hu_fs : (Function.support u.coeff).Finite) (δ' : ℝ), δ' < 1 ∧
      gFibreOpBound (I := I) (M := M) g_bg
        (tensorHsBilinSymm (I := I) g_bg u hu_fs) δ' then
    tensorSectionRealizeMetric (I := I) g_bg
      (Analysis.Parabolic.TensorSpectral.tensorHsSmoothRepr
        (I := I) (M := M) u h.choose)
      h.choose_spec.choose_spec.1 h.choose_spec.choose_spec.2
  else
    g_bg

/-- On its validity domain, the realization map genuinely realizes
`g_bg + h_sym`: the perturbed metric's inner product is the sum of `g_bg`'s and
the symmetric extracted form `tensorHsBilinSymm`. -/
theorem realizeMetricMap_eq_of_small (g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2))
    (hu_fs : (Function.support u.coeff).Finite)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g_bg
      (tensorHsBilinSymm (I := I) g_bg u hu_fs) δ')
    (x : M) (v w : TangentSpace I x) :
    (realizeMetricMap (I := I) g_bg a u).inner x v w =
      g_bg.inner x v w + tensorHsBilinSymm (I := I) g_bg u hu_fs x v w := by
  classical
  have hex : ∃ (hu_fs : (Function.support u.coeff).Finite) (δ' : ℝ), δ' < 1 ∧
      gFibreOpBound (I := I) (M := M) g_bg
        (tensorHsBilinSymm (I := I) g_bg u hu_fs) δ' :=
    ⟨hu_fs, δ', hδ'_lt, hδ'⟩
  rw [realizeMetricMap, dif_pos hex]
  rw [tensorSectionRealizeMetric_inner]
  rfl

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
