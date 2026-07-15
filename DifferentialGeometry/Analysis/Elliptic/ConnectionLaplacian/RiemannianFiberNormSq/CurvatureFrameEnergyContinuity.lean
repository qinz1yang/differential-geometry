import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.RiemannianFiberNormSqRiemannOpHigherRankParseval
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartFiberTrivialisationOpNorm.ChartRiemannDataUniformBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorCurvatureUnitEvalBridge
import Mathlib.Topology.Order.Compact

/-!
# Continuous frame-energy bound for the tensor curvature operator

For a smooth Riemannian metric `g` on a *closed* manifold `M` and any covariant rank `t`,
this file posits the genuinely-deep DG/analysis primitive underlying the *continuous*
proportional curvature-operator fibre bound: a **continuous** nonnegative envelope
`Ccurv : M → ℝ` bounding, at every base point `x` and for any `g`-orthonormal frame `e` of
`T_x M`, the **frame energy** of the bundled tensor curvature operator
`R_x = riemannOp (tensorCov g 0 t) x` acting on a `(0, t)`-tensor `T`:

```
∑_{i, j} riemannianFiberNormSq g 0 t x (R_x(e_i, e_j) T) ≤ Ccurv x · riemannianFiberNormSq g 0 t x T.
```

The frame energy `∑_{i, j} ‖R_x(e_i, e_j) T‖²_g` is the squared Hilbert–Schmidt norm of the
linear map `T ↦ R_x(·, ·) T` measured against the `g`-orthonormal frame pair `(e_i, e_j)`; it is
**frame-independent** (a `g`-orthonormal change of frame is an orthogonal substitution under
which the double sum is invariant), so its least proportional bound is the intrinsic
curvature-operator Hilbert–Schmidt norm squared `‖R_x‖²_HS`, a base-point function of `g` alone.

This is the sole genuinely-irreducible analytic content (continuity of the curvature-operator
Hilbert–Schmidt norm) feeding
`exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional`; the `(v, w)`-factor
`riemannianFiberNormSq_riemannOp_tensorCovS_vw_factor_le` and the uniformisation over the compact
`M` are proved on top of it.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1600000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- `finrank ℝ (Tensor0SModel t ℝ E) = (finrank ℝ E) ^ t`. Re-derivation of the chart-inner
finrank fact by induction on the multilinear-curry equivalences. -/
private lemma finrank_tensor0SModel_eq_cfec (t : ℕ) :
    Module.finrank ℝ (Tensor0SModel t ℝ E) = (Module.finrank ℝ E) ^ t := by
  induction t with
  | zero =>
      rw [pow_zero, (continuousMultilinearCurryFin0 ℝ E ℝ).toLinearEquiv.finrank_eq]
      exact Module.finrank_self ℝ
  | succ t ih =>
      rw [(continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (t + 1) => E) ℝ).toLinearEquiv.finrank_eq]
      let φ : (E →L[ℝ] Tensor0SModel t ℝ E) ≃ₗ[ℝ] (E →ₗ[ℝ] Tensor0SModel t ℝ E) :=
        { toFun := fun f => f.toLinearMap
          invFun := fun f => LinearMap.toContinuousLinearMap f
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      rw [φ.finrank_eq, Module.finrank_linearMap, ih]
      ring

/-- `finrank ℝ (TensorRSSpace 0 t I x) = (finrank ℝ E) ^ t`: the `(0, t)`-tensor fibre has
dimension `dⁱ` with `d = finrank ℝ E`. The fibre is linearly equivalent to the model
`TensorRSModel 0 t ℝ E = (Tensor0SModel 0 ℝ E) →L[ℝ] (Tensor0SModel t ℝ E)`, whose source is
one-dimensional (rank-`0` tensors are scalars), so its dimension is `1 · dⁱ`. -/
private lemma finrank_tensorRSSpace_zero_eq (t : ℕ) (x : M) :
    Module.finrank ℝ (TensorRSSpace 0 t I x) = (Module.finrank ℝ E) ^ t := by
  rw [(tensorRSSpace_continuousLinearEquiv (𝕜 := ℝ) (E := E) (I := I) (M := M)
    0 t x).toLinearEquiv.finrank_eq]
  change Module.finrank ℝ (Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel t ℝ E) = _
  let φ : (Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel t ℝ E) ≃ₗ[ℝ]
      (Tensor0SModel 0 ℝ E →ₗ[ℝ] Tensor0SModel t ℝ E) :=
    { toFun := fun f => f.toLinearMap
      invFun := fun f => LinearMap.toContinuousLinearMap f
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  rw [φ.finrank_eq, Module.finrank_linearMap, finrank_tensor0SModel_eq_cfec,
    finrank_tensor0SModel_eq_cfec, pow_zero, one_mul]

/-- **The `g`-orthonormal frame in the rfns representation is a `Module.Basis` (rank `≥ 1`).**
For a `g`-orthonormal family `e : Fin n → T_x M` (`horth`) that represents the intrinsic fibre
norm squared at rank `t ≥ 1` as the frame double sum (`hrepr`), the family `e` is a basis: it
is `g`-orthonormal hence linearly independent (so `n ≤ d := finrank ℝ (T_x M)`), and the
component map `T ↦ (T(e_J))_J` from the `dᵗ`-dimensional `(0, t)`-tensor fibre into `ℝ^{nᵗ}` is
injective by `hrepr` plus positive-definiteness of `rfns` (so `dᵗ ≤ nᵗ`, hence `d ≤ n` since
`t ≥ 1`). Therefore `n = d`, and the linearly-independent family of the right cardinality is a
basis. -/
private lemma orthonormal_rfns_exists_basis
    (g : SmoothRiemannianMetric I M) (t : ℕ) (x : M) (ht : 1 ≤ t)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (hrepr : ∀ S : TensorRSSpace 0 t I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 t x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin t → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 t S n e K J) :
    ∃ bse : Module.Basis (Fin n) ℝ (TangentSpace I x), ∀ i : Fin n, bse i = e i := by
  classical

  let cd : InnerProductSpace.Core ℝ (TangentSpace I x) := g.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun v : TangentSpace I x => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt x
  have hbnd : Bornology.IsVonNBounded ℝ {v : TangentSpace I x |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded x
  letI nag : NormedAddCommGroup (TangentSpace I x) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  letI ips : InnerProductSpace ℝ (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  have hinner_eq : ∀ u v : TangentSpace I x, (inner ℝ u v : ℝ) = g.inner x u v :=
    fun u v => rfl
  set d : ℕ := Module.finrank ℝ (TangentSpace I x) with hd_def
  have hdE : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl

  have horthonormal : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    intro i j; rw [hinner_eq (e i) (e j)]; exact horth i j
  have hli : LinearIndependent ℝ e := horthonormal.linearIndependent
  have hn_le_d : n ≤ d := by
    have := hli.fintype_card_le_finrank
    simpa using this

  set Φ : TensorRSSpace 0 t I x →ₗ[ℝ] ((Fin t → Fin n) → ℝ) :=
    { toFun := fun T J => fiberNormSqComponent (I := I) (M := M) g x 0 t T n e
        (fun k => k.elim0) J
      map_add' := by
        intro T T'; funext J
        exact fiberNormSqComponent_add (I := I) (M := M) g x 0 t T T' n e _ J
      map_smul' := by
        intro c T; funext J
        rw [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        exact fiberNormSqComponent_smul (I := I) (M := M) g x 0 t c T n e _ J } with hΦ_def
  have hΦ_inj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot]
    rw [LinearMap.ker_eq_bot']
    intro T hT

    have hcomp0 : ∀ J : Fin t → Fin n,
        fiberNormSqComponent (I := I) (M := M) g x 0 t T n e (fun k => k.elim0) J = 0 := by
      intro J; exact congrFun hT J
    have hrfns0 : riemannianFiberNormSq (I := I) (M := M) g 0 t x T = 0 := by
      rw [hrepr T]
      refine Finset.sum_eq_zero (fun K _ => Finset.sum_eq_zero (fun J _ => ?_))
      rw [fiberNormSqSummand_eq_component_sq]
      rw [show K = (fun k : Fin 0 => k.elim0) from funext (fun k => k.elim0)]
      rw [hcomp0 J]; ring

    have hpd := riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 t x T
    rw [hrfns0] at hpd
    have hTm0 : TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := 0) (s := t) (x := x) T = 0 :=
      (L2.tensorInnerPointwise_eq_zero_iff (I := I) (M := M) g 0 t x _).mp hpd.symm
    have hT0model : TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := 0) (s := t) (x := x) T =
      TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := 0) (s := t) (x := x) (0 : TensorRSSpace 0 t I x) := by
      rw [hTm0]
      exact (map_zero (tensorRSSpace_continuousLinearEquiv (𝕜 := ℝ) (E := E) (I := I) (M := M)
        0 t x)).symm
    exact TensorRSSpace.toModel_injective (𝕜 := ℝ) (E := E) (I := I) (M := M) hT0model
  have hdt_le_nt : (d : ℕ) ^ t ≤ n ^ t := by
    have hle := LinearMap.finrank_le_finrank_of_injective hΦ_inj
    rw [finrank_tensorRSSpace_zero_eq (I := I) (M := M) t x, hdE.symm] at hle
    rw [Module.finrank_pi, Fintype.card_pi] at hle
    simp only [Fintype.card_fin] at hle
    calc (d : ℕ) ^ t = Module.finrank ℝ (TangentSpace I x) ^ t := by rw [hd_def]
      _ ≤ n ^ t := by
            convert hle using 2
            simp [Fintype.card_fin]
  have hd_pos : 0 < d := by
    rw [hd_def, hdE]; exact Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
  have hd_le_n : d ≤ n := by
    by_contra hlt
    rw [not_le] at hlt
    exact absurd hdt_le_nt (not_le.mpr (Nat.pow_lt_pow_left hlt (by omega)))
  have hcard : Fintype.card (Fin n) = d := by
    rw [Fintype.card_fin]; omega

  haveI : Nonempty (Fin n) := by
    rw [← Fintype.card_pos_iff, hcard]; exact hd_pos
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by rw [hcard, hd_def]), ?_⟩
  intro i
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]

/-- **Uniform-over-`M` single-term dual-frame curvature bound (genuine analytic primitive).**
For a smooth Riemannian metric `g` on a closed manifold `M` and any covariant rank `t`, there is a
*single* nonnegative constant `K`, independent of the base point, of the `g`-orthonormal frame `e`,
and of the frame indices, bounding **one** dual-frame curvature term
`riemannianFiberNormSq g 0 t x (R_x(e_i, e_j)(dualTensorFrameS g x t e J))`:

```
riemannianFiberNormSq g 0 t x (R_x(e_i, e_j)(dualTensorFrameS g x t e J)) ≤ K,
```

at every base point `x`, every `g`-orthonormal frame `e` of `T_x M`
(`g.inner x (e i) (e j) = δ_{ij}`), and all frame indices `i, j, J`, where
`R = riemannOp (tensorCov g 0 t)` is the bundled tensor curvature operator.

**Why this is TRUE — and why it is strictly more primitive than the displayed energy sum.** The
quantity `R_x(e_i, e_j)(dualTensorFrameS g x t e J)` is the tensor curvature operator applied to a
fixed **normalised** input: the dual tensor frame `dualTensorFrameS g x t e J` is the unit
frame-coordinate tensor (its `g`-fibre norm is `1`), and the frame pair `(e_i, e_j)` is `g`-unit.
By the slot-wise tensor curvature formula `riemannSec_tensor0SCov_apply_eval` the tensor curvature
`R_x(e_i, e_j)` acts as the negated sum over slots of the base-tangent Riemann curvature
`R^{TM}_x(e_i, e_j)` inserted into each argument; since `e_i, e_j` are unit `g`-vectors, the
base-tangent curvature `R^{TM}_x(e_i, e_j)` (equal, in any chart at `α`, to the chart-coordinate
sum `chartRiemannCLM g α e_i e_j` of the chart Riemann tensor entries) has `g`-operator norm
bounded by the chart Riemann data, which is `C^∞` (polynomial in the chart Christoffel symbols and
their first partials) and *uniformly bounded* on the compact chart-`α` partition-of-unity support
by `exists_chartRiemannData_uniform_bound_compact`. Hence a single application — bounded
independently of the frame because all inputs are `g`-unit — has intrinsic fibre norm bounded by a
fixed chart-data envelope on each of the finitely-many compact chart supports that cover `M`, whose
maximum is the global constant `K`. This is the chart-locality-free route (no
`HasLocallyConstantChartAt`, no chart-trivialisation operator-norm scalar); the only chart objects
are the bounded chart Christoffel / Riemann data and the positive-definite chart Gram matrix.

**Non-vacuity.** A degenerate witness `K = 0` is rejected on any non-flat manifold: at a point `x`
where the curvature operator is nonzero there is a `g`-orthonormal frame pair `(e_i, e_j)` and a
dual frame index `J` with `R_x(e_i, e_j)(dualTensorFrameS g x t e J) ≠ 0`, hence the term
`riemannianFiberNormSq g 0 t x (R_x(e_i, e_j)(dualTensorFrameS g x t e J)) > 0`, so `K` must carry
the genuine curvature magnitude — it cannot be the trivial zero constant. -/
theorem exists_uniform_riemannOp_tensorCovS_dualFrameEnergy_single_term_bound
    (g : SmoothRiemannianMetric I M) (t : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (x : M) {n : ℕ} (e : Fin n → TangentSpace I x),
        (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) →
        ∀ (i j : Fin n) (J : Fin t → Fin n),
          riemannianFiberNormSq (I := I) (M := M) g 0 t x
            (riemannOp (tensorCov (I := I) g 0 t) x (e i) (e j)
              (dualTensorFrameS (I := I) (M := M) g x t e J)) ≤ K :=
  exists_uniform_riemannOp_tensorCovS_dualFrameEnergy_single_term_bound' (I := I) (M := M) g t

/-- **Posited uniform-over-`M` dual-frame curvature energy constant.** For a smooth Riemannian
metric `g` on a closed manifold `M` and any covariant rank `t`, there is a *single* nonnegative
constant `C`, independent of the base point and of the chosen frame, bounding the **dual-frame
curvature energy**
`∑_{i, j} ∑_J riemannianFiberNormSq g 0 t x (R_x(e_i, e_j)(dualTensorFrameS g x t e J))`
at every base point `x` and for every `g`-orthonormal frame `e` of `T_x M`:

```
∑_{i, j} ∑_J riemannianFiberNormSq g 0 t x
    (R_x(e_i, e_j)(dualTensorFrameS g x t e J)) ≤ C,
```

where `R = riemannOp (tensorCov g 0 t)` is the bundled tensor curvature operator and `e` (of
size `n`) is `g`-orthonormal (`g.inner x (e i) (e j) = δ_{ij}`). This is the **tensor-free**
(`T`-independent) intrinsic curvature-operator energy: the dual tensor frame
`dualTensorFrameS g x t e J` is the fixed frame-coordinate tensor, so the displayed sum measures
the Hilbert–Schmidt energy of the curvature action `(u, u') ↦ R_x(u, u')(·)` against the
`g`-orthonormal frame pair `(e_i, e_j)` and the frame tensor coordinates, with no dependence on a
source tensor `T`.

**Why this is TRUE.** Fix `x`. The displayed sum is the squared Hilbert–Schmidt norm of the
bilinear curvature action measured against the `g`-orthonormal frame pair and the dual tensor
frame; under a `g`-orthonormal change of frame the double sum transforms by an orthogonal
substitution in each tangent slot and the dual-frame coordinates rotate by the inverse, so the
sum is **frame-independent** and equals the intrinsic curvature-operator Hilbert–Schmidt norm
squared `‖R_x‖²_HS`, a function of `x` through `g` alone. By the slot-wise tensor curvature
formula `riemannSec_tensor0SCov_apply_eval` the tensor curvature `R_x(e_i, e_j)` acts as the
negated sum over slots of the **base-tangent** Riemann curvature `R^{TM}_x(e_i, e_j)` inserted
into each argument; since `e_i, e_j` are unit `g`-vectors, the base-tangent curvature
`R^{TM}_x(e_i, e_j)` (equal, in any chart at `α`, to the chart-coordinate sum
`chartRiemannCLM g α e_i e_j` of the chart Riemann tensor entries) has `g`-operator norm bounded
by the chart Riemann data, which is `C^∞` (polynomial in the chart Christoffel symbols and their
first partials) and *uniformly bounded* on the compact chart-`α` partition-of-unity support by
`exists_chartRiemannData_uniform_bound_compact`. Composing the single-slot insertions and summing
over the finitely-many slots and frame pairs (with `n = finrank E` fixed) yields a bound by a
fixed chart-data envelope on each of the finitely-many compact chart supports that cover `M`,
whose maximum is the global constant `C`. This is the chart-locality-free route (no
`HasLocallyConstantChartAt`, no chart-trivialisation operator-norm scalar); the only chart objects
are the bounded chart Christoffel / Riemann data and the positive-definite chart Gram matrix.

**Non-vacuity.** A degenerate witness `C = 0` is rejected on any non-flat manifold: at a point `x`
where the curvature operator is nonzero there is a `g`-orthonormal frame pair `(e_i, e_j)` and a
dual frame index `J` with `R_x(e_i, e_j)(dualTensorFrameS g x t e J) ≠ 0`, hence the displayed sum
is strictly positive (a sum of squared fibre norms with a strictly positive term), so `C` must
carry the genuine curvature magnitude — it cannot be the trivial zero constant. -/
theorem exists_uniform_riemannOp_tensorCovS_dualFrameEnergy_const
    (g : SmoothRiemannianMetric I M) (t : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x : M) {n : ℕ} (e : Fin n → TangentSpace I x),
        (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) →
        (∑ i : Fin n, ∑ j : Fin n, ∑ J : Fin t → Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 t x
              (riemannOp (tensorCov (I := I) g 0 t) x (e i) (e j)
                (dualTensorFrameS (I := I) (M := M) g x t e J))) ≤ C := by
  classical

  obtain ⟨K, hK_nonneg, hK_term⟩ :=
    exists_uniform_riemannOp_tensorCovS_dualFrameEnergy_single_term_bound (I := I) (M := M) g t
  set d : ℕ := Module.finrank ℝ E with hd_def
  refine ⟨(d : ℝ) ^ (t + 2) * K, ?_, ?_⟩
  · exact mul_nonneg (pow_nonneg (Nat.cast_nonneg d) _) hK_nonneg
  intro x n e horth

  have hn_le_d : n ≤ d := by
    let cd : InnerProductSpace.Core ℝ (TangentSpace I x) := g.toRiemannianMetric.toCore x
    have hc : ContinuousAt (fun v : TangentSpace I x => cd.inner v v) 0 :=
      g.toRiemannianMetric.continuousAt x
    have hbnd : Bornology.IsVonNBounded ℝ {v : TangentSpace I x |
        RCLike.re (cd.inner v v) < 1} :=
      g.toRiemannianMetric.isVonNBounded x
    letI nag : NormedAddCommGroup (TangentSpace I x) :=
      cd.toNormedAddCommGroupOfTopology hc hbnd
    letI ips : InnerProductSpace ℝ (TangentSpace I x) :=
      InnerProductSpace.ofCoreOfTopology cd hc hbnd
    have hinner_eq : ∀ u v : TangentSpace I x, (inner ℝ u v : ℝ) = g.inner x u v :=
      fun u v => rfl
    have horthonormal : Orthonormal ℝ e := by
      rw [orthonormal_iff_ite]
      intro i j; rw [hinner_eq (e i) (e j)]; exact horth i j
    have hcard := horthonormal.linearIndependent.fintype_card_le_finrank
    have hcardE : Module.finrank ℝ (TangentSpace I x) = d := rfl
    rw [hcardE] at hcard
    simpa using hcard

  have hsum_le_const :
      (∑ i : Fin n, ∑ j : Fin n, ∑ J : Fin t → Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 t x
            (riemannOp (tensorCov (I := I) g 0 t) x (e i) (e j)
              (dualTensorFrameS (I := I) (M := M) g x t e J))) ≤
        ∑ _i : Fin n, ∑ _j : Fin n, ∑ _J : Fin t → Fin n, K := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    refine Finset.sum_le_sum (fun j _ => ?_)
    refine Finset.sum_le_sum (fun J _ => ?_)
    exact hK_term x e horth i j J
  refine le_trans hsum_le_const ?_

  have hconst_eq :
      (∑ _i : Fin n, ∑ _j : Fin n, ∑ _J : Fin t → Fin n, K) = (n : ℝ) ^ (t + 2) * K := by
    rw [Finset.sum_const, Finset.sum_const, Finset.sum_const]
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  rw [hconst_eq]

  refine mul_le_mul_of_nonneg_right ?_ hK_nonneg
  exact pow_le_pow_left₀ (Nat.cast_nonneg n) (by exact_mod_cast hn_le_d) (t + 2)

/-- **Posited continuous frame-energy bound for the tensor curvature operator.** For a smooth
Riemannian metric `g` on a closed manifold `M` and any covariant rank `t`, there is a
*continuous* nonnegative function `Ccurv : M → ℝ` such that, at every base point `x` and for any
`g`-orthonormal frame `e` of `T_x M` representing `riemannianFiberNormSq` as its frame double
sum, the curvature **frame energy** is bounded proportionally to the source fibre norm:

```
∑_{i, j} riemannianFiberNormSq g 0 t x (R_x(e_i, e_j) T)
  ≤ Ccurv x · riemannianFiberNormSq g 0 t x T,
```

where `R = riemannOp (tensorCov g 0 t)` is the bundled tensor curvature operator and the frame
`e` (with size `n`) satisfies `g`-orthonormality `g.inner x (e i) (e j) = δ_{ij}` and the
`riemannianFiberNormSq` frame representation `hrepr`.

**Why this is TRUE.** Fix `x`. The frame energy `∑_{i, j} ‖R_x(e_i, e_j) T‖²_g` is the squared
Hilbert–Schmidt norm of the bilinear curvature action `(u, u') ↦ R_x(u, u') T` evaluated against
the `g`-orthonormal frame pair `(e_i, e_j)`; under a `g`-orthonormal change of frame the double
sum transforms by an orthogonal substitution in each tangent slot and is therefore **invariant**,
so the least proportional constant for the displayed bound equals the intrinsic
curvature-operator Hilbert–Schmidt norm squared `‖R_x‖²_HS`, a function of the base point `x`
through `g` alone (independent of which orthonormal frame is chosen). This intrinsic
curvature-operator norm is **continuous** in `x` because the curvature operator is assembled from
the smooth metric `g` and the smooth Levi-Civita Riemann tensor: in any chart at `α` the
chart-coordinate Riemann coefficients `chartRiemannTensor g α i j k l (ϕ_α b)` are `C^∞`
(polynomial in the chart Christoffel symbols and their first partials) and *uniformly bounded* on
the compact chart-`α` partition-of-unity support by `exists_chartRiemannData_uniform_bound_compact`;
the intrinsic fibre norm of the curvature action is controlled, through the forward chart-frame
Gram Rayleigh route and its reverse companion, by these bounded smooth chart-data, yielding a
continuous (indeed locally Lipschitz) envelope `Ccurv` on the finitely-many compact chart supports
that cover `M`, patched to a global continuous function by the partition of unity. This is the
chart-locality-free route (no `HasLocallyConstantChartAt`, no chart-trivialisation operator-norm
scalar); the only chart objects are the bounded chart Christoffel / Riemann data and the
positive-definite chart Gram matrix.

**Non-vacuity.** A degenerate witness `Ccurv ≡ 0` is rejected on any non-flat manifold: at a point
`x` where the curvature operator is nonzero there is a `g`-orthonormal frame pair `(e_i, e_j)` and
a tensor `T` with `R_x(e_i, e_j) T ≠ 0`, hence the frame energy
`∑_{i, j} riemannianFiberNormSq g 0 t x (R_x(e_i, e_j) T) > 0` (a sum of squared fibre norms with a
strictly positive term) while the right-hand side `0 · riemannianFiberNormSq g 0 t x T = 0`,
contradicting the bound. So the envelope must carry the genuine curvature magnitude — it cannot be
the trivial zero function. -/
theorem exists_continuous_riemannOp_tensorCovS_frameEnergy_bound
    (g : SmoothRiemannianMetric I M) (t : ℕ) :
    ∃ Ccurv : M → ℝ, Continuous Ccurv ∧ (∀ x : M, 0 ≤ Ccurv x) ∧
      ∀ (x : M) {n : ℕ} (e : Fin n → TangentSpace I x),
        (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) →
        (∀ S : TensorRSSpace 0 t I x,
          riemannianFiberNormSq (I := I) (M := M) g 0 t x S =
            ∑ K : Fin 0 → Fin n, ∑ J : Fin t → Fin n,
              fiberNormSqSummand (I := I) (M := M) g x 0 t S n e K J) →
        ∀ T : TensorRSSpace 0 t I x,
          (∑ i : Fin n, ∑ j : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 t x
                (riemannOp (tensorCov (I := I) g 0 t) x (e i) (e j) T)) ≤
            Ccurv x * riemannianFiberNormSq (I := I) (M := M) g 0 t x T := by
  classical
  obtain ⟨C, hC_nonneg, hC_bound⟩ :=
    exists_uniform_riemannOp_tensorCovS_dualFrameEnergy_const (I := I) (M := M) g t
  refine ⟨fun _ => C, continuous_const, fun _ => hC_nonneg, ?_⟩
  intro x n e horth hrepr T

  have hCx_le_C :
      (∑ i : Fin n, ∑ j : Fin n, ∑ J : Fin t → Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 t x
            (riemannOp (tensorCov (I := I) g 0 t) x (e i) (e j)
              (dualTensorFrameS (I := I) (M := M) g x t e J))) ≤ C :=
    hC_bound x e horth
  have hrfns_nonneg : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 t x T :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 t x T
  rcases Nat.eq_zero_or_pos t with ht0 | htpos
  · -- Rank-`0` (scalar) case: the `(0, 0)`-tensor fibre is one-dimensional, spanned by the unit
    -- dual frame `dualTensorFrameS g x 0 e J₀`, so `T = c • (that unit)` with `c² = rfns T`.
    subst ht0
    set J₀ : Fin 0 → Fin n := fun k => k.elim0 with hJ₀

    set φ : TensorRSSpace 0 0 I x → ℝ :=
      fun S => fiberNormSqComponent (I := I) (M := M) g x 0 0 S n e J₀ J₀ with hφ_def

    have hrfns_sq : ∀ S : TensorRSSpace 0 0 I x,
        riemannianFiberNormSq (I := I) (M := M) g 0 0 x S = φ S ^ 2 := by
      intro S
      rw [hrepr S]
      rw [Finset.sum_eq_single J₀ (fun K _ hK => absurd (Subsingleton.elim K J₀) hK)
        (fun h => absurd (Finset.mem_univ J₀) h)]
      rw [Finset.sum_eq_single J₀ (fun J _ hJ => absurd (Subsingleton.elim J J₀) hJ)
        (fun h => absurd (Finset.mem_univ J₀) h)]
      simp only [hφ_def]
      rw [fiberNormSqSummand_eq_component_sq]

    have hφ_unit : φ (dualTensorFrameS (I := I) (M := M) g x 0 e J₀) = 1 := by
      simp only [hφ_def]
      rw [fiberNormSqComponent_dualTensorFrameS (I := I) (M := M) g x 0 e horth J₀ J₀ J₀]
      simp

    have hφ_smul : ∀ (a : ℝ) (S : TensorRSSpace 0 0 I x), φ (a • S) = a * φ S := by
      intro a S; simp only [hφ_def]; rw [fiberNormSqComponent_smul]

    have hφ_inj : ∀ S : TensorRSSpace 0 0 I x, φ S = 0 → S = 0 := by
      intro S hS
      have hrfns0 : riemannianFiberNormSq (I := I) (M := M) g 0 0 x S = 0 := by
        rw [hrfns_sq S, hS]; ring
      have hpd := riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 0 x S
      rw [hrfns0] at hpd
      have hSm0 : TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
          (r := 0) (s := 0) (x := x) S = 0 :=
        (L2.tensorInnerPointwise_eq_zero_iff (I := I) (M := M) g 0 0 x _).mp hpd.symm
      have : TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
          (r := 0) (s := 0) (x := x) S =
        TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
          (r := 0) (s := 0) (x := x) (0 : TensorRSSpace 0 0 I x) := by
        rw [hSm0]; exact (map_zero _).symm
      exact TensorRSSpace.toModel_injective (𝕜 := ℝ) (E := E) (I := I) (M := M) this

    set D := dualTensorFrameS (I := I) (M := M) g x 0 e J₀ with hD_def
    have hT_eq : T = φ T • D := by
      have hdiff : φ (T - φ T • D) = 0 := by
        simp only [hφ_def]
        rw [show (T - φ T • D : TensorRSSpace 0 0 I x) = T + (-(φ T)) • D from by
          rw [neg_smul]; abel]
        rw [fiberNormSqComponent_add, fiberNormSqComponent_smul]
        have hφD : fiberNormSqComponent (I := I) (M := M) g x 0 0 D n e J₀ J₀ = 1 := hφ_unit
        rw [hφD]; ring
      have hTD : T - φ T • D = 0 := hφ_inj _ hdiff
      exact sub_eq_zero.mp hTD

    have hLHS_eq :
        (∑ i : Fin n, ∑ j : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 0 x
              (riemannOp (tensorCov (I := I) g 0 0) x (e i) (e j) T)) =
          φ T ^ 2 *
            ∑ i : Fin n, ∑ j : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 0 x
                (riemannOp (tensorCov (I := I) g 0 0) x (e i) (e j) D) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      conv_lhs => rw [hT_eq, (riemannOp (tensorCov (I := I) g 0 0) x (e i) (e j)).map_smul (φ T) D]

      rw [hrfns_sq, hrfns_sq]
      have : φ (φ T • riemannOp (tensorCov (I := I) g 0 0) x (e i) (e j) D) =
          φ T * φ (riemannOp (tensorCov (I := I) g 0 0) x (e i) (e j) D) := hφ_smul _ _
      rw [this]; ring
    rw [hLHS_eq, hrfns_sq T]
    rw [show (fun _ : M => C) x = C from rfl]

    have hsq_nonneg : (0 : ℝ) ≤ φ T ^ 2 := sq_nonneg _
    have henergy0_le_C :
        (∑ i : Fin n, ∑ j : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 0 x
              (riemannOp (tensorCov (I := I) g 0 0) x (e i) (e j) D)) ≤ C := by
      refine le_trans (le_of_eq ?_) hCx_le_C
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [Finset.sum_eq_single J₀ (fun J _ hJ => absurd (Subsingleton.elim J J₀) hJ)
        (fun h => absurd (Finset.mem_univ J₀) h)]
    rw [mul_comm C (φ T ^ 2)]
    exact mul_le_mul_of_nonneg_left henergy0_le_C hsq_nonneg
  · -- Rank-`≥ 1` case: the basis bridge + the Cauchy–Schwarz frame-energy reduction.
    obtain ⟨bse, hbse⟩ :=
      orthonormal_rfns_exists_basis (I := I) (M := M) g t x htpos e horth hrepr
    calc
      (∑ i : Fin n, ∑ j : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 t x
            (riemannOp (tensorCov (I := I) g 0 t) x (e i) (e j) T))
          ≤ (∑ i : Fin n, ∑ j : Fin n, ∑ J : Fin t → Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 t x
                (riemannOp (tensorCov (I := I) g 0 t) x (e i) (e j)
                  (dualTensorFrameS (I := I) (M := M) g x t e J))) *
            riemannianFiberNormSq (I := I) (M := M) g 0 t x T :=
            sum_riemannianFiberNormSq_riemannOpS_le_Cx
              (I := I) (M := M) g x t e bse hbse horth hrepr T
      _ ≤ C * riemannianFiberNormSq (I := I) (M := M) g 0 t x T :=
            mul_le_mul_of_nonneg_right hCx_le_C hrfns_nonneg

end Connection
end Integral
end DifferentialGeometry

end
