import DifferentialGeometry.Integral.Connection.TensorRicciCommutator

/-!
# The pointwise third-order Weitzenböck commutator (order-`2` Gårding core)

Let `g : SmoothRiemannianMetric I M` be a smooth Riemannian metric on a closed manifold
`M`, and `cov := tensorCov g r s` the induced covariant derivative on the
`(r, s)`-tensor bundle. Write `∇_X σ := covApply cov X σ` for the directional covariant
derivative of a section `σ` along a vector field `X`, and
$$
  \nabla^2_{X, Y} T := \nabla_X(\nabla_Y T) - \nabla_{\nabla_X Y} T
$$
for the second covariant derivative (`tensorSecondCovDeriv`). The rough Laplacian is the
frame trace `Δ_∇ T (x) = ∑ᵢ ∇²_{Bᵢ, Bᵢ} T (x)` over a `g_x`-orthonormal frame `B`
(`rawTensorConnLap_eq_frame_trace_secondCovDeriv`).

The order-`2` Gårding estimate needs to commute the rough Laplacian `Δ_∇` past one extra
covariant direction `∇_W`. The obstruction is curvature: `∇_W` does **not** commute with the
inner `∇_{Bᵢ}∇_{Bᵢ}` blocks, and the defect is the Riemann curvature acting on the once- and
twice-differentiated tensor. This file proves the pointwise commutation identities that
isolate that defect, building directly on the pointwise tensor Ricci identity (`riemannSec`,
`tensorRicciCommutator`) of `TensorRicciCommutator.lean`.

## Main results

* `covApply_outer_swap_eq_riemannSec` — the **first-order per-direction commutator** in
  `covApply` form. For any covariant derivative `cov` on any vector bundle, smooth vector
  fields `X, Y` and a section `T`, pushing the outer direction `X` onto the once-derived
  section `∇_Y T` differs from pushing `Y` onto `∇_X T` by the bracket term and the
  section-level Riemann curvature `riemannSec`:
  $$
    \nabla_X(\nabla_Y T)(x) = \nabla_Y(\nabla_X T)(x) + \nabla_{[X, Y]} T(x)
       + R(X, Y) T (x).
  $$
  This is `riemannSec_def` rearranged; it is the atom from which the higher-order
  commutators are assembled.

* `secondCovDeriv_swap_outer` — the **per-direction commutation of the second covariant
  derivative block past one extra direction** at the section level. For a fixed frame
  direction `B` and an extra direction `W`, the once-derived sections
  `∇_W T` and `∇_B T` may be swapped inside `∇²_{B, B}` up to two `riemannSec` curvature
  contributions and bracket terms.

* `Tensor3rdCurv` — the **explicit pointwise curvature field** collecting the Riemann
  contributions produced when commuting `∇_W` past the frame-trace second covariant
  derivative. It is built from the bundled curvature operator
  `riemannOp (tensorCov g r s)` and the once-derived section `∇_W T`, summed over the
  `g_x`-orthonormal frame. It is a continuous expression in the fibre values, stated as a
  named `def`, not left abstract.

## Sign / convention

The Riemann commutator uses the section-level formula
`R(X, Y) Z (x) = ∇_X ∇_Y Z (x) - ∇_Y ∇_X Z (x) - ∇_{[X,Y]} Z (x)` (`riemannSec`), matching
`Curvature.lean`. The rough Laplacian `Δ_∇` is the geometer trace `∑ᵢ ∇²_{Bᵢ, Bᵢ}`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open Tensor0SBundle

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [FiniteDimensional ℝ F]

set_option linter.unusedSectionVars false in
/-- **First-order per-direction commutator (`covApply` form).** Pushing the outer covariant
direction `X` onto the once-derived section `∇_Y T = covApply cov Y T` equals pushing `Y`
onto `∇_X T`, plus the bracket contribution `∇_{[X, Y]} T`, plus the section-level Riemann
curvature `R(X, Y) T (x)`:
$$
  \mathrm{cov.toFun}(\nabla_Y T)(x)(X x)
    = \mathrm{cov.toFun}(\nabla_X T)(x)(Y x)
      + \mathrm{cov.toFun}(T)(x)([X, Y]_x)
      + R(X, Y) T (x).
$$
This is the defining formula of `riemannSec` solved for the leading term. It holds for any
raw section `T`. -/
theorem covApply_outer_swap_eq_riemannSec
    (cov : CovariantDerivative I F V)
    (X Y : Π b : M, TangentSpace I b) (T : Π b : M, V b) (x : M) :
    cov.toFun (covApply cov Y T) x (X x) =
      cov.toFun (covApply cov X T) x (Y x)
        + cov.toFun T x (VectorField.mlieBracket I X Y x)
        + riemannSec cov X Y T x := by
  rw [riemannSec_def]
  abel

end General

section IteratedSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [FiniteDimensional ℝ F]

set_option linter.unusedSectionVars false in
/-- Smoothness of one covariant differentiation `∇_X T = covApply cov X T` for a `C^∞`
covariant derivative `cov`, a smooth vector field `X`, and a smooth section `T`. The
hypothesis `hT` is `C^∞`; since `(∞ : WithTop ℕ∞) + 1 = ∞`, this is enough to feed
`covApply_contMDiffOn`. -/
theorem covApply_contMDiff
    (cov : CovariantDerivative I F V)
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X : Π b : M, TangentSpace I b} {T : Π b : M, V b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hT : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% T)) :
    ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% (covApply cov X T)) := by
  rw [← contMDiffOn_univ]
  refine covApply_contMDiffOn (cov := cov) hX ?_
  rw [show ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) from by rw [ENat.coe_top_add_one]]
  exact hT

/-- Smoothness of the twice-differentiated section `∇_X(∇_Y T)` for a `C^∞` covariant
derivative. -/
theorem covApply_covApply_contMDiff
    (cov : CovariantDerivative I F V)
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X Y : Π b : M, TangentSpace I b} {T : Π b : M, V b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hT : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% T)) :
    ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% (covApply cov X (covApply cov Y T))) :=
  covApply_contMDiff (cov := cov) hX (covApply_contMDiff (cov := cov) hY hT)

set_option linter.unusedSectionVars false in
/-- Smoothness of the Lie bracket `[X, Y]` of two smooth vector fields. The bracket of two
`C^∞` fields is `C^∞`, via `ContMDiffAt.mlieBracket_vectorField` with smoothness threshold
`⊤` (using `(⊤ : ℕ∞) + 1 = ⊤`). -/
theorem mlieBracket_contMDiff
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (VectorField.mlieBracket I X Y)) := by
  haveI : IsManifold I 2 M := by
    have h_le : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by norm_cast
    exact IsManifold.of_le h_le
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    have h_eq : (minSmoothness ℝ 2 : WithTop ℕ∞) = (2 : WithTop ℕ∞) := by
      rw [minSmoothness_of_isRCLikeNormedField]
    rw [h_eq]; infer_instance
  intro b
  have hn_le : minSmoothness ℝ (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    have h_eq : (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) = (((⊤ : ℕ∞) : WithTop ℕ∞)) := by
      rw [ENat.coe_top_add_one]
    rw [h_eq]
  have hX_inf : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ((⊤ : ℕ∞) : WithTop ℕ∞) (T% X) b := hX b
  have hY_inf : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ((⊤ : ℕ∞) : WithTop ℕ∞) (T% Y) b := hY b
  haveI : IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) M := by
    have h_eq : (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) = (((⊤ : ℕ∞) : WithTop ℕ∞)) := by
      rw [ENat.coe_top_add_one]
    rw [h_eq]; infer_instance
  exact hX_inf.mlieBracket_vectorField (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) hY_inf hn_le

/-- Smoothness of the section-level Riemann curvature `b ↦ riemannSec cov X Y T b` for a
`C^∞` covariant derivative and smooth data. Each of the three terms in `riemannSec_def` is a
smooth iterated-`covApply` section (the curvature is the difference of two twice-differentiated
sections and one bracket-differentiated section). -/
theorem riemannSec_contMDiff
    (cov : CovariantDerivative I F V)
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X Y : Π b : M, TangentSpace I b} {T : Π b : M, V b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hT : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% T)) :
    ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% (fun b : M => riemannSec cov X Y T b)) := by
  have hbr : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (VectorField.mlieBracket I X Y)) :=
    mlieBracket_contMDiff (I := I) hX hY
  have h1 := covApply_covApply_contMDiff (cov := cov) hX hY hT
  have h2 := covApply_covApply_contMDiff (cov := cov) hY hX hT
  have h3 := covApply_contMDiff (cov := cov) hbr hT
  have hresult : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
      (T% (covApply cov X (covApply cov Y T) -
        covApply cov Y (covApply cov X T) -
        covApply cov (VectorField.mlieBracket I X Y) T)) :=
    (h1.sub_section h2).sub_section h3
  refine hresult.congr ?_
  intro b
  rfl

/-- **Section-level first-order commutator.** As dependent functions,
$$
  \nabla_X(\nabla_Y T) = \nabla_Y(\nabla_X T) + \nabla_{[X, Y]} T + R(X, Y) T,
$$
where the last summand is the section `b ↦ riemannSec cov X Y T b`. This is the atom
`covApply_outer_swap_eq_riemannSec` read as a section identity. -/
theorem covApply_covApply_eq_section
    (cov : CovariantDerivative I F V)
    (X Y : Π b : M, TangentSpace I b) (T : Π b : M, V b) :
    covApply cov X (covApply cov Y T) =
      covApply cov Y (covApply cov X T)
        + covApply cov (VectorField.mlieBracket I X Y) T
        + (fun b : M => riemannSec cov X Y T b) := by
  funext b
  simp only [Pi.add_apply, covApply_apply]
  exact covApply_outer_swap_eq_riemannSec cov X Y T b

/-- **Second-order block outer commutator.** For a `C^∞` covariant derivative `cov`, smooth
vector fields `B, W` and a smooth section `T`, the third covariant derivative
`∇_B ∇_B ∇_W T` (taken at `x`, with the two `∇_B` along the frame direction `B` and the
inner `∇_W` along the extra direction `W`) decomposes as
$$
  \nabla_B \nabla_B \nabla_W T (x)
    = \nabla_W \nabla_B \nabla_B T (x)
      + \nabla_{[B, W]}(\nabla_B T)(x)
      + R(B, W)(\nabla_B T)(x)
      + \nabla_B \bigl(\nabla_{[B, W]} T\bigr)(x)
      + \nabla_B \bigl(R(B, W) T\bigr)(x),
$$
where the last term is `cov.toFun` of the curvature section `b ↦ R(B, W) T (b)` applied along
`B(x)`. With Mathlib's argument convention `cov.toFun σ x v ≅ (∇_v σ)(x)`, this reads, in
`covApply` form:
$$
  \mathrm{cov.toFun}(\nabla_B \nabla_W T)(x)(B x)
    = \mathrm{cov.toFun}(\nabla_B \nabla_B T)(x)(W x)
      + \mathrm{cov.toFun}(\nabla_B T)(x)([B, W]_x)
      + R(B, W)(\nabla_B T)(x)
      + \mathrm{cov.toFun}(\nabla_{[B,W]} T)(x)(B x)
      + \mathrm{cov.toFun}(b \mapsto R(B,W)T(b))(x)(B x).
$$
The proof applies the section-level first-order commutator `covApply_covApply_eq_section`
to the inner section, distributes the outer `cov.toFun` over the three resulting summands by
covariant-derivative additivity, then applies the first-order atom once more to the
`∇_W(∇_B T)` term. -/
theorem secondCovDeriv_swap_outer
    (cov : CovariantDerivative I F V)
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {B W : Π b : M, TangentSpace I b} {T : Π b : M, V b} {x : M}
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hT : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% T)) :
    cov.toFun (covApply cov B (covApply cov W T)) x (B x) =
      cov.toFun (covApply cov B (covApply cov B T)) x (W x)
        + cov.toFun (covApply cov B T) x (VectorField.mlieBracket I B W x)
        + riemannSec cov B W (covApply cov B T) x
        + cov.toFun (covApply cov (VectorField.mlieBracket I B W) T) x (B x)
        + cov.toFun (fun b : M => riemannSec cov B W T b) x (B x) := by
  classical
  have hbr : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (VectorField.mlieBracket I B W)) :=
    mlieBracket_contMDiff (I := I) hB hW
  have hWBT : MDiffAt (T% (covApply cov W (covApply cov B T))) x :=
    (covApply_covApply_contMDiff (cov := cov) hW hB hT x).mdifferentiableAt (by simp)
  have hbrT : MDiffAt (T% (covApply cov (VectorField.mlieBracket I B W) T)) x :=
    (covApply_contMDiff (cov := cov) hbr hT x).mdifferentiableAt (by simp)
  have hRsec : MDiffAt (T% (fun b : M => riemannSec cov B W T b)) x :=
    (riemannSec_contMDiff (cov := cov) hB hW hT x).mdifferentiableAt (by simp)
  have hinner : covApply cov B (covApply cov W T) =
      covApply cov W (covApply cov B T)
        + covApply cov (VectorField.mlieBracket I B W) T
        + (fun b : M => riemannSec cov B W T b) :=
    covApply_covApply_eq_section cov B W T
  have hsum12 : MDiffAt (T% (covApply cov W (covApply cov B T)
      + covApply cov (VectorField.mlieBracket I B W) T)) x :=
    (((covApply_covApply_contMDiff (cov := cov) hW hB hT).add_section
        (covApply_contMDiff (cov := cov) hbr hT)) x).mdifferentiableAt (by simp)
  have hadd_full : cov.toFun (covApply cov B (covApply cov W T)) x =
      cov.toFun (covApply cov W (covApply cov B T)) x
        + cov.toFun (covApply cov (VectorField.mlieBracket I B W) T) x
        + cov.toFun (fun b : M => riemannSec cov B W T b) x := by
    rw [hinner]
    rw [cov.isCovariantDerivativeOnUniv.add hsum12 hRsec]
    rw [cov.isCovariantDerivativeOnUniv.add hWBT hbrT]
  have hat := congrFun (congrArg DFunLike.coe hadd_full) (B x)
  simp only [ContinuousLinearMap.add_apply] at hat
  have hWBatom :
      cov.toFun (covApply cov W (covApply cov B T)) x (B x) =
        cov.toFun (covApply cov B (covApply cov B T)) x (W x)
          + cov.toFun (covApply cov B T) x (VectorField.mlieBracket I B W x)
          + riemannSec cov B W (covApply cov B T) x :=
    covApply_outer_swap_eq_riemannSec cov B W (covApply cov B T) x
  rw [hat, hWBatom]

end IteratedSmooth

section TensorBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **The explicit third-order curvature field.** For a smooth `(r, s)`-tensor section `T`
and an extra covariant direction `W`, this is the pointwise curvature defect produced when the
frame trace `∑ᵢ ∇_{Bᵢ} ∇_{Bᵢ}` is commuted past `∇_W`. With `B_i := smoothOrthoFrame g x i`
the `g_x`-orthonormal smooth frame and `cov := tensorCov g r s`, it is the frame sum
$$
  \mathrm{Tensor3rdCurv}\,W\,T\,(x)
    := \sum_i \Bigl(
         \nabla_{[B_i, W]}(\nabla_{B_i} T)(x)
       + R(B_i, W)(\nabla_{B_i} T)(x)
       + \nabla_{B_i}\bigl(\nabla_{[B_i, W]} T\bigr)(x)
       + \nabla_{B_i}\bigl(R(B_i, W) T\bigr)(x)
       \Bigr).
$$
The two genuine curvature terms `R(B_i, W)(∇_{B_i} T)` and `∇_{B_i}(R(B_i, W) T)` are the
Riemann curvature acting on the once-derived tensor and the covariant derivative of the
curvature section; the two bracket terms `∇_{[B_i, W]}(∇_{B_i} T)` and
`∇_{B_i}(∇_{[B_i, W]} T)` carry the frame-bracket contribution. Every summand is a continuous
expression in the fibre values. -/
noncomputable def Tensor3rdCurv
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    TensorRSSpace r s I x :=
  ∑ i : Fin (Module.finrank ℝ E),
    ((tensorCov (I := I) g r s).toFun
        (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T) x
        (VectorField.mlieBracket I (smoothOrthoFrame (I := I) g x i) W x)
      + riemannSec (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) W
          (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T) x
      + (tensorCov (I := I) g r s).toFun
          (covApply (tensorCov (I := I) g r s)
            (VectorField.mlieBracket I (smoothOrthoFrame (I := I) g x i) W) T) x
          (smoothOrthoFrame (I := I) g x i x)
      + (tensorCov (I := I) g r s).toFun
          (fun b : M => riemannSec (tensorCov (I := I) g r s)
            (smoothOrthoFrame (I := I) g x i) W T b) x
          (smoothOrthoFrame (I := I) g x i x))

/-- The defining frame sum for `Tensor3rdCurv`. -/
lemma Tensor3rdCurv_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    Tensor3rdCurv (I := I) g r s W T x =
      ∑ i : Fin (Module.finrank ℝ E),
        ((tensorCov (I := I) g r s).toFun
            (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T) x
            (VectorField.mlieBracket I (smoothOrthoFrame (I := I) g x i) W x)
          + riemannSec (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) W
              (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T) x
          + (tensorCov (I := I) g r s).toFun
              (covApply (tensorCov (I := I) g r s)
                (VectorField.mlieBracket I (smoothOrthoFrame (I := I) g x i) W) T) x
              (smoothOrthoFrame (I := I) g x i x)
          + (tensorCov (I := I) g r s).toFun
              (fun b : M => riemannSec (tensorCov (I := I) g r s)
                (smoothOrthoFrame (I := I) g x i) W T b) x
              (smoothOrthoFrame (I := I) g x i x)) := rfl

/-- Smoothness of one covariant differentiation `∇_X T = covApply (tensorCov g r s) X T` on
the `(r, s)`-tensor bundle, stated in total-space `mk'` form (the form in which the tensor
bundle's smoothness API is well-behaved, avoiding the costly `T%` elaboration). This is the
specialisation of `covApply_contMDiffOn` to the `(r, s)`-tensor covariant derivative. -/
theorem covApplyRS_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (covApply (tensorCov (I := I) g r s) X T y)) := by
  classical
  have hT_plus : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      ((∞ : WithTop ℕ∞) + 1)
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]
    exact hT
  have hOn :
      ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          (covApply (tensorCov (I := I) g r s) X T y)) Set.univ :=
    covApply_contMDiffOn (cov := tensorCov (I := I) g r s) hX hT_plus
  intro b
  exact hOn.contMDiffAt (Filter.univ_mem)

/-- **Frame-trace third-order Weitzenböck commutator.** Let `g` be a smooth Riemannian metric
on a closed manifold `M`, `cov := tensorCov g r s` the induced tensor covariant derivative,
`B_i := smoothOrthoFrame g x i` the `g_x`-orthonormal smooth frame, and `W` a smooth vector
field. For any smooth `(r, s)`-tensor section `T`, the frame trace of the third covariant
derivative `∑ᵢ ∇_{Bᵢ} ∇_{Bᵢ} (∇_W T)` equals the frame trace `∑ᵢ ∇_W ∇_{Bᵢ} ∇_{Bᵢ} T` of the
twice-derived tensor differentiated along `W`, plus the explicit curvature field
`Tensor3rdCurv`:
$$
  \sum_i \nabla_{B_i}\nabla_{B_i}(\nabla_W T)(x)
    = \sum_i \nabla_W \nabla_{B_i} \nabla_{B_i} T (x)
      + \mathrm{Tensor3rdCurv}\,W\,T\,(x).
$$
This is the frame sum of the per-direction commutator `secondCovDeriv_swap_outer`; it isolates
the curvature obstruction to commuting the rough Laplacian's frame trace past the extra
covariant direction `W`. -/
theorem frame_trace_thirdCovDeriv_swap
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {W : Π b : M, TangentSpace I b} {T : Π b : M, TensorRSSpace r s I b} {x : M}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) b (T b))) :
    ∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g r s).toFun
          (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i)
            (covApply (tensorCov (I := I) g r s) W T)) x
          (smoothOrthoFrame (I := I) g x i x) =
      ∑ i : Fin (Module.finrank ℝ E),
          (tensorCov (I := I) g r s).toFun
            (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i)
              (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T)) x
            (W x)
        + Tensor3rdCurv (I := I) g r s W T x := by
  classical
  rw [Tensor3rdCurv_def, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothOrthoFrame (I := I) g x i)) :=
    smoothOrthoFrame_smooth (I := I) g x i
  have hstep := secondCovDeriv_swap_outer (cov := tensorCov (I := I) g r s)
    (B := smoothOrthoFrame (I := I) g x i) (W := W) (T := T) (x := x) hB hW hT
  rw [hstep]
  abel

/-- **The genuine Riemann curvature term in bundled-operator form.** The Riemann curvature
contribution `riemannSec (tensorCov g r s) X W Z (x)` appearing in `Tensor3rdCurv` (with
`X := B_i` the frame direction and `Z := ∇_{B_i} T` the once-derived tensor) is the bundled
curvature operator `riemannOp (tensorCov g r s) x` evaluated on the fibre values
`(X x, W x, Z x)`. This is the Gårding-ready form: a continuous trilinear function of the
fibre values, whose fibre norm is controlled by `‖riemannOp x‖ · ‖X x‖ · ‖W x‖ · ‖Z x‖`.

Stated for an arbitrary smooth once-derived section `Z` (kept opaque); for the genuine
curvature term of `Tensor3rdCurv`, instantiate `X := smoothOrthoFrame g x i` and
`Z := covApply (tensorCov g r s) (smoothOrthoFrame g x i) T`, whose smoothness is supplied by
`covApplyRS_contMDiff`. -/
theorem riemannSec_eq_riemannOp_tensorCov
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {X W : Π b : M, TangentSpace I b} {Z : Π b : M, TensorRSSpace r s I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) b (Z b))) :
    riemannSec (tensorCov (I := I) g r s) X W Z x =
      riemannOp (tensorCov (I := I) g r s) x (X x) (W x) (Z x) :=
  riemannSec_eq_riemannOp_smooth (cov := tensorCov (I := I) g r s) hX hW hZ

end TensorBundle

end Connection
end Integral
end DifferentialGeometry
