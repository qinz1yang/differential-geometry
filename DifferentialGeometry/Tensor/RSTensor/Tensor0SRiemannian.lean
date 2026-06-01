import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.RSTensor.TangentRiemannian
import DifferentialGeometry.Integral.L2.PointwiseInner.Defs
import DifferentialGeometry.Integral.L2.PointwiseInner.Algebra
import DifferentialGeometry.Integral.L2.PointwiseInner.DualMetric
import DifferentialGeometry.Integral.Measure.ChartDensity
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smooth Riemannian metric on the (0,s)-tensor bundle

Given a smooth Riemannian metric `g` on a manifold `M` (encoded as a
`SmoothRiemannianMetric I M`, i.e. a
`Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I)`), and an inner-product
structure on the model fibre `E`, we equip the (0,s)-tensor bundle with a
`Bundle.ContMDiffRiemannianMetric I ∞ (Tensor0SModel s ℝ E) (Tensor0SSpace s I)`
whose pointwise inner product agrees with `tensorInnerPointwise_0s s g b`.

After installing the resulting Riemannian-bundle structure on the (0,s)-tensor
bundle, Mathlib's automatic instance machinery yields
`IsContMDiffRiemannianBundle` (and `IsContinuousRiemannianBundle`) on the
(0,s)-tensor bundle.

The diamond between the project's project-level normed structure on
`Tensor0SSpace s I b` and Mathlib's scoped priority-80 normed structure coming
from `RiemannianBundle` is handled in the same way as in
`TangentRiemannian.lean`: a private auxiliary lemma locally removes the
project's preferred instances, installs the `RiemannianBundle` structure built
from the metric we construct here, and exposes only scalar-valued conclusions
from inside the diamond-handling scope.
-/

noncomputable section

open Bundle Set IsManifold ContinuousLinearMap Bornology
open scoped Manifold Topology Bundle ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Tensor
namespace Tensor0SRiemannian

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- File-local instance: install the strong topology on `Tensor0SSpace s I b →L[ℝ] ℝ`.
The standard `ContinuousLinearMap.topologicalSpace` instance is not picked up
automatically through Lean's typeclass synthesis on the bundle topology of
`Tensor0SSpace s I b`; we register it explicitly here at file scope. -/
private instance bundleDualTopologicalSpace (s : ℕ) (b : M) :
    TopologicalSpace (Tensor0SSpace s I b →L[ℝ] ℝ) :=
  ContinuousLinearMap.topologicalSpace
    (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
    (E := Tensor0SSpace s I b) (F := ℝ)

/-! ## The pointwise (0,s) inner product on the model fibre as a CLM

The pointwise inner product `tensorInnerPointwise_0s` is defined on the model
fibres `Tensor0SModel s ℝ E = Tensor0SModel s ℝ E`.
It is bilinear (proved in `PointwiseInner.Algebra`) and the model fibre is a
finite-dimensional normed space, so the bilinear map is automatically a
continuous bilinear map. We package it as a `→L[ℝ] · →L[ℝ] ·` CLM. -/

/-- Underlying bilinear (`LinearMap`-valued) pairing on the model fibre. -/
private def innerModelBilin
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    Tensor0SModel s ℝ E →ₗ[ℝ] Tensor0SModel s ℝ E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun T S => tensorInnerPointwise_0s (I := I) (M := M) s g b T S)
    (fun T₁ T₂ S =>
      tensorInnerPointwise_0s_add_left (I := I) (M := M) g b s T₁ T₂ S)
    (fun c T S =>
      tensorInnerPointwise_0s_smul_left (I := I) (M := M) g b s c T S)
    (fun T S₁ S₂ =>
      tensorInnerPointwise_0s_add_right (I := I) (M := M) g b s T S₁ S₂)
    (fun c T S =>
      tensorInnerPointwise_0s_smul_right (I := I) (M := M) g b s c T S)

@[simp] private lemma innerModelBilin_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (T S : Tensor0SModel s ℝ E) :
    innerModelBilin (I := I) (M := M) g s b T S =
      tensorInnerPointwise_0s (I := I) (M := M) s g b T S := rfl

/-- The "outer" linear map: for each `T`, the inner-argument `S ↦ inner T S` is
linear and (since the model fibre is finite-dimensional) continuous. We package
this as a CLM. -/
private def innerModelLinearOuter
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    Tensor0SModel s ℝ E →ₗ[ℝ] (Tensor0SModel s ℝ E →L[ℝ] ℝ) where
  toFun := fun T =>
    LinearMap.toContinuousLinearMap
      (innerModelBilin (I := I) (M := M) g s b T)
  map_add' := fun T₁ T₂ => by
    refine ContinuousLinearMap.ext ?_
    intro S
    change tensorInnerPointwise_0s (I := I) (M := M) s g b (T₁ + T₂) S =
      tensorInnerPointwise_0s (I := I) (M := M) s g b T₁ S +
        tensorInnerPointwise_0s (I := I) (M := M) s g b T₂ S
    exact tensorInnerPointwise_0s_add_left (I := I) (M := M) g b s T₁ T₂ S
  map_smul' := fun c T => by
    refine ContinuousLinearMap.ext ?_
    intro S
    change tensorInnerPointwise_0s (I := I) (M := M) s g b (c • T) S =
      c • tensorInnerPointwise_0s (I := I) (M := M) s g b T S
    rw [tensorInnerPointwise_0s_smul_left]
    rfl

/-- The pointwise `(0, s)` inner product as a continuous bilinear pairing on
the model fibre. -/
def innerModelCLM
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    Tensor0SModel s ℝ E →L[ℝ] Tensor0SModel s ℝ E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (innerModelLinearOuter (I := I) (M := M) g s b)

@[simp] lemma innerModelCLM_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (T S : Tensor0SModel s ℝ E) :
    innerModelCLM (I := I) (M := M) g s b T S =
      tensorInnerPointwise_0s (I := I) (M := M) s g b T S := rfl

/-! ## Transferring the inner CLM to the bundle fibre

The bundle fibre `Tensor0SSpace s I b` shares the same underlying type as the
model fibre, but with the bundle topology. We have a CLE
`tensor0SSpace_continuousLinearEquiv` between them. To define the bundle-level
inner CLM `Tensor0SSpace s I b →L[ℝ] Tensor0SSpace s I b →L[ℝ] ℝ`, we precompose
the model-level CLM `innerModelCLM` with this CLE on each argument. -/

/-- Shorthand for the CLE between the bundle fibre and the model fibre. -/
private def bundleCLE (s : ℕ) (b : M) :
    Tensor0SSpace s I b ≃L[ℝ]
      Tensor0SModel s ℝ E :=
  Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (E := E) (I := I) (M := M) s b

/-- The forward CLM of `bundleCLE`. -/
private def bundleToModelCLM (s : ℕ) (b : M) :
    Tensor0SSpace s I b →L[ℝ]
      Tensor0SModel s ℝ E :=
  (bundleCLE (I := I) (M := M) (E := E) s b).toContinuousLinearMap

@[simp] private lemma bundleToModelCLM_apply (s : ℕ) (b : M)
    (T : Tensor0SSpace s I b) :
    bundleToModelCLM (I := I) (M := M) (E := E) s b T =
      Tensor0SBundle.Tensor0SSpace.toModel
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) T := rfl

/-- The inverse CLM of `bundleCLE`. -/
private def modelToBundleCLM (s : ℕ) (b : M) :
    Tensor0SModel s ℝ E →L[ℝ]
      Tensor0SSpace s I b :=
  (bundleCLE (I := I) (M := M) (E := E) s b).symm.toContinuousLinearMap

/-- The "pre-compose into bundle" CLM, post-composing a model-fibre CLM
`Tensor0SModel s ℝ E →L[ℝ] ℝ` with `bundleToModelCLM`. We define this via
`arrowCongr`, which avoids metric-topology requirements: `arrowCongr` requires
only `IsTopologicalAddGroup` on its codomains, which `ℝ` and the bundle fibre
both satisfy. -/
private def precompBundleCLM (s : ℕ) (b : M) :
    (Tensor0SModel s ℝ E →L[ℝ] ℝ) →L[ℝ]
      (Tensor0SSpace s I b →L[ℝ] ℝ) :=
  -- `(bundleCLE.symm).arrowCongr (refl ℝ ℝ) :
  --     (Tensor0SModel s ℝ E →L[ℝ] ℝ) ≃L[ℝ] (Tensor0SSpace s I b →L[ℝ] ℝ)`.
  ((bundleCLE (I := I) (M := M) (E := E) s b).symm.arrowCongr
    (ContinuousLinearEquiv.refl ℝ ℝ)).toContinuousLinearMap

@[simp] private lemma precompBundleCLM_apply (s : ℕ) (b : M)
    (f : Tensor0SModel s ℝ E →L[ℝ] ℝ) (T : Tensor0SSpace s I b) :
    precompBundleCLM (I := I) (M := M) (E := E) s b f T =
      f (Tensor0SBundle.Tensor0SSpace.toModel
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) T) :=
  rfl

/-- The `(0, s)` pointwise inner product packaged as a continuous bilinear
pairing on the bundle fibre `Tensor0SSpace s I b`.

We construct it by composing the model-fibre CLM with `precompBundleCLM` on
the codomain side (transferring the inner-CLM domain through the CLE) and then
with `bundleToModelCLM` on the source side. -/
def innerBundleCLM
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    Tensor0SSpace s I b →L[ℝ]
      Tensor0SSpace s I b →L[ℝ] ℝ :=
  -- Step A: Post-compose the model-fibre CLM with `precompBundleCLM`.
  -- `precompBundleCLM ∘L innerModelCLM : Tensor0SModel s ℝ E →L[ℝ]
  --   (Tensor0SSpace s I b →L[ℝ] ℝ)`.
  let stepA : Tensor0SModel s ℝ E →L[ℝ] (Tensor0SSpace s I b →L[ℝ] ℝ) :=
    (precompBundleCLM (I := I) (M := M) (E := E) s b).comp
      (innerModelCLM (I := I) (M := M) g s b)
  -- Step B: Pre-compose `stepA` with `bundleToModelCLM` on the first slot.
  stepA.comp (bundleToModelCLM (I := I) (M := M) (E := E) s b)

@[simp] lemma innerBundleCLM_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (T S : Tensor0SSpace s I b) :
    innerBundleCLM (I := I) (M := M) g s b T S =
      tensorInnerPointwise_0s (I := I) (M := M) s g b
        (Tensor0SBundle.Tensor0SSpace.toModel (I := I) (M := M)
          (𝕜 := ℝ) (E := E) (s := s) (x := b) T)
        (Tensor0SBundle.Tensor0SSpace.toModel (I := I) (M := M)
          (𝕜 := ℝ) (E := E) (s := s) (x := b) S) := by
  rfl

/-! ## Algebraic properties

The `symm` and `pos` properties of `innerBundleCLM` follow from the
corresponding properties of `tensorInnerPointwise_0s` together with
linearity of the CLE `bundleCLE`. -/

/-- Symmetry of the bundle inner product: `inner b T S = inner b S T`. -/
lemma innerBundleCLM_symm
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (T S : Tensor0SSpace s I b) :
    innerBundleCLM (I := I) (M := M) g s b T S =
      innerBundleCLM (I := I) (M := M) g s b S T := by
  rw [innerBundleCLM_apply, innerBundleCLM_apply]
  exact tensorInnerPointwise_0s_symm (I := I) (M := M) g b s _ _

/-- Positive-definiteness on the diagonal: `inner b T T > 0` for `T ≠ 0`. -/
lemma innerBundleCLM_pos
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (T : Tensor0SSpace s I b) (hT : T ≠ 0) :
    0 < innerBundleCLM (I := I) (M := M) g s b T T := by
  rw [innerBundleCLM_apply]
  -- `T ≠ 0 ⟹ toModel T ≠ 0` via injectivity of the CLE.
  have hTm :
      Tensor0SBundle.Tensor0SSpace.toModel
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) T ≠ 0 := by
    intro h
    apply hT
    have hinj :=
      Tensor0SBundle.Tensor0SSpace.toModel_injective
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
    have hzero :
        Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
          (0 : Tensor0SSpace s I b) = 0 :=
      Tensor0SBundle.Tensor0SSpace.toModel_zero
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
    exact hinj (h.trans hzero.symm)
  have hnn :
      0 ≤ tensorInnerPointwise_0s (I := I) (M := M) s g b
          (Tensor0SBundle.Tensor0SSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) T)
          (Tensor0SBundle.Tensor0SSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) T) :=
    tensorInnerPointwise_0s_nonneg (I := I) (M := M) g b s _
  rcases lt_or_eq_of_le hnn with hlt | heq
  · exact hlt
  · exfalso
    apply hTm
    exact (tensorInnerPointwise_0s_eq_zero_iff
      (I := I) (M := M) g b s _).mp heq.symm

/-! ## von-Neumann boundedness of the unit ball

The set `{T : Tensor0SSpace s I b | inner b T T < 1}` is von-Neumann bounded.
Since `Tensor0SSpace s I b` is a finite-dimensional normed-like space (its
topology is induced via the trivialization from a finite-dimensional model
fibre), and the inner product is a positive-definite continuous quadratic
form, the unit ball of the metric-induced norm is contained in a multiple of
the standard unit ball, hence is bounded.

We prove this by transferring the unit ball to the model fibre via the CLE
`bundleCLE` and using the equivalence of norms on a finite-dimensional space:
on `Tensor0SModel s ℝ E`, the inner product `tensorInnerPointwise_0s` and the
operator norm both induce equivalent norms (since both are positive-definite
quadratic forms on a finite-dimensional space). -/

-- Helper: a continuous symmetric positive-definite bilinear form on a
-- finite-dim normed space has a sublevel set {v | B(v,v) < 1} that is bounded.
-- We prove this for any abstract such bilinear form, working purely in the
-- model fibre and using the standard `ContinuousMultilinearMap` instances.

/-- A general finite-dim positive-definite bilinear form has a bounded unit ball. -/
lemma posDef_bilin_unit_ball_isBounded
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F]
    (B : F →L[ℝ] F →L[ℝ] ℝ)
    (hPD : ∀ v : F, v ≠ 0 → 0 < B v v)
    (hNN : ∀ v : F, 0 ≤ B v v)
    (hBilin_smul_left : ∀ (c : ℝ) (v w : F), B (c • v) w = c * B v w)
    (hBilin_smul_right : ∀ (c : ℝ) (v w : F), B v (c • w) = c * B v w) :
    Bornology.IsBounded {v : F | B v v < 1} := by
  haveI : ProperSpace F := FiniteDimensional.proper ℝ _
  classical
  set Q : F → ℝ := fun v => B v v with hQ_def
  have hQ_cont : Continuous Q :=
    Continuous.clm_apply B.continuous continuous_id
  have hsphere_compact : IsCompact (Metric.sphere (0 : F) 1) :=
    isCompact_sphere _ _
  have hsphere_nonempty : (Metric.sphere (0 : F) 1).Nonempty := by
    rcases exists_ne (0 : F) with ⟨v₀, hv₀⟩
    refine ⟨‖v₀‖⁻¹ • v₀, ?_⟩
    rw [Metric.mem_sphere, dist_zero_right]
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have hv₀_norm_ne : ‖v₀‖ ≠ 0 := norm_ne_zero_iff.mpr hv₀
    exact inv_mul_cancel₀ hv₀_norm_ne
  obtain ⟨v_min, hv_min_mem, hv_min⟩ :=
    hsphere_compact.exists_isMinOn hsphere_nonempty hQ_cont.continuousOn
  set c := Q v_min with hc_def
  have hv_min_ne : v_min ≠ 0 := by
    intro h
    rw [Metric.mem_sphere, dist_zero_right, h, norm_zero] at hv_min_mem
    exact one_ne_zero hv_min_mem.symm
  have hc_pos : 0 < c := hPD v_min hv_min_ne
  have hQ_lower : ∀ v : F, c * ‖v‖ ^ 2 ≤ Q v := by
    intro v
    by_cases hv_zero : v = 0
    · subst hv_zero
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, mul_zero]
      exact hNN 0
    · have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_zero
      have hv_norm_ne : ‖v‖ ≠ 0 := ne_of_gt hv_norm_pos
      set u := ‖v‖⁻¹ • v with hu_def
      have hu_norm : ‖u‖ = 1 := by
        rw [hu_def, norm_smul]
        rw [norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact inv_mul_cancel₀ hv_norm_ne
      have hu_sphere : u ∈ Metric.sphere (0 : F) 1 := by
        rw [Metric.mem_sphere, dist_zero_right]; exact hu_norm
      have hQu : c ≤ Q u := hv_min hu_sphere
      have hQu_eq : Q u = ‖v‖⁻¹ * ‖v‖⁻¹ * Q v := by
        change B u u = ‖v‖⁻¹ * ‖v‖⁻¹ * B v v
        rw [hu_def, hBilin_smul_left, hBilin_smul_right]
        ring
      rw [hQu_eq] at hQu
      have hT_sq_pos : 0 < ‖v‖ ^ 2 := pow_pos hv_norm_pos 2
      have hineq : c * ‖v‖ ^ 2 ≤ (‖v‖⁻¹ * ‖v‖⁻¹ * Q v) * ‖v‖ ^ 2 := by gcongr
      have hsimp : (‖v‖⁻¹ * ‖v‖⁻¹ * Q v) * ‖v‖ ^ 2 = Q v := by field_simp
      rw [hsimp] at hineq
      exact hineq
  refine (Metric.isBounded_iff_subset_ball 0).mpr ?_
  refine ⟨1 / Real.sqrt c + 1, fun v hv => ?_⟩
  rw [Set.mem_setOf_eq] at hv
  have h1 : c * ‖v‖ ^ 2 < 1 := lt_of_le_of_lt (hQ_lower v) hv
  have h2 : ‖v‖ ^ 2 < c⁻¹ := by
    have hh : ‖v‖ ^ 2 < 1 / c := by rwa [lt_div_iff₀ hc_pos, mul_comm]
    rwa [show (1 : ℝ) / c = c⁻¹ from one_div _] at hh
  have h3 : ‖v‖ < Real.sqrt (c⁻¹) := by
    rw [show ‖v‖ = Real.sqrt (‖v‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_lt_sqrt (by positivity) h2
  have hsqrt_eq : Real.sqrt (c⁻¹) = 1 / Real.sqrt c := by
    rw [Real.sqrt_inv, one_div]
  rw [hsqrt_eq] at h3
  rw [Metric.mem_ball, dist_zero_right]
  linarith

/-! ## Bundle smoothness of the inner-product section

We assemble `innerBundleCLM g s` into a smooth section of the Hom bundle
`Hom(Tensor0S(s), Hom(Tensor0S(s), ℝ))` on `M`. The argument proceeds by
chart-localising and using the fact that the inner product, viewed in
trivialised coordinates, is a polynomial expression in the entries of the
chart-local Gram matrix and its inverse — both of which are smooth. The
chart-local representation of the inner-product section is constructed
by induction on `s` and then transferred to the bundle level.

The chart-local approach: in the trivialisation at `α : M`, the bilinear form
`innerBundleCLM g s b` (acting on bundle-fibre tensors) corresponds to a
bilinear form on the model fibre `Tensor0SModel s ℝ E`. The dependence on
`b ∈ chartAt(α).source` is smooth because the chart-local Gram matrix
`chartGramMatrix g α b` and its determinant inverse are smooth.
-/

open DifferentialGeometry.Integral.Measure (chartGramMatrix
  chartGramMatrix_apply chartGramMatrix_isHermitian
  chartGramMatrix_posDef chartGramMatrix_det_pos
  chartGramMatrix_entry_contMDiffOn chartGramMatrix_det_contMDiffOn
  chartBasisVecFiber chartBasisVec)

variable {n : ℕ}

/-! ### Smoothness of the inverse Gram matrix entries

The chart-local Gram matrix `chartGramMatrix g α b` is symmetric
positive-definite with strictly positive determinant on `chartAt(α).source`,
hence invertible. Its inverse is given by `(det)⁻¹ • adjugate`, both factors
being smooth in `b`. We expose entrywise smoothness, which is what the
inductive step of the bilinear-form smoothness proof needs. -/

/-- The adjugate matrix entries are smooth on the trivialisation base set.
We expand via `adjugate_apply` (giving a determinant of a row-update matrix)
and then via the permutation-sum formula for `det`, after which each
summand is a finite product of either constants (the `Pi.single` entry) or
smooth Gram-matrix entries. -/
private lemma chartGramMatrix_adjugate_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => (chartGramMatrix g α b).adjugate i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  -- `adjugate A i j = det (A.updateRow j (Pi.single i 1))` (Mathlib).
  have hexp :
      (fun b : M => (chartGramMatrix g α b).adjugate i j)
        = (fun b : M =>
            ((chartGramMatrix g α b).updateRow j (Pi.single i 1)).det) := by
    funext b
    rw [Matrix.adjugate_apply]
  rw [hexp]
  -- Expand the determinant via the permutation-sum formula.
  have hexp2 :
      (fun b : M =>
          ((chartGramMatrix g α b).updateRow j (Pi.single i 1)).det)
        = (fun b : M =>
            ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
              (Equiv.Perm.sign σ : ℝ) *
                ∏ k,
                  ((chartGramMatrix g α b).updateRow j (Pi.single i 1))
                    (σ k) k) := by
    funext b
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp2]
  refine contMDiffOn_finset_sum (fun σ _ => ?_)
  refine ContMDiffOn.mul (contMDiffOn_const) ?_
  refine contMDiffOn_finset_prod (fun k _ => ?_)
  -- For each `(σ, k)`, the entry `updateRow A j v (σ k) k = if σ k = j then
  -- v k else A (σ k) k`.
  by_cases hσkj : σ k = j
  · -- Row replaced: entry is `(Pi.single i 1) k`, a constant in `b`.
    have heq :
        (fun b : M =>
            ((chartGramMatrix g α b).updateRow j (Pi.single i 1)) (σ k) k)
          = (fun _ : M => (Pi.single i 1 : Fin (Module.finrank ℝ E) → ℝ) k) := by
      funext b
      rw [hσkj, Matrix.updateRow_self]
    rw [heq]
    exact contMDiffOn_const
  · -- Row not replaced: entry is `A (σ k) k`, smooth in `b`.
    have heq :
        (fun b : M =>
            ((chartGramMatrix g α b).updateRow j (Pi.single i 1)) (σ k) k)
          = (fun b : M => chartGramMatrix g α b (σ k) k) := by
      funext b
      rw [Matrix.updateRow_ne hσkj]
    rw [heq]
    exact chartGramMatrix_entry_contMDiffOn (I := I) g α (σ k) k

/-- The inverse Gram matrix entries are smooth on the trivialisation base
set. The inverse formula is `A⁻¹ = (det A)⁻¹ • adjugate A`, valid because the
determinant is strictly positive (hence nonzero) on the chart base set. -/
lemma chartGramMatrix_inv_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => (chartGramMatrix g α b)⁻¹ i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  -- Expand: `A⁻¹ = (det A)⁻¹ • adjugate A`, hence
  -- `A⁻¹ i j = (det A)⁻¹ * adjugate A i j`.
  have hexp :
      (fun b : M => (chartGramMatrix g α b)⁻¹ i j)
        = (fun b : M => (chartGramMatrix g α b).det⁻¹ *
              (chartGramMatrix g α b).adjugate i j) := by
    funext b
    rw [Matrix.inv_def]
    simp [Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [hexp]
  -- Both factors smooth on the chart base set.
  intro b hb
  have hdet := chartGramMatrix_det_contMDiffOn (I := I) g α b hb
  have hadj := chartGramMatrix_adjugate_entry_contMDiffOn (I := I) g α i j b hb
  have hpos : 0 < (chartGramMatrix g α b).det :=
    chartGramMatrix_det_pos (I := I) g α hb
  have hpos_ne : (chartGramMatrix g α b).det ≠ 0 := ne_of_gt hpos
  have hinv : ContMDiffWithinAt I 𝓘(ℝ) ∞
      (fun b' : M => (chartGramMatrix g α b').det⁻¹)
      (trivializationAt E (TangentSpace I) α).baseSet b :=
    ContMDiffWithinAt.inv₀ hdet hpos_ne
  exact hinv.mul hadj

/-! ### From `chartGramMatrix` to a chart-local replacement for the inner
product

The pointwise inner product `tensorInnerPointwise_0s s g b S T` is defined
via the canonical-basis Gram matrix `gramMatrixAt g b`, whose smoothness in
`b` is not immediately accessible through Mathlib's standard tools (the
canonical model-fibre basis vectors do not yield smooth tangent-bundle
sections in general). To bypass this we replace `gramMatrixAt g b` by the
chart-local Gram matrix `chartGramMatrix g α b`, whose entries are smooth on
`chartAt(α).source`. The two are related by the change-of-basis matrix
coming from the trivialisation, and we will see below that the resulting
chart-local inner product, after suitable change-of-coordinates, equals the
bundle-trivialised form of `innerBundleCLM g s b`. -/

/-- A chart-local replacement for `tensorInnerPointwise_0s`, defined using
`chartGramMatrix g α b` in place of `gramMatrixAt g b`. -/
noncomputable def chartTensorInnerPointwise_0s :
    (s : ℕ) → SmoothRiemannianMetric I M → (α : M) → (b : M) →
      Tensor0SModel s ℝ E →
      Tensor0SModel s ℝ E → ℝ
  | 0, _g, _α, _b, S, T =>
      S (fun i => Fin.elim0 i) * T (fun i => Fin.elim0 i)
  | s + 1, g, α, b, S, T =>
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (chartGramMatrix g α b)⁻¹ i j *
          chartTensorInnerPointwise_0s s g α b
            (S.curryLeft ((chartModelBasis E) i))
            (T.curryLeft ((chartModelBasis E) j))

lemma chartTensorInnerPointwise_0s_zero
    (g : SmoothRiemannianMetric I M) (α b : M)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) :
    chartTensorInnerPointwise_0s (I := I) (M := M) 0 g α b S T =
      S (fun i => Fin.elim0 i) * T (fun i => Fin.elim0 i) := rfl

lemma chartTensorInnerPointwise_0s_succ
    (g : SmoothRiemannianMetric I M) (α b : M) (s : ℕ)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ) :
    chartTensorInnerPointwise_0s (I := I) (M := M) (s + 1) g α b S T =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (chartGramMatrix g α b)⁻¹ i j *
          chartTensorInnerPointwise_0s (I := I) (M := M) s g α b
            (S.curryLeft ((chartModelBasis E) i))
            (T.curryLeft ((chartModelBasis E) j)) := rfl

/-! ### Smoothness of the chart-local inner product

The chart-local inner product is smooth in `b` on the chart base set. The
proof is by induction on `s`. The base case is constant; the inductive step
uses smoothness of the inverse Gram matrix and the inductive hypothesis. -/

lemma chartTensorInnerPointwise_0s_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ (s : ℕ) (S T : Tensor0SModel s ℝ E),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M =>
          chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S T)
        (trivializationAt E (TangentSpace I) α).baseSet := by
  intro s
  induction s with
  | zero =>
      intro S T
      -- The arity-zero inner product is the constant `S(Fin.elim0) * T(Fin.elim0)`.
      have heq :
          (fun b : M =>
              chartTensorInnerPointwise_0s (I := I) (M := M) 0 g α b S T)
            = fun _ : M =>
              S (fun i => Fin.elim0 i) * T (fun i => Fin.elim0 i) := by
        funext b
        rw [chartTensorInnerPointwise_0s_zero]
      rw [heq]
      exact contMDiffOn_const
  | succ s ih =>
      intro S T
      have heq :
          (fun b : M =>
              chartTensorInnerPointwise_0s (I := I) (M := M) (s + 1) g α b S T)
            = fun b : M =>
              ∑ i : Fin (Module.finrank ℝ E),
                ∑ j : Fin (Module.finrank ℝ E),
                  (chartGramMatrix g α b)⁻¹ i j *
                    chartTensorInnerPointwise_0s (I := I) (M := M) s g α b
                      (S.curryLeft ((chartModelBasis E) i))
                      (T.curryLeft ((chartModelBasis E) j)) := by
        funext b
        rw [chartTensorInnerPointwise_0s_succ]
      rw [heq]
      refine contMDiffOn_finset_sum (fun i _ => ?_)
      refine contMDiffOn_finset_sum (fun j _ => ?_)
      refine ContMDiffOn.mul ?_ ?_
      · exact chartGramMatrix_inv_entry_contMDiffOn (I := I) g α i j
      · exact ih
          (S.curryLeft ((chartModelBasis E) i))
          (T.curryLeft ((chartModelBasis E) j))

/-! ### Bilinearity of `chartTensorInnerPointwise_0s`

The chart-local inner product is bilinear in the two tensor arguments. We
prove the four bilinearity properties by induction on `s` (mirroring the
proofs of `tensorInnerPointwise_0s_*` in the project's `PointwiseInner`
files). -/

lemma chartTensorInnerPointwise_0s_add_left
    (g : SmoothRiemannianMetric I M) (α b : M) (s : ℕ)
    (S₁ S₂ T : Tensor0SModel s ℝ E) :
    chartTensorInnerPointwise_0s (I := I) (M := M) s g α b (S₁ + S₂) T =
      chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S₁ T +
        chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S₂ T := by
  induction s with
  | zero =>
      change (S₁ + S₂) _ * T _ = S₁ _ * T _ + S₂ _ * T _
      rw [ContinuousMultilinearMap.add_apply]; ring
  | succ s ih =>
      rw [chartTensorInnerPointwise_0s_succ,
          chartTensorInnerPointwise_0s_succ,
          chartTensorInnerPointwise_0s_succ]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      have hcurry :
          (S₁ + S₂).curryLeft ((chartModelBasis E) i) =
            S₁.curryLeft ((chartModelBasis E) i) +
              S₂.curryLeft ((chartModelBasis E) i) := by
        ext m
        simp [ContinuousMultilinearMap.curryLeft_apply,
              ContinuousMultilinearMap.add_apply]
      rw [hcurry, ih]
      ring

lemma chartTensorInnerPointwise_0s_smul_left
    (g : SmoothRiemannianMetric I M) (α b : M) (s : ℕ)
    (c : ℝ) (S T : Tensor0SModel s ℝ E) :
    chartTensorInnerPointwise_0s (I := I) (M := M) s g α b (c • S) T =
      c * chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S T := by
  induction s with
  | zero =>
      change (c • S) _ * T _ = c * (S _ * T _)
      rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul]; ring
  | succ s ih =>
      rw [chartTensorInnerPointwise_0s_succ,
          chartTensorInnerPointwise_0s_succ,
          Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      have hcurry :
          (c • S).curryLeft ((chartModelBasis E) i) =
            c • S.curryLeft ((chartModelBasis E) i) := by
        ext m
        simp [ContinuousMultilinearMap.curryLeft_apply,
              ContinuousMultilinearMap.smul_apply]
      rw [hcurry, ih]
      ring

lemma chartTensorInnerPointwise_0s_add_right
    (g : SmoothRiemannianMetric I M) (α b : M) (s : ℕ)
    (S T₁ T₂ : Tensor0SModel s ℝ E) :
    chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S (T₁ + T₂) =
      chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S T₁ +
        chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S T₂ := by
  induction s with
  | zero =>
      change S _ * (T₁ + T₂) _ = S _ * T₁ _ + S _ * T₂ _
      rw [ContinuousMultilinearMap.add_apply]; ring
  | succ s ih =>
      rw [chartTensorInnerPointwise_0s_succ,
          chartTensorInnerPointwise_0s_succ,
          chartTensorInnerPointwise_0s_succ]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      have hcurry :
          (T₁ + T₂).curryLeft ((chartModelBasis E) j) =
            T₁.curryLeft ((chartModelBasis E) j) +
              T₂.curryLeft ((chartModelBasis E) j) := by
        ext m
        simp [ContinuousMultilinearMap.curryLeft_apply,
              ContinuousMultilinearMap.add_apply]
      rw [hcurry, ih]
      ring

lemma chartTensorInnerPointwise_0s_smul_right
    (g : SmoothRiemannianMetric I M) (α b : M) (s : ℕ)
    (c : ℝ) (S T : Tensor0SModel s ℝ E) :
    chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S (c • T) =
      c * chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S T := by
  induction s with
  | zero =>
      change S _ * (c • T) _ = c * (S _ * T _)
      rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul]; ring
  | succ s ih =>
      rw [chartTensorInnerPointwise_0s_succ,
          chartTensorInnerPointwise_0s_succ,
          Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      have hcurry :
          (c • T).curryLeft ((chartModelBasis E) j) =
            c • T.curryLeft ((chartModelBasis E) j) := by
        ext m
        simp [ContinuousMultilinearMap.curryLeft_apply,
              ContinuousMultilinearMap.smul_apply]
      rw [hcurry, ih]
      ring

/-! ### CLM-valued chart-local inner product

We package the chart-local inner product as a `MLF →L MLF →L ℝ`-valued
function of `b`, and prove it is smooth as a map into the fixed normed
space `MLF →L MLF →L ℝ`. This is the form needed by the
trivialisation-section iff lemma. -/

/-- The bilinear `LinearMap` underlying `chartTensorInnerPointwise_0s`. -/
def chartTensorInnerPointwise_0sBilin
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α b : M) :
    Tensor0SModel s ℝ E →ₗ[ℝ]
      Tensor0SModel s ℝ E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun S T => chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S T)
    (fun S₁ S₂ T =>
      chartTensorInnerPointwise_0s_add_left (I := I) (M := M) g α b s S₁ S₂ T)
    (fun c S T =>
      chartTensorInnerPointwise_0s_smul_left (I := I) (M := M) g α b s c S T)
    (fun S T₁ T₂ =>
      chartTensorInnerPointwise_0s_add_right (I := I) (M := M) g α b s S T₁ T₂)
    (fun c S T =>
      chartTensorInnerPointwise_0s_smul_right (I := I) (M := M) g α b s c S T)

@[simp] lemma chartTensorInnerPointwise_0sBilin_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α b : M)
    (S T : Tensor0SModel s ℝ E) :
    chartTensorInnerPointwise_0sBilin (I := I) (M := M) g s α b S T =
      chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S T := rfl

/-- CLM-valued chart-local inner product as a continuous bilinear pairing
on the model fibre, indexed by `b : M`. We use that the model fibre is
finite-dimensional, so any bilinear LinearMap is automatically continuous. -/
noncomputable def chartTensorInnerPointwise_0sCLM
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α b : M) :
    Tensor0SModel s ℝ E →L[ℝ]
      Tensor0SModel s ℝ E →L[ℝ] ℝ :=
  let bilin := chartTensorInnerPointwise_0sBilin (I := I) (M := M) g s α b
  LinearMap.toContinuousLinearMap
    { toFun := fun S => LinearMap.toContinuousLinearMap (bilin S)
      map_add' := fun S₁ S₂ => by
        refine ContinuousLinearMap.ext ?_
        intro T
        change chartTensorInnerPointwise_0s (I := I) (M := M) s g α b (S₁ + S₂) T =
          chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S₁ T +
            chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S₂ T
        exact chartTensorInnerPointwise_0s_add_left
          (I := I) (M := M) g α b s S₁ S₂ T
      map_smul' := fun c S => by
        refine ContinuousLinearMap.ext ?_
        intro T
        change chartTensorInnerPointwise_0s (I := I) (M := M) s g α b (c • S) T =
          c • chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S T
        rw [chartTensorInnerPointwise_0s_smul_left]
        rfl }

@[simp] lemma chartTensorInnerPointwise_0sCLM_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α b : M)
    (S T : Tensor0SModel s ℝ E) :
    chartTensorInnerPointwise_0sCLM (I := I) (M := M) g s α b S T =
      chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S T := rfl

/-! ### Explicit recursion structure for the CLM-valued chart-local inner
product

We rewrite `chartTensorInnerPointwise_0sCLM g (s+1) α b` as an explicit
finite-sum of `((chartGramMatrix g α b)⁻¹ i j) • (constant CLM ∘ s-step CLM)`,
where the constant CLM is the "compose with `curryLeft eᵢ`" map, used to
slot the inductive `s`-step into the recursive formula. This factorisation is
what enables the smoothness induction. -/

/-- The `S ↦ S.curryLeft v` map as a CLM `MLF (s+1) →L MLF s`. We bound the
norm directly using the CMLM operator-norm formula: for any tuple
`m : Fin s → E`, `(S.curryLeft v) m = S (cons v m)` and
`‖S (cons v m)‖ ≤ ‖S‖ * ‖v‖ * ∏ ‖m i‖` by `S.norm_map_cons_le`. -/
private noncomputable def curryLeftAtCLM (s : ℕ) (v : E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ →L[ℝ]
      Tensor0SModel s ℝ E :=
  LinearMap.mkContinuous
    { toFun := fun S => S.curryLeft v
      map_add' := fun S₁ S₂ => by
        ext m
        simp [ContinuousMultilinearMap.curryLeft_apply,
              ContinuousMultilinearMap.add_apply]
      map_smul' := fun c S => by
        ext m
        simp [ContinuousMultilinearMap.curryLeft_apply,
              ContinuousMultilinearMap.smul_apply] }
    ‖v‖
    (fun S => by
      change ‖S.curryLeft v‖ ≤ _
      -- `S.curryLeft v : MLF s` has operator norm bounded by `‖S‖ * ‖v‖`.
      -- Use `ContinuousMultilinearMap.opNorm_le_bound`: norm bound from a
      -- pointwise inequality on tuples.
      refine (ContinuousMultilinearMap.opNorm_le_bound
        (M := ‖S‖ * ‖v‖) ?_ ?_).trans (by ring_nf; rfl)
      · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
      · intro m
        rw [ContinuousMultilinearMap.curryLeft_apply]
        have := S.norm_map_cons_le v m
        calc ‖S (Fin.cons v m)‖
            ≤ ‖S‖ * ‖v‖ * ∏ i, ‖m i‖ := this
          _ = ‖S‖ * ‖v‖ * ∏ i, ‖m i‖ := rfl)

private lemma curryLeftAtCLM_apply (s : ℕ) (v : E)
    (S : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ) :
    curryLeftAtCLM (E := E) s v S = S.curryLeft v := rfl

/-- Pre-composition of a CLM `MLF s →L MLF s →L ℝ` with `curryLeftAtCLM s eᵢ`
on the source side, and `curryLeftAtCLM s eⱼ` on the second argument. This
gives a CLM `MLF (s+1) →L MLF (s+1) →L ℝ`.

The construction: `composeCurryAtIJ B S T = B (S.curryLeft eᵢ) (T.curryLeft eⱼ)`.
We use `compL.flip CLj` (post-compose with `CLj`) on the inner CLM, and
`B.comp CLi` (pre-compose with `CLi`) on the outer. -/
private noncomputable def composeCurryAtIJ (s : ℕ)
    (i j : Fin (Module.finrank ℝ E))
    (B : Tensor0SModel s ℝ E →L[ℝ]
      Tensor0SModel s ℝ E →L[ℝ] ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ →L[ℝ] ℝ :=
  let CLi := curryLeftAtCLM (E := E) s ((chartModelBasis E) i)
  let CLj := curryLeftAtCLM (E := E) s ((chartModelBasis E) j)
  -- For fixed `g` (here `CLj`), `f ↦ f.comp g` is a CLM `(F →L G) →L (E →L G)`.
  -- This is `(compL).flip g`.
  let postCompCLj :
      (Tensor0SModel s ℝ E →L[ℝ] ℝ) →L[ℝ]
        (ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ
      (ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ)
      (Tensor0SModel s ℝ E) ℝ).flip CLj
  postCompCLj.comp (B.comp CLi)

@[simp] private lemma composeCurryAtIJ_apply (s : ℕ)
    (i j : Fin (Module.finrank ℝ E))
    (B : Tensor0SModel s ℝ E →L[ℝ]
      Tensor0SModel s ℝ E →L[ℝ] ℝ)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ) :
    composeCurryAtIJ (E := E) s i j B S T =
      B (S.curryLeft ((chartModelBasis E) i))
        (T.curryLeft ((chartModelBasis E) j)) := by
  rfl

/-- The factorisation of `chartTensorInnerPointwise_0sCLM g (s+1) α b` as a
`Finset.sum` of `smul`s of `composeCurryAtIJ`-transformed s-step CLMs. This
identity is the basis for the smoothness induction. -/
private lemma chartTensorInnerPointwise_0sCLM_succ_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α b : M) :
    chartTensorInnerPointwise_0sCLM (I := I) (M := M) g (s + 1) α b
      = ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            (chartGramMatrix g α b)⁻¹ i j •
              composeCurryAtIJ (E := E) s i j
                (chartTensorInnerPointwise_0sCLM (I := I) (M := M) g s α b) := by
  refine ContinuousLinearMap.ext ?_
  intro S
  refine ContinuousLinearMap.ext ?_
  intro T
  rw [chartTensorInnerPointwise_0sCLM_apply, chartTensorInnerPointwise_0s_succ]
  -- RHS: evaluate the finite-sum CLM.
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
    composeCurryAtIJ_apply, smul_eq_mul,
    chartTensorInnerPointwise_0sCLM_apply]

/-! ### Smoothness of the CLM-valued chart-local inner product

Using the explicit factorisation, we prove smoothness of
`chartTensorInnerPointwise_0sCLM g s α b` as a function of `b ∈ chartAt α`,
viewed as a map into the fixed normed space `MLF →L MLF →L ℝ`. The induction
is on `s`, with the inductive step using `ContMDiffOn.smul` and the bilinear
"compose with constant" maps (which act on smooth-in-`b` CLMs via continuous
linear pre/post-composition). -/

/-! ### Continuity of the inner product on smooth tensor sections

We deliver the public continuity theorem `Tensor0SBundle.continuous_inner_of_smooth_sections`
via the following strategy:

1. Define `chartTensorInnerPointwise_0s` as a chart-local version of the
   pointwise inner product, using `chartGramMatrix g α b` (smooth in `b`)
   in place of `gramMatrixAt g b`.
2. Establish a basis-invariance identity relating the two pointwise inner
   products: `tensorInnerPointwise_0s s g b S T = chartTensorInnerPointwise_0s s g α b S_α(b) T_α(b)`
   where `S_α(b) = S.compContinuousLinearMap (fun _ => (triv α).symmL b)`.
3. From this, on each chart, the inner product on smooth sections becomes
   a continuous function of `b` because:
   - The chart-local Gram matrix and its inverse are smooth in `b`.
   - The trivialised tensor sections are smooth (continuous) in `b`.
4. Glue via chart cover for global continuity. -/

/-! ### Auxiliary CLMs and their relations

We package the chart-Jacobian and its inverse as CLMs and establish the
basic identities (round-trip, basis-vector image, Gram-matrix expansion). -/

/-- The chart-Jacobian on the fibre at `b`: the forward map of the tangent
trivialisation centred at `α`. -/
noncomputable def chartJ (α : M) (b : M) : E →L[ℝ] E :=
  (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b

/-- The chart-Jacobian inverse on the fibre at `b`: the backward map of the
tangent trivialisation centred at `α`. -/
noncomputable def chartJinv (α : M) (b : M) : E →L[ℝ] E :=
  (trivializationAt E (TangentSpace I) α).symmL ℝ b

lemma chartJinv_apply (α : M) (b : M) (v : E) :
    chartJinv (I := I) (M := M) α b v =
      (trivializationAt E (TangentSpace I) α).symmL ℝ b v := rfl

lemma chartJ_apply (α : M) (b : M) (v : E) :
    chartJ (I := I) (M := M) α b v =
      (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b v := rfl

/-- `chartJinv α b` images the model basis vector `(chartModelBasis E) i` to the
chart-α basis vector `chartBasisVecFiber α i b`. -/
private lemma chartJinv_basis (α : M) (b : M)
    (i : Fin (Module.finrank ℝ E)) :
    chartJinv (I := I) (M := M) α b ((chartModelBasis E) i) =
      chartBasisVecFiber (I := I) α i b := by
  unfold chartBasisVecFiber chartJinv
  rfl

/-- For `b` in the chart's base set, `chartJ α b ∘ chartJinv α b = id`. -/
lemma chartJ_chartJinv (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) (v : E) :
    chartJ (I := I) (M := M) α b
        (chartJinv (I := I) (M := M) α b v) = v := by
  unfold chartJ chartJinv
  exact (trivializationAt E (TangentSpace I) α).continuousLinearMapAt_symmL hb v

/-- For `b` in the chart's base set, `chartJinv α b ∘ chartJ α b = id` on `TangentSpace I b`. -/
lemma chartJinv_chartJ (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) (v : TangentSpace I b) :
    chartJinv (I := I) (M := M) α b
        (chartJ (I := I) (M := M) α b v) = v := by
  unfold chartJ chartJinv
  exact (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt hb v

/-- Alias for `chartJinv_chartJ`: useful as a rewrite target when the
type-synonym `TangentSpace I b = E` needs to be matched against `E` directly
in downstream files. -/
lemma chartJinv_chartJ_self (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) (v : E) :
    chartJinv (I := I) (M := M) α b
        (chartJ (I := I) (M := M) α b v) = v :=
  chartJinv_chartJ (I := I) (M := M) α hb v

/-! ### Gram matrix relationship

The chart-α Gram matrix is the Gram matrix of the metric on the
chart-α basis vectors `chartBasisVecFiber α i b = chartJinv α b ((chartModelBasis E) i)`.
This is equivalent to evaluating `g.inner b` on the corresponding model-basis
vectors after applying `chartJinv α b`. -/

/-- The chart-α Gram matrix entry expressed via `chartJinv α b`. -/
lemma chartGramMatrix_eq_innerJinv
    (g : SmoothRiemannianMetric I M) (α b : M)
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramMatrix g α b i j =
      g.inner b
        (chartJinv (I := I) (M := M) α b ((chartModelBasis E) i))
        (chartJinv (I := I) (M := M) α b ((chartModelBasis E) j)) := by
  rw [chartGramMatrix_apply]
  rw [chartJinv_basis (I := I) (M := M), chartJinv_basis (I := I) (M := M)]

/-! ### Linearity of `curryLeft` in its argument

The curryLeft slot map satisfies `T.curryLeft (∑ a c_a v_a) = ∑ a c_a (T.curryLeft v_a)`. -/

private lemma curryLeft_sum {n : ℕ} {s : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ)
    (c : Fin n → ℝ) (v : Fin n → E) :
    T.curryLeft (∑ k : Fin n, c k • v k) =
      ∑ k : Fin n, c k • T.curryLeft (v k) := by
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [map_smul]

/-! ### Composition lemma for `compContinuousLinearMap` and `curryLeft`

Lemma: `(T \circ_ML L).curryLeft w = (T.curryLeft (L w)) \circ_ML L`. -/

private lemma compContinuousLinearMap_curryLeft {s : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ)
    (L : E →L[ℝ] E) (w : E) :
    (T.compContinuousLinearMap (fun _ : Fin (s + 1) => L)).curryLeft w =
      (T.curryLeft (L w)).compContinuousLinearMap (fun _ : Fin s => L) := by
  ext m
  simp only [ContinuousMultilinearMap.curryLeft_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  -- LHS: T (fun i => L ((Fin.cons w m) i))
  -- RHS: T (Fin.cons (L w) (fun i => L (m i)))
  -- Show the two argument-tuples are equal by funext and Fin.cases.
  have hcons_eq : (fun i : Fin (s + 1) => L ((Fin.cons w m : Fin (s + 1) → E) i)) =
      (Fin.cons (L w) (fun i' : Fin s => L (m i')) : Fin (s + 1) → E) := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro i'
      simp
  rw [hcons_eq]

/-! ### Bilinearity of `tensorInnerPointwise_0s` over a finite sum

For sums `S = ∑ k c_k S_k`, `T = ∑ l d_l T_l`, the tensor inner product
expands as `∑_{k,l} c_k d_l ⟨S_k, T_l⟩`. -/

private lemma tensorInnerPointwise_0s_sum_left
    (g : SmoothRiemannianMetric I M) (b : M) (s : ℕ) {n : ℕ}
    (c : Fin n → ℝ) (S : Fin n → Tensor0SModel s ℝ E)
    (T : Tensor0SModel s ℝ E) :
    tensorInnerPointwise_0s (I := I) (M := M) s g b
        (∑ k : Fin n, c k • S k) T =
      ∑ k : Fin n, c k *
        tensorInnerPointwise_0s (I := I) (M := M) s g b (S k) T := by
  classical
  induction n with
  | zero =>
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      rw [show (0 : Tensor0SModel s ℝ E) =
        (0 : ℝ) • (0 : Tensor0SModel s ℝ E) from
        (zero_smul _ _).symm]
      rw [tensorInnerPointwise_0s_smul_left, zero_mul]
  | succ n ih =>
      -- Specialize ih to (fun k => c k.succ) (fun k => S k.succ).
      have ih_app := ih (fun k : Fin n => c k.succ) (fun k : Fin n => S k.succ)
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      rw [tensorInnerPointwise_0s_add_left, tensorInnerPointwise_0s_smul_left]
      rw [ih_app]

private lemma tensorInnerPointwise_0s_sum_right
    (g : SmoothRiemannianMetric I M) (b : M) (s : ℕ) {n : ℕ}
    (S : Tensor0SModel s ℝ E)
    (d : Fin n → ℝ) (T : Fin n → Tensor0SModel s ℝ E) :
    tensorInnerPointwise_0s (I := I) (M := M) s g b S
        (∑ l : Fin n, d l • T l) =
      ∑ l : Fin n, d l *
        tensorInnerPointwise_0s (I := I) (M := M) s g b S (T l) := by
  classical
  induction n with
  | zero =>
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      rw [show (0 : Tensor0SModel s ℝ E) =
        (0 : ℝ) • (0 : Tensor0SModel s ℝ E) from
        (zero_smul _ _).symm]
      rw [tensorInnerPointwise_0s_smul_right, zero_mul]
  | succ n ih =>
      have ih_app := ih (fun l : Fin n => d l.succ) (fun l : Fin n => T l.succ)
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      rw [tensorInnerPointwise_0s_add_right, tensorInnerPointwise_0s_smul_right]
      rw [ih_app]

/-! ### Helper for the bridge identity: a generalised inner-product formula

To avoid the matrix-level basis-change argument, we define a generalised
inner-product formula `tensorInnerOnFrame s b f Ginv T S`, parametric in
the basis `f` and the matrix `Ginv`. This is the same recursion as
`tensorInnerPointwise_0s` and `chartTensorInnerPointwise_0s` with the basis
`f` and matrix `Ginv` factored out. We prove that:

* `tensorInnerOnFrame s b (chartModelBasis E) (gramMatrixAt g b)⁻¹ T S =
   tensorInnerPointwise_0s s g b T S`.
* `tensorInnerOnFrame s b (chartBasisVecFiber α · b) (chartGramMatrix g α b)⁻¹ T S =
   tensorInnerPointwise_0s s g b T S` (basis-invariance for the same metric).
* The chart-α formula equals `chartTensorInnerPointwise_0s` precomposed with
   the trivialization. -/

/-- The generalised inner-product formula on a basis `f` with matrix `Ginv`. -/
private noncomputable def tensorInnerOnFrame :
    (s : ℕ) → (Fin (Module.finrank ℝ E) → E) →
      Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ →
      Tensor0SModel s ℝ E →
      Tensor0SModel s ℝ E → ℝ
  | 0, _, _, T, S => T (fun i => Fin.elim0 i) * S (fun i => Fin.elim0 i)
  | s + 1, f, Ginv, T, S =>
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        Ginv i j *
          tensorInnerOnFrame s f Ginv (T.curryLeft (f i)) (S.curryLeft (f j))

private lemma tensorInnerOnFrame_zero
    (f : Fin (Module.finrank ℝ E) → E)
    (Ginv : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (T S : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) :
    tensorInnerOnFrame (E := E) 0 f Ginv T S =
      T (fun i => Fin.elim0 i) * S (fun i => Fin.elim0 i) := rfl

private lemma tensorInnerOnFrame_succ (s : ℕ)
    (f : Fin (Module.finrank ℝ E) → E)
    (Ginv : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (T S : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ) :
    tensorInnerOnFrame (E := E) (s + 1) f Ginv T S =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        Ginv i j *
          tensorInnerOnFrame (E := E) s f Ginv (T.curryLeft (f i)) (S.curryLeft (f j)) := rfl

/-- `tensorInnerPointwise_0s s g b T S` agrees with `tensorInnerOnFrame s e G⁻¹` on
the model basis `e = chartModelBasis E` and `G = gramMatrixAt g b`. -/
private lemma tensorInnerPointwise_0s_eq_tensorInnerOnFrame
    (g : SmoothRiemannianMetric I M) (b : M) :
    ∀ (s : ℕ) (T S : Tensor0SModel s ℝ E),
      tensorInnerPointwise_0s (I := I) (M := M) s g b T S =
        tensorInnerOnFrame (E := E) s
          (fun i : Fin (Module.finrank ℝ E) => (chartModelBasis E) i)
          (gramMatrixAt (I := I) (M := M) g b)⁻¹ T S := by
  intro s
  induction s with
  | zero => intro T S; rfl
  | succ s ih =>
      intro T S
      rw [tensorInnerPointwise_0s_succ, tensorInnerOnFrame_succ]
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [ih (T.curryLeft ((chartModelBasis E) i))
          (S.curryLeft ((chartModelBasis E) j))]

/-- `chartTensorInnerPointwise_0s g α s b T S` agrees with `tensorInnerOnFrame s e G⁻¹`
on the model basis `e = chartModelBasis E` and `G = chartGramMatrix g α b`. -/
private lemma chartTensorInnerPointwise_0s_eq_tensorInnerOnFrame
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) :
    ∀ (s : ℕ) (T S : Tensor0SModel s ℝ E),
      chartTensorInnerPointwise_0s (I := I) (M := M) s g α b T S =
        tensorInnerOnFrame (E := E) s
          (fun i : Fin (Module.finrank ℝ E) => (chartModelBasis E) i)
          (chartGramMatrix g α b)⁻¹ T S := by
  intro s
  induction s with
  | zero => intro T S; rfl
  | succ s ih =>
      intro T S
      rw [chartTensorInnerPointwise_0s_succ, tensorInnerOnFrame_succ]
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [ih (T.curryLeft ((chartModelBasis E) i))
          (S.curryLeft ((chartModelBasis E) j))]

/-! ### Basis-change for `tensorInnerOnFrame`

The key fact: changing both the basis `f → h` and the matrix
`Ginv → Hinv` consistently with the gram-matrix transformation
preserves `tensorInnerOnFrame`. We don't formulate this in full
generality; instead, we prove the specific change-of-basis result
needed for the bridge identity. -/

/-! ### Frame-change strategy

For a basis `f`, an alternative basis `h_i = ∑_a A_{ai} f_a` expressed via a matrix `A`,
and the corresponding gram matrices `G_f` (on `f`), `G_h` (on `h`) satisfying
`G_h = Aᵀ G_f A`, we expect `tensorInnerOnFrame s h G_h⁻¹ T S = tensorInnerOnFrame s f G_f⁻¹ T S`.

We work in the special case where `f = chartModelBasis E`, `h_i = chartJinv α b (e_i)`,
`A = matrix of chartJinv`. Then `G_f = gramMatrixAt g b`, `G_h = chartGramMatrix g α b`.

We don't prove the abstract change-of-basis at the matrix level. Instead, we prove
the bridge identity DIRECTLY by induction on `s` using the recursion structure. -/

/-! ### The bridge identity, by direct induction

The bridge identity:
`tensorInnerPointwise_0s s g b T S = chartTensorInnerPointwise_0s g α s b T_α S_α`
where `T_α = T.compContinuousLinearMap (fun _ => chartJinv α b)`, on `b` in the chart
base set.

We prove this directly by induction on `s` using the basis-change argument:
the chart-α basis `chartBasisVecFiber α i b = chartJinv α b ((chartModelBasis E) i)`,
and the chart-α gram matrix `chartGramMatrix g α b` is the gram matrix of `g.inner b`
on this basis.

KEY OBSERVATION: An equivalent formulation is to prove the bridge in the form:
`tensorInnerPointwise_0s s g b T S = chartTensorInnerOnChartBasis s g α b T S`
where `chartTensorInnerOnChartBasis` uses the chart-α basis `chartBasisVecFiber` directly:
this is the "true basis-change" form. Then we can connect to
`chartTensorInnerPointwise_0s` (which uses the model basis) via the
`compContinuousLinearMap` substitution.

We follow this two-step path. -/

/-- An auxiliary inner product on the chart-α basis: same recursion as
`chartTensorInnerPointwise_0s` but using `chartBasisVecFiber α i b` (the chart-α basis)
instead of the fixed model basis. -/
private noncomputable def chartTensorInnerOnChartBasis :
    (s : ℕ) → SmoothRiemannianMetric I M → (α : M) → (b : M) →
      Tensor0SModel s ℝ E →
      Tensor0SModel s ℝ E → ℝ
  | 0, _g, _α, _b, T, S =>
      T (fun i => Fin.elim0 i) * S (fun i => Fin.elim0 i)
  | s + 1, g, α, b, T, S =>
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (chartGramMatrix g α b)⁻¹ i j *
          chartTensorInnerOnChartBasis s g α b
            (T.curryLeft (chartBasisVecFiber (I := I) α i b))
            (S.curryLeft (chartBasisVecFiber (I := I) α j b))

private lemma chartTensorInnerOnChartBasis_zero
    (g : SmoothRiemannianMetric I M) (α b : M)
    (T S : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) :
    chartTensorInnerOnChartBasis (I := I) (M := M) 0 g α b T S =
      T (fun i => Fin.elim0 i) * S (fun i => Fin.elim0 i) := rfl

private lemma chartTensorInnerOnChartBasis_succ
    (g : SmoothRiemannianMetric I M) (α b : M) (s : ℕ)
    (T S : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ) :
    chartTensorInnerOnChartBasis (I := I) (M := M) (s + 1) g α b T S =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (chartGramMatrix g α b)⁻¹ i j *
          chartTensorInnerOnChartBasis (I := I) (M := M) s g α b
            (T.curryLeft (chartBasisVecFiber (I := I) α i b))
            (S.curryLeft (chartBasisVecFiber (I := I) α j b)) := rfl

/-! ### Equality of the two chart-trivialised forms

We show `chartTensorInnerOnChartBasis s g α b T S =
   chartTensorInnerPointwise_0s g α s b T_α S_α`
where `T_α = T \circ_ML chartJinv α b`.

The proof uses the "compose-and-curry" identity
`(T \circ L).curryLeft (L w) = (T.curryLeft w) \circ L` slot-by-slot. -/

/-- The "compose-and-curry" relation, packaged for `chartJinv α b`:
given an arity-(s+1) tensor `T`, currying `T` at `chartJinv α b ((chartModelBasis E) i)`
in the slot, after composing with `chartJinv α b` in the remaining slots, equals the
result of currying first then composing with `chartJinv α b` in remaining slots. -/
private lemma chartJinv_compose_curry_chartBasis {s : ℕ} (α : M) (b : M)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ)
    (i : Fin (Module.finrank ℝ E)) :
    (T.compContinuousLinearMap (fun _ : Fin (s + 1) =>
        chartJinv (I := I) (M := M) α b)).curryLeft ((chartModelBasis E) i) =
      (T.curryLeft (chartBasisVecFiber (I := I) α i b)).compContinuousLinearMap
        (fun _ : Fin s => chartJinv (I := I) (M := M) α b) := by
  rw [compContinuousLinearMap_curryLeft]
  rw [chartJinv_basis (I := I) (M := M)]

/-- Bridge B: `chartTensorInnerOnChartBasis` (using chart-α basis)
equals `chartTensorInnerPointwise_0s` precomposed with `chartJinv α b`. -/
private theorem chartTensorInnerOnChartBasis_eq_chartTensorInnerPointwise_compose
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) :
    ∀ (s : ℕ) (T S : Tensor0SModel s ℝ E),
      chartTensorInnerOnChartBasis (I := I) (M := M) s g α b T S =
        chartTensorInnerPointwise_0s (I := I) (M := M) s g α b
          (T.compContinuousLinearMap (fun _ : Fin s =>
            chartJinv (I := I) (M := M) α b))
          (S.compContinuousLinearMap (fun _ : Fin s =>
            chartJinv (I := I) (M := M) α b)) := by
  intro s
  induction s with
  | zero =>
      intro T S
      rw [chartTensorInnerOnChartBasis_zero, chartTensorInnerPointwise_0s_zero]
      -- Both sides equal T(elim0) * S(elim0) since `compContinuousLinearMap` doesn't affect
      -- the result on the empty tuple `elim0`.
      simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
      congr 1 <;>
        · congr 1
          funext i
          exact i.elim0
  | succ s ih =>
      intro T S
      rw [chartTensorInnerOnChartBasis_succ, chartTensorInnerPointwise_0s_succ]
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [chartJinv_compose_curry_chartBasis (I := I) (M := M) α b T i,
          chartJinv_compose_curry_chartBasis (I := I) (M := M) α b S j]
      rw [ih (T.curryLeft (chartBasisVecFiber (I := I) α i b))
          (S.curryLeft (chartBasisVecFiber (I := I) α j b))]

/-! ### Bridge A: `tensorInnerPointwise_0s s g b T S = chartTensorInnerOnChartBasis s g α b T S`

This is the basis-invariance fact. The proof uses the matrix identity
`(chartGramMatrix)⁻¹ = (chartJinvMatrix) (gramMatrixAt)⁻¹ (chartJinvMatrix)ᵀ` (applied to `b` on chart base set), where `chartJinvMatrix` is the matrix of `chartJinv α b` in
the model basis.

We approach this in stages, building up the matrix identities. -/

/-- The matrix of `chartJinv α b` in the model basis: `(JinvMat α b)_{ai}`
is the `a`-th coordinate of `chartJinv α b ((chartModelBasis E) i)` in the basis. -/
private noncomputable def chartJinvMatrix (α : M) (b : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun a i =>
    ((chartModelBasis E).repr
      (chartJinv (I := I) (M := M) α b ((chartModelBasis E) i))) a

@[simp] private lemma chartJinvMatrix_apply (α : M) (b : M)
    (a i : Fin (Module.finrank ℝ E)) :
    chartJinvMatrix (I := I) (M := M) α b a i =
      ((chartModelBasis E).repr
        (chartJinv (I := I) (M := M) α b ((chartModelBasis E) i))) a := rfl

/-- The chart-α basis vector `chartBasisVecFiber α i b` decomposes via `chartJinvMatrix`
in the model basis. -/
private lemma chartBasisVecFiber_eq_sum (α : M) (b : M)
    (i : Fin (Module.finrank ℝ E)) :
    chartBasisVecFiber (I := I) α i b =
      ∑ a : Fin (Module.finrank ℝ E),
        chartJinvMatrix (I := I) (M := M) α b a i • (chartModelBasis E) a := by
  rw [← chartJinv_basis (I := I) (M := M) α b i]
  exact ((chartModelBasis E).sum_repr
    (chartJinv (I := I) (M := M) α b ((chartModelBasis E) i))).symm

/-- The matrix of `chartJ α b` in the model basis. -/
private noncomputable def chartJMatrix (α : M) (b : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun a i =>
    ((chartModelBasis E).repr
      (chartJ (I := I) (M := M) α b ((chartModelBasis E) i))) a

@[simp] private lemma chartJMatrix_apply (α : M) (b : M)
    (a i : Fin (Module.finrank ℝ E)) :
    chartJMatrix (I := I) (M := M) α b a i =
      ((chartModelBasis E).repr
        (chartJ (I := I) (M := M) α b ((chartModelBasis E) i))) a := rfl

/-- For any `v : E`, `(chartJ α b v)_a = ∑_k (chartJMatrix)_{a,k} (v decomposed in basis)_k`. -/
private lemma chartJ_apply_repr (α : M) (b : M) (v : E)
    (a : Fin (Module.finrank ℝ E)) :
    ((chartModelBasis E).repr (chartJ (I := I) (M := M) α b v)) a =
      ∑ k : Fin (Module.finrank ℝ E),
        chartJMatrix (I := I) (M := M) α b a k *
          ((chartModelBasis E).repr v) k := by
  -- v = ∑ k v_k e_k ⟹ chartJ v = ∑ k v_k (chartJ e_k) ⟹ repr_a (chartJ v) = ∑ k v_k * (chartJMatrix)_{a,k}
  have hv : v = ∑ k : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr v) k • (chartModelBasis E) k :=
    ((chartModelBasis E).sum_repr v).symm
  conv_lhs => rw [hv]
  rw [map_sum, map_sum]
  rw [Finsupp.coe_finset_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [map_smul, map_smul]
  rw [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, chartJMatrix_apply]
  ring

/-- Similarly, `(chartJinv α b v)_a = ∑_k (chartJinvMatrix)_{a,k} (v decomposed)_k`. -/
private lemma chartJinv_apply_repr (α : M) (b : M) (v : E)
    (a : Fin (Module.finrank ℝ E)) :
    ((chartModelBasis E).repr (chartJinv (I := I) (M := M) α b v)) a =
      ∑ k : Fin (Module.finrank ℝ E),
        chartJinvMatrix (I := I) (M := M) α b a k *
          ((chartModelBasis E).repr v) k := by
  have hv : v = ∑ k : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr v) k • (chartModelBasis E) k :=
    ((chartModelBasis E).sum_repr v).symm
  conv_lhs => rw [hv]
  rw [map_sum, map_sum]
  rw [Finsupp.coe_finset_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [map_smul, map_smul]
  rw [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, chartJinvMatrix_apply]
  ring

/-- The Gram matrix relationship at the matrix level:
`chartGramMatrix g α b = (chartJinvMatrix α b)ᵀ * gramMatrixAt g b * chartJinvMatrix α b`. -/
private lemma chartGramMatrix_eq_matrix_form
    (g : SmoothRiemannianMetric I M) (α b : M) :
    chartGramMatrix g α b =
      (chartJinvMatrix (I := I) (M := M) α b)ᵀ *
        gramMatrixAt (I := I) (M := M) g b *
        chartJinvMatrix (I := I) (M := M) α b := by
  ext i j
  -- LHS = chartGramMatrix_{i,j} = g.inner b (chartJinv e_i) (chartJinv e_j) (chartGramMatrix_eq_innerJinv).
  rw [chartGramMatrix_eq_innerJinv]
  -- Expand chartJinv e_i and chartJinv e_j as ∑ J_{a,i} e_a, ∑ J_{b',j} e_{b'}.
  have hi : chartJinv (I := I) (M := M) α b ((chartModelBasis E) i) =
      ∑ a, chartJinvMatrix (I := I) (M := M) α b a i • (chartModelBasis E) a := by
    rw [chartJinv_basis (I := I) (M := M) α b i]
    exact chartBasisVecFiber_eq_sum (I := I) (M := M) α b i
  have hj : chartJinv (I := I) (M := M) α b ((chartModelBasis E) j) =
      ∑ b', chartJinvMatrix (I := I) (M := M) α b b' j • (chartModelBasis E) b' := by
    rw [chartJinv_basis (I := I) (M := M) α b j]
    exact chartBasisVecFiber_eq_sum (I := I) (M := M) α b j
  rw [hi, hj]
  -- Bilinear expansion of g.inner b on the sums.
  -- LHS: g.inner b (∑ a J_{ai} • e_a) (∑ b' J_{b'j} • e_{b'}).
  -- We compute: g.inner b X = ∑_a J_{ai} g.inner b e_a (after smul/sum).
  --             g.inner b (∑a J_{ai} • e_a) (∑b' J_{b'j} • e_{b'})
  --           = ∑a ∑b' J_{ai} J_{b'j} g.inner b e_a e_{b'}.
  -- RHS: (J^T G J)_{i,j} = ∑a ∑b' J_{ai} G_{a,b'} J_{b'j} = same sum (since G_{a,b'} = g.inner b e_a e_{b'}).
  -- We prove LHS = RHS by showing both equal the same double sum.
  have hLHS_eq :
      (g.inner b (∑ a : Fin (Module.finrank ℝ E),
          chartJinvMatrix (I := I) (M := M) α b a i • (chartModelBasis E) a))
        (∑ b' : Fin (Module.finrank ℝ E),
          chartJinvMatrix (I := I) (M := M) α b b' j • (chartModelBasis E) b') =
      ∑ a : Fin (Module.finrank ℝ E),
        ∑ b' : Fin (Module.finrank ℝ E),
          chartJinvMatrix (I := I) (M := M) α b a i *
            chartJinvMatrix (I := I) (M := M) α b b' j *
            g.inner b ((chartModelBasis E) a) ((chartModelBasis E) b') := by
    -- Linearity of g.inner b on the first arg (sum + smul).
    have hL : g.inner b (∑ a : Fin (Module.finrank ℝ E),
          chartJinvMatrix (I := I) (M := M) α b a i • (chartModelBasis E) a) =
        ∑ a : Fin (Module.finrank ℝ E),
          chartJinvMatrix (I := I) (M := M) α b a i •
            g.inner b ((chartModelBasis E) a) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro a _
      exact ContinuousLinearMap.map_smul (g.inner b) _ _
    rw [hL, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
    -- (J_{ai}) * (g.inner b e_a) (∑ b' J_{b'j} • e_{b'}) = ∑ b' J_{ai} J_{b'j} (g.inner b e_a e_{b'}).
    rw [show (g.inner b ((chartModelBasis E) a))
        (∑ b' : Fin (Module.finrank ℝ E),
          chartJinvMatrix (I := I) (M := M) α b b' j • (chartModelBasis E) b') =
        ∑ b' : Fin (Module.finrank ℝ E),
          chartJinvMatrix (I := I) (M := M) α b b' j *
            g.inner b ((chartModelBasis E) a) ((chartModelBasis E) b') from ?_]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro b' _
      ring
    · rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro b' _
      rw [show ((g.inner b) ((chartModelBasis E) a))
          (chartJinvMatrix (I := I) (M := M) α b b' j • (chartModelBasis E) b') =
          chartJinvMatrix (I := I) (M := M) α b b' j •
            ((g.inner b) ((chartModelBasis E) a)) ((chartModelBasis E) b') from ?_]
      · rw [smul_eq_mul]
      · exact ContinuousLinearMap.map_smul ((g.inner b) ((chartModelBasis E) a)) _ _
  refine hLHS_eq.trans ?_
  -- RHS: (J^T G J)_{i,j} = ∑ b' (J^T G)_{i,b'} J_{b',j}, and (J^T G)_{i,b'} = ∑ a J_{a,i} G_{a,b'}.
  rw [Matrix.mul_apply]
  rw [show ∑ b' : Fin (Module.finrank ℝ E),
      ((chartJinvMatrix (I := I) (M := M) α b)ᵀ *
          gramMatrixAt (I := I) (M := M) g b) i b' *
        chartJinvMatrix (I := I) (M := M) α b b' j =
        ∑ b' : Fin (Module.finrank ℝ E),
          (∑ a : Fin (Module.finrank ℝ E),
            chartJinvMatrix (I := I) (M := M) α b a i *
              gramMatrixAt (I := I) (M := M) g b a b') *
            chartJinvMatrix (I := I) (M := M) α b b' j from ?_]
  · -- ∑ b' (∑ a J_{a,i} G_{a,b'}) * J_{b',j} = ∑ a ∑ b' J_{a,i} G_{a,b'} J_{b',j}.
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b' _
    rw [gramMatrixAt_apply]
    ring
  · refine Finset.sum_congr rfl ?_
    intro b' _
    rw [Matrix.mul_apply]
    -- (J^T)_{i,a} = J_{a,i} via Matrix.transpose_apply.
    refine congr_arg (· * chartJinvMatrix (I := I) (M := M) α b b' j) ?_
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [Matrix.transpose_apply]

/-- `chartJinvMatrix α b` is invertible on the chart base set, with inverse `chartJMatrix α b`. -/
private lemma chartJinvMatrix_mul_chartJMatrix (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartJinvMatrix (I := I) (M := M) α b *
        chartJMatrix (I := I) (M := M) α b = 1 := by
  ext a c
  rw [Matrix.mul_apply]
  -- JMat_{k,c} = repr_k (chartJ e_c) definitionally; sum = repr_a (chartJinv (chartJ e_c)).
  have hsum_eq : ∑ k, chartJinvMatrix (I := I) (M := M) α b a k *
      chartJMatrix (I := I) (M := M) α b k c =
    ((chartModelBasis E).repr (chartJinv (I := I) (M := M) α b
      (chartJ (I := I) (M := M) α b ((chartModelBasis E) c)))) a := by
    rw [chartJinv_apply_repr (I := I) (M := M) α b
      (chartJ (I := I) (M := M) α b ((chartModelBasis E) c)) a]
    rfl
  rw [hsum_eq]
  rw [chartJinv_chartJ (I := I) (M := M) α hb]
  rw [Module.Basis.repr_self]
  rw [Finsupp.single_apply]
  rw [Matrix.one_apply]
  by_cases hac : c = a
  · rw [if_pos hac]
    rw [if_pos hac.symm]
  · rw [if_neg hac]
    have : ¬ a = c := fun h => hac h.symm
    rw [if_neg this]

/-- The other direction: `chartJMatrix α b * chartJinvMatrix α b = 1`. -/
private lemma chartJMatrix_mul_chartJinvMatrix (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartJMatrix (I := I) (M := M) α b *
        chartJinvMatrix (I := I) (M := M) α b = 1 := by
  ext a c
  rw [Matrix.mul_apply]
  -- Rewrite each summand: JinvMat_{k,c} = repr_k (chartJinv e_c) (definitionally rfl).
  -- Then the sum equals repr_a (chartJ (chartJinv e_c)) by chartJ_apply_repr.
  have hsum_eq : ∑ k, chartJMatrix (I := I) (M := M) α b a k *
      chartJinvMatrix (I := I) (M := M) α b k c =
    ((chartModelBasis E).repr (chartJ (I := I) (M := M) α b
      (chartJinv (I := I) (M := M) α b ((chartModelBasis E) c)))) a := by
    rw [chartJ_apply_repr (I := I) (M := M) α b
      (chartJinv (I := I) (M := M) α b ((chartModelBasis E) c)) a]
    rfl
  rw [hsum_eq]
  rw [chartJ_chartJinv (I := I) (M := M) α hb]
  rw [Module.Basis.repr_self]
  rw [Finsupp.single_apply]
  rw [Matrix.one_apply]
  by_cases hac : c = a
  · rw [if_pos hac]
    rw [if_pos hac.symm]
  · rw [if_neg hac]
    have : ¬ a = c := fun h => hac h.symm
    rw [if_neg this]

/-- `chartJinvMatrix α b` is invertible on the chart base set, with inverse `chartJMatrix α b`. -/
private lemma chartJinvMatrix_inv (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    (chartJinvMatrix (I := I) (M := M) α b)⁻¹ =
      chartJMatrix (I := I) (M := M) α b := by
  apply Matrix.inv_eq_left_inv
  exact chartJMatrix_mul_chartJinvMatrix (I := I) (M := M) α hb

/-- The Gram matrix `chartGramMatrix` is invertible on the chart base set: its determinant
is positive (hence nonzero). -/
private lemma chartGramMatrix_isUnit_det
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    IsUnit (chartGramMatrix g α b).det :=
  (chartGramMatrix_det_pos (I := I) g α hb).ne'.isUnit

private lemma chartGramMatrix_isUnit
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    IsUnit (chartGramMatrix g α b) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr
    (chartGramMatrix_isUnit_det (I := I) (M := M) g α hb)

private lemma chartGramMatrix_inv_mul_self_at
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    (chartGramMatrix g α b)⁻¹ *
        chartGramMatrix g α b = 1 :=
  Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp
      (chartGramMatrix_isUnit (I := I) (M := M) g α hb))

private lemma chartGramMatrix_self_mul_inv_at
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartGramMatrix g α b *
        (chartGramMatrix g α b)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp
      (chartGramMatrix_isUnit (I := I) (M := M) g α hb))

/-- The key matrix identity expressed in entry form.
`∑ ij (chartGramMatrix)⁻¹_{ij} (chartJinvMatrix)_{ai} (chartJinvMatrix)_{b'j} = (gramMatrixAt)⁻¹_{ab'}`.

This follows from `chartGramMatrix = chartJinvMatrixᵀ * gramMatrixAt * chartJinvMatrix`,
inverted to `chartGramMatrix⁻¹ = chartJinvMatrix⁻¹ * gramMatrixAt⁻¹ * (chartJinvMatrixᵀ)⁻¹`,
multiplied by `chartJinvMatrix * (·) * chartJinvMatrixᵀ` and using
`chartJinvMatrix * chartJinvMatrix⁻¹ = 1`. -/
private lemma chartJinv_chartGramInv_chartJinvT_eq_gramInv_entry
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (a c : Fin (Module.finrank ℝ E)) :
    ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        (chartGramMatrix g α b)⁻¹ i j *
          (chartJinvMatrix (I := I) (M := M) α b a i *
            chartJinvMatrix (I := I) (M := M) α b c j) =
      (gramMatrixAt (I := I) (M := M) g b)⁻¹ a c := by
  -- Express the LHS as a matrix product (J * G⁻¹ * J^T)_{a,c}.
  have hLHS_form :
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (chartGramMatrix g α b)⁻¹ i j *
            (chartJinvMatrix (I := I) (M := M) α b a i *
              chartJinvMatrix (I := I) (M := M) α b c j)) =
      (chartJinvMatrix (I := I) (M := M) α b *
        (chartGramMatrix g α b)⁻¹ *
        (chartJinvMatrix (I := I) (M := M) α b)ᵀ) a c := by
    -- (J * G⁻¹ * J^T)_{a,c} = ∑ j (J * G⁻¹)_{a,j} * J_{c,j}
    --                       = ∑ j (∑ i J_{a,i} G⁻¹_{i,j}) * J_{c,j}.
    rw [Matrix.mul_apply]
    -- After mul_apply: goal RHS is ∑ j (J*G⁻¹)_{a,j} * (J^T)_{j,c}.
    -- Use sum_congr to rewrite each term.
    rw [show ∑ j : Fin (Module.finrank ℝ E),
        (chartJinvMatrix (I := I) (M := M) α b *
          (chartGramMatrix g α b)⁻¹) a j *
          (chartJinvMatrix (I := I) (M := M) α b)ᵀ j c =
        ∑ j : Fin (Module.finrank ℝ E),
          (∑ i : Fin (Module.finrank ℝ E),
            chartJinvMatrix (I := I) (M := M) α b a i *
            (chartGramMatrix g α b)⁻¹ i j) *
          chartJinvMatrix (I := I) (M := M) α b c j from ?_]
    · -- Now: LHS double sum = ∑ j (∑ i J_{a,i} G⁻¹_{i,j}) * J_{c,j}.
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
    · refine Finset.sum_congr rfl ?_
      intro j _
      rw [Matrix.mul_apply, Matrix.transpose_apply]
  rw [hLHS_form]
  -- Now we want to prove the matrix identity at the matrix level.
  -- Strategy: show `chartJinvMatrix * (chartGramMatrix)⁻¹ * (chartJinvMatrix)ᵀ * gramMatrixAt = 1`.
  -- Equivalent to `((LHS)⁻¹)_{a,c} = (gramMatrixAt)⁻¹_{a,c}`, i.e., `LHS = gramMatrixAt`.
  -- But that's not what we want...
  -- Actually, we want LHS_a,c = (G⁻¹)_a,c, which is equivalent to showing LHS * G = 1.
  --
  -- LHS * G = JinvMat * chartGram⁻¹ * JinvMatᵀ * G.
  -- We have chartGram = JinvMatᵀ * G * JinvMat, so chartGram * JinvMat⁻¹ = JinvMatᵀ * G,
  -- hence JinvMatᵀ * G = chartGram * JinvMat⁻¹.
  -- Multiply LHS * G = JinvMat * chartGram⁻¹ * (JinvMatᵀ * G) = JinvMat * chartGram⁻¹ * chartGram * JinvMat⁻¹ = JinvMat * 1 * JinvMat⁻¹ = 1.
  have hJinvMat_inv := chartJinvMatrix_inv (I := I) (M := M) α hb
  -- Use `Matrix.eq_inv_of_mul_eq_one_right`: if `A * B = 1`, then `B = A⁻¹`.
  have hrhs : (chartJinvMatrix (I := I) (M := M) α b *
      (chartGramMatrix g α b)⁻¹ *
      (chartJinvMatrix (I := I) (M := M) α b)ᵀ) *
      gramMatrixAt (I := I) (M := M) g b = 1 := by
    -- Use chartGramMatrix = JinvMatᵀ * G * JinvMat.
    have hGramEq := chartGramMatrix_eq_matrix_form (I := I) (M := M) g α b
    -- hGramEq: chartGramMatrix = JinvMatᵀ * gramMatrixAt * JinvMat
    -- i.e., chartGramMatrix * JinvMat⁻¹ = JinvMatᵀ * gramMatrixAt (right multiply)
    -- Substitute (JinvMatᵀ * G) = chartGram * JinvMat⁻¹ in the goal.
    have hJinvMatT_mul_G :
        (chartJinvMatrix (I := I) (M := M) α b)ᵀ *
            gramMatrixAt (I := I) (M := M) g b =
          chartGramMatrix g α b *
            (chartJinvMatrix (I := I) (M := M) α b)⁻¹ := by
      -- From hGramEq: chartGram = JinvMatᵀ * G * JinvMat.
      -- Right-multiply both sides by JinvMat⁻¹:
      -- chartGram * JinvMat⁻¹ = JinvMatᵀ * G * (JinvMat * JinvMat⁻¹) = JinvMatᵀ * G * 1.
      rw [hGramEq, hJinvMat_inv]
      rw [Matrix.mul_assoc, Matrix.mul_assoc]
      rw [chartJinvMatrix_mul_chartJMatrix (I := I) (M := M) α hb]
      rw [Matrix.mul_one]
    -- Now compute (JinvMat * chartGram⁻¹ * JinvMatᵀ) * G:
    rw [Matrix.mul_assoc, Matrix.mul_assoc,
      hJinvMatT_mul_G,
      ← Matrix.mul_assoc (chartGramMatrix g α b)⁻¹,
      chartGramMatrix_inv_mul_self_at (I := I) (M := M) g α hb,
      Matrix.one_mul,
      hJinvMat_inv,
      chartJinvMatrix_mul_chartJMatrix (I := I) (M := M) α hb]
  -- From hrhs: (JinvMat * chartGram⁻¹ * JinvMatᵀ) * G = 1.
  -- Hence JinvMat * chartGram⁻¹ * JinvMatᵀ = G⁻¹ (right-inverse uniqueness).
  have hMain : chartJinvMatrix (I := I) (M := M) α b *
      (chartGramMatrix g α b)⁻¹ *
      (chartJinvMatrix (I := I) (M := M) α b)ᵀ =
      (gramMatrixAt (I := I) (M := M) g b)⁻¹ := by
    -- hrhs: X * G = 1. Hence G⁻¹ = X by Matrix.inv_eq_left_inv.
    exact (Matrix.inv_eq_left_inv hrhs).symm
  rw [hMain]

/-! ### Bridge A: `tensorInnerPointwise_0s s g b T S = chartTensorInnerOnChartBasis s g α b T S`

This is the basis-invariance fact. We prove it by induction on `s`. -/

private theorem tensorInnerPointwise_0s_eq_chartTensorInnerOnChartBasis
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ (s : ℕ) {b : M},
      b ∈ (trivializationAt E (TangentSpace I) α).baseSet →
      ∀ (T S : Tensor0SModel s ℝ E),
      tensorInnerPointwise_0s (I := I) (M := M) s g b T S =
        chartTensorInnerOnChartBasis (I := I) (M := M) s g α b T S := by
  intro s
  induction s with
  | zero =>
      intro b _ T S
      rw [tensorInnerPointwise_0s_zero_arity, chartTensorInnerOnChartBasis_zero]
  | succ s ih =>
      intro b hb T S
      rw [tensorInnerPointwise_0s_succ, chartTensorInnerOnChartBasis_succ]
      -- The strategy:
      -- LHS = ∑ ij G⁻¹_{ij} tensorInner s g b (T.curryLeft e_i) (S.curryLeft e_j)
      -- RHS = ∑ ij chartGram⁻¹_{ij} chartTensorInnerOnChartBasis s g α b
      --                              (T.curryLeft (chartBasisVecFiber α i b)) ...
      -- By IH, replace chartTensorInnerOnChartBasis by tensorInnerPointwise_0s in RHS.
      -- Then expand chartBasisVecFiber via JinvMat-decomposition, use bilinearity, then
      -- apply the matrix identity.
      --
      -- Step 1: Replace chartTensorInnerOnChartBasis by tensorInnerPointwise_0s in RHS.
      have step1 :
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              (chartGramMatrix g α b)⁻¹ i j *
                chartTensorInnerOnChartBasis (I := I) (M := M) s g α b
                  (T.curryLeft (chartBasisVecFiber (I := I) α i b))
                  (S.curryLeft (chartBasisVecFiber (I := I) α j b)) =
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              (chartGramMatrix g α b)⁻¹ i j *
                tensorInnerPointwise_0s (I := I) (M := M) s g b
                  (T.curryLeft (chartBasisVecFiber (I := I) α i b))
                  (S.curryLeft (chartBasisVecFiber (I := I) α j b)) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [← ih hb _ _]
      rw [step1]
      -- Step 2: Expand each chartBasisVecFiber-based curryLeft via JinvMat-decomposition.
      have step2_T : ∀ i : Fin (Module.finrank ℝ E),
          T.curryLeft (chartBasisVecFiber (I := I) α i b) =
            ∑ a : Fin (Module.finrank ℝ E),
              chartJinvMatrix (I := I) (M := M) α b a i •
                T.curryLeft ((chartModelBasis E) a) := by
        intro i
        rw [chartBasisVecFiber_eq_sum (I := I) (M := M) α b i]
        exact curryLeft_sum (E := E) (s := s) T _ _
      have step2_S : ∀ j : Fin (Module.finrank ℝ E),
          S.curryLeft (chartBasisVecFiber (I := I) α j b) =
            ∑ b' : Fin (Module.finrank ℝ E),
              chartJinvMatrix (I := I) (M := M) α b b' j •
                S.curryLeft ((chartModelBasis E) b') := by
        intro j
        rw [chartBasisVecFiber_eq_sum (I := I) (M := M) α b j]
        exact curryLeft_sum (E := E) (s := s) S _ _
      -- Step 3: Use bilinearity to expand the inner pointwise inner-product.
      have step3 : ∀ i j : Fin (Module.finrank ℝ E),
          tensorInnerPointwise_0s (I := I) (M := M) s g b
              (T.curryLeft (chartBasisVecFiber (I := I) α i b))
              (S.curryLeft (chartBasisVecFiber (I := I) α j b)) =
            ∑ a : Fin (Module.finrank ℝ E),
              ∑ b' : Fin (Module.finrank ℝ E),
                chartJinvMatrix (I := I) (M := M) α b a i *
                  chartJinvMatrix (I := I) (M := M) α b b' j *
                tensorInnerPointwise_0s (I := I) (M := M) s g b
                  (T.curryLeft ((chartModelBasis E) a))
                  (S.curryLeft ((chartModelBasis E) b')) := by
        intro i j
        rw [step2_T i, step2_S j]
        rw [tensorInnerPointwise_0s_sum_left]
        refine Finset.sum_congr rfl ?_
        intro a _
        rw [tensorInnerPointwise_0s_sum_right]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro b' _
        ring
      -- Step 4: Substitute into the sum.
      have step4 :
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              (chartGramMatrix g α b)⁻¹ i j *
                tensorInnerPointwise_0s (I := I) (M := M) s g b
                  (T.curryLeft (chartBasisVecFiber (I := I) α i b))
                  (S.curryLeft (chartBasisVecFiber (I := I) α j b)) =
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∑ a : Fin (Module.finrank ℝ E),
                ∑ b' : Fin (Module.finrank ℝ E),
                  (chartGramMatrix g α b)⁻¹ i j *
                    (chartJinvMatrix (I := I) (M := M) α b a i *
                      chartJinvMatrix (I := I) (M := M) α b b' j) *
                    tensorInnerPointwise_0s (I := I) (M := M) s g b
                      (T.curryLeft ((chartModelBasis E) a))
                      (S.curryLeft ((chartModelBasis E) b')) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [step3 i j]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro a _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro b' _
        ring
      rw [step4]
      -- Step 5: Reorder sums from (∑i ∑j ∑a ∑b') to (∑a ∑b' ∑i ∑j).
      -- Use Finset.sum_comm 3 times.
      have step5_0 :
          ∀ (i : Fin (Module.finrank ℝ E)),
            ∑ j : Fin (Module.finrank ℝ E),
              ∑ a : Fin (Module.finrank ℝ E),
                ∑ b' : Fin (Module.finrank ℝ E),
                  (chartGramMatrix g α b)⁻¹ i j *
                    (chartJinvMatrix (I := I) (M := M) α b a i *
                      chartJinvMatrix (I := I) (M := M) α b b' j) *
                    tensorInnerPointwise_0s (I := I) (M := M) s g b
                      (T.curryLeft ((chartModelBasis E) a))
                      (S.curryLeft ((chartModelBasis E) b')) =
            ∑ a : Fin (Module.finrank ℝ E),
              ∑ b' : Fin (Module.finrank ℝ E),
                ∑ j : Fin (Module.finrank ℝ E),
                  (chartGramMatrix g α b)⁻¹ i j *
                    (chartJinvMatrix (I := I) (M := M) α b a i *
                      chartJinvMatrix (I := I) (M := M) α b b' j) *
                    tensorInnerPointwise_0s (I := I) (M := M) s g b
                      (T.curryLeft ((chartModelBasis E) a))
                      (S.curryLeft ((chartModelBasis E) b')) := by
        intro i
        -- Step a: swap j,a: ∑j ∑a → ∑a ∑j.
        rw [Finset.sum_comm (γ := Fin (Module.finrank ℝ E))]
        refine Finset.sum_congr rfl ?_
        intro a _
        -- Step b: swap j,b': ∑j ∑b' → ∑b' ∑j.
        rw [Finset.sum_comm (γ := Fin (Module.finrank ℝ E))]
      have step5_1 :
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∑ a : Fin (Module.finrank ℝ E),
                ∑ b' : Fin (Module.finrank ℝ E),
                  (chartGramMatrix g α b)⁻¹ i j *
                    (chartJinvMatrix (I := I) (M := M) α b a i *
                      chartJinvMatrix (I := I) (M := M) α b b' j) *
                    tensorInnerPointwise_0s (I := I) (M := M) s g b
                      (T.curryLeft ((chartModelBasis E) a))
                      (S.curryLeft ((chartModelBasis E) b')) =
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ a : Fin (Module.finrank ℝ E),
              ∑ b' : Fin (Module.finrank ℝ E),
                ∑ j : Fin (Module.finrank ℝ E),
                  (chartGramMatrix g α b)⁻¹ i j *
                    (chartJinvMatrix (I := I) (M := M) α b a i *
                      chartJinvMatrix (I := I) (M := M) α b b' j) *
                    tensorInnerPointwise_0s (I := I) (M := M) s g b
                      (T.curryLeft ((chartModelBasis E) a))
                      (S.curryLeft ((chartModelBasis E) b')) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        exact step5_0 i
      have step5 :
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∑ a : Fin (Module.finrank ℝ E),
                ∑ b' : Fin (Module.finrank ℝ E),
                  (chartGramMatrix g α b)⁻¹ i j *
                    (chartJinvMatrix (I := I) (M := M) α b a i *
                      chartJinvMatrix (I := I) (M := M) α b b' j) *
                    tensorInnerPointwise_0s (I := I) (M := M) s g b
                      (T.curryLeft ((chartModelBasis E) a))
                      (S.curryLeft ((chartModelBasis E) b')) =
          ∑ a : Fin (Module.finrank ℝ E),
            ∑ b' : Fin (Module.finrank ℝ E),
              ∑ i : Fin (Module.finrank ℝ E),
                ∑ j : Fin (Module.finrank ℝ E),
                  (chartGramMatrix g α b)⁻¹ i j *
                    (chartJinvMatrix (I := I) (M := M) α b a i *
                      chartJinvMatrix (I := I) (M := M) α b b' j) *
                    tensorInnerPointwise_0s (I := I) (M := M) s g b
                      (T.curryLeft ((chartModelBasis E) a))
                      (S.curryLeft ((chartModelBasis E) b')) := by
        rw [step5_1]
        -- Now: ∑i ∑a ∑b' ∑j → ∑a ∑i ∑b' ∑j → ∑a ∑b' ∑i ∑j.
        rw [Finset.sum_comm (γ := Fin (Module.finrank ℝ E))]
        refine Finset.sum_congr rfl ?_
        intro a _
        rw [Finset.sum_comm (γ := Fin (Module.finrank ℝ E))]
      rw [step5]
      -- Step 6: Factor out tensorInnerPointwise_0s from inner sums.
      have step6 :
          ∑ a : Fin (Module.finrank ℝ E),
            ∑ b' : Fin (Module.finrank ℝ E),
              ∑ i : Fin (Module.finrank ℝ E),
                ∑ j : Fin (Module.finrank ℝ E),
                  (chartGramMatrix g α b)⁻¹ i j *
                    (chartJinvMatrix (I := I) (M := M) α b a i *
                      chartJinvMatrix (I := I) (M := M) α b b' j) *
                    tensorInnerPointwise_0s (I := I) (M := M) s g b
                      (T.curryLeft ((chartModelBasis E) a))
                      (S.curryLeft ((chartModelBasis E) b')) =
          ∑ a : Fin (Module.finrank ℝ E),
            ∑ b' : Fin (Module.finrank ℝ E),
              (∑ i : Fin (Module.finrank ℝ E),
                ∑ j : Fin (Module.finrank ℝ E),
                  (chartGramMatrix g α b)⁻¹ i j *
                    (chartJinvMatrix (I := I) (M := M) α b a i *
                      chartJinvMatrix (I := I) (M := M) α b b' j)) *
                tensorInnerPointwise_0s (I := I) (M := M) s g b
                  (T.curryLeft ((chartModelBasis E) a))
                  (S.curryLeft ((chartModelBasis E) b')) := by
        refine Finset.sum_congr rfl ?_
        intro a _
        refine Finset.sum_congr rfl ?_
        intro b' _
        -- (∑ i ∑ j (X i j) * Y) = (∑ i ∑ j X i j) * Y
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [Finset.sum_mul]
      rw [step6]
      -- Step 7: Apply matrix identity.
      have step7 : ∀ (a c : Fin (Module.finrank ℝ E)),
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              (chartGramMatrix g α b)⁻¹ i j *
                (chartJinvMatrix (I := I) (M := M) α b a i *
                  chartJinvMatrix (I := I) (M := M) α b c j) =
            (gramMatrixAt (I := I) (M := M) g b)⁻¹ a c := fun a c =>
        chartJinv_chartGramInv_chartJinvT_eq_gramInv_entry
          (I := I) (M := M) g α hb a c
      have step8 :
          ∑ a : Fin (Module.finrank ℝ E),
            ∑ b' : Fin (Module.finrank ℝ E),
              (∑ i : Fin (Module.finrank ℝ E),
                ∑ j : Fin (Module.finrank ℝ E),
                  (chartGramMatrix g α b)⁻¹ i j *
                    (chartJinvMatrix (I := I) (M := M) α b a i *
                      chartJinvMatrix (I := I) (M := M) α b b' j)) *
                tensorInnerPointwise_0s (I := I) (M := M) s g b
                  (T.curryLeft ((chartModelBasis E) a))
                  (S.curryLeft ((chartModelBasis E) b')) =
          ∑ a : Fin (Module.finrank ℝ E),
            ∑ b' : Fin (Module.finrank ℝ E),
              (gramMatrixAt (I := I) (M := M) g b)⁻¹ a b' *
                tensorInnerPointwise_0s (I := I) (M := M) s g b
                  (T.curryLeft ((chartModelBasis E) a))
                  (S.curryLeft ((chartModelBasis E) b')) := by
        refine Finset.sum_congr rfl ?_
        intro a _
        refine Finset.sum_congr rfl ?_
        intro b' _
        rw [step7 a b']
      -- Now goal: LHS = step8's RHS, which is the LHS form. So we should have equality with LHS now.
      symm
      exact step8

/-! ### Combining bridges: the main bridge identity -/

/-- **The bridge identity**, formal version.

For any tensors `T, S : MLF s`, on `b ∈ (chartAt H α).source` (= the trivialisation base set):
$$\text{tensorInnerPointwise\_0s s g b T S = chartTensorInnerPointwise\_0s g α s b T_α S_α}$$
where $T_α = T \circ_\text{ML} \text{chartJinv α b}$ and similarly for $S_α$. -/
theorem tensorInnerPointwise_0s_bridge_identity
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ (s : ℕ) {b : M},
      b ∈ (trivializationAt E (TangentSpace I) α).baseSet →
      ∀ (T S : Tensor0SModel s ℝ E),
      tensorInnerPointwise_0s (I := I) (M := M) s g b T S =
        chartTensorInnerPointwise_0s (I := I) (M := M) s g α b
          (T.compContinuousLinearMap (fun _ : Fin s =>
            chartJinv (I := I) (M := M) α b))
          (S.compContinuousLinearMap (fun _ : Fin s =>
            chartJinv (I := I) (M := M) α b)) := by
  intro s b hb T S
  rw [tensorInnerPointwise_0s_eq_chartTensorInnerOnChartBasis
      (I := I) (M := M) g α s hb T S]
  rw [chartTensorInnerOnChartBasis_eq_chartTensorInnerPointwise_compose
      (I := I) (M := M) g α b s T S]

/-! ### Continuity of `chartTensorInnerPointwise_0s` with smooth tensor arguments

We extend the smoothness lemma `chartTensorInnerPointwise_0s_contMDiffOn` (for fixed
tensor args) to the case where the tensor arguments themselves are smooth functions
of `b` on the chart base set. The proof is by induction on `s`. -/

-- File-local instance to ensure typeclass resolution finds NormedSpace on Tensor0SModel.
private instance tensor0SModelNormedSpace_local {s : ℕ} :
    NormedSpace ℝ (Tensor0SModel s ℝ E) :=
  Tensor0SBundle.tensor0SModel_normedSpace s

-- File-local instance for NormedAddCommGroup on Tensor0SModel.
private instance tensor0SModelNormedAddCommGroup_local {s : ℕ} :
    NormedAddCommGroup (Tensor0SModel s ℝ E) := inferInstance


/-! ### Continuity of `chartTensorInnerPointwise_0s` with smooth tensor arguments

We extend the smoothness lemma `chartTensorInnerPointwise_0s_contMDiffOn` (for fixed
tensor args) to the case where the tensor arguments themselves are smooth functions
of `b` on the chart base set. The proof is by induction on `s`, using
`curryLeftAtCLM` (a CLM, avoiding curryEquiv normed-instance issues) to extract the
arguments at each induction step. -/

/-- The chart-local inner product is continuous in `b` on the chart base set
when the tensor arguments are continuous functions of `b`. -/
lemma chartTensorInnerPointwise_0s_continuousOn_smooth_args
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ (s : ℕ)
    (T S : M → ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
    (_hT : ContinuousOn T (trivializationAt E (TangentSpace I) α).baseSet)
    (_hS : ContinuousOn S (trivializationAt E (TangentSpace I) α).baseSet),
      ContinuousOn (fun b : M =>
          chartTensorInnerPointwise_0s (I := I) (M := M) s g α b (T b) (S b))
        (trivializationAt E (TangentSpace I) α).baseSet := by
  intro s
  induction s with
  | zero =>
      intro T S hT hS
      have heval0 : Continuous
          (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ =>
            T (fun i => Fin.elim0 i)) :=
        continuous_id.eval_const _
      have heq : (fun b : M =>
          chartTensorInnerPointwise_0s (I := I) (M := M) 0 g α b (T b) (S b)) =
          fun b : M =>
            ((T b) (fun i => Fin.elim0 i)) * ((S b) (fun i => Fin.elim0 i)) := by
        funext b
        rw [chartTensorInnerPointwise_0s_zero]
      rw [heq]
      exact (heval0.comp_continuousOn hT).mul (heval0.comp_continuousOn hS)
  | succ s ih =>
      intro T S hT hS
      have heq : (fun b : M =>
          chartTensorInnerPointwise_0s (I := I) (M := M) (s + 1) g α b (T b) (S b)) =
          fun b : M =>
            ∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                (chartGramMatrix g α b)⁻¹ i j *
                  chartTensorInnerPointwise_0s (I := I) (M := M) s g α b
                    ((T b).curryLeft ((chartModelBasis E) i))
                    ((S b).curryLeft ((chartModelBasis E) j)) := by
        funext b
        rw [chartTensorInnerPointwise_0s_succ]
      rw [heq]
      refine continuousOn_finset_sum _ (fun i _ => ?_)
      refine continuousOn_finset_sum _ (fun j _ => ?_)
      refine ContinuousOn.mul ?_ ?_
      · exact (chartGramMatrix_inv_entry_contMDiffOn (I := I) g α i j).continuousOn
      · -- Apply ih: need continuity of the curryLeft-applied tensors as functions of b.
        -- Use the existing `curryLeftAtCLM` (a CLM) for continuity.
        have hT_curry : ContinuousOn
            (fun b : M => (T b).curryLeft ((chartModelBasis E) i))
            (trivializationAt E (TangentSpace I) α).baseSet := by
          have hheq : (fun b : M => (T b).curryLeft ((chartModelBasis E) i)) =
              fun b : M => curryLeftAtCLM (E := E) s ((chartModelBasis E) i) (T b) := by
            funext b
            rw [curryLeftAtCLM_apply]
          rw [hheq]
          exact (curryLeftAtCLM (E := E) s ((chartModelBasis E) i)).continuous.comp_continuousOn hT
        have hS_curry : ContinuousOn
            (fun b : M => (S b).curryLeft ((chartModelBasis E) j))
            (trivializationAt E (TangentSpace I) α).baseSet := by
          have hheq : (fun b : M => (S b).curryLeft ((chartModelBasis E) j)) =
              fun b : M => curryLeftAtCLM (E := E) s ((chartModelBasis E) j) (S b) := by
            funext b
            rw [curryLeftAtCLM_apply]
          rw [hheq]
          exact (curryLeftAtCLM (E := E) s ((chartModelBasis E) j)).continuous.comp_continuousOn hS
        exact ih _ _ hT_curry hS_curry

/-- The chart-local inner product is smooth in `b` on the chart base set when
each basis-tuple evaluation of the two tensor arguments is a smooth scalar
function of `b`. This is the smoothness analog of
`chartTensorInnerPointwise_0s_continuousOn_smooth_args`. The hypothesis form
(scalar smoothness of every basis-tuple evaluation) is used directly because
the diamond between `ContinuousMultilinearMap.instModule` and
`NormedSpace.toModule` on `Tensor0SModel` makes a direct `ContMDiffOn`
hypothesis on a `Tensor0SModel`-valued function awkward. The proof is by
induction on `s`. -/
lemma chartTensorInnerPointwise_0s_contMDiffOn_smooth_args
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ (s : ℕ)
    (T S : M → ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
    (_hT : ∀ φ : Fin s → Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => (T b) (fun k : Fin s => (chartModelBasis E) (φ k)))
        (trivializationAt E (TangentSpace I) α).baseSet)
    (_hS : ∀ φ : Fin s → Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => (S b) (fun k : Fin s => (chartModelBasis E) (φ k)))
        (trivializationAt E (TangentSpace I) α).baseSet),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M =>
          chartTensorInnerPointwise_0s (I := I) (M := M) s g α b (T b) (S b))
        (trivializationAt E (TangentSpace I) α).baseSet := by
  intro s
  induction s with
  | zero =>
      intro T S hT hS
      have heq : (fun b : M =>
          chartTensorInnerPointwise_0s (I := I) (M := M) 0 g α b (T b) (S b)) =
          fun b : M =>
            ((T b) (fun i => Fin.elim0 i)) * ((S b) (fun i => Fin.elim0 i)) := by
        funext b
        rw [chartTensorInnerPointwise_0s_zero]
      rw [heq]
      have hT0 := hT (fun i : Fin 0 => Fin.elim0 i)
      have hS0 := hS (fun i : Fin 0 => Fin.elim0 i)
      -- The two-tuple shapes `fun i => Fin.elim0 i` and the one used by `hT0`
      -- agree as functions on `Fin 0`.
      have hempty :
          (fun k : Fin 0 => (chartModelBasis E) ((fun i : Fin 0 => Fin.elim0 i) k))
            = (fun i : Fin 0 => (Fin.elim0 i : E)) := by
        funext i
        exact Fin.elim0 i
      have hT_smooth :
          ContMDiffOn I 𝓘(ℝ) ∞
            (fun b : M => (T b) (fun i => Fin.elim0 i))
            (trivializationAt E (TangentSpace I) α).baseSet := by
        have : (fun b : M => (T b) (fun i : Fin 0 => Fin.elim0 i)) =
            (fun b : M => (T b)
              (fun k : Fin 0 =>
                (chartModelBasis E) ((fun i : Fin 0 => Fin.elim0 i) k))) := by
          funext b
          congr 1
          rw [hempty]
        rw [this]
        exact hT0
      have hS_smooth :
          ContMDiffOn I 𝓘(ℝ) ∞
            (fun b : M => (S b) (fun i => Fin.elim0 i))
            (trivializationAt E (TangentSpace I) α).baseSet := by
        have : (fun b : M => (S b) (fun i : Fin 0 => Fin.elim0 i)) =
            (fun b : M => (S b)
              (fun k : Fin 0 =>
                (chartModelBasis E) ((fun i : Fin 0 => Fin.elim0 i) k))) := by
          funext b
          congr 1
          rw [hempty]
        rw [this]
        exact hS0
      exact hT_smooth.mul hS_smooth
  | succ s ih =>
      intro T S hT hS
      have heq : (fun b : M =>
          chartTensorInnerPointwise_0s (I := I) (M := M) (s + 1) g α b (T b) (S b)) =
          fun b : M =>
            ∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                (chartGramMatrix g α b)⁻¹ i j *
                  chartTensorInnerPointwise_0s (I := I) (M := M) s g α b
                    ((T b).curryLeft ((chartModelBasis E) i))
                    ((S b).curryLeft ((chartModelBasis E) j)) := by
        funext b
        rw [chartTensorInnerPointwise_0s_succ]
      rw [heq]
      refine contMDiffOn_finset_sum (fun i _ => ?_)
      refine contMDiffOn_finset_sum (fun j _ => ?_)
      refine ContMDiffOn.mul ?_ ?_
      · exact chartGramMatrix_inv_entry_contMDiffOn (I := I) g α i j
      · -- Apply the inductive hypothesis to the curryLeft-applied tensors.
        -- Each basis evaluation of the curryLeft tensor unfolds to a basis
        -- evaluation of the original tensor on the extended `Fin.cons`-tuple.
        refine ih
            (fun b : M => (T b).curryLeft ((chartModelBasis E) i))
            (fun b : M => (S b).curryLeft ((chartModelBasis E) j))
            ?_ ?_
        · intro ψ
          -- The cons-extended index tuple at the basis level.
          set ψ' : Fin (s + 1) → Fin (Module.finrank ℝ E) :=
            Fin.cons (α := fun _ => Fin (Module.finrank ℝ E)) i ψ with hψ'
          have hψ'_zero : ψ' 0 = i := by
            simp [hψ']
          have hψ'_succ : ∀ k : Fin s, ψ' k.succ = ψ k := by
            intro k
            simp [hψ']
          have heq' :
              (fun b : M => ((T b).curryLeft ((chartModelBasis E) i))
                  (fun k : Fin s => (chartModelBasis E) (ψ k)))
                = fun b : M =>
                    (T b) (fun k : Fin (s + 1) =>
                      (chartModelBasis E) (ψ' k)) := by
            funext b
            rw [ContinuousMultilinearMap.curryLeft_apply]
            congr 1
            funext k
            refine Fin.cases ?_ ?_ k
            · -- At k = 0: cons is i; on the LHS, this is i (since Fin.cons at 0)
              rw [hψ'_zero]
              -- The LHS at 0 is `Fin.cons ((chartModelBasis E) i) (fun k =>
              -- (chartModelBasis E) (ψ k)) 0 = (chartModelBasis E) i`.
              simp
            · intro k'
              rw [hψ'_succ k']
              simp
          rw [heq']
          exact hT ψ'
        · intro ψ
          set ψ' : Fin (s + 1) → Fin (Module.finrank ℝ E) :=
            Fin.cons (α := fun _ => Fin (Module.finrank ℝ E)) j ψ with hψ'
          have hψ'_zero : ψ' 0 = j := by
            simp [hψ']
          have hψ'_succ : ∀ k : Fin s, ψ' k.succ = ψ k := by
            intro k
            simp [hψ']
          have heq' :
              (fun b : M => ((S b).curryLeft ((chartModelBasis E) j))
                  (fun k : Fin s => (chartModelBasis E) (ψ k)))
                = fun b : M =>
                    (S b) (fun k : Fin (s + 1) =>
                      (chartModelBasis E) (ψ' k)) := by
            funext b
            rw [ContinuousMultilinearMap.curryLeft_apply]
            congr 1
            funext k
            refine Fin.cases ?_ ?_ k
            · rw [hψ'_zero]; simp
            · intro k'
              rw [hψ'_succ k']; simp
          rw [heq']
          exact hS ψ'

/-! ### Public continuity theorem on each chart

Given the bridge identity and the chart-local smoothness, we obtain
chart-local continuity of the inner product on smooth tensor sections. The
caller supplies the continuity hypothesis on the chart-trivialised projection. -/

/-- On each chart α, given continuity of the chart-α-trivialised projections of
the tensor sections, the pointwise inner product is continuous in `b` on the
chart's base set. -/
theorem chartLocal_continuous_inner_of_smooth_sections
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (T S : ∀ y : M, Tensor0SSpace s I y) (α : M)
    (hTα : ContinuousOn
      (fun b : M => (Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
          (T b)).compContinuousLinearMap
          (fun _ : Fin s => chartJinv (I := I) (M := M) α b))
      (trivializationAt E (TangentSpace I) α).baseSet)
    (hSα : ContinuousOn
      (fun b : M => (Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
          (S b)).compContinuousLinearMap
          (fun _ : Fin s => chartJinv (I := I) (M := M) α b))
      (trivializationAt E (TangentSpace I) α).baseSet) :
    ContinuousOn
      (fun b : M =>
        tensorInnerPointwise_0s (I := I) (M := M) s g b
          (Tensor0SBundle.Tensor0SSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) (T b))
          (Tensor0SBundle.Tensor0SSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) (S b)))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  -- Apply the bridge identity to convert the LHS to chartTensorInnerPointwise_0s,
  -- then apply the chart-local smoothness lemma.
  have hbridge : ∀ b ∈ (trivializationAt E (TangentSpace I) α).baseSet,
      tensorInnerPointwise_0s (I := I) (M := M) s g b
        (Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) (T b))
        (Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) (S b)) =
      chartTensorInnerPointwise_0s (I := I) (M := M) s g α b
        ((Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
          (T b)).compContinuousLinearMap
          (fun _ : Fin s => chartJinv (I := I) (M := M) α b))
        ((Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
          (S b)).compContinuousLinearMap
          (fun _ : Fin s => chartJinv (I := I) (M := M) α b)) := by
    intro b hb
    exact tensorInnerPointwise_0s_bridge_identity (I := I) (M := M) g α s hb _ _
  refine ContinuousOn.congr ?_ hbridge
  exact chartTensorInnerPointwise_0s_continuousOn_smooth_args
    (I := I) (M := M) g α s _ _ hTα hSα

/-- Global continuity of the pointwise inner product on (0,s) tensor sections.

Given the chart-trivialised projection-continuity hypothesis at every point of
`M` (one chart-α centred at each point), the inner product is globally
continuous. The hypothesis says: for each `α ∈ M`, the chart-α-trivialised
projection of each tensor section is continuous on the chart's base set. -/
theorem _root_.Tensor0SBundle.continuous_inner_of_smooth_sections
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (T S : ∀ y : M, Tensor0SSpace s I y)
    (hT_charts : ∀ α : M, ContinuousOn
      (fun b : M => (Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
          (T b)).compContinuousLinearMap
          (fun _ : Fin s => chartJinv (I := I) (M := M) α b))
      (trivializationAt E (TangentSpace I) α).baseSet)
    (hS_charts : ∀ α : M, ContinuousOn
      (fun b : M => (Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
          (S b)).compContinuousLinearMap
          (fun _ : Fin s => chartJinv (I := I) (M := M) α b))
      (trivializationAt E (TangentSpace I) α).baseSet) :
    Continuous (fun b : M =>
      tensorInnerPointwise_0s (I := I) (M := M) s g b
        (Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) (T b))
        (Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) (S b))) := by
  rw [continuous_iff_continuousAt]
  intro b
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) b).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt _ _ b
  have hOpen : IsOpen (trivializationAt E (TangentSpace I) b).baseSet :=
    (trivializationAt E (TangentSpace I) b).open_baseSet
  have hLocal := chartLocal_continuous_inner_of_smooth_sections
    (I := I) (M := M) g s T S b (hT_charts b) (hS_charts b)
  exact hLocal.continuousAt (hOpen.mem_nhds hb_base)

end Tensor0SRiemannian
end Tensor
end DifferentialGeometry

end
