import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivative
import DifferentialGeometry.Tensor.RSTensor.TensorRSSpaceNormBridge
import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-!
# Pointwise operator-norm bound for the chart-frame slot Christoffel corrections

For a smooth Riemannian manifold `(M, g)` with chart base point `α : M`, an
`(r, s)`-tensor section `T`, a tangent vector field `X`, a base point `b : M`,
and a slot index `k : Fin r` (input) or `l : Fin s` (output), this file
bounds the operator norm of the slot Christoffel corrections appearing in
`chartTensorRSCovariantDerivative` by a single Christoffel-derived factor
times the fibre norm `‖T b‖`.

The slot correction at `b` factorises through the chart Levi-Civita parallel
CLM `Φ := chartLeviCivitaParallelCLM g α b X` (which only depends on `X`
through the value `X b`). Define

  `c_Φ b X := max ‖Φ‖ 1 = max ‖chartLeviCivitaParallelCLM g α b X‖ 1`.

For each input slot `k : Fin r`:

  `‖chartTensorRSInputSlotCorrection r s g α T X b k‖ ≤ (c_Φ b X) ^ r · ‖T b‖`.

For each output slot `l : Fin s`:

  `‖chartTensorRSOutputSlotCorrection r s g α T X b l‖ ≤ (c_Φ b X) ^ s · ‖T b‖`.

The bound is **pointwise** in `b` and `X`; no compactness or partition-of-unity
hypothesis is needed. Composed with any uniform bound `‖Φ‖ ≤ C(b) · ‖X b‖` on
a compact set (e.g.
`chartLeviCivitaParallelCLM_general_X_opNorm_isBounded_on_pouTsupport` in the
spectral layer) this immediately yields a uniform op-norm bound for the slot
corrections of the form `(Christoffel constant) · ‖T b‖`.

## Main declarations

* `slotChristoffelCLMFactor` — abbreviation
  `(max ‖chartLeviCivitaParallelCLM g α b X‖ 1) ^ n` for the slot-product
  factor of arity `n`, capturing the slot-CLM contribution.
* `tensorSlotSubstCLM_apply_norm_le` — pointwise factor bound
  `‖tensorSlotSubstCLM n b Φ x‖ ≤ (∏ ‖Φ i‖) · ‖x‖`.
* `tangentSlotCLM_prod_norm_le` — slot-substitution product bound
  `(∏ ‖tangentSlotCLM n k Φ i‖) ≤ (max ‖Φ‖ 1) ^ n`.
* `chartTensorRSInputSlotCorrection_opNorm_le` — the headline input-slot bound.
* `chartTensorRSOutputSlotCorrection_opNorm_le` — the headline output-slot bound.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open Bundle Manifold Set
open scoped Manifold Topology ContDiff BigOperators
open Tensor0SBundle

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- Pointwise upper bound on `tensorSlotSubstCLM` in the model fibre norm.
The argument proceeds in three steps:

1. By definition, `tensorSlotSubstCLM n b Φ x = CLE.symm (compCLML Φ (CLE x))`.
2. The CLE / CLE.symm preserves norms (`tensor0SSpace_continuousLinearEquiv`
   is a norm-preserving identification of the bundle fibre with the model
   fibre), so the LHS norm equals `‖compCLML Φ (CLE x)‖`.
3. `compCLML Φ` is a CLM with op-norm `≤ ∏ ‖Φ i‖` by Mathlib's
   `ContinuousMultilinearMap.norm_compContinuousLinearMapL_le`. -/
lemma tensorSlotSubstCLM_apply_norm_le (n : ℕ) (b : M)
    (Φ : Fin n → (TangentSpace I b →L[ℝ] TangentSpace I b))
    (x : Tensor0SSpace n I b) :
    ‖tensorSlotSubstCLM (I := I) n b Φ x‖ ≤
      (∏ i : Fin n, ‖Φ i‖) * ‖x‖ := by
  classical
  have hsubst_eq :
      tensorSlotSubstCLM (I := I) n b Φ x =
        (tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b).symm
          ((ContinuousMultilinearMap.compContinuousLinearMapL
              (𝕜 := ℝ) (E := fun _ : Fin n => E) (F := ℝ) Φ)
            ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b) x)) := by
    change ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b).symm
          : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ →L[ℝ]
              Tensor0SSpace n I b).comp
        ((tangentCompCLML_E (I := I) (M := M) n b Φ).comp
          ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b)
            : Tensor0SSpace n I b →L[ℝ]
              ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ)) x =
        (tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b).symm
          ((ContinuousMultilinearMap.compContinuousLinearMapL
              (𝕜 := ℝ) (E := fun _ : Fin n => E) (F := ℝ) Φ)
            ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b) x))
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    rfl
  rw [hsubst_eq]
  rw [tensor0SSpace_continuousLinearEquiv_symm_norm_apply (𝕜 := ℝ) (E := E)
      (I := I) (M := M) n b _]
  have hopBound :
      ‖ContinuousMultilinearMap.compContinuousLinearMapL
          (𝕜 := ℝ) (E := fun _ : Fin n => E) (F := ℝ) Φ‖ ≤
        ∏ i : Fin n, ‖Φ i‖ :=
    ContinuousMultilinearMap.norm_compContinuousLinearMapL_le
      (𝕜 := ℝ) (E := fun _ : Fin n => E) ℝ Φ
  have hCLEx_nn :
      0 ≤ ‖(tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b) x‖ :=
    norm_nonneg _
  have hCLM_le :
      ‖(ContinuousMultilinearMap.compContinuousLinearMapL
            (𝕜 := ℝ) (E := fun _ : Fin n => E) (F := ℝ) Φ)
          ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b) x)‖ ≤
        ‖ContinuousMultilinearMap.compContinuousLinearMapL
            (𝕜 := ℝ) (E := fun _ : Fin n => E) (F := ℝ) Φ‖ *
          ‖(tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b) x‖ :=
    ContinuousLinearMap.le_opNorm _ _
  have hCLM_le' :
      ‖(ContinuousMultilinearMap.compContinuousLinearMapL
            (𝕜 := ℝ) (E := fun _ : Fin n => E) (F := ℝ) Φ)
          ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b) x)‖ ≤
        (∏ i : Fin n, ‖Φ i‖) *
          ‖(tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b) x‖ :=
    hCLM_le.trans (mul_le_mul_of_nonneg_right hopBound hCLEx_nn)
  rw [tensor0SSpace_continuousLinearEquiv_norm_apply (𝕜 := ℝ) (E := E)
      (I := I) (M := M) n b x] at hCLM_le'
  exact hCLM_le'

/-- Per-slot bound on `tangentSlotCLM`'s factors: identity at non-substituted
slots (`≤ 1`), the substituted CLM at the substituted slot (`= ‖Φ‖`). -/
lemma tangentSlotCLM_factor_norm_le (n : ℕ) (b : M)
    (k : Fin n) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b)
    (i : Fin n) :
    ‖tangentSlotCLM (I := I) n k Φ i‖ ≤ max ‖Φ‖ 1 := by
  classical
  by_cases hi : i = k
  · rw [hi, tangentSlotCLM_self]
    exact le_max_left _ _
  · rw [tangentSlotCLM_other (I := I) n k Φ hi]
    have h_id : ‖(ContinuousLinearMap.id ℝ (TangentSpace I b))‖ ≤ 1 :=
      ContinuousLinearMap.norm_id_le
    exact h_id.trans (le_max_right _ _)

/-- The product of the per-slot factor norms is dominated by `(max ‖Φ‖ 1) ^ n`.
At the substituted slot the factor norm is `‖Φ‖`, at every other slot it is
`‖id‖ ≤ 1`; we absorb both into the `max`-with-`1` so the bound covers all
cases uniformly. -/
lemma tangentSlotCLM_prod_norm_le (n : ℕ) (b : M)
    (k : Fin n) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b) :
    (∏ i : Fin n, ‖tangentSlotCLM (I := I) n k Φ i‖) ≤
      (max ‖Φ‖ 1) ^ n := by
  classical
  have h_pow : (max ‖Φ‖ 1) ^ n = ∏ _i : Fin n, max ‖Φ‖ 1 := by
    rw [Finset.prod_const]; simp
  rw [h_pow]
  refine Finset.prod_le_prod ?_ ?_
  · intro i _; exact norm_nonneg _
  · intro i _; exact tangentSlotCLM_factor_norm_le (I := I) n b k Φ i

/-- `tensorSlotSubstCLM n b Φ` viewed as an element of `TensorRSSpace n n I b`.

The two types are definitionally equal (`TensorRSSpace n n I b` unfolds to
`Tensor0SSpace n I b →L[ℝ] Tensor0SSpace n I b`); this packaging is purely
for `Norm`-instance access. -/
def tensorSlotSubstCLMRS (n : ℕ) (b : M)
    (Φ : Fin n → (TangentSpace I b →L[ℝ] TangentSpace I b)) :
    TensorRSSpace n n I b :=
  tensorSlotSubstCLM (I := I) n b Φ

@[simp] lemma tensorSlotSubstCLMRS_apply (n : ℕ) (b : M)
    (Φ : Fin n → (TangentSpace I b →L[ℝ] TangentSpace I b))
    (x : Tensor0SSpace n I b) :
    (show Tensor0SSpace n I b →L[ℝ] Tensor0SSpace n I b from
      tensorSlotSubstCLMRS (I := I) n b Φ) x =
      tensorSlotSubstCLM (I := I) n b Φ x := rfl

/-- The product of the slot-CLM factor norms is non-negative. -/
private lemma slotSubstCLM_factor_prod_nonneg (n : ℕ) {b : M}
    (Φ : Fin n → (TangentSpace I b →L[ℝ] TangentSpace I b)) :
    0 ≤ ∏ i : Fin n, ‖Φ i‖ :=
  Finset.prod_nonneg (fun _ _ => norm_nonneg _)

/-- **Operator-norm bound for `tensorSlotSubstCLM`.**

`tensorSlotSubstCLM n b Φ`, packaged as a `TensorRSSpace n n I b` element,
has norm bounded by `∏ ‖Φ i‖`. The bound is the `TensorRSSpace`-level lift
of `tensorSlotSubstCLM_apply_norm_le`. -/
theorem tensorSlotSubstCLM_opNorm_le (n : ℕ) (b : M)
    (Φ : Fin n → (TangentSpace I b →L[ℝ] TangentSpace I b)) :
    ‖tensorSlotSubstCLMRS (I := I) n b Φ‖ ≤ ∏ i : Fin n, ‖Φ i‖ := by
  refine tensorRSSpace_opNorm_le_bound (𝕜 := ℝ) (E := E) (I := I) (M := M)
    (tensorSlotSubstCLMRS (I := I) n b Φ)
    (slotSubstCLM_factor_prod_nonneg (I := I) (M := M) n Φ) ?_
  intro x
  exact tensorSlotSubstCLM_apply_norm_le (I := I) n b Φ x

/-- **Composite op-norm bound for the slot CLM used in the slot Christoffel
corrections.**

`tensorSlotSubstCLM n b (tangentSlotCLM n k Φ)` is the single-slot
substitution CLM appearing inside both `chartTensorRSInputSlotCorrection`
(with `n = r`) and `chartTensorRSOutputSlotCorrection` (with `n = s`). Its
`TensorRSSpace`-norm is bounded by `(max ‖Φ‖ 1) ^ n`, combining the
substitution-CLM op-norm bound with the slot-factor product bound. -/
theorem tensorSlotSubstCLM_tangentSlotCLM_opNorm_le (n : ℕ) (b : M)
    (k : Fin n) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b) :
    ‖tensorSlotSubstCLMRS (I := I) n b
        (tangentSlotCLM (I := I) n k Φ)‖ ≤ (max ‖Φ‖ 1) ^ n :=
  (tensorSlotSubstCLM_opNorm_le (I := I) n b
      (tangentSlotCLM (I := I) n k Φ)).trans
    (tangentSlotCLM_prod_norm_le (I := I) n b k Φ)

/-- **Uniform op-norm bound for the input-slot substitution CLM in terms of
the chart Levi-Civita parallel CLM.**

Specialising `Φ` to `chartLeviCivitaParallelCLM g α b X`, the input-slot
substitution CLM has `TensorRSSpace`-norm bounded by
`(max ‖chartLeviCivitaParallelCLM g α b X‖ 1) ^ r`. Combined with a uniform
bound on `‖chartLeviCivitaParallelCLM g α b X‖` over a compact set this
yields a uniform op-norm bound for the slot CLM on that compact set. -/
theorem tensorSlotSubstCLM_inputSlotChartCLM_opNorm_le (r : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Π b' : M, TangentSpace I b') (b : M) (k : Fin r) :
    ‖tensorSlotSubstCLMRS (I := I) r b
        (tangentSlotCLM (I := I) r k
          (chartLeviCivitaParallelCLM (I := I) g α b X))‖ ≤
      (max ‖chartLeviCivitaParallelCLM (I := I) g α b X‖ 1) ^ r :=
  tensorSlotSubstCLM_tangentSlotCLM_opNorm_le (I := I) r b k _

/-- **Uniform op-norm bound for the output-slot substitution CLM in terms
of the chart Levi-Civita parallel CLM.**

The dual statement of `tensorSlotSubstCLM_inputSlotChartCLM_opNorm_le`, on
the output-side `(0, s)`-tensor space, used inside
`chartTensorRSOutputSlotCorrection`. -/
theorem tensorSlotSubstCLM_outputSlotChartCLM_opNorm_le (s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Π b' : M, TangentSpace I b') (b : M) (l : Fin s) :
    ‖tensorSlotSubstCLMRS (I := I) s b
        (tangentSlotCLM (I := I) s l
          (chartLeviCivitaParallelCLM (I := I) g α b X))‖ ≤
      (max ‖chartLeviCivitaParallelCLM (I := I) g α b X‖ 1) ^ s :=
  tensorSlotSubstCLM_tangentSlotCLM_opNorm_le (I := I) s b l _

/-- **Headline.** Op-norm bound for the `k`-th input-slot Christoffel
correction, by a Christoffel factor `(max ‖chartLeviCivitaParallelCLM g α b X‖ 1) ^ r`
times the fibre norm `‖T b‖`. -/
theorem chartTensorRSInputSlotCorrection_opNorm_le (r s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (k : Fin r) :
    ‖chartTensorRSInputSlotCorrection (I := I) r s g α T X b k‖ ≤
      (max ‖chartLeviCivitaParallelCLM (I := I) g α b X‖ 1) ^ r * ‖T b‖ := by
  classical
  set Φ : TangentSpace I b →L[ℝ] TangentSpace I b :=
    chartLeviCivitaParallelCLM (I := I) g α b X with hΦ_def
  set Ψ : Fin r → (TangentSpace I b →L[ℝ] TangentSpace I b) :=
    tangentSlotCLM (I := I) r k Φ with hΨ_def
  set M_F : ℝ := (max ‖Φ‖ 1) ^ r with hM_F_def
  have hM_F_nn : 0 ≤ M_F := by
    have h1 : 0 ≤ max ‖Φ‖ 1 := le_trans zero_le_one (le_max_right _ _)
    exact pow_nonneg h1 r
  have hΨ_prod_le : (∏ i : Fin r, ‖Ψ i‖) ≤ M_F := by
    rw [hΨ_def, hM_F_def]
    exact tangentSlotCLM_prod_norm_le (I := I) r b k Φ
  have hRHS_nn : 0 ≤ M_F * ‖T b‖ :=
    mul_nonneg hM_F_nn (norm_nonneg _)
  refine tensorRSSpace_opNorm_le_bound (𝕜 := ℝ) (E := E) (I := I) (M := M)
    (chartTensorRSInputSlotCorrection (I := I) r s g α T X b k) hRHS_nn ?_
  intro x
  have hcomp : (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
      chartTensorRSInputSlotCorrection (I := I) r s g α T X b k) x =
      (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
        (tensorSlotSubstCLM (I := I) r b Ψ x) := by
    change ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b).comp
        (tensorSlotSubstCLM (I := I) r b Ψ)) x =
      (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
        (tensorSlotSubstCLM (I := I) r b Ψ x)
    rw [ContinuousLinearMap.comp_apply]
  rw [hcomp]
  have hT_apply :
      ‖(show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          (tensorSlotSubstCLM (I := I) r b Ψ x)‖ ≤
        ‖T b‖ * ‖tensorSlotSubstCLM (I := I) r b Ψ x‖ :=
    tensorRSSpace_norm_apply_le (𝕜 := ℝ) (E := E) (I := I) (M := M) (T b) _
  have hsubst :
      ‖tensorSlotSubstCLM (I := I) r b Ψ x‖ ≤
        (∏ i : Fin r, ‖Ψ i‖) * ‖x‖ :=
    tensorSlotSubstCLM_apply_norm_le (I := I) r b Ψ x
  have hTb_nn : 0 ≤ ‖T b‖ := norm_nonneg _
  have hx_nn : 0 ≤ ‖x‖ := norm_nonneg _
  have h_step1 :
      ‖T b‖ * ‖tensorSlotSubstCLM (I := I) r b Ψ x‖ ≤
        ‖T b‖ * ((∏ i : Fin r, ‖Ψ i‖) * ‖x‖) :=
    mul_le_mul_of_nonneg_left hsubst hTb_nn
  have h_step2 :
      ‖T b‖ * ((∏ i : Fin r, ‖Ψ i‖) * ‖x‖) ≤
        ‖T b‖ * (M_F * ‖x‖) := by
    have h_prod_factor : (∏ i : Fin r, ‖Ψ i‖) * ‖x‖ ≤ M_F * ‖x‖ :=
      mul_le_mul_of_nonneg_right hΨ_prod_le hx_nn
    exact mul_le_mul_of_nonneg_left h_prod_factor hTb_nn
  have h_rearrange : ‖T b‖ * (M_F * ‖x‖) = M_F * ‖T b‖ * ‖x‖ := by ring
  have hChain1 :
      ‖(show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          (tensorSlotSubstCLM (I := I) r b Ψ x)‖ ≤
        ‖T b‖ * ((∏ i : Fin r, ‖Ψ i‖) * ‖x‖) :=
    hT_apply.trans h_step1
  have hChain2 :
      ‖(show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          (tensorSlotSubstCLM (I := I) r b Ψ x)‖ ≤
        ‖T b‖ * (M_F * ‖x‖) :=
    hChain1.trans h_step2
  rw [h_rearrange] at hChain2
  exact hChain2

/-- **Headline.** Op-norm bound for the `l`-th output-slot Christoffel
correction, by a Christoffel factor `(max ‖chartLeviCivitaParallelCLM g α b X‖ 1) ^ s`
times the fibre norm `‖T b‖`. -/
theorem chartTensorRSOutputSlotCorrection_opNorm_le (r s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (l : Fin s) :
    ‖chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l‖ ≤
      (max ‖chartLeviCivitaParallelCLM (I := I) g α b X‖ 1) ^ s * ‖T b‖ := by
  classical
  set Φ : TangentSpace I b →L[ℝ] TangentSpace I b :=
    chartLeviCivitaParallelCLM (I := I) g α b X with hΦ_def
  set Ψ : Fin s → (TangentSpace I b →L[ℝ] TangentSpace I b) :=
    tangentSlotCLM (I := I) s l Φ with hΨ_def
  set M_F : ℝ := (max ‖Φ‖ 1) ^ s with hM_F_def
  have hM_F_nn : 0 ≤ M_F := by
    have h1 : 0 ≤ max ‖Φ‖ 1 := le_trans zero_le_one (le_max_right _ _)
    exact pow_nonneg h1 s
  have hΨ_prod_le : (∏ i : Fin s, ‖Ψ i‖) ≤ M_F := by
    rw [hΨ_def, hM_F_def]
    exact tangentSlotCLM_prod_norm_le (I := I) s b l Φ
  have hRHS_nn : 0 ≤ M_F * ‖T b‖ :=
    mul_nonneg hM_F_nn (norm_nonneg _)
  refine tensorRSSpace_opNorm_le_bound (𝕜 := ℝ) (E := E) (I := I) (M := M)
    (chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l) hRHS_nn ?_
  intro x
  have hcomp : (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
      chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l) x =
      tensorSlotSubstCLM (I := I) s b Ψ
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b) x) := by
    change ((tensorSlotSubstCLM (I := I) s b Ψ).comp
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)) x =
      tensorSlotSubstCLM (I := I) s b Ψ
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b) x)
    rw [ContinuousLinearMap.comp_apply]
  rw [hcomp]
  have hsubst :
      ‖tensorSlotSubstCLM (I := I) s b Ψ
          ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b) x)‖ ≤
        (∏ i : Fin s, ‖Ψ i‖) *
          ‖(show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b) x‖ :=
    tensorSlotSubstCLM_apply_norm_le (I := I) s b Ψ _
  have hT_apply :
      ‖(show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b) x‖ ≤
        ‖T b‖ * ‖x‖ :=
    tensorRSSpace_norm_apply_le (𝕜 := ℝ) (E := E) (I := I) (M := M) (T b) x
  have hTb_nn : 0 ≤ ‖T b‖ := norm_nonneg _
  have hx_nn : 0 ≤ ‖x‖ := norm_nonneg _
  have h_prod_nn : 0 ≤ ∏ i : Fin s, ‖Ψ i‖ :=
    Finset.prod_nonneg (fun i _ => norm_nonneg _)
  have h_step1 :
      (∏ i : Fin s, ‖Ψ i‖) *
        ‖(show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b) x‖ ≤
      (∏ i : Fin s, ‖Ψ i‖) * (‖T b‖ * ‖x‖) :=
    mul_le_mul_of_nonneg_left hT_apply h_prod_nn
  have h_step2 :
      (∏ i : Fin s, ‖Ψ i‖) * (‖T b‖ * ‖x‖) ≤
        M_F * (‖T b‖ * ‖x‖) := by
    have h_inner_nn : 0 ≤ ‖T b‖ * ‖x‖ := mul_nonneg hTb_nn hx_nn
    exact mul_le_mul_of_nonneg_right hΨ_prod_le h_inner_nn
  have h_rearrange : M_F * (‖T b‖ * ‖x‖) = M_F * ‖T b‖ * ‖x‖ := by ring
  have hChain1 :
      ‖tensorSlotSubstCLM (I := I) s b Ψ
          ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b) x)‖ ≤
        (∏ i : Fin s, ‖Ψ i‖) * (‖T b‖ * ‖x‖) :=
    hsubst.trans h_step1
  have hChain2 :
      ‖tensorSlotSubstCLM (I := I) s b Ψ
          ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b) x)‖ ≤
        M_F * (‖T b‖ * ‖x‖) :=
    hChain1.trans h_step2
  rw [h_rearrange] at hChain2
  exact hChain2

end Connection
end Integral
end DifferentialGeometry

end
