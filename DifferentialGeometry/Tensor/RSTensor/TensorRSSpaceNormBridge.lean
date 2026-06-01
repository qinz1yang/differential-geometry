import DifferentialGeometry.Tensor.RSTensor.Defs

/-!
# Norm bridge for `TensorRSSpace`

`TensorRSSpace r s I b` is defined as the carrier
`Tensor0SSpace r I b →L[𝕜] Tensor0SSpace s I b` and inherits a `NormedAddCommGroup`
structure by pull-back along `tensorRSSpace_continuousLinearEquiv` from the model fibre
`TensorRSModel r s 𝕜 E`. This file proves that this induced norm equals the operator
norm of the underlying function, computed using the same norms on the domain and
codomain that the carrier already supplies.

Concretely, for any `T : TensorRSSpace r s I b`:
```
‖T‖ = sInf {c : ℝ | 0 ≤ c ∧ ∀ x : Tensor0SSpace r I b, ‖T x‖ ≤ c * ‖x‖}.
```

Note: although the type `Tensor0SSpace r I b →L[𝕜] Tensor0SSpace s I b` is definitionally
equal to `TensorRSSpace r s I b`, Lean's typeclass search does not unify the bundle
topology used by the carrier with the norm topology required by Mathlib's canonical
`ContinuousLinearMap.hasOpNorm` (the two agree propositionally, by
`tensor0SSpace_topology_eq`, but not as instances). We therefore phrase the headline in
terms of the `sInf`-formula directly. Companion lemmas `tensorRSSpace_norm_apply_le`
and `tensorRSSpace_opNorm_le_bound` provide the standard "operator-norm" inequalities.

## Main results

* `tensor0SSpace_continuousLinearEquiv_norm_apply`: the bundle/model equivalence on
  `Tensor0SSpace` preserves norms.
* `tensorRSSpace_norm_eq_carrier_opNorm`: the induced norm on `TensorRSSpace r s I b`
  equals the operator-norm `sInf`-formula on the carrier.
* `tensorRSSpace_norm_apply_le`: `‖T x‖ ≤ ‖T‖ * ‖x‖`.
* `tensorRSSpace_opNorm_le_bound`: any constant `C` satisfying `‖T x‖ ≤ C * ‖x‖` is an
  upper bound on `‖T‖`.
-/

noncomputable section

namespace Tensor0SBundle

open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]
variable {r s : ℕ}

/-! ## Norm preservation by `tensor0SSpace_continuousLinearEquiv`

`tensor0SSpace_continuousLinearEquiv s b` is constructed with `toFun := id` and
`invFun := id`. Both source and target inherit their `NormedAddCommGroup` instances
from the same underlying `ContinuousMultilinearMap`-based bundle fibre (the
`Tensor0SSpace`-level instance delegates to `Bundle.continuousMultilinearMap`, which
itself delegates to the standard `ContinuousMultilinearMap` norm), so the norm is
preserved verbatim. -/

/-- The continuous linear equivalence between a `Tensor0SSpace` fibre and its model
fibre preserves the norm. -/
theorem tensor0SSpace_continuousLinearEquiv_norm_apply (s : ℕ) (b : M)
    (T : Tensor0SSpace s I b) :
    ‖tensor0SSpace_continuousLinearEquiv (𝕜 := 𝕜) (E := E) (I := I) (M := M) s b T‖
      = ‖T‖ := rfl

/-- Norm preservation phrased in the reverse direction. -/
theorem tensor0SSpace_continuousLinearEquiv_symm_norm_apply (s : ℕ) (b : M)
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) :
    ‖(tensor0SSpace_continuousLinearEquiv (𝕜 := 𝕜) (E := E) (I := I)
        (M := M) s b).symm f‖ = ‖f‖ := rfl

/-! ## The induced norm equals the carrier-side operator-norm formula

The norm on `TensorRSSpace r s I b` is by definition the pull-back norm
`‖tensorRSSpace_continuousLinearEquiv r s b T‖`, which is the operator norm of the
*model-side* continuous linear map
`Tensor0SModel r 𝕜 E →L[𝕜] Tensor0SModel s 𝕜 E` obtained by conjugating `T` with the
two `tensor0SSpace_continuousLinearEquiv`s.

Mathlib's operator norm formula is
`‖f‖ = sInf {c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖}`. We prove that the set of admissible
bounds on the model side coincides with the corresponding set on the carrier side, by
translating `x ↔ e_r.symm x` and using norm-preservation. -/

/-- **Headline.** The induced norm on `TensorRSSpace r s I b` equals the
operator-norm `sInf`-formula computed against the norms on the carrier's domain
and codomain. -/
theorem tensorRSSpace_norm_eq_carrier_opNorm {b : M} (T : TensorRSSpace r s I b) :
    ‖T‖ = sInf {c : ℝ | 0 ≤ c ∧
      ∀ x : Tensor0SSpace r I b,
        ‖(T : Tensor0SSpace r I b →L[𝕜] Tensor0SSpace s I b) x‖ ≤ c * ‖x‖} := by
  classical
  -- Step 1. Re-express `‖T‖` via the model-side operator norm.
  have hT_def : ‖T‖
      = ‖tensorRSSpace_continuousLinearEquiv
          (𝕜 := 𝕜) (E := E) (I := I) (M := M) r s b T‖ := rfl
  -- Step 2. The model-side norm unfolds via `arrowCongr`.
  set e_r := tensor0SSpace_continuousLinearEquiv
    (𝕜 := 𝕜) (E := E) (I := I) (M := M) r b with he_r
  set e_s := tensor0SSpace_continuousLinearEquiv
    (𝕜 := 𝕜) (E := E) (I := I) (M := M) s b with he_s
  have hUnfold :
      tensorRSSpace_continuousLinearEquiv (𝕜 := 𝕜) (E := E) (I := I) (M := M) r s b T
        = e_r.arrowCongr e_s
            (T : Tensor0SSpace r I b →L[𝕜] Tensor0SSpace s I b) := rfl
  -- Step 3. The two sInf sets are equal.
  set Tcarrier : Tensor0SSpace r I b →L[𝕜] Tensor0SSpace s I b := T with hTcarrier
  have hSetEq :
      {c : ℝ | 0 ≤ c ∧
          ∀ x : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜,
            ‖e_r.arrowCongr e_s Tcarrier x‖ ≤ c * ‖x‖}
        = {c : ℝ | 0 ≤ c ∧
            ∀ x : Tensor0SSpace r I b, ‖Tcarrier x‖ ≤ c * ‖x‖} := by
    apply Set.eq_of_subset_of_subset
    · rintro c ⟨hc, hbd⟩
      refine ⟨hc, fun y => ?_⟩
      have hx := hbd (e_r y)
      have h1 : e_r.arrowCongr e_s Tcarrier (e_r y) = e_s (Tcarrier y) := by
        rw [ContinuousLinearEquiv.arrowCongr_apply,
            ContinuousLinearEquiv.symm_apply_apply]
      rw [h1] at hx
      have hLHS : ‖e_s (Tcarrier y)‖ = ‖Tcarrier y‖ :=
        tensor0SSpace_continuousLinearEquiv_norm_apply (𝕜 := 𝕜) (E := E)
          (I := I) (M := M) s b (Tcarrier y)
      have hRHS : ‖e_r y‖ = ‖y‖ :=
        tensor0SSpace_continuousLinearEquiv_norm_apply (𝕜 := 𝕜) (E := E)
          (I := I) (M := M) r b y
      rw [hLHS, hRHS] at hx
      exact hx
    · rintro c ⟨hc, hbd⟩
      refine ⟨hc, fun x => ?_⟩
      have hy := hbd (e_r.symm x)
      have h1 : e_r.arrowCongr e_s Tcarrier x = e_s (Tcarrier (e_r.symm x)) := by
        rw [ContinuousLinearEquiv.arrowCongr_apply]
      rw [h1]
      have hLHS : ‖e_s (Tcarrier (e_r.symm x))‖ = ‖Tcarrier (e_r.symm x)‖ :=
        tensor0SSpace_continuousLinearEquiv_norm_apply (𝕜 := 𝕜) (E := E)
          (I := I) (M := M) s b (Tcarrier (e_r.symm x))
      have hRHS : ‖e_r.symm x‖ = ‖x‖ :=
        tensor0SSpace_continuousLinearEquiv_symm_norm_apply (𝕜 := 𝕜) (E := E)
          (I := I) (M := M) r b x
      rw [hLHS, ← hRHS]
      exact hy
  -- Step 4. Combine via the operator-norm definition on the model side.
  have hnorm_def :
      ‖e_r.arrowCongr e_s Tcarrier‖
        = sInf {c : ℝ | 0 ≤ c ∧
            ∀ x : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜,
              ‖e_r.arrowCongr e_s Tcarrier x‖ ≤ c * ‖x‖} :=
    ContinuousLinearMap.norm_def _
  rw [hT_def, hUnfold, hnorm_def]
  exact congrArg sInf hSetEq

/-! ## Standard operator-norm inequalities on `TensorRSSpace`

The carrier `Tensor0SSpace r I b →L[𝕜] Tensor0SSpace s I b` does not directly carry a
`Norm` instance (because the topology used by the carrier is the bundle topology,
which only propositionally agrees with the norm topology that `ContinuousLinearMap`'s
operator norm requires). The lemmas below recover the standard operator-norm
inequalities `‖T x‖ ≤ ‖T‖ * ‖x‖` and `opNorm_le_bound` against the *induced* norm on
`TensorRSSpace`. -/

private lemma _bounds_bddBelow_carrier {b : M} (T : TensorRSSpace r s I b) :
    BddBelow {c : ℝ | 0 ≤ c ∧
      ∀ x : Tensor0SSpace r I b,
        ‖(T : Tensor0SSpace r I b →L[𝕜] Tensor0SSpace s I b) x‖ ≤ c * ‖x‖} :=
  ⟨0, fun _ ⟨hn, _⟩ => hn⟩

/-- Standard operator-norm bound: `‖T x‖ ≤ ‖T‖ * ‖x‖`.

Proof: transport the model-side bound `ContinuousLinearMap.le_opNorm` for
`e_r.arrowCongr e_s T : Tensor0SModel r 𝕜 E →L[𝕜] Tensor0SModel s 𝕜 E` back to the
carrier via norm-preservation of `tensor0SSpace_continuousLinearEquiv` on both sides. -/
theorem tensorRSSpace_norm_apply_le {b : M} (T : TensorRSSpace r s I b)
    (x : Tensor0SSpace r I b) :
    ‖(T : Tensor0SSpace r I b →L[𝕜] Tensor0SSpace s I b) x‖ ≤ ‖T‖ * ‖x‖ := by
  set e_r := tensor0SSpace_continuousLinearEquiv
    (𝕜 := 𝕜) (E := E) (I := I) (M := M) r b with he_r
  set e_s := tensor0SSpace_continuousLinearEquiv
    (𝕜 := 𝕜) (E := E) (I := I) (M := M) s b with he_s
  -- Model-side bound.
  have hbd_model :
      ‖(e_r.arrowCongr e_s
          (T : Tensor0SSpace r I b →L[𝕜] Tensor0SSpace s I b)) (e_r x)‖
        ≤ ‖e_r.arrowCongr e_s
              (T : Tensor0SSpace r I b →L[𝕜] Tensor0SSpace s I b)‖
          * ‖e_r x‖ :=
    ContinuousLinearMap.le_opNorm _ _
  -- Translate using `arrowCongr_apply` and norm-preservation.
  have h1 :
      e_r.arrowCongr e_s
          (T : Tensor0SSpace r I b →L[𝕜] Tensor0SSpace s I b) (e_r x)
        = e_s ((T : Tensor0SSpace r I b →L[𝕜] Tensor0SSpace s I b) x) := by
    rw [ContinuousLinearEquiv.arrowCongr_apply,
        ContinuousLinearEquiv.symm_apply_apply]
    rfl
  have hLHS :
      ‖e_s ((T : Tensor0SSpace r I b →L[𝕜] Tensor0SSpace s I b) x)‖
        = ‖(T : Tensor0SSpace r I b →L[𝕜] Tensor0SSpace s I b) x‖ :=
    tensor0SSpace_continuousLinearEquiv_norm_apply (𝕜 := 𝕜) (E := E)
      (I := I) (M := M) s b _
  have hxNorm : ‖e_r x‖ = ‖x‖ :=
    tensor0SSpace_continuousLinearEquiv_norm_apply (𝕜 := 𝕜) (E := E)
      (I := I) (M := M) r b x
  have hT_norm :
      ‖e_r.arrowCongr e_s
          (T : Tensor0SSpace r I b →L[𝕜] Tensor0SSpace s I b)‖ = ‖T‖ := rfl
  rw [h1, hLHS, hxNorm, hT_norm] at hbd_model
  exact hbd_model

/-- If `C ≥ 0` and `‖T x‖ ≤ C * ‖x‖` for all `x`, then `‖T‖ ≤ C`. -/
theorem tensorRSSpace_opNorm_le_bound {b : M} (T : TensorRSSpace r s I b)
    {C : ℝ} (hCpos : 0 ≤ C)
    (hbd : ∀ x : Tensor0SSpace r I b,
      ‖(T : Tensor0SSpace r I b →L[𝕜] Tensor0SSpace s I b) x‖ ≤ C * ‖x‖) :
    ‖T‖ ≤ C := by
  rw [tensorRSSpace_norm_eq_carrier_opNorm]
  exact csInf_le (_bounds_bddBelow_carrier (𝕜 := 𝕜) (E := E) (I := I) (M := M) T)
    ⟨hCpos, hbd⟩

end Tensor0SBundle

end
