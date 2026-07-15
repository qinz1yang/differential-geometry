import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorCurvatureUnitEvalBridge
import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorSlotwiseCurvatureRS
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.RiemannianFiberNormSqRiemannOpHigherRankParseval
import Mathlib.Topology.Order.Compact

/-!
# Contravariant-valence-`r` uniform proportional fibre-norm bound for the tensor curvature operator

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file lifts to a fixed
but generic contravariant valence `r` the uniform proportional curvature-operator fibre bound that
the library carries only at contravariant rank `0`
(`exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional`,
`riemannianFiberNormSq_riemannOp_covGrad_uniform_proportional_bound`).  The result is consumed by the
order-`0` layer of the frame-free pure-Riemann differentiated curvature tower at valence `r`
(`exists_genuinePureRDiffOpRS_orderZero` in `RankRPureRCurvatureTower`).

## The route — single dual-frame curvature term through the two slot-wise branches

The per-point proportional bound `exists_Cx_riemannianFiberNormSq_riemannOp_tensorCovS_le_rs`
supplies, at each `x`, a nonnegative `C_x` with
`rfns(R_x(v, w) T) ≤ C_x · g(v, v) · g(w, w) · rfns(T)`, but its constant
`C_x = ∑_{i,j,K,J} rfns(R_x(e_i, e_j)(dualTensorFrameRS g x r s e K J))` is built from the
pointwise `stdOrthonormalBasis` frame, which is **not continuous** in `x` — so the per-point constant
cannot be supremised directly (exactly as documented at rank `0` in `UniformProportionalCurvatureSup`).

The correct route is the **uniform single dual-frame curvature term bound**: a single nonnegative
constant `K`, independent of the base point, the `g`-orthonormal frame, and the frame indices,
bounding one dual-frame curvature term
`rfns(R_x(e_i, e_j)(dualTensorFrameRS g x r s e K J))`.  Its Parseval components are the
unit-evaluations `toModel ((R^{(r,s)}_x(e_i, e_j) D_{K,J})(ω^{K'})) (e ∘ J')`, each of which the
rank-generic slot-wise curvature formula `riemannSec_tensorCov_apply_eval` splits into a covariant
`(0, s)`-tensor branch and a contravariant `(0, r)`-tensor branch.  Reading both branches at the
coframe tensor and bounding each by the proven `(0, t)` coframe-curvature magnitude bound
`abs_toModel_riemannOp_tensor0SCov_coframeS_le` — which in turn is controlled by the valence-free
Levi-Civita base-curvature `g`-norm bound `exists_uniform_riemannOp_LeviCivita_gNorm_bound` (`Kbase`)
— gives a frame-and-index-uniform component bound.  Summing the finitely-many squared components
(`(finrank E)^(r + s)` of them) bounds the single term; multiplying by the dual-frame count
(`(finrank E)^(r + s + 2)` terms) bounds the dual-frame curvature energy, hence (through the
`(v, w)`-factorisation `exists_Cx_riemannianFiberNormSq_riemannOp_tensorCovS_le_rs` re-run with the
uniformised energy) the proportional bound at every base point.

## Main results

* `riemannOp_tensorCovRS_apply_eval` — the point-level slot-wise curvature formula: the
  `(r, s)`-tensor curvature applied to an `(r, s)`-tensor `T`, evaluated on a `(0, r)`-tensor `Y₀`
  and read on a covariant tuple, splits into the covariant `(0, s)`-tensor curvature on `T(Y₀)` minus
  the value of `T` on the contravariant `(0, r)`-tensor curvature of `Y₀`.
* `riemannianFiberNormSq_riemannOp_tensorCovRS_dualTensorFrameRS_le` — the per-point single
  dual-frame curvature term bound.
* `exists_uniform_riemannOp_tensorCovRS_dualFrameEnergy_const` — the uniform dual-frame curvature
  energy constant.
* `exists_uniform_riemannianFiberNormSq_riemannOp_tensorCovRS_proportional` — the headline
  base-point-uniform proportional curvature-operator fibre bound at valence `(r, s)`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open Tensor0SBundle Tensor0SNabla TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

-- File-local instances ensuring computable typeclass resolution finds the model normed
-- structures (the bundle-level instances are noncomputable).
private instance tensor0SModelNormedSpace_local2 {s : ℕ} :
    NormedSpace ℝ (Tensor0SModel s ℝ E) :=
  Tensor0SBundle.tensor0SModel_normedSpace s

private instance tensorRSModelFiniteDimensional_local2 {r s : ℕ} :
    FiniteDimensional ℝ (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModel_finiteDimensional r s

private instance tensor0SModelFiniteDimensional_local2 {s : ℕ} :
    FiniteDimensional ℝ (Tensor0SModel s ℝ E) :=
  continuousMultilinearMap_finiteDimensional s

/-- Non-negativity of `g.inner x v v`. -/
private lemma metric_inner_self_nonneg2 (g : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) : 0 ≤ g.inner x v v := by
  rcases eq_or_ne v 0 with hv0 | hv0
  · rw [hv0]; simp
  · exact (g.pos x v hv0).le

/-- **A smooth global `(r, s)`-tensor section through a prescribed fibre value.** For any
`(r, s)`-tensor `T₀` at `x`, there is a smooth global `(r, s)`-tensor section `A` with `A x = T₀`. -/
private lemma exists_smooth_tensorRS_section_eq (r s : ℕ) (x : M) (T₀ : TensorRSSpace r s I x) :
    ∃ A : Π b : M, TensorRSSpace r s I b, A x = T₀ ∧
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun b => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) b (A b)) := by
  letI : TopologicalSpace (TotalSpace (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y)) := tensorRSBundle_topology r s
  letI : FiberBundle (TensorRSModel r s ℝ E) (fun y : M => TensorRSSpace r s I y) :=
    tensorRSBundle_fiber r s
  letI : VectorBundle ℝ (TensorRSModel r s ℝ E) (fun y : M => TensorRSSpace r s I y) :=
    tensorRSBundle_vector r s
  letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) I := tensorRSBundle_smooth ∞ r s
  exact ⟨smoothExtensionFiber (I := I) (F := TensorRSModel r s ℝ E)
      (V := fun b => TensorRSSpace r s I b) x T₀,
    smoothExtensionFiber_eq (I := I) (F := TensorRSModel r s ℝ E)
      (V := fun b => TensorRSSpace r s I b) x T₀,
    smoothExtensionFiber_contMDiff (I := I) (F := TensorRSModel r s ℝ E)
      (V := fun b => TensorRSSpace r s I b) x T₀⟩

/-- **A smooth global `(0, r)`-tensor section through a prescribed fibre value.** For any
`(0, r)`-tensor `Y₀` at `x`, there is a smooth global `(0, r)`-tensor section `A` with `A x = Y₀`. -/
private lemma exists_smooth_tensor0S_section_eq2 (r : ℕ) (x : M) (Y₀ : Tensor0SSpace r I x) :
    ∃ A : Π b : M, Tensor0SSpace r I b, A x = Y₀ ∧
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
        (fun b => TotalSpace.mk' (Tensor0SModel r ℝ E)
          (E := fun z : M => Tensor0SSpace r I z) b (A b)) := by
  letI : TopologicalSpace (TotalSpace (Tensor0SModel r ℝ E) (fun y : M => Tensor0SSpace r I y)) :=
    tensor0SBundle_topology r
  letI : FiberBundle (Tensor0SModel r ℝ E) (fun y : M => Tensor0SSpace r I y) := tensor0SBundle_fiber r
  letI : VectorBundle ℝ (Tensor0SModel r ℝ E) (fun y : M => Tensor0SSpace r I y) :=
    tensor0SBundle_vector r
  letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) I := tensor0SBundle_smooth ∞ r
  exact ⟨smoothExtensionFiber (I := I) (F := Tensor0SModel r ℝ E)
      (V := fun b => Tensor0SSpace r I b) x Y₀,
    smoothExtensionFiber_eq (I := I) (F := Tensor0SModel r ℝ E)
      (V := fun b => Tensor0SSpace r I b) x Y₀,
    smoothExtensionFiber_contMDiff (I := I) (F := Tensor0SModel r ℝ E)
      (V := fun b => Tensor0SSpace r I b) x Y₀⟩

/-- **Point-level slot-wise curvature formula for the `(r, s)`-tensor connection.** For tangent
vectors `v, w`, an `(r, s)`-tensor `T`, a `(0, r)`-tensor `Y₀`, and a covariant tuple
`u : Fin s → T_x M`, the bundled `(r, s)`-tensor curvature `R^{(r,s)} = riemannOp (tensorCov g r s)`
applied to `T`, evaluated on `Y₀`, and read on `u`, decomposes as

```
toModel ((R^{(r,s)}_x(v, w) T)(Y₀)) u
  = toModel (R^{(0,s)}_x(v, w) (T(Y₀))) u            -- covariant slots
    − toModel (T (R^{(0,r)}_x(v, w) Y₀)) u            -- contravariant slots (opposite sign)
```

where `R^{(0,s)} = riemannOp (tensor0SCovariantDerivative s …)` and
`R^{(0,r)} = riemannOp (tensor0SCovariantDerivative r …)`. This is the point-level form of the
section-level rank-generic slot-wise curvature formula `riemannSec_tensorCov_apply_eval`: the LHS and
the two RHS curvatures all become section-level `riemannSec`s through `riemannOp_apply_smooth` on
smooth extensions, and the displayed identity is the section-level formula read fibrewise. -/
theorem riemannOp_tensorCovRS_apply_eval
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (v w : TangentSpace I x)
    (T : TensorRSSpace r s I x) (Y₀ : Tensor0SSpace r I x) (u : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
            riemannOp (tensorCov (I := I) g r s) x v w T) Y₀) u =
      Tensor0SSpace.toModel
          (riemannOp (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) x v w
            ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T) Y₀)) u -
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T)
            (riemannOp (tensor0SCovariantDerivative I M r (LeviCivita (I := I) g)) x v w Y₀)) u := by
  classical

  letI : TopologicalSpace (TotalSpace (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y)) := tensor0SBundle_topology r
  letI : FiberBundle (Tensor0SModel r ℝ E) (fun y : M => Tensor0SSpace r I y) :=
    tensor0SBundle_fiber r
  letI : VectorBundle ℝ (Tensor0SModel r ℝ E) (fun y : M => Tensor0SSpace r I y) :=
    tensor0SBundle_vector r
  letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) I := tensor0SBundle_smooth ∞ r
  letI : TopologicalSpace (TotalSpace (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y)) := tensor0SBundle_topology s
  letI : FiberBundle (Tensor0SModel s ℝ E) (fun y : M => Tensor0SSpace s I y) :=
    tensor0SBundle_fiber s
  letI : VectorBundle ℝ (Tensor0SModel s ℝ E) (fun y : M => Tensor0SSpace s I y) :=
    tensor0SBundle_vector s
  letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) I := tensor0SBundle_smooth ∞ s
  letI : TopologicalSpace (TotalSpace (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y)) := tensorRSBundle_topology r s
  letI : FiberBundle (TensorRSModel r s ℝ E) (fun y : M => TensorRSSpace r s I y) :=
    tensorRSBundle_fiber r s
  letI : VectorBundle ℝ (TensorRSModel r s ℝ E) (fun y : M => TensorRSSpace r s I y) :=
    tensorRSBundle_vector r s
  letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) I := tensorRSBundle_smooth ∞ r s

  set X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent_contMDiff (I := I) x v) with hX_def
  set W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x w)
      (smoothExtensionTangent_contMDiff (I := I) x w) with hW_def
  have hXx : (X : Π b : M, TangentSpace I b) x = v := smoothExtensionTangent_eq (I := I) x v
  have hWx : (W : Π b : M, TangentSpace I b) x = w := smoothExtensionTangent_eq (I := I) x w
  have hX_smooth := smoothExtensionTangent_contMDiff (I := I) x v
  have hW_smooth := smoothExtensionTangent_contMDiff (I := I) x w

  obtain ⟨A, hAx, hA_smooth⟩ := exists_smooth_tensorRS_section_eq (I := I) (M := M) r s x T
  set τ : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯ :=
    ContMDiffSection.mk A hA_smooth with hτ_def

  obtain ⟨B, hBx, hB_smooth⟩ := exists_smooth_tensor0S_section_eq2 (I := I) (M := M) r x Y₀
  set Y : Cₛ^∞⟮I; Tensor0SModel r ℝ E, (fun x : M => Tensor0SSpace r I x)⟯ :=
    ContMDiffSection.mk B hB_smooth with hY_def
  have hτx : (τ : Π b : M, TensorRSSpace r s I b) x = T := hAx
  have hYx : (Y : Π b : M, Tensor0SSpace r I b) x = Y₀ := hBx

  have hkey := riemannSec_tensorCov_apply_eval (I := I) (M := M) g r s X W τ Y x u

  have hLHS : (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        riemannOp (tensorCov (I := I) g r s) x v w T) Y₀ =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        riemannSec (tensorCov (I := I) g r s) (fun b => X b) (fun b => W b)
          (fun b => τ b) x) (Y x) := by
    rw [hYx]
    congr 1
    rw [← hXx, ← hWx, ← hτx]
    exact riemannOp_apply_smooth (cov := tensorCov (I := I) g r s) hX_smooth hW_smooth hA_smooth

  have hpaired_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (T% (fun b : M => (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from τ b) (Y b))) := by
    have hϕ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E)) ∞
        (fun b : M => TotalSpace.mk' (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E)
          (E := fun y : M => Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y) b
          (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from A b)) := hA_smooth
    exact ContMDiff.clm_bundle_apply (b := id) hϕ hB_smooth
  have hCov : riemannSec (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
        (fun b => X b) (fun b => W b)
        (fun b => (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from τ b) (Y b)) x =
      riemannOp (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) x v w
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T) Y₀) := by
    rw [riemannSec_eq_riemannOp_smooth
      (cov := tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
      (X := fun b => X b) (Y := fun b => W b)
      (Z := fun b => (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from τ b) (Y b))
      hX_smooth hW_smooth hpaired_smooth]
    rw [hXx, hWx, hτx, hYx]

  have hContra : riemannSec (tensor0SCovariantDerivative I M r (LeviCivita (I := I) g))
        (fun b => X b) (fun b => W b) (fun b => Y b) x =
      riemannOp (tensor0SCovariantDerivative I M r (LeviCivita (I := I) g)) x v w Y₀ := by
    rw [riemannSec_eq_riemannOp_smooth
      (cov := tensor0SCovariantDerivative I M r (LeviCivita (I := I) g))
      (X := fun b => X b) (Y := fun b => W b) (Z := fun b => Y b)
      hX_smooth hW_smooth hB_smooth]
    rw [hXx, hWx, hYx]

  rw [hLHS, hkey, hCov, hContra, hτx]

end Connection
end Integral
end DifferentialGeometry

end
