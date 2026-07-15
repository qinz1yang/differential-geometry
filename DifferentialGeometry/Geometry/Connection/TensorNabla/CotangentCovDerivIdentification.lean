import DifferentialGeometry.Geometry.Connection.TensorNabla.CotangentExtension
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradParallelNaturality
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradCovDerivCommutation
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorMetricCompatible
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.CotangentRiemannian
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.CovDerivPointwise

/-!
# Identification of the cotangent-extension and bundled `(0,1)`-tensor covariant derivatives

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product space `E`,
there are two a-priori distinct Lean realizations of the Levi-Civita covariant derivative of a
covector field:

* `cotangentCov (LeviCivita g)` — the cotangent extension of the Levi-Civita connection on
  `T*M`, built by Leibniz over the canonical pairing
  `(∇_v θ)(w) = v(θ(w)) − θ(∇_v w)` (`CotangentExtension.lean`); and
* `tensorCovDerivAt g 0 1` — the bundled `(0, 1)`-tensor covariant derivative, a value in the
  Hom-bundle `Hom(Tensor0SSpace 0, Tensor0SSpace 1)` (`CovDerivPointwise.lean`), read on the
  unit `(0, 0)`-tensor section to recover a `(0, 1)`-tensor (covector) value.

Both compute the same `∇^g θ`. This file proves the identification, connecting the
`cotangentCov`/`cotangentScalar` calculus to the `tensorCovDerivAt`/`tensor0SCovariantDerivative`
calculus.

## Main theorem

* `cotangentCov_eq_tensorCovDerivAt_ccTensor01` — for a smooth covector field `θ` that is the
  realization (`cotangentToCLM`) of the unit-evaluation of a smooth compactly-supported
  `(0, 1)`-tensor `σ`, the cotangent-extension covariant derivative of `θ` equals the bundled
  `(0, 1)`-tensor covariant derivative of `σ`, both read on a tangent vector:
  `cotangentCov (LeviCivita g) θ x v w
     = cotangentToCLM ((tensorCovDerivAt g 0 1 σ x v) (unitZeroSec x)) w`.
-/

noncomputable section

open Bundle Manifold Set Filter FiberBundle Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open Tensor0SNabla
open TensorRSNabla
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The realized covector field of a smooth `(0, 1)`-tensor `σ`: the unit-evaluation
`σ(·)(unit) : Tensor0SSpace 1` read through `cotangentToCLM` as a continuous functional
`TangentSpace I b →L[ℝ] ℝ`. -/
def ccTensor01Covec (g : SmoothRiemannianMetric I M) (σ : SmoothCcTensor g 0 1) :
    Π b : M, TangentSpace I b →L[ℝ] ℝ :=
  fun b => cotangentToCLM (I := I)
    (unitEvalSection (I := I) (M := M) g 1 σ b)

/-- The unit-evaluation of the bundled `(0, 1)`-tensor covariant derivative reduces to the
abstract `(0, 1)`-tensor covariant derivative of the unit-evaluated section, since the unit
`(0, 0)`-tensor is `∇`-parallel. -/
lemma tensorCovDerivAt_unitEval
    (g : SmoothRiemannianMetric I M) (σ : SmoothCcTensor g 0 1)
    (x : M) (v : TangentSpace I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
        tensorRSCovariantDerivative I M 0 1 (LeviCivita (I := I) g)
          (fun y : M => σ.toSection y) x v) (unitZeroSec (I := I) (M := M) x) =
      tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g)
        (fun y : M =>
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 1 I y from
            σ.toSection y) (unitZeroSec (I := I) (M := M) y))
        x v := by
  classical
  have happ := tensorRSCovariantDerivative_apply (I := I) (M := M) 0 1
    (LeviCivita (I := I) g) σ.toSection (unitZeroSec (I := I) (M := M)) x v
  refine happ.trans ?_
  refine sub_eq_self.mpr ?_
  refine (congrArg (σ.toSection x) ?_).trans (map_zero _)
  exact tensor0SCovariantDerivative_unitZero_eq_zero (I := I) (M := M)
    (LeviCivita (I := I) g) x v

/-- The abstract `(0, 1)`-tensor covariant derivative of a covector section `α`, read through
`cotangentToCLM` on a tangent vector `w` (extended to a smooth field `Y` with `Y x = w`), is the
cotangent-extension Leibniz defect `cotangentScalar`: `v(θ(Y)) − θ(∇_v Y)`. This is the
unit-evaluation `(s = 0)` instance of the slot-`0` covariant Leibniz peel
`tensor0SCovariantDerivative_succ_consEval_peel`. -/
lemma tensor0SCovariantDerivative_one_cotangentToCLM
    (g : SmoothRiemannianMetric I M)
    (α : Π b : M, Tensor0SSpace 1 I b) {x : M}
    (hα : TensorSectionMDiffAt (I := I) 1 α x)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (v : TangentSpace I x) :
    cotangentToCLM (I := I)
        (tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g) α x v) (Y x) =
      extDerivFun (I := I) (fun b : M => cotangentToCLM (I := I) (α b) (Y b)) x v -
        cotangentToCLM (I := I) (α x) ((LeviCivita (I := I) g).toFun (fun y => Y y) x v) := by
  classical
  have hCLM : ∀ {b : M} (β : Tensor0SSpace 1 I b) (u : TangentSpace I b),
      cotangentToCLM (I := I) β u = Tensor0SSpace.toModel β (fun _ : Fin 1 => u) := by
    intro b β u
    have h := cotangentToDual_apply (I := I) β u
    rw [show cotangentToDual (I := I) β u = cotangentToCLM (I := I) β u from rfl] at h
    rw [h]; rfl
  have hconsEq : ∀ {b : M} (u : TangentSpace I b),
      (Fin.cons u (fun i : Fin 0 => i.elim0) : Fin 1 → TangentSpace I b) =
      (fun _ : Fin 1 => u) := by
    intro b u; funext i; fin_cases i; rfl
  have hpeel := tensor0SCovariantDerivative_succ_consEval_peel (I := I) (M := M)
    g 0 α hα Y v (fun i : Fin 0 => i.elim0)
  rw [hCLM, ← hconsEq (Y x)]
  refine hpeel.trans ?_
  congr 1
  · -- the `(0, 0)` derivative term is the exterior derivative of the curried pairing
    rw [tensor0SCovariantDerivative_zero_toModel_apply (I := I) (M := M) g
      (fun y : M => curriedSection I M α y (Y y)) x v]
    have hscalar : Tensor0SNabla.scalarFn I M
        (fun y : M => curriedSection I M α y (Y y)) =
        (fun b : M => cotangentToCLM (I := I) (α b) (Y b)) := by
      funext b
      rw [scalarFn_eq_toModel_elim0 (I := I) (M := M)
        (fun y : M => curriedSection I M α y (Y y)) b]
      rw [Tensor0SNabla.curriedSection_apply (I := I) (M := M) α b]
      rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (T := α b) (v0 := Y b) (vs := fun i : Fin 0 => i.elim0)]
      rw [hCLM]
      congr 1
      exact hconsEq (Y b)
    rw [hscalar]
    rfl
  · -- the Christoffel-correction term matches `cotangentToCLM (α x) (∇_v Y)`
    rw [hCLM]
    congr 1
    exact hconsEq ((LeviCivita (I := I) g).toFun (fun y => Y y) x v)

/-- **The cotangent-extension covariant derivative equals the bundled `(0, 1)`-tensor
covariant derivative.** For a smooth compactly-supported `(0, 1)`-tensor `σ`, with `hθ` the
manifold-differentiability of its realized covector field `ccTensor01Covec g σ` (the
unit-evaluation of `σ` read through `cotangentToCLM`) and `hUz` the manifold-differentiability
of the unit-evaluated `(0, 1)`-tensor section `unitEvalSection g 1 σ` (both genuine smoothness
preconditions on the `σ`-data at `x`), the cotangent-extension covariant derivative
`cotangentCov (LeviCivita g)` of that covector field, read on a direction `v` and a tangent
vector `w`, equals the bundled `(0, 1)`-tensor covariant derivative `tensorCovDerivAt g 0 1 σ`
read on the unit `(0, 0)`-tensor and then through `cotangentToCLM` on `w`. Both compute `∇^g`
on the same covector. -/
theorem cotangentCov_eq_tensorCovDerivAt_ccTensor01
    (g : SmoothRiemannianMetric I M) (σ : SmoothCcTensor g 0 1) {x : M}
    (hθ : MDiffAtCotangent (ccTensor01Covec g σ) x)
    (hUz : TensorSectionMDiffAt (I := I) 1 (unitEvalSection (I := I) (M := M) g 1 σ) x)
    (v w : TangentSpace I x) :
    cotangentCov (LeviCivita (I := I) g) (ccTensor01Covec g σ) x v w =
      cotangentToCLM (I := I)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
            tensorCovDerivAt g 0 1 σ x v) (unitZeroSec (I := I) (M := M) x)) w := by
  classical
  obtain ⟨X, hXx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
  obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x w
  have hXmd : MDiffAt (T% (fun b : M => X b)) x :=
    X.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hYmd : MDiffAt (T% (fun b : M => Y b)) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)

  have hcov : cotangentCov (LeviCivita (I := I) g) (ccTensor01Covec g σ) x v w =
      cotangentScalar ((LeviCivita (I := I) g).toFun) (ccTensor01Covec g σ) x
        (fun b : M => X b) (fun b : M => Y b) := by
    have hco : cotangentCov (LeviCivita (I := I) g) (ccTensor01Covec g σ) x v w =
        cotangentCovAt (LeviCivita (I := I) g) (ccTensor01Covec g σ) x v w := by
      rw [cotangentCov_toFun, cotangentCovFun_apply]
    rw [hco, ← hXx, ← hYx]
    exact cotangentCovAt_apply_of_diff (LeviCivita (I := I) g) hθ hXmd hYmd
  rw [hcov, cotangentScalar_def]
  simp only []
  rw [hXx]

  have hpair := tensor0SCovariantDerivative_one_cotangentToCLM (I := I) (M := M)
    g (unitEvalSection (I := I) (M := M) g 1 σ) hUz Y v

  have hθeq : (fun b : M => ccTensor01Covec g σ b (Y b)) =
      (fun b : M => cotangentToCLM (I := I)
        (unitEvalSection (I := I) (M := M) g 1 σ b) (Y b)) := rfl
  rw [hθeq]
  rw [show (ccTensor01Covec g σ x)
        ((LeviCivita (I := I) g).toFun (fun b : M => Y b) x v) =
      cotangentToCLM (I := I) (unitEvalSection (I := I) (M := M) g 1 σ x)
        ((LeviCivita (I := I) g).toFun (fun y => Y y) x v) from rfl]
  rw [← hpair]

  rw [← hYx]
  congr 2
  rw [tensorCovDerivAt_def]
  exact (tensorCovDerivAt_unitEval (I := I) (M := M) g σ x v).symm

end Connection
end Integral
end DifferentialGeometry
