import DifferentialGeometry.Integral.Connection.CovGradParallelNaturality

/-!
# Global agreement of the `(0, s)`-tensor covariant derivative with the `(0, s)`-rank
`(r, s)`-tensor covariant derivative

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product
space `E`, there are two a-priori distinct covariant derivatives that both deserve
the name "the Levi-Civita covariant derivative on `(0, s)`-tensors":

* the **abstract recursive** one,
  `Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita g)`, acting on the
  `(0, s)`-tensor bundle `fun x => Tensor0SSpace s I x` and built by recursion on `s`
  through the Hom-bundle covariant derivative;
* the **`(r, s)`-specialisation** at `r = 0`,
  `TensorRSNabla.tensorRSCovariantDerivative I M 0 s (LeviCivita g)`, acting on the
  `(r, s)`-tensor bundle `fun x => TensorRSSpace 0 s I x = Tensor0SSpace 0 I x →L[ℝ]
  Tensor0SSpace s I x`, built as the Hom-bundle covariant derivative from the `(0, 0)`-
  and `(0, s)`-tensor covariant derivatives.

These live in **different bundles**: `Tensor0SSpace s I x` versus
`Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x`. They are identified by the canonical
fibrewise continuous-linear equivalence "evaluate at the unit `(0, 0)`-tensor"
(equivalently, `Tensor0SSpace 0 I x ≃L[ℝ] ℝ` makes `Hom(ℝ, V) ≃L V`).

This file proves the two derivatives **agree globally** (as section identities at
every point and in every direction), once transported along that identification. The
proof is pure locality of the product rule against the `∇`-parallel unit
`(0, 0)`-section — it needs no partition of unity, no chart-good-set restriction, and
holds for an **arbitrary `s`** and an **arbitrary raw `(0, s)`-tensor section**.

## Main declarations

* `tensorRSCovariantDerivative_zeroS_unit_eval` — for any smooth `Cₛ^∞` `(0, s)`-rank
  `(r = 0, s)`-tensor section `σ`, the unit-evaluation of the directional `(r, s)`
  covariant derivative equals the abstract `(0, s)` covariant derivative of the
  unit-evaluated section:
  `(∇^{(0,s)RS}_v σ)(x)(unit) = (∇^{(0,s)abs}_v (y ↦ σ y (unit)))(x)`.
  This is the generalisation, to arbitrary `s`, of the previously committed `s = 3`
  intertwining `covDeriv_unit_eval_eq`.

* `unitScalarRSLift` — the canonical fibrewise lift of an abstract `(0, s)`-tensor to a
  `(0, s)`-rank `(r = 0, s)`-tensor (the `smulRight` of the scalar-reader CLE). It is a
  smooth section whenever the input is, and evaluates at the unit `(0, 0)`-tensor back
  to the original value (`unitScalarRSLift_apply_unit`).

* `tensor0SCovariantDerivative_eq_tensorRSCovariantDerivative` — the **headline global
  agreement**: for any smooth `Cₛ^∞` abstract `(0, s)`-tensor section `S`, the abstract
  `(0, s)` covariant derivative equals the `(r = 0, s)` covariant derivative of the
  lifted section, read back through the unit:
  `(∇^{(0,s)abs}_v S)(x) = (∇^{(0,s)RS}_v (lift S))(x)(unit)`.

## Sign / convention

The covariant gradient curries the new tangent-direction slot as the leftmost
covariant slot, matching the rest of the connection layer. Mathlib's argument
convention `cov.toFun σ x v ≅ (∇_v σ)(x)` is used throughout.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SNabla
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **Unit-evaluation commutes with the `(0, s)`-rank covariant derivative.** For an
arbitrary smooth `Cₛ^∞` `(r = 0, s)`-tensor section `σ` and tangent vector `v`, the
directional `(0, s)`-rank covariant derivative of `σ`, applied to the unit
`(0, 0)`-tensor, equals the abstract `(0, s)`-tensor covariant derivative of the
unit-evaluated section `y ↦ σ y (unit)`:
```
(∇^{(0,s)RS}_v σ)(x)(unit) = (∇^{(0,s)abs}_v (y ↦ σ y (unit)))(x).
```
The product rule against the parallel unit `(0, 0)`-section has no correction term.
This generalises the previously committed `s = 3` intertwining `covDeriv_unit_eval_eq`
to an arbitrary rank `s`. -/
theorem tensorRSCovariantDerivative_zeroS_unit_eval
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (σ : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun y : M => TensorRSSpace 0 s I y)⟯)
    (x : M) (v : TangentSpace I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)
          (fun y : M => σ y) x v)
        (unitZeroSec (I := I) (M := M) x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
        (fun y : M =>
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from σ y)
            (unitZeroSec (I := I) (M := M) y))
        x v := by
  classical
  rw [tensorRSCovariantDerivative_apply (I := I) (M := M) 0 s
    (LeviCivita (I := I) g) σ (unitZeroSec (I := I) (M := M)) x v]
  rw [show (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
        (fun y : M => unitZeroSec (I := I) (M := M) y) x v) = 0 from
    tensor0SCovariantDerivative_unitZero_eq_zero (I := I) (M := M)
      (LeviCivita (I := I) g) x v]
  rw [map_zero, sub_zero]

/-- The canonical fibrewise lift of an abstract `(0, s)`-tensor `T : Tensor0SSpace s I x`
to a `(0, s)`-rank `(r = 0, s)`-tensor `TensorRSSpace 0 s I x = Tensor0SSpace 0 I x →L[ℝ]
Tensor0SSpace s I x`: the `(0, 0)`-input is read to a scalar via `tensor0Iso` and used to
rescale `T`. -/
noncomputable def unitScalarRSLift {s : ℕ} (x : M) (T : Tensor0SSpace s I x) :
    TensorRSSpace 0 s I x :=
  TensorRSSpace.ofCLM
    (ContinuousLinearMap.smulRight
      (tensor0Iso (I := I) M x).toContinuousLinearMap T)

/-- Pointwise evaluation of `unitScalarRSLift` on a `(0, 0)`-input `D`: the result is the
scalar `tensor0Iso x D` rescaling `T`. -/
@[simp] theorem unitScalarRSLift_apply {s : ℕ} (x : M) (T : Tensor0SSpace s I x)
    (D : Tensor0SSpace 0 I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        unitScalarRSLift (I := I) (M := M) x T) D =
      (tensor0Iso (I := I) M x D) • T := by
  rfl

/-- The lift evaluated at the unit `(0, 0)`-tensor returns `T`: `tensor0Iso x (unit) = 1`,
so `unitScalarRSLift x T (unit) = 1 • T = T`. -/
@[simp] theorem unitScalarRSLift_apply_unit {s : ℕ} (x : M) (T : Tensor0SSpace s I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        unitScalarRSLift (I := I) (M := M) x T)
        (unitZeroSec (I := I) (M := M) x) = T := by
  rw [unitScalarRSLift_apply]
  have hscalar : tensor0Iso (I := I) M x (unitZeroSec (I := I) (M := M) x) = (1 : ℝ) := by
    have h := scalarFn_unitZero (I := I) (M := M)
    have := congrFun h x
    simpa [scalarFn_apply, unitZeroSec_apply] using this
  rw [hscalar, one_smul]

/-- The fibrewise lift of a section, `y ↦ unitScalarRSLift y (S y)`. -/
noncomputable def unitScalarRSLiftSection {s : ℕ} (S : Π y : M, Tensor0SSpace s I y) :
    Π y : M, TensorRSSpace 0 s I y :=
  fun y => unitScalarRSLift (I := I) (M := M) y (S y)

@[simp] theorem unitScalarRSLiftSection_apply {s : ℕ}
    (S : Π y : M, Tensor0SSpace s I y) (y : M) :
    unitScalarRSLiftSection (I := I) (M := M) S y =
      unitScalarRSLift (I := I) (M := M) y (S y) := rfl

/-- The unit-evaluated lifted section recovers the original abstract section. -/
@[simp] theorem unitScalarRSLiftSection_apply_unit {s : ℕ}
    (S : Π y : M, Tensor0SSpace s I y) (y : M) :
    (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
        unitScalarRSLiftSection (I := I) (M := M) S y)
        (unitZeroSec (I := I) (M := M) y) = S y := by
  rw [unitScalarRSLiftSection_apply, unitScalarRSLift_apply_unit]

/-- Applying the lifted section at a `(0, 0)`-input `Y y` gives the scalar
`scalarFn Y y` rescaling `S y`. This is the per-input identity feeding the
smoothness bridge. -/
theorem unitScalarRSLiftSection_apply_at_section {s : ℕ}
    (S : Π y : M, Tensor0SSpace s I y)
    (Y : Π y : M, Tensor0SSpace 0 I y) (y : M) :
    (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
        unitScalarRSLiftSection (I := I) (M := M) S y) (Y y) =
      scalarFn (I := I) (M := M) Y y • S y := by
  rw [unitScalarRSLiftSection_apply, unitScalarRSLift_apply]
  rfl

/-- **Smoothness of the lift.** If `S` is a smooth `(0, s)`-tensor section, then the lifted
`(r = 0, s)`-tensor section `unitScalarRSLiftSection S` is smooth. -/
theorem contMDiff_unitScalarRSLiftSection {s : ℕ}
    (S : Π y : M, Tensor0SSpace s I y)
    (hS : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) y (S y))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (unitScalarRSLiftSection (I := I) (M := M) S y)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := fun y : M => Tensor0SSpace 0 I y)
    (V₂ := fun y : M => Tensor0SSpace s I y)
    (φ := fun y : M => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
      unitScalarRSLiftSection (I := I) (M := M) S y))
  intro Y
  have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞ (scalarFn (I := I) (M := M) (fun y => Y y)) :=
    (contMDiff_scalarFn_iff_section (I := I) (M := M) (fun y => Y y)).mpr Y.contMDiff
  have hsmul : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) y
        (scalarFn (I := I) (M := M) (fun y => Y y) y • S y)) :=
    ContMDiff.smul_section hscalar hS
  have hpt : (fun y : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) y
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
          unitScalarRSLiftSection (I := I) (M := M) S y) (Y y))) =
      (fun y : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) y
        (scalarFn (I := I) (M := M) (fun y => Y y) y • S y)) := by
    funext y
    rw [unitScalarRSLiftSection_apply_at_section (I := I) (M := M) S (fun y => Y y) y]
  rw [hpt]
  exact hsmul

/-- The lifted section packaged as a smooth `Cₛ^∞` `(r = 0, s)`-tensor section. -/
noncomputable def unitScalarRSLiftCₛ {s : ℕ}
    (S : Cₛ^∞⟮I; Tensor0SModel s ℝ E, (fun y : M => Tensor0SSpace s I y)⟯) :
    Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun y : M => TensorRSSpace 0 s I y)⟯ :=
  ⟨fun y : M => unitScalarRSLiftSection (I := I) (M := M) (fun z => S z) y,
   contMDiff_unitScalarRSLiftSection (I := I) (M := M) (fun z => S z) S.contMDiff⟩

@[simp] theorem unitScalarRSLiftCₛ_apply {s : ℕ}
    (S : Cₛ^∞⟮I; Tensor0SModel s ℝ E, (fun y : M => Tensor0SSpace s I y)⟯) (y : M) :
    unitScalarRSLiftCₛ (I := I) (M := M) S y =
      unitScalarRSLiftSection (I := I) (M := M) (fun z => S z) y := rfl

/-- **Headline global agreement.** For a smooth `Cₛ^∞` abstract `(0, s)`-tensor section
`S`, the abstract recursive `(0, s)`-tensor covariant derivative equals the `(r = 0, s)`
covariant derivative of the canonical lift, read back through the unit `(0, 0)`-tensor:
```
(∇^{(0,s)abs}_v S)(x) = (∇^{(0,s)RS}_v (lift S))(x)(unit).
```
This is the global section identity identifying the two `(0, s)` covariant derivatives
under the canonical bundle isomorphism `TensorRSSpace 0 s ≃L Tensor0SSpace s` (evaluate at
the unit). The proof is pure locality of the Hom-bundle product rule against the
`∇`-parallel unit `(0, 0)`-section: no partition of unity and no chart restriction. -/
theorem tensor0SCovariantDerivative_eq_tensorRSCovariantDerivative
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : Cₛ^∞⟮I; Tensor0SModel s ℝ E, (fun y : M => Tensor0SSpace s I y)⟯)
    (x : M) (v : TangentSpace I x) :
    Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
        (fun y : M => S y) x v =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)
          (fun y : M => unitScalarRSLiftCₛ (I := I) (M := M) S y) x v)
        (unitZeroSec (I := I) (M := M) x) := by
  classical
  rw [tensorRSCovariantDerivative_zeroS_unit_eval (I := I) (M := M) g s
    (unitScalarRSLiftCₛ (I := I) (M := M) S) x v]
  have hsec : (fun y : M =>
        (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
          unitScalarRSLiftCₛ (I := I) (M := M) S y)
          (unitZeroSec (I := I) (M := M) y)) =
      (fun y : M => S y) := by
    funext y
    rw [unitScalarRSLiftCₛ_apply]
    exact unitScalarRSLiftSection_apply_unit (I := I) (M := M) (fun z => S z) y
  rw [hsec]

end Connection
end Integral
end DifferentialGeometry

end
