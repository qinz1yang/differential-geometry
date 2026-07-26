import DifferentialGeometry.Geometry.Metric.Sphere.RoundMetric
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The tangential-projection connection on the round sphere

For the unit sphere `S^n ⊂ E` with the round metric, the Levi-Civita connection is the
tangential projection of the ambient (flat) derivative.  This file builds that connection
*intrinsically* as a `CovariantDerivative`, `projConnCD`, defined by

  `dι_x (projConn Y x v) = π_{(ℝ∙x)ᗮ} (D_v (dι Y))`,

where `dι = dIncl` is the inclusion differential and `π_{(ℝ∙x)ᗮ}` is orthogonal projection onto
the tangent space (= range of `dι_x`).  We work entirely through the **characterization**
`dIncl_projConn`, injecting `dIncl x` and comparing in the ambient space `E`, so the
`dIncl⁻¹`/projection bookkeeping never appears in downstream proofs.

The connection's smoothness is intentionally **not** established here: the only consumer
(`RoundProjConnLC`) identifies `projConn` with `metricCov roundMetric` via Koszul uniqueness,
which needs only torsion-freeness and metric-compatibility, not a smoothness class.

## Main definitions / results

* `dInclField Y` — the ambient pushforward `x ↦ dι_x (Y x) : S^n → E`.
* `dInclField_mdifferentiableAt` — its differentiability from that of `Y`.
* `dInclEquiv x` — `dι_x` as a continuous linear equivalence onto `(ℝ∙x)ᗮ`.
* `projConn`, `dIncl_projConn` — the connection map and its ambient characterization.
* `projConnCD : CovariantDerivative (𝓡 n) E (TangentSpace (𝓡 n))` — the bundled connection.
-/

noncomputable section

open Bundle Manifold Set Metric Module
open scoped Manifold Topology ContDiff RealInnerProductSpace

namespace DifferentialGeometry
namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)]

/-- The ambient pushforward of a tangent section `Y` along the inclusion:
`dInclField Y x = dι_x (Y x) ∈ E`. -/
noncomputable def dInclField (Y : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x) :
    sphere (0 : E) 1 → E :=
  fun x => dIncl (n := n) x (Y x)

omit [FiniteDimensional ℝ E] in
@[simp] theorem dInclField_apply (Y : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x)
    (x : sphere (0 : E) 1) : dInclField (n := n) Y x = dIncl (n := n) x (Y x) := rfl

omit [FiniteDimensional ℝ E] in
/-- The ambient pushforward of a section that is differentiable at `x` is itself
differentiable at `x` (mirrors `vectorFieldActionSmooth`'s fibre extraction, at the
`MDifferentiableAt` level). -/
theorem dInclField_mdifferentiableAt
    {Y : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x} {x : sphere (0 : E) 1}
    (hY : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y (Y y))) x) :
    MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) (dInclField (n := n) Y) x := by
  have htangent : ContMDiff (𝓡 n).tangent 𝓘(ℝ, E).tangent ∞
      (tangentMap (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E)) := by
    apply ContMDiff.contMDiff_tangentMap contMDiff_coe_sphere
    exact le_top
  have hcomp : MDifferentiableAt (𝓡 n) (𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (fun y => tangentMap (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) ⟨y, Y y⟩) x :=
    (htangent.contMDiffAt.mdifferentiableAt (by simp)).comp x hY
  rw [mdifferentiableAt_totalSpace] at hcomp
  refine hcomp.2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  simp only [dInclField, dIncl, tangentMap, trivializationAt_model_space_apply]
  rfl

/-- The inclusion differential `dι_x`, as a continuous linear equivalence from `T_x S^n`
onto the model tangent space `(ℝ∙x)ᗮ ⊂ E`. -/
noncomputable def dInclEquiv (x : sphere (0 : E) 1) :
    TangentSpace (𝓡 n) x ≃L[ℝ] ((ℝ ∙ (↑x : E))ᗮ) := by
  haveI : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n)))
  haveI : T2Space (TangentSpace (𝓡 n) x) :=
    inferInstanceAs (T2Space (EuclideanSpace ℝ (Fin n)))
  have hmem : ∀ v : TangentSpace (𝓡 n) x, dIncl (n := n) x v ∈ (ℝ ∙ (↑x : E))ᗮ := by
    intro v
    rw [← range_mfderiv_coe_sphere (n := n) x]
    exact ⟨v, rfl⟩
  refine LinearEquiv.toContinuousLinearEquiv
    (LinearEquiv.ofBijective ((dIncl (n := n) x).codRestrict _ hmem).toLinearMap ⟨?_, ?_⟩)
  · intro a b hab
    exact mfderiv_coe_sphere_injective x (by simpa using congrArg Subtype.val hab)
  · intro w
    obtain ⟨v, hv⟩ := (range_mfderiv_coe_sphere (n := n) x).ge w.2
    exact ⟨v, Subtype.ext hv⟩

omit [FiniteDimensional ℝ E] in
@[simp] theorem dInclEquiv_coe (x : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) x) :
    ((dInclEquiv (n := n) x v : (ℝ ∙ (↑x : E))ᗮ) : E) = dIncl (n := n) x v := by
  simp only [dInclEquiv, LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.ofBijective_apply]
  rfl

omit [FiniteDimensional ℝ E] in
/-- `dInclField` is additive in the section argument. -/
theorem dInclField_add (Y Y' : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x) :
    dInclField (n := n) (Y + Y') = dInclField (n := n) Y + dInclField (n := n) Y' := by
  funext y
  simp only [dInclField, Pi.add_apply, map_add]

omit [FiniteDimensional ℝ E] in
/-- `dInclField` is homogeneous over scalar functions in the section argument. -/
theorem dInclField_smul (g : sphere (0 : E) 1 → ℝ)
    (Y : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x) :
    dInclField (n := n) (g • Y) = g • dInclField (n := n) Y := by
  funext y
  change dIncl (n := n) y (g y • Y y) = g y • dIncl (n := n) y (Y y)
  exact map_smul _ _ _

/-- The ambient (flat) directional derivative of the pushed section `dι Y`, with its codomain
ascribed to the model space `E` (definitionally the `mfderiv`, since `TangentSpace 𝓘(ℝ,E) p = E`).
The `E`-valued form avoids the tangent-space-at-image type synonyms when combining derivatives at
different points. -/
noncomputable def ambDeriv (Y : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x)
    (x : sphere (0 : E) 1) : TangentSpace (𝓡 n) x →L[ℝ] E :=
  (mfderiv (𝓡 n) 𝓘(ℝ, E) (dInclField (n := n) Y) x : TangentSpace (𝓡 n) x →L[ℝ] E)

omit [FiniteDimensional ℝ E] in
@[simp] theorem ambDeriv_apply (Y : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x)
    (x : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) x) :
    ambDeriv (n := n) Y x v = mfderiv (𝓡 n) 𝓘(ℝ, E) (dInclField (n := n) Y) x v := rfl

omit [FiniteDimensional ℝ E] in
/-- The ambient directional derivative is additive in the section. -/
theorem ambDeriv_add {Y Y' : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x} {x : sphere (0 : E) 1}
    (hY : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y (Y y))) x)
    (hY' : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y (Y' y))) x)
    (v : TangentSpace (𝓡 n) x) :
    ambDeriv (n := n) (Y + Y') x v
      = ambDeriv (n := n) Y x v + ambDeriv (n := n) Y' x v := by
  have h : ambDeriv (n := n) (Y + Y') x = ambDeriv (n := n) Y x + ambDeriv (n := n) Y' x := by
    have h0 := mfderiv_add (dInclField_mdifferentiableAt (n := n) hY)
      (dInclField_mdifferentiableAt (n := n) hY')
    rw [← dInclField_add] at h0
    exact h0
  rw [h, ContinuousLinearMap.add_apply]

omit [FiniteDimensional ℝ E] in
/-- The ambient directional derivative obeys the Leibniz rule against a scalar function. -/
theorem ambDeriv_smul {Y : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x}
    {g : sphere (0 : E) 1 → ℝ} {x : sphere (0 : E) 1}
    (hY : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y (Y y))) x)
    (hg : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) g x) (v : TangentSpace (𝓡 n) x) :
    ambDeriv (n := n) (g • Y) x v
      = g x • ambDeriv (n := n) Y x v + (extDerivFun g x v) • dInclField (n := n) Y x := by
  have key := fromTangentSpace_mfderiv_smul_apply hg (dInclField_mdifferentiableAt (n := n) hY) v
  rw [← dInclField_smul] at key
  exact key

/-- The tangential-projection connection map: `projConn Y x` is the unique CLM with
`dι_x (projConn Y x v) = π_{(ℝ∙x)ᗮ}(D_v (dι Y))`. -/
noncomputable def projConn (Y : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x) :
    ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x :=
  fun x => (dInclEquiv (n := n) x).symm.toContinuousLinearMap.comp
    (((ℝ ∙ (↑x : E))ᗮ).orthogonalProjection.comp (ambDeriv (n := n) Y x))

omit [FiniteDimensional ℝ E] in
/-- **Ambient characterization of `projConn`.**  Injecting `dIncl x`, the connection value
is the tangential projection of the ambient directional derivative. -/
theorem dIncl_projConn (Y : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x)
    (x : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) x) :
    dIncl (n := n) x (projConn (n := n) Y x v)
      = (↑(((ℝ ∙ (↑x : E))ᗮ).orthogonalProjection (ambDeriv (n := n) Y x v)) : E) := by
  simp only [projConn, ContinuousLinearMap.comp_apply]
  rw [← dInclEquiv_coe (n := n) x]
  congr 1
  exact (dInclEquiv (n := n) x).apply_symm_apply _

/-- The bundled tangential-projection connection on the round sphere. -/
noncomputable def projConnCD :
    CovariantDerivative (𝓡 n) (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _) where
  toFun := projConn (n := n)
  isCovariantDerivativeOnUniv := by
    refine { add := ?_, leibniz := ?_ }
    · intro Y Y' x hY hY' _
      ext v
      rw [ContinuousLinearMap.add_apply]
      refine mfderiv_coe_sphere_injective x ?_
      change dIncl (n := n) x (projConn (n := n) (Y + Y') x v)
        = dIncl (n := n) x (projConn (n := n) Y x v + projConn (n := n) Y' x v)
      rw [map_add, dIncl_projConn, dIncl_projConn, dIncl_projConn, ambDeriv_add hY hY',
        map_add, Submodule.coe_add]
    · intro Y g x hY hg _
      ext v
      rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply]
      refine mfderiv_coe_sphere_injective x ?_
      change dIncl (n := n) x (projConn (n := n) (g • Y) x v)
        = dIncl (n := n) x (g x • projConn (n := n) Y x v + (extDerivFun g x v) • Y x)
      have hmem : dInclField (n := n) Y x ∈ (ℝ ∙ (↑x : E))ᗮ := by
        rw [← range_mfderiv_coe_sphere (n := n) x]; exact ⟨Y x, rfl⟩
      have hfix : (↑(((ℝ ∙ (↑x : E))ᗮ).orthogonalProjection (dInclField (n := n) Y x)) : E)
          = dInclField (n := n) Y x := by
        rw [← Submodule.starProjection_apply]
        exact Submodule.starProjection_eq_self_iff.mpr hmem
      rw [map_add, map_smul, map_smul, dIncl_projConn, dIncl_projConn, ambDeriv_smul hY hg,
        map_add, map_smul, map_smul, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul,
        hfix, dInclField_apply]

end Geometry
end DifferentialGeometry
