import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Chart-constant tangent fields

This file contains the low-level chart-constant tangent-field helper used by
coordinate and Levi-Civita/Koszul constructions.

It deliberately lives below the tensor covariant-derivative layer: tensor
calculus may use these fields, but constructing the Levi-Civita connection from
Koszul should not import `NablaOnTensors`.
-/

namespace TensorLieDeriv

noncomputable section

open Bundle
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The tangent field whose coordinates in the tangent-bundle trivialization centered at `x₀`
are the constant vector `v`. -/
noncomputable def tangentConstInChart [IsManifold I 1 M] (x₀ : M) (v : E) (p : M) :
    TangentSpace I p :=
  (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p v

@[simp] lemma tangentConstInChart_apply [IsManifold I 1 M] (x₀ : M) (v : E) (p : M) :
    tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ v p =
      (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p v := by
  rfl

lemma tangentConstInChart_add [IsManifold I 1 M] (x₀ : M) (v w : E) :
    (tangentConstInChart x₀ (v + w) : (p : M) → TangentSpace I p) =
      (tangentConstInChart x₀ v : (p : M) → TangentSpace I p) +
        tangentConstInChart x₀ w := by
  funext p
  change (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p (v + w) =
    (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p v +
      (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p w
  exact map_add _ _ _

lemma tangentConstInChart_smul [IsManifold I 1 M] (x₀ : M) (a : 𝕜) (v : E) :
    (tangentConstInChart x₀ (a • v) : (p : M) → TangentSpace I p) =
      a • (tangentConstInChart x₀ v : (p : M) → TangentSpace I p) := by
  funext p
  change (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p (a • v) =
    a • (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p v
  exact map_smul _ _ _

lemma mdifferentiableAt_tangentConstInChart_of_mem [IsManifold I 2 M]
    {x₀ p : M} (v : E)
    (hp : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    MDiffAt (T% (tangentConstInChart x₀ v : (p : M) → TangentSpace I p)) p := by
  let e := trivializationAt E (TangentSpace I) x₀
  refine (e.mdifferentiableAt_section_iff I
    (tangentConstInChart x₀ v : (p : M) → TangentSpace I p) hp).mpr ?_
  have hconst :
      (fun y : M =>
        (e ((T% (tangentConstInChart x₀ v : (p : M) → TangentSpace I p)) y)).2) =ᶠ[𝓝 p]
          fun _ : M => v := by
    filter_upwards [e.open_baseSet.mem_nhds hp] with y hy
    have hcoe : ⇑(e.linearMapAt 𝕜 y) = fun z => (e ⟨y, z⟩).2 :=
      e.coe_linearMapAt_of_mem (R := 𝕜) hy
    simpa [Bundle.Trivialization.continuousLinearMapAt_apply, hcoe] using
      (e.continuousLinearMapAt_symmL (R := 𝕜) hy v)
  exact hconst.mdifferentiableAt_iff.mpr mdifferentiableAt_const

end

end TensorLieDeriv
