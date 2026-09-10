import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

noncomputable section
open Set Bundle
open scoped Manifold ContDiff

namespace Poincare.Geometry.VectorField

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

def extendOpenTangentField (U : TopologicalSpace.Opens M)
    (X : ∀ x : U, TangentSpace I x) (x : M) : TangentSpace I x := by
  classical
  exact if hx : x ∈ U then mfderiv I I (Subtype.val : U → M) ⟨x, hx⟩ (X ⟨x, hx⟩) else 0

theorem extendOpenTangentField_apply (U : TopologicalSpace.Opens M)
    (X : ∀ x : U, TangentSpace I x) (x : U) :
    extendOpenTangentField U X (x : M) = mfderiv I I (Subtype.val : U → M) x (X x) := by
  simp only [extendOpenTangentField, dif_pos x.property]

theorem contMDiffOn_extendOpenTangentField [IsManifold I ∞ M]
    (U : TopologicalSpace.Opens M) (X : ∀ x : U, TangentSpace I x)
    {A : Set U} (hA : IsOpen A)
    (hX : ContMDiffOn I I.tangent ∞ (fun x ↦ (⟨x, X x⟩ : TangentBundle I U)) A) :
    ContMDiffOn I I.tangent ∞
      (fun x ↦ (⟨x, extendOpenTangentField U X x⟩ : TangentBundle I M))
      (Subtype.val '' A) := by
  have hT : ContMDiff I.tangent I.tangent ∞ (tangentMap I I (Subtype.val : U → M)) :=
    (contMDiff_subtype_val (I := I) (n := ∞)).contMDiff_tangentMap (by simp)
  have heq : (fun x : U ↦ (⟨(x : M), extendOpenTangentField U X (x : M)⟩ : TangentBundle I M)) =
      tangentMap I I (Subtype.val : U → M) ∘ (fun x ↦ (⟨x, X x⟩ : TangentBundle I U)) := by
    funext x
    rw [extendOpenTangentField_apply]
    rfl
  rintro x ⟨y, hy, rfl⟩
  have hlocal : ContMDiffAt I I.tangent ∞
      (fun x : U ↦ (⟨(x : M), extendOpenTangentField U X (x : M)⟩ : TangentBundle I M)) y := by
    rw [heq]
    exact hT.contMDiffAt.comp y ((hX y hy).contMDiffAt (hA.mem_nhds hy))
  exact (contMDiffAt_subtype_iff.mp hlocal).contMDiffWithinAt

end Poincare.Geometry.VectorField
