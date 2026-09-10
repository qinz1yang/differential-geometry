import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

noncomputable section
open Set Function Topology Manifold
open scoped ContDiff

namespace Poincare.Topology.Manifold

variable {E H F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace G]

theorem exists_modelRestriction
    (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F G)
    (e : OpenPartialHomeomorph E F)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (himage : e.IsImage (range I) (range J)) :
    ∃ d : OpenPartialHomeomorph H G,
      d.source = I ⁻¹' e.source ∧ d.target = J ⁻¹' e.target ∧
      ContMDiffOn I J ∞ d d.source ∧ ContMDiffOn J I ∞ d.symm d.target ∧
      (∀ x ∈ d.source, J (d x) = e (I x)) ∧
      ∀ y ∈ d.target, I (d.symm y) = e.symm (J y) := by
  have hmap : ∀ x, I x ∈ e.source → e (I x) ∈ range J :=
    fun x hx ↦ (himage hx).mpr (mem_range_self x)
  have hinv : ∀ y, J y ∈ e.target → e.symm (J y) ∈ range I :=
    fun y hy ↦ (himage.symm hy).mpr (mem_range_self y)
  have hfor : ∀ x, I x ∈ e.source → J (J.symm (e (I x))) = e (I x) :=
    fun x hx ↦ J.right_inv (hmap x hx)
  have hback : ∀ y, J y ∈ e.target → I (I.symm (e.symm (J y))) = e.symm (J y) :=
    fun y hy ↦ I.right_inv (hinv y hy)
  let d : PartialDiffeomorph I J H G ∞ :=
    { toFun := J.symm ∘ e ∘ I
      invFun := I.symm ∘ e.symm ∘ J
      source := I ⁻¹' e.source
      target := J ⁻¹' e.target
      map_source' := by
        intro x hx
        change J (J.symm (e (I x))) ∈ e.target
        rw [hfor x hx]
        exact e.map_source hx
      map_target' := by
        intro y hy
        change I (I.symm (e.symm (J y))) ∈ e.source
        rw [hback y hy]
        exact e.map_target hy
      left_inv' := by
        intro x hx
        change I.symm (e.symm (J (J.symm (e (I x))))) = x
        rw [hfor x hx, e.left_inv hx, I.left_inv]
      right_inv' := by
        intro y hy
        change J.symm (e (I (I.symm (e.symm (J y))))) = y
        rw [hback y hy, e.right_inv hy, J.left_inv]
      open_source := e.open_source.preimage I.continuous
      open_target := e.open_target.preimage J.continuous
      contMDiffOn_toFun := J.contMDiffOn_symm.comp
        (he.contMDiffOn.comp I.contMDiff.contMDiffOn (fun x hx ↦ hx))
        (fun x hx ↦ hmap x hx)
      contMDiffOn_invFun := I.contMDiffOn_symm.comp
        (hi.contMDiffOn.comp J.contMDiff.contMDiffOn (fun y hy ↦ hy))
        (fun y hy ↦ hinv y hy) }
  exact ⟨d.toOpenPartialHomeomorph, rfl, rfl, d.contMDiffOn, d.symm.contMDiffOn, hfor, hback⟩

end Poincare.Topology.Manifold
