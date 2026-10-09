import DifferentialGeometry.Tensor.BilinearForm.Coordinates
import DifferentialGeometry.Bundle.TangentOpenRestriction
import DifferentialGeometry.Analysis.FiniteDimensional.Coercivity
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
private theorem symmL_open_model_space_finite (U : Opens E) (x₀ x : U) :
    (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).symmL ℝ x =
      (1 : E →L[ℝ] E) := by
  have hx : x ∈ (chartAt E x₀).source := by
    rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]
    exact mem_univ _
  rw [TangentBundle.symmL_trivializationAt_eq_core hx,
    tangentCoordChange_opens x₀ x x (mem_univ _), TangentBundle.coordChange_model_space]

theorem exists_contMDiffMetric_of_contDiffOn_bilinearField
    (U : Opens E) (n : WithTop ℕ∞) (B : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hsymm : ∀ x ∈ U, ∀ v w, B x v w = B x w v)
    (hpos : ∀ x, x ∈ U → ∀ v, v ≠ 0 → 0 < B x v v)
    (hB : ContDiffOn ℝ n B U) :
    ∃ g : ContMDiffRiemannianMetric 𝓘(ℝ, E) n E
        (TangentSpace 𝓘(ℝ, E) : U → Type _),
      ∀ x v w, g.inner x v w = B x.1 v w := by
  let gm : ∀ x : U, TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ :=
    fun x => B x.1
  refine ⟨{
    inner := gm
    symm := fun x v w => hsymm x.1 x.2 v w
    pos := fun x v hv => hpos x.1 x.2 v hv
    isVonNBounded := ?_
    contMDiff := ?_ }, fun _ _ _ => rfl⟩
  · intro x
    have hc := (B x.1).isCoercive_of_posDef (hpos x.1 x.2)
    change Bornology.IsVonNBounded ℝ {v : E | B x.1 v v < 1}
    exact NormedSpace.isVonNBounded_of_isBounded ℝ
      ((hc.isBounded_le 1).subset (fun v hv => show B x.1 v v ≤ 1 from le_of_lt hv))
  · intro x₀
    rw [contMDiffAt_section]
    have hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) n
        (fun x : U => B x.1) := by
      exact hB.contMDiffOn.comp_contMDiff (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := U))
        (fun x => x.property)
    apply hb.contMDiffAt.congr_of_eventuallyEq
    let e := trivializationAt E (TangentSpace 𝓘(ℝ, E) : U → Type _) x₀
    filter_upwards [e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E
      (TangentSpace 𝓘(ℝ, E) : U → Type _) x₀)] with x hx
    ext v w
    rw [BilinearForm.trivializationAt_apply x₀ hx,
      symmL_open_model_space_finite U x₀ x]
    rfl

end DifferentialGeometry.Geometry
