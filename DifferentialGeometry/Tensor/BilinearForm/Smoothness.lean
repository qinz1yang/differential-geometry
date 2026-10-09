import DifferentialGeometry.Tensor.BilinearForm.Coordinates
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold ContinuousLinearMap Filter
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Geometry.Tensor
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem bilinear_coordinate_flip (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (b : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :
    (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀
      ⟨x, ((ContinuousLinearMap.flipₗᵢ ℝ E E ℝ) b)⟩).2 =
    ((trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀
      ⟨x, b⟩).2).flip := by
  ext v w
  simp only [ContinuousLinearMap.flip_apply]
  exact (DifferentialGeometry.BilinearForm.trivializationAt_apply x₀ hx
    ((ContinuousLinearMap.flipₗᵢ ℝ E E ℝ) b) v w).trans
      (DifferentialGeometry.BilinearForm.trivializationAt_apply x₀ hx b w v).symm

theorem contMDiffOn_bilinear_flip {s : Set M}
    {b : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hb : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        (E →L[ℝ] E →L[ℝ] ℝ) x (b x)) s) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        (E →L[ℝ] E →L[ℝ] ℝ) x (((ContinuousLinearMap.flipₗᵢ ℝ E E ℝ) (b x)) :
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) s := by
  let : ∀ x : M, ContinuousAdd (TangentSpace I x →L[ℝ] ℝ) := fun x => inferInstance
  intro x hx
  let e := trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
    (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x
  have he : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
  apply (Bundle.Trivialization.contMDiffWithinAt_section (e := e) s he).mpr
  have hc := (Bundle.Trivialization.contMDiffWithinAt_section (e := e) s he).mp (hb x hx)
  have hflip : ContDiff ℝ ∞
      ((ContinuousLinearMap.flipₗᵢ ℝ E E ℝ) :
        (E →L[ℝ] E →L[ℝ] ℝ) → (E →L[ℝ] E →L[ℝ] ℝ)) := by fun_prop
  have hh := hflip.comp_contMDiffWithinAt hc
  apply hh.congr_of_eventuallyEq_of_mem _ hx
  filter_upwards [nhdsWithin_le_nhds ((trivializationAt E (TangentSpace I) x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E (TangentSpace I) x))] with y hy
  exact bilinear_coordinate_flip x hy (b y)

theorem contMDiffOn_bilinear_symmetrize {s : Set M}
    {b : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hb : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        (E →L[ℝ] E →L[ℝ] ℝ) x (b x)) s) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        (E →L[ℝ] E →L[ℝ] ℝ) x
        ((fun C : E →L[ℝ] E →L[ℝ] ℝ => (1 / 2 : ℝ) • (C + C.flip)) (b x))) s := by
  let : ∀ x : M, ContinuousAdd (TangentSpace I x →L[ℝ] ℝ) := fun x => inferInstance
  exact (hb.add_section (contMDiffOn_bilinear_flip hb)).const_smul_section

end DifferentialGeometry.Geometry.Tensor
