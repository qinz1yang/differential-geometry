import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Maps
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict

set_option autoImplicit false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SmoothBoundaryAtlas

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ} [NeZero n] {K : Set M} (C : SmoothBoundaryAtlas I n K)

def interiorPartialDiffeomorph (x₀ : K) :
    let _ := C.toChartedSpace
    PartialDiffeomorph (𝓡∂ n) I K M ∞ := by
  let _ := C.toChartedSpace
  classical
  let g : M → K := fun y => if hy : y ∈ K then ⟨y, hy⟩ else x₀
  have hg (y : M) (hy : y ∈ K) : (g y).val = y := by dsimp [g]; rw [dif_pos hy]
  refine
    { toFun := Subtype.val
      invFun := g
      source := Subtype.val ⁻¹' interior K
      target := interior K
      map_source' := fun _ hx => hx
      map_target' := fun y hy => by change (g y).val ∈ interior K; rw [hg y (interior_subset hy)]; exact hy
      left_inv' := fun x hx => Subtype.ext (hg x.val x.property)
      right_inv' := fun y hy => hg y (interior_subset hy)
      open_source := isOpen_interior.preimage continuous_subtype_val
      open_target := isOpen_interior
      contMDiffOn_toFun := C.contMDiff_subtype_val.contMDiffOn
      contMDiffOn_invFun := ?_ }
  apply (C.contMDiffOn_iff_subtype_val g (interior K)).mpr
  exact (contMDiff_id.contMDiffOn : ContMDiffOn I I ∞ id (interior K)).congr
    (fun y hy => hg y (interior_subset hy))

theorem isLocalDiffeomorphAt_subtype_val {x : K} (hx : x.val ∈ interior K) :
    let _ := C.toChartedSpace
    IsLocalDiffeomorphAt (𝓡∂ n) I ∞ (Subtype.val : K → M) x := by
  let _ := C.toChartedSpace
  exact (C.interiorPartialDiffeomorph x).isLocalDiffeomorphAt (𝓡∂ n) I ∞ hx

variable {F G X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  [TopologicalSpace X] [ChartedSpace G X]

theorem isLocalDiffeomorphAt_of_subtype_val {f : X → K} {x : X}
    (hx : (f x).val ∈ interior K)
    (hf : IsLocalDiffeomorphAt J I ∞ (Subtype.val ∘ f) x) :
    let _ := C.toChartedSpace
    IsLocalDiffeomorphAt J (𝓡∂ n) ∞ f x := by
  let _ := C.toChartedSpace
  have hc : ContinuousAt f x := _root_.Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
    hf.contMDiffAt.continuousAt
  have hg := C.isLocalDiffeomorphAt_subtype_val hx
  have hcomp := hf.comp (K := 𝓡∂ n) (P := K) hg.localInverse_isLocalDiffeomorphAt
  apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq _ hcomp
  exact (hg.localInverse_eventuallyEq_left.comp_tendsto hc).symm

end DifferentialGeometry.Topology.SmoothBoundaryAtlas
