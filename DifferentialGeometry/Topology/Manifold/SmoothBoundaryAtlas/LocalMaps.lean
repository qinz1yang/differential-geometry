import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Maps

noncomputable section

open Set Function Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SmoothBoundaryAtlas

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ} [NeZero n] {K : Set M} (C : SmoothBoundaryAtlas I n K)
  {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M'] [ChartedSpace H' M']
  {m : ℕ} [NeZero m] {K' : Set M'} (C' : SmoothBoundaryAtlas I' m K')

def partialDiffeomorphOfAmbient
    (φ : PartialDiffeomorph I I' M M' ∞) (x₀ : K) (y₀ : K')
    (hK : ∀ x ∈ φ.source, x ∈ K ↔ φ x ∈ K') :
    let _ := C.toChartedSpace
    let _ := C'.toChartedSpace
    PartialDiffeomorph (𝓡∂ n) (𝓡∂ m) K K' ∞ := by
  let _ := C.toChartedSpace
  let _ := C'.toChartedSpace
  let ψ := OpenPartialHomeomorph.restrictSubtypes φ.toOpenPartialHomeomorph K K' x₀ y₀ hK
  refine
    { ψ with
      contMDiffOn_toFun := ?_
      contMDiffOn_invFun := ?_ }
  · apply (C'.contMDiffOn_iff_subtype_val _ _).mpr
    have h := φ.contMDiffOn_toFun.comp C.contMDiff_subtype_val.contMDiffOn
      (fun x hx => hx)
    apply h.congr
    intro x hx
    exact OpenPartialHomeomorph.restrictSubtypes_apply φ.toOpenPartialHomeomorph K K' x₀ y₀ hK x hx
  · apply (C.contMDiffOn_iff_subtype_val _ _).mpr
    have h := φ.contMDiffOn_invFun.comp C'.contMDiff_subtype_val.contMDiffOn
      (fun x hx => hx)
    apply h.congr
    intro x hx
    exact OpenPartialHomeomorph.restrictSubtypes_symm_apply φ.toOpenPartialHomeomorph K K' x₀ y₀ hK x hx

theorem partialDiffeomorphOfAmbient_source
    (φ : PartialDiffeomorph I I' M M' ∞) (x₀ : K) (y₀ : K')
    (hK : ∀ x ∈ φ.source, x ∈ K ↔ φ x ∈ K') :
    let _ := C.toChartedSpace
    let _ := C'.toChartedSpace
    (C.partialDiffeomorphOfAmbient C' φ x₀ y₀ hK).source = Subtype.val ⁻¹' φ.source := rfl

theorem partialDiffeomorphOfAmbient_apply_val
    (φ : PartialDiffeomorph I I' M M' ∞) (x₀ : K) (y₀ : K')
    (hK : ∀ x ∈ φ.source, x ∈ K ↔ φ x ∈ K') (x : K) (hx : x.val ∈ φ.source) :
    (C.partialDiffeomorphOfAmbient C' φ x₀ y₀ hK x).val = φ x.val :=
  OpenPartialHomeomorph.restrictSubtypes_apply φ.toOpenPartialHomeomorph K K' x₀ y₀ hK x hx

theorem partialDiffeomorphOfAmbient_symm_apply_val
    (φ : PartialDiffeomorph I I' M M' ∞) (x₀ : K) (y₀ : K')
    (hK : ∀ x ∈ φ.source, x ∈ K ↔ φ x ∈ K') (y : K') (hy : y.val ∈ φ.target) :
    let _ := C.toChartedSpace
    let _ := C'.toChartedSpace
    ((C.partialDiffeomorphOfAmbient C' φ x₀ y₀ hK).symm y).val = φ.symm y.val :=
  OpenPartialHomeomorph.restrictSubtypes_symm_apply φ.toOpenPartialHomeomorph K K' x₀ y₀ hK y hy


def partialDiffeomorphOfBoundaryChart
    (φ : PartialDiffeomorph I (𝓡 n) M (EuclideanSpace ℝ (Fin n)) ∞) (x₀ : K)
    (hK : ∀ x ∈ φ.source, x ∈ K ↔ 0 ≤ φ x 0) :
    let _ := C.toChartedSpace
    PartialDiffeomorph (𝓡∂ n) (𝓡∂ n) K (EuclideanHalfSpace n) ∞ := by
  let _ := C.toChartedSpace
  let ψ := OpenPartialHomeomorph.restrictSubtypes φ.toOpenPartialHomeomorph
    K {v : EuclideanSpace ℝ (Fin n) | 0 ≤ v 0} x₀ (0 : EuclideanHalfSpace n) hK
  refine
    { ψ with
      contMDiffOn_toFun := ?_
      contMDiffOn_invFun := ?_ }
  · intro x hx
    rw [contMDiffWithinAt_iff_target]
    refine ⟨ψ.continuousOn x hx, ?_⟩
    have h := φ.contMDiffOn_toFun.comp C.contMDiff_subtype_val.contMDiffOn (fun y hy => hy)
    have heq : EqOn (fun y : K => (ψ y).val) (φ ∘ Subtype.val) ψ.source := by
      intro y hy
      exact OpenPartialHomeomorph.restrictSubtypes_apply φ.toOpenPartialHomeomorph
        K {v : EuclideanSpace ℝ (Fin n) | 0 ≤ v 0} x₀ (0 : EuclideanHalfSpace n) hK y hy
    change ContMDiffWithinAt (𝓡∂ n) (𝓡 n) ∞ (fun y : K => (ψ y).val) ψ.source x
    exact (h.congr heq) x hx
  · apply (C.contMDiffOn_iff_subtype_val _ _).mpr
    have h := φ.contMDiffOn_invFun.comp (𝓡∂ n).contMDiff.contMDiffOn (fun y hy => hy)
    apply h.congr
    intro y hy
    exact OpenPartialHomeomorph.restrictSubtypes_symm_apply φ.toOpenPartialHomeomorph
      K {v : EuclideanSpace ℝ (Fin n) | 0 ≤ v 0} x₀ (0 : EuclideanHalfSpace n) hK y hy

theorem partialDiffeomorphOfBoundaryChart_source
    (φ : PartialDiffeomorph I (𝓡 n) M (EuclideanSpace ℝ (Fin n)) ∞) (x₀ : K)
    (hK : ∀ x ∈ φ.source, x ∈ K ↔ 0 ≤ φ x 0) :
    let _ := C.toChartedSpace
    (C.partialDiffeomorphOfBoundaryChart φ x₀ hK).source = Subtype.val ⁻¹' φ.source := rfl

theorem partialDiffeomorphOfBoundaryChart_apply_val
    (φ : PartialDiffeomorph I (𝓡 n) M (EuclideanSpace ℝ (Fin n)) ∞) (x₀ : K)
    (hK : ∀ x ∈ φ.source, x ∈ K ↔ 0 ≤ φ x 0) (x : K) (hx : x.val ∈ φ.source) :
    (C.partialDiffeomorphOfBoundaryChart φ x₀ hK x).val = φ x.val :=
  OpenPartialHomeomorph.restrictSubtypes_apply φ.toOpenPartialHomeomorph K
    {v : EuclideanSpace ℝ (Fin n) | 0 ≤ v 0} x₀ (0 : EuclideanHalfSpace n) hK x hx

theorem partialDiffeomorphOfBoundaryChart_symm_apply_val
    (φ : PartialDiffeomorph I (𝓡 n) M (EuclideanSpace ℝ (Fin n)) ∞) (x₀ : K)
    (hK : ∀ x ∈ φ.source, x ∈ K ↔ 0 ≤ φ x 0)
    (y : EuclideanHalfSpace n) (hy : y.val ∈ φ.target) :
    let _ := C.toChartedSpace
    ((C.partialDiffeomorphOfBoundaryChart φ x₀ hK).symm y).val = φ.symm y.val :=
  OpenPartialHomeomorph.restrictSubtypes_symm_apply φ.toOpenPartialHomeomorph K
    {v : EuclideanSpace ℝ (Fin n) | 0 ≤ v 0} x₀ (0 : EuclideanHalfSpace n) hK y hy

end DifferentialGeometry.Topology.SmoothBoundaryAtlas
