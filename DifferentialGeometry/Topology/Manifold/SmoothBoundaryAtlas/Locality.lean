import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.LocalMaps
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph

section

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


theorem isLocalDiffeomorphAt_of_ambient_chart_eq
    (φ : PartialDiffeomorph I I' M M' ∞) (x₀ : K) (y₀ : K')
    (hK : ∀ x ∈ φ.source, x ∈ K ↔ φ x ∈ K')
    (f : K → K') (hf : ∀ x : K, x.val ∈ φ.source → (f x).val = φ x.val)
    (x : K) (hx : x.val ∈ φ.source) :
    let _ := C.toChartedSpace
    let _ := C'.toChartedSpace
    IsLocalDiffeomorphAt (𝓡∂ n) (𝓡∂ m) ∞ f x := by
  let _ := C.toChartedSpace
  let _ := C'.toChartedSpace
  let ψ := C.partialDiffeomorphOfAmbient C' φ x₀ y₀ hK
  have hlocal := ψ.isLocalDiffeomorphAt (𝓡∂ n) (𝓡∂ m) ∞ hx
  apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq _ hlocal
  filter_upwards [(φ.open_source.preimage continuous_subtype_val).mem_nhds hx] with y hy
  apply Subtype.ext
  exact (hf y hy).trans (C.partialDiffeomorphOfAmbient_apply_val C' φ x₀ y₀ hK y hy).symm

end DifferentialGeometry.Topology.SmoothBoundaryAtlas

end

end

section

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
  {m : ℕ} [NeZero m] {K' : Set M'} (D : SmoothBoundaryAtlas I' m K')

theorem isLocalDiffeomorphAt_of_open_ambient_map
    (U : TopologicalSpace.Opens M) (g : U → M')
    (hg : IsLocalDiffeomorph I I' ∞ g)
    (hK : ∀ y : U, y.val ∈ K ↔ g y ∈ K')
    (f : K → K') (hf : ∀ (y : K) (hy : y.val ∈ U), (f y).val = g ⟨y.val,hy⟩)
    (x : K) (hx : x.val ∈ U) :
    let _ := C.toChartedSpace
    let _ := D.toChartedSpace
    IsLocalDiffeomorphAt (𝓡∂ n) (𝓡∂ m) ∞ f x := by
  let _ := C.toChartedSpace
  let _ := D.toChartedSpace
  let xU : U := ⟨x.val,hx⟩
  obtain ⟨φ,hxφ,hφ⟩ := hg xU
  let j := PartialDiffeomorph.subtypeVal (I := I) U ⟨xU⟩
  let ψ := j.symm.trans φ
  have hinv (y : M) (hy : y ∈ U) : j.symm y = ⟨y,hy⟩ := by
    apply Subtype.ext
    exact (U.openPartialHomeomorphSubtypeCoe ⟨xU⟩).right_inv (by simpa using hy)
  have hsource (y : M) (hy : y ∈ ψ.source) : y ∈ U := by
    have hh := hy.1
    simpa [j, PartialDiffeomorph.subtypeVal] using hh
  have heq (y : M) (hy : y ∈ ψ.source) : ψ y = g ⟨y,hsource y hy⟩ := by
    change φ (j.symm y) = _
    exact (hφ hy.2).symm.trans (congrArg g (hinv y (hsource y hy)))
  apply C.isLocalDiffeomorphAt_of_ambient_chart_eq D ψ x (f x)
  · intro y hy
    exact (hK ⟨y,hsource y hy⟩).trans (by rw [heq y hy])
  · intro y hy
    exact (hf y (hsource y.val hy)).trans (heq y.val hy).symm
  · refine ⟨?_,?_⟩
    · simpa [j, PartialDiffeomorph.subtypeVal] using hx
    · change j.symm x.val ∈ φ.source
      exact (hinv x.val hx).symm ▸ hxφ

end DifferentialGeometry.Topology.SmoothBoundaryAtlas

end

end
