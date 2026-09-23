import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas
import Mathlib.Geometry.Manifold.SmoothEmbedding

noncomputable section

open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SmoothBoundaryAtlas

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ} [NeZero n] {K : Set M} (C : SmoothBoundaryAtlas I n K)

private def boundarylessModelInverse [I.Boundaryless] :
    PartialDiffeomorph 𝓘(ℝ, E) I E H ∞ where
  toPartialEquiv := I.toHomeomorph.symm.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := by
    change ContMDiffOn 𝓘(ℝ, E) I ∞ I.symm univ
    simpa only [I.range_eq_univ] using I.contMDiffOn_symm (n := ∞)
  contMDiffOn_invFun := I.contMDiff.contMDiffOn

theorem isSmoothEmbedding_subtype_val [I.Boundaryless] [IsManifold I ∞ M] :
    let _ := C.toChartedSpace
    IsSmoothEmbedding (𝓡∂ n) I ∞ (Subtype.val : K → M) := by
  let _ := C.toChartedSpace
  let _ := C.isManifold
  refine ⟨IsImmersionOfComplement.isImmersion (F := PUnit.{1}) ?_,
    _root_.Topology.IsEmbedding.subtypeVal⟩
  intro x
  let a := C.ambientChart x
  let L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] E :=
    ((a.isLocalDiffeomorphAt I (𝓡 n) ∞ (C.mem_source x)).mfderivToContinuousLinearEquiv
      (by simp)).symm
  let b := (a.trans L.toDiffeomorph.toPartialDiffeomorph).trans
    (boundarylessModelInverse (I := I))
  have hb (y : M) (hy : y ∈ a.source) : y ∈ b.source := by
    change (y ∈ a.source ∧ True) ∧ True
    exact ⟨⟨hy, trivial⟩, trivial⟩
  have hbmax : b.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas I ∞ M :=
    b.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
      b.contMDiffOn_toFun b.contMDiffOn_invFun
  have hformula (y : K) (hy : y ∈ (C.chart x).source) :
      b.toOpenPartialHomeomorph.extend I y.val = L ((C.chart x).extend (𝓡∂ n) y) := by
    change I (I.symm (L (a y.val))) = L ((C.chart x y).val)
    rw [I.right_inv (by rw [I.range_eq_univ]; trivial)]
    exact congrArg L (OpenPartialHomeomorph.restrictSubtypes_apply
      (C.ambientChart x).toOpenPartialHomeomorph K
      {v : EuclideanSpace ℝ (Fin n) | 0 ≤ v 0} x (0 : EuclideanHalfSpace n)
      (C.mem_iff x) y hy).symm
  refine IsImmersionAtOfComplement.mk_of_charts
    ((ContinuousLinearEquiv.prodUnique ℝ (EuclideanSpace ℝ (Fin n)) PUnit.{1}).trans L)
    (C.chart x) b.toOpenPartialHomeomorph (C.mem_source x) (hb x.val (C.mem_source x))
    (IsManifold.chart_mem_maximalAtlas x) hbmax (fun y hy => hb y.val hy) ?_
  intro u hu
  let y := ((C.chart x).extend (𝓡∂ n)).symm u
  have hy : y ∈ (C.chart x).source := by
    simpa only [OpenPartialHomeomorph.extend_source] using
      ((C.chart x).extend (𝓡∂ n)).map_target hu
  change b.toOpenPartialHomeomorph.extend I y.val = L u
  rw [hformula y hy]
  exact congrArg L (((C.chart x).extend (𝓡∂ n)).right_inv hu)

theorem isBoundaryPoint_iff_mem_frontier
    (hzero : ∀ x : K, C.ambientChart x x.val 0 = 0 ↔ x.val ∈ frontier K) (x : K) :
    let _ := C.toChartedSpace
    (𝓡∂ n).IsBoundaryPoint x ↔ x.val ∈ frontier K := by
  let _ := C.toChartedSpace
  exact (C.isBoundaryPoint_iff x).trans (hzero x)

theorem isInteriorPoint_iff_mem_interior
    (hzero : ∀ x : K, C.ambientChart x x.val 0 = 0 ↔ x.val ∈ frontier K) (x : K) :
    let _ := C.toChartedSpace
    (𝓡∂ n).IsInteriorPoint x ↔ x.val ∈ interior K := by
  let _ := C.toChartedSpace
  change (𝓡∂ n).IsInteriorPoint x ↔ x.val ∈ interior K
  have hb : (𝓡∂ n).IsBoundaryPoint x ↔ x.val ∈ frontier K :=
    C.isBoundaryPoint_iff_mem_frontier hzero x
  rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint, hb,
    mem_interior_iff_notMem_frontier x.property]

theorem image_boundary_subtype_val (hclosed : IsClosed K)
    (hzero : ∀ x : K, C.ambientChart x x.val 0 = 0 ↔ x.val ∈ frontier K) :
    let _ := C.toChartedSpace
    Subtype.val '' ((𝓡∂ n).boundary K) = frontier K := by
  let _ := C.toChartedSpace
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (C.isBoundaryPoint_iff_mem_frontier hzero y).mp hy
  · intro hx
    exact ⟨⟨x, hclosed.frontier_subset hx⟩,
      (C.isBoundaryPoint_iff_mem_frontier hzero _).mpr hx, rfl⟩

theorem image_interior_subtype_val
    (hzero : ∀ x : K, C.ambientChart x x.val 0 = 0 ↔ x.val ∈ frontier K) :
    let _ := C.toChartedSpace
    Subtype.val '' ((𝓡∂ n).interior K) = interior K := by
  let _ := C.toChartedSpace
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (C.isInteriorPoint_iff_mem_interior hzero y).mp hy
  · intro hx
    exact ⟨⟨x, interior_subset hx⟩,
      (C.isInteriorPoint_iff_mem_interior hzero _).mpr hx, rfl⟩

end DifferentialGeometry.Topology.SmoothBoundaryAtlas
