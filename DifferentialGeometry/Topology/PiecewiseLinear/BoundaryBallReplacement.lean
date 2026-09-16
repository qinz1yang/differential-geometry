import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldComplement
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubcomplexBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_isPLHomeomorphOn_boundary_complement
    (K A R : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite A.faces] [Finite R.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hA : IsPLBall 3 A.space)
    (hAK : A.space ⊆ K.space) (hD : IsPLBall 2 (A.space ∩ (boundaryComplex 3 K).space))
    (hR : IsCombinatorialManifoldWithBoundary 3 R) (hRspace : R.space = closure (K.space \ A.space)) :
    ∃ H : E → E, IsPLHomeomorphOn H (boundaryComplex 3 K).space (boundaryComplex 3 R).space ∧
      EqOn H id (closure ((boundaryComplex 3 K).space \ A.space)) := by
  classical
  let B := boundaryComplex 3 K
  let S := (boundaryComplex 3 A).space
  let D := A.space ∩ B.space
  let P := closure (B.space \ A.space)
  let Q := closure (S \ D)
  let _ : Finite B.faces := (boundaryComplex_faces_finite 3 K).to_subtype
  have hB : IsCombinatorialManifold 2 B := isCombinatorialManifold_boundaryComplex K hK
  have hS : IsPLSphere 2 S := isPLSphere_boundaryComplex_space_of_isPLBall A hA
  have hDS : D ⊆ S := inter_boundaryComplex_space_subset_of_subset K A hK
    hA.isCombinatorialManifoldWithBoundary hAK
  have hDB : D ⊆ B.space := inter_subset_right
  have hdiff : B.space \ A.space = B.space \ D := by
    ext x
    simp only [D, mem_sdiff, mem_inter_iff]
    tauto
  obtain ⟨r, hr⟩ := hD
  have hPQ : P ∩ D = r '' stdSimplexBoundary 2 := by
    change closure (B.space \ A.space) ∩ D = _
    rw [hdiff, inter_comm]
    exact hB.inter_closure_sdiff_eq_image_stdSimplexBoundary B hr hDB
  have hQD : Q ∩ D = r '' stdSimplexBoundary 2 := by
    rw [inter_comm]
    exact hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hr hDS
  have hQ : IsPLBall 2 Q := hS.isPLBall_closure_sdiff ⟨r, hr⟩ hDS
  obtain ⟨q, hq⟩ := hQ
  have hqJ : q '' stdSimplexBoundary 2 = r '' stdSimplexBoundary 2 :=
    (hS.image_stdSimplexBoundary_complement ⟨r, hr⟩ hDS hq).trans hQD
  have hPB : P ⊆ B.space := closure_minimal sdiff_subset (isPolyhedron_space B).isClosed
  have hQA : Q ⊆ A.space := (closure_minimal sdiff_subset hS.isPolyhedron.isClosed).trans
    (boundaryComplex_space_subset 3 A)
  have hPR : P ∩ Q = r '' stdSimplexBoundary 2 := by
    apply Subset.antisymm
    · rintro x ⟨hxP, hxQ⟩
      exact hQD.subset ⟨hxQ, hQA hxQ, hPB hxP⟩
    · intro x hx
      exact ⟨(hPQ.symm.subset hx).1, (hQD.symm.subset hx).1⟩
  have hPD : P ∪ D = B.space := by
    apply Subset.antisymm (union_subset hPB hDB)
    intro x hx
    by_cases hxD : x ∈ D
    · exact Or.inr hxD
    · exact Or.inl (subset_closure ⟨hx, fun hxA => hxD ⟨hxA, hx⟩⟩)
  have hdiff' : S \ B.space = S \ D := by
    ext x
    constructor
    · rintro ⟨hxS, hxB⟩
      exact ⟨hxS, fun hxD => hxB hxD.2⟩
    · rintro ⟨hxS, hxD⟩
      exact ⟨hxS, fun hxB => hxD ⟨boundaryComplex_space_subset 3 A hxS, hxB⟩⟩
  have hnew : (boundaryComplex 3 R).space = P ∪ Q := by
    rw [boundaryComplex_space_of_closure_sdiff K A R hK
      hA.isCombinatorialManifoldWithBoundary hAK hR hRspace]
    exact congrArg (P ∪ ·) (congrArg closure hdiff')
  have hP : IsPolyhedron P := (isPolyhedron_space B).closure_sdiff (isPolyhedron_space A)
  obtain ⟨H, hH, hfix⟩ := exists_isPLHomeomorphOn_replace_ball hP hr hq rfl hqJ hPQ hPR
  rw [hPD, ← hnew] at hH
  exact ⟨H, hH, hfix⟩

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isPLHomeomorphOn_boundary_complement
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hA : IsPLBall 3 A.space)
    (hAK : A.space ⊆ K.space) (hD : IsPLBall 2 (A.space ∩ (boundaryComplex 3 K).space)) :
    ∃ (R : Geometry.SimplicialComplex ℝ E) (H : E → E), R.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 3 R ∧ R.space = closure (K.space \ A.space) ∧
      IsPLHomeomorphOn H (boundaryComplex 3 K).space (boundaryComplex 3 R).space ∧
      EqOn H id (closure ((boundaryComplex 3 K).space \ A.space)) := by
  obtain ⟨R, hRfin, hR, hRspace⟩ :=
    hK.exists_isCombinatorialManifoldWithBoundary_closure_sdiff hA hAK hD
  let _ : Finite R.faces := hRfin.to_subtype
  obtain ⟨H, hH, hfix⟩ :=
    DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_boundary_complement
      K A R hK hA hAK hD hR hRspace
  exact ⟨R, H, hRfin, hR, hRspace, hH, hfix⟩

end DifferentialGeometry.Topology.PiecewiseLinear
