import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialTorusCusp

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.GraphManifold.Assembly.FC39P0
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

def cuspEnd (b : Bool) (t : Torus) : cuspSet := cuspProduct (t, Assembly.iccEnd b)

theorem cuspEnd_continuous (b : Bool) : Continuous (cuspEnd b) :=
  cuspProduct.continuous.comp (continuous_id.prodMk continuous_const)

theorem cuspEnd_height (b : Bool) (t : Torus) :
    cliffordHeight (cuspEnd b t).val = if b then -(1 / 4 : ℝ) else 0 := by
  change cliffordHeight (cliffordSeam.{0} (cuspProductParam (t, Assembly.iccEnd b))) = _
  rw [cuspProductPoint_height]
  cases b <;> norm_num [Assembly.iccEnd]

theorem cuspEnd_range (b : Bool) :
    range (cuspEnd b) = {p | cliffordHeight p.val = if b then -(1 / 4 : ℝ) else 0} := by
  ext p
  constructor
  · rintro ⟨t, rfl⟩
    exact cuspEnd_height b t
  · intro hp
    have ht : (cuspProductInv p).2 = Assembly.iccEnd b := by
      apply Subtype.ext
      change -4 * cliffordHeight p.val = (Assembly.iccEnd b).val
      rw [hp]
      cases b <;> norm_num [Assembly.iccEnd]
    refine ⟨(cuspProductInv p).1, ?_⟩
    change cuspProductMap ((cuspProductInv p).1, Assembly.iccEnd b) = p
    rw [← ht]
    exact cuspProduct_right_inv p

theorem cusp_boundary_eq_ends :
    (𝓡∂ 3).boundary cuspSet = range (cuspEnd false) ∪ range (cuspEnd true) := by
  rw [cuspEnd_range false, cuspEnd_range true]
  ext p
  change (𝓡∂ 3).IsBoundaryPoint p ↔ cliffordHeight p.val = 0 ∨
    cliffordHeight p.val = -(1 / 4 : ℝ)
  exact cusp_boundary_iff.trans or_comm

theorem cuspEnd_in_boundary (b : Bool) : range (cuspEnd b) ⊆ (𝓡∂ 3).boundary cuspSet := by
  rw [cusp_boundary_eq_ends]
  cases b
  · exact subset_union_left
  · exact subset_union_right

theorem cuspEnd_preconnected (b : Bool) : IsPreconnected (range (cuspEnd b)) :=
  isPreconnected_range (cuspEnd_continuous b)

def cuspEndPoint (b : Bool) : cuspSet := cuspEnd b (1, 1)

theorem cuspEndPoint_height (b : Bool) :
    cliffordHeight (cuspEndPoint b).val = if b then -(1 / 4 : ℝ) else 0 :=
  cuspEnd_height b (1, 1)

theorem cuspEnd_component (b : Bool) :
    connectedComponentIn ((𝓡∂ 3).boundary cuspSet) (cuspEndPoint b) = range (cuspEnd b) := by
  let C := connectedComponentIn ((𝓡∂ 3).boundary cuspSet) (cuspEndPoint b)
  have hpoint : cuspEndPoint b ∈ (𝓡∂ 3).boundary cuspSet :=
    cuspEnd_in_boundary b (mem_range_self (1, 1))
  have hmem : cuspEndPoint b ∈ C := mem_connectedComponentIn hpoint
  have hsub : C ⊆ (𝓡∂ 3).boundary cuspSet := connectedComponentIn_subset _ _
  have hcont : Continuous (fun p : cuspSet => cliffordHeight p.val) :=
    contMDiff_cliffordHeight.continuous.comp continuous_subtype_val
  have hcover : C ⊆ {p | cliffordHeight p.val < -(1 / 8 : ℝ)} ∪
      {p | -(1 / 8 : ℝ) < cliffordHeight p.val} := by
    intro p hp
    have hh := cusp_boundary_iff.mp (hsub hp)
    rcases hh with hh | hh
    · exact Or.inl (by change cliffordHeight p.val < _; rw [hh]; norm_num)
    · exact Or.inr (by change _ < cliffordHeight p.val; rw [hh]; norm_num)
  have hdis : Disjoint {p : cuspSet | cliffordHeight p.val < -(1 / 8 : ℝ)}
      {p | -(1 / 8 : ℝ) < cliffordHeight p.val} := by
    refine Set.disjoint_left.mpr ?_
    intro p hp hq
    change cliffordHeight p.val < -(1 / 8 : ℝ) at hp
    change -(1 / 8 : ℝ) < cliffordHeight p.val at hq
    linarith
  have hcases := (isPreconnected_connectedComponentIn : IsPreconnected C).subset_or_subset
    (isOpen_lt hcont continuous_const) (isOpen_lt continuous_const hcont) hdis hcover
  apply Set.Subset.antisymm
  · intro p hp
    rw [cuspEnd_range]
    have hh := cusp_boundary_iff.mp (hsub hp)
    cases b
    · have hx : cliffordHeight (cuspEndPoint false).val = 0 := cuspEndPoint_height false
      have hv : -(1 / 8 : ℝ) < cliffordHeight p.val := by
        rcases hcases with hl | hr
        · have hhx := hl hmem
          change cliffordHeight (cuspEndPoint false).val < -(1 / 8 : ℝ) at hhx
          rw [hx] at hhx
          norm_num at hhx
        · exact hr hp
      rcases hh with hh | hh
      · rw [hh] at hv
        norm_num at hv
      · exact hh
    · have hx : cliffordHeight (cuspEndPoint true).val = -(1 / 4 : ℝ) :=
        cuspEndPoint_height true
      have hv : cliffordHeight p.val < -(1 / 8 : ℝ) := by
        rcases hcases with hl | hr
        · exact hl hp
        · have hhx := hr hmem
          change -(1 / 8 : ℝ) < cliffordHeight (cuspEndPoint true).val at hhx
          rw [hx] at hhx
          norm_num at hhx
      rcases hh with hh | hh
      · exact hh
      · rw [hh] at hv
        norm_num at hv
  · exact (cuspEnd_preconnected b).subset_connectedComponentIn
      (mem_range_self (1, 1)) (cuspEnd_in_boundary b)

def cuspModelFace (b : Bool) : ModelBoundaryFace cuspPiece :=
  ⟨range (cuspEnd b), cuspEndPoint b, cuspEnd_in_boundary b (mem_range_self (1, 1)),
    (cuspEnd_component b).symm⟩

theorem cuspModelFace_cases (F : ModelBoundaryFace cuspPiece) :
    F = cuspModelFace false ∨ F = cuspModelFace true := by
  obtain ⟨p, hp, hF⟩ := F.property
  rcases cusp_boundary_iff.mp hp with hh | hh
  · right
    apply Subtype.ext
    rw [hF]
    change connectedComponentIn ((𝓡∂ 3).boundary cuspSet) p = range (cuspEnd true)
    rw [← cuspEnd_component true]
    symm
    apply connectedComponentIn_eq
    rw [cuspEnd_component true, cuspEnd_range true]
    exact hh
  · left
    apply Subtype.ext
    rw [hF]
    change connectedComponentIn ((𝓡∂ 3).boundary cuspSet) p = range (cuspEnd false)
    rw [← cuspEnd_component false]
    symm
    apply connectedComponentIn_eq
    rw [cuspEnd_component false, cuspEnd_range false]
    exact hh

end GC.GraphManifold.Assembly.FC39P0.X135Radial
