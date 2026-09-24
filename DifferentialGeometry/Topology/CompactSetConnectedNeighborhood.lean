import DifferentialGeometry.Topology.ConnectedCompactNeighborhood

noncomputable section

open Set

namespace DifferentialGeometry

theorem exists_isOpen_isConnected_isCompact_closure_superset
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [LocallyPathConnectedSpace X] [ConnectedSpace X]
    (x : X) {K : Set X} (hK : IsCompact K) :
    ∃ U : Set X,
      IsOpen U ∧ IsConnected U ∧ x ∈ U ∧ K ⊆ U ∧ IsCompact (closure U) := by
  classical
  choose V hVopen hVconn hxV hyV hVcompact using
    fun y : X => exists_isOpen_isConnected_isCompact_closure x y
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover V hVopen
    (fun y hy => mem_iUnion.mpr ⟨y, hyV y⟩)
  let J : Finset X := insert x F
  let U : Set X := ⋃ y ∈ J, V y
  have hxU : x ∈ U := mem_iUnion₂.mpr ⟨x, Finset.mem_insert_self x F, hxV x⟩
  have hconn : IsPreconnected U := by
    have hh : IsPreconnected (⋃ y : J, V y.val) :=
      isPreconnected_iUnion ⟨x, mem_iInter.mpr (fun y => hxV y.val)⟩
        (fun y => (hVconn y.val).isPreconnected)
    convert hh using 1
    ext z
    simp [U]
  refine ⟨U, isOpen_iUnion (fun y => isOpen_iUnion (fun _ => hVopen y)),
    ⟨⟨x, hxU⟩, hconn⟩, hxU, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.mp (hF hy)
    exact mem_iUnion₂.mpr ⟨z, Finset.mem_insert_of_mem hz, hyz⟩
  · rw [show U = ⋃ y ∈ J, V y from rfl, J.closure_biUnion]
    exact J.isCompact_biUnion (fun y _ => hVcompact y)

end DifferentialGeometry
