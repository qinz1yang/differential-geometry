import DifferentialGeometry.Topology.PiecewiseLinear.Barycentric
import DifferentialGeometry.Topology.PiecewiseLinear.PiecewiseAffine

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def closedStar (K : Geometry.SimplicialComplex ℝ E) (x : E) : Set E :=
  ⋃ s ∈ {s ∈ K.faces | x ∈ convexHull ℝ (s : Set E)}, convexHull ℝ (s : Set E)

theorem closedStar_mem_nhdsWithin (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (x : E) :
    closedStar K x ∈ 𝓝[K.space] x := by
  set B : Set E := ⋃ s ∈ {s ∈ K.faces | x ∉ convexHull ℝ (s : Set E)}, convexHull ℝ (s : Set E)
    with hBdef
  have hB : IsClosed B :=
    ((Set.toFinite K.faces).subset (Set.sep_subset _ _)).isClosed_biUnion fun s _ =>
      (s.finite_toSet.isCompact_convexHull ℝ).isClosed
  have hxB : x ∉ B := by
    intro h
    rw [hBdef, mem_iUnion₂] at h
    obtain ⟨s, ⟨_, hxs⟩, hx'⟩ := h
    exact hxs hx'
  have hBc : Bᶜ ∈ 𝓝 x := hB.isOpen_compl.mem_nhds hxB
  refine Filter.mem_of_superset (inter_mem_nhdsWithin K.space hBc) ?_
  rintro y ⟨hyK, hyB⟩
  obtain ⟨s, hs, hys⟩ := K.mem_space_iff.mp hyK
  by_cases hxs : x ∈ convexHull ℝ (s : Set E)
  · exact mem_biUnion (s := {s ∈ K.faces | x ∈ convexHull ℝ (s : Set E)})
      (t := fun s => convexHull ℝ (s : Set E)) ⟨hs, hxs⟩ hys
  · exact absurd (mem_biUnion (s := {s ∈ K.faces | x ∉ convexHull ℝ (s : Set E)})
      (t := fun s => convexHull ℝ (s : Set E)) ⟨hs, hxs⟩ hys) hyB

theorem isPiecewiseAffineOn_space_of_forall_face [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {f : E → F}
    (hf : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E))) :
    IsPiecewiseAffineOn f K.space := by
  intro x _
  unfold IsPiecewiseAffineWithinAt
  let S : Set (Finset E) := {s ∈ K.faces | x ∈ convexHull ℝ (s : Set E)}
  have hS : S.Finite := (Set.toFinite K.faces).subset (Set.sep_subset _ _)
  have := hS.to_subtype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin S
  choose A hA using hf
  refine ⟨Fin n, inferInstance, fun i => convexHull ℝ ((e.symm i : Finset E) : Set E),
    fun i => A _ (e.symm i).2.1, fun i => ?_, ?_⟩
  · exact ⟨isHPolytope_convexHull_of_affineIndependent _ (K.indep (e.symm i).2.1),
      K.convexHull_subset_space (e.symm i).2.1, hA _ _⟩
  have hunion : (⋃ i : Fin n, convexHull ℝ ((e.symm i : Finset E) : Set E)) = closedStar K x := by
    rw [closedStar, biUnion_eq_iUnion]
    exact e.symm.surjective.iUnion_comp fun s : S => convexHull ℝ ((s : Finset E) : Set E)
  rw [hunion]
  exact closedStar_mem_nhdsWithin K x

theorem exists_affineMap_eqOn [FiniteDimensional ℝ E] {s : Finset E}
    (hs : AffineIndependent ℝ ((↑) : s → E)) (q : E → F) :
    ∃ A : E →ᵃ[ℝ] F, ∀ v ∈ s, A v = q v := by
  classical
  obtain ⟨t, hst, hti, htop⟩ := exists_subset_affineIndependent_affineSpan_eq_top hs
  have htf : t.Finite := finite_set_of_fin_dim_affineIndependent ℝ hti
  have : Finite t := htf.to_subtype
  let : Fintype t := Fintype.ofFinite t
  let b : AffineBasis t ℝ E := ⟨((↑) : t → E), hti, by rw [Subtype.range_coe]; exact htop⟩
  refine ⟨(Finset.univ.affineCombination ℝ fun i : t => q i).comp b.coords, fun v hv => ?_⟩
  have hvb : v = b ⟨v, hst hv⟩ := rfl
  rw [AffineMap.comp_apply]
  conv_lhs => rw [hvb]
  refine Finset.affineCombination_of_eq_one_of_eq_zero _ _ _
    (Finset.mem_univ (⟨v, hst hv⟩ : t)) ?_ ?_
  · rw [b.coords_apply, b.coord_apply_eq]
  · intro j _ hj
    rw [b.coords_apply, b.coord_apply_ne hj]

end DifferentialGeometry.Topology.PiecewiseLinear
