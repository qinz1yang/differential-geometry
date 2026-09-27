import DifferentialGeometry.Topology.PiecewiseLinear.Combinatorial
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubdivision

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_isSubdivision_closedStar_subset_of_mem_nhds
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {p : E} (hp : p ∈ K.space)
    {U : Set E} (hU : U ∈ 𝓝 p) :
    ∃ R : Geometry.SimplicialComplex ℝ E, IsSubdivision R K ∧ R.faces.Finite ∧
      ({p} : Finset E) ∈ R.faces ∧ closedStar R p ⊆ U := by
  classical
  obtain ⟨V, hVU, hV, hpV⟩ := mem_nhds_iff.mp hU
  obtain ⟨K₀, hK₀, hK₀fin, hp₀⟩ := exists_isSubdivision_singleton_mem K hp
  let _ : Finite K₀.faces := hK₀fin.to_subtype
  let W : Bool → Set E := fun b => if b then V else {p}ᶜ
  have hW : ∀ b, IsOpen (((↑) : K₀.space → E) ⁻¹' W b) := by
    intro b
    cases b
    · exact isClosed_singleton.isOpen_compl.preimage continuous_subtype_val
    · exact hV.preimage continuous_subtype_val
  have hcover : K₀.space ⊆ ⋃ b, W b := by
    intro x _
    by_cases hxp : x = p
    · exact mem_iUnion.mpr ⟨true, hxp ▸ hpV⟩
    · exact mem_iUnion.mpr ⟨false, hxp⟩
  obtain ⟨R, hR, hRfin, hstars⟩ :=
    exists_isSubdivision_closedStars_subset_cover K₀ W hW hcover
  have hpR : ({p} : Finset E) ∈ R.faces := hR.singleton_mem hp₀
  obtain ⟨b, hb⟩ := hstars {p} hpR
  have hstar : closedStar R p ⊆ W b := by
    simpa only [Finset.mem_singleton, iUnion_iUnion_eq_left] using hb
  refine ⟨R, hR.trans hK₀, hRfin, hpR, ?_⟩
  cases b
  · exact False.elim (hstar (mem_closedStar_self R hpR) rfl)
  · exact hstar.trans hVU

theorem IsCombinatorialManifoldWithBoundary.exists_isPLBall_subset_of_mem_nhdsWithin
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) {p : E} (hp : p ∈ K.space)
    {U : Set E} (hU : U ∈ 𝓝[K.space] p) :
    ∃ D : Set E, IsPLBall (n + 1) D ∧ D ⊆ K.space ∩ U ∧ D ∈ 𝓝[K.space] p := by
  classical
  obtain ⟨V, hV, hVU⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hU
  obtain ⟨R, hR, hRfin, hpR, hRV⟩ :=
    exists_isSubdivision_closedStar_subset_of_mem_nhds K hp hV
  let _ : Finite R.faces := hRfin.to_subtype
  have hball : IsPLBall (n + 1) (closedStar R p) := by
    rcases hK.of_isSubdivision hR p hpR with hs | hb
    · exact isPLBall_closedStar R hpR hs
    · rw [closedStar_eq_coneComplex_space R hpR]
      exact (isConeBase_geometricLink R).isPLBall_of_isPLBall hb
  have hsub : closedStar R p ⊆ K.space := by
    rw [← hR.space_eq]
    exact closedStar_subset_space R p
  refine ⟨closedStar R p, hball, fun x hx => ⟨hsub hx, hVU ⟨hRV hx, hsub hx⟩⟩, ?_⟩
  rw [← hR.space_eq]
  exact closedStar_mem_nhdsWithin R p

theorem IsCombinatorialManifold.exists_isPLBall_subset_of_mem_nhds
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifold (n + 1) K) {p : E} (hp : p ∈ K.space)
    {U : Set E} (hU : U ∈ 𝓝 p) :
    ∃ D : Set E, IsPLBall (n + 1) D ∧ D ⊆ K.space ∩ U ∧ D ∈ 𝓝[K.space] p :=
  hK.isCombinatorialManifoldWithBoundary.exists_isPLBall_subset_of_mem_nhdsWithin hp
    (mem_nhdsWithin_of_mem_nhds hU)

end DifferentialGeometry.Topology.PiecewiseLinear
