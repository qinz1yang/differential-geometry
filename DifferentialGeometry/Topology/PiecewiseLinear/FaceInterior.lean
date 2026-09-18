import DifferentialGeometry.Topology.PiecewiseLinear.HeightFiber

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem IsHPolytope.eventually_mem_iff_add_of_openSimplex
    {P : Set E} (hP : IsHPolytope P) {s : Finset E} {x y : E}
    (hx : x ∈ openSimplex s) (hy : y ∈ openSimplex s) (hsP : convexHull ℝ (s : Set E) ⊆ P) :
    ∀ᶠ z in 𝓝 x, z ∈ P ↔ z + (y - x) ∈ P := by
  obtain ⟨_, ι, hι, l, c, hP_eq⟩ := hP
  let _ : Finite ι := hι
  have hbound {z : E} (hz : z ∈ convexHull ℝ (s : Set E)) : ∀ i, l i z ≤ c i := by
    have h := hsP hz
    rwa [hP_eq] at h
  have hsbound (i : ι) (w : E) (hw : w ∈ s) : l i w ≤ c i := hbound (subset_convexHull ℝ _ hw) i
  have hineq : ∀ i : ι, ∀ᶠ z in 𝓝 x, l i z ≤ c i ↔ l i (z + (y - x)) ≤ c i := by
    intro i
    have hxiff := affineMap_eq_iff_of_mem_openSimplex_of_le (l i).toAffineMap hx (hsbound i)
    have hyiff := affineMap_eq_iff_of_mem_openSimplex_of_le (l i).toAffineMap hy (hsbound i)
    change (l i x = c i ↔ ∀ w ∈ s, l i w = c i) at hxiff
    change (l i y = c i ↔ ∀ w ∈ s, l i w = c i) at hyiff
    by_cases hactive : l i x = c i
    · have hactive' : l i y = c i := hyiff.mpr (hxiff.mp hactive)
      exact Filter.Eventually.of_forall fun z => by rw [map_add, map_sub, hactive, hactive', sub_self, add_zero]
    · have hxlt : l i x < c i := lt_of_le_of_ne (hbound (openSimplex_subset_convexHull s hx) i) hactive
      have hylt : l i y < c i := lt_of_le_of_ne (hbound (openSimplex_subset_convexHull s hy) i)
        (fun h => hactive (hxiff.mpr (hyiff.mp h)))
      have hnear : ∀ᶠ z in 𝓝 x, l i z < c i :=
        (isOpen_lt (l i).continuous_of_finiteDimensional continuous_const).mem_nhds hxlt
      have hnear' : ∀ᶠ z in 𝓝 x, l i (z + (y - x)) < c i :=
        (isOpen_lt ((l i).continuous_of_finiteDimensional.comp (continuous_id.add continuous_const))
          continuous_const).mem_nhds (by
            change l i (x + (y - x)) < c i
            simpa only [show x + (y - x) = y by abel] using hylt)
      filter_upwards [hnear, hnear'] with z hz hz'
      exact iff_of_true hz.le hz'.le
  filter_upwards [Filter.eventually_all.mpr hineq] with z hz
  rw [hP_eq]
  exact forall_congr' hz

theorem eventually_mem_space_iff_add_of_mem_openSimplex
    (K A : Geometry.SimplicialComplex ℝ E) [Finite A.faces] (hAK : A.faces ⊆ K.faces)
    {s : Finset E} (hs : s ∈ K.faces) {x y : E} (hx : x ∈ openSimplex s) (hy : y ∈ openSimplex s) :
    ∀ᶠ z in 𝓝 x, z ∈ A.space ↔ z + (y - x) ∈ A.space := by
  have hface : ∀ t : A.faces, ∀ᶠ z in 𝓝 x,
      z ∈ convexHull ℝ (t.val : Set E) ↔ z + (y - x) ∈ convexHull ℝ (t.val : Set E) := by
    intro t
    have hT := isHPolytope_convexHull_of_affineIndependent t.val (A.indep t.property)
    by_cases hxt : x ∈ convexHull ℝ (t.val : Set E)
    · have hst := face_subset_of_mem_openSimplex_of_mem_convexHull K hs (hAK t.property) hx hxt
      exact hT.eventually_mem_iff_add_of_openSimplex hx hy (convexHull_mono (Finset.coe_subset.mpr hst))
    · have hyt : y ∉ convexHull ℝ (t.val : Set E) := by
        intro hyt
        have hst := face_subset_of_mem_openSimplex_of_mem_convexHull K hs (hAK t.property) hy hyt
        exact hxt (convexHull_mono (Finset.coe_subset.mpr hst) (openSimplex_subset_convexHull s hx))
      have hnear : ∀ᶠ z in 𝓝 x, z ∉ convexHull ℝ (t.val : Set E) := hT.isClosed.isOpen_compl.mem_nhds hxt
      have hnear' : ∀ᶠ z in 𝓝 x, z + (y - x) ∉ convexHull ℝ (t.val : Set E) :=
        (hT.isClosed.isOpen_compl.preimage (continuous_id.add continuous_const)).mem_nhds
          (by
            change x + (y - x) ∉ convexHull ℝ (t.val : Set E)
            simpa only [show x + (y - x) = y by abel] using hyt)
      filter_upwards [hnear, hnear'] with z hz hz'
      exact iff_of_false hz hz'
  filter_upwards [Filter.eventually_all.mpr hface] with z hz
  constructor
  · intro hzA
    obtain ⟨t, ht, hzt⟩ := A.mem_space_iff.mp hzA
    exact A.convexHull_subset_space ht ((hz ⟨t, ht⟩).mp hzt)
  · intro hzA
    obtain ⟨t, ht, hzt⟩ := A.mem_space_iff.mp hzA
    exact A.convexHull_subset_space ht ((hz ⟨t, ht⟩).mpr hzt)

theorem mem_interior_space_iff_of_mem_openSimplex
    (K A : Geometry.SimplicialComplex ℝ E) [Finite A.faces] (hAK : A.faces ⊆ K.faces)
    {s : Finset E} (hs : s ∈ K.faces) {x y : E} (hx : x ∈ openSimplex s) (hy : y ∈ openSimplex s) :
    x ∈ interior A.space ↔ y ∈ interior A.space := by
  have hstep {p q : E} (hp : p ∈ openSimplex s) (hq : q ∈ openSimplex s)
      (hpint : p ∈ interior A.space) : q ∈ interior A.space := by
    have ht : Filter.Tendsto (fun z => z + (p - q)) (𝓝 q) (𝓝 p) := by
      simpa only [ContinuousAt, show q + (p - q) = p by abel] using
        (show ContinuousAt (fun z : E => z + (p - q)) q from continuousAt_id.add continuousAt_const)
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [eventually_mem_space_iff_add_of_mem_openSimplex K A hAK hs hq hp,
      ht (mem_interior_iff_mem_nhds.mp hpint)] with z hz hz'
    exact hz.mpr hz'
  exact ⟨hstep hx hy, hstep hy hx⟩

theorem mem_frontier_space_iff_of_mem_openSimplex
    (K A : Geometry.SimplicialComplex ℝ E) [Finite A.faces] (hAK : A.faces ⊆ K.faces)
    {s : Finset E} (hs : s ∈ K.faces) {x y : E} (hx : x ∈ openSimplex s) (hy : y ∈ openSimplex s) :
    x ∈ frontier A.space ↔ y ∈ frontier A.space := by
  have hmem : x ∈ A.space ↔ y ∈ A.space := by
    have h := mem_of_mem_nhds (eventually_mem_space_iff_add_of_mem_openSimplex K A hAK hs hx hy)
    change (x ∈ A.space ↔ x + (y - x) ∈ A.space) at h
    simpa only [show x + (y - x) = y by abel] using h
  simp only [(isPolyhedron_space A).isClosed.frontier_eq, mem_sdiff]
  exact and_congr hmem (mem_interior_space_iff_of_mem_openSimplex K A hAK hs hx hy).not

theorem restrict_space_frontier_of_faces_subset
    (K A : Geometry.SimplicialComplex ℝ E) [Finite A.faces] (hAK : A.faces ⊆ K.faces) :
    (restrict K (frontier A.space)).space = frontier A.space := by
  apply Subset.antisymm (restrict_space_subset K _) _
  intro x hx
  have hxA := (isPolyhedron_space A).isClosed.frontier_subset hx
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex K (space_mono_of_faces_subset hAK hxA)
  have hface : convexHull ℝ (s : Set E) ⊆ frontier A.space :=
    (convexHull_subset_closure_openSimplex (K.nonempty_of_mem_faces hs)).trans
      (closure_minimal (fun y hy => (mem_frontier_space_iff_of_mem_openSimplex K A hAK hs hxs hy).mp hx) isClosed_frontier)
  exact (restrict K _).convexHull_subset_space ⟨hs, hface⟩ (openSimplex_subset_convexHull s hxs)

end DifferentialGeometry.Topology.PiecewiseLinear
