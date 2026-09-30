import DifferentialGeometry.Topology.PiecewiseLinear.HeightSides

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mem_openSimplex_of_forall_mem_convexHull_iff
    (K : Geometry.SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces)
    {x y : E} (hx : x ∈ openSimplex s) (hy : y ∈ K.space)
    (hfaces : ∀ t ∈ K.faces,
      y ∈ convexHull ℝ (t : Set E) ↔ x ∈ convexHull ℝ (t : Set E)) :
    y ∈ openSimplex s := by
  have ht := carrierFace_mem hy
  have hyt := mem_openSimplex_carrierFace hy
  have hys : y ∈ convexHull ℝ (s : Set E) :=
    (hfaces s hs).mpr (openSimplex_subset_convexHull s hx)
  have hxt : x ∈ convexHull ℝ (carrierFace K y : Set E) :=
    (hfaces _ ht).mp (openSimplex_subset_convexHull _ hyt)
  have heq : s = carrierFace K y := Finset.Subset.antisymm
    (face_subset_of_mem_openSimplex_of_mem_convexHull K hs ht hx hxt)
    (face_subset_of_mem_openSimplex_of_mem_convexHull K ht hs hyt hys)
  rwa [heq]

theorem openSimplex_inter_fiber_subset_of_mem_levelPolygon [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 2 K)
    (hdimE : Module.finrank ℝ E = 3) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hinj : InjOn ℓ K.vertices) {p : E} (hp : p ∈ K.vertices)
    {J : Set E} (hJ : J ∈ levelPolygons K.space ℓ (ℓ p))
    {s : Finset E} (hs : s ∈ K.faces) {q : E} (hqs : q ∈ openSimplex s)
    (hqJ : q ∈ J) (hqp : q ≠ p) :
    openSimplex s ∩ {x | ℓ x = ℓ p} ⊆ J := by
  have hpnot : p ∉ openSimplex s := by
    intro hps
    have hs_eq := face_eq_of_mem_openSimplex K hs hp hps (mem_openSimplex_singleton p)
    have hqp' : q = p := by
      simpa only [hs_eq, Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] using
        openSimplex_subset_convexHull s hqs
    exact hqp hqp'
  let U := openSimplex s ∩ {x | ℓ x = ℓ p}
  have hU : IsPreconnected U :=
    ((convex_openSimplex s).inter ((convex_singleton (ℓ p)).linear_preimage ℓ)).isPreconnected
  have hUK : U ⊆ K.space ∩ {x | ℓ x = ℓ p} := fun _ hx =>
    ⟨K.convexHull_subset_space hs (openSimplex_subset_convexHull s hx.1), hx.2⟩
  let _ : PreconnectedSpace U := Subtype.preconnectedSpace hU
  have hclosed : IsClosed (Subtype.val ⁻¹' J : Set U) :=
    hJ.1.isPolyhedron.isClosed.preimage continuous_subtype_val
  have hopen : IsOpen (Subtype.val ⁻¹' J : Set U) := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    have hlocal := eventually_mem_fiber_iff_mem_levelPolygon_of_ne_vertex K hK hdimE ℓ hℓ
      hinj hp hJ hy (fun heq => hpnot (heq ▸ y.property.1))
    have hn : J ∈ 𝓝[U] (y : E) := by
      apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      refine ⟨{z | z ∈ K.space ∩ {w | ℓ w = ℓ p} → z ∈ J}, ?_, ?_⟩
      · exact hlocal.mono fun _ hz => hz.mp
      · rintro z ⟨hz, hzU⟩
        exact hz (hUK hzU)
    rwa [nhdsWithin_eq_map_subtype_coe] at hn
  have hfull : (Subtype.val ⁻¹' J : Set U) = univ :=
    IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨q, hqs, (hJ.2 hqJ).2⟩, hqJ⟩
  intro x hx
  exact (show (⟨x, hx⟩ : U) ∈ (Subtype.val ⁻¹' J : Set U) by rw [hfull]; trivial)

end DifferentialGeometry.Topology.PiecewiseLinear
