import DifferentialGeometry.Topology.PiecewiseLinear.FaceProjection
import DifferentialGeometry.Topology.PiecewiseLinear.FiberInterior

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLHomeomorphOn.mem_nhdsWithin_fiber_iff_notMem_image_boundary {n : ℕ}
    (hdimE : Module.finrank ℝ E = n + 2) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    {D : Set E} {g : (Fin (n + 2) → ℝ) → E} (hg : IsPLHomeomorphOn g (stdSimplex ℝ (Fin (n + 2))) D)
    {r : ℝ} (hDr : D ⊆ {x | ℓ x = r}) {q : E} (hq : q ∈ D) :
    D ∈ 𝓝[{x | ℓ x = r}] q ↔ q ∉ g '' stdSimplexBoundary (n + 1) := by
  refine ⟨?_, hg.mem_nhdsWithin_fiber_of_notMem_image_boundary hdimE ℓ hℓ hDr hq⟩
  intro hDnhds hqB
  have hD : IsPLBall (n + 1) D := ⟨g, hg⟩
  obtain ⟨e, π, hleft, hfixed, hheight⟩ := exists_affine_coordinates_of_linear_fiber
    (show Module.finrank ℝ E = (n + 1) + 1 by omega) ℓ hℓ r
  have hπinj : InjOn π D := by
    intro x hx y hy heq
    have h := congrArg e heq
    rwa [(hfixed x).mpr (hDr hx), (hfixed y).mpr (hDr hy)] at h
  have hπ : IsPLHomeomorphOn π D (π '' D) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hD.isPolyhedron
      ((isPiecewiseAffineOn_of_affine π.toAffineMap isOpen_univ).mono_of_isPolyhedron hD.isPolyhedron (subset_univ D))
      ⟨fun x hx => mem_image_of_mem π hx, hπinj, fun _ hy => hy⟩
  have hecont : Filter.Tendsto e (𝓝 (π q)) (𝓝 q) := by
    simpa only [ContinuousAt, (hfixed q).mpr (hDr hq)] using
      (show ContinuousAt e (π q) from e.continuous_of_finiteDimensional.continuousAt)
  have hewithin : Filter.Tendsto e (𝓝 (π q)) (𝓝[{x | ℓ x = r}] q) :=
    tendsto_nhdsWithin_iff.mpr ⟨hecont, Filter.Eventually.of_forall hheight⟩
  have hπqint : π q ∈ interior (π '' D) := by
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hewithin hDnhds] with y hy
    exact ⟨e y, hy, hleft y⟩
  have hπqBd : π q ∈ frontier (π '' D) := by
    rw [← (hg.trans hπ).image_stdSimplexBoundary]
    obtain ⟨z, hz, rfl⟩ := hqB
    exact ⟨z, hz, rfl⟩
  exact hπqBd.2 hπqint

open Classical in
theorem mem_frontier_space_iff_mem_boundaryComplex_fiber {n : ℕ}
    (K A L : Geometry.SimplicialComplex ℝ E) [Finite A.faces] [Finite L.faces]
    (hAK : A.faces ⊆ K.faces) (hdim : Module.finrank ℝ E = n + 2)
    (hL : IsPLBall (n + 1) L.space) {s : Finset E} (hs : s ∈ K.faces)
    {x : E} (hx : x ∈ openSimplex s) (hxA : x ∈ A.space)
    {u v : E} (hu : u ∈ s) (hv : v ∈ s) (ℓ : E →ₗ[ℝ] ℝ) (hℓuv : ℓ v ≠ ℓ u)
    (hLspace : L.space = A.space ∩ {y | ℓ y = ℓ x}) :
    x ∈ frontier A.space ↔ x ∈ (boundaryComplex (n + 1) L).space := by
  have hℓ : ℓ ≠ 0 := by
    intro h
    apply hℓuv
    simp only [h, LinearMap.zero_apply]
  obtain ⟨g, hg⟩ := hL
  have hBd : (boundaryComplex (n + 1) L).space = g '' stdSimplexBoundary (n + 1) := by
    rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex L hg, simplexBoundary_stdVertices_space]
  have hxL : x ∈ L.space := hLspace.symm ▸ ⟨hxA, rfl⟩
  have hLH : L.space ⊆ {y | ℓ y = ℓ x} := by rw [hLspace]; exact inter_subset_right
  have hrelative := hg.mem_nhdsWithin_fiber_iff_notMem_image_boundary hdim ℓ hℓ hLH hxL
  have hinterior := mem_interior_space_iff_mem_nhdsWithin_fiber K A hAK hs hx hu hv ℓ hℓuv
  rw [← hLspace] at hinterior
  have hiff := hinterior.trans hrelative
  constructor
  · intro hfront
    by_contra hnot
    exact hfront.2 (hiff.mpr (by rwa [← hBd]))
  · intro hboundary
    exact ⟨subset_closure hxA, fun hint => hiff.mp hint (hBd ▸ hboundary)⟩

open Classical in
theorem mem_frontier_space_iff_mem_boundaryComplex_fiber_of_injOn {n : ℕ}
    (K A L : Geometry.SimplicialComplex ℝ E) [Finite A.faces] [Finite L.faces]
    (hAK : A.faces ⊆ K.faces) (hdim : Module.finrank ℝ E = n + 2)
    (hL : IsPLBall (n + 1) L.space) (ℓ : E →ₗ[ℝ] ℝ) (hinj : InjOn ℓ K.vertices)
    {r : ℝ} (hLspace : L.space = A.space ∩ {y | ℓ y = r})
    {x : E} (hxA : x ∈ A.space) (hxr : ℓ x = r) (hxnot : x ∉ K.vertices) :
    x ∈ frontier A.space ↔ x ∈ (boundaryComplex (n + 1) L).space := by
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex K (space_mono_of_faces_subset hAK hxA)
  have hcard : 1 < s.card := by
    by_contra hsmall
    have hpos := Finset.card_pos.mpr (K.nonempty_of_mem_faces hs)
    have hone : s.card = 1 := by omega
    obtain ⟨u, rfl⟩ := Finset.card_eq_one.mp hone
    have hxu : x = u := eq_of_mem_openSimplex_singleton hxs
    exact hxnot (hxu.symm ▸ hs)
  obtain ⟨u, v, hu, hv, huv⟩ := Finset.one_lt_card_iff.mp hcard
  have hvert (w : E) (hw : w ∈ s) : w ∈ K.vertices :=
    K.down_closed hs (Finset.singleton_subset_iff.mpr hw) (Finset.singleton_nonempty w)
  have hheight : ℓ v ≠ ℓ u := fun heq => huv (hinj (hvert v hv) (hvert u hu) heq).symm
  exact mem_frontier_space_iff_mem_boundaryComplex_fiber K A L hAK hdim hL hs hxs hxA hu hv ℓ hheight
    (by simpa only [hxr] using hLspace)

end DifferentialGeometry.Topology.PiecewiseLinear
