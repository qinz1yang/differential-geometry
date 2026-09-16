import DifferentialGeometry.Topology.PiecewiseLinear.CarrierInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.HeightProjection
import DifferentialGeometry.Topology.PiecewiseLinear.HeightPerturbation
import DifferentialGeometry.Topology.PiecewiseLinear.HeightFiber
import DifferentialGeometry.Topology.PiecewiseLinear.HeightSubdivision

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem eventually_exists_isPLHomeomorphOn_preserving_sphere_move_vertices_of_unique_vertex_in_fiber {n : ℕ}
    (K L R : Geometry.SimplicialComplex ℝ E) [Finite R.faces]
    (hK : IsPLSphere (n + 1) K.space) (hLK : IsSubdivision L K) (hLR : L ≤ R)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) {p : E} (hunique : ∀ v ∈ K.vertices, ℓ v = ℓ p → v = p)
    {U : Set E} (hU : IsOpen U) (hRU : R.space ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∃ h : E → E,
      IsPLHomeomorphOn h univ univ ∧ (∀ x, dist (h x) x < ε) ∧ EqOn h id Uᶜ ∧
      EqOn h id K.vertices ∧ h '' K.space = K.space ∧
      EqOn h id (R.vertices ∩ {x | ℓ x ≠ ℓ p}) ∧
      (∀ v ∈ R.vertices, ℓ v = ℓ p → f (h v) = f p) ∧
      ∀ s ∈ R.faces, ∃ a : E →ᵃ[ℝ] E, EqOn h a (convexHull ℝ (s : Set E)) := by
  filter_upwards [eventually_exists_isPLHomeomorphOn_move_fiber_vertices_of_unique_vertex_in_fiber K R ℓ hℓ hunique hU hRU hε]
    with f hf
  obtain ⟨h, hh, hclose, hfix, hfixK, hfixLevel, hlevel, hcarrier, hfaces⟩ := hf
  have hcarL : ∀ v ∈ L.vertices, h v ∈ convexHull ℝ (carrierFace K v : Set E) := by
    intro v hv
    exact openSimplex_subset_convexHull _ (hcarrier v
      ⟨hLR hv, hLK.space_eq.subset (L.vertices_subset_space hv)⟩)
  have himage : h '' K.space = K.space := image_space_eq_of_mem_carrierFace K L hK hLK
    (hh.isPiecewiseAffineOn.continuousOn.mono (subset_univ _))
    (hh.bijOn.injOn.mono (subset_univ _)) (fun s hs => hfaces s (hLR hs)) hcarL
  exact ⟨h, hh, hclose, hfix, fun v hv => hfixK ⟨hLR (hLK.singleton_mem hv), hv⟩,
    himage, hfixLevel, hlevel, hfaces⟩

theorem eventually_exists_isPLHomeomorphOn_preserving_sphere_move_vertices {n : ℕ}
    (K L R : Geometry.SimplicialComplex ℝ E) [Finite R.faces]
    (hK : IsPLSphere (n + 1) K.space) (hLK : IsSubdivision L K) (hLR : L ≤ R)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices) {p : E} (hp : p ∈ K.vertices)
    {U : Set E} (hU : IsOpen U) (hRU : R.space ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∃ h : E → E,
      IsPLHomeomorphOn h univ univ ∧ (∀ x, dist (h x) x < ε) ∧ EqOn h id Uᶜ ∧
      EqOn h id K.vertices ∧ h '' K.space = K.space ∧
      EqOn h id (R.vertices ∩ {x | ℓ x ≠ ℓ p}) ∧
      (∀ v ∈ R.vertices, ℓ v = ℓ p → f (h v) = f p) ∧
      ∀ s ∈ R.faces, ∃ a : E →ᵃ[ℝ] E, EqOn h a (convexHull ℝ (s : Set E)) :=
  eventually_exists_isPLHomeomorphOn_preserving_sphere_move_vertices_of_unique_vertex_in_fiber
    K L R hK hLK hLR ℓ hℓ (fun _ hv h => hinj hv hp h) hU hRU hε

theorem eventually_exists_isPLHomeomorphOn_preserving_sphere_move_fiber {n : ℕ}
    (K L R : Geometry.SimplicialComplex ℝ E) [Finite R.faces]
    (hK : IsPLSphere (n + 1) K.space) (hLK : IsSubdivision L K) (hLR : L ≤ R)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices) {p : E} (hp : p ∈ K.vertices)
    {U : Set E} (hU : IsOpen U) (hRU : R.space ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∃ h : E → E,
      IsPLHomeomorphOn h univ univ ∧ (∀ x, dist (h x) x < ε) ∧ EqOn h id Uᶜ ∧
      EqOn h id K.vertices ∧ h '' K.space = K.space ∧
      (∀ s ∈ R.faces, (∀ v ∈ s, ℓ v = ℓ p) →
        MapsTo h (convexHull ℝ (s : Set E)) {x | f x = f p}) ∧
      ∀ s ∈ R.faces, ∃ a : E →ᵃ[ℝ] E, EqOn h a (convexHull ℝ (s : Set E)) := by
  filter_upwards [eventually_exists_isPLHomeomorphOn_preserving_sphere_move_vertices
    K L R hK hLK hLR ℓ hℓ hinj hp hU hRU hε] with f hf
  obtain ⟨h, hh, hclose, hfix, hfixK, himage, -, hlevel, hfaces⟩ := hf
  refine ⟨h, hh, hclose, hfix, hfixK, himage, ?_, hfaces⟩
  intro s hs hslevel x hx
  obtain ⟨a, ha⟩ := hfaces s hs
  rw [ha hx]
  have hverts : (s : Set E) ⊆ a ⁻¹' {y | f y = f p} := by
    intro v hv
    change f (a v) = f p
    rw [← ha (subset_convexHull ℝ _ hv)]
    exact hlevel v (R.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v))
      (hslevel v hv)
  exact convexHull_min hverts
    (((convex_singleton (f p)).linear_preimage f.toLinearMap).affine_preimage a) hx

theorem eventually_exists_isPLHomeomorphOn_preserving_sphere_eq_height_of_subdivision_of_unique_vertex_in_fiber {n : ℕ}
    (K L R : Geometry.SimplicialComplex ℝ E) [Finite R.faces]
    (hK : IsPLSphere (n + 1) K.space) (hLK : IsSubdivision L K) (hLR : L ≤ R)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) {p : E} (hunique : ∀ v ∈ K.vertices, ℓ v = ℓ p → v = p) (hp : p ∈ K.vertices)
    (hside : ∀ s ∈ R.faces, convexHull ℝ (s : Set E) ⊆ {x | ℓ x ≤ ℓ p} ∨
      convexHull ℝ (s : Set E) ⊆ {x | ℓ p ≤ ℓ x})
    {U : Set E} (hU : IsOpen U) (hRU : R.space ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∃ h : E → E,
      IsPLHomeomorphOn h univ univ ∧ (∀ x, dist (h x) x < ε) ∧ EqOn h id Uᶜ ∧
      EqOn h id K.vertices ∧ h '' K.space = K.space ∧
      ∀ x ∈ R.space, ℓ x = ℓ p ↔ f (h x) = f p := by
  have hRfin : R.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite R.faces)
  have hpR : p ∈ R.vertices := hLR (hLK.singleton_mem hp)
  filter_upwards [eventually_exists_isPLHomeomorphOn_preserving_sphere_move_vertices_of_unique_vertex_in_fiber
    K L R hK hLK hLR ℓ hℓ hunique hU hRU hε, eventually_preserves_strict_order hRfin ℓ]
    with f hf horder
  obtain ⟨h, hh, hclose, hfix, hfixK, himage, hfixLevel, hlevel, hfaces⟩ := hf
  refine ⟨h, hh, hclose, hfix, hfixK, himage, ?_⟩
  have hverts : ∀ v ∈ R.vertices, (ℓ v ≤ ℓ p → f (h v) ≤ f p) ∧
      (ℓ p ≤ ℓ v → f p ≤ f (h v)) ∧ (ℓ v = ℓ p ↔ f (h v) = f p) := by
    intro v hv
    rcases lt_trichotomy (ℓ v) (ℓ p) with hlt | heq | hgt
    · have hfv : f (h v) < f p := by
        rw [hfixLevel ⟨hv, hlt.ne⟩]
        exact horder v hv p hpR hlt
      exact ⟨fun _ => hfv.le, fun hle => (not_le_of_gt hlt hle).elim,
        iff_of_false hlt.ne hfv.ne⟩
    · have hfv := hlevel v hv heq
      exact ⟨fun _ => hfv.le, fun _ => hfv.ge, iff_of_true heq hfv⟩
    · have hfv : f p < f (h v) := by
        rw [hfixLevel ⟨hv, hgt.ne'⟩]
        exact horder p hpR v hv hgt
      exact ⟨fun hle => (not_le_of_gt hgt hle).elim, fun _ => hfv.le,
        iff_of_false hgt.ne' hfv.ne'⟩
  exact fun x hx => eq_height_iff_of_affine_on_faces R ℓ.toLinearMap.toAffineMap
    f.toLinearMap.toAffineMap (ℓ p) (f p) hfaces hside hverts hx

theorem eventually_exists_isPLHomeomorphOn_preserving_sphere_eq_height_of_subdivision {n : ℕ}
    (K L R : Geometry.SimplicialComplex ℝ E) [Finite R.faces]
    (hK : IsPLSphere (n + 1) K.space) (hLK : IsSubdivision L K) (hLR : L ≤ R)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices) {p : E} (hp : p ∈ K.vertices)
    (hside : ∀ s ∈ R.faces, convexHull ℝ (s : Set E) ⊆ {x | ℓ x ≤ ℓ p} ∨
      convexHull ℝ (s : Set E) ⊆ {x | ℓ p ≤ ℓ x})
    {U : Set E} (hU : IsOpen U) (hRU : R.space ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∃ h : E → E,
      IsPLHomeomorphOn h univ univ ∧ (∀ x, dist (h x) x < ε) ∧ EqOn h id Uᶜ ∧
      EqOn h id K.vertices ∧ h '' K.space = K.space ∧
      ∀ x ∈ R.space, ℓ x = ℓ p ↔ f (h x) = f p :=
  eventually_exists_isPLHomeomorphOn_preserving_sphere_eq_height_of_subdivision_of_unique_vertex_in_fiber
    K L R hK hLK hLR ℓ hℓ (fun _ hv h => hinj hv hp h) hp hside hU hRU hε

theorem eventually_exists_isPLHomeomorphOn_preserving_sphere_eq_height_on_polyhedron_of_unique_vertex_in_fiber {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLSphere (n + 1) K.space)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) {p : E} (hunique : ∀ v ∈ K.vertices, ℓ v = ℓ p → v = p) (hp : p ∈ K.vertices)
    {D U : Set E} (hD : IsPolyhedron D) (hU : IsOpen U) (hKU : K.space ⊆ U) (hDU : D ⊆ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∃ h : E → E,
      IsPLHomeomorphOn h univ univ ∧ (∀ x, dist (h x) x < ε) ∧ EqOn h id Uᶜ ∧
      EqOn h id K.vertices ∧ h '' K.space = K.space ∧
      ∀ x ∈ K.space ∪ D, ℓ x = ℓ p ↔ f (h x) = f p := by
  obtain ⟨R, hRfin, hRspace, hRK, -, hside⟩ :=
    exists_triangulation_union_with_halfSpace_faces K hD ℓ.toLinearMap.toAffineMap (ℓ p)
  let _ : Finite R.faces := hRfin.to_subtype
  have hRU : R.space ⊆ U := hRspace.subset.trans (union_subset hKU hDU)
  simpa only [hRspace] using
    eventually_exists_isPLHomeomorphOn_preserving_sphere_eq_height_of_subdivision_of_unique_vertex_in_fiber
      K (restrict R K.space) R hK hRK (restrict_faces_subset R K.space)
      ℓ hℓ hunique hp hside hU hRU hε

theorem eventually_exists_isPLHomeomorphOn_preserving_sphere_eq_height_on_polyhedron {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLSphere (n + 1) K.space)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices) {p : E} (hp : p ∈ K.vertices)
    {D U : Set E} (hD : IsPolyhedron D) (hU : IsOpen U) (hKU : K.space ⊆ U) (hDU : D ⊆ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∃ h : E → E,
      IsPLHomeomorphOn h univ univ ∧ (∀ x, dist (h x) x < ε) ∧ EqOn h id Uᶜ ∧
      EqOn h id K.vertices ∧ h '' K.space = K.space ∧
      ∀ x ∈ K.space ∪ D, ℓ x = ℓ p ↔ f (h x) = f p :=
  eventually_exists_isPLHomeomorphOn_preserving_sphere_eq_height_on_polyhedron_of_unique_vertex_in_fiber
    K hK ℓ hℓ (fun _ hv h => hinj hv hp h) hp hD hU hKU hDU hε

theorem eventually_exists_homeomorph_preserving_sphere_image_fiber_of_unique_vertex_in_fiber {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLSphere (n + 1) K.space)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) {p : E} (hunique : ∀ v ∈ K.vertices, ℓ v = ℓ p → v = p) (hp : p ∈ K.vertices)
    {U : Set E} (hU : IsOpen U) (hKU : K.space ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∃ h : E ≃ₜ E,
      IsPLHomeomorphOn h univ univ ∧ (∀ x, dist (h x) x < ε) ∧ EqOn h id Uᶜ ∧
      EqOn h id K.vertices ∧ h '' K.space = K.space ∧
      h '' (K.space ∩ {x | ℓ x = ℓ p}) = K.space ∩ {x | f x = f p} ∧
      ∀ᶠ y in 𝓝 p, y ∈ h '' {x | ℓ x = ℓ p} ↔ f y = f p := by
  obtain ⟨D, hD, hDU, hDp⟩ :=
    exists_isHPolytope_subset_mem_nhds (hU.mem_nhds (hKU (K.vertices_subset_space hp)))
  filter_upwards [eventually_exists_isPLHomeomorphOn_preserving_sphere_eq_height_on_polyhedron_of_unique_vertex_in_fiber
    K hK ℓ hℓ hunique hp hD.isPolyhedron hU hKU hDU hε] with f hf
  obtain ⟨g, hg, hclose, hfix, hfixK, himage, hlevel⟩ := hf
  let h := (Homeomorph.Set.univ E).symm.trans (hg.homeomorph.trans (Homeomorph.Set.univ E))
  have hhp : h p = p := hfixK hp
  have hsp : h.symm p = p := h.injective ((h.apply_symm_apply p).trans hhp.symm)
  have hfiber : h '' (K.space ∩ {x | ℓ x = ℓ p}) = K.space ∩ {x | f x = f p} := by
    apply Subset.antisymm
    · rintro _ ⟨x, ⟨hxK, hxlevel⟩, rfl⟩
      exact ⟨himage.subset (mem_image_of_mem g hxK), (hlevel x (Or.inl hxK)).mp hxlevel⟩
    · rintro y ⟨hyK, hylevel⟩
      obtain ⟨x, hxK, hxy⟩ := himage.symm.subset hyK
      exact ⟨x, ⟨hxK, (hlevel x (Or.inl hxK)).mpr (by rwa [hxy])⟩, hxy⟩
  refine ⟨h, hg, hclose, hfix, hfixK, himage, hfiber, ?_⟩
  have hnear : ∀ᶠ y in 𝓝 p, h.symm y ∈ D :=
    h.symm.continuous.continuousAt.tendsto.eventually (by rwa [hsp])
  filter_upwards [hnear] with y hy
  have himageplane : y ∈ h '' {x | ℓ x = ℓ p} ↔ ℓ (h.symm y) = ℓ p := by
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [h.symm_apply_apply, mem_ofPred_eq] using hx
    · intro hy'
      exact ⟨h.symm y, hy', h.apply_symm_apply y⟩
  rw [himageplane, hlevel (h.symm y) (Or.inr hy)]
  change f (h (h.symm y)) = f p ↔ f y = f p
  rw [h.apply_symm_apply]

theorem eventually_exists_homeomorph_preserving_sphere_image_fiber {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLSphere (n + 1) K.space)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices) {p : E} (hp : p ∈ K.vertices)
    {U : Set E} (hU : IsOpen U) (hKU : K.space ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∃ h : E ≃ₜ E,
      IsPLHomeomorphOn h univ univ ∧ (∀ x, dist (h x) x < ε) ∧ EqOn h id Uᶜ ∧
      EqOn h id K.vertices ∧ h '' K.space = K.space ∧
      h '' (K.space ∩ {x | ℓ x = ℓ p}) = K.space ∩ {x | f x = f p} ∧
      ∀ᶠ y in 𝓝 p, y ∈ h '' {x | ℓ x = ℓ p} ↔ f y = f p :=
  eventually_exists_homeomorph_preserving_sphere_image_fiber_of_unique_vertex_in_fiber
    K hK ℓ hℓ (fun _ hv h => hinj hv hp h) hp hU hKU hε

end DifferentialGeometry.Topology.PiecewiseLinear
