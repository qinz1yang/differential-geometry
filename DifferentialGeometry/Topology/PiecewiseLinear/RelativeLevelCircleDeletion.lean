import DifferentialGeometry.Topology.PiecewiseLinear.HeightFiber
import DifferentialGeometry.Topology.PiecewiseLinear.HeightProjection
import DifferentialGeometry.Topology.PiecewiseLinear.SingularLevelPolygons

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem eventually_exists_vertexMap_eq_height_off_fixed
    (R : Geometry.SimplicialComplex ℝ E) [Finite R.faces]
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) {p : E} (B : Set E) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∃ φ : E → E,
      EqOn φ id B ∧ EqOn φ id {x | ℓ x ≠ ℓ p} ∧
      (∀ v ∈ R.vertices, dist (φ v) v < δ) ∧
      ∀ v ∈ R.vertices, ℓ v = ℓ p → v ∉ B → f (φ v) = f p := by
  classical
  have hdir : ∃ d : E, ℓ d ≠ 0 := by
    by_contra! h
    exact hℓ (by ext d; exact h d)
  obtain ⟨d, hd⟩ := hdir
  let P : (E →L[ℝ] ℝ) → E → E → Prop := fun f v y =>
    dist y v < δ ∧ (v ∈ B → y = v) ∧ (ℓ v ≠ ℓ p → y = v) ∧
      (ℓ v = ℓ p → v ∉ B → f y = f p)
  have hpoint : ∀ v : R.vertices, ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∃ y, P f v y := by
    intro v
    by_cases hvB : (v : E) ∈ B
    · exact Filter.Eventually.of_forall fun _ =>
        ⟨v, by simpa only [dist_self] using hδ, fun _ => rfl, fun _ => rfl,
          fun _ hvnot => (hvnot hvB).elim⟩
    · by_cases hvlevel : ℓ (v : E) = ℓ p
      · filter_upwards [eventually_exists_eq_height_of_mem_ray_nhds ℓ hvlevel hd
          (U := univ) (Filter.Eventually.of_forall fun _ => mem_univ _) hδ] with f hf
        obtain ⟨y, -, hfy, hyclose⟩ := hf
        exact ⟨y, hyclose, fun h => (hvB h).elim, fun h => (h hvlevel).elim,
          fun _ _ => hfy⟩
      · exact Filter.Eventually.of_forall fun _ =>
          ⟨v, by simpa only [dist_self] using hδ, fun h => (hvB h).elim, fun _ => rfl,
            fun h => (hvlevel h).elim⟩
  have hvertices : R.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite R.faces)
  let _ : Finite R.vertices := hvertices.to_subtype
  have hall : ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∀ v : R.vertices, ∃ y, P f v y :=
    Filter.eventually_all.mpr hpoint
  filter_upwards [hall] with f hf
  let φ : E → E := fun v =>
    if hv : v ∈ R.vertices then Classical.choose (hf ⟨v, hv⟩) else v
  have hφ : ∀ v ∈ R.vertices, P f v (φ v) := by
    intro v hv
    simpa only [φ, dif_pos hv] using Classical.choose_spec (hf ⟨v, hv⟩)
  have hfix : ∀ v ∉ R.vertices, φ v = v := fun v hv => dif_neg hv
  refine ⟨φ, ?_, ?_, fun v hv => (hφ v hv).1, fun v hv => (hφ v hv).2.2.2⟩
  · intro v hvB
    by_cases hvR : v ∈ R.vertices
    · exact (hφ v hvR).2.1 hvB
    · exact hfix v hvR
  · intro v hvlevel
    by_cases hvR : v ∈ R.vertices
    · exact (hφ v hvR).2.2.1 hvlevel
    · exact hfix v hvR

theorem eventually_exists_isPLHomeomorphOn_move_level_vertices_off_subcomplex
    (R N : Geometry.SimplicialComplex ℝ E) [Finite R.faces]
    (hNR : N.faces ⊆ R.faces) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) {p : E}
    {U : Set E} (hU : IsOpen U) (hRU : R.space ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∃ h : E → E,
      IsPLHomeomorphOn h univ univ ∧ (∀ x, dist (h x) x < ε) ∧ EqOn h id Uᶜ ∧
      EqOn h id N.space ∧ EqOn h id (R.vertices ∩ {x | ℓ x ≠ ℓ p}) ∧
      (∀ v ∈ R.vertices, ℓ v = ℓ p → v ∉ N.vertices → f (h v) = f p) ∧
      ∀ s ∈ R.faces, ∃ a : E →ᵃ[ℝ] E, EqOn h a (convexHull ℝ (s : Set E)) := by
  obtain ⟨δ, hδ, hext⟩ :=
    exists_isPLHomeomorphOn_extension_of_small_vertex_perturbation R hU hRU hε
  filter_upwards [eventually_exists_vertexMap_eq_height_off_fixed R ℓ hℓ N.vertices hδ]
    with f hf
  obtain ⟨φ, hφN, hφlevel, hφclose, hφheight⟩ := hf
  obtain ⟨h, hh, hhclose, hhfix, hhφ⟩ := hext φ hφclose
  have hvertices : EqOn h φ R.vertices := by
    intro v hv
    rw [hhφ (R.vertices_subset_space hv), simplicialMap_vertex R φ hv]
  refine ⟨h, hh, hhclose, hhfix, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := N.mem_space_iff.mp hx
    have hxR : x ∈ R.space := R.convexHull_subset_space (hNR hs) hxs
    change h x = x
    rw [hhφ hxR, simplicialMap_eq_of_mem R φ (hNR hs) hxs]
    calc
      ∑ v ∈ s, weights s x v • φ v = ∑ v ∈ s, weights s x v • v := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [hφN (N.down_closed hs (Finset.singleton_subset_iff.mpr hv)
          (Finset.singleton_nonempty v))]
        rfl
      _ = x := sum_weights_smul hxs
  · intro v hv
    exact (hvertices hv.1).trans (hφlevel hv.2)
  · intro v hv hvlevel hvN
    rw [hvertices hv]
    exact hφheight v hv hvlevel hvN
  · intro s hs
    obtain ⟨a, ha⟩ := exists_affineMap_eqOn_simplicialMap R φ hs
    exact ⟨a, (hhφ.mono (R.convexHull_subset_space hs)).trans ha⟩

omit [FiniteDimensional ℝ E] in
theorem convexHull_subset_subcomplex_of_level_face_boundary_germ
    (M B : Geometry.SimplicialComplex ℝ E) (hBM : B.faces ⊆ M.faces)
    (ℓ : E →L[ℝ] ℝ) {p : E} {s : Finset E} (hs : s ∈ M.faces)
    (hslevel : ∀ v ∈ s, ℓ v = ℓ p) {v : E} (hv : v ∈ s)
    (hlocal : ∀ᶠ x in 𝓝 v, x ∈ B.space ↔ x ∈ M.space ∧ ℓ x = ℓ p) :
    convexHull ℝ (s : Set E) ⊆ B.space := by
  have hslevel' : convexHull ℝ (s : Set E) ⊆ {x | ℓ x = ℓ p} := by
    apply convexHull_min
    · exact hslevel
    · exact (convex_singleton (ℓ p)).linear_preimage ℓ.toLinearMap
  have hvcl : v ∈ closure (openSimplex s) :=
    convexHull_subset_closure_openSimplex (M.nonempty_of_mem_faces hs)
      (subset_convexHull ℝ (s : Set E) hv)
  obtain ⟨y, hys, hylocal⟩ :=
    ((mem_closure_iff_frequently.mp hvcl).and_eventually hlocal).exists
  have hyM : y ∈ M.space :=
    M.convexHull_subset_space hs (openSimplex_subset_convexHull s hys)
  have hyB : y ∈ B.space :=
    hylocal.mpr ⟨hyM, hslevel' (openSimplex_subset_convexHull s hys)⟩
  obtain ⟨t, ht, hyt⟩ := B.mem_space_iff.mp hyB
  have hst : s ⊆ t :=
    face_subset_of_mem_openSimplex_of_mem_convexHull M hs (hBM ht) hys hyt
  exact (convexHull_mono (Finset.coe_subset.mpr hst)).trans
    (B.convexHull_subset_space ht)
omit [FiniteDimensional ℝ E] in
theorem eq_height_iff_of_move_level_vertices_off_subcomplex
    (R M N : Geometry.SimplicialComplex ℝ E)
    (hMR : M.faces ⊆ R.faces) (hNR : N.faces ⊆ R.faces)
    (ℓ f : E →L[ℝ] ℝ) {p : E} (hpR : p ∈ R.vertices) {J : Set E}
    (hMN : M.space ∩ N.space = J) {h : E → E}
    (hside : ∀ s ∈ M.faces,
      (convexHull ℝ (s : Set E) ⊆ {x | ℓ x ≤ ℓ p} ∧ ∀ v ∈ s, f (h v) ≤ f p) ∨
      (convexHull ℝ (s : Set E) ⊆ {x | ℓ p ≤ ℓ x} ∧ ∀ v ∈ s, f p ≤ f (h v)))
    (hfaces : ∀ s ∈ R.faces, ∃ a : E →ᵃ[ℝ] E, EqOn h a (convexHull ℝ (s : Set E)))
    (heqvertices : ∀ v ∈ M.vertices,
      f (h v) = f p ↔ ℓ v = ℓ p ∧ (v ∉ N.vertices ∨ v = p))
    (hzero : ∀ s ∈ M.faces, (∀ v ∈ s, ℓ v = ℓ p) →
      ∀ v ∈ s, v ∈ N.vertices → v = p ∨ convexHull ℝ (s : Set E) ⊆ J)
    {x : E} (hx : x ∈ M.space) :
    f (h x) = f p ↔ ℓ x = ℓ p ∧ x ∉ J \ {p} := by
  classical
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex M hx
  have hsR : s ∈ R.faces := hMR hs
  have hvsM : ∀ v ∈ s, v ∈ M.vertices := fun v hv =>
    M.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  obtain ⟨a, ha⟩ := hfaces s hsR
  have hav : ∀ v ∈ s, a v = h v := fun v hv =>
    (ha (subset_convexHull ℝ (s : Set E) hv)).symm
  let b : E →ᵃ[ℝ] ℝ := f.toLinearMap.toAffineMap.comp a
  have hnew : f (h x) = f p ↔ ∀ v ∈ s, f (h v) = f p := by
    rw [ha (openSimplex_subset_convexHull s hxs)]
    change b x = f p ↔ ∀ v ∈ s, f (h v) = f p
    rcases hside s hs with hle | hge
    · have hb : ∀ v ∈ s, b v ≤ f p := by
        intro v hv
        change f (a v) ≤ f p
        rw [hav v hv]
        exact hle.2 v hv
      rw [affineMap_eq_iff_of_mem_openSimplex_of_le b hxs hb]
      apply forall₂_congr
      intro v hv
      change f (a v) = f p ↔ f (h v) = f p
      rw [hav v hv]
    · have hb : ∀ v ∈ s, f p ≤ b v := by
        intro v hv
        change f p ≤ f (a v)
        rw [hav v hv]
        exact hge.2 v hv
      rw [affineMap_eq_iff_of_mem_openSimplex_of_ge b hxs hb]
      apply forall₂_congr
      intro v hv
      change f (a v) = f p ↔ f (h v) = f p
      rw [hav v hv]
  have hold : ℓ x = ℓ p ↔ ∀ v ∈ s, ℓ v = ℓ p := by
    rcases hside s hs with hle | hge
    · exact affineMap_eq_iff_of_mem_openSimplex_of_le ℓ.toLinearMap.toAffineMap hxs
        (fun v hv => hle.1 (subset_convexHull ℝ _ hv))
    · exact affineMap_eq_iff_of_mem_openSimplex_of_ge ℓ.toLinearMap.toAffineMap hxs
        (fun v hv => hge.1 (subset_convexHull ℝ _ hv))
  constructor
  · intro hxnew
    have hsnew := hnew.mp hxnew
    have hsold : ∀ v ∈ s, ℓ v = ℓ p := fun v hv =>
      ((heqvertices v (hvsM v hv)).mp (hsnew v hv)).1
    refine ⟨hold.mpr hsold, ?_⟩
    rintro ⟨hxJ, hxp⟩
    have hxN : x ∈ N.space := (hMN.symm.subset hxJ).2
    obtain ⟨t, ht, hxt⟩ := N.mem_space_iff.mp hxN
    have hst : s ⊆ t :=
      face_subset_of_mem_openSimplex_of_mem_convexHull R hsR (hNR ht) hxs hxt
    have hsp : (s : Set E) ⊆ {p} := by
      intro v hv
      have hvN : v ∈ N.vertices :=
        N.down_closed ht (Finset.singleton_subset_iff.mpr (hst hv))
          (Finset.singleton_nonempty v)
      exact ((heqvertices v (hvsM v hv)).mp (hsnew v hv)).2.resolve_left (not_not.mpr hvN)
    have hxp' : x = p := by
      have : x ∈ ({p} : Set E) :=
        convexHull_min hsp (convex_singleton p) (openSimplex_subset_convexHull s hxs)
      simpa only [mem_singleton_iff] using this
    exact hxp (by simpa only [mem_singleton_iff] using hxp')
  · rintro ⟨hxold, hxnot⟩
    have hsold := hold.mp hxold
    apply hnew.mpr
    intro v hv
    apply (heqvertices v (hvsM v hv)).mpr
    refine ⟨hsold v hv, ?_⟩
    by_cases hvN : v ∈ N.vertices
    · right
      by_cases hvp : v = p
      · exact hvp
      rcases hzero s hs hsold v hv hvN with hvp' | hsJ
      · exact (hvp hvp').elim
      · have hxJ : x ∈ J := hsJ (openSimplex_subset_convexHull s hxs)
        have hxp : x = p := by
          by_contra hxp
          exact hxnot ⟨hxJ, by simpa only [mem_singleton_iff] using hxp⟩
        have hpp : p ∈ convexHull ℝ (({p} : Finset E) : Set E) := by
          rw [Finset.coe_singleton, convexHull_singleton]
          exact mem_singleton p
        have hsp : s ⊆ {p} :=
          face_subset_of_mem_openSimplex_of_mem_convexHull R hsR hpR
            (hxp ▸ hxs) hpp
        exact (hvp (Finset.mem_singleton.mp (hsp hv))).elim
    · exact Or.inl hvN
theorem levelPolygons_eq_sdiff_of_fiber_eq_sdiff
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    {p : E} (hp : p ∈ K.vertices) {Q J T : Set E} {f : E → ℝ} {r : ℝ}
    (hQ : Q ⊆ K.space) (hJ : J ∈ levelPolygons Q ℓ (ℓ p))
    (hfiber : T ∩ {x | f x = r} =
      (Q ∩ {x | ℓ x = ℓ p}) \ (J \ {p})) :
    levelPolygons T f r = levelPolygons Q ℓ (ℓ p) \ {J} := by
  classical
  have hJK : J ∈ levelPolygons K.space ℓ (ℓ p) :=
    ⟨hJ.1, fun x hx => ⟨hQ (hJ.2 hx).1, (hJ.2 hx).2⟩⟩
  have hJpunctured : (J \ {p}).Nonempty := by
    obtain ⟨x, hxJ⟩ := hJ.1.nonempty
    by_cases hxp : x = p
    · subst x
      exact (hJ.1.isConnected_sdiff_singleton_one p).nonempty
    · exact ⟨x, hxJ, by simpa only [mem_singleton_iff] using hxp⟩
  ext L
  constructor
  · intro hL
    have hLold : L ∈ levelPolygons Q ℓ (ℓ p) := by
      refine ⟨hL.1, fun x hx => ?_⟩
      exact (hfiber.subset (hL.2 hx)).1
    refine ⟨hLold, ?_⟩
    rw [mem_singleton_iff]
    intro hLJ
    obtain ⟨x, hxJ, hxp⟩ := hJpunctured
    have hxnew := hfiber.subset (hL.2 (hLJ ▸ hxJ))
    exact hxnew.2 ⟨hxJ, hxp⟩
  · rintro ⟨hL, hLJ⟩
    refine ⟨hL.1, fun x hx => hfiber.symm.subset ?_⟩
    refine ⟨hL.2 hx, ?_⟩
    rintro ⟨hxJ, hxp⟩
    have hLK : L ∈ levelPolygons K.space ℓ (ℓ p) :=
      ⟨hL.1, fun y hy => ⟨hQ (hL.2 hy).1, (hL.2 hy).2⟩⟩
    have hxsing := inter_subset_singleton_levelPolygons_of_ne K hK hdimE ℓ hℓ hinj
      hp hLK hJK (by simpa only [mem_singleton_iff] using hLJ) ⟨hx, hxJ⟩
    exact hxp hxsing

end DifferentialGeometry.Topology.PiecewiseLinear
