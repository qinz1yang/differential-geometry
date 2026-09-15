import DifferentialGeometry.Topology.PiecewiseLinear.HalfSpacePerturbation
import DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem exists_small_vertexMaps_transverse_in_halfSpace [FiniteDimensional ℝ E]
    (V W : Finset E) (hdim : Module.finrank ℝ E = 3) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hV : ∀ v ∈ V, 0 ≤ ℓ v) (hW : ∀ w ∈ W, 0 ≤ ℓ w) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ ψ : E → E, (∀ v, dist (φ v) v < ε) ∧ (∀ w, dist (ψ w) w < ε) ∧
      (∀ v ∈ V, (ℓ (φ v) = 0 ↔ ℓ v = 0) ∧ 0 ≤ ℓ (φ v)) ∧
        (∀ w ∈ W, (ℓ (ψ w) = 0 ↔ ℓ w = 0) ∧ 0 ≤ ℓ (ψ w)) ∧
          (∀ s : Finset E, s ⊆ V → s.card ≤ 3 → AffineIndependent ℝ (fun v : s => φ (v : E))) ∧
            (∀ t : Finset E, t ⊆ W → t.card ≤ 3 → AffineIndependent ℝ (fun v : t => ψ (v : E))) ∧
              ∀ s : Finset E, s ⊆ V → ∀ t : Finset E, t ⊆ W →
                (convexHull ℝ (s.image φ : Set E) ∩ convexHull ℝ (t.image ψ : Set E)).Nonempty →
                  vectorSpan ℝ (s.image φ : Set E) ⊔ vectorSpan ℝ (t.image ψ : Set E) =
                    if (∀ v ∈ s, ℓ (φ v) = 0) ∧ (∀ w ∈ t, ℓ (ψ w) = 0) then LinearMap.ker ℓ else ⊤ := by
  let : DecidableEq (E ⊕ E) := Classical.typeDecidableEq _
  let A : Finset (E ⊕ E) := V.image Sum.inl ∪ W.image Sum.inr
  let f : E ⊕ E → E := Sum.elim id id
  let B : Finset (E ⊕ E) := A.filter fun v => ℓ (f v) = 0
  have hBA : B ⊆ A := Finset.filter_subset _ _
  have hVA : ∀ v ∈ V, Sum.inl v ∈ A := fun v hv => Finset.mem_union.mpr (Or.inl (Finset.mem_image_of_mem _ hv))
  have hWA : ∀ v ∈ W, Sum.inr v ∈ A := fun v hv => Finset.mem_union.mpr (Or.inr (Finset.mem_image_of_mem _ hv))
  have hA : ∀ v ∈ A, 0 ≤ ℓ (f v) := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      exact hV w hw
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      exact hW w hw
  have hB : ∀ v ∈ B, ℓ (f v) = 0 := fun _ hv => (Finset.mem_filter.mp hv).2
  have hpos : ∀ v ∈ A \ B, 0 < ℓ (f v) := by
    intro v hv
    have hvA := (Finset.mem_sdiff.mp hv).1
    have hv0 : ℓ (f v) ≠ 0 := fun h => (Finset.mem_sdiff.mp hv).2 (Finset.mem_filter.mpr ⟨hvA, h⟩)
    exact lt_of_le_of_ne (hA v hvA) (Ne.symm hv0)
  obtain ⟨θ, _, hclose, hzero, hpositive, hind, htrans⟩ :=
    exists_small_vertexMap_transverse_in_halfSpace A B hBA ℓ hℓ f hB hpos hε
  have hθ : ∀ v ∈ A, (ℓ (θ v) = 0 ↔ ℓ (f v) = 0) ∧ 0 ≤ ℓ (θ v) := by
    intro v hv
    by_cases hv0 : ℓ (f v) = 0
    · have h := hzero v (Finset.mem_filter.mpr ⟨hv, hv0⟩)
      exact ⟨iff_of_true h hv0, h.symm ▸ le_refl 0⟩
    · have hvB : v ∉ B := fun h => hv0 (hB v h)
      have h := hpositive v (Finset.mem_sdiff.mpr ⟨hv, hvB⟩)
      exact ⟨iff_of_false (ne_of_gt h) hv0, h.le⟩
  have hker : Module.finrank ℝ (LinearMap.ker ℓ) = 2 := by
    have h := LinearMap.finrank_range_add_finrank_ker ℓ
    rw [LinearMap.range_eq_top.mpr (LinearMap.surjective_of_ne_zero hℓ), finrank_top, Module.finrank_self, hdim] at h
    omega
  have hinl : ∀ s : Finset E, s ⊆ V → s.image Sum.inl ⊆ A := by
    intro s hs z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact hVA x (hs hx)
  have hinr : ∀ t : Finset E, t ⊆ W → t.image Sum.inr ⊆ A := by
    intro t ht z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact hWA x (ht hx)
  let φ : E → E := fun v => θ (Sum.inl v)
  let ψ : E → E := fun v => θ (Sum.inr v)
  have hφimage : ∀ s : Finset E, (s.image Sum.inl).image θ = s.image φ := by
    intro s
    simp only [Finset.image_image, φ, Function.comp_def]
  have hψimage : ∀ t : Finset E, (t.image Sum.inr).image θ = t.image ψ := by
    intro t
    simp only [Finset.image_image, ψ, Function.comp_def]
  refine ⟨φ, ψ, fun v => hclose (Sum.inl v), fun w => hclose (Sum.inr w),
    fun v hv => hθ (Sum.inl v) (hVA v hv), fun w hw => hθ (Sum.inr w) (hWA w hw), ?_, ?_, ?_⟩
  · intro s hs hcard
    have hi := hind (s.image Sum.inl) (hinl s hs)
      (by rw [hdim]; exact (Finset.card_image_le.trans hcard).trans (by norm_num))
      (by rw [hker]; exact (Finset.card_le_card Finset.inter_subset_left).trans (Finset.card_image_le.trans hcard))
    have hφinj : InjOn φ (s : Set E) := by
      intro a ha b hb hab
      have heq := hi.injective (a₁ := ⟨Sum.inl a, Finset.mem_image_of_mem _ ha⟩)
        (a₂ := ⟨Sum.inl b, Finset.mem_image_of_mem _ hb⟩) hab
      exact Sum.inl_injective (congrArg Subtype.val heq)
    apply (affineIndependent_image_iff s φ).mpr
    refine ⟨hφinj, ?_⟩
    have h := ((affineIndependent_image_iff (s.image Sum.inl) θ).mp hi).2
    rwa [hφimage] at h
  · intro t ht hcard
    have hi := hind (t.image Sum.inr) (hinr t ht)
      (by rw [hdim]; exact (Finset.card_image_le.trans hcard).trans (by norm_num))
      (by rw [hker]; exact (Finset.card_le_card Finset.inter_subset_left).trans (Finset.card_image_le.trans hcard))
    have hψinj : InjOn ψ (t : Set E) := by
      intro a ha b hb hab
      have heq := hi.injective (a₁ := ⟨Sum.inr a, Finset.mem_image_of_mem _ ha⟩)
        (a₂ := ⟨Sum.inr b, Finset.mem_image_of_mem _ hb⟩) hab
      exact Sum.inr_injective (congrArg Subtype.val heq)
    apply (affineIndependent_image_iff t ψ).mpr
    refine ⟨hψinj, ?_⟩
    have h := ((affineIndependent_image_iff (t.image Sum.inr) θ).mp hi).2
    rwa [hψimage] at h
  · intro s hs t ht hinter
    have hdisj : Disjoint (s.image Sum.inl) (t.image Sum.inr) := by
      apply Finset.disjoint_left.mpr
      intro z hz hz'
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨b, _, hba⟩ := Finset.mem_image.mp hz'
      cases hba
    have hi : (convexHull ℝ (((s.image Sum.inl).image θ) : Set E) ∩
        convexHull ℝ (((t.image Sum.inr).image θ) : Set E)).Nonempty := by
      rwa [hφimage, hψimage]
    have h := htrans (s.image Sum.inl) (hinl s hs) (t.image Sum.inr) (hinr t ht) hdisj hi
    rw [hφimage, hψimage] at h
    have hiff : s.image Sum.inl ∪ t.image Sum.inr ⊆ B ↔
        (∀ v ∈ s, ℓ (φ v) = 0) ∧ (∀ w ∈ t, ℓ (ψ w) = 0) := by
      constructor
      · intro hsub
        exact ⟨fun v hv => hzero (Sum.inl v) (hsub (Finset.mem_union.mpr (Or.inl (Finset.mem_image_of_mem _ hv)))),
          fun w hw => hzero (Sum.inr w) (hsub (Finset.mem_union.mpr (Or.inr (Finset.mem_image_of_mem _ hw))))⟩
      · rintro ⟨hφ0, hψ0⟩ z hz
        rcases Finset.mem_union.mp hz with hz | hz
        · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
          exact Finset.mem_filter.mpr ⟨hVA v (hs hv), (hθ (Sum.inl v) (hVA v (hs hv))).1.mp (hφ0 v hv)⟩
        · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
          exact Finset.mem_filter.mpr ⟨hWA w (ht hw), (hθ (Sum.inr w) (hWA w (ht hw))).1.mp (hψ0 w hw)⟩
    change vectorSpan ℝ (s.image φ : Set E) ⊔ vectorSpan ℝ (t.image ψ : Set E) =
      (if s.image Sum.inl ∪ t.image Sum.inr ⊆ B then LinearMap.ker ℓ else ⊤) at h
    simpa only [hiff] using h

open Classical in
theorem exists_small_homeomorphs_transverse_in_halfSpace [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hKcard : ∀ s ∈ K.faces, s.card ≤ 3) (hLcard : ∀ t ∈ L.faces, t.card ≤ 3)
    (hdim : Module.finrank ℝ E = 3) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hKℓ : ∀ v ∈ K.vertices, 0 ≤ ℓ v) (hLℓ : ∀ w ∈ L.vertices, 0 ≤ ℓ w)
    {U : Set E} (hU : IsOpen U) (hKU : K.space ⊆ U) (hLU : L.space ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ ψ h g : E → E, IsPLHomeomorphOn h univ univ ∧ IsPLHomeomorphOn g univ univ ∧
      (∀ x, dist (h x) x < ε) ∧ (∀ x, dist (g x) x < ε) ∧ EqOn h id Uᶜ ∧ EqOn g id Uᶜ ∧
        EqOn h (simplicialMap K φ) K.space ∧ EqOn g (simplicialMap L ψ) L.space ∧
          (∀ x, (ℓ (h x) = 0 ↔ ℓ x = 0) ∧ (0 ≤ ℓ (h x) ↔ 0 ≤ ℓ x)) ∧
            (∀ x, (ℓ (g x) = 0 ↔ ℓ x = 0) ∧ (0 ≤ ℓ (g x) ↔ 0 ≤ ℓ x)) ∧
              (∀ s ∈ K.faces, AffineIndependent ℝ (fun v : s => φ (v : E))) ∧
                (∀ t ∈ L.faces, AffineIndependent ℝ (fun v : t => ψ (v : E))) ∧
                  ∀ s ∈ K.faces, ∀ t ∈ L.faces,
                    (convexHull ℝ (s.image φ : Set E) ∩ convexHull ℝ (t.image ψ : Set E)).Nonempty →
                      vectorSpan ℝ (s.image φ : Set E) ⊔ vectorSpan ℝ (t.image ψ : Set E) =
                        if (∀ v ∈ s, ℓ (φ v) = 0) ∧ (∀ w ∈ t, ℓ (ψ w) = 0) then LinearMap.ker ℓ else ⊤ := by
  obtain ⟨ηK, hηK, hExtK⟩ := exists_isPLHomeomorphOn_extension_of_small_vertex_perturbation_preserving_halfSpace
    K ℓ hℓ hKℓ hU hKU hε
  obtain ⟨ηL, hηL, hExtL⟩ := exists_isPLHomeomorphOn_extension_of_small_vertex_perturbation_preserving_halfSpace
    L ℓ hℓ hLℓ hU hLU hε
  have hKV : K.vertices.Finite := Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite K.faces)
  have hLV : L.vertices.Finite := Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite L.faces)
  let V := hKV.toFinset
  let W := hLV.toFinset
  have hV : ∀ v, v ∈ V ↔ v ∈ K.vertices := fun _ => hKV.mem_toFinset
  have hW : ∀ v, v ∈ W ↔ v ∈ L.vertices := fun _ => hLV.mem_toFinset
  obtain ⟨φ, ψ, hφclose, hψclose, hφheight, hψheight, hφind, hψind, htrans⟩ :=
    exists_small_vertexMaps_transverse_in_halfSpace V W hdim ℓ hℓ
      (fun v hv => hKℓ v ((hV v).mp hv)) (fun v hv => hLℓ v ((hW v).mp hv)) (lt_min hηK hηL)
  obtain ⟨h, hh, hhclose, hhfix, hhmap, hhheight⟩ := hExtK φ
    (fun v _ => (hφclose v).trans_le (min_le_left ηK ηL))
    (fun v hv hv0 => (hφheight v ((hV v).mpr hv)).1.mpr hv0)
  obtain ⟨g, hg, hgclose, hgfix, hgmap, hgheight⟩ := hExtL ψ
    (fun v _ => (hψclose v).trans_le (min_le_right ηK ηL))
    (fun v hv hv0 => (hψheight v ((hW v).mpr hv)).1.mpr hv0)
  have hfaceK : ∀ s ∈ K.faces, s ⊆ V := fun s hs v hv => (hV v).mpr
    (K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v))
  have hfaceL : ∀ t ∈ L.faces, t ⊆ W := fun t ht v hv => (hW v).mpr
    (L.down_closed ht (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v))
  exact ⟨φ, ψ, h, g, hh, hg, hhclose, hgclose, hhfix, hgfix, hhmap, hgmap, hhheight, hgheight,
    fun s hs => hφind s (hfaceK s hs) (hKcard s hs), fun t ht => hψind t (hfaceL t ht) (hLcard t ht),
    fun s hs t ht => htrans s (hfaceK s hs) t (hfaceL t ht)⟩

open Classical in
theorem exists_small_homeomorphs_generalPosition_in_halfSpace [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hdim : Module.finrank ℝ E = 3) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hKℓ : ∀ v ∈ K.vertices, 0 ≤ ℓ v) (hLℓ : ∀ w ∈ L.vertices, 0 ≤ ℓ w)
    (hKboundary : ∀ x ∈ K.space, ℓ x = 0 → x ∈ (boundaryComplex 2 K).space)
    (hLboundary : ∀ x ∈ L.space, ℓ x = 0 → x ∈ (boundaryComplex 2 L).space)
    {U : Set E} (hU : IsOpen U) (hKU : K.space ⊆ U) (hLU : L.space ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ (h g : E → E) (G : Geometry.SimplicialComplex ℝ E),
      IsPLHomeomorphOn h univ univ ∧ IsPLHomeomorphOn g univ univ ∧
        (∀ x, dist (h x) x < ε) ∧ (∀ x, dist (g x) x < ε) ∧ EqOn h id Uᶜ ∧ EqOn g id Uᶜ ∧
          (∀ x, (ℓ (h x) = 0 ↔ ℓ x = 0) ∧ (0 ≤ ℓ (h x) ↔ 0 ≤ ℓ x)) ∧
            (∀ x, (ℓ (g x) = 0 ↔ ℓ x = 0) ∧ (0 ≤ ℓ (g x) ↔ 0 ≤ ℓ x)) ∧
              G.faces.Finite ∧ G.space = h '' K.space ∩ g '' L.space ∧
                IsCombinatorialManifoldWithBoundary 1 G ∧
                  ∀ y ∈ G.space,
                    (ℓ y = 0 ∧ HasPLBoundaryCrossingAt {x : E | 0 ≤ ℓ x} (h '' K.space) (g '' L.space) y) ∨
                    (0 < ℓ y ∧ HasPLCrossingAt (h '' K.space) (g '' L.space) y) := by
  obtain ⟨φ, ψ, h, g, hh, hg, hhclose, hgclose, hhfix, hgfix, hhmap, hgmap, hhheight, hgheight,
      hφind, hψind, htrans⟩ := exists_small_homeomorphs_transverse_in_halfSpace K L
    (fun s hs => hK.card_le K hs) (fun t ht => hL.card_le L ht) hdim ℓ hℓ hKℓ hLℓ hU hKU hLU hε
  have hφinj : InjOn (simplicialMap K φ) K.space := by
    intro x hx y hy hxy
    exact hh.bijOn.injOn (mem_univ _) (mem_univ _) ((hhmap hx).trans (hxy.trans (hhmap hy).symm))
  have hψinj : InjOn (simplicialMap L ψ) L.space := by
    intro x hx y hy hxy
    exact hg.bijOn.injOn (mem_univ _) (mem_univ _) ((hgmap hx).trans (hxy.trans (hgmap hy).symm))
  obtain ⟨K', hKfinite, hKspace, hKPL, hKfaces⟩ := exists_simplicialImage_of_faces_subset K K Subset.rfl φ hφind hφinj
  obtain ⟨L', hLfinite, hLspace, hLPL, hLfaces⟩ := exists_simplicialImage_of_faces_subset L L Subset.rfl ψ hψind hψinj
  have : Finite K'.faces := hKfinite.to_subtype
  have : Finite L'.faces := hLfinite.to_subtype
  have hKman : IsCombinatorialManifoldWithBoundary 2 K' := hK.of_isPLHomeomorphOn hKPL
  have hLman : IsCombinatorialManifoldWithBoundary 2 L' := hL.of_isPLHomeomorphOn hLPL
  have hKspace' : K'.space = h '' K.space := hKspace.trans hhmap.image_eq.symm
  have hLspace' : L'.space = g '' L.space := hLspace.trans hgmap.image_eq.symm
  have hKzero : ∀ x ∈ K'.space, ℓ x = 0 → x ∈ (boundaryComplex 2 K').space := by
    intro x hx hx0
    obtain ⟨y, hy, rfl⟩ := hKspace ▸ hx
    have hy0 : ℓ y = 0 := (hhheight y).1.mp ((congrArg ℓ (hhmap hy)).trans hx0)
    rw [boundaryComplex_space_of_isPLHomeomorphOn K K' hK hKPL]
    exact ⟨y, hKboundary y hy hy0, rfl⟩
  have hLzero : ∀ x ∈ L'.space, ℓ x = 0 → x ∈ (boundaryComplex 2 L').space := by
    intro x hx hx0
    obtain ⟨y, hy, rfl⟩ := hLspace ▸ hx
    have hy0 : ℓ y = 0 := (hgheight y).1.mp ((congrArg ℓ (hgmap hy)).trans hx0)
    rw [boundaryComplex_space_of_isPLHomeomorphOn L L' hL hLPL]
    exact ⟨y, hLboundary y hy hy0, rfl⟩
  have hzeroFace : ∀ C : Geometry.SimplicialComplex ℝ E,
      (∀ x ∈ C.space, ℓ x = 0 → x ∈ (boundaryComplex 2 C).space) →
        ∀ s ∈ C.faces, 2 ≤ s.card → (∀ v ∈ s, ℓ v = 0) → s ∈ (boundaryComplex 2 C).faces := by
    intro C hC s hs _ hs0
    let x := s.centroid ℝ id
    have hx : x ∈ openSimplex s := centroid_mem_openSimplex (C.nonempty_of_mem_faces hs)
    have hxHull := openSimplex_subset_convexHull s hx
    have hkerHull : convexHull ℝ (s : Set E) ⊆ LinearMap.ker ℓ :=
      convexHull_min (fun v hv => hs0 v hv) (LinearMap.ker ℓ).convex
    have hxB := hC x (C.convexHull_subset_space hs hxHull) (hkerHull hxHull)
    by_contra hnot
    exact notMem_space_of_notMem_faces (boundaryComplex_faces_subset 2 C) hs hnot hx hxB
  have hKnonneg : ∀ v ∈ K'.vertices, 0 ≤ ℓ v := by
    intro v hv
    obtain ⟨x, hx, hfx⟩ := hKspace' ▸ K'.subset_space hv (Finset.mem_singleton_self v)
    rw [← hfx]
    apply (hhheight x).2.mpr
    obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
    have heq : ℓ x = ∑ w ∈ s, weights s x w * ℓ w := by
      calc ℓ x = ℓ (∑ w ∈ s, weights s x w • w) := congrArg ℓ (sum_weights_smul hxs).symm
        _ = _ := by rw [map_sum]; simp only [map_smul, smul_eq_mul]
    rw [heq]
    exact Finset.sum_nonneg fun w hw => mul_nonneg (weights_nonneg hxs hw)
      (hKℓ w (K.down_closed hs (Finset.singleton_subset_iff.mpr hw) (Finset.singleton_nonempty w)))
  have hLnonneg : ∀ v ∈ L'.vertices, 0 ≤ ℓ v := by
    intro v hv
    obtain ⟨x, hx, hfx⟩ := hLspace' ▸ L'.subset_space hv (Finset.mem_singleton_self v)
    rw [← hfx]
    apply (hgheight x).2.mpr
    obtain ⟨s, hs, hxs⟩ := L.mem_space_iff.mp hx
    have heq : ℓ x = ∑ w ∈ s, weights s x w * ℓ w := by
      calc ℓ x = ℓ (∑ w ∈ s, weights s x w • w) := congrArg ℓ (sum_weights_smul hxs).symm
        _ = _ := by rw [map_sum]; simp only [map_smul, smul_eq_mul]
    rw [heq]
    exact Finset.sum_nonneg fun w hw => mul_nonneg (weights_nonneg hxs hw)
      (hLℓ w (L.down_closed hs (Finset.singleton_subset_iff.mpr hw) (Finset.singleton_nonempty w)))
  have htrans' : ∀ s ∈ K'.faces, ∀ t ∈ L'.faces,
      (convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty →
        vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) =
          if ∀ v ∈ s ∪ t, ℓ v = 0 then LinearMap.ker ℓ else ⊤ := by
    intro s hs t ht hinter
    obtain ⟨s₀, hs₀, rfl⟩ := hKfaces s hs
    obtain ⟨t₀, ht₀, rfl⟩ := hLfaces t ht
    have heq := htrans s₀ hs₀ t₀ ht₀ hinter
    have hiff : (∀ v ∈ s₀.image φ ∪ t₀.image ψ, ℓ v = 0) ↔
        (∀ v ∈ s₀, ℓ (φ v) = 0) ∧ (∀ w ∈ t₀, ℓ (ψ w) = 0) := by
      constructor
      · intro hz
        exact ⟨fun v hv => hz (φ v) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv)),
          fun w hw => hz (ψ w) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hw))⟩
      · rintro ⟨hszero, htzero⟩ v hv
        rcases Finset.mem_union.mp hv with hv | hv
        · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
          exact hszero w hw
        · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
          exact htzero w hw
    simpa only [hiff] using heq
  obtain ⟨G, hGfinite, hGspace, hGman, _⟩ :=
    exists_isCombinatorialManifoldWithBoundary_inter_in_halfSpace_of_boundary_edges K' L' hKman hLman
      hdim ℓ hKnonneg hLnonneg (hzeroFace K' hKzero) (hzeroFace L' hLzero) htrans'
  refine ⟨h, g, G, hh, hg, hhclose, hgclose, hhfix, hgfix, hhheight, hgheight,
    hGfinite, hGspace.trans (by rw [hKspace', hLspace']), hGman, ?_⟩
  intro y hy
  have hcross := hasPLCrossingAt_or_hasPLBoundaryCrossingAt_of_transverse_faces K' L' hKman hLman
    hdim ℓ hKnonneg hLnonneg (hzeroFace K' hKzero) (hzeroFace L' hLzero) htrans' (hGspace ▸ hy)
  rw [hKspace', hLspace'] at hcross
  rcases hcross with ⟨hy0, hycross, _⟩ | hpos
  · exact Or.inl ⟨hy0, hycross⟩
  · exact Or.inr hpos

open Classical in
theorem exists_small_homeomorph_generalPosition_in_halfSpace [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hdim : Module.finrank ℝ E = 3) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hKℓ : ∀ v ∈ K.vertices, 0 ≤ ℓ v) (hLℓ : ∀ w ∈ L.vertices, 0 ≤ ℓ w)
    (hKboundary : ∀ x ∈ K.space, ℓ x = 0 → x ∈ (boundaryComplex 2 K).space)
    (hLboundary : ∀ x ∈ L.space, ℓ x = 0 → x ∈ (boundaryComplex 2 L).space)
    {U : Set E} (hU : IsOpen U) (hKU : K.space ⊆ U) (hLU : L.space ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ (h : E → E) (G : Geometry.SimplicialComplex ℝ E), IsPLHomeomorphOn h univ univ ∧
      (∀ x, dist (h x) x < ε) ∧ EqOn h id Uᶜ ∧
        (∀ x, (ℓ (h x) = 0 ↔ ℓ x = 0) ∧ (0 ≤ ℓ (h x) ↔ 0 ≤ ℓ x)) ∧
          G.faces.Finite ∧ G.space = h '' K.space ∩ L.space ∧ IsCombinatorialManifoldWithBoundary 1 G ∧
            ∀ y ∈ G.space,
              (ℓ y = 0 ∧ HasPLBoundaryCrossingAt {x : E | 0 ≤ ℓ x} (h '' K.space) L.space y) ∨
              (0 < ℓ y ∧ HasPLCrossingAt (h '' K.space) L.space y) := by
  obtain ⟨h, g, H, hh, hg, hhclose, hgclose, hhfix, hgfix, hhheight, hgheight,
      hHfinite, hHspace, hHman, hHcross⟩ := exists_small_homeomorphs_generalPosition_in_halfSpace K L hK hL
    hdim ℓ hℓ hKℓ hLℓ hKboundary hLboundary hU hKU hLU (half_pos hε)
  have : Finite H.faces := hHfinite.to_subtype
  let e := hg.toOpenPartialHomeomorph isOpen_univ isOpen_univ
  let u := e.symm ∘ h
  have he : IsPiecewiseAffineOn e e.source := hg.isPiecewiseAffineOn
  have heTarget : e.target = univ := rfl
  have hinvHeight : ∀ y, (ℓ (e.symm y) = 0 ↔ ℓ y = 0) ∧ (0 ≤ ℓ (e.symm y) ↔ 0 ≤ ℓ y) := by
    intro y
    have hp := hgheight (e.symm y)
    change (ℓ (e (e.symm y)) = 0 ↔ ℓ (e.symm y) = 0) ∧ (0 ≤ ℓ (e (e.symm y)) ↔ 0 ≤ ℓ (e.symm y)) at hp
    rw [e.right_inv (mem_univ y)] at hp
    exact ⟨hp.1.symm, hp.2.symm⟩
  have hinvClose : ∀ y, dist (e.symm y) y < ε / 2 := by
    intro y
    have hp := hgclose (e.symm y)
    change dist (e (e.symm y)) (e.symm y) < ε / 2 at hp
    rwa [e.right_inv (mem_univ y), dist_comm] at hp
  have huPL : IsPLHomeomorphOn u univ univ := hh.trans hg.symm
  have huclose : ∀ x, dist (u x) x < ε := by
    intro x
    have hp := (dist_triangle (e.symm (h x)) (h x) x).trans_lt (add_lt_add (hinvClose (h x)) (hhclose x))
    rw [add_halves] at hp
    exact hp
  have hufix : EqOn u id Uᶜ := by
    intro x hx
    change e.symm (h x) = x
    rw [hhfix hx]
    calc e.symm x = e.symm (g x) := congrArg e.symm (hgfix hx).symm
      _ = x := e.left_inv (mem_univ x)
  have huheight : ∀ x, (ℓ (u x) = 0 ↔ ℓ x = 0) ∧ (0 ≤ ℓ (u x) ↔ 0 ≤ ℓ x) := fun x =>
    ⟨(hinvHeight (h x)).1.trans (hhheight x).1, (hinvHeight (h x)).2.trans (hhheight x).2⟩
  have hPLH : IsPiecewiseAffineOn e.symm H.space := hg.symm.isPiecewiseAffineOn.mono_of_isPolyhedron
    (isPolyhedron_space H) (subset_univ _)
  obtain ⟨G, hGfinite, hGspace, hGPL⟩ := exists_isPLHomeomorphOn_image H hPLH
    (hg.symm.bijOn.injOn.mono (subset_univ _))
  have : Finite G.faces := hGfinite.to_subtype
  have hGman : IsCombinatorialManifoldWithBoundary 1 G := hHman.of_isPLHomeomorphOn hGPL
  have hKimage : e.symm '' (e.target ∩ h '' K.space) = u '' K.space := by
    simp only [heTarget, univ_inter, image_image, u, Function.comp_def]
  have hLimage : e.symm '' (e.target ∩ g '' L.space) = L.space := by
    rw [heTarget, univ_inter]
    ext y
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, hxy⟩
      have heq : x = y := (e.left_inv (mem_univ x)).symm.trans hxy
      exact heq ▸ hx
    · intro hy
      exact ⟨g y, ⟨y, hy, rfl⟩, e.left_inv (mem_univ y)⟩
  have hMimage : e.symm '' (e.target ∩ {x : E | 0 ≤ ℓ x}) = {x : E | 0 ≤ ℓ x} := by
    ext y
    constructor
    · rintro ⟨z, ⟨_, hz⟩, rfl⟩
      exact (hinvHeight z).2.mpr hz
    · intro hy
      exact ⟨g y, ⟨mem_univ _, (hgheight y).2.mpr hy⟩, e.left_inv (mem_univ y)⟩
  have hGspace' : G.space = u '' K.space ∩ L.space := by
    rw [hGspace, hHspace]
    ext y
    constructor
    · rintro ⟨z, ⟨hzK, hzL⟩, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hzK
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      obtain ⟨w, hw, hwx⟩ := hzL
      have heq : e.symm (h x) = w := by rw [← hwx]; exact e.left_inv (mem_univ w)
      exact heq.symm ▸ hw
    · rintro ⟨⟨x, hx, rfl⟩, hxL⟩
      refine ⟨h x, ⟨⟨x, hx, rfl⟩, ⟨u x, hxL, ?_⟩⟩, rfl⟩
      exact e.right_inv (mem_univ (h x))
  refine ⟨u, G, huPL, huclose, hufix, huheight, hGfinite, hGspace', hGman, ?_⟩
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hGspace ▸ hy
  rcases hHcross z hz with ⟨hz0, hcross⟩ | ⟨hzpos, hcross⟩
  · have hc := hcross.image_openPartialHomeomorph e.symm he.symm (mem_univ z)
    change HasPLBoundaryCrossingAt (e.symm '' (e.target ∩ {x : E | 0 ≤ ℓ x}))
      (e.symm '' (e.target ∩ h '' K.space)) (e.symm '' (e.target ∩ g '' L.space)) (e.symm z) at hc
    rw [hMimage, hKimage, hLimage] at hc
    exact Or.inl ⟨(hinvHeight z).1.mpr hz0, hc⟩
  · have hc := hcross.image_openPartialHomeomorph e.symm he.symm (mem_univ z)
    change HasPLCrossingAt (e.symm '' (e.target ∩ h '' K.space))
      (e.symm '' (e.target ∩ g '' L.space)) (e.symm z) at hc
    rw [hKimage, hLimage] at hc
    have hz' : 0 < ℓ (e.symm z) := lt_of_le_of_ne ((hinvHeight z).2.mpr hzpos.le)
      (fun heq => (ne_of_gt hzpos) ((hinvHeight z).1.mp heq.symm))
    exact Or.inr ⟨hz', hc⟩

end DifferentialGeometry.Topology.PiecewiseLinear
