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

end DifferentialGeometry.Topology.PiecewiseLinear
