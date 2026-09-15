import DifferentialGeometry.Topology.PiecewiseLinear.PLPiece
import DifferentialGeometry.Topology.PiecewiseLinear.RelativeDerived

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem affineMap_apply_sum_smul_comp {ι : Type*} (A : G →ᵃ[ℝ] E) {σ : Finset ι} {μ : ι → ℝ}
    (p : ι → G) (hμ : ∑ i ∈ σ, μ i = 1) :
    A (∑ i ∈ σ, μ i • p i) = ∑ i ∈ σ, μ i • A (p i) := by
  have h1 : ∑ i ∈ σ, μ i • p i = σ.affineCombination ℝ p μ :=
    (Finset.affineCombination_eq_linear_combination σ p μ hμ).symm
  have h2 : ∑ i ∈ σ, μ i • A (p i) = σ.affineCombination ℝ (A ∘ p) μ :=
    (Finset.affineCombination_eq_linear_combination σ (A ∘ p) μ hμ).symm
  rw [h1, h2, Finset.map_affineCombination σ p μ hμ A]

theorem convexHull_subset_nonneg (ℓ : G →ₗ[ℝ] ℝ) {t : Finset G} (h : ∀ u ∈ t, 0 ≤ ℓ u) :
    convexHull ℝ (t : Set G) ⊆ {z | 0 ≤ ℓ z} :=
  convexHull_min (fun u hu => h u hu) (convex_halfSpace_ge ℓ.isLinear 0)

theorem mem_convexHull_filter_of_eq_zero (ℓ : G →ₗ[ℝ] ℝ) {t : Finset G} (h : ∀ u ∈ t, 0 ≤ ℓ u)
    {z : G} (hz : z ∈ convexHull ℝ (t : Set G)) (hz₀ : ℓ z = 0) :
    z ∈ convexHull ℝ ((t.filter fun u => ℓ u = 0 : Finset G) : Set G) := by
  obtain ⟨w, hw₀, hw₁, hwz⟩ := mem_convexHull_iff_exists_weights.mp hz
  have hsum : ∑ u ∈ t, w u * ℓ u = 0 := by
    rw [← hz₀, ← hwz, map_sum]
    exact Finset.sum_congr rfl fun u _ => by rw [map_smul, smul_eq_mul]
  have hzero : ∀ u ∈ t, w u * ℓ u = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun u hu => mul_nonneg (hw₀ u hu) (h u hu)).mp hsum
  have hw' : ∀ u ∈ t, w u ≠ 0 → ℓ u = 0 := fun u hu hwu =>
    (mul_eq_zero.mp (hzero u hu)).resolve_left hwu
  refine mem_convexHull_iff_exists_weights.mpr
    ⟨w, fun u hu => hw₀ u (Finset.filter_subset _ _ hu), ?_, ?_⟩
  · rw [Finset.sum_filter_of_ne hw', hw₁]
  · rw [Finset.sum_filter_of_ne fun u hu hne => hw' u hu fun h0 => hne (by rw [h0, zero_smul]),
      hwz]

theorem space_mono_of_faces_subset {K L : Geometry.SimplicialComplex ℝ E}
    (h : L.faces ⊆ K.faces) : L.space ⊆ K.space := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := L.mem_space_iff.mp hx
  exact K.convexHull_subset_space (h hs) hxs

section Embedding

variable (K : Geometry.SimplicialComplex ℝ E) (Θ : E → G) (π : G →ᵃ[ℝ] E)
  (hπΘ : ∀ s ∈ K.faces, ∀ v ∈ s, π (Θ v) = v)
include hπΘ

theorem apply_simplicialMap_of_leftInverse {x : E} (hx : x ∈ K.space) :
    π (simplicialMap K Θ x) = x := by
  obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
  rw [simplicialMap_eq_of_mem K Θ hs hxs, affineMap_apply_sum_smul_comp π Θ (sum_weights hxs)]
  calc ∑ v ∈ s, weights s x v • π (Θ v) = ∑ v ∈ s, weights s x v • v :=
        Finset.sum_congr rfl fun v hv => by rw [hπΘ s hs v hv]
    _ = x := sum_weights_smul hxs

theorem injOn_simplicialMap_of_leftInverse : InjOn (simplicialMap K Θ) K.space := by
  intro x hx y hy hxy
  rw [← apply_simplicialMap_of_leftInverse K Θ π hπΘ hx,
    ← apply_simplicialMap_of_leftInverse K Θ π hπΘ hy, hxy]

theorem affineIndependent_image_of_leftInverse [DecidableEq G] {s : Finset E} (hs : s ∈ K.faces) :
    AffineIndependent ℝ ((↑) : {u // u ∈ s.image Θ} → G) := by
  have hmem : ∀ u : {u // u ∈ s.image Θ}, π u ∈ s := by
    rintro ⟨u, hu⟩
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    change π (Θ v) ∈ s
    rw [hπΘ s hs v hv]
    exact hv
  have hΘπ : ∀ u : {u // u ∈ s.image Θ}, Θ (π u) = u := by
    rintro ⟨u, hu⟩
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    change Θ (π (Θ v)) = Θ v
    rw [hπΘ s hs v hv]
  let f : {u // u ∈ s.image Θ} ↪ {v // v ∈ s} :=
    ⟨fun u => ⟨π u, hmem u⟩, fun u u' h => Subtype.ext (by
      have h' : π u = π u' := congrArg Subtype.val h
      rw [← hΘπ u, ← hΘπ u', h'])⟩
  exact AffineIndependent.of_comp π ((K.indep hs).comp_embedding f)

noncomputable def embedComplex [DecidableEq G] : Geometry.SimplicialComplex ℝ G :=
  simplicialImage K Θ (fun _ hs => affineIndependent_image_of_leftInverse K Θ π hπΘ hs)
    (injOn_simplicialMap_of_leftInverse K Θ π hπΘ)

variable [DecidableEq G]

theorem mem_embedComplex_faces_iff {t : Finset G} :
    t ∈ (embedComplex K Θ π hπΘ).faces ↔ ∃ s ∈ K.faces, t = s.image Θ := Iff.rfl

theorem embedComplex_space : (embedComplex K Θ π hπΘ).space = simplicialMap K Θ '' K.space :=
  simplicialImage_space K Θ _ _

theorem embedComplex_faces_finite [Finite K.faces] : (embedComplex K Θ π hπΘ).faces.Finite :=
  simplicialImage_faces_finite K Θ _ _

theorem isPLHomeomorphOn_embedComplex [FiniteDimensional ℝ E] [FiniteDimensional ℝ G]
    [Finite K.faces] :
    IsPLHomeomorphOn (simplicialMap K Θ) K.space (embedComplex K Θ π hπΘ).space :=
  isPLHomeomorphOn_simplicialImage K Θ _ _

theorem mapsTo_embedComplex : MapsTo π (embedComplex K Θ π hπΘ).space K.space := by
  rw [embedComplex_space]
  rintro _ ⟨x, hx, rfl⟩
  rw [apply_simplicialMap_of_leftInverse K Θ π hπΘ hx]
  exact hx

theorem simplicialMap_apply_of_mem_embedComplex_space {z : G}
    (hz : z ∈ (embedComplex K Θ π hπΘ).space) : simplicialMap K Θ (π z) = z := by
  rw [embedComplex_space] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  rw [apply_simplicialMap_of_leftInverse K Θ π hπΘ hx]

theorem injOn_embedComplex : InjOn π (embedComplex K Θ π hπΘ).space := by
  intro z hz z' hz' h
  rw [← simplicialMap_apply_of_mem_embedComplex_space K Θ π hπΘ hz,
    ← simplicialMap_apply_of_mem_embedComplex_space K Θ π hπΘ hz', h]

theorem simplicialMap_mem_embedComplex_space {x : E} (hx : x ∈ K.space) :
    simplicialMap K Θ x ∈ (embedComplex K Θ π hπΘ).space := by
  rw [embedComplex_space]
  exact ⟨x, hx, rfl⟩

end Embedding

theorem convexHull_subset_nonpos (ℓ : G →ₗ[ℝ] ℝ) {t : Finset G} (h : ∀ u ∈ t, ℓ u ≤ 0) :
    convexHull ℝ (t : Set G) ⊆ {z | ℓ z ≤ 0} :=
  convexHull_min (fun u hu => h u hu) (convex_halfSpace_le ℓ.isLinear 0)

theorem mem_convexHull_filter_of_eq_zero' (ℓ : G →ₗ[ℝ] ℝ) {t : Finset G} (h : ∀ u ∈ t, ℓ u ≤ 0)
    {z : G} (hz : z ∈ convexHull ℝ (t : Set G)) (hz₀ : ℓ z = 0) :
    z ∈ convexHull ℝ ((t.filter fun u => ℓ u = 0 : Finset G) : Set G) := by
  have := mem_convexHull_filter_of_eq_zero (-ℓ) (fun u hu => by
    rw [LinearMap.neg_apply]
    exact neg_nonneg.mpr (h u hu)) hz (by rw [LinearMap.neg_apply, hz₀, neg_zero])
  rwa [Finset.filter_congr (q := fun u => ℓ u = 0) fun u _ => by
    rw [LinearMap.neg_apply, neg_eq_zero]] at this

theorem nonempty_of_mem_convexHull {t : Finset G} {z : G} (hz : z ∈ convexHull ℝ (t : Set G)) :
    t.Nonempty := by
  refine Finset.nonempty_of_ne_empty fun h0 => ?_
  rw [h0, Finset.coe_empty, convexHull_empty] at hz
  exact hz

section GlueData

variable (K₁ : Geometry.SimplicialComplex ℝ E) (K₂ : Geometry.SimplicialComplex ℝ F)
  (A₁ : Geometry.SimplicialComplex ℝ E) (A₂ : Geometry.SimplicialComplex ℝ F)
  (ψ : E → F) (ψ' : F → E)

open Classical in
noncomputable def glueEmbed₁ (v : E) : E × F × ℝ := (v, ψ v, if {v} ∈ A₁.faces then 0 else 1)

open Classical in
noncomputable def glueEmbed₂ (w : F) : E × F × ℝ := (ψ' w, w, if {w} ∈ A₂.faces then 0 else -1)

variable (E F) in
def glueFst : E × F × ℝ →ᵃ[ℝ] E := AffineMap.fst

variable (E F) in
def glueSnd : E × F × ℝ →ᵃ[ℝ] F := AffineMap.fst.comp AffineMap.snd

variable (E F) in
def glueHeight : E × F × ℝ →ₗ[ℝ] ℝ := (LinearMap.snd ℝ F ℝ).comp (LinearMap.snd ℝ E (F × ℝ))

theorem continuous_glueFst : Continuous (glueFst E F) := continuous_fst

theorem continuous_glueSnd : Continuous (glueSnd E F) := continuous_fst.comp continuous_snd

theorem glueFst_glueEmbed₁ (v : E) : glueFst E F (glueEmbed₁ A₁ ψ v) = v := rfl

theorem glueSnd_glueEmbed₁ (v : E) : glueSnd E F (glueEmbed₁ A₁ ψ v) = ψ v := rfl

theorem glueSnd_glueEmbed₂ (w : F) : glueSnd E F (glueEmbed₂ A₂ ψ' w) = w := rfl

theorem glueFst_glueEmbed₂ (w : F) : glueFst E F (glueEmbed₂ A₂ ψ' w) = ψ' w := rfl

theorem glueHeight_glueEmbed₁_nonneg (v : E) : 0 ≤ glueHeight E F (glueEmbed₁ A₁ ψ v) := by
  change (0 : ℝ) ≤ (glueEmbed₁ A₁ ψ v).2.2
  rw [glueEmbed₁]
  split_ifs <;> norm_num

theorem glueHeight_glueEmbed₁_eq_zero_iff (v : E) :
    glueHeight E F (glueEmbed₁ A₁ ψ v) = 0 ↔ {v} ∈ A₁.faces := by
  change (glueEmbed₁ A₁ ψ v).2.2 = 0 ↔ _
  rw [glueEmbed₁]
  split_ifs with h <;> simp [h]

theorem glueHeight_glueEmbed₂_nonpos (w : F) : glueHeight E F (glueEmbed₂ A₂ ψ' w) ≤ 0 := by
  change (glueEmbed₂ A₂ ψ' w).2.2 ≤ 0
  rw [glueEmbed₂]
  split_ifs <;> norm_num

theorem glueHeight_glueEmbed₂_eq_zero_iff (w : F) :
    glueHeight E F (glueEmbed₂ A₂ ψ' w) = 0 ↔ {w} ∈ A₂.faces := by
  change (glueEmbed₂ A₂ ψ' w).2.2 = 0 ↔ _
  rw [glueEmbed₂]
  split_ifs with h <;> simp [h]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem glueEmbed₁_injective : Function.Injective (glueEmbed₁ A₁ ψ) :=
  fun _ _ h => congrArg Prod.fst h

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem glueEmbed₂_injective : Function.Injective (glueEmbed₂ A₂ ψ') :=
  fun _ _ h => congrArg (fun z : E × F × ℝ => z.2.1) h

variable [DecidableEq E] [DecidableEq F]

noncomputable def glued₁ : Geometry.SimplicialComplex ℝ (E × F × ℝ) :=
  embedComplex K₁ (glueEmbed₁ A₁ ψ) (glueFst E F) fun _ _ _ _ => rfl

noncomputable def glued₂ : Geometry.SimplicialComplex ℝ (E × F × ℝ) :=
  embedComplex K₂ (glueEmbed₂ A₂ ψ') (glueSnd E F) fun _ _ _ _ => rfl

theorem mem_glued₁_faces_iff {t : Finset (E × F × ℝ)} :
    t ∈ (glued₁ K₁ A₁ ψ).faces ↔ ∃ s ∈ K₁.faces, t = s.image (glueEmbed₁ A₁ ψ) := Iff.rfl

theorem mem_glued₂_faces_iff {t : Finset (E × F × ℝ)} :
    t ∈ (glued₂ K₂ A₂ ψ').faces ↔ ∃ s ∈ K₂.faces, t = s.image (glueEmbed₂ A₂ ψ') := Iff.rfl

theorem glued₁_space :
    (glued₁ K₁ A₁ ψ).space = simplicialMap K₁ (glueEmbed₁ A₁ ψ) '' K₁.space :=
  embedComplex_space K₁ _ _ _

theorem glued₂_space :
    (glued₂ K₂ A₂ ψ').space = simplicialMap K₂ (glueEmbed₂ A₂ ψ') '' K₂.space :=
  embedComplex_space K₂ _ _ _

theorem glued₁_faces_finite [Finite K₁.faces] : (glued₁ K₁ A₁ ψ).faces.Finite :=
  embedComplex_faces_finite K₁ _ _ _

theorem glued₂_faces_finite [Finite K₂.faces] : (glued₂ K₂ A₂ ψ').faces.Finite :=
  embedComplex_faces_finite K₂ _ _ _

omit [DecidableEq E] [DecidableEq F] in
theorem glueFst_simplicialMap {x : E} (hx : x ∈ K₁.space) :
    glueFst E F (simplicialMap K₁ (glueEmbed₁ A₁ ψ) x) = x :=
  apply_simplicialMap_of_leftInverse K₁ _ _ (fun _ _ _ _ => rfl) hx

omit [DecidableEq E] [DecidableEq F] in
theorem glueSnd_simplicialMap {y : F} (hy : y ∈ K₂.space) :
    glueSnd E F (simplicialMap K₂ (glueEmbed₂ A₂ ψ') y) = y :=
  apply_simplicialMap_of_leftInverse K₂ _ _ (fun _ _ _ _ => rfl) hy

theorem simplicialMap_glueFst {z : E × F × ℝ} (hz : z ∈ (glued₁ K₁ A₁ ψ).space) :
    simplicialMap K₁ (glueEmbed₁ A₁ ψ) (glueFst E F z) = z :=
  simplicialMap_apply_of_mem_embedComplex_space K₁ _ _ _ hz

theorem simplicialMap_glueSnd {z : E × F × ℝ} (hz : z ∈ (glued₂ K₂ A₂ ψ').space) :
    simplicialMap K₂ (glueEmbed₂ A₂ ψ') (glueSnd E F z) = z :=
  simplicialMap_apply_of_mem_embedComplex_space K₂ _ _ _ hz

theorem glueFst_mem_of_mem_glued₁ {z : E × F × ℝ} (hz : z ∈ (glued₁ K₁ A₁ ψ).space) :
    glueFst E F z ∈ K₁.space :=
  mapsTo_embedComplex K₁ _ _ _ hz

theorem glueSnd_mem_of_mem_glued₂ {z : E × F × ℝ} (hz : z ∈ (glued₂ K₂ A₂ ψ').space) :
    glueSnd E F z ∈ K₂.space :=
  mapsTo_embedComplex K₂ _ _ _ hz

theorem simplicialMap_mem_glued₁ {x : E} (hx : x ∈ K₁.space) :
    simplicialMap K₁ (glueEmbed₁ A₁ ψ) x ∈ (glued₁ K₁ A₁ ψ).space :=
  simplicialMap_mem_embedComplex_space K₁ _ _ _ hx

theorem simplicialMap_mem_glued₂ {y : F} (hy : y ∈ K₂.space) :
    simplicialMap K₂ (glueEmbed₂ A₂ ψ') y ∈ (glued₂ K₂ A₂ ψ').space :=
  simplicialMap_mem_embedComplex_space K₂ _ _ _ hy

theorem glueHeight_nonneg_of_mem_glued₁_face {t : Finset (E × F × ℝ)}
    (ht : t ∈ (glued₁ K₁ A₁ ψ).faces) : ∀ u ∈ t, 0 ≤ glueHeight E F u := by
  obtain ⟨s, -, rfl⟩ := ht
  intro u hu
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hu
  exact glueHeight_glueEmbed₁_nonneg A₁ ψ v

theorem glueHeight_nonpos_of_mem_glued₂_face {t : Finset (E × F × ℝ)}
    (ht : t ∈ (glued₂ K₂ A₂ ψ').faces) : ∀ u ∈ t, glueHeight E F u ≤ 0 := by
  obtain ⟨s, -, rfl⟩ := ht
  intro u hu
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hu
  exact glueHeight_glueEmbed₂_nonpos A₂ ψ' w

theorem glueHeight_nonneg_of_mem_glued₁ {z : E × F × ℝ} (hz : z ∈ (glued₁ K₁ A₁ ψ).space) :
    0 ≤ glueHeight E F z := by
  obtain ⟨t, ht, hzt⟩ := (glued₁ K₁ A₁ ψ).mem_space_iff.mp hz
  exact convexHull_subset_nonneg _ (glueHeight_nonneg_of_mem_glued₁_face K₁ A₁ ψ ht) hzt

theorem glueHeight_nonpos_of_mem_glued₂ {z : E × F × ℝ} (hz : z ∈ (glued₂ K₂ A₂ ψ').space) :
    glueHeight E F z ≤ 0 := by
  obtain ⟨t, ht, hzt⟩ := (glued₂ K₂ A₂ ψ').mem_space_iff.mp hz
  exact convexHull_subset_nonpos _ (glueHeight_nonpos_of_mem_glued₂_face K₂ A₂ ψ' ht) hzt

theorem glueHeight_eq_zero_of_mem {z : E × F × ℝ} (hz₁ : z ∈ (glued₁ K₁ A₁ ψ).space)
    (hz₂ : z ∈ (glued₂ K₂ A₂ ψ').space) : glueHeight E F z = 0 :=
  le_antisymm (glueHeight_nonpos_of_mem_glued₂ K₂ A₂ ψ' hz₂)
    (glueHeight_nonneg_of_mem_glued₁ K₁ A₁ ψ hz₁)

structure IsGlueIso : Prop where
  image₁ : ∀ s ∈ A₁.faces, s.image ψ ∈ A₂.faces
  image₂ : ∀ t ∈ A₂.faces, t.image ψ' ∈ A₁.faces
  left : ∀ s ∈ A₁.faces, ∀ v ∈ s, ψ' (ψ v) = v
  right : ∀ t ∈ A₂.faces, ∀ u ∈ t, ψ (ψ' u) = u

variable {A₁ A₂ ψ ψ'}

theorem IsGlueIso.symm (h : IsGlueIso A₁ A₂ ψ ψ') : IsGlueIso A₂ A₁ ψ' ψ :=
  ⟨h.image₂, h.image₁, h.right, h.left⟩

theorem IsGlueIso.singleton_mem (h : IsGlueIso A₁ A₂ ψ ψ') {v : E} (hv : {v} ∈ A₁.faces) :
    {ψ v} ∈ A₂.faces := by
  have := h.image₁ _ hv
  rwa [Finset.image_singleton] at this

theorem IsGlueIso.image_image_left (h : IsGlueIso A₁ A₂ ψ ψ') {s : Finset E}
    (hs : s ∈ A₁.faces) : (s.image ψ).image ψ' = s := by
  rw [Finset.image_image]
  calc
    s.image (ψ' ∘ ψ) = s.image id := Finset.image_congr fun v hv => h.left s hs v hv
    _ = s := Finset.image_id

theorem IsGlueIso.image_image_right (h : IsGlueIso A₁ A₂ ψ ψ') {t : Finset F}
    (ht : t ∈ A₂.faces) : (t.image ψ').image ψ = t :=
  h.symm.image_image_left ht

theorem image_glueEmbed₁_eq (h : IsGlueIso A₁ A₂ ψ ψ') {s : Finset E} (hs : s ∈ A₁.faces) :
    s.image (glueEmbed₁ A₁ ψ) = (s.image ψ).image (glueEmbed₂ A₂ ψ') := by
  rw [Finset.image_image]
  refine Finset.image_congr fun v hv => ?_
  have hv₁ : {v} ∈ A₁.faces :=
    A₁.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  change glueEmbed₁ A₁ ψ v = glueEmbed₂ A₂ ψ' (ψ v)
  rw [glueEmbed₁, glueEmbed₂, if_pos hv₁, if_pos (h.singleton_mem hv₁), h.left s hs v hv]

theorem image_glueEmbed₂_eq (h : IsGlueIso A₁ A₂ ψ ψ') {t : Finset F} (ht : t ∈ A₂.faces) :
    t.image (glueEmbed₂ A₂ ψ') = (t.image ψ').image (glueEmbed₁ A₁ ψ) := by
  rw [Finset.image_image]
  refine Finset.image_congr fun w hw => ?_
  have hw₂ : {w} ∈ A₂.faces :=
    A₂.down_closed ht (Finset.singleton_subset_iff.mpr hw) (Finset.singleton_nonempty w)
  change glueEmbed₂ A₂ ψ' w = glueEmbed₁ A₁ ψ (ψ' w)
  rw [glueEmbed₁, glueEmbed₂, if_pos hw₂, if_pos (h.symm.singleton_mem hw₂), h.right t ht w hw]

theorem exists_face_filter_glued₁
    (hfull₁ : ∀ s ∈ K₁.faces, (∀ v ∈ s, {v} ∈ A₁.faces) → s ∈ A₁.faces)
    {t : Finset (E × F × ℝ)} (ht : t ∈ (glued₁ K₁ A₁ ψ).faces)
    (hne : (t.filter fun u => glueHeight E F u = 0).Nonempty) :
    ∃ s ∈ A₁.faces, t.filter (fun u => glueHeight E F u = 0) = s.image (glueEmbed₁ A₁ ψ) := by
  classical
  obtain ⟨s, hs, rfl⟩ := ht
  rw [Finset.filter_image] at hne ⊢
  have hfilter : (s.filter fun v => glueHeight E F (glueEmbed₁ A₁ ψ v) = 0) =
      s.filter fun v => {v} ∈ A₁.faces :=
    Finset.filter_congr fun v _ => glueHeight_glueEmbed₁_eq_zero_iff A₁ ψ v
  rw [hfilter] at hne ⊢
  refine ⟨_, ?_, rfl⟩
  have hne' : (s.filter fun v => {v} ∈ A₁.faces).Nonempty := by
    obtain ⟨u, hu⟩ := hne
    obtain ⟨v, hv, -⟩ := Finset.mem_image.mp hu
    exact ⟨v, hv⟩
  exact hfull₁ _ (K₁.down_closed hs (Finset.filter_subset _ _) hne')
    fun v hv => (Finset.mem_filter.mp hv).2

theorem filter_mem_glued₂_of_mem_glued₁ (h : IsGlueIso A₁ A₂ ψ ψ') (hA₂ : A₂.faces ⊆ K₂.faces)
    (hfull₁ : ∀ s ∈ K₁.faces, (∀ v ∈ s, {v} ∈ A₁.faces) → s ∈ A₁.faces)
    {t : Finset (E × F × ℝ)} (ht : t ∈ (glued₁ K₁ A₁ ψ).faces)
    (hne : (t.filter fun u => glueHeight E F u = 0).Nonempty) :
    t.filter (fun u => glueHeight E F u = 0) ∈ (glued₂ K₂ A₂ ψ').faces := by
  obtain ⟨s, hs, hst⟩ := exists_face_filter_glued₁ K₁ hfull₁ ht hne
  rw [hst, image_glueEmbed₁_eq h hs]
  exact ⟨_, hA₂ (h.image₁ s hs), rfl⟩

theorem convexHull_inter_subset_glued (h : IsGlueIso A₁ A₂ ψ ψ') (hA₂ : A₂.faces ⊆ K₂.faces)
    (hfull₁ : ∀ s ∈ K₁.faces, (∀ v ∈ s, {v} ∈ A₁.faces) → s ∈ A₁.faces)
    {t₁ t₂ : Finset (E × F × ℝ)} (ht₁ : t₁ ∈ (glued₁ K₁ A₁ ψ).faces)
    (ht₂ : t₂ ∈ (glued₂ K₂ A₂ ψ').faces) :
    convexHull ℝ (t₁ : Set (E × F × ℝ)) ∩ convexHull ℝ (t₂ : Set (E × F × ℝ)) ⊆
      convexHull ℝ ((t₁ : Set (E × F × ℝ)) ∩ (t₂ : Set (E × F × ℝ))) := by
  rintro z ⟨hz₁, hz₂⟩
  have hz₀ : glueHeight E F z = 0 :=
    glueHeight_eq_zero_of_mem K₁ K₂ A₁ A₂ ψ ψ'
      ((glued₁ K₁ A₁ ψ).convexHull_subset_space ht₁ hz₁)
      ((glued₂ K₂ A₂ ψ').convexHull_subset_space ht₂ hz₂)
  have hz₁' := mem_convexHull_filter_of_eq_zero _
    (glueHeight_nonneg_of_mem_glued₁_face K₁ A₁ ψ ht₁) hz₁ hz₀
  have hz₂' := mem_convexHull_filter_of_eq_zero' _
    (glueHeight_nonpos_of_mem_glued₂_face K₂ A₂ ψ' ht₂) hz₂ hz₀
  have ht₁' := filter_mem_glued₂_of_mem_glued₁ K₁ K₂ h hA₂ hfull₁ ht₁
    (nonempty_of_mem_convexHull hz₁')
  have ht₂' := (glued₂ K₂ A₂ ψ').down_closed ht₂ (Finset.filter_subset _ _)
    (nonempty_of_mem_convexHull hz₂')
  refine convexHull_mono ?_ ((glued₂ K₂ A₂ ψ').inter_subset_convexHull ht₁' ht₂' ⟨hz₁', hz₂'⟩)
  exact inter_subset_inter (Finset.coe_subset.mpr (Finset.filter_subset _ _))
    (Finset.coe_subset.mpr (Finset.filter_subset _ _))

noncomputable def gluedComplex (h : IsGlueIso A₁ A₂ ψ ψ') (hA₂ : A₂.faces ⊆ K₂.faces)
    (hfull₁ : ∀ s ∈ K₁.faces, (∀ v ∈ s, {v} ∈ A₁.faces) → s ∈ A₁.faces) :
    Geometry.SimplicialComplex ℝ (E × F × ℝ) where
  faces := (glued₁ K₁ A₁ ψ).faces ∪ (glued₂ K₂ A₂ ψ').faces
  isRelLowerSet_faces :=
    (glued₁ K₁ A₁ ψ).isRelLowerSet_faces.union (glued₂ K₂ A₂ ψ').isRelLowerSet_faces
  indep := by
    rintro t (ht | ht)
    · exact (glued₁ K₁ A₁ ψ).indep ht
    · exact (glued₂ K₂ A₂ ψ').indep ht
  inter_subset_convexHull := by
    rintro t₁ t₂ (ht₁ | ht₁) (ht₂ | ht₂)
    · exact (glued₁ K₁ A₁ ψ).inter_subset_convexHull ht₁ ht₂
    · exact convexHull_inter_subset_glued K₁ K₂ h hA₂ hfull₁ ht₁ ht₂
    · intro z hz
      have := convexHull_inter_subset_glued K₁ K₂ h hA₂ hfull₁ ht₂ ht₁ ⟨hz.2, hz.1⟩
      rwa [inter_comm] at this
    · exact (glued₂ K₂ A₂ ψ').inter_subset_convexHull ht₁ ht₂

theorem mem_gluedComplex_faces_iff (h : IsGlueIso A₁ A₂ ψ ψ') (hA₂ : A₂.faces ⊆ K₂.faces)
    (hfull₁ : ∀ s ∈ K₁.faces, (∀ v ∈ s, {v} ∈ A₁.faces) → s ∈ A₁.faces)
    {t : Finset (E × F × ℝ)} :
    t ∈ (gluedComplex K₁ K₂ h hA₂ hfull₁).faces ↔
      t ∈ (glued₁ K₁ A₁ ψ).faces ∨ t ∈ (glued₂ K₂ A₂ ψ').faces := Iff.rfl

theorem gluedComplex_space (h : IsGlueIso A₁ A₂ ψ ψ') (hA₂ : A₂.faces ⊆ K₂.faces)
    (hfull₁ : ∀ s ∈ K₁.faces, (∀ v ∈ s, {v} ∈ A₁.faces) → s ∈ A₁.faces) :
    (gluedComplex K₁ K₂ h hA₂ hfull₁).space =
      (glued₁ K₁ A₁ ψ).space ∪ (glued₂ K₂ A₂ ψ').space := by
  change ⋃ t ∈ (glued₁ K₁ A₁ ψ).faces ∪ (glued₂ K₂ A₂ ψ').faces,
    convexHull ℝ (t : Set (E × F × ℝ)) = _
  exact biUnion_union _ _ _

theorem gluedComplex_faces_finite [Finite K₁.faces] [Finite K₂.faces]
    (h : IsGlueIso A₁ A₂ ψ ψ') (hA₂ : A₂.faces ⊆ K₂.faces)
    (hfull₁ : ∀ s ∈ K₁.faces, (∀ v ∈ s, {v} ∈ A₁.faces) → s ∈ A₁.faces) :
    (gluedComplex K₁ K₂ h hA₂ hfull₁).faces.Finite :=
  (glued₁_faces_finite K₁ A₁ ψ).union (glued₂_faces_finite K₂ A₂ ψ')

theorem glued₁_space_inter_glued₂_space (h : IsGlueIso A₁ A₂ ψ ψ') (hA₁ : A₁.faces ⊆ K₁.faces)
    (hA₂ : A₂.faces ⊆ K₂.faces)
    (hfull₁ : ∀ s ∈ K₁.faces, (∀ v ∈ s, {v} ∈ A₁.faces) → s ∈ A₁.faces) :
    (glued₁ K₁ A₁ ψ).space ∩ (glued₂ K₂ A₂ ψ').space =
      simplicialMap K₁ (glueEmbed₁ A₁ ψ) '' A₁.space := by
  apply Subset.antisymm
  · rintro z ⟨hz₁, hz₂⟩
    obtain ⟨t₁, ht₁, hzt₁⟩ := (glued₁ K₁ A₁ ψ).mem_space_iff.mp hz₁
    have hz₀ : glueHeight E F z = 0 := glueHeight_eq_zero_of_mem K₁ K₂ A₁ A₂ ψ ψ' hz₁ hz₂
    have hz₁' := mem_convexHull_filter_of_eq_zero _
      (glueHeight_nonneg_of_mem_glued₁_face K₁ A₁ ψ ht₁) hzt₁ hz₀
    obtain ⟨s, hs, hst⟩ :=
      exists_face_filter_glued₁ K₁ hfull₁ ht₁ (nonempty_of_mem_convexHull hz₁')
    rw [hst, ← image_convexHull_simplicialMap K₁ _ (hA₁ hs)
      (glueEmbed₁_injective A₁ ψ).injOn] at hz₁'
    obtain ⟨x, hx, rfl⟩ := hz₁'
    exact ⟨x, A₁.convexHull_subset_space hs hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hxs⟩ := A₁.mem_space_iff.mp hx
    have hmem := simplicialMap_mem_convexHull_image K₁ (glueEmbed₁ A₁ ψ) (hA₁ hs) hxs
    refine ⟨(glued₁ K₁ A₁ ψ).convexHull_subset_space ⟨s, hA₁ hs, rfl⟩ hmem, ?_⟩
    rw [image_glueEmbed₁_eq h hs] at hmem
    exact (glued₂ K₂ A₂ ψ').convexHull_subset_space ⟨_, hA₂ (h.image₁ s hs), rfl⟩ hmem

omit [DecidableEq E] [DecidableEq F] in
theorem glueSnd_simplicialMap_of_mem (hA₁ : A₁.faces ⊆ K₁.faces) {x : E} (hx : x ∈ A₁.space) :
    glueSnd E F (simplicialMap K₁ (glueEmbed₁ A₁ ψ) x) = simplicialMap A₁ ψ x := by
  obtain ⟨s, hs, hxs⟩ := A₁.mem_space_iff.mp hx
  rw [simplicialMap_eq_of_mem K₁ _ (hA₁ hs) hxs, simplicialMap_eq_of_mem A₁ ψ hs hxs,
    affineMap_apply_sum_smul_comp _ _ (sum_weights hxs)]
  exact Finset.sum_congr rfl fun v _ => rfl

end GlueData

section GlueMap

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
  [DecidableEq E] [DecidableEq F]

variable (K₁ : Geometry.SimplicialComplex ℝ E) (A₁ : Geometry.SimplicialComplex ℝ E) (ψ : E → F)
  (g₁ : E → X) (g₂ : F → X)

open Classical in
noncomputable def gluedMap (z : E × F × ℝ) : X :=
  if z ∈ (glued₁ K₁ A₁ ψ).space then g₁ (glueFst E F z) else g₂ (glueSnd E F z)

omit [TopologicalSpace X] in
theorem gluedMap_of_mem {z : E × F × ℝ} (hz : z ∈ (glued₁ K₁ A₁ ψ).space) :
    gluedMap K₁ A₁ ψ g₁ g₂ z = g₁ (glueFst E F z) := by
  rw [gluedMap, if_pos hz]

omit [TopologicalSpace X] in
theorem gluedMap_of_notMem {z : E × F × ℝ} (hz : z ∉ (glued₁ K₁ A₁ ψ).space) :
    gluedMap K₁ A₁ ψ g₁ g₂ z = g₂ (glueSnd E F z) := by
  rw [gluedMap, if_neg hz]

variable {K₁ A₁ ψ g₁ g₂}

theorem PLPieceIn.exists_glue_of_full [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space X]
    {Y₁ Y₂ : Set X} (T₁ : PLPieceIn E n X Y₁) (T₂ : PLPieceIn F n X Y₂)
    {A₂ : Geometry.SimplicialComplex ℝ F} {ψ' : F → E} (h : IsGlueIso A₁ A₂ ψ ψ')
    (hA₁ : A₁.faces ⊆ T₁.complex.faces) (hA₂ : A₂.faces ⊆ T₂.complex.faces)
    (hfull₁ : ∀ s ∈ T₁.complex.faces, (∀ v ∈ s, {v} ∈ A₁.faces) → s ∈ A₁.faces)
    (hcompat : ∀ x ∈ A₁.space, T₂.map (simplicialMap A₁ ψ x) = T₁.map x)
    (hoverlap : Y₁ ∩ Y₂ = T₁.map '' A₁.space) :
    ∃ T : PLPieceIn (E × F × ℝ) n X (Y₁ ∪ Y₂),
      T.complex = gluedComplex T₁.complex T₂.complex h hA₂ hfull₁ ∧
        T.map = gluedMap T₁.complex A₁ ψ T₁.map T₂.map := by
  have hfin₁ := T₁.finite_faces.to_subtype
  have hfin₂ := T₂.finite_faces.to_subtype
  have hfinL₁ := (glued₁_faces_finite T₁.complex A₁ ψ).to_subtype
  have hfinL₂ := (glued₂_faces_finite T₂.complex A₂ ψ').to_subtype
  have hA₁sub : A₁.space ⊆ T₁.complex.space := space_mono_of_faces_subset hA₁
  have hι₁mem : ∀ x ∈ T₁.complex.space,
      simplicialMap T₁.complex (glueEmbed₁ A₁ ψ) x ∈ (glued₁ T₁.complex A₁ ψ).space :=
    fun x hx => simplicialMap_mem_glued₁ _ _ _ hx
  have hι₂mem : ∀ y ∈ T₂.complex.space,
      simplicialMap T₂.complex (glueEmbed₂ A₂ ψ') y ∈ (glued₂ T₂.complex A₂ ψ').space :=
    fun y hy => simplicialMap_mem_glued₂ _ _ _ hy
  have hπ₁ : ∀ x ∈ T₁.complex.space,
      glueFst E F (simplicialMap T₁.complex (glueEmbed₁ A₁ ψ) x) = x :=
    fun x hx => glueFst_simplicialMap _ _ _ hx
  have hπ₂ : ∀ y ∈ T₂.complex.space,
      glueSnd E F (simplicialMap T₂.complex (glueEmbed₂ A₂ ψ') y) = y :=
    fun y hy => glueSnd_simplicialMap _ _ _ hy
  have hι₁π : ∀ z ∈ (glued₁ T₁.complex A₁ ψ).space,
      simplicialMap T₁.complex (glueEmbed₁ A₁ ψ) (glueFst E F z) = z :=
    fun z hz => simplicialMap_glueFst _ _ _ hz
  have hι₂π : ∀ z ∈ (glued₂ T₂.complex A₂ ψ').space,
      simplicialMap T₂.complex (glueEmbed₂ A₂ ψ') (glueSnd E F z) = z :=
    fun z hz => simplicialMap_glueSnd _ _ _ hz
  have hπ₁mem : ∀ z ∈ (glued₁ T₁.complex A₁ ψ).space, glueFst E F z ∈ T₁.complex.space :=
    fun z hz => glueFst_mem_of_mem_glued₁ _ _ _ hz
  have hπ₂mem : ∀ z ∈ (glued₂ T₂.complex A₂ ψ').space, glueSnd E F z ∈ T₂.complex.space :=
    fun z hz => glueSnd_mem_of_mem_glued₂ _ _ _ hz
  have hinter := glued₁_space_inter_glued₂_space T₁.complex T₂.complex h hA₁ hA₂ hfull₁
  have hLspace := gluedComplex_space T₁.complex T₂.complex h hA₂ hfull₁
  have hg₁ : ∀ z ∈ (glued₁ T₁.complex A₁ ψ).space,
      gluedMap T₁.complex A₁ ψ T₁.map T₂.map z = T₁.map (glueFst E F z) :=
    fun z hz => gluedMap_of_mem _ _ _ _ _ hz
  have hg₂ : ∀ z ∈ (glued₂ T₂.complex A₂ ψ').space,
      gluedMap T₁.complex A₁ ψ T₁.map T₂.map z = T₂.map (glueSnd E F z) := by
    intro z hz
    rcases Classical.em (z ∈ (glued₁ T₁.complex A₁ ψ).space) with hz₁ | hz₁
    · rw [gluedMap_of_mem _ _ _ _ _ hz₁]
      have hz' : z ∈ (glued₁ T₁.complex A₁ ψ).space ∩ (glued₂ T₂.complex A₂ ψ').space :=
        ⟨hz₁, hz⟩
      rw [hinter] at hz'
      obtain ⟨x, hx, rfl⟩ := hz'
      rw [hπ₁ x (hA₁sub hx), glueSnd_simplicialMap_of_mem T₁.complex hA₁ hx, hcompat x hx]
    · exact gluedMap_of_notMem _ _ _ _ _ hz₁
  have hmaps : MapsTo (gluedMap T₁.complex A₁ ψ T₁.map T₂.map)
      (gluedComplex T₁.complex T₂.complex h hA₂ hfull₁).space (Y₁ ∪ Y₂) := by
    intro z hz
    rw [hLspace] at hz
    rcases Classical.em (z ∈ (glued₁ T₁.complex A₁ ψ).space) with hz₁ | hz₁
    · rw [hg₁ z hz₁]
      exact Or.inl (T₁.bijOn.mapsTo (hπ₁mem z hz₁))
    · have hz₂ : z ∈ (glued₂ T₂.complex A₂ ψ').space := hz.resolve_left hz₁
      rw [hg₂ z hz₂]
      exact Or.inr (T₂.bijOn.mapsTo (hπ₂mem z hz₂))
  have hsurj : SurjOn (gluedMap T₁.complex A₁ ψ T₁.map T₂.map)
      (gluedComplex T₁.complex T₂.complex h hA₂ hfull₁).space (Y₁ ∪ Y₂) := by
    rintro y (hy | hy)
    · obtain ⟨x, hx, rfl⟩ := T₁.bijOn.surjOn hy
      refine ⟨simplicialMap T₁.complex (glueEmbed₁ A₁ ψ) x, ?_, ?_⟩
      · rw [hLspace]
        exact Or.inl (hι₁mem x hx)
      · rw [hg₁ _ (hι₁mem x hx), hπ₁ x hx]
    · obtain ⟨x, hx, rfl⟩ := T₂.bijOn.surjOn hy
      refine ⟨simplicialMap T₂.complex (glueEmbed₂ A₂ ψ') x, ?_, ?_⟩
      · rw [hLspace]
        exact Or.inr (hι₂mem x hx)
      · rw [hg₂ _ (hι₂mem x hx), hπ₂ x hx]
  have h11 : ∀ z ∈ (glued₁ T₁.complex A₁ ψ).space, ∀ z' ∈ (glued₁ T₁.complex A₁ ψ).space,
      gluedMap T₁.complex A₁ ψ T₁.map T₂.map z = gluedMap T₁.complex A₁ ψ T₁.map T₂.map z' →
      z = z' := by
    intro z hz z' hz' hzz'
    rw [hg₁ z hz, hg₁ z' hz'] at hzz'
    rw [← hι₁π z hz, ← hι₁π z' hz', T₁.bijOn.injOn (hπ₁mem z hz) (hπ₁mem z' hz') hzz']
  have h22 : ∀ z ∈ (glued₂ T₂.complex A₂ ψ').space, ∀ z' ∈ (glued₂ T₂.complex A₂ ψ').space,
      gluedMap T₁.complex A₁ ψ T₁.map T₂.map z = gluedMap T₁.complex A₁ ψ T₁.map T₂.map z' →
      z = z' := by
    intro z hz z' hz' hzz'
    rw [hg₂ z hz, hg₂ z' hz'] at hzz'
    rw [← hι₂π z hz, ← hι₂π z' hz', T₂.bijOn.injOn (hπ₂mem z hz) (hπ₂mem z' hz') hzz']
  have h12 : ∀ z ∈ (glued₁ T₁.complex A₁ ψ).space, ∀ z' ∈ (glued₂ T₂.complex A₂ ψ').space,
      gluedMap T₁.complex A₁ ψ T₁.map T₂.map z = gluedMap T₁.complex A₁ ψ T₁.map T₂.map z' →
      z ∈ (glued₂ T₂.complex A₂ ψ').space := by
    intro z hz z' hz' hzz'
    have hy : gluedMap T₁.complex A₁ ψ T₁.map T₂.map z ∈ Y₁ ∩ Y₂ := by
      refine ⟨?_, ?_⟩
      · rw [hg₁ z hz]
        exact T₁.bijOn.mapsTo (hπ₁mem z hz)
      · rw [hzz', hg₂ z' hz']
        exact T₂.bijOn.mapsTo (hπ₂mem z' hz')
    rw [hoverlap] at hy
    obtain ⟨x, hx, hxz⟩ := hy
    rw [hg₁ z hz] at hxz
    have hxeq : x = glueFst E F z := T₁.bijOn.injOn (hA₁sub hx) (hπ₁mem z hz) hxz
    have hz' : z ∈ simplicialMap T₁.complex (glueEmbed₁ A₁ ψ) '' A₁.space := by
      refine ⟨x, hx, ?_⟩
      rw [hxeq]
      exact hι₁π z hz
    rw [← hinter] at hz'
    exact hz'.2
  have hinj : InjOn (gluedMap T₁.complex A₁ ψ T₁.map T₂.map)
      (gluedComplex T₁.complex T₂.complex h hA₂ hfull₁).space := by
    intro z hz z' hz' hzz'
    rw [hLspace] at hz hz'
    rcases Classical.em (z ∈ (glued₂ T₂.complex A₂ ψ').space) with hz₂ | hz₂ <;>
      rcases Classical.em (z' ∈ (glued₂ T₂.complex A₂ ψ').space) with hz₂' | hz₂'
    · exact h22 z hz₂ z' hz₂' hzz'
    · exact absurd (h12 z' (hz'.resolve_right hz₂') z hz₂ hzz'.symm) hz₂'
    · exact absurd (h12 z (hz.resolve_right hz₂) z' hz₂' hzz') hz₂
    · exact h11 z (hz.resolve_right hz₂) z' (hz'.resolve_right hz₂') hzz'
  have hbij : BijOn (gluedMap T₁.complex A₁ ψ T₁.map T₂.map)
      (gluedComplex T₁.complex T₂.complex h hA₂ hfull₁).space (Y₁ ∪ Y₂) :=
    ⟨hmaps, hinj, hsurj⟩
  have hpoly₁ : IsPolyhedron (glued₁ T₁.complex A₁ ψ).space :=
    PiecewiseLinear.isPolyhedron_space (glued₁ T₁.complex A₁ ψ)
  have hpoly₂ : IsPolyhedron (glued₂ T₂.complex A₂ ψ').space :=
    PiecewiseLinear.isPolyhedron_space (glued₂ T₂.complex A₂ ψ')
  have hclosed₁ : IsClosed (glued₁ T₁.complex A₁ ψ).space := hpoly₁.isClosed
  have hclosed₂ : IsClosed (glued₂ T₂.complex A₂ ψ').space := hpoly₂.isClosed
  have hcont : ContinuousOn (gluedMap T₁.complex A₁ ψ T₁.map T₂.map)
      (gluedComplex T₁.complex T₂.complex h hA₂ hfull₁).space := by
    rw [hLspace]
    refine ContinuousOn.union_of_isClosed ?_ ?_ hclosed₁ hclosed₂
    · exact (T₁.continuousOn.comp continuous_glueFst.continuousOn hπ₁mem).congr hg₁
    · exact (T₂.continuousOn.comp continuous_glueSnd.continuousOn hπ₂mem).congr hg₂
  have hπ₁pl : IsPiecewiseAffineOn (glueFst E F) (glued₁ T₁.complex A₁ ψ).space :=
    (isPiecewiseAffineOn_of_affine (glueFst E F) isOpen_univ).mono_of_isPolyhedron hpoly₁
      (subset_univ _)
  have hπ₂pl : IsPiecewiseAffineOn (glueSnd E F) (glued₂ T₂.complex A₂ ψ').space :=
    (isPiecewiseAffineOn_of_affine (glueSnd E F) isOpen_univ).mono_of_isPolyhedron hpoly₂
      (subset_univ _)
  have hchart : ∀ e ∈ atlas (EuclideanSpace ℝ (Fin n)) X,
      IsPiecewiseAffineOn (e ∘ gluedMap T₁.complex A₁ ψ T₁.map T₂.map)
        ((gluedComplex T₁.complex T₂.complex h hA₂ hfull₁).space ∩
          gluedMap T₁.complex A₁ ψ T₁.map T₂.map ⁻¹' e.source) := by
    intro e he
    rw [hLspace, union_inter_distrib_right]
    have hD₁ : IsPiecewiseAffineOn (e ∘ gluedMap T₁.complex A₁ ψ T₁.map T₂.map)
        ((glued₁ T₁.complex A₁ ψ).space ∩ gluedMap T₁.complex A₁ ψ T₁.map T₂.map ⁻¹' e.source) := by
      have h1 := (T₁.isPiecewiseAffineOn_chart e he).comp hπ₁pl
      have heq : (glued₁ T₁.complex A₁ ψ).space ∩
          glueFst E F ⁻¹' (T₁.complex.space ∩ T₁.map ⁻¹' e.source) =
          (glued₁ T₁.complex A₁ ψ).space ∩ gluedMap T₁.complex A₁ ψ T₁.map T₂.map ⁻¹' e.source := by
        ext z
        simp only [mem_inter_iff, mem_preimage]
        constructor
        · rintro ⟨hz, -, hz'⟩
          refine ⟨hz, ?_⟩
          rw [hg₁ z hz]
          exact hz'
        · rintro ⟨hz, hz'⟩
          refine ⟨hz, hπ₁mem z hz, ?_⟩
          rw [← hg₁ z hz]
          exact hz'
      rw [heq] at h1
      refine h1.congr fun z hz => ?_
      change e (gluedMap T₁.complex A₁ ψ T₁.map T₂.map z) = e (T₁.map (glueFst E F z))
      rw [hg₁ z hz.1]
    have hD₂ : IsPiecewiseAffineOn (e ∘ gluedMap T₁.complex A₁ ψ T₁.map T₂.map)
        ((glued₂ T₂.complex A₂ ψ').space ∩ gluedMap T₁.complex A₁ ψ T₁.map T₂.map ⁻¹' e.source) := by
      have h1 := (T₂.isPiecewiseAffineOn_chart e he).comp hπ₂pl
      have heq : (glued₂ T₂.complex A₂ ψ').space ∩
          glueSnd E F ⁻¹' (T₂.complex.space ∩ T₂.map ⁻¹' e.source) =
          (glued₂ T₂.complex A₂ ψ').space ∩ gluedMap T₁.complex A₁ ψ T₁.map T₂.map ⁻¹' e.source := by
        ext z
        simp only [mem_inter_iff, mem_preimage]
        constructor
        · rintro ⟨hz, -, hz'⟩
          refine ⟨hz, ?_⟩
          rw [hg₂ z hz]
          exact hz'
        · rintro ⟨hz, hz'⟩
          refine ⟨hz, hπ₂mem z hz, ?_⟩
          rw [← hg₂ z hz]
          exact hz'
      rw [heq] at h1
      refine h1.congr fun z hz => ?_
      change e (gluedMap T₁.complex A₁ ψ T₁.map T₂.map z) = e (T₂.map (glueSnd E F z))
      rw [hg₂ z hz.1]
    refine hD₁.union_of_open hD₂ ?_ ?_
    · intro z hz hz'
      refine ⟨(glued₂ T₂.complex A₂ ψ').spaceᶜ, hclosed₂.isOpen_compl,
        fun hz₂ => hz' ⟨hz₂, hz.2⟩, ?_⟩
      rintro w ⟨hw | hw, hw'⟩
      · exact hw
      · exact absurd hw.1 hw'
    · intro z hz hz'
      refine ⟨(glued₁ T₁.complex A₁ ψ).spaceᶜ, hclosed₁.isOpen_compl,
        fun hz₁ => hz' ⟨hz₁, hz.2⟩, ?_⟩
      rintro w ⟨hw | hw, hw'⟩
      · exact absurd hw.1 hw'
      · exact hw
  have hsymm : ∀ e ∈ atlas (EuclideanSpace ℝ (Fin n)) X,
      IsPiecewiseAffineOn (Function.invFunOn (gluedMap T₁.complex A₁ ψ T₁.map T₂.map)
        (gluedComplex T₁.complex T₂.complex h hA₂ hfull₁).space ∘ e.symm)
        (e.target ∩ e.symm ⁻¹' (Y₁ ∪ Y₂)) := by
    intro e he
    rw [preimage_union, inter_union_distrib_left]
    have hW₁ : IsPiecewiseAffineOn (Function.invFunOn (gluedMap T₁.complex A₁ ψ T₁.map T₂.map)
        (gluedComplex T₁.complex T₂.complex h hA₂ hfull₁).space ∘ e.symm)
        (e.target ∩ e.symm ⁻¹' Y₁) := by
      have h1 := (isPiecewiseAffineOn_simplicialMap T₁.complex (glueEmbed₁ A₁ ψ)).comp
        (T₁.isPiecewiseAffineOn_chart_symm e he)
      have hsub : e.target ∩ e.symm ⁻¹' Y₁ ⊆
          (Function.invFunOn T₁.map T₁.complex.space ∘ e.symm) ⁻¹' T₁.complex.space :=
        fun y hy => T₁.bijOn.surjOn.mapsTo_invFunOn hy.2
      rw [inter_eq_left.mpr hsub] at h1
      refine h1.congr fun y hy => ?_
      change Function.invFunOn (gluedMap T₁.complex A₁ ψ T₁.map T₂.map)
        (gluedComplex T₁.complex T₂.complex h hA₂ hfull₁).space (e.symm y) =
        simplicialMap T₁.complex (glueEmbed₁ A₁ ψ)
          (Function.invFunOn T₁.map T₁.complex.space (e.symm y))
      have hx₁ : Function.invFunOn T₁.map T₁.complex.space (e.symm y) ∈ T₁.complex.space :=
        T₁.bijOn.surjOn.mapsTo_invFunOn hy.2
      have hx₁' : T₁.map (Function.invFunOn T₁.map T₁.complex.space (e.symm y)) = e.symm y :=
        T₁.bijOn.invOn_invFunOn.2 hy.2
      have hmem : simplicialMap T₁.complex (glueEmbed₁ A₁ ψ)
          (Function.invFunOn T₁.map T₁.complex.space (e.symm y)) ∈
          (gluedComplex T₁.complex T₂.complex h hA₂ hfull₁).space := by
        rw [hLspace]
        exact Or.inl (hι₁mem _ hx₁)
      have hgι : gluedMap T₁.complex A₁ ψ T₁.map T₂.map (simplicialMap T₁.complex (glueEmbed₁ A₁ ψ)
          (Function.invFunOn T₁.map T₁.complex.space (e.symm y))) = e.symm y := by
        rw [hg₁ _ (hι₁mem _ hx₁), hπ₁ _ hx₁, hx₁']
      have hz := Function.invFunOn_pos ⟨_, hmem, hgι⟩
      exact hinj hz.1 hmem (hz.2.trans hgι.symm)
    have hW₂ : IsPiecewiseAffineOn (Function.invFunOn (gluedMap T₁.complex A₁ ψ T₁.map T₂.map)
        (gluedComplex T₁.complex T₂.complex h hA₂ hfull₁).space ∘ e.symm)
        (e.target ∩ e.symm ⁻¹' Y₂) := by
      have h1 := (isPiecewiseAffineOn_simplicialMap T₂.complex (glueEmbed₂ A₂ ψ')).comp
        (T₂.isPiecewiseAffineOn_chart_symm e he)
      have hsub : e.target ∩ e.symm ⁻¹' Y₂ ⊆
          (Function.invFunOn T₂.map T₂.complex.space ∘ e.symm) ⁻¹' T₂.complex.space :=
        fun y hy => T₂.bijOn.surjOn.mapsTo_invFunOn hy.2
      rw [inter_eq_left.mpr hsub] at h1
      refine h1.congr fun y hy => ?_
      change Function.invFunOn (gluedMap T₁.complex A₁ ψ T₁.map T₂.map)
        (gluedComplex T₁.complex T₂.complex h hA₂ hfull₁).space (e.symm y) =
        simplicialMap T₂.complex (glueEmbed₂ A₂ ψ')
          (Function.invFunOn T₂.map T₂.complex.space (e.symm y))
      have hx₂ : Function.invFunOn T₂.map T₂.complex.space (e.symm y) ∈ T₂.complex.space :=
        T₂.bijOn.surjOn.mapsTo_invFunOn hy.2
      have hx₂' : T₂.map (Function.invFunOn T₂.map T₂.complex.space (e.symm y)) = e.symm y :=
        T₂.bijOn.invOn_invFunOn.2 hy.2
      have hmem : simplicialMap T₂.complex (glueEmbed₂ A₂ ψ')
          (Function.invFunOn T₂.map T₂.complex.space (e.symm y)) ∈
          (gluedComplex T₁.complex T₂.complex h hA₂ hfull₁).space := by
        rw [hLspace]
        exact Or.inr (hι₂mem _ hx₂)
      have hgι : gluedMap T₁.complex A₁ ψ T₁.map T₂.map (simplicialMap T₂.complex (glueEmbed₂ A₂ ψ')
          (Function.invFunOn T₂.map T₂.complex.space (e.symm y))) = e.symm y := by
        rw [hg₂ _ (hι₂mem _ hx₂), hπ₂ _ hx₂, hx₂']
      have hz := Function.invFunOn_pos ⟨_, hmem, hgι⟩
      exact hinj hz.1 hmem (hz.2.trans hgι.symm)
    refine hW₁.union_of_open hW₂ ?_ ?_
    · intro y hy hy'
      refine ⟨e.target ∩ e.symm ⁻¹' Y₂ᶜ, e.continuousOn_symm.isOpen_inter_preimage e.open_target
        T₂.isCompact.isClosed.isOpen_compl, ⟨hy.1, fun h2 => hy' ⟨hy.1, h2⟩⟩, ?_⟩
      rintro w ⟨hw | hw, -, hw'⟩
      · exact hw
      · exact absurd hw.2 hw'
    · intro y hy hy'
      refine ⟨e.target ∩ e.symm ⁻¹' Y₁ᶜ, e.continuousOn_symm.isOpen_inter_preimage e.open_target
        T₁.isCompact.isClosed.isOpen_compl, ⟨hy.1, fun h1 => hy' ⟨hy.1, h1⟩⟩, ?_⟩
      rintro w ⟨hw | hw, -, hw'⟩
      · exact absurd hw.2 hw'
      · exact hw
  exact ⟨⟨gluedComplex T₁.complex T₂.complex h hA₂ hfull₁,
    gluedComplex_faces_finite T₁.complex T₂.complex h hA₂ hfull₁,
    gluedMap T₁.complex A₁ ψ T₁.map T₂.map, hbij, hcont, hchart, hsymm⟩, rfl, rfl⟩

theorem PLPieceIn.glue_of_full [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space X]
    {Y₁ Y₂ : Set X} (T₁ : PLPieceIn E n X Y₁) (T₂ : PLPieceIn F n X Y₂)
    {A₂ : Geometry.SimplicialComplex ℝ F} {ψ' : F → E} (h : IsGlueIso A₁ A₂ ψ ψ')
    (hA₁ : A₁.faces ⊆ T₁.complex.faces) (hA₂ : A₂.faces ⊆ T₂.complex.faces)
    (hfull₁ : ∀ s ∈ T₁.complex.faces, (∀ v ∈ s, {v} ∈ A₁.faces) → s ∈ A₁.faces)
    (hcompat : ∀ x ∈ A₁.space, T₂.map (simplicialMap A₁ ψ x) = T₁.map x)
    (hoverlap : Y₁ ∩ Y₂ = T₁.map '' A₁.space) :
    Nonempty (PLPieceIn (E × F × ℝ) n X (Y₁ ∪ Y₂)) := by
  obtain ⟨T, -, -⟩ := T₁.exists_glue_of_full T₂ h hA₁ hA₂ hfull₁ hcompat hoverlap
  exact ⟨T⟩

end GlueMap

theorem mem_faces_of_mem_relDerived_of_forall_singleton_mem {K L L' : Geometry.SimplicialComplex ℝ E}
    {c : Finset E → E} (hL : L.faces ⊆ K.faces) (hL' : IsSubdivision L' L)
    (hc : ∀ s ∈ K.faces, c s ∈ openSimplex s) [DecidableEq E] {f : Finset E}
    (hf : f ∈ (relDerived hL hL' hc).faces) (hv : ∀ v ∈ f, {v} ∈ L'.faces) : f ∈ L'.faces := by
  obtain ⟨τ, d, hrel, rfl⟩ := (mem_relDerived_faces_iff hL hL' hc).mp hf
  have hd : d = ∅ := by
    by_contra hne
    obtain ⟨s, hs⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hcs : c s ∈ L'.space :=
      L'.convexHull_subset_space
        (hv (c s) (Finset.mem_union_right _ (Finset.mem_image_of_mem c hs)))
        (subset_convexHull ℝ _ (by simp))
    rw [hL'.space_eq] at hcs
    exact c_notMem_space hL hc (hrel.flag.mem_faces hs) (hrel.notMem s hs) hcs
  subst hd
  rw [Finset.image_empty, Finset.union_empty]
  rcases hrel.base with h0 | h0
  · rcases hrel.nonempty with hne | hne
    · exact absurd h0 hne.ne_empty
    · exact absurd hne Finset.not_nonempty_empty
  · exact h0

theorem PLPieceIn.glue {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [DecidableEq E] [DecidableEq F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space X]
    {Y₁ Y₂ : Set X} (T₁ : PLPieceIn E n X Y₁) (T₂ : PLPieceIn F n X Y₂)
    {A₁ : Geometry.SimplicialComplex ℝ E} {A₂ : Geometry.SimplicialComplex ℝ F}
    {ψ : E → F} {ψ' : F → E} (h : IsGlueIso A₁ A₂ ψ ψ')
    (hA₁ : A₁.faces ⊆ T₁.complex.faces) (hA₂ : A₂.faces ⊆ T₂.complex.faces)
    (hcompat : ∀ x ∈ A₁.space, T₂.map (simplicialMap A₁ ψ x) = T₁.map x)
    (hoverlap : Y₁ ∩ Y₂ = T₁.map '' A₁.space) :
    Nonempty (PLPieceIn (E × F × ℝ) n X (Y₁ ∪ Y₂)) := by
  have hfin₁ := T₁.finite_faces.to_subtype
  have hfinA₁ := (T₁.finite_faces.subset hA₁).to_subtype
  have hc := centroid_mem_openSimplex_of_mem_faces T₁.complex
  let T₁' := T₁.subdivide (relDerived hA₁ (IsSubdivision.refl A₁) hc)
    (relDerived_isSubdivision hA₁ (IsSubdivision.refl A₁) hc)
    (relDerived_faces_finite hA₁ (IsSubdivision.refl A₁) hc)
  exact T₁'.glue_of_full T₂ h (faces_subset_relDerived hA₁ (IsSubdivision.refl A₁) hc) hA₂
    (fun s hs hv => mem_faces_of_mem_relDerived_of_forall_singleton_mem hA₁
      (IsSubdivision.refl A₁) hc hs hv) hcompat hoverlap

end DifferentialGeometry.Topology.PiecewiseLinear
