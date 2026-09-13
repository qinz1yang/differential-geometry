import DifferentialGeometry.Topology.PiecewiseLinear.PLImage
import DifferentialGeometry.Topology.PiecewiseLinear.SubdivisionTransport

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_isSubdivision_singleton_mem [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {x : E} (hx : x ∈ K.space) :
    ∃ K' : Geometry.SimplicialComplex ℝ E, IsSubdivision K' K ∧ K'.faces.Finite ∧
      ({x} : Finset E) ∈ K'.faces := by
  have : Subsingleton {u // u ∈ ({x} : Finset E)} :=
    ⟨fun a b => Subtype.ext ((Finset.mem_singleton.mp a.2).trans
      (Finset.mem_singleton.mp b.2).symm)⟩
  have hpoly : IsPolyhedron ({x} : Set E) := by
    have h := isPolyhedron_convexHull_of_affineIndependent ({x} : Finset E)
      (affineIndependent_of_subsingleton ℝ _)
    rwa [Finset.coe_singleton, convexHull_singleton] at h
  obtain ⟨K', hsub, hfin, hunion⟩ := exists_isSubdivision_subcomplexes K
    (fun _ : Unit => ({x} : Set E)) (fun _ => hpoly) fun _ => singleton_subset_iff.mpr hx
  have hxmem : x ∈ ({x} : Set E) := rfl
  obtain ⟨s, ⟨hs, hsx⟩, -⟩ := mem_iUnion₂.mp ((hunion ()).subset hxmem)
  have hmem : ∀ w ∈ s, w = x := fun w hw =>
    Set.mem_singleton_iff.mp (hsx (subset_convexHull ℝ _ (Finset.mem_coe.mpr hw)))
  obtain ⟨v, hv⟩ := K'.nonempty_of_mem_faces hs
  have hseq : s = {x} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hmem v hv ▸ hv, hmem⟩
  exact ⟨K', hsub, hfin, hseq ▸ hs⟩

theorem exists_isGlueIso_of_isPLHomeomorphOn [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [DecidableEq E] [DecidableEq F] (K₀ : Geometry.SimplicialComplex ℝ E) [Finite K₀.faces]
    (K : Geometry.SimplicialComplex ℝ F) [Finite K.faces] {f : E → F}
    (hf : IsPLHomeomorphOn f K₀.space K.space) :
    ∃ (K₀' : Geometry.SimplicialComplex ℝ E) (K' : Geometry.SimplicialComplex ℝ F) (φ' : F → E),
      IsSubdivision K₀' K₀ ∧ K₀'.faces.Finite ∧ IsSubdivision K' K ∧ K'.faces.Finite ∧
        IsGlueIso K₀' K' f φ' ∧ EqOn (simplicialMap K₀' f) f K₀.space := by
  obtain ⟨K₁, hK₁, hfin₁, hunion⟩ := exists_isSubdivision_subcomplexes K₀
    (fun τ : K.faces => K₀.space ∩ f ⁻¹' convexHull ℝ ((τ : Finset F) : Set F))
    (fun τ => hf.isPolyhedron_preimage
      (isPolyhedron_convexHull_of_affineIndependent _ (K.indep τ.2))
      (K.convexHull_subset_space τ.2))
    fun _ => inter_subset_left
  have : Finite K₁.faces := hfin₁.to_subtype
  have hspace₁ : K₁.space = K₀.space := hK₁.space_eq
  have hpa : IsPiecewiseAffineOn f K₁.space := by
    rw [hspace₁]
    exact hf.isPiecewiseAffineOn
  obtain ⟨K₂, hK₂, hfin₂, hAff⟩ := hpa.exists_isSubdivision_affineOn_faces K₁
  have : Finite K₂.faces := hfin₂.to_subtype
  have hspace₂ : K₂.space = K₀.space := hK₂.space_eq.trans hspace₁
  have hinj : InjOn f K₀.space := hf.bijOn.injOn
  choose A hA using hAff
  have hsm : EqOn (simplicialMap K₂ f) f K₂.space := by
    intro y hy
    obtain ⟨σ, hσ, hyσ⟩ := K₂.mem_space_iff.mp hy
    rw [simplicialMap_eq_of_mem K₂ f hσ hyσ, hA _ hσ hyσ]
    conv_rhs => rw [← sum_weights_smul hyσ]
    rw [affineMap_apply_sum_smul (A _ hσ) (sum_weights hyσ)]
    exact Finset.sum_congr rfl fun v hv => by
      rw [hA _ hσ (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv))]
  have hind : ∀ σ ∈ K₂.faces, AffineIndependent ℝ ((↑) : {u // u ∈ σ.image f} → F) := by
    intro σ hσ
    have himg : σ.image f = σ.image (A σ hσ) :=
      Finset.image_congr fun v hv => hA σ hσ (subset_convexHull ℝ _ hv)
    rw [himg]
    refine affineIndependent_image_of_injOn_convexHull (A σ hσ) (K₂.indep hσ) ?_
    intro y hy z hz hyz
    have hyK : y ∈ K₀.space := hspace₂ ▸ K₂.convexHull_subset_space hσ hy
    have hzK : z ∈ K₀.space := hspace₂ ▸ K₂.convexHull_subset_space hσ hz
    exact hinj hyK hzK (by rw [hA σ hσ hy, hA σ hσ hz, hyz])
  have hinj' : InjOn (simplicialMap K₂ f) K₂.space := by
    intro y hy z hz hyz
    rw [hsm hy, hsm hz] at hyz
    exact hinj (hspace₂ ▸ hy) (hspace₂ ▸ hz) hyz
  have hsm₀ : EqOn (simplicialMap K₂ f) f K₀.space := by
    rw [← hspace₂]
    exact hsm
  obtain ⟨φ', hglue⟩ := exists_isGlueIso_simplicialImage K₂ f hind hinj'
  refine ⟨K₂, simplicialImage K₂ f hind hinj', φ', hK₂.trans hK₁, hfin₂, ⟨?_, ?_⟩,
    simplicialImage_faces_finite K₂ f hind hinj', hglue, hsm₀⟩
  · rw [simplicialImage_space K₂ f hind hinj', hsm.image_eq, hspace₂, hf.image_eq]
  · rintro t ⟨σ, hσ, rfl⟩
    obtain ⟨σ₁, hσ₁, hσσ₁⟩ := hK₂.exists_face_subset hσ
    have hxo : σ₁.centroid ℝ id ∈ openSimplex σ₁ :=
      centroid_mem_openSimplex (K₁.nonempty_of_mem_faces hσ₁)
    have hxσ₁ : σ₁.centroid ℝ id ∈ convexHull ℝ ((σ₁ : Finset E) : Set E) :=
      openSimplex_subset_convexHull σ₁ hxo
    have hx₀ : σ₁.centroid ℝ id ∈ K₀.space :=
      hspace₁ ▸ K₁.convexHull_subset_space hσ₁ hxσ₁
    obtain ⟨τ, hτ, hfxτ⟩ := K.mem_space_iff.mp (hf.bijOn.mapsTo hx₀)
    obtain ⟨s, ⟨hs, hsP⟩, hxs⟩ := mem_iUnion₂.mp ((hunion ⟨τ, hτ⟩).subset ⟨hx₀, hfxτ⟩)
    have hsubs : σ₁ ⊆ s := face_subset_of_mem_openSimplex_of_mem_convexHull K₁ hσ₁ hs hxo hxs
    refine ⟨τ, hτ, ?_⟩
    have himg : convexHull ℝ ((σ.image f : Finset F) : Set F) =
        f '' convexHull ℝ ((σ : Finset E) : Set E) := by
      rw [← image_convexHull_simplicialMap K₂ f hσ (injOn_of_injOn_simplicialMap K₂ f hinj' hσ)]
      exact (hsm.mono (K₂.convexHull_subset_space hσ)).image_eq
    rw [himg]
    rintro _ ⟨y, hy, rfl⟩
    exact (hsP (convexHull_mono (Finset.coe_subset.mpr hsubs) (hσσ₁ hy))).2

end DifferentialGeometry.Topology.PiecewiseLinear
