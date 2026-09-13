import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialMap
import DifferentialGeometry.Topology.PiecewiseLinear.Derived

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem injOn_of_injOn_simplicialMap (K : Geometry.SimplicialComplex ℝ E) (φ : E → F)
    (hinj : InjOn (simplicialMap K φ) K.space) {σ : Finset E} (hσ : σ ∈ K.faces) :
    InjOn φ (σ : Set E) := by
  intro v hv w hw hvw
  have hv' : {v} ∈ K.faces :=
    K.down_closed hσ (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  have hw' : {w} ∈ K.faces :=
    K.down_closed hσ (Finset.singleton_subset_iff.mpr hw) (Finset.singleton_nonempty w)
  refine hinj (K.convexHull_subset_space hσ (subset_convexHull ℝ _ hv))
    (K.convexHull_subset_space hσ (subset_convexHull ℝ _ hw)) ?_
  rw [simplicialMap_vertex K φ hv', simplicialMap_vertex K φ hw', hvw]

theorem image_convexHull_simplicialMap [DecidableEq F] (K : Geometry.SimplicialComplex ℝ E)
    (φ : E → F) {σ : Finset E} (hσ : σ ∈ K.faces) (hφ : InjOn φ (σ : Set E)) :
    simplicialMap K φ '' convexHull ℝ (σ : Set E) =
      convexHull ℝ ((σ.image φ : Finset F) : Set F) := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact simplicialMap_mem_convexHull_image K φ hσ hx
  · intro y hy
    obtain ⟨μ, hμ₀, hμ₁, hμy⟩ := mem_convexHull_iff_exists_weights.mp hy
    have hinj : ∀ v ∈ σ, ∀ w ∈ σ, φ v = φ w → v = w := fun v hv w hw h => hφ hv hw h
    rw [Finset.sum_image hinj] at hμ₁ hμy
    have hx : ∑ v ∈ σ, μ (φ v) • v ∈ convexHull ℝ (σ : Set E) :=
      (convex_convexHull ℝ _).sum_mem (fun v hv => hμ₀ _ (Finset.mem_image_of_mem φ hv)) hμ₁
        fun v hv => subset_convexHull ℝ _ (Finset.mem_coe.mpr hv)
    refine ⟨_, hx, ?_⟩
    rw [simplicialMap_eq_of_mem K φ hσ hx, ← hμy]
    exact Finset.sum_congr rfl fun v hv => by rw [weights_eq (K.indep hσ) hx hμ₁ rfl v hv]

section Image

variable [DecidableEq F] (K : Geometry.SimplicialComplex ℝ E) (φ : E → F)

def simplicialImageFaces : Set (Finset F) := {t | ∃ σ ∈ K.faces, t = σ.image φ}

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem simplicialImageFaces_isRelLowerSet :
    IsRelLowerSet (simplicialImageFaces K φ) Finset.Nonempty := by
  rintro t ⟨σ, hσ, rfl⟩
  refine ⟨(K.nonempty_of_mem_faces hσ).image φ, fun g hgt hg => ?_⟩
  refine ⟨σ.filter fun v => φ v ∈ g, ?_, (image_filter_mem_eq hgt).symm⟩
  refine K.down_closed hσ (Finset.filter_subset _ _) ?_
  obtain ⟨u, hu⟩ := hg
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (hgt hu)
  exact ⟨v, Finset.mem_filter.mpr ⟨hv, hu⟩⟩

theorem simplicialImageFaces_inter (hinj : InjOn (simplicialMap K φ) K.space) {t₁ t₂ : Finset F}
    (h₁ : t₁ ∈ simplicialImageFaces K φ) (h₂ : t₂ ∈ simplicialImageFaces K φ) :
    convexHull ℝ (t₁ : Set F) ∩ convexHull ℝ (t₂ : Set F) ⊆
      convexHull ℝ ((t₁ : Set F) ∩ (t₂ : Set F)) := by
  classical
  obtain ⟨σ₁, hσ₁, rfl⟩ := h₁
  obtain ⟨σ₂, hσ₂, rfl⟩ := h₂
  rintro y ⟨hy₁, hy₂⟩
  rw [← image_convexHull_simplicialMap K φ hσ₁ (injOn_of_injOn_simplicialMap K φ hinj hσ₁)] at hy₁
  rw [← image_convexHull_simplicialMap K φ hσ₂ (injOn_of_injOn_simplicialMap K φ hinj hσ₂)] at hy₂
  obtain ⟨x₁, hx₁, rfl⟩ := hy₁
  obtain ⟨x₂, hx₂, hx⟩ := hy₂
  have heq : x₂ = x₁ :=
    hinj (K.convexHull_subset_space hσ₂ hx₂) (K.convexHull_subset_space hσ₁ hx₁) hx
  rw [heq] at hx₂
  have hxν : x₁ ∈ convexHull ℝ ((σ₁ ∩ σ₂ : Finset E) : Set E) := by
    rw [Finset.coe_inter]
    exact K.inter_subset_convexHull hσ₁ hσ₂ ⟨hx₁, hx₂⟩
  have hν : σ₁ ∩ σ₂ ∈ K.faces := by
    refine K.down_closed hσ₁ Finset.inter_subset_left ?_
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.coe_empty, convexHull_empty] at hxν
    exact hxν
  rw [← Finset.coe_inter]
  exact convexHull_mono (Finset.coe_subset.mpr (Finset.image_inter_subset φ σ₁ σ₂))
    (simplicialMap_mem_convexHull_image K φ hν hxν)

variable (hind : ∀ σ ∈ K.faces, AffineIndependent ℝ ((↑) : {u // u ∈ σ.image φ} → F))
  (hinj : InjOn (simplicialMap K φ) K.space)

def simplicialImage : Geometry.SimplicialComplex ℝ F where
  faces := simplicialImageFaces K φ
  isRelLowerSet_faces := simplicialImageFaces_isRelLowerSet K φ
  indep := by
    rintro t ⟨σ, hσ, rfl⟩
    exact hind σ hσ
  inter_subset_convexHull h₁ h₂ := simplicialImageFaces_inter K φ hinj h₁ h₂

theorem mem_simplicialImage_faces_iff {t : Finset F} :
    t ∈ (simplicialImage K φ hind hinj).faces ↔ ∃ σ ∈ K.faces, t = σ.image φ := Iff.rfl

theorem simplicialImage_faces_finite [Finite K.faces] :
    (simplicialImage K φ hind hinj).faces.Finite := by
  refine ((Set.toFinite K.faces).image fun σ => σ.image φ).subset ?_
  rintro t ⟨σ, hσ, rfl⟩
  exact ⟨σ, hσ, rfl⟩

theorem simplicialImage_space :
    (simplicialImage K φ hind hinj).space = simplicialMap K φ '' K.space := by
  apply Subset.antisymm
  · intro y hy
    obtain ⟨t, ⟨σ, hσ, rfl⟩, hyt⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hy
    rw [← image_convexHull_simplicialMap K φ hσ (injOn_of_injOn_simplicialMap K φ hinj hσ)] at hyt
    obtain ⟨x, hx, rfl⟩ := hyt
    exact ⟨x, K.convexHull_subset_space hσ hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact Geometry.SimplicialComplex.mem_space_iff.mpr ⟨_, ⟨_, carrierFace_mem hx, rfl⟩,
      simplicialMap_mem_convexHull_image K φ (carrierFace_mem hx) (mem_convexHull_carrierFace hx)⟩

theorem isPLHomeomorphOn_simplicialImage [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [Finite K.faces] :
    IsPLHomeomorphOn (simplicialMap K φ) K.space (simplicialImage K φ hind hinj).space := by
  classical
  have : Finite (simplicialImage K φ hind hinj).faces :=
    (simplicialImage_faces_finite K φ hind hinj).to_subtype
  let V : Set E := {v | {v} ∈ K.faces}
  have hV : ∀ v ∈ V, v ∈ K.space := fun v hv =>
    K.convexHull_subset_space hv (subset_convexHull ℝ _ (by simp))
  have hφV : InjOn φ V := by
    intro v hv w hw hvw
    refine hinj (hV v hv) (hV w hw) ?_
    rw [simplicialMap_vertex K φ hv, simplicialMap_vertex K φ hw, hvw]
  have hmemV : ∀ σ ∈ K.faces, ∀ v ∈ σ, v ∈ V := fun σ hσ v hv =>
    K.down_closed hσ (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  have hψφ : ∀ σ ∈ K.faces, ∀ v ∈ σ, Function.invFunOn φ V (φ v) = v := fun σ hσ v hv =>
    hφV.leftInvOn_invFunOn (hmemV σ hσ v hv)
  refine isPLHomeomorphOn_simplicialMap K (simplicialImage K φ hind hinj) φ
    (Function.invFunOn φ V) (fun σ hσ => ⟨σ, hσ, rfl⟩) ?_ hψφ ?_
  · rintro t ⟨σ, hσ, rfl⟩
    rw [Finset.image_image]
    have : σ.image (Function.invFunOn φ V ∘ φ) = σ.image id :=
      Finset.image_congr fun v hv => hψφ σ hσ v hv
    rw [this, Finset.image_id]
    exact hσ
  · rintro t ⟨σ, hσ, rfl⟩ u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    rw [hψφ σ hσ v hv]

end Image

end DifferentialGeometry.Topology.PiecewiseLinear
