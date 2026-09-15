import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import Mathlib.Topology.Instances.ENat

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def levelPolygons (S : Set E) (ℓ : E → ℝ) (r : ℝ) : Set (Set E) :=
  {J | IsPLSphere 1 J ∧ J ⊆ S ∩ {x | ℓ x = r}}

def heightSingularPoints (S : Set E) (ℓ : E → ℝ) : Set E :=
  {p | p ∈ S ∧ ¬ HasPLCrossingAt S {x | ℓ x = ℓ p} p ∧
    ¬ {p} ∈ 𝓝[S ∩ {x | ℓ x = ℓ p}] p}

noncomputable def heightIndex (S : Set E) (ℓ : E → ℝ) : ℕ∞ :=
  ∑' p : heightSingularPoints S ℓ, ((levelPolygons S ℓ (ℓ p)).encard - 1)

theorem heightSingularPoints_subset (S : Set E) (ℓ : E → ℝ) :
    heightSingularPoints S ℓ ⊆ S := fun _ hp => hp.1

theorem notMem_heightSingularPoints_of_hasPLCrossingAt {S : Set E} {ℓ : E → ℝ} {p : E}
    (hp : HasPLCrossingAt S {x | ℓ x = ℓ p} p) : p ∉ heightSingularPoints S ℓ :=
  fun h => h.2.1 hp

theorem notMem_heightSingularPoints_of_isolated {S : Set E} {ℓ : E → ℝ} {p : E}
    (hp : {p} ∈ 𝓝[S ∩ {x | ℓ x = ℓ p}] p) : p ∉ heightSingularPoints S ℓ :=
  fun h => h.2.2 hp

theorem heightSingularPoints_subset_vertices [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices) :
    heightSingularPoints K.space ℓ ⊆ K.vertices := by
  intro p hp
  by_contra hpv
  exact hp.2.1 (hasPLCrossingAt_fiber_of_notMem_vertices K hK hdimE ℓ hℓ hinj
    ⟨hp.1, rfl⟩ hpv)

theorem finite_heightSingularPoints [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices) :
    (heightSingularPoints K.space ℓ).Finite :=
  (Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite K.faces)).subset
    (heightSingularPoints_subset_vertices K hK hdimE ℓ hℓ hinj)

theorem heightIndex_eq_zero_of_no_singular_points {S : Set E} {ℓ : E → ℝ}
    (h : heightSingularPoints S ℓ = ∅) : heightIndex S ℓ = 0 := by
  rw [heightIndex, h]
  exact tsum_empty (L := SummationFilter.unconditional _)
    (f := fun p : (∅ : Set E) => (levelPolygons S ℓ (ℓ p)).encard - 1)

theorem levelPolygons_image [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (h : E ≃ₜ F) (hh : IsPLHomeomorphOn h univ univ)
    {S : Set E} {ℓ : E → ℝ} {ℓ' : F → ℝ} (hℓ : ∀ x ∈ S, ℓ' (h x) = ℓ x) (r : ℝ) :
    levelPolygons (h '' S) ℓ' r = (fun J => h '' J) '' levelPolygons S ℓ r := by
  ext J
  constructor
  · rintro ⟨hJ, hJS⟩
    have hJ' : IsPLSphere 1 (h.symm '' J) :=
      hJ.of_isPLHomeomorphOn (hh.homeomorph_symm.restrict hJ.isPolyhedron (subset_univ J))
    refine ⟨h.symm '' J, ⟨hJ', ?_⟩, ?_⟩
    swap
    · change h '' (h.symm '' J) = J
      rw [image_image]
      simp only [h.apply_symm_apply, image_id']
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxy⟩ := (hJS hy).1
    have hsymm : h.symm y = x := by rw [← hxy, h.symm_apply_apply]
    rw [hsymm]
    refine ⟨hx, ?_⟩
    change ℓ x = r
    rw [← hℓ x hx, hxy]
    exact (hJS hy).2
  · rintro ⟨J, ⟨hJ, hJS⟩, rfl⟩
    refine ⟨hJ.of_isPLHomeomorphOn (hh.restrict hJ.isPolyhedron (subset_univ J)), ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨mem_image_of_mem h (hJS hx).1, (hℓ x (hJS hx).1).trans (hJS hx).2⟩

theorem encard_levelPolygons_image [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (h : E ≃ₜ F) (hh : IsPLHomeomorphOn h univ univ)
    {S : Set E} {ℓ : E → ℝ} {ℓ' : F → ℝ} (hℓ : ∀ x ∈ S, ℓ' (h x) = ℓ x) (r : ℝ) :
    (levelPolygons (h '' S) ℓ' r).encard = (levelPolygons S ℓ r).encard := by
  rw [levelPolygons_image h hh hℓ r]
  exact (Set.image_injective.mpr h.injective).injOn.encard_image

theorem eq_of_mem_height_fiber_of_minimum_vertex (K : Geometry.SimplicialComplex ℝ E)
    (ℓ : E →ₗ[ℝ] ℝ) (hinj : InjOn ℓ K.vertices) {v x : E} (hv : v ∈ K.vertices)
    (hmin : ∀ w ∈ K.vertices, ℓ v ≤ ℓ w) (hx : x ∈ K.space) (hlevel : ℓ x = ℓ v) : x = v := by
  classical
  obtain ⟨s, hs, μ, hμpos, hμsum, hμx⟩ := exists_face_mem_openSimplex K hx
  have hverts : ∀ w ∈ s, w ∈ K.vertices := fun w hw =>
    K.down_closed hs (Finset.singleton_subset_iff.mpr hw) (Finset.singleton_nonempty w)
  have hsum : ∑ w ∈ s, μ w * (ℓ w - ℓ v) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hμsum, one_mul]
    have hm := congrArg ℓ hμx
    simp only [map_sum, map_smul, smul_eq_mul] at hm
    rw [hm, hlevel, sub_self]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun w hw => mul_nonneg (hμpos w hw).le (sub_nonneg.mpr (hmin w (hverts w hw))))).mp hsum
  have heq : ∀ w ∈ s, w = v := by
    intro w hw
    apply hinj (hverts w hw) hv
    exact sub_eq_zero.mp ((mul_eq_zero.mp (hzero w hw)).resolve_left (hμpos w hw).ne')
  calc
    x = ∑ w ∈ s, μ w • w := hμx.symm
    _ = ∑ w ∈ s, μ w • v := Finset.sum_congr rfl fun w hw => by rw [heq w hw]
    _ = v := by rw [← Finset.sum_smul, hμsum, one_smul]

theorem height_fiber_eq_singleton_of_minimum_vertex (K : Geometry.SimplicialComplex ℝ E)
    (ℓ : E →ₗ[ℝ] ℝ) (hinj : InjOn ℓ K.vertices) {v : E} (hv : v ∈ K.vertices)
    (hmin : ∀ w ∈ K.vertices, ℓ v ≤ ℓ w) : K.space ∩ {x | ℓ x = ℓ v} = {v} := by
  apply Subset.antisymm
  · intro x hx
    exact eq_of_mem_height_fiber_of_minimum_vertex K ℓ hinj hv hmin hx.1 hx.2
  · rintro x rfl
    exact ⟨K.subset_space hv (Finset.mem_singleton_self _), rfl⟩

theorem height_fiber_eq_singleton_of_maximum_vertex (K : Geometry.SimplicialComplex ℝ E)
    (ℓ : E →ₗ[ℝ] ℝ) (hinj : InjOn ℓ K.vertices) {v : E} (hv : v ∈ K.vertices)
    (hmax : ∀ w ∈ K.vertices, ℓ w ≤ ℓ v) : K.space ∩ {x | ℓ x = ℓ v} = {v} := by
  have hinj' : InjOn (-ℓ) K.vertices := fun _ hx _ hy h =>
    hinj hx hy (neg_injective h)
  simpa only [LinearMap.neg_apply, neg_inj] using
    height_fiber_eq_singleton_of_minimum_vertex K (-ℓ) hinj' hv
      (fun w hw => neg_le_neg (hmax w hw))

theorem exists_extreme_height_fibers (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : K.space.Nonempty) (ℓ : E →ₗ[ℝ] ℝ) (hinj : InjOn ℓ K.vertices) :
    ∃ v ∈ K.vertices, ∃ w ∈ K.vertices,
      (∀ x ∈ K.space, ℓ v ≤ ℓ x ∧ ℓ x ≤ ℓ w) ∧
      K.space ∩ {x | ℓ x = ℓ v} = {v} ∧ K.space ∩ {x | ℓ x = ℓ w} = {w} := by
  classical
  have hV : K.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite K.faces)
  have hVne : hV.toFinset.Nonempty := by
    obtain ⟨x, hx⟩ := hK
    obtain ⟨s, hs, _⟩ := K.mem_space_iff.mp hx
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs
    exact ⟨v, hV.mem_toFinset.mpr (K.down_closed hs
      (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v))⟩
  obtain ⟨v, hv, hmin⟩ := hV.toFinset.exists_min_image ℓ hVne
  obtain ⟨w, hw, hmax⟩ := hV.toFinset.exists_max_image ℓ hVne
  have hv' := hV.mem_toFinset.mp hv
  have hw' := hV.mem_toFinset.mp hw
  have hmin' : ∀ z ∈ K.vertices, ℓ v ≤ ℓ z := fun z hz => hmin z (hV.mem_toFinset.mpr hz)
  have hmax' : ∀ z ∈ K.vertices, ℓ z ≤ ℓ w := fun z hz => hmax z (hV.mem_toFinset.mpr hz)
  refine ⟨v, hv', w, hw', ?_, height_fiber_eq_singleton_of_minimum_vertex K ℓ hinj hv' hmin',
    height_fiber_eq_singleton_of_maximum_vertex K ℓ hinj hw' hmax'⟩
  intro x hx
  obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
  have hverts : ∀ z ∈ s, z ∈ K.vertices := fun z hz =>
    K.down_closed hs (Finset.singleton_subset_iff.mpr hz) (Finset.singleton_nonempty z)
  exact ⟨convexHull_min (fun z hz => hmin' z (hverts z hz))
      ((convex_Ici (ℓ v)).linear_preimage ℓ) hxs,
    convexHull_min (fun z hz => hmax' z (hverts z hz))
      ((convex_Iic (ℓ w)).linear_preimage ℓ) hxs⟩

end DifferentialGeometry.Topology.PiecewiseLinear
