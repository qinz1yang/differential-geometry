import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.StarComplex
import DifferentialGeometry.Topology.PiecewiseLinear.OpenStar
import DifferentialGeometry.Topology.PiecewiseLinear.Combinatorial
import Mathlib.Topology.SeparatedMap

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open Classical in
theorem affineIndependent_of_injOn_simplicialMap [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (φ : E → F)
    (hinj : InjOn (simplicialMap K φ) K.space) {s : Finset E} (hs : s ∈ K.faces) :
    AffineIndependent ℝ (fun v : s => φ (v : E)) := by
  rw [affineIndependent_image_iff]
  refine ⟨injOn_of_injOn_simplicialMap K φ hinj hs, ?_⟩
  obtain ⟨A, hA⟩ := exists_affineMap_eqOn_simplicialMap K φ hs
  have himage : s.image φ = s.image A := Finset.image_congr fun v hv => by
    rw [← hA (subset_convexHull ℝ _ hv)]
    exact (simplicialMap_vertex K φ
      (K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v))).symm
  rw [himage]
  apply affineIndependent_image_of_injOn_convexHull A (K.indep hs)
  intro x hx y hy hxy
  apply hinj (K.convexHull_subset_space hs hx) (K.convexHull_subset_space hs hy)
  rw [hA hx, hA hy]
  exact hxy

open Classical in
theorem simplicialImage_vertices (K : Geometry.SimplicialComplex ℝ E) (φ : E → F)
    (hind : ∀ s ∈ K.faces, AffineIndependent ℝ ((↑) : ↥(s.image φ : Set F) → F))
    (hinj : InjOn (simplicialMap K φ) K.space) :
    (simplicialImage K φ hind hinj).vertices = φ '' K.vertices := by
  ext w
  constructor
  · rintro ⟨s, hs, heq⟩
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs
    have hvw : φ v = w := Finset.mem_singleton.mp (heq ▸ Finset.mem_image_of_mem φ hv)
    exact ⟨v, K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v), hvw⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨{v}, hv, (Finset.image_singleton φ v).symm⟩

open Classical in
theorem simplicialMap_simplicialImage [FiniteDimensional ℝ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (K : Geometry.SimplicialComplex ℝ E) (φ : E → F)
    (hind : ∀ s ∈ K.faces, AffineIndependent ℝ ((↑) : ↥(s.image φ : Set F) → F))
    (hinj : InjOn (simplicialMap K φ) K.space) (ψ : F → G) {x : E} (hx : x ∈ K.space) :
    simplicialMap (simplicialImage K φ hind hinj) ψ (simplicialMap K φ x) =
      simplicialMap K (ψ ∘ φ) x := by
  let L := simplicialImage K φ hind hinj
  obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
  have hsL : s.image φ ∈ L.faces := ⟨s, hs, rfl⟩
  obtain ⟨A, hA⟩ := exists_affineMap_eqOn_simplicialMap L ψ hsL
  rw [hA (simplicialMap_mem_convexHull_image K φ hs hxs),
    simplicialMap_eq_of_mem K φ hs hxs, affineMap_apply_sum_smul_comp A φ (sum_weights hxs),
    simplicialMap_eq_of_mem K (ψ ∘ φ) hs hxs]
  apply Finset.sum_congr rfl
  intro v hv
  have hvL := L.down_closed hsL (Finset.singleton_subset_iff.mpr (Finset.mem_image_of_mem φ hv))
    (Finset.singleton_nonempty (φ v))
  rw [← hA (subset_convexHull ℝ _ (Finset.mem_image_of_mem φ hv)), simplicialMap_vertex L ψ hvL]
  rfl

open Classical in
theorem exists_injOn_simplicialMap_of_small_vertex_perturbation
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (φ₀ : E → F)
    (hinj : InjOn (simplicialMap K φ₀) K.space) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ φ : E → F, (∀ v ∈ K.vertices, dist (φ v) (φ₀ v) < δ) →
      InjOn (simplicialMap K φ) K.space := by
  have hind : ∀ s ∈ K.faces, AffineIndependent ℝ ((↑) : ↥(s.image φ₀ : Set F) → F) :=
    fun s hs => ((affineIndependent_image_iff s φ₀).mp
      (affineIndependent_of_injOn_simplicialMap K φ₀ hinj hs)).2
  let L := simplicialImage K φ₀ hind hinj
  have : Finite L.faces := (simplicialImage_faces_finite K φ₀ hind hinj).to_subtype
  have hvinj : InjOn φ₀ K.vertices := by
    intro v hv w hw hvw
    apply hinj (K.convexHull_subset_space hv (by simp)) (K.convexHull_subset_space hw (by simp))
    rw [simplicialMap_vertex K φ₀ hv, simplicialMap_vertex K φ₀ hw, hvw]
  obtain ⟨δ, hδ, hext⟩ := exists_isPLHomeomorphOn_extension_of_small_vertex_perturbation
    L isOpen_univ (subset_univ _) zero_lt_one
  refine ⟨δ, hδ, fun φ hφ => ?_⟩
  let ψ : F → F := φ ∘ Function.invFunOn φ₀ K.vertices
  have hψ : ∀ w ∈ L.vertices, dist (ψ w) w < δ := by
    intro w hw
    rw [simplicialImage_vertices] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    change dist (φ (Function.invFunOn φ₀ K.vertices (φ₀ v))) (φ₀ v) < δ
    rw [hvinj.leftInvOn_invFunOn hv]
    exact hφ v hv
  obtain ⟨h, hh, _, _, hagree⟩ := hext ψ hψ
  have heq : EqOn (simplicialMap K (ψ ∘ φ₀)) (simplicialMap K φ) K.space :=
    simplicialMap_eqOn_of_eqOn_vertices K fun v hv => by
      change φ (Function.invFunOn φ₀ K.vertices (φ₀ v)) = φ v
      rw [hvinj.leftInvOn_invFunOn hv]
  have hcomp : ∀ x ∈ K.space, h (simplicialMap K φ₀ x) = simplicialMap K φ x := by
    intro x hx
    have hxL : simplicialMap K φ₀ x ∈ L.space := by
      rw [simplicialImage_space]
      exact mem_image_of_mem _ hx
    rw [hagree hxL, simplicialMap_simplicialImage K φ₀ hind hinj ψ hx, heq hx]
  intro x hx y hy hxy
  apply hinj hx hy
  apply hh.bijOn.injOn (mem_univ _) (mem_univ _)
  rw [hcomp x hx, hcomp y hy]
  exact hxy

open Classical in
omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem exists_isSubdivision_injOn_starComplex [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (f : E → F)
    (hf : IsLocallyInjective (K.space.domRestrict f)) :
    ∃ R : Geometry.SimplicialComplex ℝ E, IsSubdivision R K ∧ R.faces.Finite ∧
      ∀ v ∈ R.vertices, InjOn f (starComplex R v).space := by
  have : CompactSpace K.space := isCompact_iff_compactSpace.mp (isPolyhedron_space K).isCompact
  choose W hW hxW hWinj using hf
  have hcover : (univ : Set K.space) ⊆ ⋃ x : K.space, W x := by
    intro x _
    exact mem_iUnion.mpr ⟨x, hxW x⟩
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric isCompact_univ hW hcover
  obtain ⟨R, hR, hfinite, _, hdiam⟩ := exists_isSubdivision_diam_lt K
    (fun s hs => card_le_finrank_succ_of_mem_faces K hs) hδ
  refine ⟨R, hR, hfinite, fun v hv => ?_⟩
  have hvK : v ∈ K.space := hR.space_eq ▸ R.convexHull_subset_space hv (by simp)
  obtain ⟨z, hz⟩ := hleb ⟨v, hvK⟩ (mem_univ _)
  have hsub : ∀ x ∈ (starComplex R v).space, ∃ hx : x ∈ K.space, (⟨x, hx⟩ : K.space) ∈ W z := by
    intro x hx
    rw [starComplex_space R v hv] at hx
    have hxK : x ∈ K.space := hR.space_eq ▸ closedStar_subset_space R v hx
    refine ⟨hxK, hz ?_⟩
    obtain ⟨s, ⟨hs, hvs⟩, hxs⟩ := mem_iUnion₂.mp hx
    change dist x v < δ
    exact (dist_le_diam_of_mem (s.finite_toSet.isCompact_convexHull ℝ).isBounded hxs hvs).trans_lt
      (hdiam s hs)
  intro x hx y hy hxy
  obtain ⟨hxK, hxW⟩ := hsub x hx
  obtain ⟨hyK, hyW⟩ := hsub y hy
  exact congrArg Subtype.val (hWinj z hxW hyW hxy)

open Classical in
omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem isLocallyInjective_of_injOn_starComplex (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (f : E → F) (hf : ∀ v ∈ K.vertices, InjOn f (starComplex K v).space) :
    IsLocallyInjective (K.space.domRestrict f) := by
  intro x
  obtain ⟨v, hv, hxv⟩ := exists_vertex_mem_openStar K x.property
  refine ⟨Subtype.val ⁻¹' openStar K v, isOpen_preimage_openStar K v, hxv, ?_⟩
  intro y hy z hz hyz
  apply Subtype.ext
  apply hf v hv
  · rw [starComplex_space K v hv]
    exact openStar_subset_closedStar K hv hy
  · rw [starComplex_space K v hv]
    exact openStar_subset_closedStar K hv hz
  · exact hyz

open Classical in
theorem exists_injOn_starComplex_of_small_vertex_perturbation
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (φ₀ : E → F)
    (hinj : ∀ v ∈ K.vertices, InjOn (simplicialMap K φ₀) (starComplex K v).space) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ φ : E → F, (∀ v ∈ K.vertices, dist (φ v) (φ₀ v) < δ) →
      ∀ v ∈ K.vertices, InjOn (simplicialMap K φ) (starComplex K v).space := by
  have hvertices : K.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite K.faces)
  have hlocal : ∀ v : K.vertices, ∃ δ : ℝ, 0 < δ ∧ ∀ φ : E → F,
      (∀ w ∈ K.vertices, dist (φ w) (φ₀ w) < δ) →
        InjOn (simplicialMap K φ) (starComplex K v).space := by
    intro v
    let S := starComplex K v
    have : Finite S.faces := (starComplex_faces_finite K v).to_subtype
    have heq₀ := simplicialMap_eqOn_of_faces_subset K S (starComplex_faces_subset K v) φ₀
    have hinjS : InjOn (simplicialMap S φ₀) S.space := by
      intro x hx y hy hxy
      apply hinj v v.property hx hy
      rw [heq₀ hx, heq₀ hy]
      exact hxy
    obtain ⟨δ, hδ, hδinj⟩ := exists_injOn_simplicialMap_of_small_vertex_perturbation S φ₀ hinjS
    refine ⟨δ, hδ, fun φ hφ => ?_⟩
    have heq := simplicialMap_eqOn_of_faces_subset K S (starComplex_faces_subset K v) φ
    intro x hx y hy hxy
    apply hδinj φ (fun w hw => hφ w hw.1) hx hy
    rw [← heq hx, ← heq hy]
    exact hxy
  choose δ hδ hδinj using hlocal
  have hmin : ∀ t : Finset K.vertices, ∃ ε : ℝ, 0 < ε ∧ ∀ v ∈ t, ε ≤ δ v := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, fun _ hv => False.elim (Finset.notMem_empty _ hv)⟩
    | @insert v t hv ih =>
      obtain ⟨ε, hε, hbound⟩ := ih
      refine ⟨min (δ v) ε, lt_min (hδ v) hε, ?_⟩
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hbound w hw)
  have : Fintype K.vertices := hvertices.fintype
  obtain ⟨ε, hε, hbound⟩ := hmin Finset.univ
  refine ⟨ε, hε, fun φ hφ v hv => hδinj ⟨v, hv⟩ φ ?_⟩
  intro w hw
  exact (hφ w hw).trans_le (hbound ⟨v, hv⟩ (Finset.mem_univ _))

open Classical in
theorem exists_isSubdivision_stable_locallyInjective [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (f : E → F)
    (hf : IsPiecewiseAffineOn f K.space) (hloc : IsLocallyInjective (K.space.domRestrict f)) :
    ∃ (R : Geometry.SimplicialComplex ℝ E) (δ : ℝ), IsSubdivision R K ∧ R.faces.Finite ∧
      EqOn (simplicialMap R f) f K.space ∧ 0 < δ ∧
        ∀ φ : E → F, (∀ v ∈ R.vertices, dist (φ v) (f v) < δ) →
          (∀ v ∈ R.vertices, InjOn (simplicialMap R φ) (starComplex R v).space) ∧
            IsLocallyInjective (R.space.domRestrict (simplicialMap R φ)) := by
  obtain ⟨K₀, hK₀, hfinite₀, haff⟩ := hf.exists_isSubdivision_affineOn_faces K
  have : Finite K₀.faces := hfinite₀.to_subtype
  have hloc₀ : IsLocallyInjective (K₀.space.domRestrict f) := by rwa [hK₀.space_eq]
  obtain ⟨R, hR₀, hfinite, hstar⟩ := exists_isSubdivision_injOn_starComplex K₀ f hloc₀
  have : Finite R.faces := hfinite.to_subtype
  have hR : IsSubdivision R K := hR₀.trans hK₀
  have heq : EqOn (simplicialMap R f) f R.space := by
    apply simplicialMap_eq_of_forall_affineOn
    intro s hs
    obtain ⟨t, ht, hst⟩ := hR₀.exists_face_subset hs
    obtain ⟨A, hA⟩ := haff t ht
    exact ⟨A, hA.mono hst⟩
  have hstar' : ∀ v ∈ R.vertices, InjOn (simplicialMap R f) (starComplex R v).space := by
    intro v hv x hx y hy hxy
    apply hstar v hv hx hy
    have hsub := space_mono_of_faces_subset (starComplex_faces_subset R v)
    rw [← heq (hsub hx), ← heq (hsub hy)]
    exact hxy
  obtain ⟨δ, hδ, hinj⟩ := exists_injOn_starComplex_of_small_vertex_perturbation R f hstar'
  refine ⟨R, δ, hR, hfinite, ?_, hδ, fun φ hφ => ?_⟩
  · rwa [hR.space_eq] at heq
  · exact ⟨hinj φ hφ, isLocallyInjective_of_injOn_starComplex R _ (hinj φ hφ)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
