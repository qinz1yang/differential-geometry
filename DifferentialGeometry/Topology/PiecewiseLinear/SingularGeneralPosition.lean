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

open Classical in
omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem exists_pos_eq_of_dist_lt_of_injOn_starComplex
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    ∃ η : ℝ, 0 < η ∧ ∀ g : E → F, (∀ v ∈ K.vertices, InjOn g (starComplex K v).space) →
      ∀ x ∈ K.space, ∀ y ∈ K.space, dist x y < η → g x = g y → x = y := by
  have : CompactSpace K.space := isCompact_iff_compactSpace.mp (isPolyhedron_space K).isCompact
  let W : K.vertices → Set K.space := fun v => Subtype.val ⁻¹' openStar K v
  have hW : ∀ v, IsOpen (W v) := fun v => isOpen_preimage_openStar K v
  have hcover : (univ : Set K.space) ⊆ ⋃ v, W v := by
    intro x _
    obtain ⟨v, hv, hxv⟩ := exists_vertex_mem_openStar K x.property
    exact mem_iUnion.mpr ⟨⟨v, hv⟩, hxv⟩
  obtain ⟨η, hη, hleb⟩ := lebesgue_number_lemma_of_metric isCompact_univ hW hcover
  refine ⟨η, hη, fun g hg x hx y hy hdist hxy => ?_⟩
  obtain ⟨v, hv⟩ := hleb ⟨x, hx⟩ (mem_univ _)
  have hxv : x ∈ openStar K v := hv (mem_ball_self hη)
  have hyball : (⟨y, hy⟩ : K.space) ∈ ball ⟨x, hx⟩ η := by
    change dist y x < η
    rwa [dist_comm]
  have hyv : y ∈ openStar K v := hv hyball
  apply hg v v.property
  · rw [starComplex_space K v v.property]
    exact openStar_subset_closedStar K v.property hxv
  · rw [starComplex_space K v v.property]
    exact openStar_subset_closedStar K v.property hyv
  · exact hxy

open Classical in
omit [NormedSpace ℝ F] in
theorem exists_fiber_encard_le_two_of_close_of_injOn_starComplex
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (f : E → F)
    (hf : ContinuousOn f K.space) (hcard : ∀ y : F, (K.space ∩ f ⁻¹' {y}).encard ≤ 2) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g : E → F, (∀ x ∈ K.space, dist (g x) (f x) < ε) →
      (∀ v ∈ K.vertices, InjOn g (starComplex K v).space) →
        ∀ y : F, (K.space ∩ g ⁻¹' {y}).encard ≤ 2 := by
  have : CompactSpace K.space := isCompact_iff_compactSpace.mp (isPolyhedron_space K).isCompact
  obtain ⟨η, hη, hηinj⟩ := exists_pos_eq_of_dist_lt_of_injOn_starComplex (F := F) K
  let C : Set (K.space × K.space × K.space) := {p |
    η ≤ dist p.1 p.2.1 ∧ η ≤ dist p.1 p.2.2 ∧ η ≤ dist p.2.1 p.2.2}
  have hC : IsClosed C :=
    (isClosed_le continuous_const (continuous_fst.dist (continuous_fst.comp continuous_snd))).inter
      ((isClosed_le continuous_const (continuous_fst.dist (continuous_snd.comp continuous_snd))).inter
        (isClosed_le continuous_const
          ((continuous_fst.comp continuous_snd).dist (continuous_snd.comp continuous_snd))))
  let f₀ : K.space → F := K.space.domRestrict f
  have hf₀ : Continuous f₀ := hf.comp_continuous continuous_subtype_val (fun x => x.property)
  let r : K.space × K.space × K.space → ℝ := fun p =>
    dist (f₀ p.1) (f₀ p.2.1) + dist (f₀ p.1) (f₀ p.2.2)
  have hr : Continuous r :=
    ((hf₀.comp continuous_fst).dist (hf₀.comp (continuous_fst.comp continuous_snd))).add
      ((hf₀.comp continuous_fst).dist (hf₀.comp (continuous_snd.comp continuous_snd)))
  have hrpos : ∀ p ∈ C, 0 < r p := by
    rintro ⟨x, y, z⟩ hp
    have hxy : (x : E) ≠ y := by
      intro heq
      have h := hp.1
      change η ≤ dist (x : E) y at h
      rw [heq, dist_self] at h
      exact (not_le_of_gt hη) h
    have hxz : (x : E) ≠ z := by
      intro heq
      have h := hp.2.1
      change η ≤ dist (x : E) z at h
      rw [heq, dist_self] at h
      exact (not_le_of_gt hη) h
    have hyz : (y : E) ≠ z := by
      intro heq
      have h := hp.2.2
      change η ≤ dist (y : E) z at h
      rw [heq, dist_self] at h
      exact (not_le_of_gt hη) h
    by_contra hpos
    have hle : dist (f x) (f y) + dist (f x) (f z) ≤ 0 := le_of_not_gt hpos
    have hxy0 : 0 ≤ dist (f x) (f y) := dist_nonneg
    have hxz0 : 0 ≤ dist (f x) (f z) := dist_nonneg
    have hxyf : f x = f y := dist_eq_zero.mp (by linarith)
    have hxzf : f x = f z := dist_eq_zero.mp (by linarith)
    have hsub : ({(x : E), (y : E), (z : E)} : Set E) ⊆ K.space ∩ f ⁻¹' {f x} := by
      intro w hw
      rcases hw with rfl | rfl | rfl
      · exact ⟨x.property, rfl⟩
      · exact ⟨y.property, hxyf.symm⟩
      · exact ⟨z.property, hxzf.symm⟩
    have hbound := (encard_mono hsub).trans (hcard (f x))
    rw [encard_insert_of_notMem (by simp [hxy, hxz]), encard_pair hyz] at hbound
    norm_num at hbound
  obtain ⟨m, hm, hmin⟩ : ∃ m : ℝ, 0 < m ∧ ∀ p ∈ C, m ≤ r p := by
    by_cases hne : C.Nonempty
    · obtain ⟨p, hp, hmin⟩ := hC.isCompact.exists_isMinOn hne hr.continuousOn
      exact ⟨r p, hrpos p hp, fun q hq => hmin hq⟩
    · exact ⟨1, zero_lt_one, fun p hp => False.elim (hne ⟨p, hp⟩)⟩
  refine ⟨m / 4, by positivity, fun g hclose hstar y => ?_⟩
  let A := K.space ∩ g ⁻¹' {y}
  by_cases hsub : A.Subsingleton
  · exact (encard_le_one_iff_subsingleton.mpr hsub).trans (by norm_num)
  obtain ⟨x, hx, z, hz, hxz⟩ := Set.not_subsingleton_iff.mp hsub
  have hsubset : A ⊆ {x, z} := by
    intro w hw
    by_cases hwx : w = x
    · exact Or.inl hwx
    by_cases hwz : w = z
    · exact Or.inr hwz
    have hgxz : g x = g z := hx.2.trans hz.2.symm
    have hgxw : g x = g w := hx.2.trans hw.2.symm
    have hp : (⟨x, hx.1⟩, ⟨z, hz.1⟩, ⟨w, hw.1⟩) ∈ C := by
      refine ⟨le_of_not_gt ?_, le_of_not_gt ?_, le_of_not_gt ?_⟩
      · intro hdist
        exact hxz (hηinj g hstar x hx.1 z hz.1 hdist hgxz)
      · intro hdist
        exact hwx (hηinj g hstar x hx.1 w hw.1 hdist hgxw).symm
      · intro hdist
        exact hwz (hηinj g hstar z hz.1 w hw.1 hdist (hz.2.trans hw.2.symm)).symm
    have hdist : ∀ a ∈ K.space, ∀ b ∈ K.space, g a = g b → dist (f a) (f b) < m / 2 := by
      intro a ha b hb hab
      have htriangle := dist_triangle (f a) (g a) (f b)
      rw [dist_comm (f a) (g a), hab] at htriangle
      have ha' := hclose a ha
      have hb' := hclose b hb
      rw [hab] at ha'
      linarith
    have hbound := hmin _ hp
    change m ≤ dist (f x) (f z) + dist (f x) (f w) at hbound
    have h1 := hdist x hx.1 z hz.1 hgxz
    have h2 := hdist x hx.1 w hw.1 hgxw
    linarith
  exact (encard_mono hsubset).trans_eq (encard_pair hxz)

open Classical in
theorem exists_isSubdivision_stable_fiber_encard_le_two
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (f : E → F)
    (hf : IsPiecewiseAffineOn f K.space) (hloc : IsLocallyInjective (K.space.domRestrict f))
    (hcard : ∀ y : F, (K.space ∩ f ⁻¹' {y}).encard ≤ 2) :
    ∃ (R : Geometry.SimplicialComplex ℝ E) (δ : ℝ), IsSubdivision R K ∧ R.faces.Finite ∧
      EqOn (simplicialMap R f) f K.space ∧ 0 < δ ∧
        ∀ φ : E → F, (∀ v ∈ R.vertices, dist (φ v) (f v) < δ) →
          (∀ v ∈ R.vertices, IsPLHomeomorphOn (simplicialMap R φ) (starComplex R v).space
            (simplicialMap R φ '' (starComplex R v).space)) ∧
              IsLocallyInjective (R.space.domRestrict (simplicialMap R φ)) ∧
                ∀ y : F, (R.space ∩ (simplicialMap R φ) ⁻¹' {y}).encard ≤ 2 := by
  obtain ⟨R, η, hR, hfinite, heq, hη, hinj⟩ := exists_isSubdivision_stable_locallyInjective K f hf hloc
  have : Finite R.faces := hfinite.to_subtype
  have hfR : ContinuousOn f R.space := by simpa only [hR.space_eq] using hf.continuousOn
  have hcardR : ∀ y : F, (R.space ∩ f ⁻¹' {y}).encard ≤ 2 := by rwa [hR.space_eq]
  obtain ⟨ε, hε, hbound⟩ := exists_fiber_encard_le_two_of_close_of_injOn_starComplex R f hfR hcardR
  refine ⟨R, min η ε, hR, hfinite, heq, lt_min hη hε, fun φ hφ => ?_⟩
  obtain ⟨hstar, hlocal⟩ := hinj φ (fun v hv => (hφ v hv).trans_le (min_le_left η ε))
  refine ⟨?_, hlocal, hbound (simplicialMap R φ) ?_ hstar⟩
  · intro v hv
    have : Finite (starComplex R v).faces := (starComplex_faces_finite R v).to_subtype
    have hpl : IsPiecewiseAffineOn (simplicialMap R φ) (starComplex R v).space :=
      (isPiecewiseAffineOn_simplicialMap R φ).mono_of_isPolyhedron (isPolyhedron_space _)
        (space_mono_of_faces_subset (starComplex_faces_subset R v))
    obtain ⟨L, _, hspace, hPL⟩ := exists_isPLHomeomorphOn_image (starComplex R v) hpl (hstar v hv)
    rwa [hspace] at hPL
  · intro x hx
    rw [← heq (hR.space_eq ▸ hx)]
    exact dist_simplicialMap_lt_of_dist_vertices_lt R
      (fun v hv => (hφ v hv).trans_le (min_le_right η ε)) hx

open Classical in
theorem exists_small_affineIndependent_subsets_relative [FiniteDimensional ℝ F] {ι : Type*}
    (V B : Finset ι) (hVB : Disjoint V B) (φ₀ : ι → F) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : ι → F, EqOn φ φ₀ (V : Set ι)ᶜ ∧ EqOn φ φ₀ (B : Set ι) ∧
      (∀ v, dist (φ v) (φ₀ v) < ε) ∧
      ∀ s : Finset ι, s ⊆ V ∪ B → s.card ≤ Module.finrank ℝ F + 1 →
        AffineIndependent ℝ (fun v : (s ∩ B : Finset ι) => φ₀ (v : ι)) →
          AffineIndependent ℝ (fun v : s => φ (v : ι)) := by
  induction V using Finset.induction_on with
  | empty =>
    refine ⟨φ₀, fun _ _ => rfl, fun _ _ => rfl, fun _ => by simpa only [dist_self] using hε, ?_⟩
    intro s hs _ hind
    have hsB : s ⊆ B := by simpa only [Finset.empty_union] using hs
    let e : s ↪ (s ∩ B : Finset ι) :=
      ⟨fun w => ⟨w, Finset.mem_inter.mpr ⟨w.property, hsB w.property⟩⟩,
        fun _ _ h => Subtype.ext (congrArg (fun z : (s ∩ B : Finset ι) => (z : ι)) h)⟩
    exact hind.comp_embedding e
  | @insert v V hv ih =>
    have hvB : v ∉ B := fun hvB => Finset.disjoint_left.mp hVB (Finset.mem_insert_self v V) hvB
    have hVB' : Disjoint V B := hVB.mono_left (Finset.subset_insert v V)
    obtain ⟨φ, hfix, hfixB, hclose, hgood⟩ := ih hVB'
    let I := {s : Finset ι // s ⊆ V ∪ B ∧ s.card ≤ Module.finrank ℝ F ∧
      AffineIndependent ℝ (fun w : (s ∩ B : Finset ι) => φ₀ (w : ι))}
    have : Finite I := (((V ∪ B).powerset.finite_toSet).subset
      (fun s hs => Finset.mem_powerset.mpr hs.1)).to_subtype
    let A : I → AffineSubspace ℝ F := fun s => affineSpan ℝ (s.val.image φ : Set F)
    have hA : ∀ s, A s ≠ ⊤ := by
      intro s htop
      have hs := ((affineIndependent_image_iff s.val φ).mp
        (hgood s.val s.property.1 (Nat.le_succ_of_le s.property.2.1) s.property.2.2)).2
      have hrange : range ((↑) : ↥(s.val.image φ : Set F) → F) = (s.val.image φ : Set F) := by
        ext y
        simp
      have htop' : affineSpan ℝ (range ((↑) : ↥(s.val.image φ : Set F) → F)) = ⊤ := by
        rwa [hrange]
      have hc := hs.affineSpan_eq_top_iff_card_eq_finrank_add_one.mp htop'
      rw [Fintype.card_coe] at hc
      have hle := (Finset.card_image_le (s := s.val) (f := φ)).trans s.property.2.1
      omega
    obtain ⟨p, hp, hpA⟩ := exists_mem_ball_notMem_affineSubspaces A hA (x := φ₀ v) hε
    let ψ := Function.update φ v p
    have hsame : ∀ w ≠ v, ψ w = φ w := fun w hw => Function.update_of_ne hw p φ
    have hψv : ψ v = p := Function.update_self v p φ
    refine ⟨ψ, ?_, ?_, ?_, ?_⟩
    · intro w hw
      have hwv : w ≠ v := fun heq => hw (heq ▸ Finset.mem_insert_self v V)
      exact (hsame w hwv).trans (hfix (fun hwV => hw (Finset.mem_insert_of_mem hwV)))
    · intro w hw
      exact (hsame w (ne_of_mem_of_not_mem hw hvB)).trans (hfixB hw)
    · intro w
      by_cases hwv : w = v
      · rw [hwv, hψv]
        exact hp
      · rw [hsame w hwv]
        exact hclose w
    · intro s hs hcard hfixed
      by_cases hvs : v ∈ s
      · have hsub : s.erase v ⊆ V ∪ B := by
          intro w hw
          rcases Finset.mem_union.mp (hs (Finset.mem_of_mem_erase hw)) with hwV | hwB
          · exact Finset.mem_union_left B ((Finset.mem_insert.mp hwV).resolve_left (Finset.ne_of_mem_erase hw))
          · exact Finset.mem_union_right V hwB
        have herase : (s.erase v).card ≤ Module.finrank ℝ F := by
          have h := Finset.card_erase_of_mem hvs
          omega
        have hfixed' : AffineIndependent ℝ (fun w : (s.erase v ∩ B : Finset ι) => φ₀ (w : ι)) := by
          let e : (s.erase v ∩ B : Finset ι) ↪ (s ∩ B : Finset ι) :=
            ⟨fun w => ⟨w, Finset.mem_inter.mpr
              ⟨Finset.mem_of_mem_erase (Finset.mem_inter.mp w.property).1, (Finset.mem_inter.mp w.property).2⟩⟩,
              fun _ _ h => Subtype.ext (congrArg (fun z : (s ∩ B : Finset ι) => (z : ι)) h)⟩
          exact hfixed.comp_embedding e
        have h := affineIndependent_update_insert (φ := φ) (Finset.notMem_erase v s)
          (hgood (s.erase v) hsub (Nat.le_succ_of_le herase) hfixed')
          (hpA ⟨s.erase v, hsub, herase, hfixed'⟩)
        rwa [Finset.insert_erase hvs] at h
      · have hsub : s ⊆ V ∪ B := by
          intro w hw
          rcases Finset.mem_union.mp (hs hw) with hwV | hwB
          · exact Finset.mem_union_left B ((Finset.mem_insert.mp hwV).resolve_left (ne_of_mem_of_not_mem hw hvs))
          · exact Finset.mem_union_right V hwB
        have heq : (fun w : s => ψ (w : ι)) = (fun w : s => φ (w : ι)) :=
          funext fun w => hsame w (ne_of_mem_of_not_mem w.property hvs)
        rw [heq]
        exact hgood s hsub hcard hfixed

open Classical in
theorem exists_small_affineIndependent_subsets [FiniteDimensional ℝ F] {ι : Type*}
    (V : Finset ι) (φ₀ : ι → F) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : ι → F, EqOn φ φ₀ (V : Set ι)ᶜ ∧ (∀ v, dist (φ v) (φ₀ v) < ε) ∧
      ∀ s : Finset ι, s ⊆ V → s.card ≤ Module.finrank ℝ F + 1 →
        AffineIndependent ℝ (fun v : s => φ (v : ι)) := by
  obtain ⟨φ, hfix, _, hclose, hgood⟩ :=
    exists_small_affineIndependent_subsets_relative V ∅ (Finset.disjoint_empty_right V) φ₀ hε
  refine ⟨φ, hfix, hclose, ?_⟩
  intro s hs hcard
  apply hgood s (by simpa only [Finset.union_empty] using hs) hcard
  have : IsEmpty (s ∩ ∅ : Finset ι) :=
    ⟨fun v => Finset.notMem_empty (v : ι) (Finset.mem_inter.mp v.property).2⟩
  exact affineIndependent_of_subsingleton ℝ _

open Classical in
theorem vectorSpan_sup_eq_top_of_affineIndependent_subsets_relative [FiniteDimensional ℝ F] {ι : Type*}
    (V B : Finset ι) (φ : ι → F)
    (hφ : ∀ u : Finset ι, u ⊆ V → u.card ≤ Module.finrank ℝ F + 1 →
      (u ∩ B).card ≤ Module.finrank ℝ F → AffineIndependent ℝ (fun v : u => φ (v : ι)))
    {s t : Finset ι} (hs : s ⊆ V) (ht : t ⊆ V) (hst : Disjoint s t) (hnotB : ¬s ∪ t ⊆ B)
    (hinter : (convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t.image φ : Set F)).Nonempty) :
    vectorSpan ℝ (s.image φ : Set F) ⊔ vectorSpan ℝ (t.image φ : Set F) = ⊤ := by
  have hsub : s ∪ t ⊆ V := Finset.union_subset hs ht
  obtain ⟨v, hv, hvB⟩ := Finset.not_subset.mp hnotB
  have hBbound : ∀ u : Finset ι, v ∈ u → u.card ≤ Module.finrank ℝ F + 1 →
      (u ∩ B).card ≤ Module.finrank ℝ F := by
    intro u hvu hcard
    have hle := Finset.card_le_card (show u ∩ B ⊆ u.erase v from fun w hw =>
      Finset.mem_erase.mpr ⟨ne_of_mem_of_not_mem (Finset.mem_inter.mp hw).2 hvB,
        (Finset.mem_inter.mp hw).1⟩)
    have herase := Finset.card_erase_of_mem hvu
    omega
  by_cases hcard : (s ∪ t).card ≤ Module.finrank ℝ F + 1
  · have hAI := (affineIndependent_image_iff (s ∪ t) φ).mp (hφ _ hsub hcard (hBbound _ hv hcard))
    have hdisj : Disjoint (s.image φ) (t.image φ) := by
      rw [Finset.disjoint_left]
      intro y hys hyt
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hys
      obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hyt
      have heq : b = a := hAI.1 (Finset.mem_union_right s hb) (Finset.mem_union_left t ha) hba
      exact Finset.disjoint_left.mp hst ha (heq ▸ hb)
    obtain ⟨y, hy⟩ := hinter
    have hmem := convexHull_inter_subset_of_affineIndependent hAI.2
      (Finset.image_subset_image Finset.subset_union_left)
      (Finset.image_subset_image Finset.subset_union_right) hy
    rw [← Finset.coe_inter, Finset.disjoint_iff_inter_eq_empty.mp hdisj, Finset.coe_empty,
      convexHull_empty] at hmem
    exact False.elim hmem
  · have herase := Finset.card_erase_of_mem hv
    obtain ⟨u, hu, hucard⟩ := Finset.exists_subset_card_eq
      (show Module.finrank ℝ F ≤ ((s ∪ t).erase v).card by omega)
    have hvu : v ∉ u := fun h => Finset.notMem_erase v (s ∪ t) (hu h)
    have hins : insert v u ⊆ s ∪ t := Finset.insert_subset_iff.mpr
      ⟨hv, hu.trans (Finset.erase_subset v (s ∪ t))⟩
    have hinscard : (insert v u).card = Module.finrank ℝ F + 1 := by
      rw [Finset.card_insert_of_notMem hvu, hucard]
    have huAI := hφ (insert v u) (hins.trans hsub) hinscard.le
      (hBbound _ (Finset.mem_insert_self v u) hinscard.le)
    have huSpan : affineSpan ℝ ((insert v u).image φ : Set F) = ⊤ := by
      have hrange : range (fun w : (insert v u : Finset ι) => φ (w : ι)) =
          ((insert v u).image φ : Set F) := by ext y; simp [eq_comm]
      rw [← hrange, huAI.affineSpan_eq_top_iff_card_eq_finrank_add_one, Fintype.card_coe]
      exact hinscard
    have hspan : affineSpan ℝ ((s.image φ : Set F) ∪ (t.image φ : Set F)) = ⊤ := by
      apply top_unique
      rw [← huSpan]
      apply affineSpan_mono ℝ
      intro y hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
      rcases Finset.mem_union.mp (hins ha) with has | hat
      · exact Or.inl (Finset.mem_image_of_mem φ has)
      · exact Or.inr (Finset.mem_image_of_mem φ hat)
    obtain ⟨y, hys, hyt⟩ := hinter
    have hdir := congrArg AffineSubspace.direction hspan
    rw [AffineSubspace.span_union, AffineSubspace.direction_sup
      (convexHull_subset_affineSpan _ hys) (convexHull_subset_affineSpan _ hyt),
      direction_affineSpan, direction_affineSpan, vsub_self, Submodule.span_singleton_eq_bot.mpr rfl,
      sup_bot_eq, AffineSubspace.direction_top] at hdir
    exact hdir

open Classical in
theorem vectorSpan_sup_eq_top_of_affineIndependent_subsets [FiniteDimensional ℝ F] {ι : Type*}
    (V : Finset ι) (φ : ι → F)
    (hφ : ∀ u : Finset ι, u ⊆ V → u.card ≤ Module.finrank ℝ F + 1 →
      AffineIndependent ℝ (fun v : u => φ (v : ι)))
    {s t : Finset ι} (hs : s ⊆ V) (ht : t ⊆ V) (hst : Disjoint s t)
    (hinter : (convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t.image φ : Set F)).Nonempty) :
    vectorSpan ℝ (s.image φ : Set F) ⊔ vectorSpan ℝ (t.image φ : Set F) = ⊤ := by
  apply vectorSpan_sup_eq_top_of_affineIndependent_subsets_relative V ∅ φ
    (fun u hu hc _ => hφ u hu hc) hs ht hst _ hinter
  intro h
  have hs0 : s = ∅ := Finset.subset_empty.mp (Finset.subset_union_left.trans h)
  obtain ⟨y, hy, _⟩ := hinter
  simp only [hs0, Finset.image_empty, Finset.coe_empty, convexHull_empty, Set.mem_empty_iff_false] at hy

open Classical in
theorem exists_small_simplicialMap_self_transverse_of_fiber_encard_le_two
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hdim : Module.finrank ℝ F = 3)
    (f : E → F) (hf : IsPiecewiseAffineOn f K.space)
    (hloc : IsLocallyInjective (K.space.domRestrict f))
    (hcard : ∀ y : F, (K.space ∩ f ⁻¹' {y}).encard ≤ 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ (R : Geometry.SimplicialComplex ℝ E) (φ : E → F), IsSubdivision R K ∧ R.faces.Finite ∧
      IsPiecewiseAffineOn (simplicialMap R φ) K.space ∧
        (∀ x ∈ K.space, dist (simplicialMap R φ x) (f x) < ε) ∧
          (∀ v ∈ R.vertices, IsPLHomeomorphOn (simplicialMap R φ) (starComplex R v).space
            (simplicialMap R φ '' (starComplex R v).space)) ∧
              IsLocallyInjective (K.space.domRestrict (simplicialMap R φ)) ∧
                (∀ y : F, (K.space ∩ (simplicialMap R φ) ⁻¹' {y}).encard ≤ 2) ∧
                  (∀ s ∈ R.faces, AffineIndependent ℝ (fun v : s => φ (v : E))) ∧
                    ∀ s ∈ R.faces, ∀ t ∈ R.faces, Disjoint s t →
                      (convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t.image φ : Set F)).Nonempty →
                        vectorSpan ℝ (s.image φ : Set F) ⊔ vectorSpan ℝ (t.image φ : Set F) = ⊤ := by
  obtain ⟨R, δ, hR, hfinite, heq, hδ, hstable⟩ :=
    exists_isSubdivision_stable_fiber_encard_le_two K f hf hloc hcard
  have : Finite R.faces := hfinite.to_subtype
  have hRman : IsCombinatorialManifoldWithBoundary 2 R := hK.of_isSubdivision hR
  have hvertices : R.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite R.faces)
  let V := hvertices.toFinset
  have hfaces : ∀ s ∈ R.faces, s ⊆ V := by
    intro s hs v hv
    apply hvertices.mem_toFinset.mpr
    exact R.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  obtain ⟨φ, _, hclose, hgeneral⟩ := exists_small_affineIndependent_subsets V f (lt_min hδ hε)
  obtain ⟨hstar, hlocal, hfiber⟩ := hstable φ (fun v _ => (hclose v).trans_le (min_le_left δ ε))
  refine ⟨R, φ, hR, hfinite, ?_, ?_, hstar, ?_, ?_, ?_, ?_⟩
  · simpa only [hR.space_eq] using isPiecewiseAffineOn_simplicialMap R φ
  · intro x hx
    rw [← heq hx]
    apply dist_simplicialMap_lt_of_dist_vertices_lt R
      (fun v _ => (hclose v).trans_le (min_le_right δ ε))
    rwa [hR.space_eq]
  · rwa [hR.space_eq] at hlocal
  · rwa [hR.space_eq] at hfiber
  · intro s hs
    apply hgeneral s (hfaces s hs)
    have hc := hRman.card_le R hs
    omega
  · intro s hs t ht hdisj hinter
    exact vectorSpan_sup_eq_top_of_affineIndependent_subsets V φ hgeneral
      (hfaces s hs) (hfaces t ht) hdisj hinter

def doublePointSet {X Y : Type*} (f : X → Y) (P : Set X) : Set Y :=
  {y | ∃ x ∈ P, ∃ z ∈ P, x ≠ z ∧ f x = y ∧ f z = y}

open Classical in
omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem disjoint_faces_of_eq_of_injOn_starComplex (K : Geometry.SimplicialComplex ℝ E)
    (f : E → F) (hinj : ∀ v ∈ K.vertices, InjOn f (starComplex K v).space)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) {x y : E}
    (hxs : x ∈ convexHull ℝ (s : Set E)) (hyt : y ∈ convexHull ℝ (t : Set E))
    (hxy : x ≠ y) (hfxy : f x = f y) : Disjoint s t := by
  rw [Finset.disjoint_left]
  intro v hvs hvt
  have hv := K.down_closed hs (Finset.singleton_subset_iff.mpr hvs) (Finset.singleton_nonempty v)
  apply hxy
  apply hinj v hv
  · apply (starComplex K v).convexHull_subset_space _ hxs
    exact ⟨hs, by rwa [Finset.insert_eq_of_mem hvs]⟩
  · apply (starComplex K v).convexHull_subset_space _ hyt
    exact ⟨ht, by rwa [Finset.insert_eq_of_mem hvt]⟩
  · exact hfxy

open Classical in
theorem doublePointSet_simplicialMap_eq_iUnion (K : Geometry.SimplicialComplex ℝ E) (φ : E → F)
    (hind : ∀ s ∈ K.faces, AffineIndependent ℝ (fun v : s => φ (v : E)))
    (hinj : ∀ v ∈ K.vertices, InjOn (simplicialMap K φ) (starComplex K v).space) :
    doublePointSet (simplicialMap K φ) K.space =
      ⋃ p : {p : K.faces × K.faces // Disjoint p.1.val p.2.val},
        convexHull ℝ (p.val.1.val.image φ : Set F) ∩ convexHull ℝ (p.val.2.val.image φ : Set F) := by
  ext y
  constructor
  · rintro ⟨x, hx, z, hz, hxz, hxy, hzy⟩
    obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
    obtain ⟨t, ht, hzt⟩ := K.mem_space_iff.mp hz
    have hdisj := disjoint_faces_of_eq_of_injOn_starComplex K _ hinj hs ht hxs hzt hxz
      (hxy.trans hzy.symm)
    apply mem_iUnion.mpr
    refine ⟨⟨(⟨s, hs⟩, ⟨t, ht⟩), hdisj⟩, ?_, ?_⟩
    · exact hxy ▸ simplicialMap_mem_convexHull_image K φ hs hxs
    · exact hzy ▸ simplicialMap_mem_convexHull_image K φ ht hzt
  · intro hy
    obtain ⟨p, hys, hyt⟩ := mem_iUnion.mp hy
    rw [← image_convexHull_simplicialMap K φ p.val.1.property
      ((affineIndependent_image_iff _ φ).mp (hind _ p.val.1.property)).1] at hys
    rw [← image_convexHull_simplicialMap K φ p.val.2.property
      ((affineIndependent_image_iff _ φ).mp (hind _ p.val.2.property)).1] at hyt
    obtain ⟨x, hxs, hxy⟩ := hys
    obtain ⟨z, hzt, hzy⟩ := hyt
    refine ⟨x, K.convexHull_subset_space p.val.1.property hxs,
      z, K.convexHull_subset_space p.val.2.property hzt, ?_, hxy, hzy⟩
    intro heq
    have hmem := K.inter_subset_convexHull p.val.1.property p.val.2.property ⟨hxs, heq ▸ hzt⟩
    rw [← Finset.coe_inter, Finset.disjoint_iff_inter_eq_empty.mp p.property, Finset.coe_empty,
      convexHull_empty] at hmem
    exact hmem

open Classical in
theorem exists_triangulation_doublePointSet [FiniteDimensional ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (φ : E → F)
    (hind : ∀ s ∈ K.faces, AffineIndependent ℝ (fun v : s => φ (v : E)))
    (hinj : ∀ v ∈ K.vertices, InjOn (simplicialMap K φ) (starComplex K v).space) :
    ∃ G : Geometry.SimplicialComplex ℝ F, G.faces.Finite ∧
      G.space = doublePointSet (simplicialMap K φ) K.space ∧
        ∀ u ∈ G.faces, ∃ s ∈ K.faces, ∃ t ∈ K.faces, Disjoint s t ∧
          convexHull ℝ (u : Set F) ⊆
            convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t.image φ : Set F) := by
  let I := {p : K.faces × K.faces // Disjoint p.1.val p.2.val}
  let C : I → Set F := fun p =>
    convexHull ℝ (p.val.1.val.image φ : Set F) ∩ convexHull ℝ (p.val.2.val.image φ : Set F)
  have hC : ∀ p, IsHPolytope (C p) := by
    intro p
    exact (isHPolytope_convexHull_of_affineIndependent _
      ((affineIndependent_image_iff _ φ).mp (hind _ p.val.1.property)).2).inter
      (isHPolytope_convexHull_of_affineIndependent _
        ((affineIndependent_image_iff _ φ).mp (hind _ p.val.2.property)).2)
  obtain ⟨G, hfinite, hspace, hcover⟩ := exists_simplicialComplex_of_forall_isHPolytope C hC
  refine ⟨G, hfinite, hspace.trans (doublePointSet_simplicialMap_eq_iUnion K φ hind hinj).symm,
    fun u hu => ?_⟩
  have huc : u.centroid ℝ id ∈ openSimplex u := centroid_mem_openSimplex (G.nonempty_of_mem_faces hu)
  have hucG : u.centroid ℝ id ∈ G.space := G.convexHull_subset_space hu (openSimplex_subset_convexHull _ huc)
  obtain ⟨p, hp⟩ := mem_iUnion.mp (hspace ▸ hucG)
  rw [hcover p] at hp
  obtain ⟨w, ⟨hw, hwC⟩, hcw⟩ := mem_iUnion₂.mp hp
  have huw : u ⊆ w := face_subset_of_mem_openSimplex_of_mem_convexHull G hu hw huc hcw
  exact ⟨p.val.1.val, p.val.1.property, p.val.2.val, p.val.2.property, p.property,
    (convexHull_mono (Finset.coe_subset.mpr huw)).trans hwC⟩

open Classical in
theorem exists_triangulation_doublePointSet_finrank_sup_le [FiniteDimensional ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (φ : E → F)
    (hind : ∀ s ∈ K.faces, AffineIndependent ℝ (fun v : s => φ (v : E)))
    (hinj : ∀ v ∈ K.vertices, InjOn (simplicialMap K φ) (starComplex K v).space) :
    ∃ G : Geometry.SimplicialComplex ℝ F, G.faces.Finite ∧
      G.space = doublePointSet (simplicialMap K φ) K.space ∧
        ∀ u ∈ G.faces, ∃ s ∈ K.faces, ∃ t ∈ K.faces, Disjoint s t ∧
          convexHull ℝ (u : Set F) ⊆
            convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t.image φ : Set F) ∧
              u.card + Module.finrank ℝ (vectorSpan ℝ (s.image φ : Set F) ⊔ vectorSpan ℝ (t.image φ : Set F) : Submodule ℝ F) + 1 ≤ s.card + t.card := by
  obtain ⟨G, hfinite, hspace, hcarrier⟩ := exists_triangulation_doublePointSet K φ hind hinj
  refine ⟨G, hfinite, hspace, fun u hu => ?_⟩
  obtain ⟨s, hs, t, ht, hdisj, hsub⟩ := hcarrier u hu
  have hsAI := (affineIndependent_image_iff s φ).mp (hind s hs)
  have htAI := (affineIndependent_image_iff t φ).mp (hind t ht)
  let S := simplexComplex (s.image φ) hsAI.2
  let T := simplexComplex (t.image φ) htAI.2
  have hsS : s.image φ ∈ S.faces := ⟨(K.nonempty_of_mem_faces hs).image φ, Finset.Subset.refl _⟩
  have htT : t.image φ ∈ T.faces := ⟨(K.nonempty_of_mem_faces ht).image φ, Finset.Subset.refl _⟩
  have hsub' : (u : Set F) ⊆ (fun x : F => x + 0) '' convexHull ℝ (s.image φ : Set F) ∩
      convexHull ℝ (t.image φ : Set F) := by
    simpa only [add_zero, Set.image_id'] using (subset_convexHull ℝ (u : Set F)).trans hsub
  have hbound := card_add_finrank_sup_le_of_subset_faces S T hsS htT (G.indep hu)
    (G.nonempty_of_mem_faces hu) 0 hsub'
  rw [Finset.card_image_of_injOn hsAI.1, Finset.card_image_of_injOn htAI.1] at hbound
  exact ⟨s, hs, t, ht, hdisj, hsub, hbound⟩

open Classical in
theorem exists_triangulation_doublePointSet_of_transverse_faces [FiniteDimensional ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (φ : E → F)
    (hind : ∀ s ∈ K.faces, AffineIndependent ℝ (fun v : s => φ (v : E)))
    (hinj : ∀ v ∈ K.vertices, InjOn (simplicialMap K φ) (starComplex K v).space)
    (htrans : ∀ s ∈ K.faces, ∀ t ∈ K.faces, Disjoint s t →
      (convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t.image φ : Set F)).Nonempty →
        vectorSpan ℝ (s.image φ : Set F) ⊔ vectorSpan ℝ (t.image φ : Set F) = ⊤) :
    ∃ G : Geometry.SimplicialComplex ℝ F, G.faces.Finite ∧
      G.space = doublePointSet (simplicialMap K φ) K.space ∧
        ∀ u ∈ G.faces, ∃ s ∈ K.faces, ∃ t ∈ K.faces, Disjoint s t ∧
          convexHull ℝ (u : Set F) ⊆
            convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t.image φ : Set F) ∧
              u.card + Module.finrank ℝ F + 1 ≤ s.card + t.card := by
  obtain ⟨G, hfinite, hspace, hcarrier⟩ := exists_triangulation_doublePointSet_finrank_sup_le K φ hind hinj
  refine ⟨G, hfinite, hspace, fun u hu => ?_⟩
  obtain ⟨s, hs, t, ht, hdisj, hsub, hbound⟩ := hcarrier u hu
  obtain ⟨y, hy⟩ := G.nonempty_of_mem_faces hu
  have hst := htrans s hs t ht hdisj ⟨y, hsub (subset_convexHull ℝ _ hy)⟩
  rw [hst, finrank_top] at hbound
  exact ⟨s, hs, t, ht, hdisj, hsub, hbound⟩

open Classical in
theorem exists_triangulation_doublePointSet_card_le_two [FiniteDimensional ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (φ : E → F)
    (hcard : ∀ s ∈ K.faces, s.card ≤ 3) (hdim : Module.finrank ℝ F = 3)
    (hind : ∀ s ∈ K.faces, AffineIndependent ℝ (fun v : s => φ (v : E)))
    (hinj : ∀ v ∈ K.vertices, InjOn (simplicialMap K φ) (starComplex K v).space)
    (htrans : ∀ s ∈ K.faces, ∀ t ∈ K.faces, Disjoint s t →
      (convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t.image φ : Set F)).Nonempty →
        vectorSpan ℝ (s.image φ : Set F) ⊔ vectorSpan ℝ (t.image φ : Set F) = ⊤) :
    ∃ G : Geometry.SimplicialComplex ℝ F, G.faces.Finite ∧
      G.space = doublePointSet (simplicialMap K φ) K.space ∧ (∀ u ∈ G.faces, u.card ≤ 2) ∧
        ∀ u ∈ G.faces, ∃ s ∈ K.faces, ∃ t ∈ K.faces, Disjoint s t ∧
          convexHull ℝ (u : Set F) ⊆
            convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t.image φ : Set F) := by
  obtain ⟨G, hfinite, hspace, hcarrier⟩ :=
    exists_triangulation_doublePointSet_of_transverse_faces K φ hind hinj htrans
  refine ⟨G, hfinite, hspace, ?_, ?_⟩
  · intro u hu
    obtain ⟨s, hs, t, ht, _, _, hbound⟩ := hcarrier u hu
    have hsbound := hcard s hs
    have htbound := hcard t ht
    omega
  · intro u hu
    obtain ⟨s, hs, t, ht, hdisj, hsub, _⟩ := hcarrier u hu
    exact ⟨s, hs, t, ht, hdisj, hsub⟩

open Classical in
def faceStarComplex (K : Geometry.SimplicialComplex ℝ E) (s : Finset E) :
    Geometry.SimplicialComplex ℝ E where
  faces := {t | t ∈ K.faces ∧ t ∪ s ∈ K.faces}
  isRelLowerSet_faces := by
    rintro t ⟨ht, hts⟩
    refine ⟨K.nonempty_of_mem_faces ht, fun u hut hu => ⟨K.down_closed ht hut hu, ?_⟩⟩
    exact K.down_closed hts (Finset.union_subset_union_left hut) (hu.mono Finset.subset_union_left)
  indep ht := K.indep ht.1
  inter_subset_convexHull ht hu := K.inter_subset_convexHull ht.1 hu.1

theorem faceStarComplex_faces_subset (K : Geometry.SimplicialComplex ℝ E) (s : Finset E) :
    (faceStarComplex K s).faces ⊆ K.faces := fun _ ht => ht.1

theorem faceStarComplex_faces_finite (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (s : Finset E) :
    (faceStarComplex K s).faces.Finite := (Set.toFinite K.faces).subset (faceStarComplex_faces_subset K s)

open Classical in
theorem faceStarComplex_space (K : Geometry.SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces)
    {x : E} (hx : x ∈ openSimplex s) : (faceStarComplex K s).space = closedStar K x := by
  ext y
  constructor
  · intro hy
    obtain ⟨t, ⟨ht, hts⟩, hyt⟩ := (faceStarComplex K s).mem_space_iff.mp hy
    refine mem_iUnion₂.mpr ⟨t ∪ s, ⟨hts, ?_⟩, ?_⟩
    · exact convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_right)
        (openSimplex_subset_convexHull s hx)
    · exact convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_left) hyt
  · intro hy
    obtain ⟨t, ⟨ht, hxt⟩, hyt⟩ := mem_iUnion₂.mp hy
    have hst := face_subset_of_mem_openSimplex_of_mem_convexHull K hs ht hx hxt
    exact (faceStarComplex K s).convexHull_subset_space
      ⟨ht, by rwa [Finset.union_eq_left.mpr hst]⟩ hyt

open Classical in
theorem coneComplex_starAvoiding_space (K : Geometry.SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) {x : E} (hx : x ∈ openSimplex s) :
    (coneComplex (isConeBase_starAvoiding K hs hx)).space = closedStar K x := by
  let hcone := isConeBase_starAvoiding K hs hx
  have hxx : x ∈ closedStar K x := mem_iUnion₂.mpr
    ⟨s, ⟨hs, openSimplex_subset_convexHull s hx⟩, openSimplex_subset_convexHull s hx⟩
  ext y
  constructor
  · intro hy
    rcases (mem_coneComplex_space_iff hcone).mp hy with rfl | ⟨z, hz, r, hr, hr1, rfl⟩
    · exact hxx
    · obtain ⟨t, ⟨ht, hts, _⟩, hzt⟩ := (starAvoiding K s).mem_space_iff.mp hz
      have hxu : x ∈ convexHull ℝ ((t ∪ s : Finset E) : Set E) :=
        convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_right) (openSimplex_subset_convexHull s hx)
      have hzu : z ∈ convexHull ℝ ((t ∪ s : Finset E) : Set E) :=
        convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_left) hzt
      refine mem_iUnion₂.mpr ⟨t ∪ s, ⟨hts, hxu⟩, ?_⟩
      rw [add_smul_sub_eq_combo]
      exact (convex_convexHull ℝ _) hxu hzu (by linarith) hr.le (by ring)
  · intro hy
    by_cases hyx : y = x
    · rw [hyx]
      exact apex_mem_coneComplex_space hcone
    obtain ⟨t, ⟨ht, hxt⟩, hyt⟩ := mem_iUnion₂.mp hy
    have hst := face_subset_of_mem_openSimplex_of_mem_convexHull K hs ht hx hxt
    obtain ⟨w, hws, hyw⟩ := exists_mem_convexHull_insert_erase_of_mem_openSimplex (K.indep ht) hst hx hyt
    have hne : (t.erase w).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.insert_empty, Finset.coe_singleton,
        convexHull_singleton] at hyw
      exact hyx hyw
    have hunion : t.erase w ∪ s = t := by
      apply Finset.Subset.antisymm (Finset.union_subset (Finset.erase_subset _ _) hst)
      intro z hz
      by_cases hzw : z = w
      · exact Finset.mem_union_right _ (hzw ▸ hws)
      · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hzw, hz⟩)
    have hbase : t.erase w ∈ (starAvoiding K s).faces :=
      ⟨K.down_closed ht (Finset.erase_subset _ _) hne, by rwa [hunion],
        fun h => Finset.notMem_erase w t (h hws)⟩
    exact (coneComplex hcone).convexHull_subset_space (Or.inr (Or.inr ⟨t.erase w, hbase, rfl⟩)) hyw

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLBall_faceStarComplex [FiniteDimensional ℝ E]
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) {s : Finset E} (hs : s ∈ K.faces) :
    IsPLBall (n + 1) (faceStarComplex K s).space := by
  let x := s.centroid ℝ id
  have hx : x ∈ openSimplex s := centroid_mem_openSimplex (K.nonempty_of_mem_faces hs)
  have hxK : x ∈ K.space := K.convexHull_subset_space hs (openSimplex_subset_convexHull s hx)
  obtain ⟨R, hR, hfinite, hxR⟩ := exists_isSubdivision_singleton_mem K hxK
  have : Finite R.faces := hfinite.to_subtype
  have : Finite (starAvoiding K s).faces := (starAvoiding_faces_finite K s).to_subtype
  obtain ⟨f, hf⟩ := exists_isPLHomeomorphOn_geometricLink_starAvoiding K hs hx hR hxR
  rw [faceStarComplex_space K hs hx, ← coneComplex_starAvoiding_space K hs hx]
  rcases (hK.of_isSubdivision hR) x hxR with hsphere | hball
  · exact (isConeBase_starAvoiding K hs hx).isPLBall_of_isPLSphere (hsphere.of_isPLHomeomorphOn hf)
  · exact (isConeBase_starAvoiding K hs hx).isPLBall_of_isPLBall (hball.of_isPLHomeomorphOn hf)

open Classical in
theorem geometricLink_faceStarComplex (K : Geometry.SimplicialComplex ℝ E) (s : Finset E) :
    SimplicialComplex.geometricLink (faceStarComplex K s) s = SimplicialComplex.geometricLink K s := by
  ext t
  rw [mem_geometricLink_faces_iff, mem_geometricLink_faces_iff]
  constructor
  · rintro ⟨hne, hdis, hface⟩
    exact ⟨hne, hdis, hface.1⟩
  · rintro ⟨hne, hdis, hface⟩
    refine ⟨hne, hdis, hface, ?_⟩
    simpa only [Finset.union_right_comm, Finset.union_self] using hface

open Classical in
theorem mem_boundaryComplex_faceStarComplex_faces_iff [FiniteDimensional ℝ E]
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) {s : Finset E} (hs : s ∈ K.faces) :
    s ∈ (boundaryComplex (n + 1) (faceStarComplex K s)).faces ↔
      s ∈ (boundaryComplex (n + 1) K).faces := by
  have : Finite (faceStarComplex K s).faces := (faceStarComplex_faces_finite K s).to_subtype
  have hS := (hK.isPLBall_faceStarComplex K hs).isCombinatorialManifoldWithBoundary
  have hsS : s ∈ (faceStarComplex K s).faces := ⟨hs, by rwa [Finset.union_self]⟩
  rw [hS.mem_boundaryComplex_faces_iff (faceStarComplex K s), hK.mem_boundaryComplex_faces_iff K,
    geometricLink_faceStarComplex]
  simp only [hsS, hs, true_and]

open Classical in
theorem mem_boundaryComplex_faceStarComplex_space_iff [FiniteDimensional ℝ E]
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) {s : Finset E} (hs : s ∈ K.faces)
    {x : E} (hx : x ∈ openSimplex s) :
    x ∈ (boundaryComplex (n + 1) (faceStarComplex K s)).space ↔
      x ∈ (boundaryComplex (n + 1) K).space := by
  have hsS : s ∈ (faceStarComplex K s).faces := ⟨hs, by rwa [Finset.union_self]⟩
  have hface := mem_boundaryComplex_faceStarComplex_faces_iff K hK hs
  constructor
  · intro hxS
    have hsB : s ∈ (boundaryComplex (n + 1) (faceStarComplex K s)).faces := by
      by_contra hnot
      exact notMem_space_of_notMem_faces (boundaryComplex_faces_subset (n + 1) (faceStarComplex K s)) hsS hnot hx hxS
    exact (boundaryComplex (n + 1) K).convexHull_subset_space (hface.mp hsB) (openSimplex_subset_convexHull s hx)
  · intro hxK
    have hsB : s ∈ (boundaryComplex (n + 1) K).faces := by
      by_contra hnot
      exact notMem_space_of_notMem_faces (boundaryComplex_faces_subset (n + 1) K) hs hnot hx hxK
    exact (boundaryComplex (n + 1) (faceStarComplex K s)).convexHull_subset_space (hface.mpr hsB)
      (openSimplex_subset_convexHull s hx)

theorem fiber_eq_pair_of_encard_le_two {X Y : Type*} (f : X → Y) (P : Set X)
    {a b : X} {y : Y} (ha : a ∈ P) (hb : b ∈ P) (hab : a ≠ b) (hfa : f a = y) (hfb : f b = y)
    (hcard : (P ∩ f ⁻¹' {y}).encard ≤ 2) : P ∩ f ⁻¹' {y} = {a, b} := by
  classical
  apply Subset.antisymm
  · intro x hx
    by_cases hxa : x = a
    · exact Or.inl hxa
    by_cases hxb : x = b
    · exact Or.inr hxb
    have hsub : ({x, a, b} : Set X) ⊆ P ∩ f ⁻¹' {y} := by
      intro z hz
      rcases hz with rfl | rfl | rfl
      · exact hx
      · exact ⟨ha, hfa⟩
      · exact ⟨hb, hfb⟩
    have h := (encard_mono hsub).trans hcard
    rw [encard_insert_of_notMem (by simp [hxa, hxb]), encard_pair hab] at h
    norm_num at h
  · rintro x (rfl | rfl)
    · exact ⟨ha, hfa⟩
    · exact ⟨hb, hfb⟩

theorem eventually_preimage_subset_of_isOpen_of_fiber_subset
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    (f : X → Y) {P U : Set X} (hP : IsCompact P) (hf : ContinuousOn f P)
    (hU : IsOpen U) {y : Y} (hsub : P ∩ f ⁻¹' {y} ⊆ U) :
    ∀ᶠ z in 𝓝 y, P ∩ f ⁻¹' {z} ⊆ U := by
  have hC : IsCompact (P ∩ Uᶜ) := hP.inter_right hU.isClosed_compl
  have hclosed : IsClosed (f '' (P ∩ Uᶜ)) := (hC.image_of_continuousOn (hf.mono inter_subset_left)).isClosed
  have hy : y ∉ f '' (P ∩ Uᶜ) := by
    rintro ⟨x, hx, hxy⟩
    exact hx.2 (hsub ⟨hx.1, hxy⟩)
  filter_upwards [hclosed.isOpen_compl.mem_nhds hy] with z hz
  intro x hx
  by_contra hxU
  exact hz ⟨x, ⟨hx.1, hxU⟩, hx.2⟩

theorem eventually_preimage_subset_union_of_fiber_eq_pair
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    (f : X → Y) {P A B : Set X} (hP : IsCompact P) (hf : ContinuousOn f P)
    {a b : X} {y : Y} (hfiber : P ∩ f ⁻¹' {y} = {a, b})
    (hA : A ∈ 𝓝[P] a) (hB : B ∈ 𝓝[P] b) :
    ∀ᶠ z in 𝓝 y, P ∩ f ⁻¹' {z} ⊆ A ∪ B := by
  obtain ⟨U, hU, haU, hUA⟩ := mem_nhdsWithin.mp hA
  obtain ⟨V, hV, hbV, hVB⟩ := mem_nhdsWithin.mp hB
  have hsub : P ∩ f ⁻¹' {y} ⊆ U ∪ V := by
    rw [hfiber]
    rintro x (rfl | rfl)
    · exact Or.inl haU
    · exact Or.inr hbV
  filter_upwards [eventually_preimage_subset_of_isOpen_of_fiber_subset f hP hf (hU.union hV) hsub]
    with z hz
  intro x hx
  rcases hz hx with hxU | hxV
  · exact Or.inl (hUA ⟨hxU, hx.1⟩)
  · exact Or.inr (hVB ⟨hxV, hx.1⟩)

theorem mem_doublePointSet_iff_mem_image_inter_of_injOn
    {X Y : Type*} (f : X → Y) {P A B : Set X} (hAP : A ⊆ P) (hBP : B ⊆ P)
    (hAB : Disjoint A B) (hA : InjOn f A) (hB : InjOn f B) {y : Y}
    (hcover : P ∩ f ⁻¹' {y} ⊆ A ∪ B) :
    y ∈ doublePointSet f P ↔ y ∈ f '' A ∩ f '' B := by
  constructor
  · rintro ⟨a, ha, b, hb, hab, hfa, hfb⟩
    rcases hcover ⟨ha, hfa⟩ with haA | haB
    · rcases hcover ⟨hb, hfb⟩ with hbA | hbB
      · exact False.elim (hab (hA haA hbA (hfa.trans hfb.symm)))
      · exact ⟨⟨a, haA, hfa⟩, ⟨b, hbB, hfb⟩⟩
    · rcases hcover ⟨hb, hfb⟩ with hbA | hbB
      · exact ⟨⟨b, hbA, hfb⟩, ⟨a, haB, hfa⟩⟩
      · exact False.elim (hab (hB haB hbB (hfa.trans hfb.symm)))
  · rintro ⟨⟨a, ha, hfa⟩, ⟨b, hb, hfb⟩⟩
    exact ⟨a, hAP ha, b, hBP hb, fun heq => Set.disjoint_left.mp hAB ha (heq ▸ hb), hfa, hfb⟩

open Classical in
theorem faceStarComplex_faces_subset_starComplex (K : Geometry.SimplicialComplex ℝ E)
    {s : Finset E} {v : E} (hv : v ∈ s) : (faceStarComplex K s).faces ⊆ (starComplex K v).faces := by
  intro t ht
  refine ⟨ht.1, K.down_closed ht.2 ?_ (Finset.insert_nonempty v t)⟩
  exact Finset.insert_subset_iff.mpr ⟨Finset.mem_union_right _ hv, Finset.subset_union_left⟩

open Classical in
omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem disjoint_faceStarComplex_faces_of_eq_of_injOn_starComplex (K : Geometry.SimplicialComplex ℝ E)
    (f : E → F) (hinj : ∀ v ∈ K.vertices, InjOn f (starComplex K v).space)
    {s t : Finset E} {x y : E} (hxs : x ∈ convexHull ℝ (s : Set E))
    (hyt : y ∈ convexHull ℝ (t : Set E)) (hxy : x ≠ y) (hfxy : f x = f y) :
    ∀ u ∈ (faceStarComplex K s).faces, ∀ v ∈ (faceStarComplex K t).faces, Disjoint u v := by
  intro u hu v hv
  have hxus := convexHull_mono (Finset.coe_subset.mpr (Finset.subset_union_right (s₁ := u))) hxs
  have hyvt := convexHull_mono (Finset.coe_subset.mpr (Finset.subset_union_right (s₁ := v))) hyt
  exact (disjoint_faces_of_eq_of_injOn_starComplex K f hinj hu.2 hv.2 hxus hyvt hxy hfxy).mono
    Finset.subset_union_left Finset.subset_union_left

open Classical in
theorem disjoint_spaces_of_disjoint_faces (K A B : Geometry.SimplicialComplex ℝ E)
    (hA : A.faces ⊆ K.faces) (hB : B.faces ⊆ K.faces)
    (hdisj : ∀ s ∈ A.faces, ∀ t ∈ B.faces, Disjoint s t) : Disjoint A.space B.space := by
  rw [Set.disjoint_left]
  intro x hxA hxB
  obtain ⟨s, hs, hxs⟩ := A.mem_space_iff.mp hxA
  obtain ⟨t, ht, hxt⟩ := B.mem_space_iff.mp hxB
  have hmem := K.inter_subset_convexHull (hA hs) (hB ht) ⟨hxs, hxt⟩
  rw [← Finset.coe_inter, Finset.disjoint_iff_inter_eq_empty.mp (hdisj s hs t ht),
    Finset.coe_empty, convexHull_empty] at hmem
  exact hmem

open Classical in
theorem exists_simplicialImage_of_faces_subset [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (K S : Geometry.SimplicialComplex ℝ E) [Finite S.faces] (hSK : S.faces ⊆ K.faces) (φ : E → F)
    (hind : ∀ s ∈ S.faces, AffineIndependent ℝ (fun v : s => φ (v : E)))
    (hinj : InjOn (simplicialMap K φ) S.space) :
    ∃ M : Geometry.SimplicialComplex ℝ F, M.faces.Finite ∧ M.space = simplicialMap K φ '' S.space ∧
      IsPLHomeomorphOn (simplicialMap K φ) S.space M.space ∧
        ∀ t ∈ M.faces, ∃ s ∈ S.faces, t = s.image φ := by
  have heq := simplicialMap_eqOn_of_faces_subset K S hSK φ
  have hinjS : InjOn (simplicialMap S φ) S.space := by
    intro x hx y hy hxy
    apply hinj hx hy
    rw [heq hx, heq hy]
    exact hxy
  have hindS : ∀ s ∈ S.faces, AffineIndependent ℝ ((↑) : ↥(s.image φ : Set F) → F) :=
    fun s hs => ((affineIndependent_image_iff s φ).mp (hind s hs)).2
  refine ⟨simplicialImage S φ hindS hinjS, simplicialImage_faces_finite S φ hindS hinjS, ?_,
    (isPLHomeomorphOn_simplicialImage S φ hindS hinjS).congr heq, fun t ht => ht⟩
  rw [simplicialImage_space]
  exact heq.symm.image_eq

def HasPLDoubleCrossingAt (f : E → F) (P : Set E) (y : F) : Prop :=
  ∃ (a b : E) (A B : Set E), a ∈ A ∧ b ∈ B ∧ f a = y ∧ f b = y ∧
    A ⊆ P ∧ B ⊆ P ∧ Disjoint A B ∧ A ∈ 𝓝[P] a ∧ B ∈ 𝓝[P] b ∧
      IsPLHomeomorphOn f A (f '' A) ∧ IsPLHomeomorphOn f B (f '' B) ∧
        HasPLCrossingAt (f '' A) (f '' B) y ∧ ∀ᶠ z in 𝓝 y, P ∩ f ⁻¹' {z} ⊆ A ∪ B

open Classical in
theorem hasPLDoubleCrossingAt_and_exists_local_intersection [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hdim : Module.finrank ℝ F = 3) (φ : E → F)
    (hind : ∀ s ∈ K.faces, AffineIndependent ℝ (fun v : s => φ (v : E)))
    (hinj : ∀ v ∈ K.vertices, InjOn (simplicialMap K φ) (starComplex K v).space)
    (hcard : ∀ y : F, (K.space ∩ (simplicialMap K φ) ⁻¹' {y}).encard ≤ 2)
    (htrans : ∀ s ∈ K.faces, ∀ t ∈ K.faces, Disjoint s t →
      (convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t.image φ : Set F)).Nonempty →
        vectorSpan ℝ (s.image φ : Set F) ⊔ vectorSpan ℝ (t.image φ : Set F) = ⊤)
    {y : F} (hy : y ∈ doublePointSet (simplicialMap K φ) K.space) :
    HasPLDoubleCrossingAt (simplicialMap K φ) K.space y ∧
      ∃ H : Geometry.SimplicialComplex ℝ F, H.faces.Finite ∧
        IsCombinatorialManifoldWithBoundary 1 H ∧ y ∈ H.space ∧
          ∀ᶠ z in 𝓝 y, z ∈ doublePointSet (simplicialMap K φ) K.space ↔ z ∈ H.space := by
  let f := simplicialMap K φ
  obtain ⟨a, ha, b, hb, hab, hfa, hfb⟩ := hy
  obtain ⟨s, hs, has⟩ := exists_face_mem_openSimplex K ha
  obtain ⟨t, ht, hbt⟩ := exists_face_mem_openSimplex K hb
  let S := faceStarComplex K s
  let T := faceStarComplex K t
  have hSK : S.faces ⊆ K.faces := faceStarComplex_faces_subset K s
  have hTK : T.faces ⊆ K.faces := faceStarComplex_faces_subset K t
  have : Finite S.faces := (faceStarComplex_faces_finite K s).to_subtype
  have : Finite T.faces := (faceStarComplex_faces_finite K t).to_subtype
  have hdisj : ∀ u ∈ S.faces, ∀ v ∈ T.faces, Disjoint u v :=
    disjoint_faceStarComplex_faces_of_eq_of_injOn_starComplex K f hinj
      (openSimplex_subset_convexHull s has) (openSimplex_subset_convexHull t hbt) hab (hfa.trans hfb.symm)
  have hST : Disjoint S.space T.space := disjoint_spaces_of_disjoint_faces K S T hSK hTK hdisj
  have hinjS : InjOn f S.space := by
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs
    have hvK := K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    exact (hinj v hvK).mono (space_mono_of_faces_subset (faceStarComplex_faces_subset_starComplex K hv))
  have hinjT : InjOn f T.space := by
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces ht
    have hvK := K.down_closed ht (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    exact (hinj v hvK).mono (space_mono_of_faces_subset (faceStarComplex_faces_subset_starComplex K hv))
  obtain ⟨M, hMfinite, hMspace, hMPL, hMfaces⟩ :=
    exists_simplicialImage_of_faces_subset K S hSK φ (fun u hu => hind u (hSK hu)) hinjS
  obtain ⟨N, hNfinite, hNspace, hNPL, hNfaces⟩ :=
    exists_simplicialImage_of_faces_subset K T hTK φ (fun u hu => hind u (hTK hu)) hinjT
  have : Finite M.faces := hMfinite.to_subtype
  have : Finite N.faces := hNfinite.to_subtype
  have hMman : IsCombinatorialManifoldWithBoundary 2 M :=
    ((hK.isPLBall_faceStarComplex K hs).isCombinatorialManifoldWithBoundary).of_isPLHomeomorphOn hMPL
  have hNman : IsCombinatorialManifoldWithBoundary 2 N :=
    ((hK.isPLBall_faceStarComplex K ht).isCombinatorialManifoldWithBoundary).of_isPLHomeomorphOn hNPL
  have htransMN : ∀ u ∈ M.faces, ∀ v ∈ N.faces,
      (convexHull ℝ (u : Set F) ∩ convexHull ℝ (v : Set F)).Nonempty →
        vectorSpan ℝ (u : Set F) ⊔ vectorSpan ℝ (v : Set F) = ⊤ := by
    intro u hu v hv hinter
    obtain ⟨u', hu', rfl⟩ := hMfaces u hu
    obtain ⟨v', hv', rfl⟩ := hNfaces v hv
    exact htrans u' (hSK hu') v' (hTK hv') (hdisj u' hu' v' hv') hinter
  have haS : a ∈ S.space := S.convexHull_subset_space
    ⟨hs, by rwa [Finset.union_self]⟩ (openSimplex_subset_convexHull s has)
  have hbT : b ∈ T.space := T.convexHull_subset_space
    ⟨ht, by rwa [Finset.union_self]⟩ (openSimplex_subset_convexHull t hbt)
  have hyMN : y ∈ M.space ∩ N.space := by
    rw [hMspace, hNspace]
    exact ⟨⟨a, haS, hfa⟩, ⟨b, hbT, hfb⟩⟩
  have hSneigh : S.space ∈ 𝓝[K.space] a := by
    rw [faceStarComplex_space K hs has]
    exact closedStar_mem_nhdsWithin K a
  have hTneigh : T.space ∈ 𝓝[K.space] b := by
    rw [faceStarComplex_space K ht hbt]
    exact closedStar_mem_nhdsWithin K b
  have hfiber : K.space ∩ f ⁻¹' {y} = {a, b} :=
    fiber_eq_pair_of_encard_le_two f K.space ha hb hab hfa hfb (hcard y)
  have hcover : ∀ᶠ z in 𝓝 y, K.space ∩ f ⁻¹' {z} ⊆ S.space ∪ T.space :=
    eventually_preimage_subset_union_of_fiber_eq_pair f (isPolyhedron_space K).isCompact
      (isPiecewiseAffineOn_simplicialMap K φ).continuousOn hfiber hSneigh hTneigh
  have hcross : HasPLCrossingAt (f '' S.space) (f '' T.space) y := by
    have h := hasPLCrossingAt_of_transverse_faces M N hMman hNman hdim htransMN hyMN
    rwa [hMspace, hNspace] at h
  refine ⟨⟨a, b, S.space, T.space, haS, hbT, hfa, hfb, space_mono_of_faces_subset hSK,
    space_mono_of_faces_subset hTK, hST, hSneigh, hTneigh, ?_, ?_, hcross, hcover⟩, ?_⟩
  · rwa [hMspace] at hMPL
  · rwa [hNspace] at hNPL
  · obtain ⟨H, hHfinite, hHspace, hHman⟩ :=
      exists_isCombinatorialManifoldWithBoundary_inter_of_transverse_faces M N hMman hNman hdim htransMN
    refine ⟨H, hHfinite, hHman, hHspace.symm ▸ hyMN, ?_⟩
    filter_upwards [hcover] with z hz
    rw [hHspace, hMspace, hNspace]
    exact mem_doublePointSet_iff_mem_image_inter_of_injOn f (space_mono_of_faces_subset hSK)
      (space_mono_of_faces_subset hTK) hST hinjS hinjT hz

open Classical in
theorem exists_isPLHomeomorphOn_geometricLink_of_eventually_eq_of_card_le_two
    [FiniteDimensional ℝ E] (G H : Geometry.SimplicialComplex ℝ E) [Finite G.faces] [Finite H.faces]
    (hcard : ∀ s ∈ G.faces, s.card ≤ 2) {x : E} (hxG : {x} ∈ G.faces) (hxH : {x} ∈ H.faces)
    (heq : ∀ᶠ y in 𝓝 x, y ∈ G.space ↔ y ∈ H.space) :
    ∃ f : E → E, IsPLHomeomorphOn f (SimplicialComplex.geometricLink G {x}).space
      (SimplicialComplex.geometricLink H {x}).space := by
  have hray : ∀ q : E, Filter.Tendsto (fun r : ℝ => x + r • (q - x)) (𝓝 0) (𝓝 x) := by
    intro q
    have hcont : Continuous (fun r : ℝ => x + r • (q - x)) := by fun_prop
    simpa only [zero_smul, add_zero] using hcont.tendsto 0
  refine exists_isPLHomeomorphOn_of_radial x (SimplicialComplex.geometricLink H {x})
    (SimplicialComplex.geometricLink G {x}) (isRadiallyInjective_geometricLink H)
    (isConeBase_geometricLink G) ?_ ?_
  · intro σ hσ
    obtain ⟨hσne, hxσ, hins⟩ := (SimplicialComplex.mem_geometricLink_singleton G x σ).mp hσ
    have hbound := hcard (insert x σ) hins
    rw [Finset.card_insert_of_notMem hxσ] at hbound
    have hpos := hσne.card_pos
    obtain ⟨q, rfl⟩ := Finset.card_eq_one.mp (show σ.card = 1 by omega)
    have hq : q ∈ (SimplicialComplex.geometricLink G {x}).space :=
      (SimplicialComplex.geometricLink G {x}).convexHull_subset_space hσ (by simp)
    have hqx : q ≠ x := ne_of_mem_of_not_mem hq (notMem_geometricLink_space G)
    have hHray : ∀ᶠ r : ℝ in 𝓝 0, 0 < r → x + r • (q - x) ∈ H.space := by
      filter_upwards [(hray q).eventually heq, eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)]
        with r hr hr1
      exact fun hr0 => hr.mp (mem_convexHull_insert_of_mem_geometricLink_space G hq hr0.le hr1.le)
    obtain ⟨c, hc, hclink⟩ := exists_ray_mem_geometricLink_space_of_eventually H hxH
      (sub_ne_zero.mpr hqx) hHray
    obtain ⟨τ, hτ, hcτ⟩ := (SimplicialComplex.geometricLink H {x}).mem_space_iff.mp hclink
    refine ⟨τ, hτ, ?_⟩
    intro w hw
    rw [Finset.mem_singleton] at hw
    subst w
    exact ⟨c, hc, hcτ⟩
  · intro q hq
    have hqx : q ≠ x := ne_of_mem_of_not_mem hq (notMem_geometricLink_space H)
    apply exists_ray_mem_geometricLink_space_of_eventually G hxG (sub_ne_zero.mpr hqx)
    filter_upwards [(hray q).eventually heq, eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)]
      with r hr hr1
    exact fun hr0 => hr.mpr (mem_convexHull_insert_of_mem_geometricLink_space H hq hr0.le hr1.le)

open Classical in
theorem isCombinatorialManifoldWithBoundary_one_of_locally_eq [FiniteDimensional ℝ E]
    (G : Geometry.SimplicialComplex ℝ E) [Finite G.faces] (hcard : ∀ s ∈ G.faces, s.card ≤ 2)
    (hlocal : ∀ x ∈ G.space, ∃ H : Geometry.SimplicialComplex ℝ E, H.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 1 H ∧ x ∈ H.space ∧
        ∀ᶠ y in 𝓝 x, y ∈ G.space ↔ y ∈ H.space) :
    IsCombinatorialManifoldWithBoundary 1 G := by
  intro x hx
  have hxG : x ∈ G.space := G.convexHull_subset_space hx (by simp)
  obtain ⟨H, hfinite, hHman, hxH, heq⟩ := hlocal x hxG
  have : Finite H.faces := hfinite.to_subtype
  obtain ⟨R, hR, hRfinite, hxR⟩ := exists_isSubdivision_singleton_mem H hxH
  have : Finite R.faces := hRfinite.to_subtype
  have heqR : ∀ᶠ y in 𝓝 x, y ∈ G.space ↔ y ∈ R.space := by
    simpa only [hR.space_eq] using heq
  obtain ⟨f, hf⟩ := exists_isPLHomeomorphOn_geometricLink_of_eventually_eq_of_card_le_two G R hcard hx hxR heqR
  rcases (hHman.of_isSubdivision hR) x hxR with hsphere | hball
  · exact Or.inl (hsphere.of_isPLHomeomorphOn hf.symm)
  · exact Or.inr (hball.of_isPLHomeomorphOn hf.symm)

open Classical in
theorem exists_isCombinatorialManifoldWithBoundary_doublePointSet_of_transverse_faces
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hdim : Module.finrank ℝ F = 3) (φ : E → F)
    (hind : ∀ s ∈ K.faces, AffineIndependent ℝ (fun v : s => φ (v : E)))
    (hinj : ∀ v ∈ K.vertices, InjOn (simplicialMap K φ) (starComplex K v).space)
    (hcard : ∀ y : F, (K.space ∩ (simplicialMap K φ) ⁻¹' {y}).encard ≤ 2)
    (htrans : ∀ s ∈ K.faces, ∀ t ∈ K.faces, Disjoint s t →
      (convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t.image φ : Set F)).Nonempty →
        vectorSpan ℝ (s.image φ : Set F) ⊔ vectorSpan ℝ (t.image φ : Set F) = ⊤) :
    ∃ G : Geometry.SimplicialComplex ℝ F, G.faces.Finite ∧
      G.space = doublePointSet (simplicialMap K φ) K.space ∧
        IsCombinatorialManifoldWithBoundary 1 G ∧
          ∀ y ∈ G.space, HasPLDoubleCrossingAt (simplicialMap K φ) K.space y := by
  obtain ⟨G, hfinite, hspace, hGcard, _⟩ := exists_triangulation_doublePointSet_card_le_two K φ
    (fun s hs => hK.card_le K hs) hdim hind hinj htrans
  have : Finite G.faces := hfinite.to_subtype
  have hlocal := fun (y : F) (hy : y ∈ doublePointSet (simplicialMap K φ) K.space) =>
    hasPLDoubleCrossingAt_and_exists_local_intersection K hK hdim φ hind hinj hcard htrans hy
  refine ⟨G, hfinite, hspace, isCombinatorialManifoldWithBoundary_one_of_locally_eq G hGcard ?_, ?_⟩
  · intro y hy
    obtain ⟨H, hHfinite, hHman, hyH, heq⟩ := (hlocal y (hspace ▸ hy)).2
    exact ⟨H, hHfinite, hHman, hyH, by simpa only [hspace] using heq⟩
  · exact fun y hy => (hlocal y (hspace ▸ hy)).1

open Classical in
theorem exists_small_simplicialMap_doublePointSet_manifold [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hdim : Module.finrank ℝ F = 3)
    (f : E → F) (hf : IsPiecewiseAffineOn f K.space)
    (hloc : IsLocallyInjective (K.space.domRestrict f))
    (hcard : ∀ y : F, (K.space ∩ f ⁻¹' {y}).encard ≤ 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ (R : Geometry.SimplicialComplex ℝ E) (φ : E → F) (G : Geometry.SimplicialComplex ℝ F),
      IsSubdivision R K ∧ R.faces.Finite ∧ IsPiecewiseAffineOn (simplicialMap R φ) K.space ∧
        (∀ x ∈ K.space, dist (simplicialMap R φ x) (f x) < ε) ∧
          (∀ v ∈ R.vertices, IsPLHomeomorphOn (simplicialMap R φ) (starComplex R v).space
            (simplicialMap R φ '' (starComplex R v).space)) ∧
              IsLocallyInjective (K.space.domRestrict (simplicialMap R φ)) ∧
                (∀ y : F, (K.space ∩ (simplicialMap R φ) ⁻¹' {y}).encard ≤ 2) ∧
                  G.faces.Finite ∧ G.space = doublePointSet (simplicialMap R φ) K.space ∧
                    IsCombinatorialManifoldWithBoundary 1 G ∧
                      ∀ y ∈ G.space, HasPLDoubleCrossingAt (simplicialMap R φ) K.space y := by
  obtain ⟨R, φ, hR, hfinite, hpl, hclose, hstar, hlocal, hfiber, hind, htrans⟩ :=
    exists_small_simplicialMap_self_transverse_of_fiber_encard_le_two K hK hdim f hf hloc hcard hε
  have : Finite R.faces := hfinite.to_subtype
  have hinj : ∀ v ∈ R.vertices, InjOn (simplicialMap R φ) (starComplex R v).space :=
    fun v hv => (hstar v hv).bijOn.injOn
  have hfiberR : ∀ y : F, (R.space ∩ (simplicialMap R φ) ⁻¹' {y}).encard ≤ 2 := by
    simpa only [hR.space_eq] using hfiber
  obtain ⟨G, hGfinite, hGspace, hGman, hcross⟩ :=
    exists_isCombinatorialManifoldWithBoundary_doublePointSet_of_transverse_faces R (hK.of_isSubdivision hR)
      hdim φ hind hinj hfiberR htrans
  rw [hR.space_eq] at hGspace hcross
  exact ⟨R, φ, G, hR, hfinite, hpl, hclose, hstar, hlocal, hfiber, hGfinite, hGspace, hGman, hcross⟩

open Classical in
theorem injOn_simplicialMap_of_dim_of_transverse_faces [FiniteDimensional ℝ F]
    (K S : Geometry.SimplicialComplex ℝ E) (hSK : S.faces ⊆ K.faces) (φ : E → F)
    (hdim : ∀ s ∈ S.faces, 2 * s.card ≤ Module.finrank ℝ F + 1)
    (hind : ∀ s ∈ K.faces, AffineIndependent ℝ (fun v : s => φ (v : E)))
    (hinj : ∀ v ∈ K.vertices, InjOn (simplicialMap K φ) (starComplex K v).space)
    (htrans : ∀ s ∈ K.faces, ∀ t ∈ K.faces, Disjoint s t →
      (convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t.image φ : Set F)).Nonempty →
        vectorSpan ℝ (s.image φ : Set F) ⊔ vectorSpan ℝ (t.image φ : Set F) = ⊤) :
    InjOn (simplicialMap K φ) S.space := by
  have hrank : ∀ u ∈ K.faces, Module.finrank ℝ (vectorSpan ℝ (u.image φ : Set F)) + 1 = u.card := by
    intro u hu
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hu
    have : Nonempty u := ⟨⟨v, hv⟩⟩
    have hrange : Set.range (fun v : u => φ v) = (u.image φ : Set F) := by ext q; simp
    have h := (hind u hu).finrank_vectorSpan_add_one
    change Module.finrank ℝ (vectorSpan ℝ (Set.range (fun v : u => φ v))) + 1 = Fintype.card u at h
    rw [hrange] at h
    simpa only [Fintype.card_coe] using h
  intro a ha b hb heq
  by_contra hab
  obtain ⟨s, hs, has⟩ := S.mem_space_iff.mp ha
  obtain ⟨t, ht, hbt⟩ := S.mem_space_iff.mp hb
  have hdisj := disjoint_faces_of_eq_of_injOn_starComplex K _ hinj (hSK hs) (hSK ht) has hbt hab heq
  have hinter : (convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t.image φ : Set F)).Nonempty :=
    ⟨simplicialMap K φ a, simplicialMap_mem_convexHull_image K φ (hSK hs) has,
      heq.symm ▸ simplicialMap_mem_convexHull_image K φ (hSK ht) hbt⟩
  have hsup := htrans s (hSK hs) t (hSK ht) hdisj hinter
  have hsdim := hrank s (hSK hs)
  have htdim := hrank t (hSK ht)
  have hsbound := hdim s hs
  have htbound := hdim t ht
  have hdim' := Submodule.finrank_sup_add_finrank_inf_eq
    (vectorSpan ℝ (s.image φ : Set F)) (vectorSpan ℝ (t.image φ : Set F))
  rw [hsup] at hdim'
  have hsum : Module.finrank ℝ F +
      Module.finrank ℝ (vectorSpan ℝ (s.image φ : Set F) ⊓ vectorSpan ℝ (t.image φ : Set F) : Submodule ℝ F) =
        Module.finrank ℝ (vectorSpan ℝ (s.image φ : Set F)) +
          Module.finrank ℝ (vectorSpan ℝ (t.image φ : Set F)) := by simpa using hdim'
  omega

open Classical in
theorem injOn_boundaryComplex_of_transverse_faces [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hdim : 3 ≤ Module.finrank ℝ F) (φ : E → F)
    (hind : ∀ s ∈ K.faces, AffineIndependent ℝ (fun v : s => φ (v : E)))
    (hinj : ∀ v ∈ K.vertices, InjOn (simplicialMap K φ) (starComplex K v).space)
    (htrans : ∀ s ∈ K.faces, ∀ t ∈ K.faces, Disjoint s t →
      (convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t.image φ : Set F)).Nonempty →
        vectorSpan ℝ (s.image φ : Set F) ⊔ vectorSpan ℝ (t.image φ : Set F) = ⊤) :
    InjOn (simplicialMap K φ) (boundaryComplex 2 K).space := by
  apply injOn_simplicialMap_of_dim_of_transverse_faces K (boundaryComplex 2 K)
    (boundaryComplex_faces_subset 2 K) φ _ hind hinj htrans
  intro s hs
  have hbound := ((hK.mem_boundaryComplex_faces_iff K).mp hs).2.1
  omega

open Classical in
theorem exists_small_affineIndependent_subsets_in_submodule [FiniteDimensional ℝ F] {ι : Type*}
    (V B : Finset ι) (hBV : B ⊆ V) (H : Submodule ℝ F) (φ₀ : ι → F)
    (hB : ∀ v ∈ B, φ₀ v ∈ H) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : ι → F, EqOn φ φ₀ (V : Set ι)ᶜ ∧ (∀ v, dist (φ v) (φ₀ v) < ε) ∧
      (∀ v ∈ B, φ v ∈ H) ∧ ∀ s : Finset ι, s ⊆ V → s.card ≤ Module.finrank ℝ F + 1 →
        (s ∩ B).card ≤ Module.finrank ℝ H + 1 → AffineIndependent ℝ (fun v : s => φ (v : ι)) := by
  let b₀ : ι → H := fun v => if hv : v ∈ B then ⟨φ₀ v, hB v hv⟩ else 0
  obtain ⟨b, _, hbclose, hbgood⟩ := exists_small_affineIndependent_subsets B b₀ (half_pos hε)
  let ψ₀ : ι → F := fun v => if v ∈ B then (b v : F) else φ₀ v
  have hψB : ∀ v ∈ B, ψ₀ v = (b v : F) := fun v hv => if_pos hv
  have hψclose : ∀ v, dist (ψ₀ v) (φ₀ v) < ε / 2 := by
    intro v
    by_cases hv : v ∈ B
    · rw [hψB v hv]
      have heq : (b₀ v : F) = φ₀ v := by simp only [b₀, dif_pos hv]
      rw [← heq]
      exact hbclose v
    · change dist (if v ∈ B then (b v : F) else φ₀ v) (φ₀ v) < ε / 2
      simpa only [if_neg hv, dist_self] using half_pos hε
  have hdisj : Disjoint (V \ B) B := Finset.disjoint_left.mpr
    (fun _ hv hBv => (Finset.mem_sdiff.mp hv).2 hBv)
  obtain ⟨φ, hfix, hfixB, hclose, hgood⟩ :=
    exists_small_affineIndependent_subsets_relative (V \ B) B hdisj ψ₀ (half_pos hε)
  refine ⟨φ, ?_, ?_, ?_, ?_⟩
  · intro v hv
    have hvB : v ∉ B := fun h => hv (hBV h)
    exact (hfix (fun h => hv (Finset.mem_sdiff.mp h).1)).trans (if_neg hvB)
  · intro v
    calc dist (φ v) (φ₀ v) ≤ dist (φ v) (ψ₀ v) + dist (ψ₀ v) (φ₀ v) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hclose v) (hψclose v)
      _ = ε := add_halves ε
  · intro v hv
    rw [hfixB hv, hψB v hv]
    exact (b v).property
  · intro s hs hcard hBcard
    apply hgood s (by simpa only [Finset.sdiff_union_of_subset hBV] using hs) hcard
    have hind := (hbgood (s ∩ B) Finset.inter_subset_right hBcard).map'
      H.subtype.toAffineMap Subtype.val_injective
    have heq : (fun w : (s ∩ B : Finset ι) => ψ₀ (w : ι)) =
        H.subtype.toAffineMap ∘ (fun w : (s ∩ B : Finset ι) => b (w : ι)) := by
      funext w
      exact hψB w (Finset.mem_inter.mp w.property).2
    rw [heq]
    exact hind

open Classical in
theorem exists_small_affineIndependent_subsets_in_halfSpace [FiniteDimensional ℝ F] {ι : Type*}
    (V B : Finset ι) (hBV : B ⊆ V) (ℓ : F →ₗ[ℝ] ℝ) (φ₀ : ι → F)
    (hB : ∀ v ∈ B, ℓ (φ₀ v) = 0) (hV : ∀ v ∈ V \ B, 0 < ℓ (φ₀ v)) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : ι → F, EqOn φ φ₀ (V : Set ι)ᶜ ∧ (∀ v, dist (φ v) (φ₀ v) < ε) ∧
      (∀ v ∈ B, ℓ (φ v) = 0) ∧ (∀ v ∈ V \ B, 0 < ℓ (φ v)) ∧
        ∀ s : Finset ι, s ⊆ V → s.card ≤ Module.finrank ℝ F + 1 →
          (s ∩ B).card ≤ Module.finrank ℝ (LinearMap.ker ℓ) + 1 →
            AffineIndependent ℝ (fun v : s => φ (v : ι)) := by
  let C := φ₀ '' ((V \ B : Finset ι) : Set ι)
  have hC : IsCompact C := ((V \ B).finite_toSet.image φ₀).isCompact
  have hopen : IsOpen {y : F | 0 < ℓ y} :=
    isOpen_lt continuous_const ℓ.continuous_of_finiteDimensional
  have hsub : C ⊆ {y : F | 0 < ℓ y} := by
    rintro y ⟨v, hv, rfl⟩
    exact hV v hv
  obtain ⟨δ, hδ, hthick⟩ := hC.exists_cthickening_subset_open hopen hsub
  obtain ⟨φ, hfix, hclose, hker, hgood⟩ := exists_small_affineIndependent_subsets_in_submodule V B hBV
    (LinearMap.ker ℓ) φ₀ (fun v hv => hB v hv) (lt_min hε hδ)
  refine ⟨φ, hfix, fun v => (hclose v).trans_le (min_le_left ε δ), hker, ?_, hgood⟩
  intro v hv
  exact hthick (mem_cthickening_of_dist_le (φ v) (φ₀ v) δ C ⟨v, hv, rfl⟩
    ((hclose v).trans_le (min_le_right ε δ)).le)

open Classical in
theorem vectorSpan_sup_eq_submodule_of_affineIndependent_subsets {ι : Type*}
    (B : Finset ι) (H : Submodule ℝ F) [FiniteDimensional ℝ H] (φ : ι → F)
    (hB : ∀ v ∈ B, φ v ∈ H)
    (hφ : ∀ u : Finset ι, u ⊆ B → u.card ≤ Module.finrank ℝ H + 1 →
      AffineIndependent ℝ (fun v : u => φ (v : ι)))
    {s t : Finset ι} (hs : s ⊆ B) (ht : t ⊆ B) (hst : Disjoint s t)
    (hinter : (convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t.image φ : Set F)).Nonempty) :
    vectorSpan ℝ (s.image φ : Set F) ⊔ vectorSpan ℝ (t.image φ : Set F) = H := by
  let : DecidableEq H := Classical.typeDecidableEq H
  let ψ : ι → H := fun v => if hv : v ∈ B then ⟨φ v, hB v hv⟩ else 0
  have hψ : ∀ v ∈ B, (ψ v : F) = φ v := fun v hv => by simp only [ψ, dif_pos hv]
  have hgood : ∀ u : Finset ι, u ⊆ B → u.card ≤ Module.finrank ℝ H + 1 →
      AffineIndependent ℝ (fun v : u => ψ (v : ι)) := by
    intro u hu hcard
    apply AffineIndependent.of_comp H.subtype.toAffineMap
    have heq : H.subtype.toAffineMap ∘ (fun v : u => ψ (v : ι)) = (fun v : u => φ (v : ι)) :=
      funext fun v => hψ v (hu v.property)
    rw [heq]
    exact hφ u hu hcard
  have himage : ∀ u : Finset ι, u ⊆ B →
      H.subtype.toAffineMap '' (u.image ψ : Set H) = (u.image φ : Set F) := by
    intro u hu
    simp only [Finset.coe_image, Set.image_image]
    exact image_congr fun v hv => hψ v (hu hv)
  have hinterH : (convexHull ℝ (s.image ψ : Set H) ∩ convexHull ℝ (t.image ψ : Set H)).Nonempty := by
    obtain ⟨y, hys, hyt⟩ := hinter
    rw [← himage s hs, ← H.subtype.toAffineMap.image_convexHull] at hys
    rw [← himage t ht, ← H.subtype.toAffineMap.image_convexHull] at hyt
    obtain ⟨a, ha, hay⟩ := hys
    obtain ⟨b, hb, hby⟩ := hyt
    have hab : a = b := Subtype.ext (hay.trans hby.symm)
    exact ⟨a, ha, hab.symm ▸ hb⟩
  have htrans := vectorSpan_sup_eq_top_of_affineIndependent_subsets B ψ hgood hs ht hst hinterH
  have hmap := congrArg (Submodule.map H.subtype) htrans
  rw [Submodule.map_sup, Submodule.map_subtype_top] at hmap
  have hspan : ∀ u : Finset ι, u ⊆ B →
      Submodule.map H.subtype (vectorSpan ℝ (u.image ψ : Set H)) = vectorSpan ℝ (u.image φ : Set F) := by
    intro u hu
    change Submodule.map H.subtype.toAffineMap.linear (vectorSpan ℝ (u.image ψ : Set H)) = _
    rw [H.subtype.toAffineMap.map_vectorSpan, himage u hu]
  simp only [Finset.coe_image] at hmap hspan ⊢
  rwa [hspan s hs, hspan t ht] at hmap

open Classical in
theorem exists_small_vertexMap_transverse_in_halfSpace [FiniteDimensional ℝ F] {ι : Type*}
    (V B : Finset ι) (hBV : B ⊆ V) (ℓ : F →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (φ₀ : ι → F)
    (hB : ∀ v ∈ B, ℓ (φ₀ v) = 0) (hV : ∀ v ∈ V \ B, 0 < ℓ (φ₀ v)) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : ι → F, EqOn φ φ₀ (V : Set ι)ᶜ ∧ (∀ v, dist (φ v) (φ₀ v) < ε) ∧
      (∀ v ∈ B, ℓ (φ v) = 0) ∧ (∀ v ∈ V \ B, 0 < ℓ (φ v)) ∧
        (∀ s : Finset ι, s ⊆ V → s.card ≤ Module.finrank ℝ F + 1 →
          (s ∩ B).card ≤ Module.finrank ℝ (LinearMap.ker ℓ) + 1 →
            AffineIndependent ℝ (fun v : s => φ (v : ι))) ∧
          ∀ s : Finset ι, s ⊆ V → ∀ t : Finset ι, t ⊆ V → Disjoint s t →
            (convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t.image φ : Set F)).Nonempty →
              vectorSpan ℝ (s.image φ : Set F) ⊔ vectorSpan ℝ (t.image φ : Set F) =
                if s ∪ t ⊆ B then LinearMap.ker ℓ else ⊤ := by
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hℓ
  rw [LinearMap.zero_apply] at hv
  have hrange : LinearMap.range ℓ = ⊤ := LinearMap.range_eq_top.mpr fun c =>
    ⟨(c / ℓ v) • v, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]⟩
  have hkerRank : Module.finrank ℝ (LinearMap.ker ℓ) + 1 = Module.finrank ℝ F := by
    have h := LinearMap.finrank_range_add_finrank_ker ℓ
    rw [hrange, finrank_top, Module.finrank_self] at h
    omega
  obtain ⟨φ, hfix, hclose, hzero, hpos, hgood⟩ :=
    exists_small_affineIndependent_subsets_in_halfSpace V B hBV ℓ φ₀ hB hV hε
  have hboundary : ∀ u : Finset ι, u ⊆ B → u.card ≤ Module.finrank ℝ (LinearMap.ker ℓ) + 1 →
      AffineIndependent ℝ (fun v : u => φ (v : ι)) := by
    intro u hu hcard
    apply hgood u (hu.trans hBV) (by omega)
    rwa [Finset.inter_eq_left.mpr hu]
  refine ⟨φ, hfix, hclose, hzero, hpos, hgood, ?_⟩
  intro s hs t ht hdisj hinter
  by_cases hsubB : s ∪ t ⊆ B
  · rw [if_pos hsubB]
    exact vectorSpan_sup_eq_submodule_of_affineIndependent_subsets B (LinearMap.ker ℓ) φ hzero hboundary
      (Finset.subset_union_left.trans hsubB) (Finset.subset_union_right.trans hsubB) hdisj hinter
  · rw [if_neg hsubB]
    apply vectorSpan_sup_eq_top_of_affineIndependent_subsets_relative V B φ _ hs ht hdisj hsubB hinter
    intro u hu hcard hBcard
    apply hgood u hu hcard
    omega

theorem linearMap_simplicialMap {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (K : Geometry.SimplicialComplex ℝ E) (φ : E → F) (A : F →ₗ[ℝ] G) (x : E) :
    A (simplicialMap K φ x) = simplicialMap K (A ∘ φ) x := by
  simp only [simplicialMap, map_sum, map_smul, Function.comp_apply]

theorem simplicialMap_nonneg_of_nonneg_vertices (K : Geometry.SimplicialComplex ℝ E) (φ : E → ℝ)
    (hφ : ∀ v ∈ K.vertices, 0 ≤ φ v) {x : E} (hx : x ∈ K.space) : 0 ≤ simplicialMap K φ x := by
  classical
  obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
  rw [simplicialMap_eq_of_mem K φ hs hxs]
  apply Finset.sum_nonneg
  intro v hv
  exact mul_nonneg (weights_nonneg hxs hv)
    (hφ v (K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)))

open Classical in
theorem simplicialMap_eq_zero_iff_of_mem_openSimplex (K : Geometry.SimplicialComplex ℝ E)
    (φ : E → ℝ) {s : Finset E} (hs : s ∈ K.faces) (hφ : ∀ v ∈ s, 0 ≤ φ v)
    {x : E} (hx : x ∈ openSimplex s) : simplicialMap K φ x = 0 ↔ ∀ v ∈ s, φ v = 0 := by
  have hxs := openSimplex_subset_convexHull s hx
  have hpos := (mem_openSimplex_self_iff (K.indep hs) hxs).mp hx
  rw [simplicialMap_eq_of_mem K φ hs hxs]
  simp only [smul_eq_mul]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun v hv => mul_nonneg (hpos v hv).le (hφ v hv))]
  constructor
  · intro h v hv
    exact (mul_eq_zero.mp (h v hv)).resolve_left (hpos v hv).ne'
  · intro h v hv
    rw [h v hv, mul_zero]

theorem simplicialMap_eq_zero_iff_of_eq_zero_on_vertices (K : Geometry.SimplicialComplex ℝ E)
    (φ ψ : E → ℝ) (hφ : ∀ v ∈ K.vertices, 0 ≤ φ v) (hψ : ∀ v ∈ K.vertices, 0 ≤ ψ v)
    (heq : ∀ v ∈ K.vertices, φ v = 0 ↔ ψ v = 0) {x : E} (hx : x ∈ K.space) :
    simplicialMap K φ x = 0 ↔ simplicialMap K ψ x = 0 := by
  classical
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex K hx
  have hvert : ∀ v ∈ s, v ∈ K.vertices := fun v hv =>
    K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  rw [simplicialMap_eq_zero_iff_of_mem_openSimplex K φ hs (fun v hv => hφ v (hvert v hv)) hxs,
    simplicialMap_eq_zero_iff_of_mem_openSimplex K ψ hs (fun v hv => hψ v (hvert v hv)) hxs]
  exact forall₂_congr fun v hv => heq v (hvert v hv)

open Classical in
theorem exists_small_simplicialMap_transverse_in_halfSpace [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hdim : Module.finrank ℝ F = 3)
    (ℓ : F →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (f : E → F) (hf : IsPiecewiseAffineOn f K.space)
    (hloc : IsLocallyInjective (K.space.domRestrict f))
    (hcard : ∀ y : F, (K.space ∩ f ⁻¹' {y}).encard ≤ 2)
    (hnonneg : ∀ x ∈ K.space, 0 ≤ ℓ (f x))
    (hboundary : ∀ x ∈ K.space, ℓ (f x) = 0 ↔ x ∈ (boundaryComplex 2 K).space)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (R : Geometry.SimplicialComplex ℝ E) (φ : E → F), IsSubdivision R K ∧ R.faces.Finite ∧
      IsPiecewiseAffineOn (simplicialMap R φ) K.space ∧
        (∀ x ∈ K.space, dist (simplicialMap R φ x) (f x) < ε) ∧
          (∀ v ∈ R.vertices, IsPLHomeomorphOn (simplicialMap R φ) (starComplex R v).space
            (simplicialMap R φ '' (starComplex R v).space)) ∧
              IsLocallyInjective (K.space.domRestrict (simplicialMap R φ)) ∧
                (∀ y : F, (K.space ∩ (simplicialMap R φ) ⁻¹' {y}).encard ≤ 2) ∧
                  (∀ x ∈ K.space, 0 ≤ ℓ (simplicialMap R φ x)) ∧
                    (∀ x ∈ K.space, ℓ (simplicialMap R φ x) = 0 ↔ x ∈ (boundaryComplex 2 K).space) ∧
                      (∀ s ∈ R.faces, AffineIndependent ℝ (fun v : s => φ (v : E))) ∧
                        ∀ s ∈ R.faces, ∀ t ∈ R.faces, Disjoint s t →
                          (convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t.image φ : Set F)).Nonempty →
                            vectorSpan ℝ (s.image φ : Set F) ⊔ vectorSpan ℝ (t.image φ : Set F) =
                              if ((s ∪ t : Finset E) : Set E) ⊆ (boundaryComplex 2 K).space
                                then LinearMap.ker ℓ else ⊤ := by
  obtain ⟨R, δ, hR, hfinite, heq, hδ, hstable⟩ :=
    exists_isSubdivision_stable_fiber_encard_le_two K f hf hloc hcard
  have : Finite R.faces := hfinite.to_subtype
  have hRman : IsCombinatorialManifoldWithBoundary 2 R := hK.of_isSubdivision hR
  have hvertices : R.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite R.faces)
  let V := hvertices.toFinset
  let B := V.filter (fun v => ℓ (f v) = 0)
  have hBV : B ⊆ V := Finset.filter_subset _ _
  have hVK : ∀ v ∈ V, v ∈ K.space := by
    intro v hv
    rw [← hR.space_eq]
    exact R.subset_space (hvertices.mem_toFinset.mp hv) (Finset.mem_singleton_self v)
  have hfaces : ∀ s ∈ R.faces, s ⊆ V := by
    intro s hs v hv
    apply hvertices.mem_toFinset.mpr
    exact R.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  have hB : ∀ v ∈ B, ℓ (f v) = 0 := fun _ hv => (Finset.mem_filter.mp hv).2
  have hV : ∀ v ∈ V \ B, 0 < ℓ (f v) := by
    intro v hv
    obtain ⟨hvV, hvB⟩ := Finset.mem_sdiff.mp hv
    have hne : ℓ (f v) ≠ 0 := fun h => hvB (Finset.mem_filter.mpr ⟨hvV, h⟩)
    exact lt_of_le_of_ne (hnonneg v (hVK v hvV)) hne.symm
  obtain ⟨φ, _, hclose, hzero, hpos, hgood, htrans⟩ :=
    exists_small_vertexMap_transverse_in_halfSpace V B hBV ℓ hℓ f hB hV (lt_min hδ hε)
  have hφnonneg : ∀ v ∈ R.vertices, 0 ≤ ℓ (φ v) := by
    intro v hv
    by_cases hvB : v ∈ B
    · rw [hzero v hvB]
    · exact (hpos v (Finset.mem_sdiff.mpr ⟨hvertices.mem_toFinset.mpr hv, hvB⟩)).le
  have hfnonneg : ∀ v ∈ R.vertices, 0 ≤ ℓ (f v) :=
    fun v hv => hnonneg v (hVK v (hvertices.mem_toFinset.mpr hv))
  have hzeroiff : ∀ v ∈ R.vertices, ℓ (φ v) = 0 ↔ ℓ (f v) = 0 := by
    intro v hv
    by_cases hvB : v ∈ B
    · simp only [hzero v hvB, hB v hvB]
    · have hφne := (hpos v (Finset.mem_sdiff.mpr ⟨hvertices.mem_toFinset.mpr hv, hvB⟩)).ne'
      have hfne : ℓ (f v) ≠ 0 := fun h => hvB (Finset.mem_filter.mpr ⟨hvertices.mem_toFinset.mpr hv, h⟩)
      simp only [hφne, hfne]
  obtain ⟨hstar, hlocal, hfiber⟩ := hstable φ
    (fun v _ => (hclose v).trans_le (min_le_left δ ε))
  have hkerbound : 2 ≤ Module.finrank ℝ (LinearMap.ker ℓ) := by
    have h := LinearMap.finrank_range_add_finrank_ker ℓ
    have hle := Submodule.finrank_le (LinearMap.range ℓ)
    rw [Module.finrank_self] at hle
    omega
  refine ⟨R, φ, hR, hfinite, ?_, ?_, hstar, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hR.space_eq] using isPiecewiseAffineOn_simplicialMap R φ
  · intro x hx
    rw [← heq hx]
    exact dist_simplicialMap_lt_of_dist_vertices_lt R
      (fun v _ => (hclose v).trans_le (min_le_right δ ε)) (hR.space_eq.symm ▸ hx)
  · rwa [hR.space_eq] at hlocal
  · rwa [hR.space_eq] at hfiber
  · intro x hx
    rw [linearMap_simplicialMap]
    exact simplicialMap_nonneg_of_nonneg_vertices R (ℓ ∘ φ) hφnonneg (hR.space_eq.symm ▸ hx)
  · intro x hx
    have h := simplicialMap_eq_zero_iff_of_eq_zero_on_vertices R (ℓ ∘ φ) (ℓ ∘ f)
      hφnonneg hfnonneg hzeroiff (hR.space_eq.symm ▸ hx)
    rw [← linearMap_simplicialMap R φ ℓ x, ← linearMap_simplicialMap R f ℓ x, heq hx] at h
    exact h.trans (hboundary x hx)
  · intro s hs
    have hc := hRman.card_le R hs
    have hbc := Finset.card_le_card (Finset.inter_subset_left (s₁ := s) (s₂ := B))
    exact hgood s (hfaces s hs) (by omega) (by omega)
  · intro s hs t ht hdisj hinter
    have hiff : s ∪ t ⊆ B ↔ ((s ∪ t : Finset E) : Set E) ⊆ (boundaryComplex 2 K).space := by
      constructor
      · intro h v hv
        exact (hboundary v (hVK v (hBV (h hv)))).mp (hB v (h hv))
      · intro h v hv
        have hvV := (Finset.union_subset (hfaces s hs) (hfaces t ht)) hv
        exact Finset.mem_filter.mpr ⟨hvV, (hboundary v (hVK v hvV)).mpr (h hv)⟩
    have h := htrans s (hfaces s hs) t (hfaces t ht) hdisj hinter
    simpa only [hiff] using h

theorem halfSpace_eq_of_linearMap_pos {V : Type*} [AddCommGroup V] [Module ℝ V]
    (S : Submodule ℝ V) (ℓ : V →ₗ[ℝ] ℝ) (hS : S ≤ LinearMap.ker ℓ) {u : V} (hu : 0 < ℓ u) (x : V) :
    (∃ z ∈ S, ∃ r : ℝ, 0 ≤ r ∧ x = z + r • u) ↔
      x ∈ S ⊔ Submodule.span ℝ {u} ∧ 0 ≤ ℓ x := by
  have heval : ∀ z ∈ S, ∀ r : ℝ, ℓ (z + r • u) = r * ℓ u := by
    intro z hz r
    have hz0 : ℓ z = 0 := hS hz
    rw [map_add, map_smul, hz0, smul_eq_mul, zero_add]
  constructor
  · rintro ⟨z, hz, r, hr, rfl⟩
    refine ⟨Submodule.add_mem _ (Submodule.mem_sup_left hz)
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u)))), ?_⟩
    rw [heval z hz r]
    exact mul_nonneg hr hu.le
  · rintro ⟨hx, hpos⟩
    obtain ⟨z, hz, w, hw, hzw⟩ := Submodule.mem_sup.mp hx
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hw
    have hr : 0 ≤ r := by
      rw [← hzw, heval z hz r] at hpos
      nlinarith
    exact ⟨z, hz, r, hr, hzw.symm⟩

theorem exists_common_inward_vector_of_sup_eq_ker {V : Type*} [AddCommGroup V] [Module ℝ V]
    (S T : Submodule ℝ V) (ℓ : V →ₗ[ℝ] ℝ) (hST : S ⊔ T = LinearMap.ker ℓ)
    {u v : V} (hu : 0 < ℓ u) (hv : 0 < ℓ v) :
    ∃ w ∈ (S ⊔ Submodule.span ℝ {u}) ⊓ (T ⊔ Submodule.span ℝ {v}), ℓ w = 1 := by
  let a := (ℓ u)⁻¹ • u
  let b := (ℓ v)⁻¹ • v
  have ha : ℓ a = 1 := by dsimp [a]; rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hu.ne']
  have hb : ℓ b = 1 := by dsimp [b]; rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hv.ne']
  have hab : a - b ∈ S ⊔ T := by
    rw [hST]
    change ℓ (a - b) = 0
    rw [map_sub, ha, hb, sub_self]
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp hab
  have hs0 : ℓ s = 0 := (le_sup_left.trans hST.le) hs
  have heq : a - s = b + t := by
    have haeq : a = s + t + b := sub_eq_iff_eq_add.mp hst.symm
    rw [haeq]
    abel
  refine ⟨a - s, ⟨?_, ?_⟩, ?_⟩
  · exact Submodule.sub_mem _
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u))))
      (Submodule.mem_sup_left hs)
  · rw [heq]
    exact Submodule.add_mem _
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton v))))
      (Submodule.mem_sup_left ht)
  · rw [map_sub, ha, hs0, sub_zero]

def HasPLBoundaryCrossingAt (M A B : Set E) (x : E) : Prop :=
  ∃ (U V : Set E) (h : E → E) (P Q : Submodule ℝ E) (ℓ : E →ₗ[ℝ] ℝ),
    IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ IsPLHomeomorphOn h U V ∧ h x = 0 ∧
      Module.finrank ℝ P = 2 ∧ Module.finrank ℝ Q = 2 ∧
        Module.finrank ℝ (P ⊓ Q : Submodule ℝ E) = 1 ∧ P ⊔ Q = ⊤ ∧
          (∃ u ∈ P ⊓ Q, ℓ u = 1) ∧ ∀ᶠ y in 𝓝 x,
            (y ∈ M ↔ 0 ≤ ℓ (h y)) ∧ (y ∈ A ↔ h y ∈ P ∧ 0 ≤ ℓ (h y)) ∧
              (y ∈ B ↔ h y ∈ Q ∧ 0 ≤ ℓ (h y))

theorem hasPLBoundaryCrossingAt_of_halfSpace_cones [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 3) (S T : Submodule ℝ E)
    (hSdim : Module.finrank ℝ S = 1) (hTdim : Module.finrank ℝ T = 1)
    (ℓ : E →ₗ[ℝ] ℝ) (hST : S ⊔ T = LinearMap.ker ℓ) {u v x : E}
    (hu : 0 < ℓ u) (hv : 0 < ℓ v) (hx : ℓ x = 0) {A B : Set E}
    (hA : ∀ᶠ y in 𝓝 x, y ∈ A ↔ ∃ z ∈ S, ∃ r : ℝ, 0 ≤ r ∧ y - x = z + r • u)
    (hB : ∀ᶠ y in 𝓝 x, y ∈ B ↔ ∃ z ∈ T, ∃ r : ℝ, 0 ≤ r ∧ y - x = z + r • v) :
    HasPLBoundaryCrossingAt {y : E | 0 ≤ ℓ y} A B x := by
  let P := S ⊔ Submodule.span ℝ {u}
  let Q := T ⊔ Submodule.span ℝ {v}
  have hSker : S ≤ LinearMap.ker ℓ := le_sup_left.trans hST.le
  have hTker : T ≤ LinearMap.ker ℓ := le_sup_right.trans hST.le
  have hdimPlane : ∀ R : Submodule ℝ E, ∀ w : E, Module.finrank ℝ R = 1 →
      R ≤ LinearMap.ker ℓ → 0 < ℓ w → Module.finrank ℝ (R ⊔ Submodule.span ℝ {w} : Submodule ℝ E) = 2 := by
    intro R w hRdim hRker hw
    have hwR : w ∉ R := fun h => hw.ne' (hRker h)
    have hw0 : w ≠ 0 := fun h => hwR (h.symm ▸ R.zero_mem)
    have hspan : Module.finrank ℝ (Submodule.span ℝ ({w} : Set E)) = 1 := finrank_span_singleton hw0
    have hinf : Module.finrank ℝ (R ⊓ Submodule.span ℝ {w} : Submodule ℝ E) = 0 :=
      Submodule.finrank_eq_zero.mpr (disjoint_iff.mp (Submodule.disjoint_span_singleton_of_notMem hwR))
    have h := Submodule.finrank_sup_add_finrank_inf_eq R (Submodule.span ℝ {w})
    omega
  have hPdim : Module.finrank ℝ P = 2 := hdimPlane S u hSdim hSker hu
  have hQdim : Module.finrank ℝ Q = 2 := hdimPlane T v hTdim hTker hv
  have hSP : S ≤ P := le_sup_left
  have hTQ : T ≤ Q := le_sup_left
  have hkerPQ : LinearMap.ker ℓ ≤ P ⊔ Q := by
    rw [← hST]
    exact sup_le (hSP.trans le_sup_left) (hTQ.trans le_sup_right)
  have huP : u ∈ P := Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton u))
  have hPQ : P ⊔ Q = ⊤ := by
    apply top_unique
    intro z _
    have hzker : z - (ℓ z / ℓ u) • u ∈ LinearMap.ker ℓ := by
      change ℓ (z - (ℓ z / ℓ u) • u) = 0
      rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hu.ne', sub_self]
    have h := Submodule.add_mem (P ⊔ Q) (hkerPQ hzker)
      ((P ⊔ Q).smul_mem (ℓ z / ℓ u) (Submodule.mem_sup_left huP))
    simpa only [sub_add_cancel] using h
  have hIdim : Module.finrank ℝ (P ⊓ Q : Submodule ℝ E) = 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq P Q
    rw [hPQ, finrank_top] at h
    omega
  have hh : IsPLHomeomorphOn (fun y : E => y - x) univ univ := by
    simpa only [sub_eq_add_neg] using isPLHomeomorphOn_add_const (-x)
  refine ⟨univ, univ, fun y => y - x, P, Q, ℓ, isOpen_univ, isOpen_univ, mem_univ x,
    hh, sub_self x, hPdim, hQdim, hIdim, hPQ, exists_common_inward_vector_of_sup_eq_ker S T ℓ hST hu hv, ?_⟩
  filter_upwards [hA, hB] with y hyA hyB
  refine ⟨?_, hyA.trans (halfSpace_eq_of_linearMap_pos S ℓ hSker hu (y - x)),
    hyB.trans (halfSpace_eq_of_linearMap_pos T ℓ hTker hv (y - x))⟩
  rw [map_sub, hx, sub_zero]

open Classical in
theorem eventually_mem_space_iff_mem_unique_coface_cone [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {s : Finset E} (hs : s ∈ K.faces)
    (hbound : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card + 1) {a x : E}
    (hcoface : {w | w ∉ s ∧ insert w s ∈ K.faces} = {a}) (hx : x ∈ openSimplex s) :
    ∀ᶠ y in 𝓝 x, y ∈ K.space ↔ ∃ z ∈ vectorSpan ℝ (s : Set E),
      ∃ r : ℝ, 0 ≤ r ∧ y - x = z + r • (a - x) := by
  have ha : a ∉ s ∧ insert a s ∈ K.faces := by
    change a ∈ {w | w ∉ s ∧ insert w s ∈ K.faces}
    rw [hcoface]
    exact rfl
  filter_upwards [eventually_mem_space_iff_mem_codimension_one_cone K hs hbound ⟨a, ha⟩ hx] with y hy
  constructor
  · intro hyK
    obtain ⟨w, hw, hws, hcone⟩ := hy.mp hyK
    have hwa : w = a := by
      have hmem : w ∈ {v | v ∉ s ∧ insert v s ∈ K.faces} := ⟨hw, hws⟩
      rwa [hcoface] at hmem
    exact hwa ▸ hcone
  · exact fun hcone => hy.mpr ⟨a, ha.1, ha.2, hcone⟩

open Classical in
theorem hasPLBoundaryCrossingAt_of_unique_cofaces [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hdim : Module.finrank ℝ E = 3) {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ L.faces)
    (hscard : s.card = 2) (htcard : t.card = 2)
    (hKbound : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card + 1)
    (hLbound : ∀ u ∈ L.faces, t ⊆ u → u.card ≤ t.card + 1) {a b x : E}
    (hKa : {w | w ∉ s ∧ insert w s ∈ K.faces} = {a})
    (hLb : {w | w ∉ t ∧ insert w t ∈ L.faces} = {b})
    (ℓ : E →ₗ[ℝ] ℝ) (hST : vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = LinearMap.ker ℓ)
    (ha : 0 < ℓ a) (hb : 0 < ℓ b) (hx : ℓ x = 0)
    (hxs : x ∈ openSimplex s) (hxt : x ∈ openSimplex t) :
    HasPLBoundaryCrossingAt {y : E | 0 ≤ ℓ y} K.space L.space x := by
  have hrank : ∀ (P : Geometry.SimplicialComplex ℝ E) (u : Finset E), u ∈ P.faces → u.card = 2 →
      Module.finrank ℝ (vectorSpan ℝ (u : Set E)) = 1 := by
    intro P u hu hcard
    have h := (P.indep hu).finrank_vectorSpan (show Fintype.card u = 1 + 1 by
      simpa only [Fintype.card_coe] using hcard)
    have hrange : Set.range ((↑) : u → E) = (u : Set E) := by ext y; simp
    change Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : u → E))) = 1 at h
    rwa [hrange] at h
  have hau : 0 < ℓ (a - x) := by rwa [map_sub, hx, sub_zero]
  have hbv : 0 < ℓ (b - x) := by rwa [map_sub, hx, sub_zero]
  exact hasPLBoundaryCrossingAt_of_halfSpace_cones hdim (vectorSpan ℝ (s : Set E))
    (vectorSpan ℝ (t : Set E)) (hrank K s hs hscard) (hrank L t ht htcard) ℓ hST hau hbv hx
      (eventually_mem_space_iff_mem_unique_coface_cone K hs hKbound hKa hxs)
      (eventually_mem_space_iff_mem_unique_coface_cone L ht hLbound hLb hxt)

open Classical in
theorem neighbors_singleton_of_eventually_nonneg_ray (G : Geometry.SimplicialComplex ℝ E)
    [Finite G.faces] (hcard : ∀ s ∈ G.faces, s.card ≤ 2) {x d : E} (hx : {x} ∈ G.faces) (hd : d ≠ 0)
    (hlocal : ∀ᶠ y in 𝓝 x, y ∈ G.space ↔ ∃ t : ℝ, 0 ≤ t ∧ y = x + t • d) :
    ∃ a, {y | y ≠ x ∧ {x, y} ∈ G.faces} = {a} := by
  have hray : ∀ z : E, Filter.Tendsto (fun r : ℝ => x + r • z) (𝓝 0) (𝓝 x) := by
    intro z
    have hcont : Continuous (fun r : ℝ => x + r • z) := by fun_prop
    simpa only [zero_smul, add_zero] using hcont.tendsto 0
  have hdG : ∀ᶠ r : ℝ in 𝓝 0, 0 < r → x + r • d ∈ G.space := by
    filter_upwards [(hray d).eventually hlocal] with r hr
    exact fun hr0 => hr.mpr ⟨r, hr0.le, rfl⟩
  obtain ⟨c, hc, hax, haedge⟩ := exists_neighbor_on_ray_of_eventually G hcard hx hd hdG
  let a := x + c • d
  have haL : a ∈ (SimplicialComplex.geometricLink G {x}).space := by
    rw [geometricLink_space_eq_neighbors_of_card_le G hcard x]
    exact ⟨hax, haedge⟩
  refine ⟨a, ?_⟩
  ext q
  change (q ≠ x ∧ {x, q} ∈ G.faces) ↔ q = a
  constructor
  · rintro ⟨hqx, hqedge⟩
    have hqL : q ∈ (SimplicialComplex.geometricLink G {x}).space := by
      rw [geometricLink_space_eq_neighbors_of_card_le G hcard x]
      exact ⟨hqx, hqedge⟩
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp ((hray (q - x)).eventually hlocal)
    let r := min δ 1 / 2
    have hr : 0 < r := half_pos (lt_min hδ zero_lt_one)
    have hrδ : r < δ := by
      have h := min_le_left δ 1
      dsimp [r]
      linarith
    have hr1 : r ≤ 1 := by
      have h := min_le_right δ 1
      dsimp [r]
      linarith
    have hrball : r ∈ ball (0 : ℝ) δ := by
      simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hr] using hrδ
    obtain ⟨t, ht, hpoint⟩ := (hball hrball).mp
      (mem_convexHull_insert_of_mem_geometricLink_space G hqL hr.le hr1)
    have hscalar : r • (q - x) = t • d := add_left_cancel hpoint
    have htne : t ≠ 0 := by
      intro hzero
      rw [hzero, zero_smul] at hscalar
      exact hqx (sub_eq_zero.mp ((smul_eq_zero.mp hscalar).resolve_left hr.ne'))
    have htpos : 0 < t := lt_of_le_of_ne ht htne.symm
    have hq : q - x = (t / r) • d := by
      calc q - x = r⁻¹ • (r • (q - x)) := by rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
        _ = r⁻¹ • (t • d) := by rw [hscalar]
        _ = (t / r) • d := by rw [smul_smul]; congr 1; ring
    apply isRadiallyInjective_geometricLink G a haL q hqL ((t / r) / c)
      (div_pos (div_pos htpos hr) hc)
    change q = x + ((t / r) / c) • (x + c • d - x)
    rw [add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ hc.ne', ← hq, add_sub_cancel]
  · rintro rfl
    exact ⟨hax, haedge⟩

theorem exists_nonneg_ray_eq_inter_halfSpace_cones {V : Type*} [AddCommGroup V] [Module ℝ V]
    (S T : Submodule ℝ V) (ℓ : V →ₗ[ℝ] ℝ) (hST : S ⊔ T = LinearMap.ker ℓ)
    (hdis : Disjoint S T) {u v : V} (hu : 0 < ℓ u) (hv : 0 < ℓ v) :
    ∃ w : V, ℓ w = 1 ∧ ∀ z : V,
      ((∃ s ∈ S, ∃ r : ℝ, 0 ≤ r ∧ z = s + r • u) ∧
        ∃ t ∈ T, ∃ r : ℝ, 0 ≤ r ∧ z = t + r • v) ↔
          ∃ r : ℝ, 0 ≤ r ∧ z = r • w := by
  let P := S ⊔ Submodule.span ℝ {u}
  let Q := T ⊔ Submodule.span ℝ {v}
  have hSker : S ≤ LinearMap.ker ℓ := le_sup_left.trans hST.le
  have hTker : T ≤ LinearMap.ker ℓ := le_sup_right.trans hST.le
  have hmem : ∀ R : Submodule ℝ V, R ≤ LinearMap.ker ℓ → ∀ a : V, ℓ a ≠ 0 →
      ∀ z ∈ R ⊔ Submodule.span ℝ {a}, ℓ z = 0 → z ∈ R := by
    intro R hR a ha z hz hz0
    obtain ⟨s, hs, q, hq, hsq⟩ := Submodule.mem_sup.mp hz
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hq
    have hs0 : ℓ s = 0 := hR hs
    have hr : r = 0 := by
      rw [← hsq, map_add, map_smul, hs0, zero_add, smul_eq_mul] at hz0
      exact (mul_eq_zero.mp hz0).resolve_right ha
    simpa only [← hsq, hr, zero_smul, add_zero] using hs
  obtain ⟨w, hw, hw1⟩ := exists_common_inward_vector_of_sup_eq_ker S T ℓ hST hu hv
  refine ⟨w, hw1, fun z => ?_⟩
  rw [halfSpace_eq_of_linearMap_pos S ℓ hSker hu,
    halfSpace_eq_of_linearMap_pos T ℓ hTker hv]
  constructor
  · rintro ⟨⟨hzP, hz0⟩, hzQ, _⟩
    have hzero : ℓ (z - ℓ z • w) = 0 := by
      rw [map_sub, map_smul, hw1, smul_eq_mul, mul_one, sub_self]
    have hzS : z - ℓ z • w ∈ S := hmem S hSker u hu.ne' _
      (P.sub_mem hzP (P.smul_mem _ hw.1)) hzero
    have hzT : z - ℓ z • w ∈ T := hmem T hTker v hv.ne' _
      (Q.sub_mem hzQ (Q.smul_mem _ hw.2)) hzero
    exact ⟨ℓ z, hz0, sub_eq_zero.mp (Submodule.disjoint_def.mp hdis _ hzS hzT)⟩
  · rintro ⟨r, hr, rfl⟩
    have hnonneg : 0 ≤ ℓ (r • w) := by rwa [map_smul, hw1, smul_eq_mul, mul_one]
    exact ⟨⟨P.smul_mem r hw.1, hnonneg⟩, Q.smul_mem r hw.2, hnonneg⟩

theorem eventually_mem_inter_iff_nonneg_ray_of_halfSpace_cones [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 3) (S T : Submodule ℝ E)
    (hSdim : Module.finrank ℝ S = 1) (hTdim : Module.finrank ℝ T = 1)
    (ℓ : E →ₗ[ℝ] ℝ) (hST : S ⊔ T = LinearMap.ker ℓ) {u v x : E}
    (hu : 0 < ℓ u) (hv : 0 < ℓ v) {A B : Set E}
    (hA : ∀ᶠ y in 𝓝 x, y ∈ A ↔ ∃ z ∈ S, ∃ r : ℝ, 0 ≤ r ∧ y - x = z + r • u)
    (hB : ∀ᶠ y in 𝓝 x, y ∈ B ↔ ∃ z ∈ T, ∃ r : ℝ, 0 ≤ r ∧ y - x = z + r • v) :
    ∃ w : E, ℓ w = 1 ∧ ∀ᶠ y in 𝓝 x,
      y ∈ A ∩ B ↔ ∃ r : ℝ, 0 ≤ r ∧ y = x + r • w := by
  have hrange : LinearMap.range ℓ = ⊤ := LinearMap.range_eq_top.mpr fun c =>
    ⟨(c / ℓ u) • u, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hu.ne']⟩
  have hker : Module.finrank ℝ (LinearMap.ker ℓ) = 2 := by
    have h := LinearMap.finrank_range_add_finrank_ker ℓ
    rw [hrange, finrank_top, Module.finrank_self] at h
    omega
  have hdis : Disjoint S T := by
    apply disjoint_iff.mpr
    apply Submodule.finrank_eq_zero.mp
    have h := Submodule.finrank_sup_add_finrank_inf_eq S T
    rw [hST, hker, hSdim, hTdim] at h
    omega
  obtain ⟨w, hw, heq⟩ := exists_nonneg_ray_eq_inter_halfSpace_cones S T ℓ hST hdis hu hv
  refine ⟨w, hw, ?_⟩
  filter_upwards [hA, hB] with y hyA hyB
  rw [Set.mem_inter_iff, hyA, hyB, heq]
  simp only [sub_eq_iff_eq_add, add_comm]

open Classical in
theorem eventually_mem_inter_iff_nonneg_ray_of_unique_cofaces [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hdim : Module.finrank ℝ E = 3) {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ L.faces)
    (hscard : s.card = 2) (htcard : t.card = 2)
    (hKbound : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card + 1)
    (hLbound : ∀ u ∈ L.faces, t ⊆ u → u.card ≤ t.card + 1) {a b x : E}
    (hKa : {w | w ∉ s ∧ insert w s ∈ K.faces} = {a})
    (hLb : {w | w ∉ t ∧ insert w t ∈ L.faces} = {b})
    (ℓ : E →ₗ[ℝ] ℝ) (hST : vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = LinearMap.ker ℓ)
    (ha : 0 < ℓ a) (hb : 0 < ℓ b) (hx : ℓ x = 0)
    (hxs : x ∈ openSimplex s) (hxt : x ∈ openSimplex t) :
    ∃ w : E, ℓ w = 1 ∧ ∀ᶠ y in 𝓝 x,
      y ∈ K.space ∩ L.space ↔ ∃ r : ℝ, 0 ≤ r ∧ y = x + r • w := by
  have hrank : ∀ (P : Geometry.SimplicialComplex ℝ E) (u : Finset E), u ∈ P.faces → u.card = 2 →
      Module.finrank ℝ (vectorSpan ℝ (u : Set E)) = 1 := by
    intro P u hu hcard
    have h := (P.indep hu).finrank_vectorSpan (show Fintype.card u = 1 + 1 by
      simpa only [Fintype.card_coe] using hcard)
    have hrange : Set.range ((↑) : u → E) = (u : Set E) := by ext y; simp
    change Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : u → E))) = 1 at h
    rwa [hrange] at h
  have hau : 0 < ℓ (a - x) := by rwa [map_sub, hx, sub_zero]
  have hbv : 0 < ℓ (b - x) := by rwa [map_sub, hx, sub_zero]
  exact eventually_mem_inter_iff_nonneg_ray_of_halfSpace_cones hdim
    (vectorSpan ℝ (s : Set E)) (vectorSpan ℝ (t : Set E)) (hrank K s hs hscard)
    (hrank L t ht htcard) ℓ hST hau hbv
    (eventually_mem_space_iff_mem_unique_coface_cone K hs hKbound hKa hxs)
    (eventually_mem_space_iff_mem_unique_coface_cone L ht hLbound hLb hxt)

open Classical in
theorem neighbors_singleton_of_unique_cofaces [FiniteDimensional ℝ E]
    (K L G : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces] [Finite G.faces]
    (hdim : Module.finrank ℝ E = 3) (hGcard : ∀ u ∈ G.faces, u.card ≤ 2)
    (hspace : G.space = K.space ∩ L.space)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ L.faces)
    (hscard : s.card = 2) (htcard : t.card = 2)
    (hKbound : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card + 1)
    (hLbound : ∀ u ∈ L.faces, t ⊆ u → u.card ≤ t.card + 1) {a b x : E}
    (hKa : {w | w ∉ s ∧ insert w s ∈ K.faces} = {a})
    (hLb : {w | w ∉ t ∧ insert w t ∈ L.faces} = {b})
    (ℓ : E →ₗ[ℝ] ℝ) (hST : vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = LinearMap.ker ℓ)
    (ha : 0 < ℓ a) (hb : 0 < ℓ b) (hx : ℓ x = 0)
    (hxs : x ∈ openSimplex s) (hxt : x ∈ openSimplex t) (hxG : {x} ∈ G.faces) :
    ∃ c, {y | y ≠ x ∧ {x, y} ∈ G.faces} = {c} := by
  obtain ⟨w, hw, hlocal⟩ := eventually_mem_inter_iff_nonneg_ray_of_unique_cofaces K L hdim hs ht
    hscard htcard hKbound hLbound hKa hLb ℓ hST ha hb hx hxs hxt
  have hw0 : w ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hw
    exact zero_ne_one hw
  apply neighbors_singleton_of_eventually_nonneg_ray G hGcard hxG hw0
  rwa [hspace]

open Classical in
theorem linearMap_eq_zero_iff_of_mem_openSimplex (K : Geometry.SimplicialComplex ℝ E)
    (ℓ : E →ₗ[ℝ] ℝ) {s : Finset E} (hs : s ∈ K.faces) (hℓ : ∀ v ∈ s, 0 ≤ ℓ v)
    {x : E} (hx : x ∈ openSimplex s) : ℓ x = 0 ↔ ∀ v ∈ s, ℓ v = 0 := by
  have heq := simplicialMap_eqOn_affine K ℓ.toAffineMap
    (K.convexHull_subset_space hs (openSimplex_subset_convexHull s hx))
  exact heq ▸ simplicialMap_eq_zero_iff_of_mem_openSimplex K ℓ hs hℓ hx

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_unique_coface_in_halfSpace_of_boundary_facets [FiniteDimensional ℝ E]
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) (ℓ : E →ₗ[ℝ] ℝ)
    (hnonneg : ∀ v ∈ K.vertices, 0 ≤ ℓ v)
    (hboundary : ∀ s ∈ K.faces, n + 1 ≤ s.card → (∀ v ∈ s, ℓ v = 0) → s ∈ (boundaryComplex (n + 1) K).faces)
    {s : Finset E} (hs : s ∈ K.faces) (hscard : s.card = n + 1) (hszero : ∀ v ∈ s, ℓ v = 0) :
    ∃ a, 0 < ℓ a ∧ {w | w ∉ s ∧ insert w s ∈ K.faces} = {a} := by
  have hbound : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card + 1 := by
    intro u hu _
    rw [hscard]
    exact hK.card_le K hu
  have hlink := ((hK.mem_boundaryComplex_faces_iff K).mp (hboundary s hs hscard.ge hszero)).2.2
  rw [hscard, Nat.sub_self, geometricLink_space_eq_coface_vertices_of_card_le K s hbound] at hlink
  obtain ⟨a, ha⟩ := isPLBall_zero_iff.mp hlink
  have hamem : a ∉ s ∧ insert a s ∈ K.faces := by
    change a ∈ {w | w ∉ s ∧ insert w s ∈ K.faces}
    rw [ha]
    exact rfl
  have ha0 : 0 ≤ ℓ a := hnonneg a (K.down_closed hamem.2 (by simp) (Finset.singleton_nonempty a))
  have hane : ℓ a ≠ 0 := by
    intro hzero
    have hB := hboundary (insert a s) hamem.2 (by rw [Finset.card_insert_of_notMem hamem.1, hscard]; omega) (by simpa only [Finset.mem_insert, forall_eq_or_imp] using And.intro hzero hszero)
    have hcard := ((hK.mem_boundaryComplex_faces_iff K).mp hB).2.1
    rw [Finset.card_insert_of_notMem hamem.1, hscard] at hcard
    omega
  exact ⟨a, lt_of_le_of_ne ha0 hane.symm, ha⟩

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_unique_coface_in_halfSpace [FiniteDimensional ℝ E]
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) (ℓ : E →ₗ[ℝ] ℝ)
    (hnonneg : ∀ v ∈ K.vertices, 0 ≤ ℓ v)
    (hboundary : ∀ s ∈ K.faces, (∀ v ∈ s, ℓ v = 0) → s ∈ (boundaryComplex (n + 1) K).faces)
    {s : Finset E} (hs : s ∈ K.faces) (hscard : s.card = n + 1) (hszero : ∀ v ∈ s, ℓ v = 0) :
    ∃ a, 0 < ℓ a ∧ {w | w ∉ s ∧ insert w s ∈ K.faces} = {a} := by
  exact hK.exists_unique_coface_in_halfSpace_of_boundary_facets K ℓ hnonneg
    (fun u hu _ => hboundary u hu) hs hscard hszero

open Classical in
theorem exists_unique_cofaces_of_transverse_boundary_faces [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hdim : Module.finrank ℝ E = 3) (ℓ : E →ₗ[ℝ] ℝ)
    (hKnonneg : ∀ v ∈ K.vertices, 0 ≤ ℓ v) (hLnonneg : ∀ v ∈ L.vertices, 0 ≤ ℓ v)
    (hKboundary : ∀ s ∈ K.faces, 2 ≤ s.card → (∀ v ∈ s, ℓ v = 0) → s ∈ (boundaryComplex 2 K).faces)
    (hLboundary : ∀ t ∈ L.faces, 2 ≤ t.card → (∀ v ∈ t, ℓ v = 0) → t ∈ (boundaryComplex 2 L).faces)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ L.faces)
    (hszero : ∀ v ∈ s, ℓ v = 0) (htzero : ∀ v ∈ t, ℓ v = 0)
    (hinter : (convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty)
    (hst : vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = LinearMap.ker ℓ) :
    ∃ a b, s.card = 2 ∧ t.card = 2 ∧ 0 < ℓ a ∧ 0 < ℓ b ∧
      {w | w ∉ s ∧ insert w s ∈ K.faces} = {a} ∧ {w | w ∉ t ∧ insert w t ∈ L.faces} = {b} := by
  have hsbound : s.card ≤ 2 := by
    by_cases hsc : 2 ≤ s.card
    · exact ((hK.mem_boundaryComplex_faces_iff K).mp (hKboundary s hs hsc hszero)).2.1
    · omega
  have htbound : t.card ≤ 2 := by
    by_cases htc : 2 ≤ t.card
    · exact ((hL.mem_boundaryComplex_faces_iff L).mp (hLboundary t ht htc htzero)).2.1
    · omega
  have hker : 2 ≤ Module.finrank ℝ (LinearMap.ker ℓ) := by
    have h := LinearMap.finrank_range_add_finrank_ker ℓ
    have hrange : Module.finrank ℝ (LinearMap.range ℓ) ≤ 1 := by
      simpa using Submodule.finrank_le (LinearMap.range ℓ)
    omega
  obtain ⟨x, hx⟩ := hinter
  have hAI : AffineIndependent ℝ ((↑) : ({x} : Finset E) → E) := by
    apply affineIndependent_of_forall_eq_zero
    intro c hc _ v hv
    simpa only [Finset.sum_singleton, Finset.mem_singleton.mp hv] using hc
  have hsub : (({x} : Finset E) : Set E) ⊆ (fun y : E => y + 0) '' convexHull ℝ (s : Set E) ∩
      convexHull ℝ (t : Set E) := by
    simpa only [add_zero, Set.image_id', Finset.coe_singleton, Set.singleton_subset_iff] using hx
  have hbound := card_add_finrank_sup_le_of_subset_faces K L hs ht hAI (Finset.singleton_nonempty x) 0 hsub
  rw [hst, Finset.card_singleton] at hbound
  have hsc : s.card = 2 := by omega
  have htc : t.card = 2 := by omega
  obtain ⟨a, ha, hKa⟩ := hK.exists_unique_coface_in_halfSpace_of_boundary_facets K ℓ hKnonneg hKboundary hs hsc hszero
  obtain ⟨b, hb, hLb⟩ := hL.exists_unique_coface_in_halfSpace_of_boundary_facets L ℓ hLnonneg hLboundary ht htc htzero
  exact ⟨a, b, hsc, htc, ha, hb, hKa, hLb⟩

open Classical in
theorem neighbors_of_inter_in_halfSpace_of_boundary_edges [FiniteDimensional ℝ E]
    (K L G : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces] [Finite G.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hdim : Module.finrank ℝ E = 3) (ℓ : E →ₗ[ℝ] ℝ)
    (hKnonneg : ∀ v ∈ K.vertices, 0 ≤ ℓ v) (hLnonneg : ∀ v ∈ L.vertices, 0 ≤ ℓ v)
    (hKboundary : ∀ s ∈ K.faces, 2 ≤ s.card → (∀ v ∈ s, ℓ v = 0) → s ∈ (boundaryComplex 2 K).faces)
    (hLboundary : ∀ t ∈ L.faces, 2 ≤ t.card → (∀ v ∈ t, ℓ v = 0) → t ∈ (boundaryComplex 2 L).faces)
    (hcard : ∀ u ∈ G.faces, u.card ≤ 2) (hspace : G.space = K.space ∩ L.space)
    (hcarrier : ∀ u ∈ G.faces, ∃ s ∈ K.faces, ∃ t ∈ L.faces,
      convexHull ℝ (u : Set E) ⊆ convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E))
    (htrans : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      (convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty →
        vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) =
          if ∀ v ∈ s ∪ t, ℓ v = 0 then LinearMap.ker ℓ else ⊤)
    {x : E} (hxG : {x} ∈ G.faces) :
    (ℓ x = 0 ∧ ∃ a, {y | y ≠ x ∧ {x, y} ∈ G.faces} = {a}) ∨
      (ℓ x ≠ 0 ∧ ((∃ a, {y | y ≠ x ∧ {x, y} ∈ G.faces} = {a}) ∨
        ∃ a b, a ≠ b ∧ {y | y ≠ x ∧ {x, y} ∈ G.faces} = {a, b})) := by
  have hxspace : x ∈ G.space := G.subset_space hxG (Finset.mem_singleton_self _)
  rw [hspace] at hxspace
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex K hxspace.1
  obtain ⟨t, ht, hxt⟩ := exists_face_mem_openSimplex L hxspace.2
  have hsiff := linearMap_eq_zero_iff_of_mem_openSimplex K ℓ hs (fun v hv =>
    hKnonneg v (K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v))) hxs
  have htiff := linearMap_eq_zero_iff_of_mem_openSimplex L ℓ ht (fun v hv =>
    hLnonneg v (L.down_closed ht (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v))) hxt
  have hzero : (∀ v ∈ s ∪ t, ℓ v = 0) ↔ ℓ x = 0 := by
    constructor
    · intro h
      exact hsiff.mpr fun v hv => h v (Finset.mem_union_left t hv)
    · intro h v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact hsiff.mp h v hv
      · exact htiff.mp h v hv
  have hst := htrans s hs t ht ⟨x, openSimplex_subset_convexHull s hxs,
    openSimplex_subset_convexHull t hxt⟩
  by_cases hx0 : ℓ x = 0
  · rw [if_pos (hzero.mpr hx0)] at hst
    obtain ⟨a, b, hsc, htc, ha, hb, hKa, hLb⟩ := exists_unique_cofaces_of_transverse_boundary_faces
      K L hK hL hdim ℓ hKnonneg hLnonneg hKboundary hLboundary hs ht (hsiff.mp hx0) (htiff.mp hx0)
      ⟨x, openSimplex_subset_convexHull s hxs, openSimplex_subset_convexHull t hxt⟩ hst
    refine Or.inl ⟨hx0, neighbors_singleton_of_unique_cofaces K L G hdim hcard hspace hs ht hsc htc
      (fun u hu _ => ?_) (fun u hu _ => ?_) hKa hLb ℓ hst ha hb hx0 hxs hxt hxG⟩
    · rw [hsc]
      exact hK.card_le K hu
    · rw [htc]
      exact hL.card_le L hu
  · rw [if_neg (fun h => hx0 (hzero.mp h))] at hst
    exact Or.inr ⟨hx0, neighbors_singleton_or_pair_of_transverse_face K L G hK hL hdim hcard
      hspace hcarrier hs ht hxs hxt hxG hst⟩

open Classical in
theorem neighbors_of_inter_in_halfSpace [FiniteDimensional ℝ E]
    (K L G : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces] [Finite G.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hdim : Module.finrank ℝ E = 3) (ℓ : E →ₗ[ℝ] ℝ)
    (hKnonneg : ∀ v ∈ K.vertices, 0 ≤ ℓ v) (hLnonneg : ∀ v ∈ L.vertices, 0 ≤ ℓ v)
    (hKboundary : ∀ s ∈ K.faces, (∀ v ∈ s, ℓ v = 0) → s ∈ (boundaryComplex 2 K).faces)
    (hLboundary : ∀ t ∈ L.faces, (∀ v ∈ t, ℓ v = 0) → t ∈ (boundaryComplex 2 L).faces)
    (hcard : ∀ u ∈ G.faces, u.card ≤ 2) (hspace : G.space = K.space ∩ L.space)
    (hcarrier : ∀ u ∈ G.faces, ∃ s ∈ K.faces, ∃ t ∈ L.faces,
      convexHull ℝ (u : Set E) ⊆ convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E))
    (htrans : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      (convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty →
        vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) =
          if ∀ v ∈ s ∪ t, ℓ v = 0 then LinearMap.ker ℓ else ⊤)
    {x : E} (hxG : {x} ∈ G.faces) :
    (ℓ x = 0 ∧ ∃ a, {y | y ≠ x ∧ {x, y} ∈ G.faces} = {a}) ∨
      (ℓ x ≠ 0 ∧ ((∃ a, {y | y ≠ x ∧ {x, y} ∈ G.faces} = {a}) ∨
        ∃ a b, a ≠ b ∧ {y | y ≠ x ∧ {x, y} ∈ G.faces} = {a, b})) := by
  exact neighbors_of_inter_in_halfSpace_of_boundary_edges K L G hK hL hdim ℓ hKnonneg hLnonneg
    (fun s hs _ => hKboundary s hs) (fun t ht _ => hLboundary t ht) hcard hspace hcarrier htrans hxG

open Classical in
theorem isCombinatorialManifoldWithBoundary_inter_in_halfSpace_of_boundary_edges [FiniteDimensional ℝ E]
    (K L G : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces] [Finite G.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hdim : Module.finrank ℝ E = 3) (ℓ : E →ₗ[ℝ] ℝ)
    (hKnonneg : ∀ v ∈ K.vertices, 0 ≤ ℓ v) (hLnonneg : ∀ v ∈ L.vertices, 0 ≤ ℓ v)
    (hKboundary : ∀ s ∈ K.faces, 2 ≤ s.card → (∀ v ∈ s, ℓ v = 0) → s ∈ (boundaryComplex 2 K).faces)
    (hLboundary : ∀ t ∈ L.faces, 2 ≤ t.card → (∀ v ∈ t, ℓ v = 0) → t ∈ (boundaryComplex 2 L).faces)
    (hspace : G.space = K.space ∩ L.space)
    (hcarrier : ∀ u ∈ G.faces, ∃ s ∈ K.faces, ∃ t ∈ L.faces,
      convexHull ℝ (u : Set E) ⊆ convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E))
    (htrans : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      (convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty →
        vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) =
          if ∀ v ∈ s ∪ t, ℓ v = 0 then LinearMap.ker ℓ else ⊤) :
    IsCombinatorialManifoldWithBoundary 1 G ∧ ∀ x, {x} ∈ G.faces → ℓ x = 0 →
      ∃ a, {y | y ≠ x ∧ {x, y} ∈ G.faces} = {a} := by
  have hker : 2 ≤ Module.finrank ℝ (LinearMap.ker ℓ) := by
    have h := LinearMap.finrank_range_add_finrank_ker ℓ
    have hrange : Module.finrank ℝ (LinearMap.range ℓ) ≤ 1 := by
      simpa using Submodule.finrank_le (LinearMap.range ℓ)
    omega
  have hcard : ∀ u ∈ G.faces, u.card ≤ 2 := by
    intro u hu
    obtain ⟨s, hs, t, ht, hsub⟩ := hcarrier u hu
    obtain ⟨p, hp⟩ := G.nonempty_of_mem_faces hu
    have hst := htrans s hs t ht ⟨p, hsub (subset_convexHull ℝ _ hp)⟩
    have hsub' : (u : Set E) ⊆ (fun y : E => y + 0) '' convexHull ℝ (s : Set E) ∩
        convexHull ℝ (t : Set E) := by
      simpa only [add_zero, Set.image_id'] using (subset_convexHull ℝ (u : Set E)).trans hsub
    have hbound := card_add_finrank_sup_le_of_subset_faces K L hs ht (G.indep hu)
      (G.nonempty_of_mem_faces hu) 0 hsub'
    by_cases hzero : ∀ v ∈ s ∪ t, ℓ v = 0
    · rw [if_pos hzero] at hst
      rw [hst] at hbound
      have hsbound : s.card ≤ 2 := by
        by_cases hsc : 2 ≤ s.card
        · exact ((hK.mem_boundaryComplex_faces_iff K).mp
            (hKboundary s hs hsc (fun v hv => hzero v (Finset.mem_union_left t hv)))).2.1
        · omega
      have htbound : t.card ≤ 2 := by
        by_cases htc : 2 ≤ t.card
        · exact ((hL.mem_boundaryComplex_faces_iff L).mp
            (hLboundary t ht htc (fun v hv => hzero v (Finset.mem_union_right s hv)))).2.1
        · omega
      omega
    · rw [if_neg hzero] at hst
      rw [hst, finrank_top, hdim] at hbound
      have hsbound := hK.card_le K hs
      have htbound := hL.card_le L ht
      omega
  have hdegrees := fun x hx => neighbors_of_inter_in_halfSpace_of_boundary_edges K L G hK hL hdim ℓ hKnonneg
    hLnonneg hKboundary hLboundary hcard hspace hcarrier htrans (x := x) hx
  refine ⟨(isCombinatorialManifoldWithBoundary_one_iff G).mpr ⟨hcard, ?_⟩, ?_⟩
  · intro x hx
    rcases hdegrees x hx with ⟨_, hsingle⟩ | ⟨_, hdegree⟩
    · exact Or.inl hsingle
    · exact hdegree
  · intro x hx hx0
    rcases hdegrees x hx with ⟨_, hsingle⟩ | ⟨hne, _⟩
    · exact hsingle
    · exact (hne hx0).elim

open Classical in
theorem exists_isCombinatorialManifoldWithBoundary_inter_in_halfSpace_of_boundary_edges [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hdim : Module.finrank ℝ E = 3) (ℓ : E →ₗ[ℝ] ℝ)
    (hKnonneg : ∀ v ∈ K.vertices, 0 ≤ ℓ v) (hLnonneg : ∀ v ∈ L.vertices, 0 ≤ ℓ v)
    (hKboundary : ∀ s ∈ K.faces, 2 ≤ s.card → (∀ v ∈ s, ℓ v = 0) → s ∈ (boundaryComplex 2 K).faces)
    (hLboundary : ∀ t ∈ L.faces, 2 ≤ t.card → (∀ v ∈ t, ℓ v = 0) → t ∈ (boundaryComplex 2 L).faces)
    (htrans : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      (convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty →
        vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) =
          if ∀ v ∈ s ∪ t, ℓ v = 0 then LinearMap.ker ℓ else ⊤) :
    ∃ G : Geometry.SimplicialComplex ℝ E, G.faces.Finite ∧ G.space = K.space ∩ L.space ∧
      IsCombinatorialManifoldWithBoundary 1 G ∧ ∀ x, {x} ∈ G.faces → ℓ x = 0 →
        ∃ a, {y | y ≠ x ∧ {x, y} ∈ G.faces} = {a} := by
  obtain ⟨G, hGfin, hspace, hcarrier⟩ := exists_triangulation_inter K L
  have : Finite G.faces := hGfin.to_subtype
  obtain ⟨hman, hdegree⟩ := isCombinatorialManifoldWithBoundary_inter_in_halfSpace_of_boundary_edges
    K L G hK hL hdim ℓ hKnonneg hLnonneg hKboundary hLboundary hspace hcarrier htrans
  exact ⟨G, hGfin, hspace, hman, hdegree⟩

open Classical in
theorem exists_isCombinatorialManifoldWithBoundary_inter_in_halfSpace [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hdim : Module.finrank ℝ E = 3) (ℓ : E →ₗ[ℝ] ℝ)
    (hKnonneg : ∀ v ∈ K.vertices, 0 ≤ ℓ v) (hLnonneg : ∀ v ∈ L.vertices, 0 ≤ ℓ v)
    (hKboundary : ∀ s ∈ K.faces, (∀ v ∈ s, ℓ v = 0) → s ∈ (boundaryComplex 2 K).faces)
    (hLboundary : ∀ t ∈ L.faces, (∀ v ∈ t, ℓ v = 0) → t ∈ (boundaryComplex 2 L).faces)
    (htrans : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      (convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty →
        vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) =
          if ∀ v ∈ s ∪ t, ℓ v = 0 then LinearMap.ker ℓ else ⊤) :
    ∃ G : Geometry.SimplicialComplex ℝ E, G.faces.Finite ∧ G.space = K.space ∩ L.space ∧
      IsCombinatorialManifoldWithBoundary 1 G ∧ ∀ x, {x} ∈ G.faces → ℓ x = 0 →
        ∃ a, {y | y ≠ x ∧ {x, y} ∈ G.faces} = {a} := by
  exact exists_isCombinatorialManifoldWithBoundary_inter_in_halfSpace_of_boundary_edges K L hK hL
    hdim ℓ hKnonneg hLnonneg (fun s hs _ => hKboundary s hs) (fun t ht _ => hLboundary t ht) htrans

open Classical in
theorem IsCombinatorialManifoldWithBoundary.mem_boundaryComplex_of_faces_subset [FiniteDimensional ℝ E]
    {n : ℕ} (K S : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite S.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hS : IsCombinatorialManifoldWithBoundary (n + 1) S) (hSK : S.faces ⊆ K.faces)
    {s : Finset E} (hs : s ∈ S.faces) (hcard : s.card = n + 1)
    (hsB : s ∈ (boundaryComplex (n + 1) K).faces) : s ∈ (boundaryComplex (n + 1) S).faces := by
  have hKbound : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card + 1 := by
    intro u hu _
    rw [hcard]
    exact hK.card_le K hu
  have hSbound : ∀ u ∈ S.faces, s ⊆ u → u.card ≤ s.card + 1 := by
    intro u hu _
    rw [hcard]
    exact hS.card_le S hu
  have hlink := ((hK.mem_boundaryComplex_faces_iff K).mp hsB).2.2
  rw [hcard, Nat.sub_self, geometricLink_space_eq_coface_vertices_of_card_le K s hKbound] at hlink
  obtain ⟨a, ha⟩ := isPLBall_zero_iff.mp hlink
  have hsub : {w | w ∉ s ∧ insert w s ∈ S.faces} ⊆ {a} := by
    rw [← ha]
    exact fun w hw => ⟨hw.1, hSK hw.2⟩
  have hsingle : ∃ b, {w | w ∉ s ∧ insert w s ∈ S.faces} = {b} := by
    rcases hS.codimension_one_cofaces S hs hcard with h | ⟨b, c, hbc, heq⟩
    · exact h
    · have hb : b = a := hsub (heq.symm ▸ (show b ∈ ({b, c} : Set E) by simp))
      have hc : c = a := hsub (heq.symm ▸ (show c ∈ ({b, c} : Set E) by simp))
      exact (hbc (hb.trans hc.symm)).elim
  apply (hS.mem_boundaryComplex_faces_iff S).mpr
  refine ⟨hs, hcard.le, ?_⟩
  rw [hcard, Nat.sub_self, geometricLink_space_eq_coface_vertices_of_card_le S s hSbound]
  exact isPLBall_zero_iff.mpr hsingle

open Classical in
theorem boundaryComplex_space_of_isPLHomeomorphOn_of_isPLBall [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] {n : ℕ} (K : Geometry.SimplicialComplex ℝ E)
    (L : Geometry.SimplicialComplex ℝ F) [Finite K.faces] [Finite L.faces]
    (hK : IsPLBall (n + 1) K.space) {f : E → F} (hf : IsPLHomeomorphOn f K.space L.space) :
    (boundaryComplex (n + 1) L).space = f '' (boundaryComplex (n + 1) K).space := by
  obtain ⟨g, hg⟩ := hK
  rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex L (hg.trans hf),
    boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex K hg, Set.image_image]
  rfl

open Classical in
theorem IsPLHomeomorphOn.mem_boundaryComplex_image [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F)
    [Finite K.faces] [Finite L.faces] (hK : IsPLBall (n + 1) K.space) (φ : E → F)
    (hf : IsPLHomeomorphOn (simplicialMap K φ) K.space L.space) {s : Finset E}
    (hs : s ∈ (boundaryComplex (n + 1) K).faces) (ht : s.image φ ∈ L.faces) :
    s.image φ ∈ (boundaryComplex (n + 1) L).faces := by
  let y := (s.image φ).centroid ℝ id
  have hy : y ∈ openSimplex (s.image φ) := centroid_mem_openSimplex (L.nonempty_of_mem_faces ht)
  have hyHull := openSimplex_subset_convexHull (s.image φ) hy
  rw [← image_convexHull_simplicialMap K φ hs.1
    (injOn_of_injOn_simplicialMap K φ hf.1.injOn hs.1)] at hyHull
  obtain ⟨x, hx, hxy⟩ := hyHull
  have hyB : y ∈ (boundaryComplex (n + 1) L).space := by
    rw [boundaryComplex_space_of_isPLHomeomorphOn_of_isPLBall K L hK hf]
    exact ⟨x, (boundaryComplex (n + 1) K).convexHull_subset_space hs hx, hxy⟩
  by_contra hnot
  exact notMem_space_of_notMem_faces (boundaryComplex_faces_subset (n + 1) L) ht hnot hy hyB

open Classical in
theorem boundary_faces_of_simplicialImage_of_faces_subset [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (K S : Geometry.SimplicialComplex ℝ E)
    (M : Geometry.SimplicialComplex ℝ F) [Finite K.faces] [Finite S.faces] [Finite M.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hS : IsPLBall 2 S.space)
    (hSK : S.faces ⊆ K.faces) (φ : E → F) (ℓ : F →ₗ[ℝ] ℝ)
    (hM : IsPLHomeomorphOn (simplicialMap K φ) S.space M.space)
    (hfaces : ∀ t ∈ M.faces, ∃ s ∈ S.faces, t = s.image φ)
    (hboundary : ∀ s ∈ K.faces, (∀ v ∈ s, ℓ (φ v) = 0) → s ∈ (boundaryComplex 2 K).faces) :
    ∀ t ∈ M.faces, 2 ≤ t.card → (∀ v ∈ t, ℓ v = 0) → t ∈ (boundaryComplex 2 M).faces := by
  intro t ht htcard htzero
  obtain ⟨s, hs, rfl⟩ := hfaces t ht
  have hsB : s ∈ (boundaryComplex 2 K).faces :=
    hboundary s (hSK hs) (fun v hv => htzero (φ v) (Finset.mem_image_of_mem φ hv))
  have hsbound := ((hK.mem_boundaryComplex_faces_iff K).mp hsB).2.1
  have hscard : s.card = 2 := by
    have hle := Finset.card_image_le (f := φ) (s := s)
    omega
  have hsSB := hK.mem_boundaryComplex_of_faces_subset K S hS.isCombinatorialManifoldWithBoundary
    hSK hs hscard hsB
  have hM' : IsPLHomeomorphOn (simplicialMap S φ) S.space M.space :=
    hM.congr (simplicialMap_eqOn_of_faces_subset K S hSK φ).symm
  exact hM'.mem_boundaryComplex_image S M hS φ hsSB ht

open Classical in
theorem hasPLCrossingAt_or_hasPLBoundaryCrossingAt_of_transverse_faces [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hdim : Module.finrank ℝ E = 3) (ℓ : E →ₗ[ℝ] ℝ)
    (hKnonneg : ∀ v ∈ K.vertices, 0 ≤ ℓ v) (hLnonneg : ∀ v ∈ L.vertices, 0 ≤ ℓ v)
    (hKboundary : ∀ s ∈ K.faces, 2 ≤ s.card → (∀ v ∈ s, ℓ v = 0) → s ∈ (boundaryComplex 2 K).faces)
    (hLboundary : ∀ t ∈ L.faces, 2 ≤ t.card → (∀ v ∈ t, ℓ v = 0) → t ∈ (boundaryComplex 2 L).faces)
    (htrans : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      (convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty →
        vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) =
          if ∀ v ∈ s ∪ t, ℓ v = 0 then LinearMap.ker ℓ else ⊤)
    {x : E} (hx : x ∈ K.space ∩ L.space) :
    (ℓ x = 0 ∧ HasPLBoundaryCrossingAt {y : E | 0 ≤ ℓ y} K.space L.space x ∧
      ∃ w : E, ℓ w = 1 ∧ ∀ᶠ y in 𝓝 x,
        y ∈ K.space ∩ L.space ↔ ∃ r : ℝ, 0 ≤ r ∧ y = x + r • w) ∨
      (0 < ℓ x ∧ HasPLCrossingAt K.space L.space x) := by
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex K hx.1
  obtain ⟨t, ht, hxt⟩ := exists_face_mem_openSimplex L hx.2
  have hsiff := linearMap_eq_zero_iff_of_mem_openSimplex K ℓ hs (fun v hv =>
    hKnonneg v (K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v))) hxs
  have htiff := linearMap_eq_zero_iff_of_mem_openSimplex L ℓ ht (fun v hv =>
    hLnonneg v (L.down_closed ht (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v))) hxt
  have hzero : (∀ v ∈ s ∪ t, ℓ v = 0) ↔ ℓ x = 0 := by
    constructor
    · intro h
      exact hsiff.mpr fun v hv => h v (Finset.mem_union_left t hv)
    · intro h v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact hsiff.mp h v hv
      · exact htiff.mp h v hv
  have hinter : (convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty :=
    ⟨x, openSimplex_subset_convexHull s hxs, openSimplex_subset_convexHull t hxt⟩
  have hst := htrans s hs t ht hinter
  by_cases hx0 : ℓ x = 0
  · rw [if_pos (hzero.mpr hx0)] at hst
    obtain ⟨a, b, hsc, htc, ha, hb, hKa, hLb⟩ := exists_unique_cofaces_of_transverse_boundary_faces
      K L hK hL hdim ℓ hKnonneg hLnonneg hKboundary hLboundary hs ht (hsiff.mp hx0) (htiff.mp hx0) hinter hst
    have hKbound : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card + 1 := by
      intro u hu _
      rw [hsc]
      exact hK.card_le K hu
    have hLbound : ∀ u ∈ L.faces, t ⊆ u → u.card ≤ t.card + 1 := by
      intro u hu _
      rw [htc]
      exact hL.card_le L hu
    exact Or.inl ⟨hx0, hasPLBoundaryCrossingAt_of_unique_cofaces K L hdim hs ht hsc htc
      hKbound hLbound hKa hLb ℓ hst ha hb hx0 hxs hxt,
        eventually_mem_inter_iff_nonneg_ray_of_unique_cofaces K L hdim hs ht hsc htc
          hKbound hLbound hKa hLb ℓ hst ha hb hx0 hxs hxt⟩
  · rw [if_neg (fun h => hx0 (hzero.mp h))] at hst
    have hxnonneg : 0 ≤ ℓ x := by
      have h := simplicialMap_nonneg_of_nonneg_vertices K ℓ hKnonneg hx.1
      have heq : simplicialMap K ℓ x = ℓ x := simplicialMap_eqOn_affine K ℓ.toAffineMap hx.1
      exact heq ▸ h
    exact Or.inr ⟨lt_of_le_of_ne hxnonneg (Ne.symm hx0),
      hasPLCrossingAt_of_transverse_face K L hK hL hdim hs ht hxs hxt hst⟩

def HasPLBoundaryDoubleCrossingAt (f : E → F) (P : Set E) (M : Set F) (y : F) : Prop :=
  ∃ (a b : E) (A B : Set E), a ∈ A ∧ b ∈ B ∧ f a = y ∧ f b = y ∧
    A ⊆ P ∧ B ⊆ P ∧ Disjoint A B ∧ A ∈ 𝓝[P] a ∧ B ∈ 𝓝[P] b ∧
      IsPLHomeomorphOn f A (f '' A) ∧ IsPLHomeomorphOn f B (f '' B) ∧
        HasPLBoundaryCrossingAt M (f '' A) (f '' B) y ∧ ∀ᶠ z in 𝓝 y, P ∩ f ⁻¹' {z} ⊆ A ∪ B

open Classical in
theorem neighbors_eq_pair_of_inter_in_halfSpace_of_notMem_boundary [FiniteDimensional ℝ E]
    (K L G : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces] [Finite G.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hdim : Module.finrank ℝ E = 3) (ℓ : E →ₗ[ℝ] ℝ)
    (hKnonneg : ∀ v ∈ K.vertices, 0 ≤ ℓ v) (hLnonneg : ∀ v ∈ L.vertices, 0 ≤ ℓ v)
    (hKboundary : ∀ s ∈ K.faces, 2 ≤ s.card → (∀ v ∈ s, ℓ v = 0) → s ∈ (boundaryComplex 2 K).faces)
    (hLboundary : ∀ t ∈ L.faces, 2 ≤ t.card → (∀ v ∈ t, ℓ v = 0) → t ∈ (boundaryComplex 2 L).faces)
    (hcard : ∀ u ∈ G.faces, u.card ≤ 2) (hspace : G.space = K.space ∩ L.space)
    (hcarrier : ∀ u ∈ G.faces, ∃ s ∈ K.faces, ∃ t ∈ L.faces,
      convexHull ℝ (u : Set E) ⊆ convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E))
    (htrans : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      (convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty →
        vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) =
          if ∀ v ∈ s ∪ t, ℓ v = 0 then LinearMap.ker ℓ else ⊤)
    {x : E} (hxG : {x} ∈ G.faces) (hxK : x ∉ (boundaryComplex 2 K).space)
    (hxL : x ∉ (boundaryComplex 2 L).space) :
    ∃ a b, a ≠ b ∧ {y | y ≠ x ∧ {x, y} ∈ G.faces} = {a, b} := by
  have hx : x ∈ K.space ∩ L.space := hspace ▸ G.subset_space hxG (Finset.mem_singleton_self x)
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex K hx.1
  obtain ⟨t, ht, hxt⟩ := exists_face_mem_openSimplex L hx.2
  have hinter : (convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty :=
    ⟨x, openSimplex_subset_convexHull s hxs, openSimplex_subset_convexHull t hxt⟩
  have hst := htrans s hs t ht hinter
  by_cases hzero : ∀ v ∈ s ∪ t, ℓ v = 0
  · rw [if_pos hzero] at hst
    have hszero : ∀ v ∈ s, ℓ v = 0 := fun v hv => hzero v (Finset.mem_union_left t hv)
    have htzero : ∀ v ∈ t, ℓ v = 0 := fun v hv => hzero v (Finset.mem_union_right s hv)
    obtain ⟨a, b, hsc, _, _, _, _, _⟩ := exists_unique_cofaces_of_transverse_boundary_faces
      K L hK hL hdim ℓ hKnonneg hLnonneg hKboundary hLboundary hs ht hszero htzero hinter hst
    exact (hxK ((boundaryComplex 2 K).convexHull_subset_space (hKboundary s hs hsc.ge hszero)
      (openSimplex_subset_convexHull s hxs))).elim
  · rw [if_neg hzero] at hst
    exact neighbors_eq_pair_of_transverse_face K L G hK hL hdim hcard hspace hcarrier hs ht hxs hxt hxG hst hxK hxL

open Classical in
theorem neighbors_eq_pair_of_eventually_eq [FiniteDimensional ℝ E]
    (G H : Geometry.SimplicialComplex ℝ E) [Finite G.faces] [Finite H.faces]
    (hGcard : ∀ s ∈ G.faces, s.card ≤ 2) (hHcard : ∀ s ∈ H.faces, s.card ≤ 2)
    {x : E} (hxG : {x} ∈ G.faces) (hxH : {x} ∈ H.faces)
    (heq : ∀ᶠ y in 𝓝 x, y ∈ G.space ↔ y ∈ H.space)
    (hpair : ∃ a b, a ≠ b ∧ {y | y ≠ x ∧ {x, y} ∈ H.faces} = {a, b}) :
    ∃ a b, a ≠ b ∧ {y | y ≠ x ∧ {x, y} ∈ G.faces} = {a, b} := by
  obtain ⟨f, hf⟩ := exists_isPLHomeomorphOn_geometricLink_of_eventually_eq_of_card_le_two G H hGcard hxG hxH heq
  have hH : IsPLSphere 0 (SimplicialComplex.geometricLink H {x}).space := by
    rw [geometricLink_space_eq_neighbors_of_card_le H hHcard x]
    exact isPLSphere_zero_iff.mpr hpair
  have hG := hH.of_isPLHomeomorphOn hf.symm
  rw [geometricLink_space_eq_neighbors_of_card_le G hGcard x] at hG
  exact isPLSphere_zero_iff.mp hG

open Classical in
theorem exists_local_intersection_with_crossings_and_degrees_at_doublePoint_in_halfSpace [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hdim : Module.finrank ℝ F = 3)
    (φ : E → F) (ℓ : F →ₗ[ℝ] ℝ)
    (hind : ∀ s ∈ K.faces, AffineIndependent ℝ (fun v : s => φ (v : E)))
    (hinj : ∀ v ∈ K.vertices, InjOn (simplicialMap K φ) (starComplex K v).space)
    (hcard : ∀ y : F, (K.space ∩ (simplicialMap K φ) ⁻¹' {y}).encard ≤ 2)
    (hnonneg : ∀ v ∈ K.vertices, 0 ≤ ℓ (φ v))
    (hboundary : ∀ s ∈ K.faces, (∀ v ∈ s, ℓ (φ v) = 0) → s ∈ (boundaryComplex 2 K).faces)
    (htrans : ∀ s ∈ K.faces, ∀ t ∈ K.faces, Disjoint s t →
      (convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t.image φ : Set F)).Nonempty →
        vectorSpan ℝ (s.image φ : Set F) ⊔ vectorSpan ℝ (t.image φ : Set F) =
          if ∀ v ∈ s ∪ t, ℓ (φ v) = 0 then LinearMap.ker ℓ else ⊤)
    {y : F} (hy : y ∈ doublePointSet (simplicialMap K φ) K.space) :
    (
    ((ℓ y = 0 ∧ HasPLBoundaryDoubleCrossingAt (simplicialMap K φ) K.space {z : F | 0 ≤ ℓ z} y ∧
      ∃ w : F, ℓ w = 1 ∧ ∀ᶠ z in 𝓝 y,
        z ∈ doublePointSet (simplicialMap K φ) K.space ↔ ∃ r : ℝ, 0 ≤ r ∧ z = y + r • w) ∨
      (0 < ℓ y ∧ HasPLDoubleCrossingAt (simplicialMap K φ) K.space y)) ∧
    ∃ H : Geometry.SimplicialComplex ℝ F, H.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 1 H ∧ y ∈ H.space ∧
        (∀ᶠ z in 𝓝 y, z ∈ doublePointSet (simplicialMap K φ) K.space ↔ z ∈ H.space) ∧
          ∀ z, {z} ∈ H.faces → ℓ z = 0 → ∃ a, {w | w ≠ z ∧ {z, w} ∈ H.faces} = {a}
    ) ∧ (y ∉ simplicialMap K φ '' (boundaryComplex 2 K).space →
      ∃ R : Geometry.SimplicialComplex ℝ F, R.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 1 R ∧
        {y} ∈ R.faces ∧ (∃ a b, a ≠ b ∧ {z | z ≠ y ∧ {y, z} ∈ R.faces} = {a, b}) ∧
          ∀ᶠ z in 𝓝 y, z ∈ doublePointSet (simplicialMap K φ) K.space ↔ z ∈ R.space) := by
  let f := simplicialMap K φ
  obtain ⟨a, ha, b, hb, hab, hfa, hfb⟩ := hy
  obtain ⟨s, hs, has⟩ := exists_face_mem_openSimplex K ha
  obtain ⟨t, ht, hbt⟩ := exists_face_mem_openSimplex K hb
  let S := faceStarComplex K s
  let T := faceStarComplex K t
  have hSK : S.faces ⊆ K.faces := faceStarComplex_faces_subset K s
  have hTK : T.faces ⊆ K.faces := faceStarComplex_faces_subset K t
  have : Finite S.faces := (faceStarComplex_faces_finite K s).to_subtype
  have : Finite T.faces := (faceStarComplex_faces_finite K t).to_subtype
  have hdisj : ∀ u ∈ S.faces, ∀ v ∈ T.faces, Disjoint u v :=
    disjoint_faceStarComplex_faces_of_eq_of_injOn_starComplex K f hinj
      (openSimplex_subset_convexHull s has) (openSimplex_subset_convexHull t hbt) hab (hfa.trans hfb.symm)
  have hST : Disjoint S.space T.space := disjoint_spaces_of_disjoint_faces K S T hSK hTK hdisj
  have hinjS : InjOn f S.space := by
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs
    have hvK := K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    exact (hinj v hvK).mono (space_mono_of_faces_subset (faceStarComplex_faces_subset_starComplex K hv))
  have hinjT : InjOn f T.space := by
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces ht
    have hvK := K.down_closed ht (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    exact (hinj v hvK).mono (space_mono_of_faces_subset (faceStarComplex_faces_subset_starComplex K hv))
  obtain ⟨M, hMfinite, hMspace, hMPL, hMfaces⟩ :=
    exists_simplicialImage_of_faces_subset K S hSK φ (fun u hu => hind u (hSK hu)) hinjS
  obtain ⟨N, hNfinite, hNspace, hNPL, hNfaces⟩ :=
    exists_simplicialImage_of_faces_subset K T hTK φ (fun u hu => hind u (hTK hu)) hinjT
  have : Finite M.faces := hMfinite.to_subtype
  have : Finite N.faces := hNfinite.to_subtype
  have hSball : IsPLBall 2 S.space := hK.isPLBall_faceStarComplex K hs
  have hTball : IsPLBall 2 T.space := hK.isPLBall_faceStarComplex K ht
  have hMman : IsCombinatorialManifoldWithBoundary 2 M :=
    hSball.isCombinatorialManifoldWithBoundary.of_isPLHomeomorphOn hMPL
  have hNman : IsCombinatorialManifoldWithBoundary 2 N :=
    hTball.isCombinatorialManifoldWithBoundary.of_isPLHomeomorphOn hNPL
  have hnonnegImage : ∀ (P : Geometry.SimplicialComplex ℝ E) (Q : Geometry.SimplicialComplex ℝ F),
      P.faces ⊆ K.faces → (∀ u ∈ Q.faces, ∃ v ∈ P.faces, u = v.image φ) →
        ∀ w ∈ Q.vertices, 0 ≤ ℓ w := by
    intro P Q hPK hQfaces w hw
    obtain ⟨u, hu, heq⟩ := hQfaces {w} hw
    have hwmem : w ∈ u.image φ := heq ▸ Finset.mem_singleton_self w
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hwmem
    exact hnonneg v (K.down_closed (hPK hu) (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v))
  have htransMN : ∀ u ∈ M.faces, ∀ v ∈ N.faces,
      (convexHull ℝ (u : Set F) ∩ convexHull ℝ (v : Set F)).Nonempty →
        vectorSpan ℝ (u : Set F) ⊔ vectorSpan ℝ (v : Set F) =
          if ∀ w ∈ u ∪ v, ℓ w = 0 then LinearMap.ker ℓ else ⊤ := by
    intro u hu v hv hinter
    obtain ⟨u', hu', rfl⟩ := hMfaces u hu
    obtain ⟨v', hv', rfl⟩ := hNfaces v hv
    have h := htrans u' (hSK hu') v' (hTK hv') (hdisj u' hu' v' hv') hinter
    simpa only [← Finset.image_union, Finset.forall_mem_image] using h
  obtain ⟨H, hHfinite, hHspace, hHman, hHboundary⟩ :=
    exists_isCombinatorialManifoldWithBoundary_inter_in_halfSpace_of_boundary_edges M N hMman hNman
      hdim ℓ (hnonnegImage S M hSK hMfaces) (hnonnegImage T N hTK hNfaces)
      (boundary_faces_of_simplicialImage_of_faces_subset K S M hK hSball hSK φ ℓ hMPL hMfaces hboundary)
      (boundary_faces_of_simplicialImage_of_faces_subset K T N hK hTball hTK φ ℓ hNPL hNfaces hboundary) htransMN
  have haS : a ∈ S.space := S.convexHull_subset_space
    ⟨hs, by rwa [Finset.union_self]⟩ (openSimplex_subset_convexHull s has)
  have hbT : b ∈ T.space := T.convexHull_subset_space
    ⟨ht, by rwa [Finset.union_self]⟩ (openSimplex_subset_convexHull t hbt)
  have hyMN : y ∈ M.space ∩ N.space := by
    rw [hMspace, hNspace]
    exact ⟨⟨a, haS, hfa⟩, ⟨b, hbT, hfb⟩⟩
  have hSneigh : S.space ∈ 𝓝[K.space] a := by
    rw [faceStarComplex_space K hs has]
    exact closedStar_mem_nhdsWithin K a
  have hTneigh : T.space ∈ 𝓝[K.space] b := by
    rw [faceStarComplex_space K ht hbt]
    exact closedStar_mem_nhdsWithin K b
  have hfiber : K.space ∩ f ⁻¹' {y} = {a, b} :=
    fiber_eq_pair_of_encard_le_two f K.space ha hb hab hfa hfb (hcard y)
  have hcover : ∀ᶠ z in 𝓝 y, K.space ∩ f ⁻¹' {z} ⊆ S.space ∪ T.space :=
    eventually_preimage_subset_union_of_fiber_eq_pair f (isPolyhedron_space K).isCompact
      (isPiecewiseAffineOn_simplicialMap K φ).continuousOn hfiber hSneigh hTneigh
  have hcross := hasPLCrossingAt_or_hasPLBoundaryCrossingAt_of_transverse_faces M N hMman hNman hdim ℓ
    (hnonnegImage S M hSK hMfaces) (hnonnegImage T N hTK hNfaces)
    (boundary_faces_of_simplicialImage_of_faces_subset K S M hK hSball hSK φ ℓ hMPL hMfaces hboundary)
    (boundary_faces_of_simplicialImage_of_faces_subset K T N hK hTball hTK φ ℓ hNPL hNfaces hboundary) htransMN hyMN
  rw [hMspace, hNspace] at hcross
  have hMPL' : IsPLHomeomorphOn f S.space (f '' S.space) := by rwa [hMspace] at hMPL
  have hNPL' : IsPLHomeomorphOn f T.space (f '' T.space) := by rwa [hNspace] at hNPL
  refine ⟨⟨?_, H, hHfinite, hHman, hHspace.symm ▸ hyMN, ?_, hHboundary⟩, ?_⟩
  · rcases hcross with ⟨hy0, hboundaryCross, w, hw, hray⟩ | ⟨hypos, hinteriorCross⟩
    · refine Or.inl ⟨hy0, ⟨a, b, S.space, T.space, haS, hbT, hfa, hfb,
        space_mono_of_faces_subset hSK, space_mono_of_faces_subset hTK, hST, hSneigh, hTneigh,
        hMPL', hNPL', hboundaryCross, hcover⟩, w, hw, ?_⟩
      filter_upwards [hcover, hray] with z hz hzr
      exact (mem_doublePointSet_iff_mem_image_inter_of_injOn f (space_mono_of_faces_subset hSK)
        (space_mono_of_faces_subset hTK) hST hinjS hinjT hz).trans hzr
    · exact Or.inr ⟨hypos, a, b, S.space, T.space, haS, hbT, hfa, hfb,
        space_mono_of_faces_subset hSK, space_mono_of_faces_subset hTK, hST, hSneigh, hTneigh,
        hMPL', hNPL', hinteriorCross, hcover⟩
  · filter_upwards [hcover] with z hz
    rw [hHspace, hMspace, hNspace]
    exact mem_doublePointSet_iff_mem_image_inter_of_injOn f (space_mono_of_faces_subset hSK)
      (space_mono_of_faces_subset hTK) hST hinjS hinjT hz
  · intro hyB
    have haSnotB : a ∉ (boundaryComplex 2 S).space := by
      intro haB
      exact hyB ⟨a, (mem_boundaryComplex_faceStarComplex_space_iff K hK hs has).mp haB, hfa⟩
    have hbTnotB : b ∉ (boundaryComplex 2 T).space := by
      intro hbB
      exact hyB ⟨b, (mem_boundaryComplex_faceStarComplex_space_iff K hK ht hbt).mp hbB, hfb⟩
    have hyMnotB : y ∉ (boundaryComplex 2 M).space := by
      intro hyM
      rw [boundaryComplex_space_of_isPLHomeomorphOn_of_isPLBall S M hSball hMPL] at hyM
      obtain ⟨c, hc, hcy⟩ := hyM
      have hca : c = a := hinjS (boundaryComplex_space_subset 2 S hc) haS (hcy.trans hfa.symm)
      exact haSnotB (hca ▸ hc)
    have hyNnotB : y ∉ (boundaryComplex 2 N).space := by
      intro hyN
      rw [boundaryComplex_space_of_isPLHomeomorphOn_of_isPLBall T N hTball hNPL] at hyN
      obtain ⟨c, hc, hcy⟩ := hyN
      have hcb : c = b := hinjT (boundaryComplex_space_subset 2 T hc) hbT (hcy.trans hfb.symm)
      exact hbTnotB (hcb ▸ hc)
    obtain ⟨J, hJfinite, hJspace, hJcarrier⟩ := exists_triangulation_inter M N
    have : Finite J.faces := hJfinite.to_subtype
    obtain ⟨R, hRJ, hRfinite, hyR⟩ := exists_isSubdivision_singleton_mem J (hJspace.symm ▸ hyMN)
    have : Finite R.faces := hRfinite.to_subtype
    have hRspace : R.space = M.space ∩ N.space := hRJ.space_eq.trans hJspace
    have hRcarrier : ∀ u ∈ R.faces, ∃ p ∈ M.faces, ∃ q ∈ N.faces,
        convexHull ℝ (u : Set F) ⊆ convexHull ℝ (p : Set F) ∩ convexHull ℝ (q : Set F) := by
      intro u hu
      obtain ⟨v, hv, huv⟩ := hRJ.exists_face_subset hu
      obtain ⟨p, hp, q, hq, hpq⟩ := hJcarrier v hv
      exact ⟨p, hp, q, hq, huv.trans hpq⟩
    obtain ⟨hRman, _⟩ := isCombinatorialManifoldWithBoundary_inter_in_halfSpace_of_boundary_edges M N R
      hMman hNman hdim ℓ (hnonnegImage S M hSK hMfaces) (hnonnegImage T N hTK hNfaces)
      (boundary_faces_of_simplicialImage_of_faces_subset K S M hK hSball hSK φ ℓ hMPL hMfaces hboundary)
      (boundary_faces_of_simplicialImage_of_faces_subset K T N hK hTball hTK φ ℓ hNPL hNfaces hboundary)
      hRspace hRcarrier htransMN
    have hRpair := neighbors_eq_pair_of_inter_in_halfSpace_of_notMem_boundary M N R hMman hNman hdim ℓ
      (hnonnegImage S M hSK hMfaces) (hnonnegImage T N hTK hNfaces)
      (boundary_faces_of_simplicialImage_of_faces_subset K S M hK hSball hSK φ ℓ hMPL hMfaces hboundary)
      (boundary_faces_of_simplicialImage_of_faces_subset K T N hK hTball hTK φ ℓ hNPL hNfaces hboundary)
      (fun u hu => hRman.card_le R hu) hRspace hRcarrier htransMN hyR hyMnotB hyNnotB
    refine ⟨R, hRfinite, hRman, hyR, hRpair, ?_⟩
    filter_upwards [hcover] with z hz
    rw [hRspace, hMspace, hNspace]
    exact mem_doublePointSet_iff_mem_image_inter_of_injOn f (space_mono_of_faces_subset hSK)
      (space_mono_of_faces_subset hTK) hST hinjS hinjT hz

open Classical in
theorem exists_local_intersection_with_crossings_at_doublePoint_in_halfSpace [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hdim : Module.finrank ℝ F = 3)
    (φ : E → F) (ℓ : F →ₗ[ℝ] ℝ)
    (hind : ∀ s ∈ K.faces, AffineIndependent ℝ (fun v : s => φ (v : E)))
    (hinj : ∀ v ∈ K.vertices, InjOn (simplicialMap K φ) (starComplex K v).space)
    (hcard : ∀ y : F, (K.space ∩ (simplicialMap K φ) ⁻¹' {y}).encard ≤ 2)
    (hnonneg : ∀ v ∈ K.vertices, 0 ≤ ℓ (φ v))
    (hboundary : ∀ s ∈ K.faces, (∀ v ∈ s, ℓ (φ v) = 0) → s ∈ (boundaryComplex 2 K).faces)
    (htrans : ∀ s ∈ K.faces, ∀ t ∈ K.faces, Disjoint s t →
      (convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t.image φ : Set F)).Nonempty →
        vectorSpan ℝ (s.image φ : Set F) ⊔ vectorSpan ℝ (t.image φ : Set F) =
          if ∀ v ∈ s ∪ t, ℓ (φ v) = 0 then LinearMap.ker ℓ else ⊤)
    {y : F} (hy : y ∈ doublePointSet (simplicialMap K φ) K.space) :
    ((ℓ y = 0 ∧ HasPLBoundaryDoubleCrossingAt (simplicialMap K φ) K.space {z : F | 0 ≤ ℓ z} y ∧
      ∃ w : F, ℓ w = 1 ∧ ∀ᶠ z in 𝓝 y,
        z ∈ doublePointSet (simplicialMap K φ) K.space ↔ ∃ r : ℝ, 0 ≤ r ∧ z = y + r • w) ∨
      (0 < ℓ y ∧ HasPLDoubleCrossingAt (simplicialMap K φ) K.space y)) ∧
    ∃ H : Geometry.SimplicialComplex ℝ F, H.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 1 H ∧ y ∈ H.space ∧
        (∀ᶠ z in 𝓝 y, z ∈ doublePointSet (simplicialMap K φ) K.space ↔ z ∈ H.space) ∧
          ∀ z, {z} ∈ H.faces → ℓ z = 0 → ∃ a, {w | w ≠ z ∧ {z, w} ∈ H.faces} = {a} := by
  exact (exists_local_intersection_with_crossings_and_degrees_at_doublePoint_in_halfSpace K hK hdim φ ℓ
    hind hinj hcard hnonneg hboundary htrans hy).1

open Classical in
theorem exists_local_intersection_at_doublePoint_in_halfSpace [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hdim : Module.finrank ℝ F = 3)
    (φ : E → F) (ℓ : F →ₗ[ℝ] ℝ)
    (hind : ∀ s ∈ K.faces, AffineIndependent ℝ (fun v : s => φ (v : E)))
    (hinj : ∀ v ∈ K.vertices, InjOn (simplicialMap K φ) (starComplex K v).space)
    (hcard : ∀ y : F, (K.space ∩ (simplicialMap K φ) ⁻¹' {y}).encard ≤ 2)
    (hnonneg : ∀ v ∈ K.vertices, 0 ≤ ℓ (φ v))
    (hboundary : ∀ s ∈ K.faces, (∀ v ∈ s, ℓ (φ v) = 0) → s ∈ (boundaryComplex 2 K).faces)
    (htrans : ∀ s ∈ K.faces, ∀ t ∈ K.faces, Disjoint s t →
      (convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t.image φ : Set F)).Nonempty →
        vectorSpan ℝ (s.image φ : Set F) ⊔ vectorSpan ℝ (t.image φ : Set F) =
          if ∀ v ∈ s ∪ t, ℓ (φ v) = 0 then LinearMap.ker ℓ else ⊤)
    {y : F} (hy : y ∈ doublePointSet (simplicialMap K φ) K.space) :
    ∃ H : Geometry.SimplicialComplex ℝ F, H.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 1 H ∧ y ∈ H.space ∧
        (∀ᶠ z in 𝓝 y, z ∈ doublePointSet (simplicialMap K φ) K.space ↔ z ∈ H.space) ∧
          ∀ z, {z} ∈ H.faces → ℓ z = 0 → ∃ a, {w | w ≠ z ∧ {z, w} ∈ H.faces} = {a} := by
  exact (exists_local_intersection_with_crossings_at_doublePoint_in_halfSpace K hK hdim φ ℓ hind hinj
    hcard hnonneg hboundary htrans hy).2

open Classical in
theorem exists_triangulation_doublePointSet_card_le_two_in_halfSpace [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hdim : Module.finrank ℝ F = 3)
    (φ : E → F) (ℓ : F →ₗ[ℝ] ℝ)
    (hind : ∀ s ∈ K.faces, AffineIndependent ℝ (fun v : s => φ (v : E)))
    (hinj : ∀ v ∈ K.vertices, InjOn (simplicialMap K φ) (starComplex K v).space)
    (hboundary : ∀ s ∈ K.faces, (∀ v ∈ s, ℓ (φ v) = 0) → s ∈ (boundaryComplex 2 K).faces)
    (htrans : ∀ s ∈ K.faces, ∀ t ∈ K.faces, Disjoint s t →
      (convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t.image φ : Set F)).Nonempty →
        vectorSpan ℝ (s.image φ : Set F) ⊔ vectorSpan ℝ (t.image φ : Set F) =
          if ∀ v ∈ s ∪ t, ℓ (φ v) = 0 then LinearMap.ker ℓ else ⊤) :
    ∃ G : Geometry.SimplicialComplex ℝ F, G.faces.Finite ∧
      G.space = doublePointSet (simplicialMap K φ) K.space ∧ (∀ u ∈ G.faces, u.card ≤ 2) ∧
        ∀ u ∈ G.faces, ∃ s ∈ K.faces, ∃ t ∈ K.faces, Disjoint s t ∧
          convexHull ℝ (u : Set F) ⊆
            convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t.image φ : Set F) := by
  obtain ⟨G, hfinite, hspace, hcarrier⟩ := exists_triangulation_doublePointSet_finrank_sup_le K φ hind hinj
  have hker : 2 ≤ Module.finrank ℝ (LinearMap.ker ℓ) := by
    have h := LinearMap.finrank_range_add_finrank_ker ℓ
    have hrange : Module.finrank ℝ (LinearMap.range ℓ) ≤ 1 := by
      simpa using Submodule.finrank_le (LinearMap.range ℓ)
    omega
  refine ⟨G, hfinite, hspace, ?_, ?_⟩
  · intro u hu
    obtain ⟨s, hs, t, ht, hdisj, hsub, hbound⟩ := hcarrier u hu
    obtain ⟨y, hy⟩ := G.nonempty_of_mem_faces hu
    have hst := htrans s hs t ht hdisj ⟨y, hsub (subset_convexHull ℝ _ hy)⟩
    by_cases hzero : ∀ v ∈ s ∪ t, ℓ (φ v) = 0
    · rw [if_pos hzero] at hst
      rw [hst] at hbound
      have hsbound := ((hK.mem_boundaryComplex_faces_iff K).mp
        (hboundary s hs (fun v hv => hzero v (Finset.mem_union_left t hv)))).2.1
      have htbound := ((hK.mem_boundaryComplex_faces_iff K).mp
        (hboundary t ht (fun v hv => hzero v (Finset.mem_union_right s hv)))).2.1
      omega
    · rw [if_neg hzero] at hst
      rw [hst, finrank_top, hdim] at hbound
      have hsbound := hK.card_le K hs
      have htbound := hK.card_le K ht
      omega
  · intro u hu
    obtain ⟨s, hs, t, ht, hdisj, hsub, _⟩ := hcarrier u hu
    exact ⟨s, hs, t, ht, hdisj, hsub⟩

open Classical in
theorem exists_isCombinatorialManifoldWithBoundary_doublePointSet_with_degrees_in_halfSpace [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hdim : Module.finrank ℝ F = 3)
    (φ : E → F) (ℓ : F →ₗ[ℝ] ℝ)
    (hind : ∀ s ∈ K.faces, AffineIndependent ℝ (fun v : s => φ (v : E)))
    (hinj : ∀ v ∈ K.vertices, InjOn (simplicialMap K φ) (starComplex K v).space)
    (hcard : ∀ y : F, (K.space ∩ (simplicialMap K φ) ⁻¹' {y}).encard ≤ 2)
    (hnonneg : ∀ v ∈ K.vertices, 0 ≤ ℓ (φ v))
    (hboundary : ∀ s ∈ K.faces, (∀ v ∈ s, ℓ (φ v) = 0) → s ∈ (boundaryComplex 2 K).faces)
    (htrans : ∀ s ∈ K.faces, ∀ t ∈ K.faces, Disjoint s t →
      (convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t.image φ : Set F)).Nonempty →
        vectorSpan ℝ (s.image φ : Set F) ⊔ vectorSpan ℝ (t.image φ : Set F) =
          if ∀ v ∈ s ∪ t, ℓ (φ v) = 0 then LinearMap.ker ℓ else ⊤) :
    ∃ G : Geometry.SimplicialComplex ℝ F, G.faces.Finite ∧
      G.space = doublePointSet (simplicialMap K φ) K.space ∧ IsCombinatorialManifoldWithBoundary 1 G ∧
        (∀ y ∈ G.space,
          (ℓ y = 0 ∧ HasPLBoundaryDoubleCrossingAt (simplicialMap K φ) K.space {z : F | 0 ≤ ℓ z} y) ∨
          (0 < ℓ y ∧ HasPLDoubleCrossingAt (simplicialMap K φ) K.space y)) ∧
            (∀ y, {y} ∈ G.faces → ℓ y = 0 → ∃ a, {z | z ≠ y ∧ {y, z} ∈ G.faces} = {a}) ∧
              ∀ y, {y} ∈ G.faces → y ∉ simplicialMap K φ '' (boundaryComplex 2 K).space →
                ∃ a b, a ≠ b ∧ {z | z ≠ y ∧ {y, z} ∈ G.faces} = {a, b} := by
  obtain ⟨G, hfinite, hspace, hGcard, _⟩ :=
    exists_triangulation_doublePointSet_card_le_two_in_halfSpace K hK hdim φ ℓ hind hinj hboundary htrans
  have : Finite G.faces := hfinite.to_subtype
  have hlocal := fun (y : F) (hy : y ∈ doublePointSet (simplicialMap K φ) K.space) =>
    exists_local_intersection_with_crossings_and_degrees_at_doublePoint_in_halfSpace K hK hdim φ ℓ hind hinj
      hcard hnonneg hboundary htrans hy
  refine ⟨G, hfinite, hspace, isCombinatorialManifoldWithBoundary_one_of_locally_eq G hGcard ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨H, hHfinite, hHman, hyH, heq, _⟩ := (hlocal y (hspace ▸ hy)).1.2
    refine ⟨H, hHfinite, hHman, hyH, ?_⟩
    rwa [hspace]
  · intro y hy
    rcases (hlocal y (hspace ▸ hy)).1.1 with ⟨hy0, hcross, _⟩ | hcross
    · exact Or.inl ⟨hy0, hcross⟩
    · exact Or.inr hcross
  · intro y hy hy0
    have hyG : y ∈ G.space := G.subset_space hy (Finset.mem_singleton_self y)
    rcases (hlocal y (hspace ▸ hyG)).1.1 with ⟨_, _, w, hw, hray⟩ | ⟨hypos, _⟩
    · have hw0 : w ≠ 0 := by
        intro hzero
        rw [hzero, map_zero] at hw
        exact zero_ne_one hw
      apply neighbors_singleton_of_eventually_nonneg_ray G hGcard hy hw0
      rwa [hspace]
    · rw [hy0] at hypos
      exact (lt_irrefl 0 hypos).elim
  · intro y hy hyBoundary
    have hyG : y ∈ G.space := G.subset_space hy (Finset.mem_singleton_self y)
    obtain ⟨H, hHfinite, hHman, hyH, hpair, heq⟩ := (hlocal y (hspace ▸ hyG)).2 hyBoundary
    have : Finite H.faces := hHfinite.to_subtype
    apply neighbors_eq_pair_of_eventually_eq G H hGcard (fun s hs => hHman.card_le H hs)
      hy hyH _ hpair
    rwa [hspace]

open Classical in
theorem exists_isCombinatorialManifoldWithBoundary_doublePointSet_with_crossings_in_halfSpace [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hdim : Module.finrank ℝ F = 3)
    (φ : E → F) (ℓ : F →ₗ[ℝ] ℝ)
    (hind : ∀ s ∈ K.faces, AffineIndependent ℝ (fun v : s => φ (v : E)))
    (hinj : ∀ v ∈ K.vertices, InjOn (simplicialMap K φ) (starComplex K v).space)
    (hcard : ∀ y : F, (K.space ∩ (simplicialMap K φ) ⁻¹' {y}).encard ≤ 2)
    (hnonneg : ∀ v ∈ K.vertices, 0 ≤ ℓ (φ v))
    (hboundary : ∀ s ∈ K.faces, (∀ v ∈ s, ℓ (φ v) = 0) → s ∈ (boundaryComplex 2 K).faces)
    (htrans : ∀ s ∈ K.faces, ∀ t ∈ K.faces, Disjoint s t →
      (convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t.image φ : Set F)).Nonempty →
        vectorSpan ℝ (s.image φ : Set F) ⊔ vectorSpan ℝ (t.image φ : Set F) =
          if ∀ v ∈ s ∪ t, ℓ (φ v) = 0 then LinearMap.ker ℓ else ⊤) :
    ∃ G : Geometry.SimplicialComplex ℝ F, G.faces.Finite ∧
      G.space = doublePointSet (simplicialMap K φ) K.space ∧ IsCombinatorialManifoldWithBoundary 1 G ∧
        (∀ y ∈ G.space,
          (ℓ y = 0 ∧ HasPLBoundaryDoubleCrossingAt (simplicialMap K φ) K.space {z : F | 0 ≤ ℓ z} y) ∨
          (0 < ℓ y ∧ HasPLDoubleCrossingAt (simplicialMap K φ) K.space y)) ∧
            ∀ y, {y} ∈ G.faces → ℓ y = 0 → ∃ a, {z | z ≠ y ∧ {y, z} ∈ G.faces} = {a} := by
  obtain ⟨G, hfinite, hspace, hman, hcross, hdegree, _⟩ :=
    exists_isCombinatorialManifoldWithBoundary_doublePointSet_with_degrees_in_halfSpace K hK hdim φ ℓ
      hind hinj hcard hnonneg hboundary htrans
  exact ⟨G, hfinite, hspace, hman, hcross, hdegree⟩

open Classical in
theorem exists_isCombinatorialManifoldWithBoundary_doublePointSet_in_halfSpace [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hdim : Module.finrank ℝ F = 3)
    (φ : E → F) (ℓ : F →ₗ[ℝ] ℝ)
    (hind : ∀ s ∈ K.faces, AffineIndependent ℝ (fun v : s => φ (v : E)))
    (hinj : ∀ v ∈ K.vertices, InjOn (simplicialMap K φ) (starComplex K v).space)
    (hcard : ∀ y : F, (K.space ∩ (simplicialMap K φ) ⁻¹' {y}).encard ≤ 2)
    (hnonneg : ∀ v ∈ K.vertices, 0 ≤ ℓ (φ v))
    (hboundary : ∀ s ∈ K.faces, (∀ v ∈ s, ℓ (φ v) = 0) → s ∈ (boundaryComplex 2 K).faces)
    (htrans : ∀ s ∈ K.faces, ∀ t ∈ K.faces, Disjoint s t →
      (convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t.image φ : Set F)).Nonempty →
        vectorSpan ℝ (s.image φ : Set F) ⊔ vectorSpan ℝ (t.image φ : Set F) =
          if ∀ v ∈ s ∪ t, ℓ (φ v) = 0 then LinearMap.ker ℓ else ⊤) :
    ∃ G : Geometry.SimplicialComplex ℝ F, G.faces.Finite ∧
      G.space = doublePointSet (simplicialMap K φ) K.space ∧ IsCombinatorialManifoldWithBoundary 1 G := by
  obtain ⟨G, hfinite, hspace, hman, _, _⟩ :=
    exists_isCombinatorialManifoldWithBoundary_doublePointSet_with_crossings_in_halfSpace K hK hdim φ ℓ
      hind hinj hcard hnonneg hboundary htrans
  exact ⟨G, hfinite, hspace, hman⟩

open Classical in
theorem simplicialMap_indicator_compl_subcomplex_eq_zero_iff
    (K L : Geometry.SimplicialComplex ℝ E) (hLK : L.faces ⊆ K.faces) {x : E} (hx : x ∈ K.space) :
    simplicialMap (barycentricSubdivision K) (fun v => if v ∈ L.space then (0 : ℝ) else 1) x = 0 ↔
      x ∈ L.space := by
  let S := barycentricSubdivision K
  let c : Finset E → E := fun s => s.centroid ℝ id
  have hc : ∀ s ∈ K.faces, c s ∈ openSimplex s := centroid_mem_openSimplex_of_mem_faces K
  have hxS : x ∈ S.space := (barycentricSubdivision_isSubdivision K).space_eq.symm ▸ hx
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex S hxS
  obtain ⟨d, hd, hdne, rfl⟩ := (mem_derived_faces_iff K hc).mp hs
  obtain ⟨u, hu, htop⟩ := hd.exists_top hdne
  have hxu : x ∈ openSimplex u := mem_openSimplex_top K hc hd hu htop hxs
  rw [simplicialMap_eq_zero_iff_of_mem_openSimplex S _ hs (fun v _ => by split_ifs <;> norm_num) hxs]
  constructor
  · intro hzero
    have hcu : c u ∈ L.space := by
      have h := hzero (c u) (Finset.mem_image_of_mem c hu)
      simpa only [ite_eq_left_iff, one_ne_zero, imp_false, not_not] using h
    have huL : u ∈ L.faces := by
      by_contra hnot
      exact notMem_space_of_notMem_faces hLK (hd.mem_faces hu) hnot (hc u (hd.mem_faces hu)) hcu
    exact L.convexHull_subset_space huL (openSimplex_subset_convexHull u hxu)
  · intro hxL v hv
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hv
    have huL : u ∈ L.faces := by
      by_contra hnot
      exact notMem_space_of_notMem_faces hLK (hd.mem_faces hu) hnot hxu hxL
    have htL : t ∈ L.faces := L.down_closed huL (htop t ht) (K.nonempty_of_mem_faces (hd.mem_faces ht))
    rw [if_pos (L.convexHull_subset_space htL (openSimplex_subset_convexHull t (hc t (hd.mem_faces ht))))]
open Classical in
theorem exists_small_simplicialMap_in_halfSpace_of_subcomplex [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hLK : L.faces ⊆ K.faces) (ℓ : F →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (f : E → F)
    (hf : IsPiecewiseAffineOn f K.space) (hloc : IsLocallyInjective (K.space.domRestrict f))
    (hcard : ∀ y : F, (K.space ∩ f ⁻¹' {y}).encard ≤ 2)
    (hnonneg : ∀ x ∈ K.space, 0 ≤ ℓ (f x)) (hzero : ∀ x ∈ L.space, ℓ (f x) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (R : Geometry.SimplicialComplex ℝ E) (φ : E → F), IsSubdivision R K ∧ R.faces.Finite ∧
      IsPiecewiseAffineOn (simplicialMap R φ) K.space ∧
        (∀ x ∈ K.space, dist (simplicialMap R φ x) (f x) < ε) ∧
          (∀ v ∈ R.vertices, IsPLHomeomorphOn (simplicialMap R φ) (starComplex R v).space
            (simplicialMap R φ '' (starComplex R v).space)) ∧
              IsLocallyInjective (K.space.domRestrict (simplicialMap R φ)) ∧
                (∀ y : F, (K.space ∩ (simplicialMap R φ) ⁻¹' {y}).encard ≤ 2) ∧
                  (∀ x ∈ K.space, 0 ≤ ℓ (simplicialMap R φ x)) ∧
                    (∀ x ∈ K.space, ℓ (simplicialMap R φ x) = 0 ↔ x ∈ L.space) ∧
                      EqOn (simplicialMap R φ) f L.space := by
  let S := barycentricSubdivision K
  have hS : IsSubdivision S K := barycentricSubdivision_isSubdivision K
  have : Finite S.faces := inferInstanceAs (Finite (barycentricSubdivision K).faces)
  have hfS : IsPiecewiseAffineOn f S.space := by rwa [hS.space_eq]
  have hlocS : IsLocallyInjective (S.space.domRestrict f) := by rwa [hS.space_eq]
  have hcardS : ∀ y : F, (S.space ∩ f ⁻¹' {y}).encard ≤ 2 := by rwa [hS.space_eq]
  obtain ⟨R, δ, hRS, hfinite, heq, hδ, hstable⟩ :=
    exists_isSubdivision_stable_fiber_encard_le_two S f hfS hlocS hcardS
  have : Finite R.faces := hfinite.to_subtype
  have hR : IsSubdivision R K := hRS.trans hS
  have hVK : ∀ v ∈ R.vertices, v ∈ K.space := fun v hv =>
    hR.space_eq ▸ R.subset_space hv (Finset.mem_singleton_self v)
  let q : E → ℝ := simplicialMap S (fun v => if v ∈ L.space then 0 else 1)
  have hqzero : ∀ x ∈ K.space, q x = 0 ↔ x ∈ L.space :=
    fun _ hx => simplicialMap_indicator_compl_subcomplex_eq_zero_iff K L hLK hx
  have hqnonneg : ∀ x ∈ K.space, 0 ≤ q x := by
    intro x hx
    exact simplicialMap_nonneg_of_nonneg_vertices S _ (fun v _ => by split_ifs <;> norm_num)
      (hS.space_eq.symm ▸ hx)
  have hqR : EqOn (simplicialMap R q) q R.space := by
    apply simplicialMap_eq_of_forall_affineOn
    intro s hs
    obtain ⟨t, ht, hst⟩ := hRS.exists_face_subset hs
    obtain ⟨A, hA⟩ := exists_affineMap_eqOn_simplicialMap S (fun v => if v ∈ L.space then (0 : ℝ) else 1) ht
    exact ⟨A, hA.mono hst⟩
  obtain ⟨u, hu⟩ := DFunLike.ne_iff.mp hℓ
  rw [LinearMap.zero_apply] at hu
  let w : F := (ℓ u)⁻¹ • u
  have hw : ℓ w = 1 := by
    dsimp [w]
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hu]
  let η := min δ ε
  have hη : 0 < η := lt_min hδ hε
  let a : ℝ := η / (‖w‖ + 1)
  have ha : 0 < a := div_pos hη (by positivity)
  have habound : a * ‖w‖ < η := by
    have hmul : a * (‖w‖ + 1) = η := div_mul_cancel₀ _ (by positivity)
    nlinarith
  let φ : E → F := fun v => if v ∈ L.space then f v else f v + a • w
  have hcloseVertex : ∀ v, dist (φ v) (f v) < η := by
    intro v
    by_cases hv : v ∈ L.space
    · simpa only [φ, if_pos hv, dist_self] using hη
    · simpa only [φ, if_neg hv, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_pos ha] using habound
  have hφnonneg : ∀ v ∈ R.vertices, 0 ≤ ℓ (φ v) := by
    intro v hv
    by_cases hvL : v ∈ L.space
    · simp only [φ, if_pos hvL, hzero v hvL, le_refl]
    · simp only [φ, if_neg hvL, map_add, map_smul, smul_eq_mul, hw, mul_one]
      exact add_nonneg (hnonneg v (hVK v hv)) ha.le
  have hφzero : ∀ v ∈ R.vertices, ℓ (φ v) = 0 ↔ q v = 0 := by
    intro v hv
    rw [hqzero v (hVK v hv)]
    by_cases hvL : v ∈ L.space
    · simp only [φ, if_pos hvL, hzero v hvL, hvL]
    · have hpos : 0 < ℓ (f v) + a := add_pos_of_nonneg_of_pos (hnonneg v (hVK v hv)) ha
      simp only [φ, if_neg hvL, map_add, map_smul, smul_eq_mul, hw, mul_one, hpos.ne', hvL]
  obtain ⟨hstar, hlocal, hfiber⟩ := hstable φ (fun v _ => (hcloseVertex v).trans_le (min_le_left δ ε))
  refine ⟨R, φ, hR, hfinite, ?_, ?_, hstar, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hR.space_eq] using isPiecewiseAffineOn_simplicialMap R φ
  · intro x hx
    rw [← heq (hS.space_eq.symm ▸ hx)]
    exact dist_simplicialMap_lt_of_dist_vertices_lt R
      (fun v _ => (hcloseVertex v).trans_le (min_le_right δ ε)) (hR.space_eq.symm ▸ hx)
  · rwa [hR.space_eq] at hlocal
  · simpa only [hR.space_eq] using hfiber
  · intro x hx
    rw [linearMap_simplicialMap]
    exact simplicialMap_nonneg_of_nonneg_vertices R (ℓ ∘ φ) hφnonneg (hR.space_eq.symm ▸ hx)
  · intro x hx
    have hxR : x ∈ R.space := hR.space_eq.symm ▸ hx
    rw [linearMap_simplicialMap, simplicialMap_eq_zero_iff_of_eq_zero_on_vertices R (ℓ ∘ φ) q
      hφnonneg (fun v hv => hqnonneg v (hVK v hv)) hφzero hxR, hqR hxR]
    exact hqzero x hx
  · intro x hxL
    have hxK : x ∈ K.space := space_mono_of_faces_subset hLK hxL
    have hxR : x ∈ R.space := hR.space_eq.symm ▸ hxK
    obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex R hxR
    have hqs : ∀ v ∈ s, q v = 0 :=
      (simplicialMap_eq_zero_iff_of_mem_openSimplex R q hs
        (fun v hv => hqnonneg v (hVK v (R.down_closed hs (Finset.singleton_subset_iff.mpr hv)
          (Finset.singleton_nonempty v)))) hxs).mp ((hqR hxR).trans ((hqzero x hxK).mpr hxL))
    rw [← heq (hS.space_eq.symm ▸ hxK), simplicialMap_eq_of_mem R φ hs (openSimplex_subset_convexHull s hxs),
      simplicialMap_eq_of_mem R f hs (openSimplex_subset_convexHull s hxs)]
    apply Finset.sum_congr rfl
    intro v hv
    have hvL := (hqzero v (hVK v (R.down_closed hs (Finset.singleton_subset_iff.mpr hv)
      (Finset.singleton_nonempty v)))).mp (hqs v hv)
    rw [show φ v = f v by simp only [φ, if_pos hvL]]

open Classical in
theorem exists_small_simplicialMap_doublePointSet_normal_form_in_halfSpace_of_maps_boundary [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLBall 2 K.space) (hdim : Module.finrank ℝ F = 3) (ℓ : F →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (f : E → F) (hf : IsPiecewiseAffineOn f K.space) (hloc : IsLocallyInjective (K.space.domRestrict f))
    (hcard : ∀ y : F, (K.space ∩ f ⁻¹' {y}).encard ≤ 2)
    (hnonneg : ∀ x ∈ K.space, 0 ≤ ℓ (f x))
    (hboundary : ∀ x ∈ (boundaryComplex 2 K).space, ℓ (f x) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (R : Geometry.SimplicialComplex ℝ E) (φ : E → F) (G : Geometry.SimplicialComplex ℝ F),
      IsSubdivision R K ∧ R.faces.Finite ∧ IsPiecewiseAffineOn (simplicialMap R φ) K.space ∧
        (∀ x ∈ K.space, dist (simplicialMap R φ x) (f x) < ε) ∧
          (∀ v ∈ R.vertices, IsPLHomeomorphOn (simplicialMap R φ) (starComplex R v).space
            (simplicialMap R φ '' (starComplex R v).space)) ∧
              IsLocallyInjective (K.space.domRestrict (simplicialMap R φ)) ∧
                (∀ y : F, (K.space ∩ (simplicialMap R φ) ⁻¹' {y}).encard ≤ 2) ∧
                  (∀ x ∈ K.space, 0 ≤ ℓ (simplicialMap R φ x)) ∧
                    (∀ x ∈ K.space, ℓ (simplicialMap R φ x) = 0 ↔ x ∈ (boundaryComplex 2 K).space) ∧
                      G.faces.Finite ∧ G.space = doublePointSet (simplicialMap R φ) K.space ∧
                        IsCombinatorialManifoldWithBoundary 1 G ∧
                          (∀ y ∈ G.space,
                            (ℓ y = 0 ∧ HasPLBoundaryDoubleCrossingAt (simplicialMap R φ) K.space {z : F | 0 ≤ ℓ z} y) ∨
                            (0 < ℓ y ∧ HasPLDoubleCrossingAt (simplicialMap R φ) K.space y)) ∧
                              (∀ y, {y} ∈ G.faces → ℓ y = 0 → ∃ a, {z | z ≠ y ∧ {y, z} ∈ G.faces} = {a}) ∧
                                ∀ y, {y} ∈ G.faces → ℓ y ≠ 0 →
                                  ∃ a b, a ≠ b ∧ {z | z ≠ y ∧ {y, z} ∈ G.faces} = {a, b} := by
  obtain ⟨S, ψ, _, _, hg, hgclose, _, hglocal, hgfiber, hgnonneg, hgboundary, _⟩ :=
    exists_small_simplicialMap_in_halfSpace_of_subcomplex K (boundaryComplex 2 K)
      (boundaryComplex_faces_subset 2 K) ℓ hℓ f hf hloc hcard hnonneg hboundary (half_pos hε)
  obtain ⟨R, φ, hR, hfinite, hpl, hclose, hstar, hlocal, hfiber, hRnonneg, hRboundary, hind, htrans⟩ :=
    exists_small_simplicialMap_transverse_in_halfSpace K hK.isCombinatorialManifoldWithBoundary hdim
      ℓ hℓ (simplicialMap S ψ) hg hglocal hgfiber hgnonneg hgboundary (half_pos hε)
  have : Finite R.faces := hfinite.to_subtype
  have hRman : IsCombinatorialManifoldWithBoundary 2 R := hK.isCombinatorialManifoldWithBoundary.of_isSubdivision hR
  have hboundarySpace : (boundaryComplex 2 R).space = (boundaryComplex 2 K).space := by
    obtain ⟨g, hg⟩ := hK
    have hgR : IsPLHomeomorphOn g (stdSimplex ℝ (Fin 3)) R.space := by rwa [hR.space_eq]
    rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex R hgR,
      boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex K hg]
  have hVK : ∀ v ∈ R.vertices, v ∈ K.space := by
    intro v hv
    rw [← hR.space_eq]
    exact R.subset_space hv (Finset.mem_singleton_self v)
  have hφnonneg : ∀ v ∈ R.vertices, 0 ≤ ℓ (φ v) := by
    intro v hv
    rw [← simplicialMap_vertex R φ hv]
    exact hRnonneg v (hVK v hv)
  have hφboundary : ∀ v ∈ R.vertices, ℓ (φ v) = 0 ↔ v ∈ (boundaryComplex 2 K).space := by
    intro v hv
    rw [← simplicialMap_vertex R φ hv]
    exact hRboundary v (hVK v hv)
  have hboundaryFaces : ∀ s ∈ R.faces, (∀ v ∈ s, ℓ (φ v) = 0) → s ∈ (boundaryComplex 2 R).faces := by
    intro s hs hzero
    let x := s.centroid ℝ id
    have hx : x ∈ openSimplex s := centroid_mem_openSimplex (R.nonempty_of_mem_faces hs)
    have hxR : x ∈ R.space := R.convexHull_subset_space hs (openSimplex_subset_convexHull s hx)
    have hxzero : ℓ (simplicialMap R φ x) = 0 := by
      rw [linearMap_simplicialMap]
      exact (simplicialMap_eq_zero_iff_of_mem_openSimplex R (ℓ ∘ φ) hs
        (fun v hv => hφnonneg v (R.down_closed hs (Finset.singleton_subset_iff.mpr hv)
          (Finset.singleton_nonempty v))) hx).mpr hzero
    have hxB : x ∈ (boundaryComplex 2 R).space := by
      rw [hboundarySpace]
      exact (hRboundary x (hR.space_eq ▸ hxR)).mp hxzero
    by_contra hnot
    exact notMem_space_of_notMem_faces (boundaryComplex_faces_subset 2 R) hs hnot hx hxB
  have htrans' : ∀ s ∈ R.faces, ∀ t ∈ R.faces, Disjoint s t →
      (convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t.image φ : Set F)).Nonempty →
        vectorSpan ℝ (s.image φ : Set F) ⊔ vectorSpan ℝ (t.image φ : Set F) =
          if ∀ v ∈ s ∪ t, ℓ (φ v) = 0 then LinearMap.ker ℓ else ⊤ := by
    intro s hs t ht hdisj hinter
    have hvert : ∀ v ∈ s ∪ t, v ∈ R.vertices := by
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact R.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
      · exact R.down_closed ht (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    have heq : (((s ∪ t : Finset E) : Set E) ⊆ (boundaryComplex 2 K).space) ↔ ∀ v ∈ s ∪ t, ℓ (φ v) = 0 := by
      constructor
      · intro h v hv
        exact (hφboundary v (hvert v hv)).mpr (h hv)
      · intro h v hv
        exact (hφboundary v (hvert v hv)).mp (h v hv)
    simpa only [heq] using htrans s hs t ht hdisj hinter
  have hinj : ∀ v ∈ R.vertices, InjOn (simplicialMap R φ) (starComplex R v).space :=
    fun v hv => (hstar v hv).bijOn.injOn
  have hfiberR : ∀ y : F, (R.space ∩ (simplicialMap R φ) ⁻¹' {y}).encard ≤ 2 := by
    simpa only [hR.space_eq] using hfiber
  obtain ⟨G, hGfinite, hGspace, hGman, hcross, hdegree, hdegreeInterior⟩ := exists_isCombinatorialManifoldWithBoundary_doublePointSet_with_degrees_in_halfSpace
    R hRman hdim φ ℓ hind hinj hfiberR hφnonneg hboundaryFaces htrans'
  rw [hR.space_eq] at hGspace hcross
  have hclose' : ∀ x ∈ K.space, dist (simplicialMap R φ x) (f x) < ε := by
    intro x hx
    calc
      dist (simplicialMap R φ x) (f x) ≤
          dist (simplicialMap R φ x) (simplicialMap S ψ x) + dist (simplicialMap S ψ x) (f x) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hclose x hx) (hgclose x hx)
      _ = ε := add_halves ε
  refine ⟨R, φ, G, hR, hfinite, hpl, hclose', hstar, hlocal, hfiber, hRnonneg, hRboundary, hGfinite, hGspace, hGman, hcross, hdegree, ?_⟩
  intro y hy hy0
  apply hdegreeInterior y hy
  rintro ⟨x, hxBoundary, hxy⟩
  have hxK : x ∈ K.space := hR.space_eq ▸ boundaryComplex_space_subset 2 R hxBoundary
  have hx0 : ℓ (simplicialMap R φ x) = 0 := (hRboundary x hxK).mpr (hboundarySpace ▸ hxBoundary)
  exact hy0 (hxy ▸ hx0)

open Classical in
theorem exists_small_simplicialMap_doublePointSet_normal_form_in_halfSpace [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLBall 2 K.space) (hdim : Module.finrank ℝ F = 3) (ℓ : F →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (f : E → F) (hf : IsPiecewiseAffineOn f K.space) (hloc : IsLocallyInjective (K.space.domRestrict f))
    (hcard : ∀ y : F, (K.space ∩ f ⁻¹' {y}).encard ≤ 2)
    (hnonneg : ∀ x ∈ K.space, 0 ≤ ℓ (f x))
    (hboundary : ∀ x ∈ K.space, ℓ (f x) = 0 ↔ x ∈ (boundaryComplex 2 K).space)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (R : Geometry.SimplicialComplex ℝ E) (φ : E → F) (G : Geometry.SimplicialComplex ℝ F),
      IsSubdivision R K ∧ R.faces.Finite ∧ IsPiecewiseAffineOn (simplicialMap R φ) K.space ∧
        (∀ x ∈ K.space, dist (simplicialMap R φ x) (f x) < ε) ∧
          (∀ v ∈ R.vertices, IsPLHomeomorphOn (simplicialMap R φ) (starComplex R v).space
            (simplicialMap R φ '' (starComplex R v).space)) ∧
              IsLocallyInjective (K.space.domRestrict (simplicialMap R φ)) ∧
                (∀ y : F, (K.space ∩ (simplicialMap R φ) ⁻¹' {y}).encard ≤ 2) ∧
                  (∀ x ∈ K.space, 0 ≤ ℓ (simplicialMap R φ x)) ∧
                    (∀ x ∈ K.space, ℓ (simplicialMap R φ x) = 0 ↔ x ∈ (boundaryComplex 2 K).space) ∧
                      G.faces.Finite ∧ G.space = doublePointSet (simplicialMap R φ) K.space ∧
                        IsCombinatorialManifoldWithBoundary 1 G ∧
                          (∀ y ∈ G.space,
                            (ℓ y = 0 ∧ HasPLBoundaryDoubleCrossingAt (simplicialMap R φ) K.space {z : F | 0 ≤ ℓ z} y) ∨
                            (0 < ℓ y ∧ HasPLDoubleCrossingAt (simplicialMap R φ) K.space y)) ∧
                              (∀ y, {y} ∈ G.faces → ℓ y = 0 → ∃ a, {z | z ≠ y ∧ {y, z} ∈ G.faces} = {a}) ∧
                                ∀ y, {y} ∈ G.faces → ℓ y ≠ 0 →
                                  ∃ a b, a ≠ b ∧ {z | z ≠ y ∧ {y, z} ∈ G.faces} = {a, b} := by
  exact exists_small_simplicialMap_doublePointSet_normal_form_in_halfSpace_of_maps_boundary K hK hdim ℓ hℓ
    f hf hloc hcard hnonneg (fun x hx => (hboundary x (boundaryComplex_space_subset 2 K hx)).mpr hx) hε

open Classical in
theorem exists_small_simplicialMap_doublePointSet_with_crossings_in_halfSpace [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLBall 2 K.space) (hdim : Module.finrank ℝ F = 3) (ℓ : F →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (f : E → F) (hf : IsPiecewiseAffineOn f K.space) (hloc : IsLocallyInjective (K.space.domRestrict f))
    (hcard : ∀ y : F, (K.space ∩ f ⁻¹' {y}).encard ≤ 2)
    (hnonneg : ∀ x ∈ K.space, 0 ≤ ℓ (f x))
    (hboundary : ∀ x ∈ K.space, ℓ (f x) = 0 ↔ x ∈ (boundaryComplex 2 K).space)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (R : Geometry.SimplicialComplex ℝ E) (φ : E → F) (G : Geometry.SimplicialComplex ℝ F),
      IsSubdivision R K ∧ R.faces.Finite ∧ IsPiecewiseAffineOn (simplicialMap R φ) K.space ∧
        (∀ x ∈ K.space, dist (simplicialMap R φ x) (f x) < ε) ∧
          (∀ v ∈ R.vertices, IsPLHomeomorphOn (simplicialMap R φ) (starComplex R v).space
            (simplicialMap R φ '' (starComplex R v).space)) ∧
              IsLocallyInjective (K.space.domRestrict (simplicialMap R φ)) ∧
                (∀ y : F, (K.space ∩ (simplicialMap R φ) ⁻¹' {y}).encard ≤ 2) ∧
                  (∀ x ∈ K.space, 0 ≤ ℓ (simplicialMap R φ x)) ∧
                    (∀ x ∈ K.space, ℓ (simplicialMap R φ x) = 0 ↔ x ∈ (boundaryComplex 2 K).space) ∧
                      G.faces.Finite ∧ G.space = doublePointSet (simplicialMap R φ) K.space ∧
                        IsCombinatorialManifoldWithBoundary 1 G ∧
                          (∀ y ∈ G.space,
                            (ℓ y = 0 ∧ HasPLBoundaryDoubleCrossingAt (simplicialMap R φ) K.space {z : F | 0 ≤ ℓ z} y) ∨
                            (0 < ℓ y ∧ HasPLDoubleCrossingAt (simplicialMap R φ) K.space y)) ∧
                              ∀ y, {y} ∈ G.faces → ℓ y = 0 → ∃ a, {z | z ≠ y ∧ {y, z} ∈ G.faces} = {a} := by
  obtain ⟨R, φ, G, hR, hfinite, hpl, hclose, hstar, hlocal, hfiber, hnonneg', hboundary', hGfinite, hGspace, hGman, hcross, hdegree, _⟩ :=
    exists_small_simplicialMap_doublePointSet_normal_form_in_halfSpace K hK hdim ℓ hℓ f hf hloc hcard hnonneg hboundary hε
  exact ⟨R, φ, G, hR, hfinite, hpl, hclose, hstar, hlocal, hfiber, hnonneg', hboundary', hGfinite, hGspace, hGman, hcross, hdegree⟩

open Classical in
theorem exists_small_simplicialMap_doublePointSet_manifold_in_halfSpace [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLBall 2 K.space) (hdim : Module.finrank ℝ F = 3) (ℓ : F →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (f : E → F) (hf : IsPiecewiseAffineOn f K.space) (hloc : IsLocallyInjective (K.space.domRestrict f))
    (hcard : ∀ y : F, (K.space ∩ f ⁻¹' {y}).encard ≤ 2)
    (hnonneg : ∀ x ∈ K.space, 0 ≤ ℓ (f x))
    (hboundary : ∀ x ∈ K.space, ℓ (f x) = 0 ↔ x ∈ (boundaryComplex 2 K).space)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (R : Geometry.SimplicialComplex ℝ E) (φ : E → F) (G : Geometry.SimplicialComplex ℝ F),
      IsSubdivision R K ∧ R.faces.Finite ∧ IsPiecewiseAffineOn (simplicialMap R φ) K.space ∧
        (∀ x ∈ K.space, dist (simplicialMap R φ x) (f x) < ε) ∧
          (∀ v ∈ R.vertices, IsPLHomeomorphOn (simplicialMap R φ) (starComplex R v).space
            (simplicialMap R φ '' (starComplex R v).space)) ∧
              IsLocallyInjective (K.space.domRestrict (simplicialMap R φ)) ∧
                (∀ y : F, (K.space ∩ (simplicialMap R φ) ⁻¹' {y}).encard ≤ 2) ∧
                  (∀ x ∈ K.space, 0 ≤ ℓ (simplicialMap R φ x)) ∧
                    (∀ x ∈ K.space, ℓ (simplicialMap R φ x) = 0 ↔ x ∈ (boundaryComplex 2 K).space) ∧
                      G.faces.Finite ∧ G.space = doublePointSet (simplicialMap R φ) K.space ∧
                        IsCombinatorialManifoldWithBoundary 1 G := by
  obtain ⟨R, φ, G, hR, hfinite, hpl, hclose, hstar, hlocal, hfiber, hnonneg', hboundary', hGfinite, hGspace, hGman, _, _⟩ :=
    exists_small_simplicialMap_doublePointSet_with_crossings_in_halfSpace K hK hdim ℓ hℓ f hf hloc hcard hnonneg hboundary hε
  exact ⟨R, φ, G, hR, hfinite, hpl, hclose, hstar, hlocal, hfiber, hnonneg', hboundary', hGfinite, hGspace, hGman⟩

end DifferentialGeometry.Topology.PiecewiseLinear
