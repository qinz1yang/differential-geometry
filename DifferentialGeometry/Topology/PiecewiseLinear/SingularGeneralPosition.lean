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

end DifferentialGeometry.Topology.PiecewiseLinear
