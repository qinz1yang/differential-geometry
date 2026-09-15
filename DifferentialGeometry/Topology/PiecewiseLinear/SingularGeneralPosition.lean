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
theorem exists_small_affineIndependent_subsets [FiniteDimensional ℝ F] {ι : Type*}
    (V : Finset ι) (φ₀ : ι → F) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : ι → F, EqOn φ φ₀ (V : Set ι)ᶜ ∧ (∀ v, dist (φ v) (φ₀ v) < ε) ∧
      ∀ s : Finset ι, s ⊆ V → s.card ≤ Module.finrank ℝ F + 1 →
        AffineIndependent ℝ (fun v : s => φ (v : ι)) := by
  induction V using Finset.induction_on with
  | empty =>
    refine ⟨φ₀, fun _ _ => rfl, fun _ => by simpa only [dist_self] using hε, ?_⟩
    intro s hs _
    have hs0 : s = ∅ := Finset.subset_empty.mp hs
    subst s
    exact affineIndependent_of_subsingleton ℝ _
  | @insert v V hv ih =>
    obtain ⟨φ, hfix, hclose, hgood⟩ := ih
    let I := {s : Finset ι // s ⊆ V ∧ s.card ≤ Module.finrank ℝ F}
    have : Finite I := ((V.powerset.finite_toSet).subset
      (fun s hs => Finset.mem_powerset.mpr hs.1)).to_subtype
    let A : I → AffineSubspace ℝ F := fun s => affineSpan ℝ (s.val.image φ : Set F)
    have hA : ∀ s, A s ≠ ⊤ := by
      intro s htop
      have hs := ((affineIndependent_image_iff s.val φ).mp
        (hgood s.val s.property.1 (Nat.le_succ_of_le s.property.2))).2
      have hrange : range ((↑) : ↥(s.val.image φ : Set F) → F) = (s.val.image φ : Set F) := by
        ext y
        simp
      have htop' : affineSpan ℝ (range ((↑) : ↥(s.val.image φ : Set F) → F)) = ⊤ := by
        rwa [hrange]
      have hc := hs.affineSpan_eq_top_iff_card_eq_finrank_add_one.mp htop'
      rw [Fintype.card_coe] at hc
      have hle := (Finset.card_image_le (s := s.val) (f := φ)).trans s.property.2
      omega
    obtain ⟨p, hp, hpA⟩ := exists_mem_ball_notMem_affineSubspaces A hA (x := φ₀ v) hε
    let ψ := Function.update φ v p
    have hsame : ∀ w ≠ v, ψ w = φ w := fun w hw => Function.update_of_ne hw p φ
    have hψv : ψ v = p := Function.update_self v p φ
    refine ⟨ψ, ?_, ?_, ?_⟩
    · intro w hw
      have hwv : w ≠ v := fun heq => hw (heq ▸ Finset.mem_insert_self v V)
      exact (hsame w hwv).trans (hfix (fun hwV => hw (Finset.mem_insert_of_mem hwV)))
    · intro w
      by_cases hwv : w = v
      · rw [hwv, hψv]
        exact hp
      · rw [hsame w hwv]
        exact hclose w
    · intro s hs hcard
      by_cases hvs : v ∈ s
      · have hsub : s.erase v ⊆ V := by
          intro w hw
          exact (Finset.mem_insert.mp (hs (Finset.mem_of_mem_erase hw))).resolve_left
            (Finset.ne_of_mem_erase hw)
        have herase : (s.erase v).card ≤ Module.finrank ℝ F := by
          have h := Finset.card_erase_of_mem hvs
          omega
        have h := affineIndependent_update_insert (φ := φ) (Finset.notMem_erase v s)
          (hgood (s.erase v) hsub (Nat.le_succ_of_le herase)) (hpA ⟨s.erase v, hsub, herase⟩)
        rwa [Finset.insert_erase hvs] at h
      · have hsub : s ⊆ V := fun w hw =>
          (Finset.mem_insert.mp (hs hw)).resolve_left (ne_of_mem_of_not_mem hw hvs)
        have heq : (fun w : s => ψ (w : ι)) = (fun w : s => φ (w : ι)) :=
          funext fun w => hsame w (ne_of_mem_of_not_mem w.property hvs)
        rw [heq]
        exact hgood s hsub hcard

open Classical in
theorem vectorSpan_sup_eq_top_of_affineIndependent_subsets [FiniteDimensional ℝ F] {ι : Type*}
    (V : Finset ι) (φ : ι → F)
    (hφ : ∀ u : Finset ι, u ⊆ V → u.card ≤ Module.finrank ℝ F + 1 →
      AffineIndependent ℝ (fun v : u => φ (v : ι)))
    {s t : Finset ι} (hs : s ⊆ V) (ht : t ⊆ V) (hst : Disjoint s t)
    (hinter : (convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t.image φ : Set F)).Nonempty) :
    vectorSpan ℝ (s.image φ : Set F) ⊔ vectorSpan ℝ (t.image φ : Set F) = ⊤ := by
  have hsub : s ∪ t ⊆ V := Finset.union_subset hs ht
  by_cases hcard : (s ∪ t).card ≤ Module.finrank ℝ F + 1
  · have hAI := (affineIndependent_image_iff (s ∪ t) φ).mp (hφ _ hsub hcard)
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
  · obtain ⟨u, hu, hucard⟩ := Finset.exists_subset_card_eq
      (show Module.finrank ℝ F + 1 ≤ (s ∪ t).card by omega)
    have huAI := hφ u (hu.trans hsub) hucard.le
    have huSpan : affineSpan ℝ (u.image φ : Set F) = ⊤ := by
      have hrange : range (fun v : u => φ (v : ι)) = (u.image φ : Set F) := by ext y; simp
      rw [← hrange, huAI.affineSpan_eq_top_iff_card_eq_finrank_add_one, Fintype.card_coe]
      exact hucard
    have hspan : affineSpan ℝ ((s.image φ : Set F) ∪ (t.image φ : Set F)) = ⊤ := by
      apply top_unique
      rw [← huSpan]
      apply affineSpan_mono ℝ
      intro y hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
      rcases Finset.mem_union.mp (hu ha) with has | hat
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
  obtain ⟨G, hfinite, hspace, hcarrier⟩ := exists_triangulation_doublePointSet K φ hind hinj
  refine ⟨G, hfinite, hspace, fun u hu => ?_⟩
  obtain ⟨s, hs, t, ht, hdisj, hsub⟩ := hcarrier u hu
  have hsAI := (affineIndependent_image_iff s φ).mp (hind s hs)
  have htAI := (affineIndependent_image_iff t φ).mp (hind t ht)
  let S := simplexComplex (s.image φ) hsAI.2
  let T := simplexComplex (t.image φ) htAI.2
  have hsS : s.image φ ∈ S.faces := ⟨(K.nonempty_of_mem_faces hs).image φ, Finset.Subset.refl _⟩
  have htT : t.image φ ∈ T.faces := ⟨(K.nonempty_of_mem_faces ht).image φ, Finset.Subset.refl _⟩
  obtain ⟨y, hy⟩ := G.nonempty_of_mem_faces hu
  have hinter := hsub (subset_convexHull ℝ _ hy)
  have hsub' : (u : Set F) ⊆ (fun x : F => x + 0) '' convexHull ℝ (s.image φ : Set F) ∩
      convexHull ℝ (t.image φ : Set F) := by
    simpa only [add_zero, Set.image_id'] using (subset_convexHull ℝ (u : Set F)).trans hsub
  have hbound := card_add_finrank_le_of_subset_transverse_faces S T hsS htT (G.indep hu)
    (G.nonempty_of_mem_faces hu) 0 hsub' (htrans s hs t ht hdisj ⟨y, hinter⟩)
  rw [Finset.card_image_of_injOn hsAI.1, Finset.card_image_of_injOn htAI.1] at hbound
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

end DifferentialGeometry.Topology.PiecewiseLinear
