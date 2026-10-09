import DifferentialGeometry.Topology.ThreeManifold.TorusCut.Taming

set_option autoImplicit false

/-!
# Set-level transport and presentation lemmas for PL piece atlases (LT-P2)

Set-level (`Y : Set X`) versions of the torus-specific lemmas of `TorusCut/CompressionTransport`
and `TorusCut/Compression`. Private helpers are copied verbatim since they are not exported.
-/

noncomputable section
open Set Topology
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Topology.PiecewiseLinear

namespace GC.LongTime.CuspP1
open GC.Topology
universe u

private theorem hasGroupoid_chartedSpaceOfHomeomorph {n : ℕ} {X X' : Type*} [TopologicalSpace X]
    [TopologicalSpace X'] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    [HasGroupoid X (plGroupoid n)] (h : X' ≃ₜ X) :
    @HasGroupoid _ _ X' _ (Handle.chartedSpaceOfHomeomorph h) (plGroupoid n) := by
  let := Handle.chartedSpaceOfHomeomorph (H := EuclideanSpace ℝ (Fin n)) h
  have hmid : h.toOpenPartialHomeomorph.symm.trans h.toOpenPartialHomeomorph =
      (OpenPartialHomeomorph.refl X : OpenPartialHomeomorph X X) := by
    apply OpenPartialHomeomorph.ext
    · intro x
      change h.toPartialEquiv.toFun (h.toOpenPartialHomeomorph.symm x) = x
      exact h.right_inv x
    · intro x
      change h.toPartialEquiv.toFun (h.toOpenPartialHomeomorph.symm x) = x
      exact h.right_inv x
    · ext x
      simp
  refine ⟨fun he he' => ?_⟩
  rcases he with ⟨e₁, he₁, rfl⟩
  rcases he' with ⟨e₂, he₂, rfl⟩
  have htrans : (h.toOpenPartialHomeomorph.trans e₁).symm.trans
      (h.toOpenPartialHomeomorph.trans e₂) = e₁.symm.trans e₂ := by
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc,
      ← OpenPartialHomeomorph.trans_assoc (e'' := e₂), hmid]
    simp
  rw [htrans]
  exact HasGroupoid.compatible he₁ he₂

private theorem nonempty_plPieceIn_chartedSpaceOfHomeomorph {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {X X' : Type*} [TopologicalSpace X]
    [TopologicalSpace X'] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] (h : X' ≃ₜ X) {Y : Set X}
    (S : PLPieceIn E n X Y) :
    Nonempty (@PLPieceIn E _ _ n X' _ (Handle.chartedSpaceOfHomeomorph h) (h ⁻¹' Y)) := by
  let := Handle.chartedSpaceOfHomeomorph (H := EuclideanSpace ℝ (Fin n)) h
  have hY : BijOn h.symm Y (h ⁻¹' Y) := by
    have hb := h.symm.injective.injOn.bijOn_image (s := Y)
    rwa [h.image_symm] at hb
  have hinj : InjOn (h.symm ∘ S.map) S.complex.space :=
    h.symm.injective.comp_injOn S.bijOn.injOn
  refine ⟨{
    complex := S.complex
    finite_faces := S.finite_faces
    map := h.symm ∘ S.map
    bijOn := hY.comp S.bijOn
    continuousOn := h.symm.continuous.comp_continuousOn S.continuousOn
    isPiecewiseAffineOn_chart := ?_
    isPiecewiseAffineOn_chart_symm := ?_ }⟩
  · rintro _ ⟨e₀, he₀, rfl⟩
    have hfun : (h.toOpenPartialHomeomorph.trans e₀) ∘ (h.symm ∘ S.map) = e₀ ∘ S.map :=
      funext fun z => by simp
    have hset : (h.symm ∘ S.map) ⁻¹' (h.toOpenPartialHomeomorph.trans e₀).source =
        S.map ⁻¹' e₀.source := by
      ext z
      simp
    rw [hfun, hset]
    exact S.isPiecewiseAffineOn_chart e₀ he₀
  · rintro _ ⟨e₀, he₀, rfl⟩
    have hset : (h.toOpenPartialHomeomorph.trans e₀).target ∩
        (h.toOpenPartialHomeomorph.trans e₀).symm ⁻¹' (h ⁻¹' Y) = e₀.target ∩ e₀.symm ⁻¹' Y := by
      ext w
      simp
    rw [hset]
    refine (S.isPiecewiseAffineOn_chart_symm e₀ he₀).congr ?_
    rintro w ⟨-, hw⟩
    obtain ⟨a, ha, haw⟩ := S.bijOn.surjOn hw
    have h1 : (h.toOpenPartialHomeomorph.trans e₀).symm w = (h.symm ∘ S.map) a := by
      simp [haw]
    simp only [Function.comp_apply]
    rw [h1, hinj.leftInvOn_invFunOn ha, ← haw, S.bijOn.injOn.leftInvOn_invFunOn ha]


theorem plPieceAtlas_of_homeomorph_set_LTP2 {X : Type u} [TopologicalSpace X] (G : X ≃ₜ X)
    {Y Y' : Set X} (hY : G ⁻¹' Y' = Y)
    (h : ∃ A : ChartedSpace (EuclideanSpace ℝ (Fin 3)) X,
      letI := A
      HasGroupoid X (plGroupoid 3) ∧
        ∃ N : ℕ, Nonempty (PLPieceIn (EuclideanSpace ℝ (Fin N)) 3 X Y')) :
    ∃ A : ChartedSpace (EuclideanSpace ℝ (Fin 3)) X,
      letI := A
      HasGroupoid X (plGroupoid 3) ∧
        ∃ N : ℕ, Nonempty (PLPieceIn (EuclideanSpace ℝ (Fin N)) 3 X Y) := by
  obtain ⟨A, hG, N, ⟨S⟩⟩ := h
  let := A
  have : HasGroupoid X (plGroupoid 3) := hG
  obtain ⟨S'⟩ := nonempty_plPieceIn_chartedSpaceOfHomeomorph G S
  rw [hY] at S'
  exact ⟨Handle.chartedSpaceOfHomeomorph G, hasGroupoid_chartedSpaceOfHomeomorph G, N, ⟨S'⟩⟩

private theorem isPiecewiseAffineWithinAt_of_subset_of_mem_nhdsWithin {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {R S : Set E} {x : E} (hf : IsPiecewiseAffineWithinAt f R x) (hRS : R ⊆ S)
    (hR : R ∈ 𝓝[S] x) : IsPiecewiseAffineWithinAt f S x := by
  obtain ⟨ι, hι, C, A, hC, hCx⟩ := hf
  refine ⟨ι, hι, C, A, fun i => ⟨(hC i).1, (hC i).2.1.trans hRS, (hC i).2.2⟩, ?_⟩
  rw [nhdsWithin_restrict'' S hR, inter_eq_right.mpr hRS]
  exact hCx

private theorem isPLHomeomorphInto_mono_of_isPolyhedron {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] {W Q : Set (EuclideanSpace ℝ (Fin 3))}
    {f : EuclideanSpace ℝ (Fin 3) → X} (hf : IsPLHomeomorphInto 3 f W) (hQ : IsPolyhedron Q)
    (hQW : Q ⊆ W) : IsPLHomeomorphInto 3 f Q := by
  refine ⟨hf.isPLOn.mono_of_isPolyhedron hQ hQW, hf.injOn.mono hQW, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨g, hg, hgf⟩ := hf.2.2 (f x) ⟨x, hQW hx, rfl⟩
  refine ⟨g, ?_, hgf.mono hQW⟩
  set e := chartAt (EuclideanSpace ℝ (Fin 3)) (f x) with he
  have hfx : f x ∈ e.source := mem_chart_source _ _
  have hgx : g (f x) = x := hgf (hQW hx)
  have hg' : ChartedSpace.LiftPropWithinAt (piecewiseAffineProperty 3 3) g (f '' W) (f x) := hg
  rw [StructureGroupoid.liftPropWithinAt_self_target] at hg'
  obtain ⟨hgc, hgpa⟩ := hg'
  change IsPiecewiseAffineWithinAt (g ∘ e.symm) (e.symm ⁻¹' (f '' W)) (e (f x)) at hgpa
  change ChartedSpace.LiftPropWithinAt (piecewiseAffineProperty 3 3) g (f '' Q) (f x)
  rw [StructureGroupoid.liftPropWithinAt_self_target]
  refine ⟨hgc.mono (image_mono hQW), ?_⟩
  change IsPiecewiseAffineWithinAt (g ∘ e.symm) (e.symm ⁻¹' (f '' Q)) (e (f x))
  have hfx' : ChartedSpace.LiftPropWithinAt (piecewiseAffineProperty 3 3) f Q x :=
    hf.isPLOn.mono_of_isPolyhedron hQ hQW x hx
  rw [StructureGroupoid.liftPropWithinAt_self_source] at hfx'
  obtain ⟨hfc, hFpa⟩ := hfx'
  change IsPiecewiseAffineWithinAt (e ∘ f) Q x at hFpa
  obtain ⟨U, hUopen, hxU, hUsub⟩ := mem_nhdsWithin.mp
    (hfc.preimage_mem_nhdsWithin (e.open_source.mem_nhds hfx))
  obtain ⟨ι, hι, C, A, hCprop, hCnhds⟩ := hFpa.inter_of_mem_nhds (hUopen.mem_nhds hxU)
  have hPpoly : IsPolyhedron (⋃ i, C i) := ⟨ι, hι, C, fun i => (hCprop i).1, rfl⟩
  have hPsub : (⋃ i, C i) ⊆ Q ∩ U := iUnion_subset fun i => (hCprop i).2.1
  have hPsrc : ∀ z ∈ ⋃ i, C i, f z ∈ e.source := fun z hz =>
    hUsub ⟨(hPsub hz).2, (hPsub hz).1⟩
  have hFP : IsPiecewiseAffineOn (e ∘ f) (⋃ i, C i) := fun _ _ =>
    ⟨ι, hι, C, A, fun i => ⟨(hCprop i).1, subset_iUnion C i, (hCprop i).2.2⟩,
      self_mem_nhdsWithin⟩
  have hFinj : InjOn (e ∘ f) (⋃ i, C i) := by
    intro z hz w hw hzw
    change e (f z) = e (f w) at hzw
    have hzw' : f z = f w := by
      rw [← e.left_inv (hPsrc z hz), ← e.left_inv (hPsrc w hw), hzw]
    exact hf.injOn (hQW (hPsub hz).1) (hQW (hPsub hw).1) hzw'
  have hR : IsPolyhedron ((e ∘ f) '' ⋃ i, C i) := hPpoly.image_of_isPiecewiseAffineOn hFP hFinj
  have hRQ : (e ∘ f) '' (⋃ i, C i) ⊆ e.symm ⁻¹' (f '' Q) := by
    rintro _ ⟨z, hz, rfl⟩
    simp only [mem_preimage, Function.comp_apply, e.left_inv (hPsrc z hz)]
    exact ⟨z, (hPsub hz).1, rfl⟩
  have hRW : (e ∘ f) '' (⋃ i, C i) ⊆ e.symm ⁻¹' (f '' W) :=
    hRQ.trans (preimage_mono (image_mono hQW))
  have hnhds : (e ∘ f) '' (⋃ i, C i) ∈ 𝓝[e.symm ⁻¹' (f '' Q)] (e (f x)) := by
    obtain ⟨V, hVopen, hxV, hVsub⟩ := mem_nhdsWithin.mp hCnhds
    have hgx' : (g ∘ e.symm) (e (f x)) = x := by
      simp only [Function.comp_apply, e.left_inv hfx, hgx]
    have h1 : (g ∘ e.symm) ⁻¹' (V ∩ U) ∈ 𝓝[e.symm ⁻¹' (f '' Q)] (e (f x)) := by
      apply nhdsWithin_mono _ (preimage_mono (image_mono hQW))
      apply hgpa.continuousWithinAt.preimage_mem_nhdsWithin
      rw [hgx']
      exact (hVopen.inter hUopen).mem_nhds ⟨hxV, hxU⟩
    have h2 : e.target ∈ 𝓝[e.symm ⁻¹' (f '' Q)] (e (f x)) :=
      mem_nhdsWithin_of_mem_nhds (e.open_target.mem_nhds (e.map_source hfx))
    filter_upwards [h1, h2, self_mem_nhdsWithin] with w hw1 hw2 hw3
    obtain ⟨q, hq, hqw⟩ := hw3
    have hgq : g (e.symm w) = q := by
      rw [← hqw]
      exact hgf (hQW hq)
    have hqVU : q ∈ V ∩ U := by
      rw [← hgq]
      exact hw1
    refine ⟨q, hVsub ⟨hqVU.1, hq, hqVU.2⟩, ?_⟩
    change e (f q) = w
    rw [hqw, e.right_inv hw2]
  exact isPiecewiseAffineWithinAt_of_subset_of_mem_nhdsWithin
    (hgpa.mono_of_isPolyhedron hR hRW) hRQ hnhds

theorem plPieceAtlas_of_isPLHomeomorphInto_set_LTP2 {X : Type u} [TopologicalSpace X]
    (A : ChartedSpace (EuclideanSpace ℝ (Fin 3)) X) (hA : letI := A; HasGroupoid X (plGroupoid 3))
    {W : Set (EuclideanSpace ℝ (Fin 3))} {f : EuclideanSpace ℝ (Fin 3) → X}
    (hf : letI := A; IsPLHomeomorphInto 3 f W) {Q : Set (EuclideanSpace ℝ (Fin 3))}
    (hQ : IsPolyhedron Q) (hQW : Q ⊆ W) (Y : Set X) (hτ : Y = f '' Q) :
    ∃ A : ChartedSpace (EuclideanSpace ℝ (Fin 3)) X,
      letI := A
      HasGroupoid X (plGroupoid 3) ∧
        ∃ N : ℕ, Nonempty (PLPieceIn (EuclideanSpace ℝ (Fin N)) 3 X Y) := by
  let := A
  have : HasGroupoid X (plGroupoid 3) := hA
  obtain ⟨T, -, -⟩ :=
    (isPLHomeomorphInto_mono_of_isPolyhedron hf hQ hQW).exists_pLPiece_of_isPolyhedron hQ
  rw [hτ.symm] at T
  exact ⟨A, hA, 3, ⟨T⟩⟩


theorem plPresentation_of_plPieceAtlas_set_LTP2 {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [Nonempty X] {Y : Set X}
    (hA : ∃ A : ChartedSpace (EuclideanSpace ℝ (Fin 3)) X,
      letI := A
      HasGroupoid X (plGroupoid 3) ∧
        ∃ N : ℕ, Nonempty (PLPieceIn (EuclideanSpace ℝ (Fin N)) 3 X Y))
    (hO : IsTriangulationOrientable X) :
    ∃ (N : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
      (_ : Finite K.faces) (h : K.space ≃ₜ X), IsCombinatorialManifold 3 K ∧ IsOrientable 3 K ∧
        IsPolyhedron (((↑) : K.space → EuclideanSpace ℝ (Fin N)) '' (h ⁻¹' Y)) := by
  obtain ⟨A, hG, N₁, ⟨S⟩⟩ := hA
  let := A
  obtain ⟨T⟩ := exists_pLPiece_univ (n := 3) (X := X)
  obtain ⟨K', hK', hfin', hcomb⟩ :=
    T.piece.exists_isSubdivision_isCombinatorialManifold_succ (m := 2)
  let T' := T.piece.subdivide K' hK' hfin'
  have hKfin : Finite K'.faces := hfin'.to_subtype
  have hSfin : Finite S.complex.faces := S.finite_faces.to_subtype
  have hKc : CompactSpace K'.space :=
    isCompact_iff_compactSpace.mp (isPolyhedron_space K').isCompact
  let f : K'.space → X := fun k => T'.map k
  have hfc : Continuous f := T'.continuousOn.domRestrict
  have hfinj : Function.Injective f := fun a b hab => Subtype.ext (T'.bijOn.injOn a.2 b.2 hab)
  have hfsurj : Function.Surjective f := fun y => by
    obtain ⟨k, hk, hky⟩ := T'.bijOn.surjOn (mem_univ y)
    exact ⟨⟨k, hk⟩, hky⟩
  let h : K'.space ≃ₜ X :=
    hfc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hfinj, hfsurj⟩)
  refine ⟨T.ambientDim, K', hKfin, h, hcomb, hO _ K' hcomb ⟨h⟩, ?_⟩
  have htr := S.isPLHomeomorphOn_transition_of_subset T' (subset_univ _)
  have heq : ((↑) : K'.space → EuclideanSpace ℝ (Fin T.ambientDim)) '' (h ⁻¹' Y) =
      T'.complex.space ∩ T'.map ⁻¹' Y := by
    ext y
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k.2, hk⟩
    · rintro ⟨hy, hyS⟩
      exact ⟨⟨y, hy⟩, hyS, rfl⟩
  rw [heq, ← htr.1.image_eq]
  exact (isPolyhedron_space S.complex).image_of_isPiecewiseAffineOn htr.2.1 htr.1.injOn


end GC.LongTime.CuspP1
