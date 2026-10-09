import DifferentialGeometry.Topology.ThreeManifold.TorusCut.Compression
import DifferentialGeometry.Topology.Handle.Manifold
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundarySphere
set_option autoImplicit false

/-!
# Transporting PL piece atlases

A PL atlas on `X` in which the image of a torus `G ∘ τ` is a PL piece pulls back along the
homeomorphism `G` to a PL atlas in which the image of `τ` is a PL piece. The image of a polyhedron
under a PL homeomorphism from a subset of Euclidean three-space into `X` is a PL piece.
-/

noncomputable section
open Set Topology
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Topology.PiecewiseLinear

namespace GC.Topology
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

theorem hasPLPieceAtlas_of_homeomorph {X : Type u} [TopologicalSpace X] (G : X ≃ₜ X)
    {τ : C(GC.Topology.Torus, X)} (h : HasPLPieceAtlas ((G : C(X, X)).comp τ)) :
    HasPLPieceAtlas τ := by
  obtain ⟨A, hG, N, ⟨S⟩⟩ := h
  let := A
  have : HasGroupoid X (plGroupoid 3) := hG
  have hY : G ⁻¹' range ((G : C(X, X)).comp τ) = range τ := by
    ext x
    simp
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

theorem hasPLPieceAtlas_of_isPLHomeomorphInto {X : Type u} [TopologicalSpace X]
    (A : ChartedSpace (EuclideanSpace ℝ (Fin 3)) X) (hA : letI := A; HasGroupoid X (plGroupoid 3))
    {W : Set (EuclideanSpace ℝ (Fin 3))} {f : EuclideanSpace ℝ (Fin 3) → X}
    (hf : letI := A; IsPLHomeomorphInto 3 f W) {Q : Set (EuclideanSpace ℝ (Fin 3))}
    (hQ : IsPolyhedron Q) (hQW : Q ⊆ W) (τ : C(GC.Topology.Torus, X)) (hτ : range τ = f '' Q) :
    HasPLPieceAtlas τ := by
  let := A
  have : HasGroupoid X (plGroupoid 3) := hA
  obtain ⟨T, -, -⟩ :=
    (isPLHomeomorphInto_mono_of_isPolyhedron hf hQ hQW).exists_pLPiece_of_isPolyhedron hQ
  rw [← hτ] at T
  exact ⟨A, hA, 3, ⟨T⟩⟩

end GC.Topology
