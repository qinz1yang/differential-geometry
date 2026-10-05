import DifferentialGeometry.Topology.Homotopy.FreeLoopNullhomotopy
import DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import DifferentialGeometry.Topology.PiecewiseLinear.DiskFilling
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.NormalSystem.SimplicialConstruction
import DifferentialGeometry.Topology.PiecewiseLinear.SingularDisk.BoundaryWord.EmbeddedDisk
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedronLocalConnectedness

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v

section LoopClass

variable {X : Type u} [TopologicalSpace X]

theorem conjugacyClassMeets_bot_iff_nullhomotopic {x : X} (γ : freeLoop X) (q : Path x (γ 0)) :
    conjugacyClassMeets (normalSystemLoopConjugacyClass x γ q)
        (⊥ : Subgroup (FundamentalGroup X x)) ↔ γ.Nullhomotopic := by
  classical
  have hmem := NormalSystem.conjugacyClassMeets_mk_iff_mem
    (loopRepresentativeAlong q (⟨γ, rfl⟩ : basedCircleLoop (γ 0)))
    (⊥ : Subgroup (FundamentalGroup X x))
  rw [show normalSystemLoopConjugacyClass x γ q =
      ConjClasses.mk (loopRepresentativeAlong q (⟨γ, rfl⟩ : basedCircleLoop (γ 0))) from rfl,
    hmem, Subgroup.mem_bot]
  have hchange : loopRepresentativeAlong q (⟨γ, rfl⟩ : basedCircleLoop (γ 0)) =
      fundamentalGroupChangeBasepoint q
        (basedCircleFundamentalGroupClass (⟨γ, rfl⟩ : basedCircleLoop (γ 0))) := rfl
  rw [hchange, (fundamentalGroupChangeBasepoint q).map_eq_one_iff]
  have hpath : (pathToCircle (circleToPath (⟨γ, rfl⟩ : basedCircleLoop (γ 0)))) = γ :=
    congrArg Subtype.val ((basedPathCircleHomeomorph (γ 0)).apply_symm_apply ⟨γ, rfl⟩)
  constructor
  · intro h
    have hhom : (circleToPath (⟨γ, rfl⟩ : basedCircleLoop (γ 0))).Homotopic (Path.refl (γ 0)) :=
      Path.Homotopic.Quotient.eq.mp h
    have := (pathToCircle_nullhomotopic_iff
      (circleToPath (⟨γ, rfl⟩ : basedCircleLoop (γ 0)))).mpr hhom
    rwa [hpath] at this
  · intro h
    rw [← hpath] at h
    exact Path.Homotopic.Quotient.eq.mpr
      ((pathToCircle_nullhomotopic_iff (circleToPath (⟨γ, rfl⟩ : basedCircleLoop (γ 0)))).mp h)

theorem nullhomotopic_freeLoop_of_inclusion_nullhomotopic {Y : Type v} [TopologicalSpace Y]
    {A : Set Y} {W : Set Y} (hAW : A ⊆ W)
    (hnull : (⟨Set.inclusion hAW, continuous_inclusion hAW⟩ : C(A, W)).Nullhomotopic)
    (γ : freeLoop W) (hγ : ∀ θ, (γ θ : Y) ∈ A) :
    γ.Nullhomotopic := by
  have hfac : γ = (⟨Set.inclusion hAW, continuous_inclusion hAW⟩ : C(A, W)).comp
      (⟨fun θ => ⟨(γ θ : Y), hγ θ⟩,
        (continuous_subtype_val.comp γ.continuous).subtype_mk _⟩ : C(loopCircle, A)) := by
    ext θ
    rfl
  rw [hfac]
  exact hnull.comp_left _

end LoopClass

section Subcomplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem convexHull_carrierFace_subset_of_mem_subcomplex
    {K B : Geometry.SimplicialComplex ℝ E} (hBK : B.faces ⊆ K.faces) {y : E} (hy : y ∈ B.space) :
    convexHull ℝ ((carrierFace K y : Finset E) : Set E) ⊆ B.space := by
  classical
  obtain ⟨s, hs, hys⟩ := B.mem_space_iff.mp hy
  have hyK : y ∈ K.space := space_mono_of_faces_subset hBK hy
  have hsub : carrierFace K y ⊆ s := carrierFace_subset hyK (hBK hs) hys
  exact (convexHull_mono (Finset.coe_subset.mpr hsub)).trans (B.convexHull_subset_space hs)

theorem convexHull_carrierFace_subset_connectedComponentIn
    {K B : Geometry.SimplicialComplex ℝ E} (hBK : B.faces ⊆ K.faces) {y : E} (hy : y ∈ B.space) :
    convexHull ℝ ((carrierFace K y : Finset E) : Set E) ⊆ connectedComponentIn B.space y := by
  have hyK : y ∈ K.space := space_mono_of_faces_subset hBK hy
  exact (convex_convexHull ℝ _).isPreconnected.subset_connectedComponentIn
    (mem_convexHull_carrierFace hyK)
    (convexHull_carrierFace_subset_of_mem_subcomplex hBK hy)

theorem connectedComponentComplex_space_eq_connectedComponentIn
    (B : Geometry.SimplicialComplex ℝ E) (c : ConnectedComponents B.space) {y : E}
    (hy : y ∈ (connectedComponentComplex B c).space) :
    (connectedComponentComplex B c).space = connectedComponentIn B.space y := by
  rw [connectedComponentComplex_space] at hy ⊢
  obtain ⟨p, hp, rfl⟩ := hy
  rw [← hp, ← connectedComponentComplex_space, connectedComponentComplex_mk,
    restrict_connectedComponentIn_space]

theorem exists_isOpen_inter_eq_connectedComponentComplex_space
    (B : Geometry.SimplicialComplex ℝ E) [Finite B.faces] (c : ConnectedComponents B.space) :
    ∃ O : Set E, IsOpen O ∧ O ∩ B.space = (connectedComponentComplex B c).space := by
  classical
  let _ : LocallyConnectedSpace B.space := locallyConnectedSpace_space B
  have hopen : IsOpen (ConnectedComponents.mk ⁻¹' {c}) := by
    obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [connectedComponents_preimage_singleton]
    exact isOpen_connectedComponent
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp hopen
  refine ⟨O, hO, ?_⟩
  rw [connectedComponentComplex_space, ← hOeq]
  ext z
  constructor
  · rintro ⟨hzO, hzB⟩
    exact ⟨⟨z, hzB⟩, hzO, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨hp, p.2⟩

end Subcomplex

section Extension

variable {Q : Type v} [TopologicalSpace Q]

theorem exists_continuousMap_extension_of_nullhomotopic_complex {s : Set ℂ}
    (hc : Convex ℝ s) (hs : IsClosed s) (hb : Bornology.IsBounded s)
    (hi : (interior s).Nonempty) (f : C(frontier s, Q)) (hf : f.Nullhomotopic) :
    ∃ F : C(s, Q), ∀ z : frontier s, F ⟨z.val, hs.frontier_subset z.property⟩ = f z := by
  obtain ⟨e, -, he, heB⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall hc hi hb
  rw [hs.closure_eq] at he
  have hboundary (z : Circle) : e.symm z.val ∈ frontier s := by
    have hz : z.val ∈ e '' frontier s := by rw [heB]; exact z.property
    obtain ⟨w, hw, hew⟩ := hz
    simpa only [← hew, e.symm_apply_apply] using hw
  let c : C(loopCircle, frontier s) :=
    ⟨fun θ => ⟨e.symm (AddCircle.toCircle θ : ℂ), hboundary (AddCircle.toCircle θ)⟩,
      (e.symm.continuous.comp
        (continuous_subtype_val.comp AddCircle.continuous_toCircle)).subtype_mk _⟩
  obtain ⟨u, hu⟩ := exists_continuous_disk_of_nullhomotopic (hf.comp_left c)
  have hbody (z : s) : e z.val ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [← he]
    exact ⟨z.val, z.property, rfl⟩
  let F : C(s, Q) := ⟨fun z => u ⟨e z.val, hbody z⟩,
    u.continuous.comp ((e.continuous.comp continuous_subtype_val).subtype_mk _)⟩
  refine ⟨F, ?_⟩
  intro z
  let a : Circle := ⟨e z.val, by
    change e z.val ∈ Metric.sphere (0 : ℂ) 1
    rw [← heB]
    exact ⟨z.val, z.property, rfl⟩⟩
  let θ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm a
  have hθ : AddCircle.toCircle θ = a := by
    rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
    exact (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).apply_symm_apply a
  have hd : (⟨e z.val, hbody ⟨z.val, hs.frontier_subset z.property⟩⟩ : closedDisk) =
      diskBoundary θ :=
    Subtype.ext (congrArg (fun w : Circle => (w : ℂ)) hθ).symm
  change u ⟨e z.val, hbody ⟨z.val, hs.frontier_subset z.property⟩⟩ = f z
  rw [hd]
  refine (congrArg (fun g : freeLoop Q => g θ) hu).trans ?_
  change f (c θ) = f z
  refine congrArg f (Subtype.ext ?_)
  change e.symm (AddCircle.toCircle θ : ℂ) = z.val
  rw [hθ]
  exact e.symm_apply_apply z.val

theorem exists_continuousMap_extension_of_nullhomotopic
    {P : Set (EuclideanSpace ℝ (Fin 2))} (hP : IsCompact P) (hc : Convex ℝ P)
    (hi : (interior P).Nonempty) (f : C(frontier P, Q)) (hf : f.Nullhomotopic) :
    ∃ F : C(P, Q), ∀ z : frontier P, F ⟨z.val, hP.isClosed.frontier_subset z.property⟩ = f z := by
  let e : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] ℂ :=
    ((EuclideanSpace.equiv (Fin 2) ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).trans
      Complex.equivRealProdCLM.symm
  have hfront : e '' frontier P = frontier (e '' P) := e.toHomeomorph.image_frontier P
  have hbd : ∀ z ∈ frontier (e '' P), e.symm z ∈ frontier P := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hfront.symm.subset hz
    simpa only [e.symm_apply_apply] using hw
  let j : C(frontier (e '' P), frontier P) :=
    ⟨fun z => ⟨e.symm z, hbd z z.property⟩,
      (e.symm.continuous.comp continuous_subtype_val).subtype_mk _⟩
  obtain ⟨F, hF⟩ := exists_continuousMap_extension_of_nullhomotopic_complex
    (hc.linear_image e.toLinearMap) (hP.image e.continuous).isClosed
    (hP.image e.continuous).isBounded
    (e.toHomeomorph.image_interior P ▸ hi.image e) (f.comp j) (hf.comp_left j)
  refine ⟨⟨fun z => F ⟨e z, mem_image_of_mem e z.property⟩,
    F.continuous.comp ((e.continuous.comp continuous_subtype_val).subtype_mk _)⟩, fun z => ?_⟩
  have hz : e z ∈ frontier (e '' P) := hfront.subset (mem_image_of_mem e z.property)
  exact (hF ⟨e z, hz⟩).trans (congrArg f (Subtype.ext (e.symm_apply_apply z)))

theorem exists_continuousOn_mapsTo_of_nullhomotopic {E : Type*} [NormedAddCommGroup E]
    {P : Set (EuclideanSpace ℝ (Fin 2))} (hP : IsPLBall 2 P) (hc : Convex ℝ P)
    {W : Set E} (b : C(frontier P, W)) (hb : b.Nullhomotopic) :
    ∃ v : EuclideanSpace ℝ (Fin 2) → E, ContinuousOn v P ∧ MapsTo v P W ∧
      ∀ z : frontier P, v z = (b z : E) := by
  classical
  have hbd : frontier P ⊆ P := hP.isPolyhedron.isClosed.frontier_subset
  obtain ⟨F, hF⟩ := exists_continuousMap_extension_of_nullhomotopic
    hP.isPolyhedron.isCompact hc hP.interior_nonempty b hb
  let v : EuclideanSpace ℝ (Fin 2) → E := fun z => if hz : z ∈ P then (F ⟨z, hz⟩ : E) else 0
  have hv : ∀ z : P, v z = (F z : E) := by
    intro z
    simp only [v, dite_eq_left z.property]
  refine ⟨v, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp F.continuous).congr fun z => (hv z).symm
  · intro z hz
    rw [hv ⟨z, hz⟩]
    exact (F ⟨z, hz⟩).property
  · intro z
    rw [hv ⟨z, hbd z.property⟩]
    exact congrArg (fun w : W => (w : E)) (hF z)

end Extension

section Filling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem exists_isPiecewiseAffineOn_mapsTo_carrierFace
    (D : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) [Finite D.faces]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {v : EuclideanSpace ℝ (Fin 2) → E} (hv : ContinuousOn v D.space)
    (hmap : MapsTo v D.space K.space) :
    ∃ g : EuclideanSpace ℝ (Fin 2) → E, IsPiecewiseAffineOn g D.space ∧
      MapsTo g D.space K.space ∧
      ∀ x ∈ D.space, g x ∈ convexHull ℝ ((carrierFace K (v x) : Finset E) : Set E) := by
  obtain ⟨D', φ, hD', hD'fin, hφ, hclose⟩ :=
    exists_isSubdivision_simplicialApproximation D K hv hmap
  let _ : Finite D'.faces := hD'fin.to_subtype
  have hspace : D'.space = D.space := hD'.space_eq
  refine ⟨simplicialMap D' φ, ?_, ?_, hclose⟩
  · rw [← hspace]
    exact isPiecewiseAffineOn_simplicialMap D' φ
  · rw [← hspace]
    exact simplicialMap_mapsTo D' K φ hφ

open Classical in
theorem exists_isPiecewiseAffineOn_fill_of_nullhomotopic
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (B : Geometry.SimplicialComplex ℝ E) (hBK : B.faces ⊆ K.faces)
    {V : Set E} (hVB : V ⊆ B.space) (hVK : V ⊆ K.space)
    (hVcomp : ∀ y ∈ V, connectedComponentIn B.space y = V) (γ : freeLoop V)
    (hnull : ((⟨Set.inclusion hVK, continuous_inclusion hVK⟩ :
      C(V, K.space)).comp γ).Nullhomotopic) :
    ∃ (P : Set (EuclideanSpace ℝ (Fin 2))) (f : EuclideanSpace ℝ (Fin 2) → E)
      (a : loopCircle ≃ₜ frontier P) (δ : freeLoop V),
      IsPLBall 2 P ∧ IsPiecewiseAffineOn f P ∧ MapsTo f P K.space ∧
        MapsTo f (frontier P) V ∧ (∀ θ, (δ θ : E) = f (a θ)) ∧ δ.Homotopic γ := by
  obtain ⟨T, hT, hcard, -, -, -⟩ := exists_affineIndependent_openSimplex_subset
    (n := 1) (by simp) (0 : EuclideanSpace ℝ (Fin 2)) Filter.univ_mem
  set P := convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 2))) with hPdef
  have hP : IsPLBall 2 P := isPLBall_convexHull_of_affineIndependent T hT hcard
  have hconv : Convex ℝ P := convex_convexHull ℝ _
  have hfrontP : frontier P ⊆ P := hP.isPolyhedron.isClosed.frontier_subset
  obtain ⟨a⟩ := nonempty_homeomorph_loopCircle_of_isPLSphere_one hP.isPLSphere_frontier
  set bK : C(frontier P, K.space) :=
    ((⟨Set.inclusion hVK, continuous_inclusion hVK⟩ : C(V, K.space)).comp γ).comp
      (a.symm : C(frontier P, loopCircle)) with hbKdef
  obtain ⟨v, hvcont, hvmap, hvbd⟩ := exists_continuousOn_mapsTo_of_nullhomotopic hP hconv bK
    (hnull.comp_left (a.symm : C(frontier P, loopCircle)))
  have hvval : ∀ θ : loopCircle, v (a θ) = (γ θ : E) := by
    intro θ
    rw [hvbd (a θ)]
    change ((γ (a.symm (a θ)) : V) : E) = (γ θ : E)
    rw [a.symm_apply_apply]
  obtain ⟨D, hDfin, hDspace⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite D.faces := hDfin.to_subtype
  obtain ⟨g, hg, hgmap, hclose⟩ := exists_isPiecewiseAffineOn_mapsTo_carrierFace D K
    (hDspace.symm ▸ hvcont) (hDspace.symm ▸ hvmap)
  rw [hDspace] at hg hgmap hclose
  have hcarrier : ∀ θ : loopCircle,
      convexHull ℝ ((carrierFace K (v (a θ)) : Finset E) : Set E) ⊆ V := by
    intro θ
    have hmemV : v (a θ) ∈ V := by
      rw [hvval θ]
      exact (γ θ).property
    have := convexHull_carrierFace_subset_connectedComponentIn hBK (hVB hmemV)
    rwa [hVcomp _ hmemV] at this
  have hgV : ∀ θ : loopCircle, g (a θ) ∈ V :=
    fun θ => hcarrier θ (hclose _ (hfrontP (a θ).property))
  have hgfront : MapsTo g (frontier P) V := by
    intro z hz
    obtain ⟨θ, hθ⟩ := a.surjective ⟨z, hz⟩
    have : g (a θ) ∈ V := hgV θ
    rwa [show ((a θ : EuclideanSpace ℝ (Fin 2))) = z from congrArg Subtype.val hθ] at this
  have hgcont : Continuous fun θ : loopCircle => g (a θ) :=
    (hg.continuousOn.mono hfrontP).comp_continuous
      (continuous_subtype_val.comp a.continuous) fun θ => (a θ).property
  refine ⟨P, g, a, ⟨fun θ => ⟨g (a θ), hgV θ⟩, hgcont.subtype_mk _⟩, hP, hg, hgmap, hgfront,
    fun _ => rfl, ?_⟩
  have hmem : ∀ p : unitInterval × loopCircle,
      (1 - (p.1 : ℝ)) • g (a p.2) + (p.1 : ℝ) • ((γ p.2 : E)) ∈ V := by
    intro p
    refine hcarrier p.2 ((convex_convexHull ℝ _) (hclose _ (hfrontP (a p.2).property)) ?_
      (by linarith [p.1.2.2]) p.1.2.1 (by ring))
    rw [← hvval p.2]
    exact mem_convexHull_carrierFace (hvmap (hfrontP (a p.2).property))
  exact ⟨{ toFun := fun p => ⟨(1 - (p.1 : ℝ)) • g (a p.2) + (p.1 : ℝ) • ((γ p.2 : E)), hmem p⟩
           continuous_toFun := by
             refine Continuous.subtype_mk ?_ _
             exact ((continuous_const.sub
               (continuous_subtype_val.comp continuous_fst)).smul
                 (hgcont.comp continuous_snd)).add
               ((continuous_subtype_val.comp continuous_fst).smul
                 ((continuous_subtype_val.comp γ.continuous).comp continuous_snd))
           map_zero_left := by
             intro θ
             apply Subtype.ext
             simp
           map_one_left := by
             intro θ
             apply Subtype.ext
             simp }⟩

end Filling

end DifferentialGeometry.Topology.PiecewiseLinear
