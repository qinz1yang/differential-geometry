import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SaddleSlabUniqueness
import DifferentialGeometry.Topology.Manifold.OneManifold.CircleClassification
import DifferentialGeometry.Topology.Manifold.ContMDiff.OpenSubtype
import DifferentialGeometry.Geometry.Boundary.SmoothFactorization

/-!
# Circle parametrisations of the components of a regular level

Lane RG03c. Let `f` be smooth on a boundaryless surface `N` with `f ⁻¹' [a, b]` compact and
`a`, `b` regular. `exists_levelCircle`: every connected component of the level `f ⁻¹' {a}` is the
image of an injective smooth map `ι : ℝ/ℤ → N` whose inverse `invFun ι` is smooth within the
component. The component is a connected component of the boundary level of the slab manifold
`slabSet f a b`, a compact connected one-manifold, hence a circle by
`nonempty_circle_diffeomorph_of_finrank_eq_one`; smoothness of maps into it is read off in `N`
through `contMDiffWithinAt_boundaryLevelInclusion_comp_iff` and the slab atlas. The same
identification gives `locallyConnectedSpace_level`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter TopologicalSpace
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Boundary
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Topology.Manifold.OneManifold

universe uN

namespace GC.Seifert.SaddleSlabProof

variable {E H : Type} {N : Type uN} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

theorem exists_levelCircle (hdim : Module.finrank ℝ E = 2) {f : N → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (hreg : ∀ x, f x = a ∨ f x = b → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (hcpt : IsCompact (f ⁻¹' Icc a b)) {x₀ : N} (hx₀ : f x₀ = a) :
    ∃ ι : AddCircle (1 : ℝ) → N, ContMDiff 𝓘(ℝ, ℝ) I ∞ ι ∧ Injective ι ∧
      range ι = connectedComponentIn (f ⁻¹' {a}) x₀ ∧
      ∀ x ∈ range ι, ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞ (invFun ι) (range ι) x := by
  let C := slabAtlas hdim hf hab hreg
  let := C.toChartedSpace
  have := C.isManifold
  let hI : HasSmoothBoundary (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 2) (𝓡∂ 2) :=
    inferInstance
  have hdimB : Module.finrank ℝ hI.boundaryE = 1 := by
    have h := hI.finrank_boundaryE_succ
    simp at h
    omega
  have hu : Continuous (fun x : slabSet f a b => f x.val) :=
    hf.continuous.comp continuous_subtype_val
  have hbd : ∀ x : slabSet f a b, (𝓡∂ 2).IsBoundaryPoint x → f x.val = a ∨ f x.val = b :=
    fun x hx => (slab_isBoundaryPoint x).mp hx
  let L := boundaryLevel (fun x : slabSet f a b => f x.val) a b hab.ne hu hbd
  have hslab : slabSet f a b = f ⁻¹' Icc a b := by
    ext x
    exact mem_slabSet_iff hab.le x
  have : CompactSpace (slabSet f a b) := isCompact_iff_compactSpace.mp (hslab ▸ hcpt)
  have : CompactSpace L := boundaryLevel_compactSpace _ _ _ _ _ _
  have : LocallyConnectedSpace hI.boundaryH :=
    hI.boundaryI.toHomeomorph.isOpenEmbedding.locallyConnectedSpace
  have : LocallyConnectedSpace L := ChartedSpace.locallyConnectedSpace hI.boundaryH L
  have hmemK : ∀ y : N, f y = a → y ∈ slabSet f a b := fun y hy =>
    (mem_slabSet_iff hab.le y).mpr ⟨hy.ge, hy ▸ hab.le⟩
  have hbdK : ∀ y (hy : f y = a), (𝓡∂ 2).IsBoundaryPoint (⟨y, hmemK y hy⟩ : slabSet f a b) :=
    fun y hy => (slab_isBoundaryPoint _).mpr (Or.inl hy)
  let toL : f ⁻¹' {a} → L := fun y => ⟨⟨⟨y.1, hmemK y.1 y.2⟩, hbdK y.1 y.2⟩, y.2⟩
  let ofL : L → f ⁻¹' {a} := fun y => ⟨y.1.1.1, y.2⟩
  have hofL : Continuous ofL :=
    ((C.contMDiff_subtype_val.comp
      (contMDiff_boundaryLevelInclusion _ a b hab.ne hu hbd)).continuous).subtype_mk _
  have hK : Continuous (fun y : f ⁻¹' {a} => (⟨y.1, hmemK y.1 y.2⟩ : slabSet f a b)) :=
    continuous_subtype_val.subtype_mk _
  have hB : Continuous (fun y : f ⁻¹' {a} =>
      (⟨⟨y.1, hmemK y.1 y.2⟩, hbdK y.1 y.2⟩ : BoundaryManifold (𝓡∂ 2) (slabSet f a b))) :=
    hK.subtype_mk _
  have htoL : Continuous toL := hB.subtype_mk _
  let Φ : L ≃ₜ f ⁻¹' {a} :=
    { toFun := ofL
      invFun := toL
      left_inv := fun y => rfl
      right_inv := fun y => rfl
      continuous_toFun := hofL
      continuous_invFun := htoL }
  set x₀L : L := toL ⟨x₀, hx₀⟩ with hx₀L
  let Cc : Opens L := ⟨connectedComponent x₀L, isOpen_connectedComponent⟩
  have : CompactSpace Cc := isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact
  have : ConnectedSpace Cc := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  obtain ⟨φ⟩ := nonempty_circle_diffeomorph_of_finrank_eq_one hI.boundaryE hI.boundaryH Cc
    hI.boundaryI hdimB
  let incl : Cc → N := fun c => c.1.1.1.1
  have hincl : ContMDiff hI.boundaryI I ∞ incl :=
    (C.contMDiff_subtype_val.comp (contMDiff_boundaryLevelInclusion _ a b hab.ne hu hbd)).comp
      contMDiff_subtype_val
  set ι : AddCircle (1 : ℝ) → N := fun z => incl (φ (AddCircle.diffeomorphCircle z)) with hιdef
  have hι : ContMDiff 𝓘(ℝ, ℝ) I ∞ ι :=
    (hincl.comp φ.contMDiff).comp AddCircle.diffeomorphCircle.contMDiff
  have hinclinj : Injective incl := fun c d h => Subtype.ext (Subtype.ext (Subtype.ext
    (Subtype.ext h)))
  have hιinj : Injective ι := fun z w h =>
    AddCircle.diffeomorphCircle.injective (φ.injective (hinclinj h))
  let inclL : L → N := fun c => c.1.1.1
  have hrange : range ι = inclL '' (Cc : Set L) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨(φ (AddCircle.diffeomorphCircle z)).1, (φ (AddCircle.diffeomorphCircle z)).2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      refine ⟨AddCircle.diffeomorphCircle.symm (φ.symm ⟨c, hc⟩), ?_⟩
      simp only [hιdef, Diffeomorph.apply_symm_apply]
      rfl
  have hcomp : range ι = connectedComponentIn (f ⁻¹' {a}) x₀ := by
    rw [hrange, connectedComponentIn_eq_image (show x₀ ∈ f ⁻¹' {a} from hx₀)]
    have h1 := Φ.image_connectedComponentIn (s := univ) (x := x₀L) (mem_univ _)
    rw [connectedComponentIn_univ, image_univ, Φ.range_coe, connectedComponentIn_univ] at h1
    have h2 : Φ x₀L = ⟨x₀, hx₀⟩ := rfl
    rw [h2] at h1
    rw [← h1, image_image]
    rfl
  refine ⟨ι, hι, hιinj, hcomp, ?_⟩
  intro x hgx
  set g : N → N := fun y => y with hgdef
  set s : Set N := range ι with hsdef
  have hg : ContMDiffWithinAt I I ∞ g s x := contMDiffWithinAt_id
  have hev : ∀ᶠ y in 𝓝[s] x, g y ∈ range ι := self_mem_nhdsWithin
  let ρ : N → Cc := fun y => φ (AddCircle.diffeomorphCircle (invFun ι y))
  have hρ : ∀ y ∈ range ι, incl (ρ y) = y := fun y hy => invFun_eq (f := ι) hy
  have hinv : invFun ι =
      fun y => AddCircle.diffeomorphCircle.symm (φ.symm (ρ (g y))) := by
    funext y
    simp only [ρ, Diffeomorph.symm_apply_apply, hgdef]
  rw [hinv]
  have h1 : ContMDiffWithinAt I I ∞ (fun y => incl (ρ (g y))) s x := by
    apply hg.congr_of_eventuallyEq
    · filter_upwards [hev] with y hy
      exact hρ (g y) hy
    · exact hρ (g x) hgx
  have h2 : ContMDiffWithinAt I (𝓡∂ 2) ∞ (fun y => (ρ (g y)).1.1.1) s x :=
    (C.contMDiffWithinAt_iff_subtype_val (fun y => (ρ (g y)).1.1.1) s x).mpr h1
  have h3 : ContMDiffWithinAt I hI.boundaryI ∞ (fun y => (ρ (g y)).1) s x :=
    (contMDiffWithinAt_boundaryLevelInclusion_comp_iff (fun z : slabSet f a b => f z.val)
      a b hab.ne hu hbd (f := fun y => (ρ (g y)).1)).mp h2
  have hρg : ContMDiffWithinAt I hI.boundaryI ∞ (fun y => ρ (g y)) s x :=
    (DifferentialGeometry.Manifold.contMDiffWithinAt_subtypeVal_comp_iff Cc
      (fun y => ρ (g y)) s x).mp h3
  exact AddCircle.diffeomorphCircle.symm.contMDiff.contMDiffAt.comp_contMDiffWithinAt x
    (φ.symm.contMDiff.contMDiffAt.comp_contMDiffWithinAt x hρg)

omit [T2Space N] in
theorem locallyConnectedSpace_level (hdim : Module.finrank ℝ E = 2) {f : N → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (hreg : ∀ x, f x = a ∨ f x = b → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    LocallyConnectedSpace (f ⁻¹' {a}) := by
  let C := slabAtlas hdim hf hab hreg
  let := C.toChartedSpace
  have := C.isManifold
  let hI : HasSmoothBoundary (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 2) (𝓡∂ 2) :=
    inferInstance
  have hu : Continuous (fun x : slabSet f a b => f x.val) :=
    hf.continuous.comp continuous_subtype_val
  have hbd : ∀ x : slabSet f a b, (𝓡∂ 2).IsBoundaryPoint x → f x.val = a ∨ f x.val = b :=
    fun x hx => (slab_isBoundaryPoint x).mp hx
  let L := boundaryLevel (fun x : slabSet f a b => f x.val) a b hab.ne hu hbd
  have : LocallyConnectedSpace hI.boundaryH :=
    hI.boundaryI.toHomeomorph.isOpenEmbedding.locallyConnectedSpace
  have : LocallyConnectedSpace L := ChartedSpace.locallyConnectedSpace hI.boundaryH L
  have hmemK : ∀ y : N, f y = a → y ∈ slabSet f a b := fun y hy =>
    (mem_slabSet_iff hab.le y).mpr ⟨hy.ge, hy ▸ hab.le⟩
  have hbdK : ∀ y (hy : f y = a), (𝓡∂ 2).IsBoundaryPoint (⟨y, hmemK y hy⟩ : slabSet f a b) :=
    fun y hy => (slab_isBoundaryPoint _).mpr (Or.inl hy)
  let toL : f ⁻¹' {a} → L := fun y => ⟨⟨⟨y.1, hmemK y.1 y.2⟩, hbdK y.1 y.2⟩, y.2⟩
  let ofL : L → f ⁻¹' {a} := fun y => ⟨y.1.1.1, y.2⟩
  have hofL : Continuous ofL :=
    ((C.contMDiff_subtype_val.comp
      (contMDiff_boundaryLevelInclusion _ a b hab.ne hu hbd)).continuous).subtype_mk _
  have hK : Continuous (fun y : f ⁻¹' {a} => (⟨y.1, hmemK y.1 y.2⟩ : slabSet f a b)) :=
    continuous_subtype_val.subtype_mk _
  have hB : Continuous (fun y : f ⁻¹' {a} =>
      (⟨⟨y.1, hmemK y.1 y.2⟩, hbdK y.1 y.2⟩ : BoundaryManifold (𝓡∂ 2) (slabSet f a b))) :=
    hK.subtype_mk _
  have htoL : Continuous toL := hB.subtype_mk _
  let Φ : L ≃ₜ f ⁻¹' {a} :=
    { toFun := ofL
      invFun := toL
      left_inv := fun y => rfl
      right_inv := fun y => rfl
      continuous_toFun := hofL
      continuous_invFun := htoL }
  exact Φ.symm.isOpenEmbedding.locallyConnectedSpace

end GC.Seifert.SaddleSlabProof
