import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SlimLoopPiece74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SlimIntervalFaces74
import DifferentialGeometry.Topology.Manifold.ImmersionCriterionInteriorTarget

/-!
# Draft 74, package S2 (loops), part 2: the `overCircle` slim model of a loop component

Lane S-JUNCTIONS (suffix `_JN74`, group G4b). The circle branch of S-ZSP04's slim bundle (G18,
`slim_loop_circle_ZSP35`, in `W`-form after the closed identification `M.ψ`): an open compact
connected region `O ⊆ int W` of the interior, a circle-valued map `p`, smooth on `O` with onto
differential at every point of `O`, and a standard `S²` (resp. `T²`) smoothly embedded onto the
fibre `{x ∈ O | p x = 1}`. These records are the exit shapes `SphereLoopExit74` /
`TorusLoopExit74`; from them

* `sphereLoopPiece74 L : PieceEmbedding W` (the piece of the clopen region, image exactly `O`),
* `sphereLoopModel74 L : SlimModel (sphereLoopPiece74 L)` (`SlimModel.overCircle`: `p ∘ map` is a
  smooth submersion of the piece, the lifted fibre is a smooth embedding of the model surface,
  `∂ = ∅`)

are produced (and the same for the torus).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

/-- A loop component's region: a clopen connected set inside the interior. -/
structure LoopRegion74 (W : CompactCarrier.{0}) where
  O : Set W.Carrier
  isClopen : IsClopen O
  interior : O ⊆ W.interior
  connected : IsPreconnected O

/-- **The exit of a sphere loop** (S-ZSP04 G18 in `W`-form): the region `O`, a circle-valued
function `p` smooth on `O` with onto differential, and the standard sphere embedded onto the fibre
over `1`. -/
structure SphereLoopExit74 (W : CompactCarrier.{0}) where
  region : LoopRegion74 W
  p : W.Carrier → Circle
  fibre : ClosureSphere.{0} → W.Carrier
  p_smooth : ContMDiffOn W.model (𝓡 1) ∞ p region.O
  p_sub : ∀ x ∈ region.O, Surjective (mfderiv W.model (𝓡 1) p x)
  fibre_embedding : IsSmoothEmbedding (𝓡 2) W.model ∞ fibre
  fibre_range : range fibre = {x | x ∈ region.O ∧ p x = 1}

/-- **The exit of a torus loop**: the same with the standard torus. -/
structure TorusLoopExit74 (W : CompactCarrier.{0}) where
  region : LoopRegion74 W
  p : W.Carrier → Circle
  fibre : Torus → W.Carrier
  p_smooth : ContMDiffOn W.model (𝓡 1) ∞ p region.O
  p_sub : ∀ x ∈ region.O, Surjective (mfderiv W.model (𝓡 1) p x)
  fibre_embedding : IsSmoothEmbedding torusModel W.model ∞ fibre
  fibre_range : range fibre = {x | x ∈ region.O ∧ p x = 1}

/-! ## Lifting maps into the piece of a clopen region -/

section Lift

variable {W : CompactCarrier.{0}} (R : LoopRegion74 W) {x₀ : W.Carrier} (hx₀ : x₀ ∈ R.O)

include hx₀ in
/-- Every point of the connected region has the component index of `x₀`. -/
theorem mk_clopen_eq74 {y : W.Carrier} (hy : y ∈ R.O) :
    (ConnectedComponents.mk ⟨y, (clopenFn74_le_zero_iff).2 hy⟩ :
      ConnectedComponents {x : W.Carrier // clopenFn74 R.O x ≤ 0}) = clopenIdx74 hx₀ := by
  have hset : {x : W.Carrier | clopenFn74 R.O x ≤ 0} = R.O :=
    Set.ext fun x => clopenFn74_le_zero_iff
  have hpre0 : IsPreconnected {x : W.Carrier | clopenFn74 R.O x ≤ 0} := by
    rw [hset]
    exact R.connected
  have hps : PreconnectedSpace {x : W.Carrier | clopenFn74 R.O x ≤ 0} :=
    Subtype.preconnectedSpace hpre0
  have hpre : IsPreconnected (univ : Set {x : W.Carrier // clopenFn74 R.O x ≤ 0}) :=
    hps.isPreconnected_univ
  exact ConnectedComponents.coe_eq_coe'.2
    (hpre.subset_connectedComponent (x := ⟨x₀, (clopenFn74_le_zero_iff).2 hx₀⟩)
      (mem_univ _) (mem_univ _))

/-- The lift of a point of `O` to the piece of the clopen region. -/
def liftPoint74 {y : W.Carrier} (hy : y ∈ R.O) : (clopenPiece74 R.isClopen hx₀).Piece :=
  ⟨⟨y, (clopenFn74_le_zero_iff).2 hy⟩, mk_clopen_eq74 R hx₀ hy⟩

theorem map_liftPoint74 {y : W.Carrier} (hy : y ∈ R.O) :
    (clopenPiece74 R.isClopen hx₀).map (liftPoint74 R hx₀ hy) = y :=
  rfl

theorem liftPoint74_map (q : (clopenPiece74 R.isClopen hx₀).Piece) :
    liftPoint74 R hx₀ (map_mem_clopenPiece74 R.isClopen hx₀ q) = q := by
  apply (clopenPiece74 R.isClopen hx₀).injective
  rfl

/-- **A smooth embedding of a closed manifold into the interior region lifts to a smooth
embedding into its piece** (the piece map is a local diffeomorphism). -/
theorem exists_liftEmbedding74 {EF HF F : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF]
    [FiniteDimensional ℝ EF] [Nontrivial EF] [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF}
    [IF.Boundaryless] [TopologicalSpace F] [ChartedSpace HF F] [IsManifold IF ∞ F]
    {φ : F → W.Carrier} (hφ : IsSmoothEmbedding IF W.model ∞ φ) (hmem : ∀ z, φ z ∈ R.O) :
    ∃ f : F → (clopenPiece74 R.isClopen hx₀).Piece,
      (∀ z, (clopenPiece74 R.isClopen hx₀).map (f z) = φ z) ∧
        IsSmoothEmbedding IF (𝓡∂ 3) ∞ f := by
  let P := clopenPiece74 R.isClopen hx₀
  let f : F → P.Piece := fun z => liftPoint74 R hx₀ (hmem z)
  have hmap : ∀ z, P.map (f z) = φ z := fun z => rfl
  have hfc : Continuous f :=
    ((hφ.contMDiff.continuous.subtype_mk fun z =>
      (clopenFn74_le_zero_iff).2 (hmem z)).subtype_mk fun z => mk_clopen_eq74 R hx₀ (hmem z))
  have hcomp : P.map ∘ f = φ := funext hmap
  have hfs : ContMDiff IF (𝓡∂ 3) ∞ f :=
    contMDiff_of_comp_localDiffeo74 P hfc (clopenPiece74_localDiffeo R.isClopen hx₀)
      (by rw [hcomp]; exact hφ.contMDiff)
  have hfe : Topology.IsEmbedding f :=
    Topology.IsEmbedding.of_comp hfc P.continuous_map (by rw [hcomp]; exact hφ.isEmbedding)
  have hinj : ∀ z, Injective (mfderiv IF (𝓡∂ 3) f z) := by
    intro z
    have h1 := mfderiv_comp (I := IF) (I' := 𝓡∂ 3) (I'' := W.model) z
      (g := P.map) (f := f) (P.mdifferentiable_map _) (hfs.mdifferentiableAt (by simp))
    have h2 : Injective (mfderiv IF W.model (P.map ∘ f) z) := by
      rw [hcomp]
      exact (hφ.isImmersion.isImmersionAt z).mfderiv_injective (by simp)
    rw [h1] at h2
    exact Injective.of_comp h2
  have hint : ∀ z, (𝓡∂ 3).IsInteriorPoint (f z) := by
    intro z
    rw [(𝓡∂ 3).isInteriorPoint_iff_not_isBoundaryPoint]
    intro hb
    have := clopenPiece74_boundary_empty R.isClopen R.interior hx₀
    rw [eq_empty_iff_forall_notMem] at this
    exact this (f z) hb
  exact ⟨f, hmap, isSmoothEmbedding_of_injective_mfderiv_of_interior_GSF (by simp) hfs hfe hinj
    hint⟩

/-- The circle map of a loop, read on the piece, is smooth. -/
theorem loopProj74_smooth {p : W.Carrier → Circle} (hp : ContMDiffOn W.model (𝓡 1) ∞ p R.O) :
    ContMDiff (𝓡∂ 3) (𝓡 1) ∞ (fun q => p ((clopenPiece74 R.isClopen hx₀).map q)) :=
  hp.comp_contMDiff (clopenPiece74 R.isClopen hx₀).smooth
    (map_mem_clopenPiece74 R.isClopen hx₀)

/-- The circle map of a loop, read on the piece, is a submersion. -/
theorem loopProj74_submersion {p : W.Carrier → Circle} (hp : ContMDiffOn W.model (𝓡 1) ∞ p R.O)
    (hsub : ∀ x ∈ R.O, Surjective (mfderiv W.model (𝓡 1) p x))
    (q : (clopenPiece74 R.isClopen hx₀).Piece) :
    Surjective (mfderiv (𝓡∂ 3) (𝓡 1) (fun q => p ((clopenPiece74 R.isClopen hx₀).map q)) q) := by
  let P := clopenPiece74 R.isClopen hx₀
  have hpd : MDifferentiableAt W.model (𝓡 1) p (P.map q) :=
    ((hp.contMDiffAt (R.isClopen.isOpen.mem_nhds
      (map_mem_clopenPiece74 R.isClopen hx₀ q))).mdifferentiableAt (by simp))
  have h1 := mfderiv_comp (I := 𝓡∂ 3) (I' := W.model) (I'' := 𝓡 1) q (g := p) (f := P.map) hpd
    (P.mdifferentiable_map q)
  have h2 : Surjective ((mfderiv W.model (𝓡 1) p (P.map q)).comp
      (mfderiv (𝓡∂ 3) W.model P.map q)) :=
    (hsub _ (map_mem_clopenPiece74 R.isClopen hx₀ q)).comp (P.mfderiv_bijective q).2
  exact h1 ▸ h2

/-- The fibre of the circle map on the piece is the lifted standard surface. -/
theorem range_liftFibre74 {F : Type*} {p : W.Carrier → Circle} {φ : F → W.Carrier}
    (hrange : range φ = {x | x ∈ R.O ∧ p x = 1})
    {f : F → (clopenPiece74 R.isClopen hx₀).Piece}
    (hf : ∀ z, (clopenPiece74 R.isClopen hx₀).map (f z) = φ z) :
    range f = (fun q => p ((clopenPiece74 R.isClopen hx₀).map q)) ⁻¹' {1} := by
  let P := clopenPiece74 R.isClopen hx₀
  ext q
  constructor
  · rintro ⟨z, rfl⟩
    change p (P.map (f z)) = 1
    rw [hf z]
    have : φ z ∈ range φ := mem_range_self z
    rw [hrange] at this
    exact this.2
  · intro hq
    have hq' : p (P.map q) = 1 := hq
    have hmem : P.map q ∈ range φ := by
      rw [hrange]
      exact ⟨map_mem_clopenPiece74 R.isClopen hx₀ q, hq'⟩
    obtain ⟨z, hz⟩ := hmem
    exact ⟨z, P.injective ((hf z).trans hz)⟩

end Lift

/-! ## The sphere loop and the torus loop -/

section SphereLoop

variable {W : CompactCarrier.{0}} (L : SphereLoopExit74 W)

theorem SphereLoopExit74.fibre_mem (z : ClosureSphere.{0}) : L.fibre z ∈ L.region.O := by
  have : L.fibre z ∈ range L.fibre := mem_range_self z
  rw [L.fibre_range] at this
  exact this.1

/-- A point of the loop region: the base point of the standard fibre. -/
def SphereLoopExit74.basePoint : W.Carrier :=
  L.fibre FC39P0.sphereBasePoint74

theorem SphereLoopExit74.basePoint_mem : L.basePoint ∈ L.region.O :=
  L.fibre_mem _

/-- **The slim piece of a sphere loop**: the piece of the clopen region (image exactly `O`). -/
def sphereLoopPiece74 : PieceEmbedding W :=
  clopenPiece74 L.region.isClopen L.basePoint_mem

theorem range_sphereLoopPiece74 : range (sphereLoopPiece74 L).map = L.region.O :=
  range_clopenPiece74 L.region.isClopen L.region.connected L.basePoint_mem

/-- **The `overCircle` slim model of a sphere loop.** -/
def sphereLoopModel74 : SlimModel (sphereLoopPiece74 L) :=
  SlimModel.overCircle (fun q => L.p ((sphereLoopPiece74 L).map q))
    (loopProj74_smooth L.region L.basePoint_mem L.p_smooth)
    (loopProj74_submersion L.region L.basePoint_mem L.p_smooth L.p_sub)
    (SlimFibre.sphere
      (Classical.choose (exists_liftEmbedding74 L.region L.basePoint_mem L.fibre_embedding
        L.fibre_mem))
      (Classical.choose_spec (exists_liftEmbedding74 L.region L.basePoint_mem L.fibre_embedding
        L.fibre_mem)).2
      (range_liftFibre74 L.region L.basePoint_mem L.fibre_range
        (Classical.choose_spec (exists_liftEmbedding74 L.region L.basePoint_mem
          L.fibre_embedding L.fibre_mem)).1))
    (clopenPiece74_boundary_empty L.region.isClopen L.region.interior L.basePoint_mem)

end SphereLoop

section TorusLoop

variable {W : CompactCarrier.{0}} (L : TorusLoopExit74 W)

theorem TorusLoopExit74.fibre_mem (z : Torus) : L.fibre z ∈ L.region.O := by
  have : L.fibre z ∈ range L.fibre := mem_range_self z
  rw [L.fibre_range] at this
  exact this.1

/-- A point of the loop region: the base point of the standard fibre. -/
def TorusLoopExit74.basePoint : W.Carrier :=
  L.fibre (1 : Torus)

theorem TorusLoopExit74.basePoint_mem : L.basePoint ∈ L.region.O :=
  L.fibre_mem _

/-- **The slim piece of a torus loop**: the piece of the clopen region (image exactly `O`). -/
def torusLoopPiece74 : PieceEmbedding W :=
  clopenPiece74 L.region.isClopen L.basePoint_mem

theorem range_torusLoopPiece74 : range (torusLoopPiece74 L).map = L.region.O :=
  range_clopenPiece74 L.region.isClopen L.region.connected L.basePoint_mem

/-- **The `overCircle` slim model of a torus loop.** -/
def torusLoopModel74 : SlimModel (torusLoopPiece74 L) :=
  SlimModel.overCircle (fun q => L.p ((torusLoopPiece74 L).map q))
    (loopProj74_smooth L.region L.basePoint_mem L.p_smooth)
    (loopProj74_submersion L.region L.basePoint_mem L.p_smooth L.p_sub)
    (SlimFibre.torus
      (Classical.choose (exists_liftEmbedding74 L.region L.basePoint_mem L.fibre_embedding
        L.fibre_mem))
      (Classical.choose_spec (exists_liftEmbedding74 L.region L.basePoint_mem L.fibre_embedding
        L.fibre_mem)).2
      (range_liftFibre74 L.region L.basePoint_mem L.fibre_range
        (Classical.choose_spec (exists_liftEmbedding74 L.region L.basePoint_mem
          L.fibre_embedding L.fibre_mem)).1))
    (clopenPiece74_boundary_empty L.region.isClopen L.region.interior L.basePoint_mem)

end TorusLoop

end GC.GraphManifold.Assembly
