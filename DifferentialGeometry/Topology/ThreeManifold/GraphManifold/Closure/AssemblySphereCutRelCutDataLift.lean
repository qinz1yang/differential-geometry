import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyInverseSmooth
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCutSystem

/-!
# Chapter-14 assembly, relative COMPARE cut data (shared, part 1): lifting charts into a piece

Lane ASM-L2f, shared cut-data group (for G5 SEP and G6 NONSEP). A regular cut of `W` needs, for
every port of `W` and every side of every seam, a half collar of the owning piece lying over the
given collar of `W` (`RegularCutData.externalLift_eq`, `RegularCutData.lift_eq`). For an injective
piece this is a pull back: any partial diffeomorphism into `W` whose target lies in the range of the
piece lifts, as a partial diffeomorphism with the same source, through the piece map (the piece map
is a closed embedding with bijective differentials; smoothness of the lift at boundary points is
`contMDiffOn_of_leftInverse_of_bijective_mfderiv`, `Closure/AssemblyInverseSmooth.lean`).

* `PieceFold.isClosedEmbedding_map`: an injective piece map is a closed embedding.
* `PieceFold.exists_lift_of_injective`: the lift of a partial diffeomorphism with target in the
  range, with its source, its target (the preimage of the old target) and its values.
* `PieceFold.exists_halfCollarLift_of_injective`: the half-collar form (source `halfCollarSource`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace PieceFold

variable {W : CompactCarrier.{u}} (P : PieceFold W)

/-- An injective piece map is a closed embedding. -/
theorem isClosedEmbedding_map (hinj : Injective P.map) :
    _root_.Topology.IsClosedEmbedding P.map :=
  P.continuous_map.isClosedEmbedding hinj

/-- **Lifting a chart into an injective piece.** A partial diffeomorphism into `W` whose target
lies in the range of an injective piece lifts through the piece map. -/
theorem exists_lift_of_injective (hinj : Injective P.map)
    {EX HX X : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
    {K : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X] [IsManifold K ∞ X]
    (c : PartialDiffeomorph K W.model X W.Carrier ∞) (hc : c.target ⊆ range P.map) :
    ∃ c' : PartialDiffeomorph K (𝓡∂ 3) X P.Piece ∞,
      c'.source = c.source ∧ c'.target = P.map ⁻¹' c.target ∧
      ∀ p, p ∈ c.source → P.map (c' p) = c p := by
  classical
  let g : X → P.Piece := fun p => Function.invFun P.map (c p)
  let f : P.Piece → X := fun q => c.symm (P.map q)
  have hmg : ∀ p, p ∈ c.source → P.map (g p) = c p :=
    fun p hp => Function.invFun_eq (hc (c.map_source hp))
  have hgm : ∀ q, Function.invFun P.map (P.map q) = q := Function.leftInverse_invFun hinj
  let A : Set P.Piece := P.map ⁻¹' c.target
  have hA : IsOpen A := c.open_target.preimage P.continuous_map
  have hf : ContMDiffOn (𝓡∂ 3) K ∞ f A :=
    c.contMDiffOn_invFun.comp P.smooth.contMDiffOn (fun _ hq => hq)
  have hfA : MapsTo f A c.source := fun q hq => c.map_target hq
  have hgB : MapsTo g c.source A := by
    intro p hp
    change P.map (g p) ∈ c.target
    rw [hmg p hp]
    exact c.map_source hp
  have hfg : ∀ p ∈ c.source, f (g p) = p := by
    intro p hp
    change c.symm (P.map (g p)) = p
    rw [hmg p hp]
    exact c.left_inv hp
  have hgf : ∀ q ∈ A, g (f q) = q := by
    intro q hq
    have hr : c.toPartialEquiv (c.symm.toPartialEquiv (P.map q)) = P.map q :=
      c.toPartialEquiv.right_inv hq
    change Function.invFun P.map (c.toPartialEquiv (c.symm.toPartialEquiv (P.map q))) = q
    rw [hr, hgm]
  have hgc : ContinuousOn g c.source := by
    rw [(P.isClosedEmbedding_map hinj).isInducing.continuousOn_iff]
    exact c.contMDiffOn_toFun.continuousOn.congr fun p hp => hmg p hp
  have hbij : ∀ q ∈ A, Bijective (mfderiv (𝓡∂ 3) K f q) := by
    intro q hq
    have hloc := c.symm.isLocalDiffeomorphAt W.model K ∞ (show P.map q ∈ c.symm.source from hq)
    have hc' : MDifferentiableAt W.model K c.symm (P.map q) :=
      hloc.mdifferentiableAt (by simp)
    rw [show f = c.symm ∘ P.map from rfl,
      mfderiv_comp q hc' (P.mdifferentiable_map q), ContinuousLinearMap.coe_comp,
      ← hloc.mfderivToContinuousLinearEquiv_coe (by simp)]
    exact (hloc.mfderivToContinuousLinearEquiv (by simp)).bijective.comp (P.mfderiv_bijective q)
  have hgs : ContMDiffOn K (𝓡∂ 3) ∞ g c.source :=
    contMDiffOn_of_leftInverse_of_bijective_mfderiv hA c.open_source hf hfA hgB hfg hgf hgc hbij
  refine ⟨{ toFun := g
            invFun := f
            source := c.source
            target := A
            map_source' := hgB
            map_target' := hfA
            left_inv' := hfg
            right_inv' := hgf
            open_source := c.open_source
            open_target := hA
            contMDiffOn_toFun := hgs
            contMDiffOn_invFun := hf }, rfl, rfl, hmg⟩

/-- **The half-collar form.** A half collar of `W` whose target lies in the range of an injective
piece lifts to a half collar of the piece over it, with the same zero section image. -/
theorem exists_halfCollarLift_of_injective (hinj : Injective P.map)
    (c : PartialDiffeomorph halfCollarModel W.model (Torus × EuclideanHalfSpace 1) W.Carrier ∞)
    (hcs : c.source = halfCollarSource) (hc : c.target ⊆ range P.map) :
    ∃ c' : PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1) P.Piece ∞,
      c'.source = halfCollarSource ∧ c'.target = P.map ⁻¹' c.target ∧
      ∀ p, p ∈ halfCollarSource → P.map (c' p) = c p := by
  obtain ⟨c', hs, ht, hv⟩ := P.exists_lift_of_injective hinj c hc
  exact ⟨c', hs.trans hcs, ht, fun p hp => hv p (hcs ▸ hp)⟩

end PieceFold

end GC.GraphManifold.Assembly
