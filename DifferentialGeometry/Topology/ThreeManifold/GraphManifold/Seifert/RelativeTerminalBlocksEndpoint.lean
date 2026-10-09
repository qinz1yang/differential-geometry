import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeTerminalBlocksInitial
import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeTerminalBlocksPorts
import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeTerminalBlocksVertices
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MultiSeamInjective

/-!
# Actual relative terminal blocks for the mixed endpoint

The finite actual grouping preserves the protected signed seams and frozen compact pieces.
Every remaining port is incompressible, every vertex group is freely indecomposable and
noncyclic at every basepoint, and every remaining seam is injective in the ambient group.
The main existence theorem has the exact terminal-theory type consumed by lane BE.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.Topology (componentCarrier)
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.RelativeNormalization

namespace RelativeGroupedPresentation

variable {Q : ConnectedClosedOrientedManifold.{u} 3} {σ : MixedStage Q}
  (B : RelativeGroupedPresentation σ)
  (hInc : ∀ k : σ.ProtSeam, ∀ t,
    Function.Injective (FundamentalGroup.map (σ.toTorus.seamTorus k.val) t))
  (hp : σ.prot.Nonempty)

include hp in
theorem pairing_pos : 0 < B.base.pairing.count := by
  obtain ⟨j, hj⟩ := hp
  exact Fin.pos (B.protectedIndex ⟨j, hj⟩)

theorem frozen_hyperbolic (f : σ.Frozen) :
    ∃ g : B.base.cutCarrier.InteriorGeometry (B.base.components.piece (B.frozen f)),
      letI := Manifold.interiorChartedSpace B.base.cutCarrier.model ∞
        (M := B.base.cutCarrier.pieceInterior (B.base.components.piece (B.frozen f)))
      letI := Manifold.interiorIsManifold B.base.cutCarrier.model ∞
        (M := B.base.cutCarrier.pieceInterior (B.base.components.piece (B.frozen f)))
      g.model = .hyperbolic := by
  obtain ⟨g, hg⟩ := σ.hyperbolic f.val f.property
  let := Manifold.interiorChartedSpace σ.toTorus.cutCarrier.model ∞
    (M := σ.toTorus.cutCarrier.pieceInterior (σ.toTorus.components.piece f.val))
  let := Manifold.interiorIsManifold σ.toTorus.cutCarrier.model ∞
    (M := σ.toTorus.cutCarrier.pieceInterior (σ.toTorus.components.piece f.val))
  refine ⟨(B.transfer f).relativeGeometry g, ?_⟩
  change g.model = .hyperbolic
  exact hg

include hInc in
theorem ports_incompressible (i : Fin B.base.components.count) :
    (B.base.pieceBoundaryTori i).incompressible := by
  classical
  by_cases hf : ∃ f, B.frozen f = i
  · obtain ⟨f, rfl⟩ := hf
    exact (B.transfer f).incompressible (σ.frozen_ports_incompressible hInc f.val f.property)
  · have hi : ∀ f, B.frozen f ≠ i := fun f he => hf ⟨f, he⟩
    exact (B.block i hi).val.relativePorts_incompressible ((B.block i hi).property _ _)

include hInc hp in
theorem vertex_indecomposableNoncyclic (i : Fin B.base.components.count)
    (x : B.base.components.piece i) :
    IndecomposableNoncyclic (FundamentalGroup (B.base.components.piece i) x) := by
  classical
  by_cases hf : ∃ f, B.frozen f = i
  · obtain ⟨f, rfl⟩ := hf
    obtain ⟨g, hg⟩ := B.frozen_hyperbolic f
    exact B.base.indecomposableNoncyclic_of_hyperbolic _ (B.ports_incompressible hInc _)
      (B.base.card_ownedSide_pos (B.pairing_pos hp) _) g hg x
  · have hi : ∀ f, B.frozen f ≠ i := fun f he => hf ⟨f, he⟩
    exact (B.block i hi).val.relativeVertex_indecomposableNoncyclic
      ((B.block i hi).property _ _) (B.pairing_pos hp) x

include hInc in
theorem remaining_seam_injective (j : Fin B.base.pairing.count) (t : Torus) :
    Function.Injective (FundamentalGroup.map (B.base.seamTorus j) t) :=
  B.base.injective_seamTorus_of_ports B.base.externalCount_eq_zero (B.ports_incompressible hInc) j t

include B hInc hp in
theorem isPrime : IsPrime Q :=
  isPrime_of_torusPresentation B.base (B.ports_incompressible hInc)
    (B.vertex_indecomposableNoncyclic hInc hp)

include hp in
theorem vertex_profile (i : Fin B.base.components.count) :
    (∃ g : B.base.cutCarrier.InteriorGeometry (B.base.components.piece i),
      letI := Manifold.interiorChartedSpace B.base.cutCarrier.model ∞
        (M := B.base.cutCarrier.pieceInterior (B.base.components.piece i))
      letI := Manifold.interiorIsManifold B.base.cutCarrier.model ∞
        (M := B.base.cutCarrier.pieceInterior (B.base.components.piece i))
      g.model = .hyperbolic) ∨
    ∃ (d : SeifertData)
      (C : SeifertBlock (componentCarrier B.base.cutCarrier B.base.components i) d),
      C.IsGoodBlock ∧ 0 < d.ports := by
  classical
  by_cases hf : ∃ f, B.frozen f = i
  · obtain ⟨f, rfl⟩ := hf
    exact Or.inl (B.frozen_hyperbolic f)
  · have hi : ∀ f, B.frozen f ≠ i := fun f he => hf ⟨f, he⟩
    let C := (B.block i hi).val
    exact Or.inr ⟨C.data, C.block, (B.block i hi).property _ _,
      C.relativeData_ports_pos (B.pairing_pos hp)⟩

end RelativeGroupedPresentation

theorem relativeTerminal_to_blockPresentation
    (Q : ConnectedClosedOrientedManifold.{u} 3) (σ : MixedStage Q) (ht : σ.IsTerminal)
    (hp : σ.prot.Nonempty)
    (hInc : ∀ k : σ.ProtSeam, ∀ t₀,
      Function.Injective (FundamentalGroup.map (σ.toTorus.seamTorus k.val) t₀)) :
    ∃ T : TorusPresentation.{u} (NoCuts.carrier Q), 0 < T.pairing.count ∧
      (∀ i, (T.pieceBoundaryTori i).incompressible) ∧
      ∀ i, (∃ g : T.cutCarrier.InteriorGeometry (T.components.piece i),
        letI := Manifold.interiorChartedSpace T.cutCarrier.model ∞
          (M := T.cutCarrier.pieceInterior (T.components.piece i))
        letI := Manifold.interiorIsManifold T.cutCarrier.model ∞
          (M := T.cutCarrier.pieceInterior (T.components.piece i))
        g.model = .hyperbolic) ∨
      ∃ (d : SeifertData) (B : SeifertBlock (componentCarrier T.cutCarrier T.components i) d),
        B.IsGoodBlock ∧ 0 < d.ports := by
  obtain ⟨B⟩ := σ.relativeTerminal_exists_groupedPresentation hInc ht hp
  exact ⟨B.base, B.pairing_pos hp, B.ports_incompressible hInc, B.vertex_profile hp⟩

theorem relativeTerminal_isPrime
    (Q : ConnectedClosedOrientedManifold.{u} 3) (σ : MixedStage Q) (ht : σ.IsTerminal)
    (hp : σ.prot.Nonempty)
    (hInc : ∀ k : σ.ProtSeam, ∀ t,
      Function.Injective (FundamentalGroup.map (σ.toTorus.seamTorus k.val) t)) : IsPrime Q := by
  obtain ⟨B⟩ := σ.relativeTerminal_exists_groupedPresentation hInc ht hp
  exact B.isPrime hInc hp

theorem relativeTerminal_exists_preservedPresentation
    (Q : ConnectedClosedOrientedManifold.{u} 3) (σ : MixedStage Q) (ht : σ.IsTerminal)
    (hp : σ.prot.Nonempty)
    (hInc : ∀ k : σ.ProtSeam, ∀ t,
      Function.Injective (FundamentalGroup.map (σ.toTorus.seamTorus k.val) t)) :
    ∃ B : RelativeGroupedPresentation σ,
      (∀ i, (B.base.pieceBoundaryTori i).incompressible) ∧
      (∀ i (x : B.base.components.piece i),
        IndecomposableNoncyclic (FundamentalGroup (B.base.components.piece i) x)) ∧
      ∀ j t, Function.Injective (FundamentalGroup.map (B.base.seamTorus j) t) := by
  obtain ⟨B⟩ := σ.relativeTerminal_exists_groupedPresentation hInc ht hp
  exact ⟨B, B.ports_incompressible hInc, B.vertex_indecomposableNoncyclic hInc hp,
    B.remaining_seam_injective hInc⟩

end GC.Seifert.RelativeNormalization
