import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeTerminalBlocksFrozen
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TerminalUnionPrime

/-!
# Actual mixed vertices without solid fillings

Every nonfrozen product vertex of kind two or three is an actual zero-filling good Seifert
block on its original compact component, with its original ports. Combined with the frozen
hyperbolic certificates, a mixed stage containing no solid vertices already satisfies P4 on
its unchanged torus presentation. This is a classification branch of relative terminal
theory; stages containing inner solid fillings still require actual grouping.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.RelativeNormalization.MixedStage

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)

theorem unfilled_kind_bounds (i : Fin σ.toTorus.components.count) (hi : i ∉ σ.frozen)
    (hk : σ.kind i ≠ 1) : 2 ≤ σ.kind i ∧ σ.kind i ≤ 3 := by
  have hm := σ.kind_mem i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  omega

def unfilledPieceBlock (i : Fin σ.toTorus.components.count) (hi : i ∉ σ.frozen)
    (hk : σ.kind i ≠ 1) : PieceBlock σ.toTorus i :=
  (σ.piece i hi).pieceBlock (by have hb := σ.unfilled_kind_bounds i hi hk; omega)
    (σ.unfilled_kind_bounds i hi hk).2

theorem unfilledPieceBlock_isGood (i : Fin σ.toTorus.components.count) (hi : i ∉ σ.frozen)
    (hk : σ.kind i ≠ 1) : (σ.unfilledPieceBlock i hi hk).block.IsGoodBlock :=
  (σ.piece i hi).pieceBlock_isGoodBlock
    (by have hb := σ.unfilled_kind_bounds i hi hk; omega)
    (σ.unfilled_kind_bounds i hi hk).1 (σ.unfilled_kind_bounds i hi hk).2

theorem unfilled_ports_incompressible (i : Fin σ.toTorus.components.count)
    (hi : i ∉ σ.frozen) (hk : σ.kind i ≠ 1) :
    (σ.toTorus.pieceBoundaryTori i).incompressible :=
  σ.unfilledPieceBlock_isGood i hi hk

theorem unfilled_indecomposableNoncyclic (i : Fin σ.toTorus.components.count)
    (hi : i ∉ σ.frozen) (hk : σ.kind i ≠ 1) (x : σ.toTorus.components.piece i) :
    IndecomposableNoncyclic (FundamentalGroup (σ.toTorus.components.piece i) x) :=
  (σ.unfilledPieceBlock i hi hk).block.indecomposableNoncyclic
    (σ.unfilledPieceBlock_isGood i hi hk)
    (by change σ.kind i ≠ 0; have hb := σ.unfilled_kind_bounds i hi hk; omega) x

theorem without_solid_ports_incompressible
    (hInc : ∀ k : σ.ProtSeam, ∀ t₀,
      Function.Injective (FundamentalGroup.map (σ.toTorus.seamTorus k.val) t₀))
    (hns : ∀ i, i ∉ σ.frozen → σ.kind i ≠ 1) :
    ∀ i, (σ.toTorus.pieceBoundaryTori i).incompressible := by
  intro i
  by_cases hi : i ∈ σ.frozen
  · exact σ.frozen_ports_incompressible hInc i hi
  · exact σ.unfilled_ports_incompressible i hi (hns i hi)

theorem without_solid_indecomposableNoncyclic
    (hInc : ∀ k : σ.ProtSeam, ∀ t₀,
      Function.Injective (FundamentalGroup.map (σ.toTorus.seamTorus k.val) t₀))
    (hn : 0 < σ.toTorus.pairing.count) (hns : ∀ i, i ∉ σ.frozen → σ.kind i ≠ 1)
    (i : Fin σ.toTorus.components.count) (x : σ.toTorus.components.piece i) :
    IndecomposableNoncyclic (FundamentalGroup (σ.toTorus.components.piece i) x) := by
  by_cases hi : i ∈ σ.frozen
  · exact σ.frozen_indecomposableNoncyclic hInc hn i hi x
  · exact σ.unfilled_indecomposableNoncyclic i hi (hns i hi) x

theorem without_solid_isPrime
    (hInc : ∀ k : σ.ProtSeam, ∀ t₀,
      Function.Injective (FundamentalGroup.map (σ.toTorus.seamTorus k.val) t₀))
    (hn : 0 < σ.toTorus.pairing.count) (hns : ∀ i, i ∉ σ.frozen → σ.kind i ≠ 1) :
    IsPrime Q :=
  isPrime_of_torusPresentation σ.toTorus (σ.without_solid_ports_incompressible hInc hns)
    (σ.without_solid_indecomposableNoncyclic hInc hn hns)

end GC.Seifert.RelativeNormalization.MixedStage
