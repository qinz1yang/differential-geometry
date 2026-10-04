import
  DifferentialGeometry.Topology.ThreeManifold.Geometrization.PrimeGeometricDecompositionWithToriTerminal
import
  DifferentialGeometry.Topology.ThreeManifold.Geometrization.PrimeGeometricDecompositionWithToriProfile

/-!
# Admission (b) with incompressible tori: the endpoint wiring

Lane BE (X38 survey row BE as corrected by reviews 20 and 26). The conclusion of admission (b)
of `GM/Refinement.lean` — a prime decomposition of `M` all of whose factors have geometric
decompositions — for the original data `M`, `D`, the incompressibility `hinj` of `D`, and the
piece profile `pieces` (`PieceProfile`, the constructor-by-constructor mirror of the frozen
`HyperbolicOrGraph`).

`exists_prime_geometric_decomposition_mixed_of_inputs` runs the relative normalisation:

1. B0's presentation `T₀` of `D` with the profile moved to the actual component carriers and the
   invariant (Inc) at the start (`exists_initialStageInputs`);
2. the initial mixed stage on `M`, all seams of `T₀` protected with exact collar ledgers
   (explicit producer hypothesis `hInit`, BR's tier R6: B0 + P1 + BA; it constructs a stage and
   asserts nothing about primeness or geometry), so (Inc) holds on it
   (`stagePred_of_collarLedger`);
3. BR's terminal expansion (`exists_terminalExpansion_of_moves` under its three frozen contracts
   `MX`, `MixedSplit`, `OrientedSingleSphere`): terminal stages with multiplicity, the `S² × S¹`
   count, the oriented reconstruction of `M`, and (Inc) on every terminal stage;
4. every terminal stage geometrizes (`geometrizes_of_terminalExpansion`): closed factors by P5
   (`hnon`) and their Seifert factor (`hC`, `hA` through X30), closed hyperbolic stages by K17,
   mixed stages through the relative terminal theory (`hRT`, Codex X57: a presentation with
   hyperbolic or good-block vertices and π₁-injective ports), BHD, P4 and X30.

No other parameter enters: `hU` is X30's `goodBlockUnionGeometry_unconditional hA hC`, the torus
mapping class input is MC4's `torusMappingClassLinear_holds`, `hfin` is X42's
`closedTriangle_finite_fundamentalGroup`. The theorem keeps the original parameters
`M`, `D`, `hinj`, `pieces`; `geometrizes_mixed_of_inputs` is the same statement in the shape of
`geometrizes_of_hyperbolicOrGraph`.

The cases that are already unconditional, in the admission's shape: all pieces hyperbolic
(`exists_prime_geometric_decomposition_of_forall_ne_graph`, BHD's theorem through the profile),
and no torus (`exists_prime_geometric_decomposition_of_count_eq_zero_of_inputs`, K17b's zero-cut
endpoint, whose graph branch keeps the existing closed inputs `hP`, `hS`, `hC`, `hA`).
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Topology GC.GraphManifold
open GC.Seifert GC.Seifert.RelativeNormalization
open scoped Manifold ContDiff Topology

universe u

namespace GC.Endpoint

theorem exists_prime_geometric_decomposition_mixed_of_inputs
    (hMX : MX.{u}) (hMS : MixedSplit.{u}) (hOS : OrientedSingleSphere.{u})
    (hRT : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (σ : MixedStage Q), σ.IsTerminal →
      σ.prot.Nonempty →
      (∀ k : σ.ProtSeam, ∀ t₀,
        Function.Injective (FundamentalGroup.map (σ.toTorus.seamTorus k.val) t₀)) →
      ∃ T : TorusPresentation.{u} (NoCuts.carrier Q), 0 < T.pairing.count ∧
        (∀ i, (T.pieceBoundaryTori i).incompressible) ∧
        ∀ i, (∃ g : T.cutCarrier.InteriorGeometry (T.components.piece i),
          letI := Manifold.interiorChartedSpace T.cutCarrier.model ∞
            (M := T.cutCarrier.pieceInterior (T.components.piece i))
          letI := Manifold.interiorIsManifold T.cutCarrier.model ∞
            (M := T.cutCarrier.pieceInterior (T.components.piece i))
          g.model = .hyperbolic) ∨
        ∃ (d : SeifertData) (B : SeifertBlock (componentCarrier T.cutCarrier T.components i) d),
          B.IsGoodBlock ∧ 0 < d.ports)
    (hInit : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3)
      (T₀ : TorusPresentation.{u} (NoCuts.carrier Q)),
      (∀ i, (∃ g : (componentCarrier T₀.cutCarrier T₀.components i).InteriorGeometry ⊤,
          letI := Manifold.interiorChartedSpace
            (componentCarrier T₀.cutCarrier T₀.components i).model ∞
            (M := (componentCarrier T₀.cutCarrier T₀.components i).pieceInterior ⊤)
          letI := Manifold.interiorIsManifold
            (componentCarrier T₀.cutCarrier T₀.components i).model ∞
            (M := (componentCarrier T₀.cutCarrier T₀.components i).pieceInterior ⊤)
          g.model = .hyperbolic) ∨
        Nonempty (RawGraphPresentation (componentCarrier T₀.cutCarrier T₀.components i))) →
      ∃ (σ : MixedStage Q) (e : Fin T₀.pairing.count ≃ σ.ProtSeam),
        ∀ j, Nonempty (CollarLedger Eq (T₀.seam j) (σ.toTorus.seam (e j).1)))
    (hnon : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
      (B : SeifertBlock (NoCuts.carrier Q) d), d.ports = 0 → d.cones.length = 3 →
        d.orbChi ≤ 0 → ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1)
    (hC : ClosedTriangleBlockGeometry.{u}) (hA : FilledPantsBlockGeometry.{u})
    (M : ConnectedClosedOrientedManifold.{u} 3) (D : TorusDecomposition M)
    (hinj : D.reconstructionAtlas.Incompressible D.reconstruction)
    (pieces : ∀ i : Fin D.components.count, PieceProfile D.carrier D.components i) :
    ∃ P : PrimeDecomposition M,
      ∀ j : Fin P.factors.length, Nonempty (GeometricDecomposition (P.factors.get j)) := by
  obtain ⟨P, hseam, -, hprof⟩ := exists_initialStageInputs M D hinj pieces
  obtain ⟨σ, e, hL⟩ := hInit M P.presentation hprof
  obtain ⟨E⟩ := exists_terminalExpansion_of_moves hMX hMS hOS ⟨M, σ⟩
  exact exists_prime_geometric_decomposition_of_geometrizes
    (geometrizes_of_terminalExpansion hRT hnon hC hA ⟨M, σ⟩ E
      (stagePred_of_collarLedger P.presentation hseam σ e hL))

theorem geometrizes_mixed_of_inputs
    (hMX : MX.{u}) (hMS : MixedSplit.{u}) (hOS : OrientedSingleSphere.{u})
    (hRT : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (σ : MixedStage Q), σ.IsTerminal →
      σ.prot.Nonempty →
      (∀ k : σ.ProtSeam, ∀ t₀,
        Function.Injective (FundamentalGroup.map (σ.toTorus.seamTorus k.val) t₀)) →
      ∃ T : TorusPresentation.{u} (NoCuts.carrier Q), 0 < T.pairing.count ∧
        (∀ i, (T.pieceBoundaryTori i).incompressible) ∧
        ∀ i, (∃ g : T.cutCarrier.InteriorGeometry (T.components.piece i),
          letI := Manifold.interiorChartedSpace T.cutCarrier.model ∞
            (M := T.cutCarrier.pieceInterior (T.components.piece i))
          letI := Manifold.interiorIsManifold T.cutCarrier.model ∞
            (M := T.cutCarrier.pieceInterior (T.components.piece i))
          g.model = .hyperbolic) ∨
        ∃ (d : SeifertData) (B : SeifertBlock (componentCarrier T.cutCarrier T.components i) d),
          B.IsGoodBlock ∧ 0 < d.ports)
    (hInit : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3)
      (T₀ : TorusPresentation.{u} (NoCuts.carrier Q)),
      (∀ i, (∃ g : (componentCarrier T₀.cutCarrier T₀.components i).InteriorGeometry ⊤,
          letI := Manifold.interiorChartedSpace
            (componentCarrier T₀.cutCarrier T₀.components i).model ∞
            (M := (componentCarrier T₀.cutCarrier T₀.components i).pieceInterior ⊤)
          letI := Manifold.interiorIsManifold
            (componentCarrier T₀.cutCarrier T₀.components i).model ∞
            (M := (componentCarrier T₀.cutCarrier T₀.components i).pieceInterior ⊤)
          g.model = .hyperbolic) ∨
        Nonempty (RawGraphPresentation (componentCarrier T₀.cutCarrier T₀.components i))) →
      ∃ (σ : MixedStage Q) (e : Fin T₀.pairing.count ≃ σ.ProtSeam),
        ∀ j, Nonempty (CollarLedger Eq (T₀.seam j) (σ.toTorus.seam (e j).1)))
    (hnon : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
      (B : SeifertBlock (NoCuts.carrier Q) d), d.ports = 0 → d.cones.length = 3 →
        d.orbChi ≤ 0 → ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1)
    (hC : ClosedTriangleBlockGeometry.{u}) (hA : FilledPantsBlockGeometry.{u})
    (M : ConnectedClosedOrientedManifold.{u} 3) (D : TorusDecomposition M)
    (hinj : D.reconstructionAtlas.Incompressible D.reconstruction)
    (pieces : ∀ i : Fin D.components.count, PieceProfile D.carrier D.components i) :
    Geometrizes M :=
  geometrizes_of_exists_prime_geometric_decomposition
    (exists_prime_geometric_decomposition_mixed_of_inputs hMX hMS hOS hRT hInit hnon hC hA
      M D hinj pieces)

theorem exists_prime_geometric_decomposition_of_forall_ne_graph
    (M : ConnectedClosedOrientedManifold.{u} 3) (D : TorusDecomposition M)
    (hinj : D.reconstructionAtlas.Incompressible D.reconstruction)
    (pieces : ∀ i : Fin D.components.count, PieceProfile D.carrier D.components i)
    (hyperbolic : ∀ i G, pieces i ≠ .graph G) :
    ∃ P : PrimeDecomposition M,
      ∀ j : Fin P.factors.length, Nonempty (GeometricDecomposition (P.factors.get j)) :=
  exists_prime_geometric_decomposition_of_forall_hyperbolic_incompressible M D hinj fun i =>
    (pieces i).exists_hyperbolic_of_forall_ne_graph (hyperbolic i)

theorem exists_prime_geometric_decomposition_of_count_eq_zero_of_inputs
    (hP : GraphPrimeStructure.{u}) (hS : SeifertRefinement.{u})
    (hC : ClosedTriangleBlockGeometry.{u}) (hA : FilledPantsBlockGeometry.{u})
    (M : ConnectedClosedOrientedManifold.{u} 3) (D : TorusDecomposition M)
    (h : D.boundary.count = 0)
    (pieces : ∀ i : Fin D.components.count, PieceProfile D.carrier D.components i) :
    ∃ P : PrimeDecomposition M,
      ∀ j : Fin P.factors.length, Nonempty (GeometricDecomposition (P.factors.get j)) :=
  exists_prime_geometric_decomposition_of_hyperbolicOrGraph_of_count_eq_zero_of_inputs hP hS hC
    (goodBlockUnionGeometry_unconditional hA hC) M D h fun i => (pieces i).toOr

end GC.Endpoint
