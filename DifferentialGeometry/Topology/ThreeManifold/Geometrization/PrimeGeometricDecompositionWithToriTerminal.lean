import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeSeifertNormalizationStep
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.HyperbolicPieceGroupFI
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusMappingClassConsumers
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTerminalPrimeNonneg
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TerminalUnionPrime
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.FiniteConnectedSum

/-!
# Terminal stages of the relative normalisation geometrize

Lane BE, deliverable 2, consumer half (X38 survey row BE, reviews 20 §9 and 26 §1.2, §8.2). The
relative normalisation of lane BR ends in terminal mixed stages `⟨Q, σ⟩` whose protected seam
tori are π₁-injective in `Q` (the invariant (Inc), `stagePred`). Each terminal stage gives a
prime decomposition of `Q` with geometric factors, in three branches:

* Closed factor (`σ.prot = ∅`, `σ.frozen = ∅`): the move-free elementary presentation is P0a's
  `TerminalPresentation` (`MixedStage.terminalPresentation`); `Q` is prime by P5's
  `TerminalPresentation.isPrime_of_nonneg` (only the three-cone certificate `hnon` remains) and
  has a geometric decomposition from its Seifert factor (`geometricDecomposition_of_seifertFactor`
  with X30's `goodBlockUnionGeometry_unconditional hA hC`).
* Closed hyperbolic stage (`σ.prot = ∅`, `σ.frozen ≠ ∅`): it has no seam
  (`frozen_eq_empty_of_prot_eq_empty`), so its decomposition is a zero-cut decomposition with a
  hyperbolic piece (K17's `exists_prime_geometric_decomposition_of_zeroCut_of_hyperbolic`).
* Mixed stage (`σ.prot` nonempty): the relative terminal theory (Codex X57, explicit hypothesis
  `hRT`, a producer of a presentation, never of primeness) regroups it into a torus presentation
  `T` of `Q` with at least one seam, π₁-injective ports, and every vertex either a hyperbolic
  piece or a good Seifert block with ports. The vertex groups are then freely indecomposable and
  non-cyclic at every basepoint — hyperbolic vertices by BHD's
  `TorusPresentation.indecomposableNoncyclic_of_hyperbolic`, good blocks by P4's
  `SeifertBlock.indecomposableNoncyclic` — so `Q` is prime by P4
  (`isPrime_of_torusPresentation`); the vertex geometries (the hyperbolic one, X30's open block
  geometry `SeifertBlock.exists_openInteriorGeometry` moved to the piece) assemble along
  `T.toTorusDecomposition` (`geometrizes_of_blockPresentation`).

`geometrizes_of_terminalExpansion` assembles a terminal `Expansion` of BR: every terminal stage
geometrizes, the `S² × S¹` summands are standard factors, and the oriented reconstruction carries
a geometrization of the connected sum to the source. The invariant (Inc) of the source stage
holds as soon as its protected seams track, by collar ledgers, π₁-injective seams of a
presentation (`stagePred_of_collarLedger`).
-/

set_option autoImplicit false

noncomputable section
open Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Topology GC.GraphManifold
open GC.Seifert GC.Seifert.RelativeNormalization
open scoped Manifold ContDiff Topology

universe u

namespace GC.Endpoint

theorem geometrizes_of_exists_prime_geometric_decomposition
    {Q : ConnectedClosedOrientedManifold.{u} 3}
    (h : ∃ P : PrimeDecomposition Q,
      ∀ j : Fin P.factors.length, Nonempty (GeometricDecomposition (P.factors.get j))) :
    Geometrizes Q := by
  obtain ⟨P, hP⟩ := h
  exact ⟨{ primeData := P, geometricFactors := fun j => Classical.choice (hP j) }⟩

theorem exists_prime_geometric_decomposition_of_isPrime_of_nonempty
    {Q : ConnectedClosedOrientedManifold.{u} 3} (hQ : IsPrime Q)
    (hG : Nonempty (GeometricDecomposition Q)) :
    ∃ P : PrimeDecomposition Q,
      ∀ j : Fin P.factors.length, Nonempty (GeometricDecomposition (P.factors.get j)) := by
  refine ⟨PrimeDecomposition.ofIsPrime Q hQ, ?_⟩
  rintro ⟨_ | n, hn⟩
  · exact hG
  · exact absurd hn (by simp [PrimeDecomposition.ofIsPrime_factors])

theorem geometrizes_sphereSummand : Geometrizes sphereSummand.{u} := by
  have h : isStandardFactor sphereSummand.{u} :=
    isStandardFactor_ulift isStandardFactor_sphereTwoTimesCircleLift
  exact geometrizes_of_exists_prime_geometric_decomposition
    (exists_prime_geometric_decomposition_of_isPrime_of_nonempty
      (isPrime_of_isStandardFactor _ h) (geometricDecomposition_of_isStandardFactor h))

theorem exists_prime_geometric_decomposition_of_blockPresentation
    (hA : FilledPantsBlockGeometry.{u}) {Q : ConnectedClosedOrientedManifold.{u} 3}
    (T : TorusPresentation.{u} (NoCuts.carrier Q)) (hcount : 0 < T.pairing.count)
    (hports : ∀ i, (T.pieceBoundaryTori i).incompressible)
    (hpieces : ∀ i,
      (∃ g : T.cutCarrier.InteriorGeometry (T.components.piece i),
        letI := Manifold.interiorChartedSpace T.cutCarrier.model ∞
          (M := T.cutCarrier.pieceInterior (T.components.piece i))
        letI := Manifold.interiorIsManifold T.cutCarrier.model ∞
          (M := T.cutCarrier.pieceInterior (T.components.piece i))
        g.model = .hyperbolic) ∨
      ∃ (d : SeifertData) (B : SeifertBlock (componentCarrier T.cutCarrier T.components i) d),
        B.IsGoodBlock ∧ 0 < d.ports) :
    ∃ P : PrimeDecomposition Q,
      ∀ j : Fin P.factors.length, Nonempty (GeometricDecomposition (P.factors.get j)) := by
  have hvert : ∀ i (x : T.components.piece i),
      IndecomposableNoncyclic (FundamentalGroup (T.components.piece i) x) := by
    intro i x
    rcases hpieces i with ⟨g, hg⟩ | ⟨d, B, hB, hp⟩
    · exact T.indecomposableNoncyclic_of_hyperbolic i (hports i) (T.card_ownedSide_pos hcount i)
        g hg x
    · exact B.indecomposableNoncyclic hB hp.ne' x
  have hgeo : ∀ i, Nonempty (T.cutCarrier.InteriorGeometry (T.components.piece i)) := by
    intro i
    rcases hpieces i with ⟨g, -⟩ | ⟨d, B, hB, hp⟩
    · exact ⟨g⟩
    · obtain ⟨G⟩ := B.exists_openInteriorGeometry hB hp torusMappingClassLinear_holds hA
      exact ⟨transportInteriorGeometry
        (componentInteriorDiffeomorph T.cutCarrier T.components i).symm G⟩
  exact exists_prime_geometric_decomposition_of_isPrime_of_geometry Q
    (isPrime_of_torusPresentation T hports hvert) T.toTorusDecomposition
    (T.incompressible_toTorusDecomposition_of_ports hports) fun i => Classical.choice (hgeo i)

theorem exists_prime_geometric_decomposition_of_closedTerminal
    (hnon : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
      (B : SeifertBlock (NoCuts.carrier Q) d), d.ports = 0 → d.cones.length = 3 →
        d.orbChi ≤ 0 → ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1)
    (hC : ClosedTriangleBlockGeometry.{u}) (hA : FilledPantsBlockGeometry.{u})
    {Q : ConnectedClosedOrientedManifold.{u} 3} (T : TerminalPresentation Q) :
    ∃ P : PrimeDecomposition Q,
      ∀ j : Fin P.factors.length, Nonempty (GeometricDecomposition (P.factors.get j)) :=
  exists_prime_geometric_decomposition_of_isPrime_of_nonempty (T.isPrime_of_nonneg hnon)
    (geometricDecomposition_of_seifertFactor hC (goodBlockUnionGeometry_unconditional hA hC)
      T.factor)

theorem exists_prime_geometric_decomposition_of_frozen_of_prot_eq_empty
    {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q) (hp : σ.prot = ∅)
    (hf : σ.frozen ≠ ∅) :
    ∃ P : PrimeDecomposition Q,
      ∀ j : Fin P.factors.length, Nonempty (GeometricDecomposition (P.factors.get j)) := by
  have hcount : σ.toTorus.pairing.count = 0 := by
    by_contra h
    exact hf (σ.frozen_eq_empty_of_prot_eq_empty hp (Nat.pos_of_ne_zero h))
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hf
  exact exists_prime_geometric_decomposition_of_zeroCut_of_hyperbolic Q
    σ.toTorus.toTorusDecomposition hcount i (σ.hyperbolic i hi)

theorem exists_prime_geometric_decomposition_of_isTerminal
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
    (hnon : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
      (B : SeifertBlock (NoCuts.carrier Q) d), d.ports = 0 → d.cones.length = 3 →
        d.orbChi ≤ 0 → ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1)
    (hC : ClosedTriangleBlockGeometry.{u}) (hA : FilledPantsBlockGeometry.{u})
    {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q) (ht : σ.IsTerminal)
    (hInc : ∀ k : σ.ProtSeam, ∀ t₀,
      Function.Injective (FundamentalGroup.map (σ.toTorus.seamTorus k.val) t₀)) :
    ∃ P : PrimeDecomposition Q,
      ∀ j : Fin P.factors.length, Nonempty (GeometricDecomposition (P.factors.get j)) := by
  rcases σ.prot.eq_empty_or_nonempty with hp | hne
  · by_cases hf : σ.frozen = ∅
    · exact exists_prime_geometric_decomposition_of_closedTerminal hnon hC hA
        (σ.terminalPresentation hf hp ht)
    · exact exists_prime_geometric_decomposition_of_frozen_of_prot_eq_empty σ hp hf
  · obtain ⟨T, hcount, hports, hpieces⟩ := hRT Q σ ht hne hInc
    exact exists_prime_geometric_decomposition_of_blockPresentation hA T hcount hports hpieces

theorem stagePred_of_collarLedger {Q : ConnectedClosedOrientedManifold.{u} 3}
    (T₀ : TorusPresentation.{u} (NoCuts.carrier Q))
    (hT₀ : ∀ k t₀, Function.Injective (FundamentalGroup.map (T₀.seamTorus k) t₀))
    (σ : MixedStage Q) (e : Fin T₀.pairing.count ≃ σ.ProtSeam)
    (hL : ∀ j, Nonempty (CollarLedger Eq (T₀.seam j) (σ.toTorus.seam (e j).1))) :
    ∀ p, stagePred ⟨Q, σ⟩ p := by
  rintro ⟨k | i⟩
  · obtain ⟨j, rfl⟩ := e.surjective k
    obtain ⟨L⟩ := hL j
    have heq : σ.toTorus.seamTorus (e j).1 =
        (T₀.seamTorus j).comp (L.reparam.toHomeomorph : C(Torus, Torus)) := by
      ext t
      exact (L.tracked_zero t).symm
    change ∀ t₀, Function.Injective (FundamentalGroup.map (σ.toTorus.seamTorus (e j).1) t₀)
    rw [heq, forall_injective_comp_homeomorph_iff]
    exact hT₀ j
  · trivial

theorem geometrizes_of_terminalExpansion
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
    (hnon : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
      (B : SeifertBlock (NoCuts.carrier Q) d), d.ports = 0 → d.cones.length = 3 →
        d.orbChi ≤ 0 → ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1)
    (hC : ClosedTriangleBlockGeometry.{u}) (hA : FilledPantsBlockGeometry.{u}) (s : Stage.{u})
    (E : Expansion Sigma.fst sphereSummand stageProt stagePred (fun t : Stage.{u} => t.2.IsTerminal)
      s)
    (hs : ∀ p, stagePred s p) : Geometrizes s.1 := by
  have hall : ∀ q : Σ i, stageProt (E.stage i), stagePred (E.stage q.1) q.2 := by
    intro q
    obtain ⟨p, rfl⟩ := E.seam.surjective q
    exact (E.seam_pred p).mp (hs p)
  have hstage : ∀ i, Geometrizes (E.stage i).1 := fun i =>
    geometrizes_of_exists_prime_geometric_decomposition
      (exists_prime_geometric_decomposition_of_isTerminal hRT hnon hC hA (E.stage i).2 (E.good i)
        fun k => hall ⟨i, ⟨.inl k⟩⟩)
  have hsum : Geometrizes (finiteConnectedSum (E.enum.map (Sigma.fst ∘ E.stage) ++
      List.replicate E.count sphereSummand)) := by
    refine geometrizes_finiteConnectedSum _ fun P hP => ?_
    rcases List.mem_append.mp hP with h | h
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp h
      exact hstage i
    · rw [List.eq_of_mem_replicate h]
      exact geometrizes_sphereSummand
  obtain ⟨f⟩ := E.reconstruction
  exact geometrizes_of_orientedDiffeomorph f hsum

end GC.Endpoint
