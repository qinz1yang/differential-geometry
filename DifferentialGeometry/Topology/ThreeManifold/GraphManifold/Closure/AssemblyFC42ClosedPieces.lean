import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificateApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyInverseSmooth
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyClosedModelApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyTorusBundleRawApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.CarrierDiffeomorphTransport
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.OldPortCollar
import DifferentialGeometry.Geometry.Collapse.ClosedCutComponent

/-!
# FC42 pieces B1 and B2: a closed piece of the certificate is the whole carrier

FC42 steps 1 and 2 (design `design-fc39-fc42-assembly-20261004.md` §3, "FC42 consumer"): a vertex
whose piece has empty boundary (a closed zero piece, or a slim piece over the circle with
`hclosed`) exhausts the connected carrier `W`.

* `PieceEmbedding.isOpen_range_of_boundary_eq_empty`, `…range_eq_univ_of_boundary_eq_empty`: the
  image of a piece without boundary is open (every point is interior and the differential is
  bijective: `image_mem_nhds_of_mfderiv_injective`) and closed (compact), so it is all of the
  connected `W`.
* `PieceEmbedding.boundary_eq_empty_of_range_eq_univ`, `PieceEmbedding.diffeomorphOfRangeEqUniv`:
  then `∂W = ∅` and the piece map is an actual diffeomorphism onto `W` (inverse smooth by
  `contMDiffOn_of_leftInverse_of_bijective_mfderiv`, corners allowed).
* **B1** `ClosedZeroPiece.boundary_eq_empty_and_exists_nonneg`: a closed zero piece gives `∂W = ∅`
  and a smooth metric on `W` with `sec ≥ 0` (the metric of `Q` pulled back along
  `W ≃ piece ≃ Q`) — the right disjunct of FC42.
* **B2** `exists_rawGraphPresentation_of_slimCircle`: a slim piece over the circle with empty
  boundary gives a raw presentation of `W`: L3 (`exists_rawGraphPresentation_of_circleBundle`) on
  the piece's own carrier, then G1 along the diffeomorphism onto `W`.

Deviations from the FC42 dry stubs (`build-logs/scratch/ASM-V3/FC42Dry.lean`): the stubs carried the
certificate, the vertex index and the equation `D.vertex k = …`, which their conclusions do not use;
these arguments are dropped (strengthening; the stub forms are the consumers in
`AssemblyFC42ClosedPiecesApplications.lean`). B2 concludes the raw presentation directly instead of
the L3 inputs transported to `W` (that transport would need a cross-model embedding composition,
and FC42 only uses the raw presentation).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace PieceEmbedding

variable {W : CompactCarrier.{u}} (P : PieceEmbedding W)

/-- An interior point of a piece goes to an interior point of `W`. -/
theorem isInteriorPoint_map {q : P.Piece} (hq : (𝓡∂ 3).IsInteriorPoint q) :
    W.model.IsInteriorPoint (P.map q) :=
  (P.smooth.mdifferentiableAt (by simp)).isInteriorPoint_of_surjective_mfderiv
    (P.mfderiv_bijective q).2 hq

theorem isInteriorPoint_of_boundary_eq_empty (h : (𝓡∂ 3).boundary P.Piece = ∅) (q : P.Piece) :
    (𝓡∂ 3).IsInteriorPoint q := by
  rcases (𝓡∂ 3).isInteriorPoint_or_isBoundaryPoint q with hq | hq
  · exact hq
  · have hb : q ∈ (𝓡∂ 3).boundary P.Piece := hq
    rw [h] at hb
    exact hb.elim

/-- The image of a piece without boundary is open. -/
theorem isOpen_range_of_boundary_eq_empty (h : (𝓡∂ 3).boundary P.Piece = ∅) :
    IsOpen (range P.map) := by
  refine isOpen_iff_mem_nhds.mpr ?_
  rintro _ ⟨q, rfl⟩
  have hq := P.isInteriorPoint_of_boundary_eq_empty h q
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := rfl
  have hn := GC.Seifert.image_mem_nhds_of_mfderiv_injective P.smooth hq (P.isInteriorPoint_map hq)
    (P.mfderiv_bijective q).1 hdim Filter.univ_mem
  rwa [image_univ] at hn

/-- **The piece exhausts `W`.** A piece without boundary in a connected carrier has image `W`. -/
theorem range_eq_univ_of_boundary_eq_empty [ConnectedSpace W.Carrier]
    (h : (𝓡∂ 3).boundary P.Piece = ∅) : range P.map = univ :=
  (IsClopen.eq_univ ⟨P.isClosed_range, P.isOpen_range_of_boundary_eq_empty h⟩ P.range_nonempty)

/-- A piece without boundary whose image is `W` forces `∂W = ∅`. -/
theorem boundary_eq_empty_of_range_eq_univ (h : (𝓡∂ 3).boundary P.Piece = ∅)
    (hr : range P.map = univ) : W.model.boundary W.Carrier = ∅ := by
  refine eq_empty_of_forall_notMem fun x hx => ?_
  obtain ⟨q, rfl⟩ : x ∈ range P.map := hr ▸ mem_univ x
  exact (W.model.isInteriorPoint_iff_not_isBoundaryPoint _).1
    (P.isInteriorPoint_map (P.isInteriorPoint_of_boundary_eq_empty h q)) hx

theorem bijective_map_of_range_eq_univ (hr : range P.map = univ) : Bijective P.map :=
  ⟨P.injective, range_eq_univ.mp hr⟩

/-- The piece map of a piece with image `W`, as a homeomorphism. -/
def homeomorphOfRangeEqUniv (hr : range P.map = univ) : P.Piece ≃ₜ W.Carrier :=
  P.continuous_map.homeoOfEquivCompactToT2 (f := Equiv.ofBijective P.map
    (P.bijective_map_of_range_eq_univ hr))

/-- **The piece map of a piece with image `W` is a diffeomorphism.** -/
def diffeomorphOfRangeEqUniv (hr : range P.map = univ) :
    P.Piece ≃ₘ⟮𝓡∂ 3, W.model⟯ W.Carrier where
  toEquiv := Equiv.ofBijective P.map (P.bijective_map_of_range_eq_univ hr)
  contMDiff_toFun := P.smooth
  contMDiff_invFun := by
    rw [← contMDiffOn_univ]
    exact contMDiffOn_of_leftInverse_of_bijective_mfderiv isOpen_univ isOpen_univ
      P.smooth.contMDiffOn (mapsTo_univ _ _) (mapsTo_univ _ _)
      (fun y _ => (Equiv.ofBijective P.map (P.bijective_map_of_range_eq_univ hr)).apply_symm_apply y)
      (fun x _ => (Equiv.ofBijective P.map (P.bijective_map_of_range_eq_univ hr)).symm_apply_apply x)
      (P.homeomorphOfRangeEqUniv hr).symm.continuous.continuousOn
      (fun x _ => P.mfderiv_bijective x)

@[simp]
theorem diffeomorphOfRangeEqUniv_apply (hr : range P.map = univ) (q : P.Piece) :
    P.diffeomorphOfRangeEqUniv hr q = P.map q :=
  rfl

end PieceEmbedding

/-- **B1 (FC42 step 1).** A closed zero piece in a connected carrier exhausts it; then `∂W = ∅` and
`W` carries a smooth metric with nonnegative sectional curvature (the metric of `Q` pulled back
along `W ≃ piece ≃ Q`). -/
theorem ClosedZeroPiece.boundary_eq_empty_and_exists_nonneg {W : CompactCarrier.{u}}
    [ConnectedSpace W.Carrier] (C : ClosedZeroPiece W) :
    W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
      DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow g' 0 := by
  have hr := C.piece.range_eq_univ_of_boundary_eq_empty C.boundary_empty
  refine ⟨C.boundary_eq_empty_of_range_eq_univ hr, ?_⟩
  let Φ : W.Carrier ≃ₘ⟮W.model, 𝓡 3⟯ C.Q.Carrier :=
    (C.piece.diffeomorphOfRangeEqUniv hr).symm.trans C.ident
  exact ⟨DifferentialGeometry.Diffeomorph.pullbackMetricCross C.metric Φ,
    DifferentialGeometry.Geometry.Collapse.sectionalBoundedBelow_pullbackMetricCross C.metric Φ
      C.nonneg⟩

/-- **B2 (FC42 step 2).** A slim piece over the circle with empty boundary in a connected carrier
gives a raw graph presentation of the carrier: L3 on the piece's carrier (its fibre over `1` is an
actual torus or sphere), then G1 along the diffeomorphism of the piece onto `W`. -/
theorem exists_rawGraphPresentation_of_slimCircle {W : CompactCarrier.{u}}
    [ConnectedSpace W.Carrier] (P : PieceEmbedding W) (p : P.Piece → Circle)
    (hp : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ p) (hsub : ∀ q, Surjective (mfderiv (𝓡∂ 3) (𝓡 1) p q))
    (fib : SlimFibre P p) (hcl : (𝓡∂ 3).boundary P.Piece = ∅) :
    Nonempty (RawGraphPresentation W) := by
  have hr := P.range_eq_univ_of_boundary_eq_empty hcl
  have hfibre : (∃ f : Torus → P.toCarrier.Carrier,
      IsSmoothEmbedding torusModel P.toCarrier.model ∞ f ∧ range f = p ⁻¹' {1}) ∨
      ∃ f : ClosureSphere.{u} → P.toCarrier.Carrier,
        IsSmoothEmbedding (𝓡 2) P.toCarrier.model ∞ f ∧ range f = p ⁻¹' {1} := by
    cases fib with
    | sphere f hf hr' => exact Or.inr ⟨f, hf, hr'⟩
    | torus f hf hr' => exact Or.inl ⟨f, hf, hr'⟩
  obtain ⟨G⟩ := exists_rawGraphPresentation_of_circleBundle P.toCarrier hcl p hp hsub hfibre
  exact nonempty_rawGraphPresentation_of_carrierDiffeomorph G
    (P.diffeomorphOfRangeEqUniv hr)

end GC.GraphManifold.Assembly
