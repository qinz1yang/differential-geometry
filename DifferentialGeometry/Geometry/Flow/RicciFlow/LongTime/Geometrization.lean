import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.LateDecomposition
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.RouteWLateSequenceC11R
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12Enhanced
import DifferentialGeometry.Topology.ThreeManifold.TorusCut.Decomposition

/-!
# Geometrization of closed oriented three-manifolds

`geometrization` states the geometric conclusion directly: a finite nonempty list of prime
factors reconstructs the original manifold as an oriented connected sum. Each factor has a
finite torus decomposition whose actual tori are smooth, embedded, pairwise disjoint and
injective on fundamental groups, and every cut-piece interior has a Thurston geometry.

The model and metric are explicit witnesses. The metric is complete and has a local
isometric atlas modelled on one of the eight values of `GC.Geometry.ThurstonModel`: spherical,
Euclidean, hyperbolic, sphere times line, hyperbolic plane times line, the universal cover
of SL(2, ℝ), Nil or Sol. The conclusion explicitly requires finite total Riemannian volume
whenever the model is hyperbolic. The metric is on the actual cut-piece interior, with
its inherited interior smooth structure.

`geometrization_certificate` retains the construction certificate for implementation consumers.
No minimality or uniqueness of the torus decomposition is asserted.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff
namespace GC.Endpoint
universe u

/-- The construction certificate underlying geometrization, including its reconstruction data. -/
theorem geometrization_certificate (M : ConnectedClosedOrientedManifold.{u} 3) :
    Nonempty (GeometrizationCertificate M) := by
  obtain ⟨g⟩ := Geometry.nonempty_smoothRiemannianMetric_of_compact (𝓡 3) (M := M.Carrier)
  exact GC.LongTime.Ch11.geometrizes_of_metric_C11R
    GC.LongTime.exists_surgery_with_decaying_accuracy_enhanced M g

/-- Every closed, connected, oriented smooth three-manifold is a finite connected sum of
prime manifolds. Each prime factor can be cut along finitely many pairwise disjoint smooth
incompressible tori into pieces whose interiors carry complete Thurston geometries; the
hyperbolic interiors have finite volume.

`D` is an actual smooth torus cutting and reconstruction of the given factor `P`. The family
`T` consists of its tori in `P`. For every actual piece interior the conclusion supplies
a model `k : ThurstonModel` and a smooth Riemannian metric `g`, its completeness and local
isometric model atlas, and finite total volume when `k` is hyperbolic. The torus family may
be empty; the inherited interior smooth structure is used throughout. -/
theorem geometrization (M : ConnectedClosedOrientedManifold.{u} 3) :
    ∃ factors : List (ConnectedClosedOrientedManifold.{u} 3),
      factors ≠ [] ∧
      (∀ P ∈ factors, IsPrime P) ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (finiteConnectedSum factors).toClosedOrientedManifold M.toClosedOrientedManifold) ∧
      ∀ P ∈ factors, ∃ D : GC.Topology.TorusDecomposition P,
        let T := D.reconstructionAtlas.torusInPrime D.reconstruction
        (∀ i, ContMDiff torusModel (𝓡 3) ∞ (T i) ∧ _root_.Topology.IsEmbedding (T i)) ∧
        Pairwise (fun i j => Disjoint (Set.range (T i)) (Set.range (T j))) ∧
        (∀ i x, Function.Injective (FundamentalGroup.map (T i) x)) ∧
        ∀ j : Fin D.components.count,
          let := Manifold.interiorChartedSpace D.carrier.model ∞
            (M := D.carrier.pieceInterior (D.components.piece j))
          let := Manifold.interiorIsManifold D.carrier.model ∞
            (M := D.carrier.pieceInterior (D.components.piece j))
          ∃ (k : GC.Geometry.ThurstonModel)
            (g : SmoothRiemannianMetric (𝓡 3)
              (D.carrier.pieceInterior (D.components.piece j))),
            RiemannianMetricComplete g ∧ GC.Geometry.HasThurstonAtlas g k ∧
              (k = .hyperbolic → Integral.Measure.riemannianVolumeMeasure (𝓡 3)
                (D.carrier.pieceInterior (D.components.piece j)) g Set.univ < ⊤) := by
  obtain ⟨C⟩ := geometrization_certificate M
  refine ⟨C.primeData.factors, C.primeData.factors_nonempty, C.primeData.prime,
    ⟨C.primeData.reconstruction⟩, ?_⟩
  intro P hP
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hP
  subst P
  let G := C.geometricFactors i
  let D : GC.Topology.TorusDecomposition (C.primeData.factors.get i) :=
    { carrier := G.carrier
      components := G.components
      boundary := G.boundary
      reconstructionAtlas := G.assembly
      reconstruction := G.reconstruction
      leftPiece := G.leftPiece
      rightPiece := G.rightPiece
      left_owned := G.left_owned
      right_owned := G.right_owned }
  refine ⟨D, ?_, ?_, G.incompressible, ?_⟩
  · intro j
    exact ⟨G.assembly.torusInPrime_smooth G.reconstruction j,
      G.assembly.torusInPrime_isEmbedding G.reconstruction j⟩
  · intro j k hjk
    rw [Set.disjoint_left]
    rintro x ⟨a, rfl⟩ ⟨b, h⟩
    have h' : G.boundary.torusMap k b = G.boundary.torusMap j a :=
      G.reconstruction.val.injective h
    exact (Set.disjoint_left.mp (G.boundary.torusMap_pairwise_disjoint hjk))
      ⟨a, rfl⟩ ⟨b, h'⟩
  · intro j
    let := Manifold.interiorChartedSpace D.carrier.model ∞
      (M := D.carrier.pieceInterior (D.components.piece j))
    let := Manifold.interiorIsManifold D.carrier.model ∞
      (M := D.carrier.pieceInterior (D.components.piece j))
    let g := G.geometry j
    exact ⟨g.model, g.metric, g.complete, g.atlas, g.hyperbolic_finite_volume⟩

/-- The certificate formulation, retained for existing construction consumers. -/
theorem geometrization_conjecture : GeometrizationConjecture.{u} :=
  geometrization_certificate

/-- The unbundled smooth certificate formulation. -/
theorem smooth_geometrization_conjecture : SmoothGeometrizationConjecture.{u} :=
  geometrizationConjecture_iff_smooth.mp geometrization_conjecture

end GC.Endpoint
