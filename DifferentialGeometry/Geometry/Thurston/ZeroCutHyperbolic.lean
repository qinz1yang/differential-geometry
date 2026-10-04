import DifferentialGeometry.Geometry.Thurston.HyperbolicPrime

/-!
# Zero-cut hyperbolic pieces

Lane K17 (open item of K18). A torus decomposition `D` of a closed `M` with no cuts
(`D.boundary.count = 0`) has a single piece, and the interior of that piece is `M`.

* `boundary_eq_empty_of_count_eq_zero`, `mem_interior_of_count_eq_zero`: with no cuts the
  carrier has empty boundary (`boundary_exhausted`).
* `interiorDiffeomorphOfCountEqZero`: the assembly identifies the carrier interior with the
  whole assembled manifold (`interior_map`), and `reconstruction` identifies that with `M`.
* `piece_eq_top_of_count_eq_zero`, `components_count_eq_one_of_count_eq_zero`: the carrier is
  connected, so every piece (clopen and nonempty) is everything and there is one piece.
* Tier 1, `pieceInteriorDiffeomorphOfCountEqZero`: the piece interior, with the interior atlas
  used by `InteriorGeometry`, is diffeomorphic to `M.Carrier`.
* Tier 2, `carrierGeometryOfCountEqZero`: an `InteriorGeometry` of the piece pulls back to a
  `GeometricStructure (𝓡 3) M.Carrier` of the same model, complete, and of finite volume when
  the model is hyperbolic.
* Tier 3, `isPrime_of_zeroCut_hyperbolic`,
  `exists_prime_geometric_decomposition_of_zeroCut_hyperbolic`: the arguments of the
  `.hyperbolic` constructor of `HyperbolicOrGraph` in the zero-cut case make `M` prime with a
  prime geometric decomposition, by K18 (`isPrime_of_hyperbolicStructure`,
  `exists_prime_geometric_decomposition_of_hyperbolic_torusDecomposition`).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

namespace GC.Topology.TorusDecomposition

universe u

private def openTopDiffeomorph {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] (U : TopologicalSpace.Opens X) (h : ∀ x : X, x ∈ U) :
    U ≃ₘ⟮I, I⟯ X where
  toFun := Subtype.val
  invFun x := ⟨x, h x⟩
  left_inv := Function.leftInverse_iff_comp.mpr rfl
  right_inv := Function.rightInverse_iff_comp.mpr rfl
  contMDiff_toFun := contMDiff_subtype_val
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff U _).mp contMDiff_id

variable {M : ConnectedClosedOrientedManifold.{u} 3} (D : TorusDecomposition M)

theorem boundary_eq_empty_of_count_eq_zero (h : D.boundary.count = 0) :
    D.carrier.model.boundary D.carrier.Carrier = ∅ := by
  rw [D.boundary.boundary_exhausted]
  exact Set.iUnion_eq_empty.mpr fun i => (Fin.cast h i).elim0

theorem isInteriorPoint_of_count_eq_zero (h : D.boundary.count = 0) (x : D.carrier.Carrier) :
    D.carrier.model.IsInteriorPoint x := by
  rcases D.carrier.model.isInteriorPoint_or_isBoundaryPoint x with hx | hx
  · exact hx
  · have hb : x ∈ D.carrier.model.boundary D.carrier.Carrier := hx
    rw [D.boundary_eq_empty_of_count_eq_zero h] at hb
    exact hb.elim

theorem mem_interior_of_count_eq_zero (h : D.boundary.count = 0) (x : D.carrier.Carrier) :
    x ∈ D.carrier.interior :=
  D.isInteriorPoint_of_count_eq_zero h x

theorem mem_interiorImage_of_count_eq_zero (h : D.boundary.count = 0)
    (q : D.boundary.Assembled) : q ∈ D.reconstructionAtlas.interiorImage := by
  induction q using Quotient.inductionOn with
  | h x =>
    have hx := D.reconstructionAtlas.interior_map ⟨x, D.mem_interior_of_count_eq_zero h x⟩
    change D.boundary.quotientMap x ∈ D.reconstructionAtlas.interiorImage
    rw [← hx]
    exact (D.reconstructionAtlas.interiorDiffeomorph _).property

def interiorDiffeomorphOfCountEqZero (h : D.boundary.count = 0) :
    D.carrier.interior ≃ₘ⟮D.carrier.model, 𝓡 3⟯ M.Carrier := by
  letI := D.reconstructionAtlas.charts
  letI := D.reconstructionAtlas.smooth
  exact (D.reconstructionAtlas.interiorDiffeomorph.trans
    (openTopDiffeomorph D.reconstructionAtlas.interiorImage
      (D.mem_interiorImage_of_count_eq_zero h))).trans D.reconstruction.val

def carrierDiffeomorphOfCountEqZero (h : D.boundary.count = 0) :
    D.carrier.Carrier ≃ₘ⟮D.carrier.model, 𝓡 3⟯ M.Carrier :=
  (openTopDiffeomorph D.carrier.interior (D.mem_interior_of_count_eq_zero h)).symm.trans
    (D.interiorDiffeomorphOfCountEqZero h)

theorem connectedSpace_carrier_of_count_eq_zero (h : D.boundary.count = 0) :
    ConnectedSpace D.carrier.Carrier :=
  (D.carrierDiffeomorphOfCountEqZero h).toHomeomorph.connectedSpace_iff.mpr inferInstance

theorem piece_eq_top_of_count_eq_zero (h : D.boundary.count = 0)
    (i : Fin D.components.count) : D.components.piece i = ⊤ := by
  have := D.connectedSpace_carrier_of_count_eq_zero h
  have := D.components.connected i
  have hc : IsClopen (D.components.piece i : Set D.carrier.Carrier) :=
    ⟨D.components.closed i, (D.components.piece i).isOpen⟩
  rcases isClopen_iff.mp hc with he | hu
  · obtain ⟨x⟩ := (inferInstance : Nonempty (D.components.piece i))
    have hx : x.val ∈ (D.components.piece i : Set D.carrier.Carrier) := x.property
    rw [he] at hx
    exact hx.elim
  · exact TopologicalSpace.Opens.coe_eq_univ.mp hu

theorem components_count_eq_one_of_count_eq_zero (h : D.boundary.count = 0) :
    D.components.count = 1 := by
  by_contra hne
  have h2 : 1 < D.components.count := by
    have := D.components.count_pos
    omega
  let i : Fin D.components.count := ⟨0, D.components.count_pos⟩
  let j : Fin D.components.count := ⟨1, h2⟩
  have hij : i ≠ j := fun hij => absurd (congrArg Fin.val hij) (by simp [i, j])
  have := D.components.connected i
  obtain ⟨x⟩ := (inferInstance : Nonempty (D.components.piece i))
  have hd : Disjoint (D.components.piece i : Set D.carrier.Carrier) (D.components.piece j) :=
    D.components.disjoint hij
  rw [D.piece_eq_top_of_count_eq_zero h i, D.piece_eq_top_of_count_eq_zero h j] at hd
  have hx : x.val ∈ ((⊤ : TopologicalSpace.Opens D.carrier.Carrier) : Set D.carrier.Carrier) :=
    trivial
  exact Set.disjoint_left.mp hd hx hx

theorem mem_pieceInterior_of_count_eq_zero (h : D.boundary.count = 0)
    (i : Fin D.components.count) (x : D.carrier.Carrier) :
    x ∈ D.carrier.pieceInterior (D.components.piece i) := by
  refine ⟨?_, D.mem_interior_of_count_eq_zero h x⟩
  rw [D.piece_eq_top_of_count_eq_zero h i]
  trivial

def pieceInteriorDiffeomorphOfCountEqZero (h : D.boundary.count = 0)
    (i : Fin D.components.count) :
    letI := Manifold.interiorChartedSpace D.carrier.model ∞
      (M := D.carrier.pieceInterior (D.components.piece i))
    letI := Manifold.interiorIsManifold D.carrier.model ∞
      (M := D.carrier.pieceInterior (D.components.piece i))
    D.carrier.pieceInterior (D.components.piece i) ≃ₘ⟮𝓡 3, 𝓡 3⟯ M.Carrier := by
  let e := (openTopDiffeomorph (D.carrier.pieceInterior (D.components.piece i))
    (D.mem_pieceInterior_of_count_eq_zero h i)).trans (D.carrierDiffeomorphOfCountEqZero h)
  letI := Manifold.interiorChartedSpace D.carrier.model ∞
    (M := D.carrier.pieceInterior (D.components.piece i))
  letI := Manifold.interiorIsManifold D.carrier.model ∞
    (M := D.carrier.pieceInterior (D.components.piece i))
  exact (Manifold.interiorAtlasDiffeomorph D.carrier.model ∞
    (M := D.carrier.pieceInterior (D.components.piece i))).symm.trans e

theorem pieceInteriorDiffeomorphOfCountEqZero_apply (h : D.boundary.count = 0)
    (i : Fin D.components.count) (x : D.carrier.pieceInterior (D.components.piece i)) :
    D.pieceInteriorDiffeomorphOfCountEqZero h i x = D.carrierDiffeomorphOfCountEqZero h x.val :=
  rfl

def carrierGeometryOfCountEqZero (h : D.boundary.count = 0) (i : Fin D.components.count)
    (g : D.carrier.InteriorGeometry (D.components.piece i)) :
    GC.Geometry.GeometricStructure (𝓡 3) M.Carrier := by
  letI := Manifold.interiorChartedSpace D.carrier.model ∞
    (M := D.carrier.pieceInterior (D.components.piece i))
  letI := Manifold.interiorIsManifold D.carrier.model ∞
    (M := D.carrier.pieceInterior (D.components.piece i))
  exact GC.Geometry.GeometricStructure.pullback (I := 𝓡 3) g
    (D.pieceInteriorDiffeomorphOfCountEqZero h i).symm

theorem carrierGeometryOfCountEqZero_model (h : D.boundary.count = 0)
    (i : Fin D.components.count) (g : D.carrier.InteriorGeometry (D.components.piece i)) :
    letI := Manifold.interiorChartedSpace D.carrier.model ∞
      (M := D.carrier.pieceInterior (D.components.piece i))
    letI := Manifold.interiorIsManifold D.carrier.model ∞
      (M := D.carrier.pieceInterior (D.components.piece i))
    (D.carrierGeometryOfCountEqZero h i g).model = g.model :=
  rfl

theorem carrierGeometryOfCountEqZero_complete (h : D.boundary.count = 0)
    (i : Fin D.components.count) (g : D.carrier.InteriorGeometry (D.components.piece i)) :
    RiemannianMetricComplete (D.carrierGeometryOfCountEqZero h i g).metric :=
  (D.carrierGeometryOfCountEqZero h i g).complete

theorem carrierGeometryOfCountEqZero_finite_volume (h : D.boundary.count = 0)
    (i : Fin D.components.count) (g : D.carrier.InteriorGeometry (D.components.piece i))
    (hg : letI := Manifold.interiorChartedSpace D.carrier.model ∞
            (M := D.carrier.pieceInterior (D.components.piece i))
          letI := Manifold.interiorIsManifold D.carrier.model ∞
            (M := D.carrier.pieceInterior (D.components.piece i))
          g.model = .hyperbolic) :
    Integral.Measure.riemannianVolumeMeasure (𝓡 3) M.Carrier
      (D.carrierGeometryOfCountEqZero h i g).metric Set.univ < ⊤ :=
  (D.carrierGeometryOfCountEqZero h i g).hyperbolic_finite_volume hg

def geometryOfCountEqZero (h : D.boundary.count = 0)
    (G : GC.Geometry.GeometricStructure (𝓡 3) M.Carrier) : D.components.Geometry := by
  intro j
  letI := Manifold.interiorChartedSpace D.carrier.model ∞
    (M := D.carrier.pieceInterior (D.components.piece j))
  letI := Manifold.interiorIsManifold D.carrier.model ∞
    (M := D.carrier.pieceInterior (D.components.piece j))
  exact G.pullback (D.pieceInteriorDiffeomorphOfCountEqZero h j)

theorem incompressible_of_count_eq_zero (h : D.boundary.count = 0) :
    D.reconstructionAtlas.Incompressible D.reconstruction :=
  fun i => (Fin.cast h i).elim0

end GC.Topology.TorusDecomposition

namespace GC.Endpoint

universe u

open GC.Topology

theorem isPrime_of_zeroCut_hyperbolic (M : ConnectedClosedOrientedManifold.{u} 3)
    (D : TorusDecomposition M) (h : D.boundary.count = 0) (i : Fin D.components.count)
    (g : D.carrier.InteriorGeometry (D.components.piece i))
    (hg : letI := Manifold.interiorChartedSpace D.carrier.model ∞
            (M := D.carrier.pieceInterior (D.components.piece i))
          letI := Manifold.interiorIsManifold D.carrier.model ∞
            (M := D.carrier.pieceInterior (D.components.piece i))
          g.model = .hyperbolic) :
    IsPrime M :=
  isPrime_of_hyperbolicStructure M (D.carrierGeometryOfCountEqZero h i g) hg

theorem exists_prime_geometric_decomposition_of_zeroCut_hyperbolic
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (D : TorusDecomposition M) (h : D.boundary.count = 0) (i : Fin D.components.count)
    (g : D.carrier.InteriorGeometry (D.components.piece i))
    (hg : letI := Manifold.interiorChartedSpace D.carrier.model ∞
            (M := D.carrier.pieceInterior (D.components.piece i))
          letI := Manifold.interiorIsManifold D.carrier.model ∞
            (M := D.carrier.pieceInterior (D.components.piece i))
          g.model = .hyperbolic) :
    ∃ P : PrimeDecomposition M,
      ∀ j : Fin P.factors.length, Nonempty (GeometricDecomposition (P.factors.get j)) :=
  exists_prime_geometric_decomposition_of_hyperbolic_torusDecomposition M
    (D.carrierGeometryOfCountEqZero h i g) hg D (D.incompressible_of_count_eq_zero h)
    (D.geometryOfCountEqZero h (D.carrierGeometryOfCountEqZero h i g))

theorem geometrizes_of_zeroCut_hyperbolic (M : ConnectedClosedOrientedManifold.{u} 3)
    (D : TorusDecomposition M) (h : D.boundary.count = 0) (i : Fin D.components.count)
    (g : D.carrier.InteriorGeometry (D.components.piece i))
    (hg : letI := Manifold.interiorChartedSpace D.carrier.model ∞
            (M := D.carrier.pieceInterior (D.components.piece i))
          letI := Manifold.interiorIsManifold D.carrier.model ∞
            (M := D.carrier.pieceInterior (D.components.piece i))
          g.model = .hyperbolic) :
    Geometrizes M := by
  obtain ⟨P, hP⟩ := exists_prime_geometric_decomposition_of_zeroCut_hyperbolic M D h i g hg
  exact ⟨{ primeData := P, geometricFactors := fun j => Classical.choice (hP j) }⟩

end GC.Endpoint
