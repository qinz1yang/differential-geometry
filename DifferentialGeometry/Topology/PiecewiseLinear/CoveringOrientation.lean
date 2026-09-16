import DifferentialGeometry.Topology.PiecewiseLinear.CoveringTriangulation
import DifferentialGeometry.Topology.PiecewiseLinear.Orientation
import DifferentialGeometry.Topology.PiecewiseLinear.OrientationCocycle

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
  {X' : Type u} [TopologicalSpace X'] {p : X' → K.space}
  [Finite (coveringVertex K p)]

open Classical in
noncomputable instance finite_coveringComplex_faces : Finite (coveringComplex K p).faces :=
  (coveringComplex_faces_finite K p).to_subtype

open Classical in
theorem IsCombinatorialManifold.coveringComplex
    (hp : IsCoveringMap p) {n : ℕ} (hK : IsCombinatorialManifold n K) :
    IsCombinatorialManifold n (coveringComplex K p) := by
  let _ : DecidableEq (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))) :=
    Classical.decEq _
  cases n with
  | zero =>
      intro z hz
      obtain ⟨v, rfl⟩ := exists_coveringVertexPoint_of_singleton_mem K p hz
      rw [Set.eq_empty_iff_forall_notMem]
      intro q hq
      have hbase := (coveringVertexLink_isGlueIso K p hp v).image₂ q hq
      rw [hK (coveringVertex.base v) (coveringVertex.singleton_base_mem_faces v)] at hbase
      exact hbase
  | succ n =>
      intro z hz
      obtain ⟨v, rfl⟩ := exists_coveringVertexPoint_of_singleton_mem K p hz
      exact (hK (coveringVertex.base v) (coveringVertex.singleton_base_mem_faces v)).of_isPLHomeomorphOn
        (coveringVertexLink_isGlueIso K p hp v).isPLHomeomorphOn

open Classical in
noncomputable def CoherentOrientation.coveringVertexLink {n : ℕ}
    (v : coveringVertex K p)
    (o : CoherentOrientation n
      (SimplicialComplex.geometricLink K {coveringVertex.base v}))
    (hp : IsCoveringMap p) :
    let _ : DecidableEq (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))) :=
      Classical.decEq _
    CoherentOrientation n
      (SimplicialComplex.geometricLink (coveringComplex K p)
        {coveringVertexPoint K p v}) := by
  dsimp only
  exact o.map (coveringVertexLink_isGlueIso K p hp v)

open Classical in
theorem isOrientable_coveringVertexLink_iff {n : ℕ}
    (hp : IsCoveringMap p) (v : coveringVertex K p) :
    let _ : DecidableEq (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))) :=
      Classical.decEq _
    IsOrientable n (SimplicialComplex.geometricLink K {coveringVertex.base v}) ↔
      IsOrientable n (SimplicialComplex.geometricLink (coveringComplex K p)
        {coveringVertexPoint K p v}) := by
  dsimp only
  exact isOrientable_iff_of_isGlueIso (coveringVertexLink_isGlueIso K p hp v)

open Classical in
theorem isOrientable_coveringVertexLink_of_isCombinatorialManifoldWithBoundary
    (hp : IsCoveringMap p) {n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (v : coveringVertex K p) :
    let _ : DecidableEq (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))) :=
      Classical.decEq _
    IsOrientable n (SimplicialComplex.geometricLink (coveringComplex K p)
      {coveringVertexPoint K p v}) := by
  dsimp only
  apply (isOrientable_coveringVertexLink_iff hp v).mp
  rcases hK (coveringVertex.base v) (coveringVertex.singleton_base_mem_faces v) with hS | hB
  · exact isOrientable_of_isPLSphere hS
  · exact isOrientable_of_isPLBall hB

open Classical in
noncomputable instance SimplicialBoolCocycle.finite_coveringVertex
    (ε : SimplicialBoolCocycle K) :
    Finite (coveringVertex K ε.toBoolCocycle.toFiberBundleCore.proj) := by
  apply coveringVertex.finite K
  intro x
  apply Set.finite_coe_iff.mp
  apply Nat.finite_of_card_ne_zero
  rw [ε.card_fiber x]
  decide

open Classical in
theorem SimplicialBoolCocycle.coveringComplex_isCombinatorialManifoldWithBoundary
    (ε : SimplicialBoolCocycle K) {n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary n K) :
    IsCombinatorialManifoldWithBoundary n
      (coveringComplex K ε.toBoolCocycle.toFiberBundleCore.proj) :=
  isCombinatorialManifoldWithBoundary_coveringComplex K
    ε.toBoolCocycle.toFiberBundleCore.proj ε.isCoveringMap hK

open Classical in
theorem SimplicialBoolCocycle.coveringComplex_isCombinatorialManifold
    (ε : SimplicialBoolCocycle K) {n : ℕ} (hK : IsCombinatorialManifold n K) :
    IsCombinatorialManifold n
      (coveringComplex K ε.toBoolCocycle.toFiberBundleCore.proj) :=
  hK.coveringComplex ε.isCoveringMap

open Classical in
noncomputable def SimplicialBoolCocycle.coveringComplexHomeomorph
    (ε : SimplicialBoolCocycle K) :
    (coveringComplex K ε.toBoolCocycle.toFiberBundleCore.proj).space ≃ₜ
      ε.toBoolCocycle.toFiberBundleCore.TotalSpace :=
  coveringSpaceHomeomorph K ε.toBoolCocycle.toFiberBundleCore.proj ε.isCoveringMap

open Classical in
theorem SimplicialBoolCocycle.isOrientable_coveringComplex_vertexLink
    (ε : SimplicialBoolCocycle K) {n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (v : coveringVertex K ε.toBoolCocycle.toFiberBundleCore.proj) :
    let _ : DecidableEq (EuclideanSpace ℝ
      (Fin (Nat.card (coveringVertex K ε.toBoolCocycle.toFiberBundleCore.proj)))) :=
        Classical.decEq _
    IsOrientable n (SimplicialComplex.geometricLink
      (coveringComplex K ε.toBoolCocycle.toFiberBundleCore.proj)
      {coveringVertexPoint K ε.toBoolCocycle.toFiberBundleCore.proj v}) := by
  dsimp only
  exact isOrientable_coveringVertexLink_of_isCombinatorialManifoldWithBoundary
    ε.isCoveringMap hK v

end DifferentialGeometry.Topology.PiecewiseLinear
