/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CoverNormalSystem
import DifferentialGeometry.Topology.PiecewiseLinear.DoubleCoverExistence
import DifferentialGeometry.Topology.PiecewiseLinear.OrientationCocycle
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodPolygon

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem isConnected_manifoldComplex_space (S : NormalSystem E) :
    IsConnected S.manifoldComplex.space := by
  let _ : Finite S.ambientComplex.faces := S.finite_ambient.to_subtype
  let _ : Finite S.sourceComplex.faces := S.finite_source.to_subtype
  let _ : Finite S.imageComplex.faces :=
    (S.finite_ambient.subset S.image_faces_subset_ambient).to_subtype
  rw [S.manifold_space]
  apply isConnected_derivedNeighborhood_space S.image_faces_subset_ambient
  rw [S.image_space]
  exact S.source_isPLBall.isConnected.image _
    (isPiecewiseAffineOn_simplicialMap S.sourceComplex S.vertexMap).continuousOn

variable [FiniteDimensional ℝ E]

open Classical in
theorem exists_doubleCoverReduction_boundary_mem_nhdsWithin_of_not_isOrientable
    (S : NormalSystem E)
    (hproper : S.sourceComplex.space ∩ S.singularMap ⁻¹' S.boundaryComplex.space =
      frontier S.sourceComplex.space)
    (hbase : S.basepoint = S.boundaryLoop 0)
    (hnot : ¬S.IsOrientableManifold) :
    ∃ (N : ℕ) (T : NormalSystem (EuclideanSpace ℝ (Fin N)))
      (R : DoubleCoverReduction S T),
      T.basepoint = T.boundaryLoop 0 ∧
      T.sourceComplex.space ∩ T.singularMap ⁻¹' T.boundaryComplex.space =
        frontier T.sourceComplex.space ∧
      ∀ x ∈ T.boundaryNeighborhood.space,
        S.boundaryNeighborhood.space ∈ 𝓝[S.boundaryComplex.space] (R.projection x) := by
  let K := S.manifoldComplex
  let _ : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
  let _ : ConnectedSpace K.space :=
    isConnected_iff_connectedSpace.mp S.isConnected_manifoldComplex_space
  let e : (barycentricSubdivision K).space ≃ₜ K.space :=
    Homeomorph.setCongr (barycentricSubdivision_isSubdivision K).space_eq
  let _ : ConnectedSpace (barycentricSubdivision K).space :=
    e.symm.surjective.connectedSpace e.symm.continuous
  obtain ⟨ε, hε⟩ := exists_orientationCocycle_of_not_isOrientable (K := K) S.isManifold hnot
  let p := e ∘ ε.toBoolCocycle.toFiberBundleCore.proj
  let _ : ConnectedSpace ε.toBoolCocycle.toFiberBundleCore.TotalSpace :=
    ε.connectedSpace_iff.mpr hε
  apply S.exists_doubleCoverReduction_boundary_mem_nhdsWithin_of_isCoveringMap hproper hbase p
    (ε.isCoveringMap.homeomorph_comp e)
  intro y
  have hfiber : p ⁻¹' {y} =
      ε.toBoolCocycle.toFiberBundleCore.proj ⁻¹' {e.symm y} := by
    ext z
    exact e.toEquiv.eq_symm_apply.symm
  rw [hfiber, ← (ε.finite_fiber (e.symm y)).cast_ncard_eq,
    ← Nat.card_coe_set_eq, ε.card_fiber]
  rfl

open Classical in
theorem exists_doubleCoverReduction_boundary_mem_nhdsWithin_of_isOrientable_of_not_isPLSphere
    (S : NormalSystem E)
    (hproper : S.sourceComplex.space ∩ S.singularMap ⁻¹' S.boundaryComplex.space =
      frontier S.sourceComplex.space)
    (hbase : S.basepoint = S.boundaryLoop 0)
    (hor : S.IsOrientableManifold) (hnot : ¬IsPLSphere 2 S.boundaryComponent) :
    ∃ (N : ℕ) (T : NormalSystem (EuclideanSpace ℝ (Fin N)))
      (R : DoubleCoverReduction S T),
      T.basepoint = T.boundaryLoop 0 ∧
      T.sourceComplex.space ∩ T.singularMap ⁻¹' T.boundaryComplex.space =
        frontier T.sourceComplex.space ∧
      ∀ x ∈ T.boundaryNeighborhood.space,
        S.boundaryNeighborhood.space ∈ 𝓝[S.boundaryComplex.space] (R.projection x) := by
  let K := S.manifoldComplex
  let _ : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
  let _ : Finite S.boundaryComplex.faces := S.boundaryComplex_faces_finite.to_subtype
  let _ : ConnectedSpace K.space :=
    isConnected_iff_connectedSpace.mp S.isConnected_manifoldComplex_space
  have hx : (S.boundaryLoop 0 : E) ∈ (PiecewiseLinear.boundaryComplex 3 K).space :=
    derivedNeighborhood_space_subset S.boundaryComplex S.loopComplex (S.boundaryLoop 0).2
  let c := ConnectedComponents.mk
    (⟨(S.boundaryLoop 0 : E), hx⟩ : (PiecewiseLinear.boundaryComplex 3 K).space)
  have hc : (connectedComponentComplex (PiecewiseLinear.boundaryComplex 3 K) c).space =
      S.boundaryComponent := by
    dsimp only [c]
    rw [connectedComponentComplex_mk, restrict_connectedComponentIn_space]
    rfl
  obtain ⟨ε, -, -, -, hε, -, -, -, -, -⟩ :=
    exists_connected_double_cover_complex_of_isOrientable_of_boundary_component_not_sphere
      K S.isManifold hor c (hc ▸ hnot)
  let _ : ConnectedSpace ε.toBoolCocycle.toFiberBundleCore.TotalSpace :=
    ε.connectedSpace_iff.mpr hε
  apply S.exists_doubleCoverReduction_boundary_mem_nhdsWithin_of_isCoveringMap hproper hbase
    ε.toBoolCocycle.toFiberBundleCore.proj ε.isCoveringMap
  intro y
  rw [← (ε.finite_fiber y).cast_ncard_eq, ← Nat.card_coe_set_eq, ε.card_fiber]
  rfl

open Classical in
theorem exists_doubleCoverReduction_boundary_mem_nhdsWithin_of_not_isPLSphere
    (S : NormalSystem E)
    (hproper : S.sourceComplex.space ∩ S.singularMap ⁻¹' S.boundaryComplex.space =
      frontier S.sourceComplex.space)
    (hbase : S.basepoint = S.boundaryLoop 0)
    (hnot : ¬IsPLSphere 2 S.boundaryComponent) :
    ∃ (N : ℕ) (T : NormalSystem (EuclideanSpace ℝ (Fin N)))
      (R : DoubleCoverReduction S T),
      T.basepoint = T.boundaryLoop 0 ∧
      T.sourceComplex.space ∩ T.singularMap ⁻¹' T.boundaryComplex.space =
        frontier T.sourceComplex.space ∧
      ∀ x ∈ T.boundaryNeighborhood.space,
        S.boundaryNeighborhood.space ∈ 𝓝[S.boundaryComplex.space] (R.projection x) := by
  by_cases hor : S.IsOrientableManifold
  · exact S.exists_doubleCoverReduction_boundary_mem_nhdsWithin_of_isOrientable_of_not_isPLSphere
      hproper hbase hor hnot
  · exact S.exists_doubleCoverReduction_boundary_mem_nhdsWithin_of_not_isOrientable
      hproper hbase hor

open Classical in
theorem exists_doubleCoverReduction_of_not_isOrientable
    (S : NormalSystem E)
    (hproper : S.sourceComplex.space ∩ S.singularMap ⁻¹' S.boundaryComplex.space =
      frontier S.sourceComplex.space)
    (hbase : S.basepoint = S.boundaryLoop 0)
    (hnot : ¬S.IsOrientableManifold) :
    ∃ (N : ℕ) (T : NormalSystem (EuclideanSpace ℝ (Fin N))),
      Nonempty (DoubleCoverReduction S T) ∧ T.basepoint = T.boundaryLoop 0 ∧
      T.sourceComplex.space ∩ T.singularMap ⁻¹' T.boundaryComplex.space =
        frontier T.sourceComplex.space := by
  obtain ⟨N, T, R, hbaseT, hproperT, -⟩ :=
    S.exists_doubleCoverReduction_boundary_mem_nhdsWithin_of_not_isOrientable
      hproper hbase hnot
  exact ⟨N, T, ⟨R⟩, hbaseT, hproperT⟩

open Classical in
theorem exists_doubleCoverReduction_of_isOrientable_of_boundaryComponent_not_isPLSphere
    (S : NormalSystem E)
    (hproper : S.sourceComplex.space ∩ S.singularMap ⁻¹' S.boundaryComplex.space =
      frontier S.sourceComplex.space)
    (hbase : S.basepoint = S.boundaryLoop 0)
    (hor : S.IsOrientableManifold) (hnot : ¬IsPLSphere 2 S.boundaryComponent) :
    ∃ (N : ℕ) (T : NormalSystem (EuclideanSpace ℝ (Fin N))),
      Nonempty (DoubleCoverReduction S T) ∧ T.basepoint = T.boundaryLoop 0 ∧
      T.sourceComplex.space ∩ T.singularMap ⁻¹' T.boundaryComplex.space =
        frontier T.sourceComplex.space := by
  obtain ⟨N, T, R, hbaseT, hproperT, -⟩ :=
    S.exists_doubleCoverReduction_boundary_mem_nhdsWithin_of_isOrientable_of_not_isPLSphere
      hproper hbase hor hnot
  exact ⟨N, T, ⟨R⟩, hbaseT, hproperT⟩

open Classical in
theorem exists_doubleCoverReduction_of_boundaryComponent_not_isPLSphere
    (S : NormalSystem E)
    (hproper : S.sourceComplex.space ∩ S.singularMap ⁻¹' S.boundaryComplex.space =
      frontier S.sourceComplex.space)
    (hbase : S.basepoint = S.boundaryLoop 0)
    (hnot : ¬IsPLSphere 2 S.boundaryComponent) :
    ∃ (N : ℕ) (T : NormalSystem (EuclideanSpace ℝ (Fin N))),
      Nonempty (DoubleCoverReduction S T) ∧ T.basepoint = T.boundaryLoop 0 ∧
      T.sourceComplex.space ∩ T.singularMap ⁻¹' T.boundaryComplex.space =
        frontier T.sourceComplex.space := by
  obtain ⟨N, T, R, hbaseT, hproperT, -⟩ :=
    S.exists_doubleCoverReduction_boundary_mem_nhdsWithin_of_not_isPLSphere
      hproper hbase hnot
  exact ⟨N, T, ⟨R⟩, hbaseT, hproperT⟩

end DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem
