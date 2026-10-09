import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.DiagonalCoverModel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.DiagonalCanonicalWitness

section
set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open KappaSolutions

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

private theorem cap_tube_eq_of_heq
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D} {eps : ℝ} {p : M} {t : ℝ}
    {U V : Set M} (hUV : U = V) {a : LocalCap S eps p t U} {b : LocalCap S eps p t V} (h : HEq a b) : a.tube = b.tube := by
  cases hUV
  rw [eq_of_heq h]

private theorem cap_tube_map_eq_of_heq
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D} {eps : ℝ} {p : M} {t : ℝ}
    {U V : Set M} (hUV : U = V) {a : LocalCap S eps p t U} {b : LocalCap S eps p t V}
    (h : HEq a b) : a.tubeMap = b.tubeMap := by
  cases hUV
  rw [eq_of_heq h]

theorem exists_canonicalWitness_with_neck_tube_of_diagonal_cylinder_cover
    (P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    (cover : ShrinkingCylinderCover P) (hdiagonal : cover.DiagonalModel)
    (hscalar : PointedFlowScalarAtBase P 1) {eps : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11)
    (H : ℝ) :
    ∃ A C : ℝ, ∃ K : CanonicalWitness P.S eps A C P.basepoint 0,
      ∃ cap : LocalCap P.S eps P.basepoint 0 K.domain.carrier,
        (∃ depth, K.alternative = CanonicalAlternative.cap cap depth) ∧
        ∃ (v : P.M) (neck : StrongNeck P.S eps v 0),
          (∀ z : Cylinder, cap.tubeMap z = neck.map z) ∧ v ∈ cap.tube ∧
          neck.map '' (univ ×ˢ ({0} : Set ℝ)) ⊆ cap.tube ∧
          ∀ y ∈ cap.tube, H < metricDistance (P.S.base.metric 0) P.basepoint y := by
  obtain ⟨d, _hprojection, hmetric⟩ := cover.exists_diagonal_shrinking_model P hdiagonal hscalar
  obtain ⟨p, hp⟩ := cylinderDiagonalQuotientMap_surjective (d.symm P.basepoint)
  have hpbase : d (cylinderDiagonalQuotientMap p) = P.basepoint := by rw [hp, d.apply_symm_apply]
  obtain ⟨L, r, C, _hL, _hpL, _hr, _hC, cap, _hcore, htube, hmap, hcount, hchain, hfar,
      K, hKU, _hKr, capK, depthK, hKalt, hcapK⟩ :=
    exists_canonicalWitness_diagonal_shrinking_model P.S d hmetric heps hsmall p H
  let j : Fin cap.chain.count := ⟨0, by omega⟩
  let v := cap.chain.centers j
  let neck := cap.chain.necks j
  have hv : v ∈ cap.tube := by
    change cap.chain.centers j ∈ cap.tube
    rw [(hchain j).1]
    apply htube.symm.subset
    exact ⟨cylinderDiagonalQuotientMap (p.1, L), ⟨(p.1, L), ⟨mem_univ _, le_rfl, by linarith⟩, rfl⟩, rfl⟩
  have hcentral : neck.map '' (univ ×ˢ ({0} : Set ℝ)) ⊆ cap.tube := by
    rintro y ⟨⟨z, s⟩, hs, rfl⟩
    have hs0 : s = 0 := hs.2
    subst s
    apply cap.tube_eq.subset
    refine ⟨(z, 0), ⟨mem_univ _, by norm_num⟩, ?_⟩
    have hh := (hchain j).2.1 (z, 0)
    change neck.map (z, 0) = _ at hh
    rw [hmap, hh]
    simp only [add_zero, zero_add]
  have hdata : v ∈ capK.tube ∧ neck.map '' (univ ×ˢ ({0} : Set ℝ)) ⊆ capK.tube ∧
      ∀ y ∈ capK.tube, H < metricDistance (P.S.base.metric 0) (d (cylinderDiagonalQuotientMap p)) y := by
    rw [cap_tube_eq_of_heq hKU hcapK]
    exact ⟨hv, hcentral, fun y hy => (le_max_right _ _).trans_lt (hfar y hy)⟩
  have hmaps : ∀ z : Cylinder, capK.tubeMap z = neck.map z := by
    intro z
    rw [cap_tube_map_eq_of_heq hKU hcapK]
    have hneck := (hchain j).2.1 z
    change neck.map z = _ at hneck
    rw [hmap, hneck, add_comm L z.2]
  have hresult : ∃ A C : ℝ, ∃ K : CanonicalWitness P.S eps A C (d (cylinderDiagonalQuotientMap p)) 0,
      ∃ cap : LocalCap P.S eps (d (cylinderDiagonalQuotientMap p)) 0 K.domain.carrier,
        (∃ depth, K.alternative = CanonicalAlternative.cap cap depth) ∧
        ∃ (v : P.M) (neck : StrongNeck P.S eps v 0),
          (∀ z : Cylinder, cap.tubeMap z = neck.map z) ∧ v ∈ cap.tube ∧
          neck.map '' (univ ×ˢ ({0} : Set ℝ)) ⊆ cap.tube ∧
          ∀ y ∈ cap.tube, H < metricDistance (P.S.base.metric 0) (d (cylinderDiagonalQuotientMap p)) y :=
    ⟨r, C, K, capK, ⟨depthK, hKalt⟩, v, neck, hmaps, hdata⟩
  rwa [hpbase] at hresult

theorem exists_canonicalWitness_of_diagonal_cylinder_cover
    (P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    (cover : ShrinkingCylinderCover P) (hdiagonal : cover.DiagonalModel)
    (hscalar : PointedFlowScalarAtBase P 1) {eps : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11)
    (H : ℝ) :
    ∃ A C : ℝ, ∃ K : CanonicalWitness P.S eps A C P.basepoint 0,
      ∃ cap : LocalCap P.S eps P.basepoint 0 K.domain.carrier,
        (∃ depth, K.alternative = CanonicalAlternative.cap cap depth) ∧
        ∃ (v : P.M) (neck : StrongNeck P.S eps v 0), v ∈ cap.tube ∧
          neck.map '' (univ ×ˢ ({0} : Set ℝ)) ⊆ cap.tube ∧
          ∀ y ∈ cap.tube, H < metricDistance (P.S.base.metric 0) P.basepoint y := by
  obtain ⟨A, C, K, cap, halt, v, neck, _, hv, hcentral, hfar⟩ :=
    exists_canonicalWitness_with_neck_tube_of_diagonal_cylinder_cover
      P cover hdiagonal hscalar heps hsmall H
  exact ⟨A, C, K, cap, halt, v, neck, hv, hcentral, hfar⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
