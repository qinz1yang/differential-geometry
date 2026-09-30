import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ProjectiveCapDomain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.DiagonalModelChain
import Batteries.Tactic.OpenPrivate

open private exists_projective_diagonal_slab_with_collar from DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ProjectiveCapDomain

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open Surgery.Topology
open KappaSolutions

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]

theorem exists_localCap_diagonal_slab
    (S : SolutionOn (I := I3) (M := M) ancientTimeInterval)
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮IC, I3⟯ M)
    (hmetric : ∀ t : ℝ, ∀ ht : t ≤ 0,
      localPullMetric (Diffeomorph.pullbackMetricCross (S.base.metric t) d) cylinderDiagonalQuotientMap
        cylinderDiagonalQuotientMap_isLocalDiffeomorph =
          scalarOneShrinkingCylinderMetric t (ht.trans_lt (by norm_num)))
    {eps : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11)
    (p : Cylinder) (L : ℝ) (hp : |p.2| < L) (hL : eps⁻¹ ≤ L) :
    let U := d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-(L + 1)) (L + 1)))
    ∃ cap : LocalCap S eps (d (cylinderDiagonalQuotientMap p)) 0 U,
      cap.core.carrier = d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-L) L)) ∧
      cap.tube = d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc L (L + 1))) ∧
      (∀ z : Cylinder, cap.tubeMap z = d (cylinderDiagonalQuotientMap (z.1, L + z.2))) ∧
      cap.chain.count = 1 ∧ ∀ i,
        cap.chain.centers i = d (cylinderDiagonalQuotientMap (p.1, L)) ∧
        (∀ z : Cylinder, (cap.chain.necks i).map z =
          d (cylinderDiagonalQuotientMap (z.1, z.2 + L))) ∧
        cap.chain.lo i = 0 ∧ cap.chain.hi i = 1 := by
  intro U
  have hwidth : (L + 1) - L < eps⁻¹ := by
    have heps1 : eps < 1 := hsmall.trans (by norm_num)
    have hi : 1 < eps⁻¹ := (one_lt_inv₀ heps).mpr heps1
    linarith
  obtain ⟨K, tube, hK, ⟨core⟩, hpK, hKU, hmap, hdom, himage, hin, hout, hunion,
      hoverlap, hfront, hdisjoint⟩ := exists_projective_diagonal_slab_with_collar d p hp
        (show L < L + 1 by linarith)
  obtain ⟨nk, _hcenter, _hsource, hneckmap, chain, hcount, hchain⟩ :=
    exists_orderedNeckChain_diagonal_tube S d hmetric heps hsmall p.1 L (L + 1) hL
      (by linarith) hwidth
  let V := d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc L (L + 1)))
  let cap : LocalCap S eps (d (cylinderDiagonalQuotientMap p)) 0 U := {
    core := K
    core_inside := hKU
    center_inside := hpK
    coreModel := core
    tube := V
    tubeMap := tube
    tube_domain := hdom
    tube_eq := himage
    union_eq := by dsimp only [V]; rw [← himage]; exact hunion.symm
    overlap_eq := by dsimp only [V]; rw [← himage]; exact hoverlap
    inner_boundary := hin
    outer_boundary := hout
    boundary_eq := by dsimp only [V]; rw [← himage]; exact hfront
    boundaries_disjoint := hdisjoint
    chain := chain
    coreBoundaryMap := fun z => tube (z, 0)
    core_boundary_eq := fun _ => rfl }
  refine ⟨cap, hK, rfl, ?_, hcount, ?_⟩
  · intro z
    have hh := hmap z
    simpa only [add_sub_cancel_left, one_mul] using hh
  · intro i
    obtain ⟨hc, hm, hlo, hhi⟩ := hchain i
    refine ⟨hc, ?_, hlo, ?_⟩
    · intro z
      exact (congrArg (fun e => e z) hm).trans (hneckmap z)
    · simpa only [add_sub_cancel_left] using hhi

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
