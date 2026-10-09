import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.DiagonalTranslatedNeck
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckSlabChain

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open Surgery.Topology
open KappaSolutions

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
theorem exists_orderedNeckChain_diagonal_tube
    (S : SolutionOn (I := I3) (M := M) ancientTimeInterval)
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮IC, I3⟯ M)
    (hmetric : ∀ t : ℝ, ∀ ht : t ≤ 0,
      localPullMetric (Diffeomorph.pullbackMetricCross (S.base.metric t) d) cylinderDiagonalQuotientMap
        cylinderDiagonalQuotientMap_isLocalDiffeomorph =
          scalarOneShrinkingCylinderMetric t (ht.trans_lt (by norm_num)))
    {eps : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11)
    (p : Sphere 2) (L R : ℝ) (hL : eps⁻¹ ≤ L) (hLR : L < R) (hwidth : R - L < eps⁻¹) :
    ∃ nk : StrongNeck S eps (d (cylinderDiagonalQuotientMap (p, L))) 0,
      nk.center = p ∧ nk.map.source = univ ×ˢ Ioi (-L) ∧
      (∀ z : Cylinder, nk.map z = d (cylinderDiagonalQuotientMap (z.1, z.2 + L))) ∧
      ∃ chain : OrderedNeckChain S eps 0 (d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc L R))),
        chain.count = 1 ∧ ∀ i, chain.centers i = d (cylinderDiagonalQuotientMap (p, L)) ∧
          (chain.necks i).map = nk.map ∧ chain.lo i = 0 ∧ chain.hi i = R - L := by
  obtain ⟨nk, hcenter, hsource, hmap⟩ := exists_strongNeck_diagonal_projection_translate
    S d hmetric heps hsmall p L hL
  refine ⟨nk, hcenter, hsource, hmap, ?_⟩
  have himage : nk.map '' (univ ×ˢ Icc (0 : ℝ) (R - L)) =
      d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc L R)) := by
    ext y
    constructor
    · rintro ⟨⟨z, s⟩, ⟨_, hs⟩, rfl⟩
      exact ⟨cylinderDiagonalQuotientMap (z, s + L),
        ⟨(z, s + L), ⟨mem_univ _, by constructor <;> linarith [hs.1, hs.2]⟩, rfl⟩,
        (hmap (z, s)).symm⟩
    · rintro ⟨x, ⟨⟨z, s⟩, ⟨_, hs⟩, rfl⟩, rfl⟩
      refine ⟨(z, s - L), ⟨mem_univ _, by constructor <;> linarith [hs.1, hs.2]⟩, ?_⟩
      rw [hmap, sub_add_cancel]
  rw [← himage]
  exact ⟨OrderedNeckChain.singleInterval nk (sub_pos.mpr hLR)
    (neg_neg_of_pos (inv_pos.mpr heps)) hwidth, rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
