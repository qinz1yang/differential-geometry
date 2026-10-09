import DifferentialGeometry.Geometry.Neck.SpatialLevelGraph
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalCapCollar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckLocalTransport
import DifferentialGeometry.Geometry.Neck.FrontierGraphAnnulus
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapCoreCylinderAbsorption

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_cap_inner_boundary_graph_at_neck_crossing_tolerance :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D)
        (epsc C1 C2 t : ℝ) (x p : M)
        (witness : CanonicalWitness S epsc C1 C2 x t), witness.capTubeHasNeckChart eps →
        ∀ (cap : LocalCap S epsc x t witness.domain.carrier)
          (depth : ∀ z ∈ cap.tube,
            10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x z),
          witness.alternative = CanonicalAlternative.cap cap depth →
          ∀ (nk : SpatialNeck (S.base.metric t) eps p) (u v : Sphere 2) (a : ℝ),
            |a| ≤ 4 → nk.map (u, a) = cap.tubeMap (v, 0) →
            ∃ (q : M) (tube : StrongNeck S eps q t)
              (eta : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2) (f : Sphere 2 → ℝ),
              (∀ z, tube.map z = cap.tubeMap z) ∧ ContMDiff I2 𝓘(ℝ) ∞ f ∧
              (∀ z, |f z - a| < 1 / 10) ∧ f u = a ∧
              (∀ z, (z, f z) ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ∧
              (∀ z, nk.map (z, f z) = cap.tubeMap (eta z, 0)) ∧
              frontier cap.core.carrier = range (fun z : Sphere 2 => nk.map (z, f z)) := by
  obtain ⟨eta, heta, hgraph⟩ := exists_spatial_neck_level_graph_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ _ D S epsc C1 C2 t x p witness hchart cap depth htag nk u v a ha hcross
  obtain ⟨q, tube, hmap⟩ := hchart cap depth htag
  have hcross' : tube.toSpatialNeck.map (v, 0) = nk.map (u, a) :=
    (hmap (v, 0)).symm.trans hcross.symm
  obtain ⟨eta, f, hf, hsmall, hpoint, hmem, heq⟩ :=
    hgraph eps heps M (S.base.metric t) q p tube.toSpatialNeck nk v u 0 a
      (by norm_num) ha hcross'
  refine ⟨q, tube, eta, f, fun z => (hmap z).symm, hf, hsmall, hpoint, hmem,
    fun z => (heq z).trans (hmap (eta z, 0)).symm, ?_⟩
  rw [← cap.inner_boundary]
  ext y
  constructor
  · rintro ⟨⟨z, b⟩, ⟨_, hb⟩, hz⟩
    have hb0 : b = 0 := hb
    subst b
    refine ⟨eta.symm z, ?_⟩
    have hh := (heq (eta.symm z)).trans (hmap (eta (eta.symm z), 0)).symm
    rw [eta.apply_symm_apply] at hh
    exact hh.trans hz
  · rintro ⟨z, hz⟩
    exact ⟨(eta z, 0), ⟨mem_univ _, rfl⟩,
      ((heq z).trans (hmap (eta z, 0)).symm).symm.trans hz⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_cap_inner_boundary_to_cut_neck_level_annulus_tolerance :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D)
        (epsc C1 C2 t : ℝ) (x p : M)
        (witness : CanonicalWitness S epsc C1 C2 x t), witness.capTubeHasNeckChart eps →
        ∀ (cap : LocalCap S epsc x t witness.domain.carrier)
          (depth : ∀ z ∈ cap.tube,
            10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x z),
          witness.alternative = CanonicalAlternative.cap cap depth →
          ∀ (nk : SpatialNeck (S.base.metric t) eps p) (u v : Sphere 2) (a : ℝ),
            |a| ≤ 1 → nk.map (u, a) = cap.tubeMap (v, 0) →
            ∃ (b : ℝ) (eta : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2)
              (f : Sphere 2 → ℝ) (A : PartialDiffeomorph IC I3 Cylinder M ∞),
              (b = -2 ∨ b = 2) ∧ ContMDiff I2 𝓘(ℝ) ∞ f ∧
              (∀ z, |f z - a| < 1 / 10) ∧ f u = a ∧
              univ ×ˢ Icc (0 : ℝ) 1 ⊆ A.source ∧
              (∀ z t, A (z, t) = nk.map (z, f z + (b - f z) * t)) ∧
              (∀ z, A (z, 0) = cap.tubeMap (eta z, 0)) ∧
              (∀ z, A (z, 1) = nk.map (z, b)) ∧
              IsCompact (A '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
              A '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ cap.core.carrier = frontier cap.core.carrier ∧
              Nonempty (CapCore (cap.core.carrier ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1))) ∧
              IsCompact (cap.core.carrier ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
              closure (interior (cap.core.carrier ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1))) =
                cap.core.carrier ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1) ∧
              frontier (cap.core.carrier ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1)) =
                range (fun z : Sphere 2 => nk.map (z, b)) := by
  obtain ⟨eta, heta, hgraph⟩ := exists_cap_inner_boundary_graph_at_neck_crossing_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ _ D S epsc C1 C2 t x p witness hchart cap depth htag nk u v a ha hcross
  obtain ⟨q, tube, _, f, _, hf, hsmall, hpoint, _, hmap, hfront⟩ :=
    hgraph eps heps M D S epsc C1 C2 t x p witness hchart cap depth htag nk u v a
      (ha.trans (by norm_num)) hcross
  have hfsmall (z : Sphere 2) : |f z| < 11 / 10 := by
    rw [abs_lt]
    constructor <;> linarith [(abs_lt.mp (hsmall z)).1, (abs_lt.mp (hsmall z)).2,
      (abs_le.mp ha).1, (abs_le.mp ha).2]
  obtain ⟨b, A, hb, hA, hformula, hzero, hone, hcompact, hinter, hreg, hnew⟩ :=
    nk.exists_outward_annulus_of_core_frontier_graph cap.core.regular_closed f hf hfsmall hfront
  have hAf : frontier cap.core.carrier = range (fun z : Sphere 2 => A (z, 0)) := by
    simpa only [hzero] using hfront
  have hside (z : Sphere 2) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
      (hm : A (z, a) ∈ cap.core.carrier) : a = 0 := by
    have hx : A (z, a) ∈ frontier cap.core.carrier :=
      hinter ▸ ⟨⟨(z, a), ⟨mem_univ _, ha⟩, rfl⟩, hm⟩
    obtain ⟨v, hv⟩ := hAf ▸ hx
    have he := A.toPartialEquiv.injOn (hA ⟨mem_univ _, by norm_num⟩) (hA ⟨mem_univ _, ha⟩) hv
    exact (congrArg Prod.snd he).symm
  have hmodel := cap.coreModel.nonempty_union_cylinder A hA hAf hside
  exact ⟨b, _, f, A, hb, hf, hsmall, hpoint, hA, hformula,
    fun z => (hzero z).trans (hmap z), hone, hcompact, hinter, hmodel,
    cap.core.compact.union hcompact, hreg, hnew⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
