import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapNeckCrossing
import DifferentialGeometry.Geometry.Neck.FrontierBandCapture

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_cap_inner_boundary_to_cut_neck_level_annulus_and_capture_tolerance :
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
            |a| ≤ 1 → nk.map (u, a) = cap.tube_map (v, 0) →
            ∃ (b : ℝ) (eta : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2)
              (f : Sphere 2 → ℝ) (A : PartialDiffeomorph IC I3 Cylinder M ∞),
              (b = -2 ∨ b = 2) ∧ ContMDiff I2 𝓘(ℝ) ∞ f ∧
              (∀ z, |f z - a| < 1 / 10) ∧ f u = a ∧
              univ ×ˢ Icc (0 : ℝ) 1 ⊆ A.source ∧
              (∀ z t, A (z, t) = nk.map (z, f z + (b - f z) * t)) ∧
              (∀ z, A (z, 0) = cap.tube_map (eta z, 0)) ∧
              (∀ z, A (z, 1) = nk.map (z, b)) ∧
              IsCompact (A '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
              A '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ cap.core.carrier = frontier cap.core.carrier ∧
              nk.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ⊆
                interior (cap.core.carrier ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
              Nonempty (CapCore (cap.core.carrier ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1))) ∧
              IsCompact (cap.core.carrier ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
              closure (interior (cap.core.carrier ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1))) =
                cap.core.carrier ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1) ∧
              frontier (cap.core.carrier ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1)) =
                range (fun z : Sphere 2 => nk.map (z, b)) := by
  obtain ⟨eta, heta, hstep⟩ := exists_cap_inner_boundary_to_cut_neck_level_annulus_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ _ D S epsc C1 C2 t x p witness hchart cap depth htag nk u v a ha hcross
  obtain ⟨b, e, f, A, hb, hf, hsmall, hpoint, hA, hformula, hzero, hone, hcompact,
    hinter, hmodel, hK, hreg, hfront⟩ :=
    hstep eps heps M D S epsc C1 C2 t x p witness hchart cap depth htag nk u v a ha hcross
  have hcontact : nk.map (u, a) ∈ cap.core.carrier := by
    rw [hcross]
    apply cap.core.compact.isClosed.frontier_subset
    rw [← cap.inner_boundary]
    exact ⟨(v, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  have hcapture := nk.closed_unit_band_subset_interior_of_frontier_level_two hb hfront
    ⟨nk.map (u, a), ⟨(u, a), ⟨mem_univ _, abs_le.mp ha⟩, rfl⟩, Or.inl hcontact⟩
  exact ⟨b, e, f, A, hb, hf, hsmall, hpoint, hA, hformula, hzero, hone, hcompact,
    hinter, hcapture, hmodel, hK, hreg, hfront⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
