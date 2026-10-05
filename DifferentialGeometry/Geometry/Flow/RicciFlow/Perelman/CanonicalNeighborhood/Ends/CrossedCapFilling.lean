import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapNeckCrossingCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCapContact

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_cap_filling_at_crossed_cut_neck_tolerance :
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
          ∀ (nk : SpatialNeck (S.base.metric t) eps p) (u v : Sphere 2) (a level : ℝ),
            |a| ≤ 1 → nk.map (u, a) = cap.tubeMap (v, 0) → |level| ≤ 1 →
            ∀ W R : Set M, closure (interior W) = W → IsPreconnected (interior W) → IsClosed R →
              frontier W = range (fun z : Sphere 2 => nk.map (z, level)) ∪ R →
              Disjoint (range (fun z : Sphere 2 => nk.map (z, level))) R →
              ∃ K : Set M, IsCompact K ∧ closure (interior K) = K ∧
                frontier K = range (fun z : Sphere 2 => nk.map (z, level)) ∧
                (W ⊆ K ∨ K ∩ W = range (fun z : Sphere 2 => nk.map (z, level)) ∧
                  closure (interior (W ∪ K)) = W ∪ K ∧ frontier (W ∪ K) = R ∧
                  range (fun z : Sphere 2 => nk.map (z, level)) ⊆ interior (W ∪ K)) := by
  obtain ⟨eta, heta, hstep⟩ := exists_cap_inner_boundary_to_cut_neck_level_annulus_and_capture_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ _ D S epsc C1 C2 t x p witness hchart cap depth htag nk u v a level
    ha hcross hlevel W R hW hconn hR hfront hdis
  obtain ⟨_, _, _, A, _, _, _, _, _, _, _, _, _, _, hcapture, ⟨core⟩, _, _, _⟩ :=
    hstep eps heps M D S epsc C1 C2 t x p witness hchart cap depth htag nk u v a ha hcross
  obtain ⟨K, hK, hKr, hKf, _, hcases⟩ :=
    nk.exists_cap_filling_or_containment_of_sphere_subset (hlevel.trans (by norm_num)) core
      (by rintro z ⟨q, rfl⟩; exact hcapture ⟨(q, level), ⟨mem_univ _, abs_le.mp hlevel⟩, rfl⟩)
      hW hconn hR hfront hdis
  exact ⟨K, hK, hKr, hKf, hcases⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
