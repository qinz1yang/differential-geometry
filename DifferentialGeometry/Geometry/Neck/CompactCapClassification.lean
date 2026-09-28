import DifferentialGeometry.Geometry.Neck.CompactCapCover
import DifferentialGeometry.Geometry.Neck.CompactClassification
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PositiveComponentSpaceForm

noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_compact_spatial_poincareStandard_tolerance :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
      ∀ (M : ConnectedClosedOrientedManifold.{u} 3)
        (g : SmoothRiemannianMetric I3 M.Carrier),
        (∀ x : M.Carrier, ¬ Nonempty (SpatialNeck g eps x) →
          Nonempty (PositiveComponent (M := M.Carrier) univ) ∨
          admitsConstantPositiveSectionalCurvature (I := I3) (M := M.Carrier) ∨
          ∃ (K : CompactDomain M.Carrier) (v : M.Carrier) (nk : SpatialNeck g eps v) (a : ℝ),
            0 < metricScalarAt g x ∧ Nonempty (CapCore K.carrier) ∧ |a| ≤ 4 ∧
            frontier K.carrier = range (fun q : Sphere 2 => nk.map (q, a)) ∧
            riemannianBallOf g x (1000 / Real.sqrt (metricScalarAt g x)) ⊆ interior K.carrier) →
        isPoincareStandard M.Carrier := by
  obtain ⟨eta₀, hη₀, hcover⟩ := exists_compact_spatial_neck_cap_cover_alternatives_tolerance.{u}
  obtain ⟨eta₁, hη₁, hneck⟩ := exists_spatial_neck_standard_factor_tolerance.{u}
  refine ⟨min eta₀ eta₁, lt_min hη₀ hη₁, ?_⟩
  intro eps heps M g hmodels
  classical
  by_cases hpositive : Nonempty (PositiveComponent (M := M.Carrier) univ)
  · exact isPoincareStandard_of_positiveComponent hpositive.some
  by_cases hround : admitsConstantPositiveSectionalCurvature (I := I3) (M := M.Carrier)
  · exact isPoincareStandard_of_standard_factor M
      (isStandardFactor_of_admitsConstantPositiveSectionalCurvature (M := M) hround)
  have hcap : ∀ x : M.Carrier, ¬ Nonempty (SpatialNeck g eps x) →
      ∃ (K : CompactDomain M.Carrier) (v : M.Carrier) (nk : SpatialNeck g eps v) (a : ℝ),
        0 < metricScalarAt g x ∧ Nonempty (CapCore K.carrier) ∧ |a| ≤ 4 ∧
        frontier K.carrier = range (fun q : Sphere 2 => nk.map (q, a)) ∧
        riemannianBallOf g x (1000 / Real.sqrt (metricScalarAt g x)) ⊆ interior K.carrier := by
    intro x hx
    exact ((hmodels x hx).resolve_left hpositive).resolve_left hround
  rcases hcover eps (heps.trans (min_le_left _ _)) M.Carrier g hcap with
    hall | ⟨K, L, _, _, _, hcK, hcL, _, _, hinter, _, htotal⟩
  · exact isPoincareStandard_of_standard_factor M
      (hneck eps (heps.trans (min_le_right _ _)) M g hall)
  · exact isPoincareStandard_of_capCore_cover hcK.some hcL.some hinter htotal

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
