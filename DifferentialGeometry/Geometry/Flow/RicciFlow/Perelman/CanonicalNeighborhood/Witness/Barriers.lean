import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckCap

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps C1 C2 : ℝ} {x : M} {t : ℝ}

theorem canonicalWitness_localBarrier_neck
    (W : CanonicalWitness S eps C1 C2 x t)
    (hneck : ∃ nk : LocalNeck S eps x t W.domain.carrier,
      W.alternative = CanonicalAlternative.neck nk)
    {A B : ℝ}
    (hband : ∀ y ∈ W.domain.carrier, 2 * A < S.scalar t y ∧
      S.scalar t y ≤ B) :
    ∃ (U : CompactDomain M) (nk : LocalNeck S eps x t U.carrier),
      U = W.domain ∧ x ∈ interior U.carrier ∧
      U.carrier = nk.strong.map '' (Set.univ ×ˢ Set.Icc (-10 : ℝ) 10) ∧
      frontier U.carrier = nk.strong.map '' (Set.univ ×ˢ ({-10, 10} : Set ℝ)) ∧
      (∀ y ∈ U.carrier, 2 * A < S.scalar t y ∧ S.scalar t y ≤ B) := by
  obtain ⟨nk, halt⟩ := hneck
  refine ⟨W.domain, ?_, rfl, W.center_inside, ?_, ?_, ?_⟩
  · simpa only [halt] using nk
  · exact nk.region_eq
  · exact nk.boundary_eq
  · simpa only [halt] using hband


theorem canonicalWitness_localBarrier_cap
    (W : CanonicalWitness S eps C1 C2 x t)
    (hcap : ∃ (cap : LocalCap S eps x t W.domain.carrier) (hdepth : ∀ y ∈ cap.tube,
      10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x y),
      W.alternative = CanonicalAlternative.cap cap hdepth)
    {A B : ℝ}
    (hband : ∀ y ∈ W.domain.carrier, 2 * A < S.scalar t y ∧
      S.scalar t y ≤ B) :
    ∃ (U : CompactDomain M) (cap : LocalCap S eps x t U.carrier),
      U = W.domain ∧ x ∈ interior U.carrier ∧
      (cap.tubeMap '' (Set.univ ×ˢ ({1} : Set ℝ)) = frontier U.carrier) ∧
      ∀ y ∈ U.carrier, 2 * A < S.scalar t y ∧ S.scalar t y ≤ B := by
  obtain ⟨cap, _, halt⟩ := hcap
  refine ⟨W.domain, ?_, rfl, W.center_inside, ?_, ?_⟩
  · simpa only [halt] using cap
  · exact cap.outer_boundary
  · simpa only [halt] using hband

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
