import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialRoundFiniteDegree
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ReservedCanonical
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff ENNReal
namespace GC.GeneralFlow
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem spatialRound_volume_lower_of_degree_bound
    {g : SmoothRiemannianMetric I3 M} {ε : ℝ} {x : M} {U : Set M}
    (D : SpatialRoundComponent g ε x U) (y₀ : U) (N : ℕ)
    (hN : Nat.card (FundamentalGroup U y₀) ≤ N) :
    ENNReal.ofReal ((4 * Real.sqrt 3 * Real.pi / (N : ℝ)) /
      (metricScalarAt g x * Real.sqrt (metricScalarAt g x))) ≤
      riemannianVolumeMeasure I3 M g U := by
  obtain ⟨_hf,hpos,hvolume⟩ := spatialRound_volume_lower_div_fundamental_degree D y₀
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hvolume
  apply div_le_div_of_nonneg_right _ (mul_nonneg D.Q_pos.le (Real.sqrt_nonneg _))
  exact div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hpos)
    (by exact_mod_cast hN)

def ReservedCanonicalWitness.ofDegreeBound
    {g : SmoothRiemannianMetric I3 M} {ε C1 C2 : ℝ} {x : M}
    (W : SpatialCanonicalWitness g ε C1 C2 x) (hc : W.capTubeHasNeckChart ε) (N : ℕ)
    (hN : ¬ W.alternative.requiresVolume →
      Nat.card (FundamentalGroup W.domain.carrier ⟨x, interior_subset W.center_inside⟩) ≤ N) :
    ReservedCanonicalWitness g ε C1 C2 (4 * Real.sqrt 3 * Real.pi / (N : ℝ)) x where
  witness := W
  cap_neck := hc
  reserve := by
    intro hn
    have hcard := hN hn
    cases hA : W.alternative with
    | round whole D =>
      rw [← whole]
      exact spatialRound_volume_lower_of_degree_bound D _ N hcard
    | neck data => exact (hn (by rw [hA]; trivial)).elim
    | cap data deep => exact (hn (by rw [hA]; trivial)).elim
    | positive whole data sec => exact (hn (by rw [hA]; trivial)).elim

theorem degreeBoundCanonicalConsumer (ε C1 C2 : ℝ) (N : ℕ) (hN : 0 < N) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {x : P.Carrier}
      (W : SpatialCanonicalWitness g ε C1 C2 x), W.capTubeHasNeckChart ε →
      (¬ W.alternative.requiresVolume →
        Nat.card (FundamentalGroup W.domain.carrier ⟨x, interior_subset W.center_inside⟩) ≤ N) →
      ∀ r : ℝ, 0 < r → r^4 * normSq0S g x 4 (metricRm04At g x) ≤ 1 →
      ENNReal.ofReal (κ*r^3) ≤ riemannianVolumeMeasure I3 P.Carrier g
        (riemannianBallOf g x r) := by
  obtain ⟨κ,hκ,hball⟩ := reservedCanonicalBallConsumer.{u} ε C1 C2
    (4 * Real.sqrt 3 * Real.pi / (N : ℝ)) (by positivity)
  refine ⟨κ,hκ,?_⟩
  intro P g x W hc hcard r hr hcurv
  exact hball (ReservedCanonicalWitness.ofDegreeBound W hc N hcard) r hr hcurv

end GC.GeneralFlow
