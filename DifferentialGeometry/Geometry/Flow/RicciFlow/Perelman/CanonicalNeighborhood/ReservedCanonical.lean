import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComponentVolumeBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessProjection
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff ENNReal
namespace GC.GeneralFlow
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

structure ReservedCanonicalWitness (g : SmoothRiemannianMetric I3 M)
    (ε C1 C2 ν : ℝ) (x : M) where
  witness : SpatialCanonicalWitness g ε C1 C2 x
  cap_neck : witness.capTubeHasNeckChart ε
  reserve : ¬ witness.alternative.requiresVolume →
    ENNReal.ofReal (ν / (metricScalarAt g x * Real.sqrt (metricScalarAt g x))) ≤
      riemannianVolumeMeasure I3 M g (connectedComponent x)

namespace ReservedCanonicalWitness
variable {g : SmoothRiemannianMetric I3 M} {ε C1 C2 ν : ℝ} {x : M}

def ofVolumeRequired (W : SpatialCanonicalWitness g ε C1 C2 x)
    (hc : W.capTubeHasNeckChart ε) (hv : W.alternative.requiresVolume) :
    ReservedCanonicalWitness g ε C1 C2 ν x :=
  ⟨W,hc,fun h => (h hv).elim⟩

def enlarge (W : ReservedCanonicalWitness g ε C1 C2 ν x)
    {C1' C2' : ℝ} (h1 : C1 ≤ C1') (h2 : C2 ≤ C2') :
    ReservedCanonicalWitness g ε C1' C2' ν x where
  witness := W.witness.enlargeConstants h1 h2
  cap_neck := W.cap_neck.enlarge_constants h1 h2
  reserve := by
    intro hn
    apply W.reserve
    intro hv
    apply hn
    change (W.witness.alternative.monoConstant
      (zero_lt_one.trans_le W.witness.one_le_comparison_constant) h2 W.witness.Q_pos.le).requiresVolume
    simpa only [SpatialCanonicalAlternative.monoConstant_requiresVolume] using hv

def weakenReserve (W : ReservedCanonicalWitness g ε C1 C2 ν x)
    {ν' : ℝ} (h : ν' ≤ ν) : ReservedCanonicalWitness g ε C1 C2 ν' x where
  witness := W.witness
  cap_neck := W.cap_neck
  reserve hn := (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right h
    (mul_nonneg W.witness.Q_pos.le (Real.sqrt_nonneg _)))).trans (W.reserve hn)

end ReservedCanonicalWitness

theorem reservedCanonicalBallConsumer (ε C1 C2 ν : ℝ) (hν : 0 < ν) :
    ∃ k : ℝ, 0 < k ∧ ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {x : P.Carrier}
      (_V : ReservedCanonicalWitness g ε C1 C2 ν x) (r : ℝ), 0 < r →
      r^4 * normSq0S g x 4 (metricRm04At g x) ≤ 1 →
      ENNReal.ofReal (k*r^3) ≤ riemannianVolumeMeasure I3 P.Carrier g
        (riemannianBallOf g x r) := by
  obtain ⟨k₀,hk₀,h₀⟩ := exists_ball_volume_of_spatialCanonicalWitness.{u} ε C1 C2
  obtain ⟨kr,hkr,hrnd⟩ := exists_ball_volume_of_normalizedComponentVolume.{u} C1 C2 ν hν
  refine ⟨min k₀ kr,lt_min hk₀ hkr,?_⟩
  intro P g x V r hr hcurv
  have hm : ∀ {b : ℝ}, min k₀ kr ≤ b →
      ENNReal.ofReal (min k₀ kr*r^3) ≤ ENNReal.ofReal (b*r^3) :=
    fun hb => ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hb (by positivity))
  by_cases hv : V.witness.alternative.requiresVolume
  · exact (hm (min_le_left _ _)).trans (h₀ V.witness V.cap_neck hv r hr hcurv)
  · have hwhole : V.witness.domain.carrier = connectedComponent x := by
      cases hA : V.witness.alternative with
      | round whole D => exact whole
      | neck data => exact (hv (by rw [hA]; trivial)).elim
      | cap data deep => exact (hv (by rw [hA]; trivial)).elim
      | positive whole data sec => exact whole
    exact (hm (min_le_right _ _)).trans (hrnd V.witness hwhole
      (by rw [hwhole]; exact V.reserve hv) r hr hcurv)

end GC.GeneralFlow
