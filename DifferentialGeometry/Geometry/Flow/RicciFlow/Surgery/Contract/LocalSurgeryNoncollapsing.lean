import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.NoncollapseLocalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RoundCanonicalWitness

set_option autoImplicit false

noncomputable section

open Bundle Filter
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

open DifferentialGeometry.PDE.RicciFlow.Perelman

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [T2Space M] [SigmaCompactSpace M]
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

theorem kappaNoncollapsedBelowScale_mono (S : SolutionOn (I := I) (M := M) D) {kappa rho r : Real}
    (hr : 0 < r) (hrle : r ≤ rho) (h : KappaNoncollapsedBelowScale S kappa rho) :
    KappaNoncollapsedBelowScale S kappa r :=
  ⟨hr, fun t B hrB hB => h.2 t B (le_trans hrB hrle) hB⟩

theorem spatiallyKappaNoncollapsedBelowScale_mono (S : SolutionOn (I := I) (M := M) D)
    {kappa rho r : Real} (hr : 0 < r) (hrle : r ≤ rho)
    (h : SpatiallyKappaNoncollapsedBelowScale S kappa rho) :
    SpatiallyKappaNoncollapsedBelowScale S kappa r :=
  ⟨hr, fun t B hB => h.2 t B (le_trans hB hrle)⟩

def RetainedRegionAgreement (S S' : SolutionOn (I := I) (M := M) D)
    (W : Real → Set M) : Prop :=
  (∀ s : Real, IsOpen (W s)) ∧
    ∀ (s : Real) (x : M), x ∈ W s → ∀ v w : TangentSpace I x,
      (S'.base.metric s).inner x v w = (S.base.metric s).inner x v w

omit [FiniteDimensional Real E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem surgeryRegionAgreesOnParabolicBalls_of_retainedRegion
    (S S' : SolutionOn (I := I) (M := M) D) {rho : Real} {W : Real → Set M}
    (hW : RetainedRegionAgreement S S' W)
    (hball : ∀ (t : D.FlowTime) (B' : FlowMetricBall S' t), B'.radius ≤ rho →
      ∀ s ∈ Set.Icc ((t : Real) - B'.radius ^ 2) (t : Real), B'.setAt s ⊆ W s) :
    surgeryRegionAgreesOnParabolicBalls S S' rho :=
  fun t B' hr s hs => ⟨W s, hW.1 s, hball t B' hr s hs, fun x hx => hW.2 s x hx⟩

omit [FiniteDimensional Real E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem surgeryRegionAgreesOnParabolicBalls_of_isSurgeryNoncollapsingStep
    {S S' : SolutionOn (I := I) (M := M) D} {rho r : Real} (hrle : r ≤ rho)
    (h : isSurgeryNoncollapsingStep S S' rho) :
    metricDomination S S' r ∧ surgeryRegionAgreesOnParabolicBalls S S' r :=
  ⟨fun t rad hrad hradr => h.1 t rad hrad (le_trans hradr hrle),
    fun t B' hB => h.2 t B' (le_trans hB hrle)⟩

theorem kappaNoncollapsedBelowScale_of_local_surgery
    (S S' : SolutionOn (I := I) (M := M) D) (kappa rho r : Real)
    (hr : 0 < r) (hrle : r ≤ rho)
    (h : KappaNoncollapsedBelowScale S kappa rho)
    (hdom : metricDomination S S' r)
    (hagr : surgeryRegionAgreesOnParabolicBalls S S' r) :
    KappaNoncollapsedBelowScale S' kappa r :=
  kappaNoncollapsedBelowScale_of_isSurgeryNoncollapsingStep S S' kappa r
    (kappaNoncollapsedBelowScale_mono S hr hrle h) ⟨hdom, hagr⟩

theorem spatiallyKappaNoncollapsedBelowScale_of_local_surgery
    (S S' : SolutionOn (I := I) (M := M) D) (kappa rho r : Real)
    (hr : 0 < r) (hrle : r ≤ rho)
    (h : SpatiallyKappaNoncollapsedBelowScale S kappa rho)
    (hdom : metricDomination S S' r)
    (hagr : surgeryRegionAgreesOnParabolicBalls S S' r) :
    SpatiallyKappaNoncollapsedBelowScale S' kappa r :=
  spatiallyKappaNoncollapsedBelowScale_of_isSurgeryNoncollapsingStep S S' kappa r
    (spatiallyKappaNoncollapsedBelowScale_mono S hr hrle h) ⟨hdom, hagr⟩

omit [FiniteDimensional Real E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem isSurgeryNoncollapsingStep_self_local (S : SolutionOn (I := I) (M := M) D) (r : Real) :
    metricDomination S S r ∧ surgeryRegionAgreesOnParabolicBalls S S r :=
  ⟨metricDomination_self S r, surgeryRegionAgreesOnParabolicBalls_self S r⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Perelman

theorem roundSphereThreeSolution_local_surgery_witness
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval) (r : Real) :
    metricDomination (roundSphereThreeSolution D) (roundSphereThreeSolution D) r ∧
      surgeryRegionAgreesOnParabolicBalls (roundSphereThreeSolution D)
        (roundSphereThreeSolution D) r :=
  isSurgeryNoncollapsingStep_self_local (roundSphereThreeSolution D) r

theorem roundSphereThreeSolution_local_noncollapsing
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval) {kappa rho r : Real}
    (hr : 0 < r) (hrle : r ≤ rho)
    (h : KappaNoncollapsedBelowScale (roundSphereThreeSolution D) kappa rho) :
    KappaNoncollapsedBelowScale (roundSphereThreeSolution D) kappa r :=
  kappaNoncollapsedBelowScale_mono (roundSphereThreeSolution D) hr hrle h

end DifferentialGeometry.PDE.RicciFlow.Surgery
