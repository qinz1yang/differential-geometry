import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SameManifoldLimitEquation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LimitUniqueness
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Canonical.ReferenceChange
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SameManifoldSlabWindowLink

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Filter
open scoped _root_.Manifold ContDiff _root_.Topology

theorem PointedCGHMaps.pointedlyIdentified_of_map_eq
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] [CompleteSpace E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : Nat → Nat}
    (Phi₁ Phi₂ : PointedCGHMaps (I := I) X P subseq)
    (h : ∀ (k : Nat) (x : P.M), Phi₁.map k x = Phi₂.map k x) :
    Phi₁.PointedlyIdentified Phi₂ :=
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : IsManifold I ∞ P.M := P.smooth
  letI : T2Space P.M := P.t2
  ⟨Diffeomorph.refl I P.M (∞ : WithTop ℕ∞), rfl,
    Diffeomorph.pullbackMetricCross_refl (I := I) P.metric, fun x => by
      have hzero : (fun k : Nat => sourceRiemannianEDist (I := I) X (subseq k) 0
          (Phi₁.map k x)
          (Phi₂.map k ((Diffeomorph.refl I P.M (∞ : WithTop ℕ∞)) x))) =
          fun _ : Nat => 0 := by
        funext k
        simp only [Diffeomorph.coe_refl, id_eq]
        rw [h k x, sourceRiemannianEDist_self]
      rw [hzero]
      exact tendsto_const_nhds⟩

theorem PointedCGHMaps.pointedlyIsometric_of_pointedlyIdentified
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] [CompleteSpace E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P₁ P₂ : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : Nat → Nat}
    (Phi₁ : PointedCGHMaps (I := I) X P₁ subseq)
    (Phi₂ : PointedCGHMaps (I := I) X P₂ subseq)
    (h : Phi₁.PointedlyIdentified Phi₂) :
    PointedRiemannianManifold.PointedlyIsometric (I := I) P₁ P₂ := by
  obtain ⟨F, hbase, hmetric, _⟩ := h
  exact ⟨F, hbase, hmetric⟩

end CheegerGromovCompactness
end DifferentialGeometry

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]
variable [T2Space M] [SigmaCompactSpace M]

theorem arcInterval_carrier_subset_ancient (T : Real) (hT : 0 < T) :
    (arcInterval T).carrier ⊆ CanonicalNeighborhood.ancientTimeInterval.carrier := by
  rw [CanonicalNeighborhood.ancientTimeInterval_carrier]
  exact arcInterval_carrier_subset_Iic T hT

theorem arcInterval_regular_subset_ancient (T : Real) (hT : 0 < T) :
    (arcInterval T).regular ⊆ CanonicalNeighborhood.ancientTimeInterval.regular := by
  rw [arcInterval_regular hT, CanonicalNeighborhood.ancientTimeInterval_regular]
  exact fun t ht => ht.2

noncomputable def sameManifoldWindowRestrict
    (L : PointedFlowData.{u, uE, uH} (I := I) CanonicalNeighborhood.ancientTimeInterval)
    (m : Nat) : PointedFlowData.{u, uE, uH} (I := I) (arcInterval (windowHorizon m)) :=
  L.timeRestrict (arcInterval (windowHorizon m))
    (arcInterval_carrier_subset_ancient (windowHorizon m) (windowHorizon_pos m))
    (arcInterval_regular_subset_ancient (windowHorizon m) (windowHorizon_pos m))

@[simp] theorem sameManifoldWindowRestrict_atTime
    (L : PointedFlowData.{u, uE, uH} (I := I) CanonicalNeighborhood.ancientTimeInterval)
    (m : Nat) (t : Real) :
    (sameManifoldWindowRestrict (I := I) L m).atTime t = L.atTime t := rfl

def SameManifoldWindowLimitGlue (Y : SameManifoldFlowSeq.{u, uE, uH} I M)
    (hT : Tendsto Y.horizon atTop atTop) (phi : Nat → Nat)
    (L : PointedFlowData.{u, uE, uH} (I := I) CanonicalNeighborhood.ancientTimeInterval) : Prop :=
  ∀ m : Nat, Nonempty (SmoothCGHConverges (I := I) (Y.toFiniteArcFlowSeq.windowSeq hT m)
    (sameManifoldWindowRestrict (I := I) L m) (fun k => phi (m + k)))

def SameManifoldWindowSliceGlue (Y : SameManifoldFlowSeq.{u, uE, uH} I M)
    (hT : Tendsto Y.horizon atTop atTop) (phi : Nat → Nat)
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : Prop :=
  ∀ m : Nat, Nonempty (PointedCGHMaps (I := I) (Y.toFiniteArcFlowSeq.windowSeq hT m) P
    (fun k => phi (m + k)))

theorem sameManifoldWindowSliceGlue_of_limitGlue
    (Y : SameManifoldFlowSeq.{u, uE, uH} I M) (hT : Tendsto Y.horizon atTop atTop)
    (phi : Nat → Nat)
    (L : PointedFlowData.{u, uE, uH} (I := I) CanonicalNeighborhood.ancientTimeInterval)
    (h : SameManifoldWindowLimitGlue Y hT phi L) :
    SameManifoldWindowSliceGlue Y hT phi (L.atTime 0) :=
  fun m => (h m).map fun c => c.spatial.maps

theorem sameManifoldWindowSliceGlue_of_diffeomorphFamily
    (Y : SameManifoldFlowSeq.{u, uE, uH} I M) (hT : Tendsto Y.horizon atTop atTop)
    (p : M) (g : SmoothRiemannianMetric I M) (phi : Nat → Nat)
    (Phi : Nat → Nat → Diffeomorph I I M M (∞ : WithTop ℕ∞))
    (hbase : ∀ m k : Nat,
      Phi m k p = (Y.toFiniteArcFlowSeq.windowSeq hT m).basepoint (phi (m + k))) :
    SameManifoldWindowSliceGlue Y hT phi (Y.windowPointedManifold p g) :=
  fun m =>
    ⟨PointedCGHMaps.ofDiffeomorphFamily (I := I)
      (X := Y.toFiniteArcFlowSeq.windowSeq hT m) (P := Y.windowPointedManifold p g)
      (subseq := fun k => phi (m + k)) (fun k => Phi m k) (fun k => hbase m k)⟩

theorem exists_windowSliceLimit_pair_of_diffeomorphFamily
    (Y : SameManifoldFlowSeq.{u, uE, uH} I M) (hT : Tendsto Y.horizon atTop atTop)
    (p : M) (g : SmoothRiemannianMetric I M) (phi : Nat → Nat)
    (Phi : Nat → Nat → Diffeomorph I I M M (∞ : WithTop ℕ∞))
    (hbase : ∀ m k : Nat,
      Phi m k p = (Y.toFiniteArcFlowSeq.windowSeq hT m).basepoint (phi (m + k)))
    (m₁ m₂ : Nat) :
    ∃ P : PointedRiemannianManifold.{u, uE, uH} (I := I),
      Nonempty (PointedCGHMaps (I := I) (Y.toFiniteArcFlowSeq.windowSeq hT m₁) P
        (fun k => phi (m₁ + k))) ∧
      Nonempty (PointedCGHMaps (I := I) (Y.toFiniteArcFlowSeq.windowSeq hT m₂) P
        (fun k => phi (m₂ + k))) :=
  ⟨Y.windowPointedManifold p g,
    sameManifoldWindowSliceGlue_of_diffeomorphFamily Y hT p g phi Phi hbase m₁,
    sameManifoldWindowSliceGlue_of_diffeomorphFamily Y hT p g phi Phi hbase m₂⟩

theorem sameManifoldWindowSliceConvergenceMaps_of_limitGlue
    [I.Boundaryless] (Y : SameManifoldFlowSeq.{u, uE, uH} I M)
    (hT : Tendsto Y.horizon atTop atTop) (phi : Nat → Nat) (t : Real)
    (L : PointedFlowData.{u, uE, uH} (I := I) CanonicalNeighborhood.ancientTimeInterval)
    (h : SameManifoldWindowLimitGlue Y hT phi L) :
    ∀ m : Nat, Nonempty (PointedRiemannianConvergenceMaps (I := I)
      ((Y.toFiniteArcFlowSeq.windowSeq hT m).atTime t) (L.atTime t) (fun k => phi (m + k))) :=
  fun m => (h m).map fun c => c.spatial.maps.atTimeSlice t

noncomputable def staticLineSameManifoldFlowSeq :
    SameManifoldFlowSeq.{0, 0, 0} 𝓘(Real, Real) Real where
  horizon n := (n : Real) + 1
  horizon_pos n := by positivity
  basepoint _ := 0
  t2TangentBundle := inferInstance
  solution n := SolutionOn.const (euclideanMetric (E := Real)) (arcInterval ((n : Real) + 1))
  isSolution n := isSolutionOn_const_euclidean_real (arcInterval ((n : Real) + 1))

theorem staticLineSameManifoldFlowSeq_horizon_tendsto :
    Tendsto staticLineSameManifoldFlowSeq.horizon atTop atTop := by
  have h : Tendsto (fun n : Nat => ((n + 1 : Nat) : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  simpa [staticLineSameManifoldFlowSeq, Nat.cast_add, Nat.cast_one, add_comm] using h

theorem sameManifoldWindowSliceGlue_staticLine (phi : Nat → Nat) :
    SameManifoldWindowSliceGlue staticLineSameManifoldFlowSeq
      staticLineSameManifoldFlowSeq_horizon_tendsto phi
      (staticLineSameManifoldFlowSeq.windowPointedManifold 0 (euclideanMetric (E := Real))) :=
  sameManifoldWindowSliceGlue_of_diffeomorphFamily staticLineSameManifoldFlowSeq
    staticLineSameManifoldFlowSeq_horizon_tendsto 0 (euclideanMetric (E := Real)) phi
    (fun _ _ => Diffeomorph.refl 𝓘(Real, Real) Real (∞ : WithTop ℕ∞))
    (fun _ _ => rfl)

def SameManifoldWindowLimitUniqueness (Y : SameManifoldFlowSeq.{u, uE, uH} I M)
    (hT : Tendsto Y.horizon atTop atTop) (phi : Nat → Nat) : Prop :=
  ∀ (L₁ L₂ : PointedFlowData.{u, uE, uH} (I := I) CanonicalNeighborhood.ancientTimeInterval),
    SameManifoldWindowLimitGlue Y hT phi L₁ → SameManifoldWindowLimitGlue Y hT phi L₂ →
      ∀ m : Nat, Nonempty (PointedRiemannianManifold.PointedlyIsometric (I := I)
        ((sameManifoldWindowRestrict (I := I) L₁ m).atTime 0)
        ((sameManifoldWindowRestrict (I := I) L₂ m).atTime 0))

theorem sameManifoldWindowLimitUniqueness_of_pointedlyIdentified
    (Y : SameManifoldFlowSeq.{u, uE, uH} I M) (hT : Tendsto Y.horizon atTop atTop)
    (phi : Nat → Nat)
    (h : ∀ (L₁ L₂ : PointedFlowData.{u, uE, uH} (I := I)
        CanonicalNeighborhood.ancientTimeInterval)
      (c₁ : ∀ m : Nat, SmoothCGHConverges (I := I) (Y.toFiniteArcFlowSeq.windowSeq hT m)
        (sameManifoldWindowRestrict (I := I) L₁ m) (fun k => phi (m + k)))
      (c₂ : ∀ m : Nat, SmoothCGHConverges (I := I) (Y.toFiniteArcFlowSeq.windowSeq hT m)
        (sameManifoldWindowRestrict (I := I) L₂ m) (fun k => phi (m + k))),
      ∀ m : Nat, (c₁ m).spatial.maps.PointedlyIdentified (c₂ m).spatial.maps) :
    SameManifoldWindowLimitUniqueness Y hT phi :=
  fun L₁ L₂ h₁ h₂ m =>
    ⟨PointedCGHMaps.pointedlyIsometric_of_pointedlyIdentified (I := I) _
      _ (h L₁ L₂ (fun m => Classical.choice (h₁ m)) (fun m => Classical.choice (h₂ m)) m)⟩

omit [SigmaCompactSpace M] in
def SameManifoldWindowLimitEquationInput (gInf : Real → SmoothRiemannianMetric I M) : Prop :=
  Nonempty (SameManifoldLimitEquationData (I := I) gInf
    CanonicalNeighborhood.ancientTimeInterval)

omit [SigmaCompactSpace M] in
theorem exists_solutionOn_of_sameManifoldWindowLimitEquationInput
    (gInf : Real → SmoothRiemannianMetric I M)
    (h : SameManifoldWindowLimitEquationInput (I := I) gInf) :
    ∃ S : SolutionOn (I := I) (M := M) CanonicalNeighborhood.ancientTimeInterval,
      IsSolutionOn (I := I) S ∧
        ∀ t : Real, t ∈ CanonicalNeighborhood.ancientTimeInterval.carrier →
          S.family.metric t = gInf t := by
  obtain ⟨H⟩ := h
  exact ⟨H.solution, H.isSolution, H.agrees⟩

def SameManifoldWindowCanonicalSourceInput
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : Nat → Nat}
    (F : PointedRiemannianConvergenceMaps (I := I) X P subseq)
    (C : MetricConvergenceData (I := I) F) : Prop :=
  ∀ k : Nat, C.domain k = CanonicalMetricCompactness.canonicalSourceData (I := I) F k

theorem metricSourceConvergesOn_canonicalSourceData_of_input
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : Nat → Nat}
    {F : PointedRiemannianConvergenceMaps (I := I) X P subseq}
    {C : MetricConvergenceData (I := I) F}
    (h : SameManifoldWindowCanonicalSourceInput F C) :
    letI : TopologicalSpace P.M := P.topology
    ∀ K : Set P.M, IsCompact K → ∀ p : Nat,
      metricSourceConvergesOn (I := I) F
        (CanonicalMetricCompactness.canonicalSourceData (I := I) F) K p := by
  intro K hK p ε hε
  obtain ⟨k0, hk0⟩ := C.converges K hK p ε hε
  exact ⟨k0, fun k hk => by rw [← h k]; exact hk0 k hk⟩

theorem exists_canonicalSourceInput_of_derivNormSupOn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : Nat → Nat}
    (F : PointedRiemannianConvergenceMaps (I := I) X P subseq)
    (hconv :
      letI : TopologicalSpace P.M := P.topology
      ∀ K : Set P.M, IsCompact K → ∀ p : Nat, ∀ ε : Real, 0 < ε →
        ∃ k0 : Nat, ∀ k : Nat, k0 ≤ k →
          (CanonicalMetricCompactness.canonicalSourceData (I := I) F k).derivNormSupOn
            (I := I) K p < ε) :
    ∃ C : MetricConvergenceData (I := I) F, SameManifoldWindowCanonicalSourceInput F C :=
  let ⟨C, hC, _⟩ :=
    exists_metricConvergenceData_canonicalSourceData (I := I) F hconv
  ⟨C, hC⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology (ThreeModel ThreeSpace)
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
  (MetricComparisonOn)
open scoped _root_.Manifold ContDiff _root_.Topology

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
variable [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]

def SameManifoldWindowComparisonTowerInput
    (Y : SameManifoldFlowSeq.{u, 0, 0} ThreeModel M)
    (hT : Tendsto Y.horizon atTop atTop) (m : Nat) (phi : Nat → Nat)
    (L : PointedFlowData.{u, 0, 0} (I := ThreeModel) CanonicalNeighborhood.ancientTimeInterval)
    (F : PointedRiemannianConvergenceMaps (I := ThreeModel)
      ((Y.toFiniteArcFlowSeq.windowSeq hT m).atTime (I := ThreeModel) 0)
      (L.atTime (I := ThreeModel) 0) (fun k => phi (m + k))) : Prop :=
  ∀ K : Set L.M, IsCompact K → ∀ A : Real, 0 < A →
    ∀ order : Nat, ∀ eta : Real, 0 < eta → ∀ᶠ k in Filter.atTop,
      K ⊆ (F.partialDiffeomorph k).source ∧
        Nonempty (MetricComparisonOn (fun s : Real => L.S.base.metric s)
          (Y.windowMetricFamily (Y.toFiniteArcFlowSeq.windowShift hT m) (phi (m + k)))
          (fun x : L.M => F.map k x) K (Set.Icc (-A) 0) order eta)

theorem eventually_inner_bounds_of_windowComparisonTowerInput
    (Y : SameManifoldFlowSeq.{u, 0, 0} ThreeModel M)
    (hT : Tendsto Y.horizon atTop atTop) (m : Nat) (phi : Nat → Nat)
    (L : PointedFlowData.{u, 0, 0} (I := ThreeModel) CanonicalNeighborhood.ancientTimeInterval)
    (F : PointedRiemannianConvergenceMaps (I := ThreeModel)
      ((Y.toFiniteArcFlowSeq.windowSeq hT m).atTime (I := ThreeModel) 0)
      (L.atTime (I := ThreeModel) 0) (fun k => phi (m + k)))
    (h : SameManifoldWindowComparisonTowerInput Y hT m phi L F) :
    ∀ K : Set L.M, IsCompact K → ∀ A : Real, 0 < A → ∀ eta : Real, 0 < eta →
      ∀ᶠ k in Filter.atTop, ∀ s : Real, s ∈ Set.Icc (-A) 0 → ∀ y : L.M, y ∈ K →
        ∀ v : TangentSpace ThreeModel y,
          (1 - eta) * (L.S.base.metric s).inner y v v ≤
              (Y.windowMetricFamily (Y.toFiniteArcFlowSeq.windowShift hT m)
                  (phi (m + k)) s).inner (F.map k y)
                (mfderiv ThreeModel ThreeModel (fun x : L.M => F.map k x) y v)
                (mfderiv ThreeModel ThreeModel (fun x : L.M => F.map k x) y v) ∧
            (Y.windowMetricFamily (Y.toFiniteArcFlowSeq.windowShift hT m)
                (phi (m + k)) s).inner (F.map k y)
              (mfderiv ThreeModel ThreeModel (fun x : L.M => F.map k x) y v)
              (mfderiv ThreeModel ThreeModel (fun x : L.M => F.map k x) y v) ≤
              (1 + eta) * (L.S.base.metric s).inner y v v := by
  intro K hK A hA eta heta
  filter_upwards [h K hK A hA 0 eta heta] with k hk s hs y hy v
  let C := hk.2.some
  have hp := C.pullback_eq s y hy (fun _ => v)
  have he := C.equivalence s hs y hy v
  rw [hp] at he
  exact he

theorem exists_jet_bound_of_windowComparisonTowerInput
    (Y : SameManifoldFlowSeq.{u, 0, 0} ThreeModel M)
    (hT : Tendsto Y.horizon atTop atTop) (m : Nat) (phi : Nat → Nat)
    (L : PointedFlowData.{u, 0, 0} (I := ThreeModel) CanonicalNeighborhood.ancientTimeInterval)
    (F : PointedRiemannianConvergenceMaps (I := ThreeModel)
      ((Y.toFiniteArcFlowSeq.windowSeq hT m).atTime (I := ThreeModel) 0)
      (L.atTime (I := ThreeModel) 0) (fun k => phi (m + k)))
    (h : SameManifoldWindowComparisonTowerInput Y hT m phi L F) :
    ∀ K : Set L.M, IsCompact K → ∀ A : Real, 0 < A →
      ∀ order : Nat, ∀ eta : Real, 0 < eta → ∀ᶠ k in Filter.atTop,
        K ⊆ (F.partialDiffeomorph k).source ∧
          ∃ C : MetricComparisonOn (fun s : Real => L.S.base.metric s)
              (Y.windowMetricFamily (Y.toFiniteArcFlowSeq.windowShift hT m) (phi (m + k)))
              (fun x : L.M => F.map k x) K (Set.Icc (-A) 0) order eta,
            ∀ (a b : Nat), a + 2 * b ≤ order → ∀ s : Real, s ∈ Set.Icc (-A) 0 →
              ∀ y : L.M, y ∈ K →
                tensor02CovDerivNormWith (I := ThreeModel) a (C.jet b s)
                  (L.S.base.metric s) (L.S.base.metric s) y ≤ eta := by
  intro K hK A hA order eta heta
  filter_upwards [h K hK A hA order eta heta] with k hk
  exact ⟨hk.1, hk.2.some, fun a b hab s hs y hy => hk.2.some.close a b hab s hs y hy⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
