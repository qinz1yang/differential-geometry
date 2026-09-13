import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.BelowScaleVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Invariance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.MetricStep

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [T2Space M] [SigmaCompactSpace M]
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

open DifferentialGeometry.PDE.RicciFlow.Perelman (FlowMetricBall KappaNoncollapsedBelowScale
  SpatiallyKappaNoncollapsedBelowScale kappaNoncollapsedBelowScale_of_metric_eqOn
  spatiallyKappaNoncollapsedBelowScale_of_metric_eqOn)

def surgeryRegion (S S' : SolutionOn (I := I) (M := M) D) : Set (Real × M) :=
  {p | ∃ V W : TangentSpace I p.2,
    (S'.base.metric p.1).inner p.2 V W ≠ (S.base.metric p.1).inner p.2 V W}

omit [FiniteDimensional Real E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem mem_surgeryRegion_iff (S S' : SolutionOn (I := I) (M := M) D) (p : Real × M) :
    p ∈ surgeryRegion S S' ↔ ∃ V W : TangentSpace I p.2,
      (S'.base.metric p.1).inner p.2 V W ≠ (S.base.metric p.1).inner p.2 V W :=
  Iff.rfl

omit [FiniteDimensional Real E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem not_mem_surgeryRegion_iff (S S' : SolutionOn (I := I) (M := M) D) (p : Real × M) :
    p ∉ surgeryRegion S S' ↔ ∀ V W : TangentSpace I p.2,
      (S'.base.metric p.1).inner p.2 V W = (S.base.metric p.1).inner p.2 V W := by
  rw [mem_surgeryRegion_iff]
  constructor
  · intro h V W
    by_contra hne
    exact h ⟨V, W, hne⟩
  · rintro h ⟨V, W, hne⟩
    exact hne (h V W)

omit [FiniteDimensional Real E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem metric_eq_of_forall_not_mem_surgeryRegion (S S' : SolutionOn (I := I) (M := M) D)
    {s : Real} (h : ∀ x : M, (s, x) ∉ surgeryRegion S S') :
    S'.base.metric s = S.base.metric s := by
  refine SmoothRiemannianMetric.ext_inner fun x v w => ?_
  exact ((not_mem_surgeryRegion_iff S S' (s, x)).1 (h x)) v w

omit [FiniteDimensional Real E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem surgeryRegion_self (S : SolutionOn (I := I) (M := M) D) :
    surgeryRegion S S = ∅ := by
  ext p
  rw [mem_surgeryRegion_iff]
  simp

def surgeryRegionMissesParabolicBalls (S S' : SolutionOn (I := I) (M := M) D)
    (rho : Real) : Prop :=
  ∀ (t : D.FlowTime) (r : Real), 0 < r → r ≤ rho →
    ∀ s ∈ Set.Icc ((t : Real) - r ^ 2) (t : Real), ∀ x : M, (s, x) ∉ surgeryRegion S S'

omit [FiniteDimensional Real E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem surgeryRegionMissesParabolicBalls_iff (S S' : SolutionOn (I := I) (M := M) D)
    (rho : Real) :
    surgeryRegionMissesParabolicBalls S S' rho ↔
      ∀ (t : D.FlowTime) (r : Real), 0 < r → r ≤ rho →
        ∀ s ∈ Set.Icc ((t : Real) - r ^ 2) (t : Real),
          S'.base.metric s = S.base.metric s := by
  constructor
  · intro h t r hr hrle s hs
    exact metric_eq_of_forall_not_mem_surgeryRegion S S' fun x => h t r hr hrle s hs x
  · intro h t r hr hrle s hs x
    rw [not_mem_surgeryRegion_iff]
    intro V W
    rw [h t r hr hrle s hs]

omit [FiniteDimensional Real E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem surgeryRegionMissesParabolicBalls_self (S : SolutionOn (I := I) (M := M) D)
    (rho : Real) :
    surgeryRegionMissesParabolicBalls S S rho := by
  intro t r hr hrle s hs x
  rw [surgeryRegion_self S]
  exact Set.notMem_empty (s, x)

omit [FiniteDimensional Real E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem exists_surgeryRegion_of_not_surgeryRegionMissesParabolicBalls
    (S S' : SolutionOn (I := I) (M := M) D) {rho : Real}
    (h : ¬ surgeryRegionMissesParabolicBalls S S' rho) :
    ∃ (t : D.FlowTime) (r s : Real) (x : M), 0 < r ∧ r ≤ rho ∧
      s ∈ Set.Icc ((t : Real) - r ^ 2) (t : Real) ∧ (s, x) ∈ surgeryRegion S S' := by
  by_contra hc
  refine h ?_
  rw [surgeryRegionMissesParabolicBalls_iff]
  intro t r hr hrle s hs
  refine SmoothRiemannianMetric.ext_inner fun x v w => ?_
  by_contra hne
  exact hc ⟨t, r, s, x, hr, hrle, hs, ⟨v, w, hne⟩⟩

omit [FiniteDimensional Real E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem surgeryRegionMissesParabolicBalls_mono (S S' : SolutionOn (I := I) (M := M) D)
    {rho rho' : Real} (h : rho ≤ rho')
    (hmiss : surgeryRegionMissesParabolicBalls S S' rho') :
    surgeryRegionMissesParabolicBalls S S' rho :=
  fun t r hr hrle => hmiss t r hr (le_trans hrle h)

omit [FiniteDimensional Real E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem surgeryRegionMissesParabolicBalls_comp (S S' S'' : SolutionOn (I := I) (M := M) D)
    (rho : Real) (h₁ : surgeryRegionMissesParabolicBalls S S' rho)
    (h₂ : surgeryRegionMissesParabolicBalls S' S'' rho) :
    surgeryRegionMissesParabolicBalls S S'' rho := by
  have h₁' := (surgeryRegionMissesParabolicBalls_iff S S' rho).1 h₁
  have h₂' := (surgeryRegionMissesParabolicBalls_iff S' S'' rho).1 h₂
  exact (surgeryRegionMissesParabolicBalls_iff S S'' rho).2 fun t r hr hrle s hs => by
    rw [h₂' t r hr hrle s hs, h₁' t r hr hrle s hs]

theorem kappaNoncollapsedBelowScale_of_surgeryRegionMisses
    (S S' : SolutionOn (I := I) (M := M) D) (kappa rho : Real)
    (h : KappaNoncollapsedBelowScale S kappa rho)
    (hmiss : surgeryRegionMissesParabolicBalls S S' rho) :
    KappaNoncollapsedBelowScale S' kappa rho :=
  kappaNoncollapsedBelowScale_of_metric_eqOn S S' kappa rho h
    ((surgeryRegionMissesParabolicBalls_iff S S' rho).1 hmiss)

theorem spatiallyKappaNoncollapsedBelowScale_of_surgeryRegionMisses
    (S S' : SolutionOn (I := I) (M := M) D) (kappa rho : Real)
    (h : SpatiallyKappaNoncollapsedBelowScale S kappa rho)
    (hmiss : surgeryRegionMissesParabolicBalls S S' rho) :
    SpatiallyKappaNoncollapsedBelowScale S' kappa rho :=
  spatiallyKappaNoncollapsedBelowScale_of_metric_eqOn S S' kappa rho h fun t r hr hrle =>
    metric_eq_of_forall_not_mem_surgeryRegion S S' fun x =>
      hmiss t r hr hrle (t : Real) ⟨by linarith [sq_nonneg r], le_rfl⟩ x

end DifferentialGeometry.PDE.RicciFlow.Surgery

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

section OldData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M]
variable [IsManifold ThreeModel 1 M]
variable [T2Space M] [SigmaCompactSpace M]
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

open DifferentialGeometry.PDE.RicciFlow.Perelman (KappaNoncollapsedBelowScale FlowMetricBall
  mul_pow_le_volume_toReal_of_kappaNoncollapsedBelowScale)

def OldData.noncollapsingBelowScale (d : OldData)
    (S : SolutionOn (I := ThreeModel) (M := M) D) (rho : Real) : Prop :=
  KappaNoncollapsedBelowScale S d.noncollapsing rho

theorem OldData.noncollapsingBelowScale_iff (d : OldData)
    (S : SolutionOn (I := ThreeModel) (M := M) D) (rho : Real) :
    d.noncollapsingBelowScale S rho ↔ KappaNoncollapsedBelowScale S d.noncollapsing rho :=
  Iff.rfl

theorem OldData.noncollapsingBelowScale_scale_pos (d : OldData)
    (S : SolutionOn (I := ThreeModel) (M := M) D) {rho : Real}
    (h : d.noncollapsingBelowScale S rho) : 0 < rho :=
  h.1

theorem OldData.noncollapsingBelowScale_of_surgeryRegionMisses (d : OldData)
    (S S' : SolutionOn (I := ThreeModel) (M := M) D) (rho : Real)
    (h : d.noncollapsingBelowScale S rho)
    (hmiss : surgeryRegionMissesParabolicBalls S S' rho) :
    d.noncollapsingBelowScale S' rho :=
  kappaNoncollapsedBelowScale_of_surgeryRegionMisses S S' d.noncollapsing rho h hmiss

theorem OldData.mul_pow_le_volume_toReal_of_noncollapsingBelowScale (d : OldData)
    (S : SolutionOn (I := ThreeModel) (M := M) D) {rho : Real}
    (h : d.noncollapsingBelowScale S rho) {t : D.FlowTime} (B : FlowMetricBall S t)
    (hr : B.radius ≤ rho) (hB : B.IsRmControlled) (hvol : B.volume ≠ ⊤) :
    d.noncollapsing * B.radius ^ Module.finrank Real ThreeSpace ≤ (B.volume).toReal :=
  mul_pow_le_volume_toReal_of_kappaNoncollapsedBelowScale S h B hr hB hvol

theorem OldData.not_noncollapsingBelowScale_of_volume_toReal_lt (d : OldData)
    (S : SolutionOn (I := ThreeModel) (M := M) D) {rho : Real} {t : D.FlowTime}
    (B : FlowMetricBall S t) (hr : B.radius ≤ rho) (hB : B.IsRmControlled)
    (hvol : B.volume ≠ ⊤)
    (hlt : (B.volume).toReal < d.noncollapsing * B.radius ^ Module.finrank Real ThreeSpace) :
    ¬ d.noncollapsingBelowScale S rho := fun h =>
  absurd (OldData.mul_pow_le_volume_toReal_of_noncollapsingBelowScale d S h B hr hB hvol)
    (not_le_of_gt hlt)

end OldData

section Data

theorem exists_oldData_noncollapsing_eq (v : Real) (hv : 0 < v) :
    ∃ d : OldData, d.noncollapsing = v :=
  ⟨{ horizon := 1
     horizon_pos := one_pos
     initialParameter := 1
     initialParameter_pos := one_pos
     epsilon := 1
     epsilon_pos := one_pos
     comparisonConstant := 1
     comparisonConstant_pos := one_pos
     volumeConstant := 1
     volumeConstant_pos := one_pos
     scaleLower := 1
     scaleLower_pos := one_pos
     noncollapsing := v
     noncollapsing_pos := hv
     olderLength := 1
     olderLength_pos := one_pos
     energyBound := 1
     olderLength_le_energy := le_rfl }, rfl⟩

theorem isEnlargementInput_iff_forall_exists :
    isEnlargementInput.{u} ↔
      ∀ d : OldData, ∃ α : Real, 0 < α ∧ α ≤ 1 / 100 ∧ ∃ sstar : Real, 0 < sstar ∧
        sstar ≤ d.epsilon / 2 ∧
          ∀ (H : ObservedHistory.{u}) (S : EnlargementStrip H),
            S.radius < min (α * d.scaleLower) (sstar / 4) →
            Nonempty (EnlargementConclusion S) :=
  ⟨fun h d => h d d.noncollapsing_pos, fun h d _ => h d⟩

end Data

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
