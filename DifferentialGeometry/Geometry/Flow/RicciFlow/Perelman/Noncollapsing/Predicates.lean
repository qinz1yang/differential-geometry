import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Curvature.ScalarBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Scale.Collapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Scale.Transfer
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

noncomputable section

universe u uE uH

open Bundle DifferentialGeometry.Tensor0SBundle MeasureTheory
open scoped Manifold ContDiff ENNReal

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [T2Space M] [SigmaCompactSpace M]
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

namespace FlowMetricBall

variable {S : SolutionOn (I := I) (M := M) D}
variable {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}

def IsSpatiallyRmControlled (B : FlowMetricBall S time) : Prop :=
  ∀ x ∈ B.set, B.radius ^ 4 * rmNormSq S (time : Real) x ≤ 1

def IsSpatiallyKappaNoncollapsed (kappa : Real) (B : FlowMetricBall S time) : Prop :=
  B.IsSpatiallyRmControlled → B.IsKappaNoncollapsed kappa

def IsScalarControlled (B : FlowMetricBall S time) : Prop :=
  ∀ x ∈ B.set, B.radius ^ 2 * S.scalar (time : Real) x ≤ 1

def IsStronglyScalarKappaNoncollapsed (kappa : Real) (B : FlowMetricBall S time) : Prop :=
  B.IsScalarControlled →
    ∀ B' : FlowMetricBall S time, B'.center = B.center → B'.radius ≤ B.radius →
      B'.IsKappaNoncollapsed kappa

omit [SigmaCompactSpace M] in
theorem isSpatiallyRmControlled_of_isRmControlled (B : FlowMetricBall S time)
    (hB : B.IsRmControlled) : B.IsSpatiallyRmControlled := by
  intro x hx
  refine hB.2 (time : Real) ⟨?_, le_rfl⟩ x hx
  linarith [sq_nonneg B.radius]

end FlowMetricBall

def SpatiallyKappaNoncollapsedBelowScale
    (S : SolutionOn (I := I) (M := M) D) (kappa rho : Real) : Prop :=
  0 < rho ∧ ∀ (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D)
    (B : FlowMetricBall S t), B.radius ≤ rho →
    B.IsSpatiallyKappaNoncollapsed kappa

def SpatialNoLocalCollapsing
    (S : SolutionOn (I := I) (M := M) D) (rho : Real) : Prop :=
  ∃ kappa : Real, 0 < kappa ∧ SpatiallyKappaNoncollapsedBelowScale S kappa rho


def StronglyScalarKappaNoncollapsedBelowScale
    (S : SolutionOn (I := I) (M := M) D) (kappa rho : Real) : Prop :=
  0 < rho ∧ ∀ (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D)
    (B : FlowMetricBall S t), B.radius ≤ rho →
    B.IsStronglyScalarKappaNoncollapsed kappa

def StrongScalarNoLocalCollapsing
    (S : SolutionOn (I := I) (M := M) D) (rho : Real) : Prop :=
  ∃ kappa : Real, 0 < kappa ∧ StronglyScalarKappaNoncollapsedBelowScale S kappa rho

theorem kappaNoncollapsedBelowScale_of_spatially
    {S : SolutionOn (I := I) (M := M) D} {kappa rho : Real}
    (h : SpatiallyKappaNoncollapsedBelowScale S kappa rho) :
    KappaNoncollapsedBelowScale S kappa rho :=
  ⟨h.1, fun t B hr hB =>
    h.2 t B hr (B.isSpatiallyRmControlled_of_isRmControlled hB)⟩

theorem noLocalCollapsing_of_spatial
    {S : SolutionOn (I := I) (M := M) D} {rho : Real}
    (h : SpatialNoLocalCollapsing S rho) : NoLocalCollapsing S rho := by
  obtain ⟨kappa, hkappa, hbelow⟩ := h
  exact ⟨kappa, hkappa, kappaNoncollapsedBelowScale_of_spatially hbelow⟩

def scalarFromRmConst (n : Nat) : Real := max 1 ((n : Real) ^ 2)

theorem one_le_scalarFromRmConst (n : Nat) : 1 ≤ scalarFromRmConst n := le_max_left _ _


def scalarFromRmRadius (n : Nat) : Real := Real.sqrt (scalarFromRmConst n)

theorem one_le_scalarFromRmRadius (n : Nat) : 1 ≤ scalarFromRmRadius n := by
  have h : Real.sqrt 1 ≤ Real.sqrt (scalarFromRmConst n) :=
    Real.sqrt_le_sqrt (one_le_scalarFromRmConst n)
  rw [Real.sqrt_one] at h
  exact h

theorem scalarFromRmRadius_pos (n : Nat) : 0 < scalarFromRmRadius n :=
  lt_of_lt_of_le zero_lt_one (one_le_scalarFromRmRadius n)

theorem sq_scalarFromRmRadius (n : Nat) :
    scalarFromRmRadius n ^ 2 = scalarFromRmConst n :=
  Real.sq_sqrt (le_trans zero_le_one (one_le_scalarFromRmConst n))

omit [SigmaCompactSpace M] in
theorem scalar_le_of_spatial_rm
    {S : SolutionOn (I := I) (M := M) D}
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsSpatiallyRmControlled)
    {x : M} (hx : x ∈ B.set) :
    B.radius ^ 2 * S.scalar (time : Real) x ≤ (Module.finrank Real E : Real) ^ 2 := by
  have hscalar' :
      |DifferentialGeometry.Geometry.Curvature.metricScalarAt
          (I := I) (M := M) (S.base.metric (time : Real)) x| ≤
        (Module.finrank Real E : Real) ^ 2 *
          Real.sqrt (FlowMetricBall.rmNormSq S (time : Real) x) := by
    simpa only [FlowMetricBall.rmNormSq, SolutionFamily.rm04,
      DifferentialGeometry.Geometry.Curvature.metricRm04_apply,
      show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl] using
        DifferentialGeometry.Geometry.Curvature.scalar_abs_le_rm
          (I := I) (M := M) (S.base.metric (time : Real)) x
  have hr4 : Real.sqrt (B.radius ^ 4) = B.radius ^ 2 := by
    rw [show B.radius ^ 4 = (B.radius ^ 2) ^ 2 by ring,
      Real.sqrt_sq (sq_nonneg B.radius)]
  have hkey : B.radius ^ 2 *
      Real.sqrt (FlowMetricBall.rmNormSq S (time : Real) x) ≤ 1 := by
    calc B.radius ^ 2 * Real.sqrt (FlowMetricBall.rmNormSq S (time : Real) x)
        = Real.sqrt (B.radius ^ 4) *
            Real.sqrt (FlowMetricBall.rmNormSq S (time : Real) x) := by rw [hr4]
      _ = Real.sqrt (B.radius ^ 4 * FlowMetricBall.rmNormSq S (time : Real) x) :=
          (Real.sqrt_mul (by positivity) _).symm
      _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (hB x hx)
      _ = 1 := Real.sqrt_one
  calc B.radius ^ 2 * S.scalar (time : Real) x
      ≤ B.radius ^ 2 *
          |DifferentialGeometry.Geometry.Curvature.metricScalarAt
            (I := I) (M := M) (S.base.metric (time : Real)) x| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (sq_nonneg _)
    _ ≤ B.radius ^ 2 * ((Module.finrank Real E : Real) ^ 2 *
          Real.sqrt (FlowMetricBall.rmNormSq S (time : Real) x)) :=
        mul_le_mul_of_nonneg_left hscalar' (sq_nonneg _)
    _ = (Module.finrank Real E : Real) ^ 2 *
          (B.radius ^ 2 *
            Real.sqrt (FlowMetricBall.rmNormSq S (time : Real) x)) := by ring
    _ ≤ (Module.finrank Real E : Real) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hkey (sq_nonneg _)
    _ = (Module.finrank Real E : Real) ^ 2 := mul_one _

omit [SigmaCompactSpace M] in
theorem FlowMetricBall.isScalarControlled_shrink
    {S : SolutionOn (I := I) (M := M) D}
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsSpatiallyRmControlled)
    (hq : 0 < 1 / scalarFromRmRadius (Module.finrank Real E)) :
    (B.shrink (1 / scalarFromRmRadius (Module.finrank Real E)) hq).IsScalarControlled := by
  intro x hx
  have hcpos : 0 < scalarFromRmRadius (Module.finrank Real E) :=
    scalarFromRmRadius_pos _
  have hq1 : 1 / scalarFromRmRadius (Module.finrank Real E) ≤ 1 :=
    (div_le_one hcpos).2 (one_le_scalarFromRmRadius _)
  have hx0 : x ∈ B.set :=
    FlowMetricBall.shrink_setAt B hq hq1 (time : Real) hx
  have hspat := scalar_le_of_spatial_rm B hB hx0
  have hle : B.radius ^ 2 * S.scalar (time : Real) x ≤
      scalarFromRmRadius (Module.finrank Real E) ^ 2 := by
    rw [sq_scalarFromRmRadius]
    exact hspat.trans (le_max_right _ _)
  have hrw : (1 / scalarFromRmRadius (Module.finrank Real E) * B.radius) ^ 2 *
      S.scalar (time : Real) x =
      (B.radius ^ 2 * S.scalar (time : Real) x) /
        scalarFromRmRadius (Module.finrank Real E) ^ 2 := by
    rw [mul_pow, div_pow, one_pow]
    ring
  change (1 / scalarFromRmRadius (Module.finrank Real E) * B.radius) ^ 2 *
    S.scalar (time : Real) x ≤ 1
  rw [hrw]
  exact (div_le_one (by positivity)).2 hle

theorem spatiallyKappaNoncollapsedBelowScale_of_stronglyScalar
    {S : SolutionOn (I := I) (M := M) D} {kappa rho : Real}
    (hS : StronglyScalarKappaNoncollapsedBelowScale S kappa rho) :
    SpatiallyKappaNoncollapsedBelowScale S
      (kappa / scalarFromRmRadius (Module.finrank Real E) ^ Module.finrank Real E)
      (scalarFromRmRadius (Module.finrank Real E) * rho) := by
  refine ⟨mul_pos (scalarFromRmRadius_pos _) hS.1, ?_⟩
  intro t B hrho hB
  have hcpos : 0 < scalarFromRmRadius (Module.finrank Real E) :=
    scalarFromRmRadius_pos _
  have hqpos : 0 < 1 / scalarFromRmRadius (Module.finrank Real E) :=
    one_div_pos.mpr hcpos
  have hq1 : 1 / scalarFromRmRadius (Module.finrank Real E) ≤ 1 :=
    (div_le_one hcpos).2 (one_le_scalarFromRmRadius _)
  have hrad : (B.shrink (1 / scalarFromRmRadius (Module.finrank Real E)) hqpos).radius
      ≤ rho := by
    change 1 / scalarFromRmRadius (Module.finrank Real E) * B.radius ≤ rho
    rw [div_mul_eq_mul_div, one_mul]
    exact (div_le_iff₀ hcpos).2 (by simpa only [mul_comm] using hrho)
  have hsc := FlowMetricBall.isScalarControlled_shrink B hB hqpos
  have hk := hS.2 t (B.shrink (1 / scalarFromRmRadius (Module.finrank Real E)) hqpos)
    hrad hsc (B.shrink (1 / scalarFromRmRadius (Module.finrank Real E)) hqpos) rfl le_rfl
  have hvol : (B.shrink (1 / scalarFromRmRadius (Module.finrank Real E)) hqpos).volume
      ≤ B.volume :=
    FlowMetricBall.volume_mono (FlowMetricBall.shrink_nested B hqpos hq1)
  have hkpos : 0 < kappa /
      scalarFromRmRadius (Module.finrank Real E) ^ Module.finrank Real E :=
    div_pos hk.1 (pow_pos hcpos _)
  refine ⟨hkpos, ?_⟩
  have heq : kappa / scalarFromRmRadius (Module.finrank Real E) ^ Module.finrank Real E *
      B.radius ^ Module.finrank Real E =
      kappa * (1 / scalarFromRmRadius (Module.finrank Real E) * B.radius) ^
        Module.finrank Real E := by
    rw [mul_pow, div_pow, one_pow]
    ring
  calc ENNReal.ofReal
        (kappa / scalarFromRmRadius (Module.finrank Real E) ^ Module.finrank Real E) *
        ENNReal.ofReal B.radius ^ Module.finrank Real E
      = ENNReal.ofReal
          (kappa / scalarFromRmRadius (Module.finrank Real E) ^ Module.finrank Real E *
            B.radius ^ Module.finrank Real E) := by
        rw [ENNReal.ofReal_mul hkpos.le, ENNReal.ofReal_pow B.radius_pos.le]
    _ = ENNReal.ofReal (kappa *
          (1 / scalarFromRmRadius (Module.finrank Real E) * B.radius) ^
            Module.finrank Real E) := by rw [heq]
    _ = ENNReal.ofReal kappa *
          ENNReal.ofReal (1 / scalarFromRmRadius (Module.finrank Real E) * B.radius) ^
            Module.finrank Real E := by
        rw [ENNReal.ofReal_mul hk.1.le,
          ENNReal.ofReal_pow (mul_pos hqpos B.radius_pos).le]
    _ ≤ (B.shrink (1 / scalarFromRmRadius (Module.finrank Real E)) hqpos).volume := hk.2
    _ ≤ B.volume := hvol

theorem spatialNoLocalCollapsing_of_strongScalar
    {S : SolutionOn (I := I) (M := M) D} {rho : Real}
    (h : StrongScalarNoLocalCollapsing S rho) :
    SpatialNoLocalCollapsing S (scalarFromRmRadius (Module.finrank Real E) * rho) := by
  obtain ⟨kappa, hkappa, hbelow⟩ := h
  exact ⟨kappa / scalarFromRmRadius (Module.finrank Real E) ^ Module.finrank Real E,
    div_pos hkappa (pow_pos (scalarFromRmRadius_pos _) _),
    spatiallyKappaNoncollapsedBelowScale_of_stronglyScalar hbelow⟩

theorem noLocalCollapsing_of_strongScalar
    {S : SolutionOn (I := I) (M := M) D} {rho : Real}
    (h : StrongScalarNoLocalCollapsing S rho) :
    NoLocalCollapsing S (scalarFromRmRadius (Module.finrank Real E) * rho) :=
  noLocalCollapsing_of_spatial (spatialNoLocalCollapsing_of_strongScalar h)

section Scaling

variable [CompleteSpace E]

omit [SigmaCompactSpace M] in
theorem parabolicBall_spatial_rm
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (parabolicInterval D tau R htau).FlowTime)
    (B : FlowMetricBall S (parabolicFlowTime tau R htau s))
    (hB : B.IsSpatiallyRmControlled) :
    (parabolicBall S tau R hR htau s B).IsSpatiallyRmControlled := by
  intro x hx
  have hx_old : x ∈ B.set := by
    rw [← parabolicBall_set (I := I) S tau R hR htau s B]
    exact hx
  have hold := hB x hx_old
  unfold FlowMetricBall.rmNormSq
  rw [parabolicRmNormSq]
  have hscale : (Real.sqrt R * B.radius) ^ 4 * R⁻¹ ^ 2 = B.radius ^ 4 := by
    rw [mul_pow]
    calc Real.sqrt R ^ 4 * B.radius ^ 4 * R⁻¹ ^ 2
        = (Real.sqrt R ^ 2) ^ 2 * B.radius ^ 4 * R⁻¹ ^ 2 := by ring
      _ = R ^ 2 * B.radius ^ 4 * R⁻¹ ^ 2 := by rw [Real.sq_sqrt hR.le]
      _ = B.radius ^ 4 := by field_simp [ne_of_gt hR]
  calc (Real.sqrt R * B.radius) ^ 4 *
        (R⁻¹ ^ 2 * Tensor0SBundle.normSq0S (I := I)
          (S.base.metric (parabolicTime tau R (s : Real))) x 4
          (S.base.rm04 (parabolicTime tau R (s : Real)) x))
      = ((Real.sqrt R * B.radius) ^ 4 * R⁻¹ ^ 2) *
          Tensor0SBundle.normSq0S (I := I)
            (S.base.metric (parabolicTime tau R (s : Real))) x 4
            (S.base.rm04 (parabolicTime tau R (s : Real)) x) := by ring
    _ = B.radius ^ 4 *
          Tensor0SBundle.normSq0S (I := I)
            (S.base.metric (parabolicTime tau R (s : Real))) x 4
            (S.base.rm04 (parabolicTime tau R (s : Real)) x) := by rw [hscale]
    _ ≤ 1 := hold

omit [SigmaCompactSpace M] in
theorem backBall_spatial_rm
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (parabolicInterval D tau R htau).FlowTime)
    (B : FlowMetricBall (parabolicSolution (I := I) S tau R hR htau) s)
    (hB : B.IsSpatiallyRmControlled) :
    (backBall S tau R hR htau s B).IsSpatiallyRmControlled := by
  intro x hx
  have hset := backBall_setAt (I := I) S tau R hR htau s B (s : Real)
  have hx0 : x ∈ (backBall S tau R hR htau s B).setAt
      (parabolicTime tau R (s : Real)) := hx
  rw [hset] at hx0
  have hold := hB x hx0
  unfold FlowMetricBall.rmNormSq at hold ⊢
  rw [parabolicRmNormSq] at hold
  change (B.radius / Real.sqrt R) ^ 4 *
    Tensor0SBundle.normSq0S (I := I)
      (S.base.metric (parabolicTime tau R (s : Real))) x 4
      (S.base.rm04 (parabolicTime tau R (s : Real)) x) ≤ 1
  have hscale : (B.radius / Real.sqrt R) ^ 4 = B.radius ^ 4 * R⁻¹ ^ 2 := by
    rw [div_pow]
    have hsqrt : Real.sqrt R ^ 4 = R ^ 2 := by
      calc Real.sqrt R ^ 4 = (Real.sqrt R ^ 2) ^ 2 := by ring
        _ = R ^ 2 := by rw [Real.sq_sqrt hR.le]
    rw [hsqrt, div_eq_mul_inv, inv_pow]
  rw [hscale]
  simpa only [mul_assoc] using hold

theorem parabolic_spatial_noncollapse
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (kappa rho : Real)
    (hS : SpatiallyKappaNoncollapsedBelowScale S kappa rho) :
    SpatiallyKappaNoncollapsedBelowScale
      (parabolicSolution (I := I) S tau R hR htau) kappa (Real.sqrt R * rho) := by
  refine ⟨mul_pos (Real.sqrt_pos.2 hR) hS.1, ?_⟩
  intro s B hscale hRm
  have hradius : (backBall S tau R hR htau s B).radius ≤ rho := by
    change B.radius / Real.sqrt R ≤ rho
    apply (div_le_iff₀ (Real.sqrt_pos.2 hR)).2
    simpa only [mul_comm] using hscale
  have hRm₀ : (backBall S tau R hR htau s B).IsSpatiallyRmControlled :=
    backBall_spatial_rm (I := I) S tau R hR htau s B hRm
  have hk₀ := hS.2 (parabolicFlowTime tau R htau s)
    (backBall S tau R hR htau s B) hradius hRm₀
  have hk := parabolicBall_kappa (I := I) S tau R hR htau s
    (backBall S tau R hR htau s B) kappa hk₀
  rw [parabolicBall_back (I := I) S tau R hR htau s B] at hk
  exact hk


theorem parabolic_spatial_no_local
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (rho : Real) (hS : SpatialNoLocalCollapsing S rho) :
    SpatialNoLocalCollapsing (parabolicSolution (I := I) S tau R hR htau)
      (Real.sqrt R * rho) := by
  obtain ⟨kappa, hkappa, hbelow⟩ := hS
  exact ⟨kappa, hkappa,
    parabolic_spatial_noncollapse (I := I) S tau R hR htau kappa rho hbelow⟩

omit [T2Space M] [SigmaCompactSpace M] in
theorem parabolicBall_scalar_controlled
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (parabolicInterval D tau R htau).FlowTime)
    (B : FlowMetricBall S (parabolicFlowTime tau R htau s))
    (hB : B.IsScalarControlled) :
    (parabolicBall S tau R hR htau s B).IsScalarControlled := by
  intro x hx
  have hx_old : x ∈ B.set := by
    rw [← parabolicBall_set (I := I) S tau R hR htau s B]
    exact hx
  have hold := hB x hx_old
  have hsc : (parabolicSolution (I := I) S tau R hR htau).scalar (s : Real) x =
      R⁻¹ * S.scalar (parabolicTime tau R (s : Real)) x :=
    congrFun (congrFun (parabolicSolution_scalar (I := I) S tau R hR htau) (s : Real)) x
  change (Real.sqrt R * B.radius) ^ 2 *
    (parabolicSolution (I := I) S tau R hR htau).scalar (s : Real) x ≤ 1
  rw [hsc, mul_pow, Real.sq_sqrt hR.le,
    show R * B.radius ^ 2 * (R⁻¹ * S.scalar (parabolicTime tau R (s : Real)) x) =
      (R * R⁻¹) * (B.radius ^ 2 * S.scalar (parabolicTime tau R (s : Real)) x) by ring,
    mul_inv_cancel₀ (ne_of_gt hR), one_mul]
  exact hold

omit [T2Space M] [SigmaCompactSpace M] in
theorem backBall_scalar_controlled
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (parabolicInterval D tau R htau).FlowTime)
    (B : FlowMetricBall (parabolicSolution (I := I) S tau R hR htau) s)
    (hB : B.IsScalarControlled) :
    (backBall S tau R hR htau s B).IsScalarControlled := by
  intro x hx
  have hset := backBall_setAt (I := I) S tau R hR htau s B (s : Real)
  have hx0 : x ∈ (backBall S tau R hR htau s B).setAt
      (parabolicTime tau R (s : Real)) := hx
  rw [hset] at hx0
  have hold := hB x hx0
  have hsc : (parabolicSolution (I := I) S tau R hR htau).scalar (s : Real) x =
      R⁻¹ * S.scalar (parabolicTime tau R (s : Real)) x :=
    congrFun (congrFun (parabolicSolution_scalar (I := I) S tau R hR htau) (s : Real)) x
  rw [hsc] at hold
  change (B.radius / Real.sqrt R) ^ 2 *
    S.scalar (parabolicTime tau R (s : Real)) x ≤ 1
  rw [div_pow, Real.sq_sqrt hR.le,
    show B.radius ^ 2 / R * S.scalar (parabolicTime tau R (s : Real)) x =
      B.radius ^ 2 * (R⁻¹ * S.scalar (parabolicTime tau R (s : Real)) x) by
        rw [div_eq_mul_inv]
        ring]
  exact hold

theorem parabolic_strong_scalar_noncollapse
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (kappa rho : Real)
    (hS : StronglyScalarKappaNoncollapsedBelowScale S kappa rho) :
    StronglyScalarKappaNoncollapsedBelowScale
      (parabolicSolution (I := I) S tau R hR htau) kappa (Real.sqrt R * rho) := by
  refine ⟨mul_pos (Real.sqrt_pos.2 hR) hS.1, ?_⟩
  intro s B hscale hsc B' hcenter hradius'
  have hradius : (backBall S tau R hR htau s B).radius ≤ rho := by
    change B.radius / Real.sqrt R ≤ rho
    apply (div_le_iff₀ (Real.sqrt_pos.2 hR)).2
    simpa only [mul_comm] using hscale
  have hsc₀ : (backBall S tau R hR htau s B).IsScalarControlled :=
    backBall_scalar_controlled (I := I) S tau R hR htau s B hsc
  have hstrong := hS.2 (parabolicFlowTime tau R htau s)
    (backBall S tau R hR htau s B) hradius hsc₀
  have hr' : (backBall S tau R hR htau s B').radius ≤
      (backBall S tau R hR htau s B).radius := by
    change B'.radius / Real.sqrt R ≤ B.radius / Real.sqrt R
    exact (div_le_div_iff_of_pos_right (Real.sqrt_pos.2 hR)).2 hradius'
  have hk₀ := hstrong (backBall S tau R hR htau s B') hcenter hr'
  have hk := parabolicBall_kappa (I := I) S tau R hR htau s
    (backBall S tau R hR htau s B') kappa hk₀
  rw [parabolicBall_back (I := I) S tau R hR htau s B'] at hk
  exact hk


theorem parabolic_strong_scalar_no_local
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (rho : Real) (hS : StrongScalarNoLocalCollapsing S rho) :
    StrongScalarNoLocalCollapsing (parabolicSolution (I := I) S tau R hR htau)
      (Real.sqrt R * rho) := by
  obtain ⟨kappa, hkappa, hbelow⟩ := hS
  exact ⟨kappa, hkappa,
    parabolic_strong_scalar_noncollapse (I := I) S tau R hR htau kappa rho hbelow⟩

end Scaling

end

end DifferentialGeometry.PDE.RicciFlow.Perelman
