import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.SecondOrderLift
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.SmallTimeLiftBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.ZeroOrderNonlinearityBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.FixedPoint

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Spectral.MetricRealization

section TimeConst

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [CompleteSpace Y]

def timeConstL2 (T : ℝ) (x : X) : timeL2 X T :=
  (memLp_const (μ := timeMeasure T) (p := 2) x).toLp _

theorem timeConstL2_coeFn (T : ℝ) (x : X) :
    timeConstL2 T x =ᵐ[timeMeasure T] fun _ => x :=
  MemLp.coeFn_toLp _

theorem norm_timeConstL2_le (T : ℝ) (x : X) :
    ‖timeConstL2 T x‖ ≤ ‖x‖ * Real.sqrt T :=
  norm_toLp_le_bd (memLp_const (μ := timeMeasure T) (p := 2) x) (norm_nonneg x)
    (Filter.Eventually.of_forall fun _ => le_rfl)

theorem compLpL_timeConstL2 (L : X →L[ℝ] Y) (T : ℝ) (x : X) :
    L.compLpL 2 (timeMeasure T) (timeConstL2 T x) = timeConstL2 T (L x) := by
  refine Lp.ext ?_
  have h1 := L.coeFn_compLpL (p := 2) (μ := timeMeasure T) (timeConstL2 T x)
  have h2 := timeConstL2_coeFn (X := X) T x
  have h3 := timeConstL2_coeFn (X := Y) T (L x)
  filter_upwards [h1, h2, h3] with t ht1 ht2 ht3
  rw [ht1, ht2, ht3]

end TimeConst

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem timeL2Inclusion_const {g : SmoothRiemannianMetric I M} {τ σ : ℝ}
    (hτσ : τ ≤ σ) (T : ℝ) (x : tensorHs (I := I) (M := M) g 0 2 σ) :
    timeL2Inclusion (I := I) (M := M) (g := g) (r := 0) (s := 2) hτσ
        (timeConstL2 T x) =
      timeConstL2 T
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          hτσ x) :=
  compLpL_timeConstL2 _ T x

def staticForce (g₀ g_bg : SmoothRiemannianMetric I M) (σ : ℝ) :
    tensorHs (I := I) (M := M) g₀ 0 2 σ :=
  smoothCcToTensorHs (I := I) (M := M) g₀ σ
    (deTurckRHSSection (I := I) g_bg g₀)

theorem staticForce_incl (g₀ g_bg : SmoothRiemannianMetric I M) {τ σ : ℝ}
    (hτσ : τ ≤ σ) :
    tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hτσ
        (staticForce (I := I) (M := M) g₀ g_bg σ) =
      staticForce (I := I) (M := M) g₀ g_bg τ :=
  tensorHsInclusion_smoothCcToTensorHs (I := I) (M := M) g₀ hτσ _

theorem staticForce_congr (g₀ g_bg : SmoothRiemannianMetric I M) {a b : ℝ}
    (hab : a = b) :
    tensorHsCongr (I := I) (M := M) g₀ 0 2 hab
        (staticForce (I := I) (M := M) g₀ g_bg a) =
      staticForce (I := I) (M := M) g₀ g_bg b := by
  cases hab
  rfl

theorem staticForcing_eq_zeroStateDeTurckRemainderH2 (g₀ g_bg : SmoothRiemannianMetric I M) :
    zeroStateDeTurckRemainderH2 (I := I) (M := M) g₀ g_bg =
      staticForce (I := I) (M := M) g₀ g_bg (2 : ℝ) := by
  refine Eq.trans (congrArg (ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ))
    (deTurckRem_zero (I := I) (M := M) g₀ g_bg _ _)) ?_
  exact tensorHs.ext (funext fun _ => rfl)

theorem lowerScaleForce_eq_static (g : SmoothRiemannianMetric I M) :
    lowerScaleForce (I := I) (M := M) g =
      staticForce (I := I) (M := M) g g (1 : ℝ) := by
  refine Eq.trans (congrArg
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (by norm_num : (1 : ℝ) ≤ (2 : ℝ)))
    (staticForcing_eq_zeroStateDeTurckRemainderH2 (I := I) (M := M) g g)) ?_
  exact staticForce_incl (I := I) (M := M) g g _

theorem deTurckRemainderOnLowerState_zero_eq_staticForce (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg hδ hreal)) :
    deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal
        ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩ =
      staticForce (I := I) (M := M) g₀ g_bg ((1 : ℕ) : ℝ) :=
  deTurckRemainderOnLowerState_zero_eq_deTurckRHS (I := I) (M := M) g₀ g_bg hR hδ hreal hcore

theorem deTurckRemainderOnLowerState_zero_h1_eq_staticForce (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg hδ hreal)) :
    tensorHsCongr (I := I) (M := M) g₀ 0 2
        (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
        (deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal
          ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩) =
      staticForce (I := I) (M := M) g₀ g_bg (1 : ℝ) := by
  refine Eq.trans (congrArg
    (fun v => tensorHsCongr (I := I) (M := M) g₀ 0 2
      (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num) v)
    (deTurckRemainderOnLowerState_zero_eq_staticForce (I := I) (M := M) g₀ g_bg hR hδ hreal hcore)) ?_
  exact staticForce_congr (I := I) (M := M) g₀ g_bg _

def liftForceHi (g₀ g_bg : SmoothRiemannianMetric I M) (T : ℝ) :
    timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (2 : ℝ)) T :=
  timeConstL2 T (staticForce (I := I) (M := M) g₀ g_bg (2 : ℝ))

def liftForceLo (g₀ g_bg : SmoothRiemannianMetric I M) (T : ℝ) :
    timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (1 : ℝ)) T :=
  timeConstL2 T (staticForce (I := I) (M := M) g₀ g_bg (1 : ℝ))

theorem timeConst_static_incl (g₀ g_bg : SmoothRiemannianMetric I M) {τ σ : ℝ}
    (hτσ : τ ≤ σ) (T : ℝ) :
    timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hτσ
        (timeConstL2 T (staticForce (I := I) (M := M) g₀ g_bg σ)) =
      timeConstL2 T (staticForce (I := I) (M := M) g₀ g_bg τ) := by
  rw [timeL2Inclusion_const, staticForce_incl]

theorem lift_force_incl (g₀ g_bg : SmoothRiemannianMetric I M) (T : ℝ) :
    timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (by norm_num : (1 : ℝ) ≤ (2 : ℝ))
        (liftForceHi (I := I) (M := M) g₀ g_bg T) =
      liftForceLo (I := I) (M := M) g₀ g_bg T :=
  timeConst_static_incl (I := I) (M := M) g₀ g_bg _ T

theorem norm_liftForceHi_le (g₀ g_bg : SmoothRiemannianMetric I M) (T : ℝ)
    {D : ℝ} (hD : ‖staticForce (I := I) (M := M) g₀ g_bg (2 : ℝ)‖ ≤ D) :
    ‖liftForceHi (I := I) (M := M) g₀ g_bg T‖ ≤ D * Real.sqrt T :=
  (norm_timeConstL2_le T _).trans
    (mul_le_mul_of_nonneg_right hD (Real.sqrt_nonneg T))

theorem norm_liftForceLo_le (g₀ g_bg : SmoothRiemannianMetric I M) (T : ℝ)
    {D : ℝ} (hD : ‖staticForce (I := I) (M := M) g₀ g_bg (1 : ℝ)‖ ≤ D) :
    ‖liftForceLo (I := I) (M := M) g₀ g_bg T‖ ≤ D * Real.sqrt T :=
  (norm_timeConstL2_le T _).trans
    (mul_le_mul_of_nonneg_right hD (Real.sqrt_nonneg T))

theorem liftForceLo_lowerScale (g : SmoothRiemannianMetric I M) (T : ℝ) :
    liftForceLo (I := I) (M := M) g g T =
      timeConstL2 T (lowerScaleForce (I := I) (M := M) g) := by
  rw [liftForceLo, lowerScaleForce_eq_static]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
