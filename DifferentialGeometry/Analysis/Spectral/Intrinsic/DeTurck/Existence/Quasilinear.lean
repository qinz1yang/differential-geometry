import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearity.Basic
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Nemytskii.SubcriticalSmallTime
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Interpolation.TimeL2Limit
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.TimeSupremumTrace
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.Estimates
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.MixedNorm
open DifferentialGeometry.Geometry.Curvature


noncomputable section

open Bundle MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g₀ g_bg : SmoothRiemannianMetric I M}

def deTurckLipConst (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) : ℝ≥0 :=
  (deTurckSobolevNHa2_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super).choose

theorem deTurckSobolevNHa2_lipschitzWith_lipConst (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    LipschitzWith (deTurckLipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg) a ha_super)
      (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a) :=
  (deTurckSobolevNHa2_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super).choose_spec

def deTurckTimeNemytskii (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} :
    timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) T →
      timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T :=
  nemytskii (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
    (a := (a : ℝ)) (T := T)
    (deTurckSobolevNHa2_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
      a ha_super)

def deTurckLipConstSymm (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) : ℝ≥0 :=
  (deTurckSobolevNHa2Symm_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super).choose

theorem deTurckSobolevNHa2Symm_lipschitzWith_lipConst (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    LipschitzWith (deTurckLipConstSymm (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg) a ha_super)
      (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a) :=
  (deTurckSobolevNHa2Symm_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super).choose_spec

theorem deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ C₁ C₂ : ℝ≥0, ∀ (u u' : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)),
      ‖deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a u -
          deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a u'‖ ≤
        (C₁ : ℝ) * max ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u‖
                       ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u'‖
          * ‖u - u'‖ +
        (C₂ : ℝ) * ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                      (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u - u')‖ :=
  deTurckSobolevNonlinearitySymm_mixed_lipschitz_pointwise (I := I) (M := M) g₀ g_bg a ha_super

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem nemytskii_time_mixed_bound (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {L : ℝ≥0}
    {Nfun : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) →
      TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)}
    (hLip : LipschitzWith L Nfun) {C₁ C₂ : ℝ≥0}
    (hsingle : ∀ (u u' : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)),
      ‖Nfun u - Nfun u'‖ ≤
        (C₁ : ℝ) * max ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u‖
                       ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u'‖
          * ‖u - u'‖ +
        (C₂ : ℝ) * ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                      (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u - u')‖)
    {T : ℝ} (R : ℝ) (hR : 0 ≤ R)
    (f f' : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) T)
    (hfR : ∀ᵐ t ∂(timeMeasure T),
      ‖(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) f) t‖ ≤ R)
    (hf'R : ∀ᵐ t ∂(timeMeasure T),
      ‖(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) f') t‖ ≤ R) :
    ‖nemytskii (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (a := (a : ℝ)) (T := T) hLip f -
      nemytskii (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (a := (a : ℝ)) (T := T) hLip f'‖ ≤
      (C₁ : ℝ) * R * ‖f - f'‖ +
        (C₂ : ℝ) *
          ‖timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f - f')‖ := by
  have hNf := nemytskii_coeFn (I := I) (M := M) hLip f
  have hNf' := nemytskii_coeFn (I := I) (M := M) hLip f'
  have hsub := Lp.coeFn_sub
    (nemytskii (I := I) (M := M) hLip f) (nemytskii (I := I) (M := M) hLip f')
  have hsubff' := Lp.coeFn_sub f f'
  have hinclf :
      ⇑(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) f) =ᵐ[timeMeasure T]
        fun t => tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f t) :=
    (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith)).coeFn_compLpL
      (p := 2) (μ := timeMeasure T) f
  have hinclf' :
      ⇑(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) f') =ᵐ[timeMeasure T]
        fun t => tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f' t) :=
    (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith)).coeFn_compLpL
      (p := 2) (μ := timeMeasure T) f'
  have hincldiff :
      ⇑(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f - f')) =ᵐ[timeMeasure T]
        fun t => tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) ((f - f') t) :=
    (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith)).coeFn_compLpL
      (p := 2) (μ := timeMeasure T) (f - f')
  have hbound : ∀ᵐ t ∂(timeMeasure T),
      ‖(nemytskii (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (a := (a : ℝ)) (T := T) hLip f -
        nemytskii (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (a := (a : ℝ)) (T := T) hLip f') t‖ ≤
        (C₁ : ℝ) * R * ‖(f - f') t‖ +
          (C₂ : ℝ) *
            ‖(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f - f')) t‖ := by
    filter_upwards [hsub, hNf, hNf', hsubff', hfR, hf'R, hinclf, hinclf', hincldiff]
      with t ht htf htf' htsubff' htfR htf'R htinclf htinclf' htincldiff
    rw [ht, Pi.sub_apply, htf, htf']
    have hsg := hsingle (f t) (f' t)
    have hmax_le :
        max ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                  (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f t)‖
               ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                  (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f' t)‖ ≤ R := by
      refine max_le ?_ ?_
      · rw [← htinclf]; exact htfR
      · rw [← htinclf']; exact htf'R
    have hstep1 :
        (C₁ : ℝ) * max ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f t)‖
                       ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f' t)‖
            * ‖(f t) - (f' t)‖ ≤ (C₁ : ℝ) * R * ‖(f t) - (f' t)‖ := by
      have hnn : (0 : ℝ) ≤ ‖(f t) - (f' t)‖ := norm_nonneg _
      have hmul : (C₁ : ℝ) * max _ _ ≤ (C₁ : ℝ) * R :=
        mul_le_mul_of_nonneg_left hmax_le C₁.coe_nonneg
      exact mul_le_mul_of_nonneg_right hmul hnn
    have hff'eq : ‖(f t) - (f' t)‖ = ‖(f - f') t‖ := by
      rw [htsubff', Pi.sub_apply]
    have hstep2 :
        (C₂ : ℝ) * ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                      (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) ((f t) - (f' t))‖
          = (C₂ : ℝ) * ‖(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f - f')) t‖ := by
      rw [htincldiff, htsubff', Pi.sub_apply]
    calc ‖Nfun (f t) - Nfun (f' t)‖
        ≤ (C₁ : ℝ) * max ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                            (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f t)‖
                         ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                            (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f' t)‖
            * ‖(f t) - (f' t)‖ +
          (C₂ : ℝ) * ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                        (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) ((f t) - (f' t))‖ := hsg
      _ ≤ (C₁ : ℝ) * R * ‖(f - f') t‖ +
            (C₂ : ℝ) * ‖(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f - f')) t‖ := by
          refine add_le_add ?_ (le_of_eq hstep2)
          rw [← hff'eq]
          exact hstep1
  exact timeL2_norm_le_of_ae_mixed_bound (T := T)
    (nemytskii (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (a := (a : ℝ)) (T := T) hLip f -
      nemytskii (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (a := (a : ℝ)) (T := T) hLip f')
    (f - f')
    (timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f - f'))
    (mul_nonneg C₁.coe_nonneg hR) C₂.coe_nonneg hbound

def nemytskiiMixedForcingMap (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {L : ℝ≥0}
    {Nfun : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) →
      TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)}
    (hLip : LipschitzWith L Nfun)
    {T : ℝ} (hT : 0 < T) :
    timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T →
      timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T :=
  fun F => nemytskii (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
    (a := (a : ℝ)) (T := T) hLip
    (maximalRegularityDuhamelSolutionField (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (T := T) (a : ℝ) hT
      (0 : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) F)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem nemytskiiMixedForcingMap_apply (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {L : ℝ≥0}
    {Nfun : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) →
      TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)}
    (hLip : LipschitzWith L Nfun)
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T) :
    nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT F =
      nemytskii (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (a := (a : ℝ)) (T := T) hLip
        (maximalRegularityDuhamelSolutionField (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (T := T) (a : ℝ) hT
          (0 : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) F) :=
  rfl

omit [BoundarylessManifold I M] in
theorem nemytskiiMixedForcingMap_dist_le (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {L : ℝ≥0}
    {Nfun : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) →
      TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)}
    (hLip : LipschitzWith L Nfun) {C₁ C₂ : ℝ≥0}
    (hsingle : ∀ (u u' : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)),
      ‖Nfun u - Nfun u'‖ ≤
        (C₁ : ℝ) * max ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u‖
                       ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u'‖
          * ‖u - u'‖ +
        (C₂ : ℝ) * ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                      (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u - u')‖)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (F F' : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hF : ‖F‖ ≤ ρ) (hF' : ‖F'‖ ≤ ρ) :
    ‖nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT F -
        nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT F'‖ ≤
      ((C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) + (C₂ : ℝ) * (2 * Real.sqrt T)) * ‖F - F'‖ := by
  classical
  have h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  set z : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) := 0 with hz
  set fF := maximalRegularityDuhamelSolutionField (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
    (T := T) (a : ℝ) hT z F with hfF
  set fF' := maximalRegularityDuhamelSolutionField (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
    (T := T) (a : ℝ) hT z F' with hfF'
  set R := Real.sqrt (1 + T) * ρ with hR
  have hT_pos : (0 : ℝ) < 1 + T := by linarith
  have hsqrtnn : 0 ≤ Real.sqrt (1 + T) := Real.sqrt_nonneg _
  have hRnn : 0 ≤ R := mul_nonneg hsqrtnn hρ
  have hfR : ∀ᵐ t ∂(timeMeasure T),
      ‖(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) fF) t‖ ≤ R := by
    filter_upwards [maximalRegularityDuhamelSolutionField_inclusion_Ha1_ae_pointwise_le
      (I := I) (M := M) (g₀ := g₀) hT F] with t ht
    refine le_trans ht ?_
    rw [hR]
    exact mul_le_mul_of_nonneg_left hF hsqrtnn
  have hf'R : ∀ᵐ t ∂(timeMeasure T),
      ‖(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) fF') t‖ ≤ R := by
    filter_upwards [maximalRegularityDuhamelSolutionField_inclusion_Ha1_ae_pointwise_le
      (I := I) (M := M) (g₀ := g₀) hT F'] with t ht
    refine le_trans ht ?_
    rw [hR]
    exact mul_le_mul_of_nonneg_left hF' hsqrtnn
  have hfield_dist : ‖fF - fF'‖ ≤ (1 + T) * ‖F - F'‖ :=
    maximalRegularityDuhamelSolutionField_dist_le (I := I) (M := M) (h_compact := h_compact) (a := (a : ℝ))
      hT z F F'
  have hincl_dist :
      ‖timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (fF - fF')‖ ≤
        2 * Real.sqrt T * ‖F - F'‖ := by
    rw [map_sub, timeL2Inclusion_maximalRegularityDuhamelSolutionField (I := I) (M := M) hT hT1 z F,
      timeL2Inclusion_maximalRegularityDuhamelSolutionField (I := I) (M := M) hT hT1 z F']
    exact maximalRegularityDuhamelSolutionFieldHa1_dist_le (I := I) (M := M) (h_compact := h_compact)
      (a := (a : ℝ)) hT hT1 z F F'
  have hmain := nemytskii_time_mixed_bound (I := I) (M := M) g₀ a hLip hsingle R hRnn fF fF'
    hfR hf'R
  calc ‖nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT F -
          nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT F'‖
      = ‖nemytskii (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (a := (a : ℝ)) (T := T) hLip fF -
          nemytskii (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (a := (a : ℝ)) (T := T) hLip fF'‖ := by
        rw [nemytskiiMixedForcingMap_apply, nemytskiiMixedForcingMap_apply]
    _ ≤ (C₁ : ℝ) * R * ‖fF - fF'‖ +
          (C₂ : ℝ) * ‖timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (fF - fF')‖ := hmain
    _ ≤ (C₁ : ℝ) * R * ((1 + T) * ‖F - F'‖) +
          (C₂ : ℝ) * (2 * Real.sqrt T * ‖F - F'‖) := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left hfield_dist (mul_nonneg C₁.coe_nonneg hRnn)
        · exact mul_le_mul_of_nonneg_left hincl_dist C₂.coe_nonneg
    _ = ((C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) + (C₂ : ℝ) * (2 * Real.sqrt T)) * ‖F -
      F'‖ := by
        rw [hR]; ring

omit [BoundarylessManifold I M] in
private theorem norm_nemytskiiMixedForcingMap_zero_le (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    {L : ℝ≥0}
    {Nfun : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) →
      TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)}
    (hLip : LipschitzWith L Nfun)
    {T : ℝ} (hT : 0 < T) :
    ‖nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT
        (0 : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)‖ ≤
      Real.sqrt T * ‖Nfun (0 : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ := by
  rw [nemytskiiMixedForcingMap_apply,
    maximalRegularityDuhamelSolutionField_zero_zero (I := I) (M := M) (g₀ := g₀) hT]
  refine timeL2_norm_le_of_ae_bound _ (norm_nonneg _) ?_
  have hcoe := nemytskii_coeFn (I := I) (M := M) hLip
    (0 : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) T)
  have hzero := Lp.coeFn_zero (E := TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
    (p := 2) (μ := timeMeasure T)
  filter_upwards [hcoe, hzero] with t ht htz
  rw [ht, htz, Pi.zero_apply]

def deTurckForceBallRadiusSymm (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) : ℝ :=
  1 / (16 * (((deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M)
    (g₀ := g₀) (g_bg := g_bg) a ha_super).choose : ℝ) + 1))

omit [BoundarylessManifold I M] in
theorem nemytskii_solution_const
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {L : ℝ≥0}
    (Nfun : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) →
      TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (hLip : LipschitzWith L Nfun)
    (C₁ C₂ : ℝ≥0) (D : ℝ) (hD : 0 ≤ D)
    (hzero : ‖Nfun (0 : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ ≤ D)
    (hsingle : ∀ (u u' : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)),
      ‖Nfun u - Nfun u'‖ ≤
        (C₁ : ℝ) * max ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u‖
                       ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u'‖
          * ‖u - u'‖ +
        (C₂ : ℝ) * ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                      (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u - u')‖) :
    ∃ T₀ : ℝ,
      T₀ = min 1 (min (1 / (64 * ((C₂ : ℝ) + 1) ^ 2))
        ((1 / (16 * ((C₁ : ℝ) + 1)) / (2 * (D + 1))) ^ 2)) ∧
      0 < T₀ ∧ ∀ {T : ℝ} (hT : 0 < T) (_hTT₀ : T ≤ T₀) (_hT1 : T ≤ 1),
      ∃ (u : MaximalRegularitySolutionSpace (I := I) (M := M) (a : ℝ) T)
        (gforce : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T),
        u = maximalRegularityDuhamelMap (I := I) (M := M) (a : ℝ) hT
            (0 : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce ∧
          gforce =ᵐ[timeMeasure T]
            (fun t => Nfun (maximalRegularityDuhamelSolutionField (I := I) (M := M)
                (g := g₀) (r := 0) (s := 2) (T := T) (a : ℝ) hT
                (0 : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)) ∧
          timeH1.trace0 _ T u = 0 ∧
          timeH1.timeDeriv _ T u =
            timeScaleLaplacian (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (T := T) (a : ℝ)
                (maximalRegularityDuhamelSolutionField (I := I) (M := M)
                  (g := g₀) (r := 0) (s := 2) (T := T) (a : ℝ) hT
                  (0 : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce) + gforce ∧
          ‖gforce‖ ≤ 1 / (16 * ((C₁ : ℝ) + 1)) := by
  classical
  have h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  set M₀ := ‖Nfun (0 : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ with hM₀def
  have hM₀ : 0 ≤ M₀ := norm_nonneg _
  have hM₀D : M₀ ≤ D := by simpa only [hM₀def] using hzero
  have hD1pos : 0 < D + 1 := by linarith
  set ρ : ℝ := 1 / (16 * ((C₁ : ℝ) + 1)) with hρdef
  have hC₁p : (0 : ℝ) < 16 * ((C₁ : ℝ) + 1) := by positivity
  have hρpos : 0 < ρ := by rw [hρdef]; positivity
  set T₀ : ℝ := min 1 (min (1 / (64 * ((C₂ : ℝ) + 1) ^ 2))
    ((ρ / (2 * (D + 1))) ^ 2)) with hT₀def
  have hT₀pos : 0 < T₀ := by
    refine lt_min one_pos (lt_min ?_ ?_)
    · positivity
    · have : 0 < ρ / (2 * (D + 1)) := by positivity
      positivity
  refine ⟨T₀, ?_, hT₀pos, ?_⟩
  · rw [hT₀def, hρdef]
  intro T hT hTT₀ hT1
  have hT_le1 : T ≤ 1 := hT1
  have hT_lo : T ≤ 1 / (64 * ((C₂ : ℝ) + 1) ^ 2) :=
    le_trans hTT₀ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hT_stay : T ≤ (ρ / (2 * (D + 1))) ^ 2 :=
    le_trans hTT₀ (le_trans (min_le_right _ _) (min_le_right _ _))
  set Λ : ℝ := (C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) + (C₂ : ℝ) * (2 * Real.sqrt T) with
    hΛdef
  have hΛnn : 0 ≤ Λ := by
    rw [hΛdef]; have : (0:ℝ) ≤ 1 + T := by linarith
    positivity
  have h1T : (1 : ℝ) + T ≤ 2 := by linarith
  have hsqrt1T_le : Real.sqrt (1 + T) ≤ 1 + T := by
    have h1le : (1 : ℝ) ≤ 1 + T := by linarith
    calc Real.sqrt (1 + T) ≤ Real.sqrt ((1 + T) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (1 + T)])
      _ = 1 + T := Real.sqrt_sq (by linarith)
  have harm1 : (C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) ≤ 1 / 4 := by
    have hle : (C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) ≤ (C₁ : ℝ) * 2 * ρ * 2 := by
      have hc1 : (0:ℝ) ≤ (C₁:ℝ) := C₁.coe_nonneg
      have h0 : (0:ℝ) ≤ 1 + T := by linarith
      have hsqrt2 : Real.sqrt (1 + T) ≤ 2 := le_trans hsqrt1T_le h1T
      gcongr
    refine le_trans hle ?_
    rw [hρdef]
    rw [show (C₁ : ℝ) * 2 * (1 / (16 * ((C₁ : ℝ) + 1))) * 2 =
        (C₁ : ℝ) / ((C₁ : ℝ) + 1) * (4 / 16) by field_simp; ring]
    have hfrac : (C₁ : ℝ) / ((C₁ : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [C₁.coe_nonneg]
    nlinarith [hfrac, div_nonneg C₁.coe_nonneg (by positivity : (0:ℝ) ≤ (C₁:ℝ)+1)]
  have hsqrtT : Real.sqrt T ≤ 1 / (8 * ((C₂ : ℝ) + 1)) := by
    rw [show (1 : ℝ) / (8 * ((C₂ : ℝ) + 1)) =
        Real.sqrt ((1 / (8 * ((C₂ : ℝ) + 1))) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    refine Real.sqrt_le_sqrt (le_trans hT_lo ?_)
    rw [div_pow, one_pow, mul_pow]; norm_num
  have harm2 : (C₂ : ℝ) * (2 * Real.sqrt T) ≤ 1 / 4 := by
    have hc2 : (0:ℝ) ≤ (C₂:ℝ) := C₂.coe_nonneg
    calc (C₂ : ℝ) * (2 * Real.sqrt T)
        = 2 * (C₂ : ℝ) * Real.sqrt T := by ring
      _ ≤ 2 * (C₂ : ℝ) * (1 / (8 * ((C₂ : ℝ) + 1))) := by
          apply mul_le_mul_of_nonneg_left hsqrtT (by positivity)
      _ = (C₂ : ℝ) / ((C₂ : ℝ) + 1) * (1 / 4) := by
          have hne : ((C₂ : ℝ) + 1) ≠ 0 := by positivity
          field_simp
          ring
      _ ≤ 1 / 4 := by
          have hfrac : (C₂ : ℝ) / ((C₂ : ℝ) + 1) ≤ 1 := by
            rw [div_le_one (by positivity)]; linarith
          nlinarith [hfrac, div_nonneg hc2 (by positivity : (0:ℝ) ≤ (C₂:ℝ)+1)]
  have hΛ_le : Λ ≤ 1 / 2 := by rw [hΛdef]; linarith
  have hΛ_lt : Λ < 1 := by linarith
  set Ψ := nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT
    with hΨdef
  set z₀ : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T := 0 with hz₀
  set ρt := recenteredBallRetraction (z₀) ρ with hρtdef
  set Ψ' : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T →
      timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T := fun F => Ψ (ρt F) with hΨ'def
  have hΨ_ball : ∀ (F F' : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T),
      ‖F‖ ≤ ρ → ‖F'‖ ≤ ρ → ‖Ψ F - Ψ F'‖ ≤ Λ * ‖F - F'‖ := by
    intro F F' hF hF'
    have h := nemytskiiMixedForcingMap_dist_le (I := I) (M := M) g₀ a hLip hsingle
      hT hT1 hρpos.le F F' hF hF'
    rw [hΛdef]
    exact h
  have hρt_mem : ∀ F, ρt F ∈ Metric.closedBall z₀ ρ := fun F =>
    recenteredBallRetraction_mapsTo (X := _) hρpos.le z₀ (Set.mem_univ F)
  have hρt_norm : ∀ F, ‖ρt F‖ ≤ ρ := by
    intro F
    have := hρt_mem F
    rw [Metric.mem_closedBall, hz₀, dist_zero_right] at this
    exact this
  have hρt_lip : LipschitzWith 1 ρt :=
    recenteredBallRetraction_lipschitzWith_one hρpos.le z₀
  have hΨ'_lip : ∀ (F F' : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T),
      ‖Ψ' F - Ψ' F'‖ ≤ Λ * ‖F - F'‖ := by
    intro F F'
    have hbase := hΨ_ball (ρt F) (ρt F') (hρt_norm F) (hρt_norm F')
    refine le_trans hbase ?_
    have hretr : ‖ρt F - ρt F'‖ ≤ ‖F - F'‖ := by
      have := hρt_lip.dist_le_mul F F'
      rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at this
      exact this
    exact mul_le_mul_of_nonneg_left hretr hΛnn
  have hcontr : ContractingWith Λ.toNNReal Ψ' := by
    refine ⟨?_, ?_⟩
    · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hΛnn]
      simpa using hΛ_lt
    · refine LipschitzWith.of_dist_le_mul (fun F F' => ?_)
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hΛnn]
      exact hΨ'_lip F F'
  set Fstar := ContractingWith.fixedPoint Ψ' hcontr with hFstar_def
  have hFstar_fix : Ψ' Fstar = Fstar := ContractingWith.fixedPoint_isFixedPt hcontr
  have hΨ0 : ‖Ψ z₀‖ ≤ Real.sqrt T * M₀ := by
    rw [hΨdef, hz₀, hM₀def]
    exact norm_nemytskiiMixedForcingMap_zero_le (I := I) (M := M) g₀ a hLip hT
  have hsqrtTM : Real.sqrt T * M₀ ≤ ρ / 2 := by
    have hsqrtT_le : Real.sqrt T ≤ ρ / (2 * (D + 1)) := by
      rw [show ρ / (2 * (D + 1)) = Real.sqrt ((ρ / (2 * (D + 1))) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt hT_stay
    calc Real.sqrt T * M₀ ≤ (ρ / (2 * (D + 1))) * M₀ :=
          mul_le_mul_of_nonneg_right hsqrtT_le hM₀
      _ ≤ (ρ / (2 * (D + 1))) * (D + 1) := by
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ρ / 2 := by
          have hne : (D + 1) ≠ 0 := ne_of_gt hD1pos
          field_simp
  have hz₀norm : ‖z₀‖ = 0 := by rw [hz₀, norm_zero]
  have hΨ_stay : ∀ G, ‖G‖ ≤ ρ → ‖Ψ G‖ ≤ ρ := by
    intro G hG
    have hball := hΨ_ball G z₀ hG (by rw [hz₀norm]; exact hρpos.le)
    have hGz : ‖G - z₀‖ = ‖G‖ := by rw [hz₀, sub_zero]
    rw [hGz] at hball
    calc ‖Ψ G‖ = ‖(Ψ G - Ψ z₀) + Ψ z₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖Ψ G - Ψ z₀‖ + ‖Ψ z₀‖ := norm_add_le _ _
      _ ≤ Λ * ‖G‖ + Real.sqrt T * M₀ := add_le_add hball hΨ0
      _ ≤ (1 / 2) * ρ + ρ / 2 := by
          refine add_le_add ?_ hsqrtTM
          calc Λ * ‖G‖ ≤ Λ * ρ := mul_le_mul_of_nonneg_left hG hΛnn
            _ ≤ (1 / 2) * ρ := mul_le_mul_of_nonneg_right hΛ_le hρpos.le
      _ = ρ := by ring
  have hFstar_mem : ‖Fstar‖ ≤ ρ := by
    have heq : Fstar = Ψ (ρt Fstar) := hFstar_fix.symm
    rw [heq]
    exact hΨ_stay (ρt Fstar) (hρt_norm Fstar)
  have hρt_Fstar : ρt Fstar = Fstar :=
    recenteredBallRetraction_eq_self_of_mem (by
      rw [Metric.mem_closedBall, hz₀, dist_zero_right]; exact hFstar_mem)
  have hΨFstar : Ψ Fstar = Fstar := by
    have hstep : Ψ' Fstar = Ψ Fstar := by simp only [hΨ'def, hρt_Fstar]
    rw [← hstep]; exact hFstar_fix
  set field := maximalRegularityDuhamelSolutionField (I := I) (M := M) (a : ℝ) hT
    (0 : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) Fstar with hfielddef
  have hforce_eq : Fstar = nemytskii (I := I) (M := M) hLip field := by
    rw [← hΨFstar, hΨdef, nemytskiiMixedForcingMap_apply]
  refine ⟨maximalRegularityDuhamelMap (I := I) (M := M) (a : ℝ) hT
      (0 : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) Fstar, Fstar, rfl, ?_, ?_, ?_, ?_⟩
  · have hcoe := nemytskii_coeFn (I := I) (M := M) hLip field
    have hforce_ae : ⇑Fstar =ᵐ[timeMeasure T]
        ⇑(nemytskii (I := I) (M := M) hLip field) := by
      rw [hforce_eq]
    refine hforce_ae.trans ?_
    exact hcoe
  · rw [maximalRegularityDuhamelMap_trace0 (I := I) (M := M) (a := (a : ℝ)) (T := T) hT
      (0 : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) Fstar, map_zero]
  · rw [maximalRegularityDuhamelMap_timeDeriv_eq (I := I) (M := M) (h_compact := h_compact)
      (a := (a : ℝ)) (T := T) hT (0 : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) Fstar]
  · exact hFstar_mem

omit [BoundarylessManifold I M] in
theorem quasilinear_maxreg_solution_of_nemytskii
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {L : ℝ≥0}
    (Nfun : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) →
      TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (hLip : LipschitzWith L Nfun)
    (hmix : ∃ C₁ C₂ : ℝ≥0, ∀ (u u' : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)),
      ‖Nfun u - Nfun u'‖ ≤
        (C₁ : ℝ) * max ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u‖
                       ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u'‖
          * ‖u - u'‖ +
        (C₂ : ℝ) * ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                      (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u - u')‖) :
    ∃ T₀ : ℝ,
      T₀ = min 1 (min (1 / (64 * ((hmix.choose_spec.choose : ℝ) + 1) ^ 2))
        ((1 / (16 * ((hmix.choose : ℝ) + 1)) /
            (2 * (‖Nfun (0 : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ + 1))) ^ 2)) ∧
      0 < T₀ ∧ ∀ {T : ℝ} (hT : 0 < T) (_hTT₀ : T ≤ T₀) (_hT1 : T ≤ 1),
      ∃ (u : MaximalRegularitySolutionSpace (I := I) (M := M) (a : ℝ) T)
        (gforce : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T),
        u = maximalRegularityDuhamelMap (I := I) (M := M) (a : ℝ) hT
            (0 : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce ∧
          gforce =ᵐ[timeMeasure T]
            (fun t => Nfun (maximalRegularityDuhamelSolutionField (I := I) (M := M)
                (g := g₀) (r := 0) (s := 2) (T := T) (a : ℝ) hT
                (0 : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)) ∧
          timeH1.trace0 _ T u = 0 ∧
          timeH1.timeDeriv _ T u =
            timeScaleLaplacian (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (T := T) (a : ℝ)
                (maximalRegularityDuhamelSolutionField (I := I) (M := M)
                  (g := g₀) (r := 0) (s := 2) (T := T) (a : ℝ) hT
                  (0 : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce) + gforce ∧
          ‖gforce‖ ≤ 1 / (16 * ((hmix.choose : ℝ) + 1)) := by
  exact nemytskii_solution_const (I := I) (M := M) g₀ a Nfun hLip
    hmix.choose hmix.choose_spec.choose
    ‖Nfun (0 : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖
    (norm_nonneg _) le_rfl hmix.choose_spec.choose_spec

end DifferentialGeometry.Analysis.Spectral

end
