import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.LocalNemytskii
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.DenseLowerState
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckQuasilinearExistence

/-!
# A forcing fixed point for a lower-Sobolev state set

The critical Ricci--DeTurck estimate is available only while the unknown is
small in the uniformly-in-time lower Sobolev norm.  Maximal regularity gives
that lower-norm control almost everywhere, but only an `L²` bound at the top
Sobolev order.  This file adapts the existing mixed forcing-space contraction
to a nonlinearity defined on precisely that lower-norm state set.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- The top-order tensors whose order-`a+1` view has norm at most `R`. -/
def lowerState (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (R : ℝ) :
    Set (tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) :=
  lowerBall (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
    (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith)) R

theorem zero_mem_lowerState (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    {R : ℝ} (hR : 0 ≤ R) :
    (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) ∈
      lowerState (I := I) (M := M) g₀ a R := by
  change
    ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith)
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ ≤ R
  simpa only [map_zero, norm_zero] using hR

/-- A Duhamel field driven by a forcing-space ball stays almost everywhere
in a prescribed lower-order state ball. -/
theorem field_mem_lower
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {T ρ R : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1) (hρR : 2 * ρ ≤ R)
    (F : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hF : ‖F‖ ≤ ρ) :
    ∀ᵐ t ∂(timeMeasure T),
      maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) F t ∈
        lowerState (I := I) (M := M) g₀ a R := by
  let field := maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
    (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) F
  have hincl :
      ⇑(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) field)
        =ᵐ[timeMeasure T]
          fun t => tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (field t) :=
    (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith)).coeFn_compLpL
      (p := 2) (μ := timeMeasure T) field
  have hpoint := maxRegDuhamelSolField_inclusion_Ha1_ae_pointwise_le
    (I := I) (M := M) (g₀ := g₀) hT hT1 F
  have hsqrt : Real.sqrt (1 + T) ≤ 2 := by
    have hsq : Real.sqrt (1 + T) ≤ 1 + T := by
      calc
        Real.sqrt (1 + T) ≤ Real.sqrt ((1 + T) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (1 + T)])
        _ = 1 + T := Real.sqrt_sq (by linarith)
    linarith
  filter_upwards [hincl, hpoint] with t htincl ht
  change ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (field t)‖ ≤ R
  calc
    ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (field t)‖ =
        ‖(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) field) t‖ := by rw [htincl]
    _ ≤ Real.sqrt (1 + T) * ‖F‖ := ht
    _ ≤ 2 * ρ := mul_le_mul hsqrt hF (norm_nonneg F) (by positivity)
    _ ≤ R := hρR

/-- The mixed pointwise estimate on a lower-norm state set integrates to the
same mixed time-`L²` estimate. -/
theorem nemytskiiOn_mixed
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (hR : 0 ≤ R)
    {L : ℝ≥0}
    {Nfun : lowerState (I := I) (M := M) g₀ a R →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)}
    (hLip : LipschitzWith L Nfun) {C₁ C₂ : ℝ≥0}
    (hsingle : ∀ u u' : lowerState (I := I) (M := M) g₀ a R,
      ‖Nfun u - Nfun u'‖ ≤
        (C₁ : ℝ) *
            max ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                    (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u : _)‖
                ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                    (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u' : _)‖ *
              ‖(u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) - (u' : _)‖ +
          (C₂ : ℝ) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) ((u : _) - (u' : _))‖)
    {T : ℝ}
    (f f' : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) T)
    (hf : ∀ᵐ t ∂(timeMeasure T), f t ∈ lowerState (I := I) (M := M) g₀ a R)
    (hf' : ∀ᵐ t ∂(timeMeasure T), f' t ∈ lowerState (I := I) (M := M) g₀ a R) :
    ‖nemytskiiOn (zero_mem_lowerState (I := I) (M := M) g₀ a hR) hLip f hf -
        nemytskiiOn (zero_mem_lowerState (I := I) (M := M) g₀ a hR) hLip f' hf'‖ ≤
      (C₁ : ℝ) * R * ‖f - f'‖ +
        (C₂ : ℝ) *
          ‖timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f - f')‖ := by
  let hz := zero_mem_lowerState (I := I) (M := M) g₀ a hR
  have hNf := nemytskiiOn_coeFn hz hLip f hf
  have hNf' := nemytskiiOn_coeFn hz hLip f' hf'
  have hsub := Lp.coeFn_sub (nemytskiiOn hz hLip f hf) (nemytskiiOn hz hLip f' hf')
  have hsubff' := Lp.coeFn_sub f f'
  have hincldiff :
      ⇑(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f - f'))
        =ᵐ[timeMeasure T]
          fun t => tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) ((f - f') t) :=
    (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith)).coeFn_compLpL
      (p := 2) (μ := timeMeasure T) (f - f')
  have hbound : ∀ᵐ t ∂(timeMeasure T),
      ‖(nemytskiiOn hz hLip f hf - nemytskiiOn hz hLip f' hf') t‖ ≤
        (C₁ : ℝ) * R * ‖(f - f') t‖ +
          (C₂ : ℝ) *
            ‖(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f - f')) t‖ := by
    filter_upwards [hsub, hNf, hNf', hsubff', hf, hf', hincldiff]
      with t ht htf htf' htdiff hft hft' htincl
    rw [ht, Pi.sub_apply, htf, htf']
    simp only [aeSetLift, dif_pos hft, dif_pos hft']
    let u : lowerState (I := I) (M := M) g₀ a R := ⟨f t, hft⟩
    let u' : lowerState (I := I) (M := M) g₀ a R := ⟨f' t, hft'⟩
    have hsg := hsingle u u'
    have huR :
        ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f t)‖ ≤ R := by
      simpa only [lowerState, lowerBall] using hft
    have hu'R :
        ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f' t)‖ ≤ R := by
      simpa only [lowerState, lowerBall] using hft'
    have hmax : max
        ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f t)‖
        ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f' t)‖ ≤ R :=
      max_le huR hu'R
    have htop :
        (C₁ : ℝ) * max
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f t)‖
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f' t)‖ *
              ‖f t - f' t‖ ≤
          (C₁ : ℝ) * R * ‖(f - f') t‖ := by
      rw [htdiff, Pi.sub_apply]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmax C₁.coe_nonneg) (norm_nonneg _)
    have hlow :
        (C₂ : ℝ) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f t - f' t)‖ =
          (C₂ : ℝ) *
            ‖(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f - f')) t‖ := by
      rw [htincl, htdiff, Pi.sub_apply]
    have hsum := hsg.trans (add_le_add htop hlow.le)
    simpa only [u, u'] using hsum
  exact timeL2_norm_le_of_ae_mixed_bound
    (nemytskiiOn hz hLip f hf - nemytskiiOn hz hLip f' hf') (f - f')
    (timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f - f'))
    (mul_nonneg C₁.coe_nonneg hR) C₂.coe_nonneg hbound

/-- Quantitative forcing-space existence for a nonlinearity defined only on
the lower-order state ball.  The state radius makes the top-order arm small;
the horizon makes the lower-order arm and the zero-forcing displacement
small. -/
theorem partial_sol_const
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (hR : 0 < R)
    {L : ℝ≥0}
    (Nfun : lowerState (I := I) (M := M) g₀ a R →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (hLip : LipschitzWith L Nfun)
    (C₁ C₂ : ℝ≥0) (D : ℝ) (hD : 0 ≤ D)
    (hzero : ‖Nfun ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ a hR.le⟩‖ ≤ D)
    (hsmall : (C₁ : ℝ) * R ≤ 1 / 8)
    (hsingle : ∀ u u' : lowerState (I := I) (M := M) g₀ a R,
      ‖Nfun u - Nfun u'‖ ≤
        (C₁ : ℝ) *
            max ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                    (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u : _)‖
                ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                    (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u' : _)‖ *
              ‖(u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) - (u' : _)‖ +
          (C₂ : ℝ) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) ((u : _) - (u' : _))‖) :
    ∃ T₀ : ℝ,
      T₀ = min 1 (min (1 / (64 * ((C₂ : ℝ) + 1) ^ 2))
        (((R / 4) / (2 * (D + 1))) ^ 2)) ∧
      0 < T₀ ∧ ∀ {T : ℝ} (hT : 0 < T) (_hTT₀ : T ≤ T₀) (hT1 : T ≤ 1),
      ∃ (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
        (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T),
        let field := maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce
        u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce ∧
          (∀ᵐ t ∂(timeMeasure T),
            field t ∈ lowerState (I := I) (M := M) g₀ a R) ∧
          gforce =ᵐ[timeMeasure T]
            (fun t => Nfun (aeSetLift
              (zero_mem_lowerState (I := I) (M := M) g₀ a hR.le) field t)) ∧
          timeH1.trace0 _ T u = 0 ∧
          timeH1.timeDeriv _ T u =
            timeScaleLaplacian (I := I) (M := M) (a : ℝ) field + gforce ∧
          ‖gforce‖ ≤ R / 4 := by
  classical
  have h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  let hz := zero_mem_lowerState (I := I) (M := M) g₀ a hR.le
  set ρ : ℝ := R / 4 with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; positivity
  have h2ρR : 2 * ρ ≤ R := by rw [hρdef]; nlinarith [hR]
  set T₀ : ℝ := min 1 (min (1 / (64 * ((C₂ : ℝ) + 1) ^ 2))
    ((ρ / (2 * (D + 1))) ^ 2)) with hT₀def
  have hD1 : 0 < D + 1 := by linarith
  have hT₀ : 0 < T₀ := by
    refine lt_min one_pos (lt_min (by positivity) ?_)
    positivity
  refine ⟨T₀, ?_, hT₀, ?_⟩
  · rw [hT₀def, hρdef]
  intro T hT hTT₀ hT1
  have hTlo : T ≤ 1 / (64 * ((C₂ : ℝ) + 1) ^ 2) :=
    le_trans hTT₀ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hTstay : T ≤ (ρ / (2 * (D + 1))) ^ 2 :=
    le_trans hTT₀ (le_trans (min_le_right _ _) (min_le_right _ _))
  set Λ : ℝ := (C₁ : ℝ) * R * (1 + T) + (C₂ : ℝ) * (2 * Real.sqrt T)
    with hΛdef
  have hΛnn : 0 ≤ Λ := by rw [hΛdef]; positivity
  have h1T : (1 : ℝ) + T ≤ 2 := by linarith
  have harm1 : (C₁ : ℝ) * R * (1 + T) ≤ 1 / 4 := by
    have hCRnn : 0 ≤ (C₁ : ℝ) * R := mul_nonneg C₁.coe_nonneg hR.le
    calc
      (C₁ : ℝ) * R * (1 + T) ≤ (C₁ : ℝ) * R * 2 :=
        mul_le_mul_of_nonneg_left h1T hCRnn
      _ ≤ (1 / 8 : ℝ) * 2 := mul_le_mul_of_nonneg_right hsmall (by positivity)
      _ = 1 / 4 := by norm_num
  have hsqrtT : Real.sqrt T ≤ 1 / (8 * ((C₂ : ℝ) + 1)) := by
    rw [show (1 : ℝ) / (8 * ((C₂ : ℝ) + 1)) =
      Real.sqrt ((1 / (8 * ((C₂ : ℝ) + 1))) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
    refine Real.sqrt_le_sqrt (le_trans hTlo ?_)
    rw [div_pow, one_pow, mul_pow]
    norm_num
  have harm2 : (C₂ : ℝ) * (2 * Real.sqrt T) ≤ 1 / 4 := by
    calc
      (C₂ : ℝ) * (2 * Real.sqrt T) = 2 * (C₂ : ℝ) * Real.sqrt T := by ring
      _ ≤ 2 * (C₂ : ℝ) * (1 / (8 * ((C₂ : ℝ) + 1))) := by
        exact mul_le_mul_of_nonneg_left hsqrtT (by positivity)
      _ = (C₂ : ℝ) / ((C₂ : ℝ) + 1) * (1 / 4) := by
        field_simp
        ring
      _ ≤ 1 / 4 := by
        have hfrac : (C₂ : ℝ) / ((C₂ : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]
          linarith [C₂.coe_nonneg]
        nlinarith [hfrac,
          div_nonneg C₂.coe_nonneg (by positivity : (0 : ℝ) ≤ (C₂ : ℝ) + 1)]
  have hΛle : Λ ≤ 1 / 2 := by rw [hΛdef]; linarith
  have hΛlt : Λ < 1 := by linarith

  set z₀ : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T := 0 with hz₀
  set ρt := recenteredBallRetraction z₀ ρ with hρtdef
  have hρt_mem : ∀ F, ρt F ∈ Metric.closedBall z₀ ρ := fun F =>
    recenteredBallRetraction_mapsTo (X := _) hρ.le z₀ (Set.mem_univ F)
  have hρt_norm : ∀ F, ‖ρt F‖ ≤ ρ := by
    intro F
    have h := hρt_mem F
    rw [Metric.mem_closedBall, hz₀, dist_zero_right] at h
    exact h
  have hρt_lip : LipschitzWith 1 ρt :=
    recenteredBallRetraction_lipschitzWith hρ.le z₀
  set field : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T →
      timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) T :=
    fun F => maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) (ρt F)
    with hfielddef
  have hstate : ∀ F, ∀ᵐ t ∂(timeMeasure T),
      field F t ∈ lowerState (I := I) (M := M) g₀ a R := by
    intro F
    exact field_mem_lower (I := I) (M := M) g₀ a hT hT1 h2ρR
      (ρt F) (hρt_norm F)
  set Ψ : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T →
      timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T :=
    fun F => nemytskiiOn hz hLip (field F) (hstate F)
    with hΨdef

  have hΨ_retr : ∀ F F',
      ‖Ψ F - Ψ F'‖ ≤ Λ * ‖ρt F - ρt F'‖ := by
    intro F F'
    have hfield_dist : ‖field F - field F'‖ ≤ (1 + T) * ‖ρt F - ρt F'‖ := by
      exact maxRegDuhamelSolField_dist_le (I := I) (M := M) (h_compact := h_compact)
        (a := (a : ℝ)) hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) (ρt F) (ρt F')
    have hincl_dist :
        ‖timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (field F - field F')‖ ≤
          2 * Real.sqrt T * ‖ρt F - ρt F'‖ := by
      change
        ‖timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith)
            (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
                (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) (ρt F) -
              maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
                (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) (ρt F'))‖ ≤
          2 * Real.sqrt T * ‖ρt F - ρt F'‖
      rw [map_sub,
        timeL2Inclusion_maxRegDuhamelSolField (I := I) (M := M) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) (ρt F),
        timeL2Inclusion_maxRegDuhamelSolField (I := I) (M := M) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) (ρt F')]
      exact maxRegDuhamelSolFieldHa1_dist_le (I := I) (M := M) (h_compact := h_compact)
        (a := (a : ℝ)) hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) (ρt F) (ρt F')
    have hmain := nemytskiiOn_mixed (I := I) (M := M) g₀ a hR.le hLip hsingle
      (field F) (field F') (hstate F) (hstate F')
    calc
      ‖Ψ F - Ψ F'‖ ≤
          (C₁ : ℝ) * R * ‖field F - field F'‖ +
            (C₂ : ℝ) *
              ‖timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (field F - field F')‖ :=
        by simpa only [hΨdef] using hmain
      _ ≤ (C₁ : ℝ) * R * ((1 + T) * ‖ρt F - ρt F'‖) +
            (C₂ : ℝ) * (2 * Real.sqrt T * ‖ρt F - ρt F'‖) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hfield_dist (mul_nonneg C₁.coe_nonneg hR.le))
          (mul_le_mul_of_nonneg_left hincl_dist C₂.coe_nonneg)
      _ = Λ * ‖ρt F - ρt F'‖ := by rw [hΛdef]; ring
  have hΨ_lip : ∀ F F', ‖Ψ F - Ψ F'‖ ≤ Λ * ‖F - F'‖ := by
    intro F F'
    refine (hΨ_retr F F').trans ?_
    have hr := hρt_lip.dist_le_mul F F'
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at hr
    exact mul_le_mul_of_nonneg_left hr hΛnn
  have hcontr : ContractingWith Λ.toNNReal Ψ := by
    refine ⟨?_, ?_⟩
    · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hΛnn]
      exact hΛlt
    · refine LipschitzWith.of_dist_le_mul (fun F F' => ?_)
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hΛnn]
      exact hΨ_lip F F'

  have hρt0 : ρt z₀ = z₀ :=
    recenteredBallRetraction_eq_self_of_mem (Metric.mem_closedBall_self hρ.le)
  have hfield0 : field z₀ = 0 := by
    change maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) (ρt z₀) = 0
    rw [hρt0, hz₀]
    exact maxRegDuhamelSolField_zero_zero (I := I) (M := M) (g₀ := g₀) hT hT1
  have hΨ0 : ‖Ψ z₀‖ ≤ Real.sqrt T * ‖Nfun ⟨0, hz⟩‖ := by
    change ‖nemytskiiOn hz hLip (field z₀) (hstate z₀)‖ ≤
      Real.sqrt T * ‖Nfun ⟨0, hz⟩‖
    have hstate0 : ∀ᵐ t ∂(timeMeasure T),
        ((0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) T) t) ∈
          lowerState (I := I) (M := M) g₀ a R := by
      simpa only [hfield0] using hstate z₀
    have hzeroBound := nemytskiiOn_zero_le hz hLip hstate0
    simpa only [hfield0] using hzeroBound
  have hsqrtTD : Real.sqrt T * D ≤ ρ / 2 := by
    have hsqrtTstay : Real.sqrt T ≤ ρ / (2 * (D + 1)) := by
      rw [show ρ / (2 * (D + 1)) = Real.sqrt ((ρ / (2 * (D + 1))) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt hTstay
    calc
      Real.sqrt T * D ≤ (ρ / (2 * (D + 1))) * D :=
        mul_le_mul_of_nonneg_right hsqrtTstay hD
      _ ≤ (ρ / (2 * (D + 1))) * (D + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ρ / 2 := by field_simp
  have hΨ0' : ‖Ψ z₀‖ ≤ ρ / 2 :=
    hΨ0.trans ((mul_le_mul_of_nonneg_left hzero (Real.sqrt_nonneg T)).trans hsqrtTD)
  have hΨstay : ∀ F, ‖Ψ F‖ ≤ ρ := by
    intro F
    have hdist := hΨ_retr F z₀
    have hretr0 : ‖ρt F - ρt z₀‖ ≤ ρ := by
      rw [hρt0, hz₀, sub_zero]
      exact hρt_norm F
    calc
      ‖Ψ F‖ = ‖(Ψ F - Ψ z₀) + Ψ z₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖Ψ F - Ψ z₀‖ + ‖Ψ z₀‖ := norm_add_le _ _
      _ ≤ Λ * ‖ρt F - ρt z₀‖ + ρ / 2 := add_le_add hdist hΨ0'
      _ ≤ (1 / 2) * ρ + ρ / 2 := by
        exact add_le_add
          ((mul_le_mul_of_nonneg_left hretr0 hΛnn).trans
            (mul_le_mul_of_nonneg_right hΛle hρ.le)) le_rfl
      _ = ρ := by ring

  set Fstar := ContractingWith.fixedPoint Ψ hcontr with hFstar_def
  have hfix : Ψ Fstar = Fstar := ContractingWith.fixedPoint_isFixedPt hcontr
  have hFstar : ‖Fstar‖ ≤ ρ := by rw [← hfix]; exact hΨstay Fstar
  have hρtstar : ρt Fstar = Fstar :=
    recenteredBallRetraction_eq_self_of_mem (by
      rw [Metric.mem_closedBall, hz₀, dist_zero_right]
      exact hFstar)
  set trueField := maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
    (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) Fstar with htrueField
  have hfieldstar : field Fstar = trueField := by
    change maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) (ρt Fstar) = trueField
    rw [hρtstar, htrueField]
  have hstateStar : ∀ᵐ t ∂(timeMeasure T),
      trueField t ∈ lowerState (I := I) (M := M) g₀ a R := by
    rw [← hfieldstar]
    exact hstate Fstar
  have hforceEq : Fstar = nemytskiiOn hz hLip (field Fstar) (hstate Fstar) := by
    calc
      Fstar = Ψ Fstar := hfix.symm
      _ = nemytskiiOn hz hLip (field Fstar) (hstate Fstar) := by
        simp only [hΨdef]
  have hforceAe₀ : ⇑Fstar =ᵐ[timeMeasure T]
      fun t => Nfun (aeSetLift hz (field Fstar) t) := by
    have heq : ⇑Fstar =ᵐ[timeMeasure T]
        ⇑(nemytskiiOn hz hLip (field Fstar) (hstate Fstar)) := by
      exact Filter.Eventually.of_forall (fun t =>
        congrArg (fun F : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T => F t)
          hforceEq)
    exact heq.trans (nemytskiiOn_coeFn hz hLip (field Fstar) (hstate Fstar))
  have hforceAe : ⇑Fstar =ᵐ[timeMeasure T]
      fun t => Nfun (aeSetLift hz trueField t) := by
    simpa only [hfieldstar] using hforceAe₀

  refine ⟨maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) Fstar,
    Fstar, ?_⟩
  dsimp only
  refine ⟨rfl, hstateStar, hforceAe, ?_, ?_, ?_⟩
  · rw [maxRegDuhamelMap_trace0 (I := I) (M := M) (a := (a : ℝ)) (T := T) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) Fstar, map_zero]
  · rw [maxRegDuhamelMap_timeDeriv_eq (I := I) (M := M) (h_compact := h_compact)
      (a := (a : ℝ)) (T := T) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) Fstar]
  · simpa only [hρdef] using hFstar

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
