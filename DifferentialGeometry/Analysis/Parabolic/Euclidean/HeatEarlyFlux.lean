import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelGaussian
import DifferentialGeometry.Analysis.Parabolic.Euclidean.RoughCarleson
import DifferentialGeometry.External.DeGiorgi.FiniteCover
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The early divergence-source heat potential

This file begins the `Y¹ → L∞` value estimate for the Euclidean heat map.
The source is only locally `L²`, so the early Duhamel slab is treated by
Cauchy--Schwarz on parabolic cylinders and the off-diagonal first-derivative
Gaussian majorant.
-/

noncomputable section

open MeasureTheory Real Set
open scoped ENNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

section Holder

variable {X F : Type*} [MeasurableSpace X]
  [NormedAddCommGroup F]

/-- The finite-measure `L² → L¹` estimate in the `ENNReal` form used by
rough parabolic cylinder masses. -/
theorem lintegral_enorm_le_sqrt (μ : Measure X) (f : X → F)
    (hf : AEStronglyMeasurable f μ) :
    (∫⁻ x, ‖f x‖ₑ ∂μ) ≤
      (μ Set.univ) ^ ((1 : ℝ) / 2) *
        (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ) ^ ((1 : ℝ) / 2) := by
  have hg : AEMeasurable (fun x => ‖f x‖ₑ) μ := by
    simpa only [← ofReal_norm_eq_enorm] using
      hf.norm.aemeasurable.ennreal_ofReal
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq
    (μ := μ) Real.HolderConjugate.two_two
    (aemeasurable_const : AEMeasurable (fun _ : X => (1 : ℝ≥0∞)) μ)
    hg
  have hone : (∫⁻ _ : X, (1 : ℝ≥0∞) ^ (2 : ℝ) ∂μ) = μ Set.univ := by
    simp
  have hsq : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) =
      ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ := by
    apply lintegral_congr
    intro x
    rw [ENNReal.rpow_two, ← ofReal_norm_eq_enorm,
      ← ENNReal.ofReal_pow (norm_nonneg _) 2]
  rw [hone, hsq] at hholder
  simpa only [Pi.mul_apply, one_mul] using hholder

end Holder

section Cylinders

variable {V : Type*} [NormedAddCommGroup V]

/-- An early half-cylinder at the observation-time heat scale. -/
def earlyFluxCyl (t : ℝ) (x : V) : Set (ℝ × V) :=
  Set.Ioc 0 (t / 2) ×ˢ Metric.ball x (heatScale t)

/-- The early half-cylinder is contained in the full Carleson cylinder at
the same heat scale. -/
theorem earlyFluxCyl_sub {t : ℝ} (ht : 0 ≤ t) (x : V) :
    earlyFluxCyl t x ⊆ paraCyl x (heatScale t) := by
  rintro z ⟨hzs, hzx⟩
  refine ⟨⟨hzs.1, ?_⟩, hzx⟩
  have hhalf : t / 2 ≤ t := by linarith
  simpa [heatScale, Real.sq_sqrt ht] using hzs.2.trans hhalf

variable [MeasurableSpace V] [BorelSpace V]

theorem earlyFluxCyl_meas (t : ℝ) (x : V) :
    MeasurableSet (earlyFluxCyl t x) :=
  measurableSet_Ioc.prod measurableSet_ball

variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [Nontrivial V]
  {F : Type*} [NormedAddCommGroup F]

/-- The volume of the unit ball in the normalized Euclidean Haar measure. -/
def heatBallVol (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.sqrt Real.pi ^ Module.finrank ℝ V /
      Real.Gamma (Module.finrank ℝ V / 2 + 1))

/-- A half-cylinder has at most the full parabolic volume scale
`(sqrt t)^(n+2)` times the unit-ball volume. -/
theorem earlyFluxCyl_volume_le {t : ℝ} (ht : 0 < t) (x : V) :
    (stVolume : Measure (ℝ × V)) (earlyFluxCyl t x) ≤
      (ENNReal.ofReal (heatScale t)) ^ (Module.finrank ℝ V + 2) *
        heatBallVol V := by
  rw [stVolume, earlyFluxCyl, Measure.prod_prod, Real.volume_Ioc,
    InnerProductSpace.volume_ball]
  have ht2 : t / 2 ≤ t := by linarith
  have hs0 : 0 ≤ heatScale t := Real.sqrt_nonneg _
  calc
    ENNReal.ofReal (t / 2 - 0) *
          (ENNReal.ofReal (heatScale t) ^ Module.finrank ℝ V * heatBallVol V) ≤
        ENNReal.ofReal t *
          (ENNReal.ofReal (heatScale t) ^ Module.finrank ℝ V * heatBallVol V) := by
      gcongr
      linarith
    _ = ENNReal.ofReal ((heatScale t) ^ 2) *
          (ENNReal.ofReal (heatScale t) ^ Module.finrank ℝ V * heatBallVol V) := by
      rw [heatScale, Real.sq_sqrt ht.le]
    _ = (ENNReal.ofReal (heatScale t)) ^ (Module.finrank ℝ V + 2) *
          heatBallVol V := by
      rw [ENNReal.ofReal_pow hs0 2, pow_add]
      ring

/-- The two square-root factors supplied by cylinder volume and local `L²`
mass have exactly the parabolic scale `r^(n+1)`. -/
theorem parabolicSqrt_mul (r B C : ℝ≥0∞) (n : ℕ) :
    (r ^ (n + 2) * B) ^ ((1 : ℝ) / 2) *
        (C * r ^ n) ^ ((1 : ℝ) / 2) =
      r ^ (n + 1) * B ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2) := by
  have hh : (0 : ℝ) ≤ (1 : ℝ) / 2 := by norm_num
  have hp (k : ℕ) : (r ^ k) ^ ((1 : ℝ) / 2) =
      r ^ ((k : ℝ) * ((1 : ℝ) / 2)) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  rw [ENNReal.mul_rpow_of_nonneg _ _ hh,
    ENNReal.mul_rpow_of_nonneg _ _ hh, hp, hp]
  calc
    r ^ ((n + 2 : ℕ) * ((1 : ℝ) / 2)) * B ^ ((1 : ℝ) / 2) *
          (C ^ ((1 : ℝ) / 2) * r ^ ((n : ℝ) * ((1 : ℝ) / 2))) =
        (r ^ ((n + 2 : ℕ) * ((1 : ℝ) / 2)) *
          r ^ ((n : ℝ) * ((1 : ℝ) / 2))) *
            B ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2) := by
      ac_rfl
    _ = r ^ (((n + 2 : ℕ) : ℝ) * ((1 : ℝ) / 2) +
          (n : ℝ) * ((1 : ℝ) / 2)) *
            B ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2) := by
      rw [← ENNReal.rpow_add_of_nonneg _ _
        (mul_nonneg (Nat.cast_nonneg _) hh)
        (mul_nonneg (Nat.cast_nonneg _) hh)]
    _ = r ^ (((n + 1 : ℕ) : ℝ)) *
          B ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2) := by
      congr 3
      norm_num
      ring
    _ = r ^ (n + 1) * B ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2) := by
      rw [ENNReal.rpow_natCast]

/-- Cauchy--Schwarz converts local gradient-Carleson mass into the `L¹`
mass needed by a pointwise kernel bound on an early cylinder. -/
theorem earlyFlux_l1 {T t : ℝ} {C : ℝ≥0∞}
    (ht : 0 < t) (htT : t ≤ T) (f : ℝ × V → F) (x : V)
    (hsrc : GradCarl T C f) :
    (∫⁻ z in earlyFluxCyl t x, ENNReal.ofReal ‖f z‖
        ∂(stVolume : Measure (ℝ × V))) ≤
      ((ENNReal.ofReal (heatScale t)) ^ (Module.finrank ℝ V + 2) *
          heatBallVol V) ^ ((1 : ℝ) / 2) *
        (C * ENNReal.ofReal
          ((heatScale t) ^ Module.finrank ℝ V)) ^ ((1 : ℝ) / 2) := by
  let μ : Measure (ℝ × V) :=
    (stVolume : Measure (ℝ × V)).restrict (earlyFluxCyl t x)
  have hholder := lintegral_enorm_le_sqrt μ f
    (hsrc.ae.mono_measure Measure.restrict_le_self)
  have hvol : μ Set.univ ≤
      (ENNReal.ofReal (heatScale t)) ^ (Module.finrank ℝ V + 2) *
        heatBallVol V := by
    simpa only [μ, Measure.restrict_apply_univ] using
      earlyFluxCyl_volume_le ht x
  have hscaleT : (heatScale t) ^ 2 ≤ T := by
    simpa [heatScale, Real.sq_sqrt ht.le] using htT
  have hmass :
      (∫⁻ z, ENNReal.ofReal (‖f z‖ ^ 2) ∂μ) ≤
        C * ENNReal.ofReal
          ((heatScale t) ^ Module.finrank ℝ V) := by
    calc
      (∫⁻ z, ENNReal.ofReal (‖f z‖ ^ 2) ∂μ) ≤
          gradMass f x (heatScale t) := by
        exact lintegral_mono_set (earlyFluxCyl_sub ht.le x)
      _ ≤ C * ENNReal.ofReal
          ((heatScale t) ^ Module.finrank ℝ V) :=
        hsrc.bound x (heatScale t) (heatScale_pos ht) hscaleT
  calc
    (∫⁻ z in earlyFluxCyl t x, ENNReal.ofReal ‖f z‖
        ∂(stVolume : Measure (ℝ × V))) = ∫⁻ z, ‖f z‖ₑ ∂μ := by
      change (∫⁻ z, ENNReal.ofReal ‖f z‖ ∂μ) = ∫⁻ z, ‖f z‖ₑ ∂μ
      apply lintegral_congr
      intro z
      rw [ofReal_norm_eq_enorm]
    _ ≤ (μ Set.univ) ^ ((1 : ℝ) / 2) *
        (∫⁻ z, ENNReal.ofReal (‖f z‖ ^ 2) ∂μ) ^ ((1 : ℝ) / 2) := hholder
    _ ≤ ((ENNReal.ofReal (heatScale t)) ^ (Module.finrank ℝ V + 2) *
          heatBallVol V) ^ ((1 : ℝ) / 2) *
        (C * ENNReal.ofReal
          ((heatScale t) ^ Module.finrank ℝ V)) ^ ((1 : ℝ) / 2) := by
      gcongr

/-- Scale-cancelled form of `earlyFlux_l1`: the early-cylinder `L¹` source
mass carries exactly one factor `(sqrt t)^(n+1)`. -/
theorem earlyFlux_l1_scale {T t : ℝ} {C : ℝ≥0∞}
    (ht : 0 < t) (htT : t ≤ T) (f : ℝ × V → F) (x : V)
    (hsrc : GradCarl T C f) :
    (∫⁻ z in earlyFluxCyl t x, ENNReal.ofReal ‖f z‖
        ∂(stVolume : Measure (ℝ × V))) ≤
      (ENNReal.ofReal (heatScale t)) ^ (Module.finrank ℝ V + 1) *
        (heatBallVol V) ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2) := by
  refine (earlyFlux_l1 ht htT f x hsrc).trans_eq ?_
  have hs0 : 0 ≤ heatScale t := Real.sqrt_nonneg _
  have hpow : ENNReal.ofReal
      ((heatScale t) ^ Module.finrank ℝ V) =
      (ENNReal.ofReal (heatScale t)) ^ Module.finrank ℝ V :=
    ENNReal.ofReal_pow hs0 (Module.finrank ℝ V)
  rw [hpow, parabolicSqrt_mul]

/-- A finite heat-scale ball cover converts the local gradient-Carleson
estimate into an `L¹` estimate on the covered early slab.  The theorem is
stated independently of how the cover is produced, so quantitative Euclidean
covering lemmas can be inserted without duplicating the analytic argument. -/
theorem earlyFlux_cover_l1 {T t : ℝ} {C : ℝ≥0∞}
    (ht : 0 < t) (htT : t ≤ T) (f : ℝ × V → F) (A : Set V)
    (s : Finset V)
    (hcover : A ⊆ ⋃ c ∈ s, Metric.ball c (heatScale t))
    (hsrc : GradCarl T C f) :
    (∫⁻ z in Set.Ioc 0 (t / 2) ×ˢ A, ENNReal.ofReal ‖f z‖
        ∂(stVolume : Measure (ℝ × V))) ≤
      (s.card : ℝ≥0∞) *
        ((ENNReal.ofReal (heatScale t)) ^ (Module.finrank ℝ V + 1) *
          (heatBallVol V) ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2)) := by
  let U : V → Set (ℝ × V) := fun c => earlyFluxCyl t c
  have hcyl : (Set.Ioc 0 (t / 2) ×ˢ A) ⊆ ⋃ c ∈ s, U c := by
    rintro z ⟨hzs, hzy⟩
    have hcov := hcover hzy
    rw [Set.mem_iUnion] at hcov
    obtain ⟨c, hcov⟩ := hcov
    rw [Set.mem_iUnion] at hcov
    obtain ⟨hc, hyc⟩ := hcov
    exact Set.mem_iUnion.2 ⟨c, Set.mem_iUnion.2 ⟨hc, hzs, hyc⟩⟩
  calc
    (∫⁻ z in Set.Ioc 0 (t / 2) ×ˢ A, ENNReal.ofReal ‖f z‖
        ∂(stVolume : Measure (ℝ × V))) ≤
        ∑ c ∈ s, ∫⁻ z in U c, ENNReal.ofReal ‖f z‖
          ∂(stVolume : Measure (ℝ × V)) :=
      DeGiorgi.lintegralOn_le_sum_lintegralOn_of_finite_cover hcyl
    _ ≤ ∑ _c ∈ s,
        (ENNReal.ofReal (heatScale t)) ^ (Module.finrank ℝ V + 1) *
          (heatBallVol V) ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2) := by
      apply Finset.sum_le_sum
      intro c hc
      exact earlyFlux_l1_scale ht htT f c hsrc
    _ = (s.card : ℝ≥0∞) *
        ((ENNReal.ofReal (heatScale t)) ^ (Module.finrank ℝ V + 1) *
          (heatBallVol V) ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2)) := by
      rw [Finset.sum_const, nsmul_eq_mul]

/-- The `k`-th spatial shell in observation-time heat units. -/
def fluxShell (t : ℝ) (x : V) (k : ℕ) : Set V :=
  {y | (k : ℝ) * heatScale t ≤ ‖x - y‖ ∧
    ‖x - y‖ < ((k + 1 : ℕ) : ℝ) * heatScale t}

/-- The early time slab over one divergence-source heat shell. -/
def fluxShellCyl (t : ℝ) (x : V) (k : ℕ) : Set (ℝ × V) :=
  Set.Ioc 0 (t / 2) ×ˢ fluxShell t x k

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [Nontrivial V] in
theorem fluxShellCyl_meas (t : ℝ) (x : V) (k : ℕ) :
    MeasurableSet (fluxShellCyl t x k) := by
  have hnorm : Continuous (fun y : V => ‖x - y‖) :=
    (continuous_const.sub continuous_id).norm
  exact measurableSet_Ioc.prod
    ((isClosed_le continuous_const hnorm).measurableSet.inter
      (isOpen_lt hnorm continuous_const).measurableSet)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- On the `k`-th early shell, the first heat derivative carries the exact
radial factor `k+1` and Gaussian decay `exp (-k^2/4)`. -/
theorem heatD1_early_shell {t s : ℝ} (ht : 0 < t) (hs : 0 ≤ s)
    (hst : s ≤ t / 2) (w : V) {x y : V} (k : ℕ)
    (hy : y ∈ fluxShell t x k) :
    ‖heatD1 (t - s) w (x - y)‖ ≤
      ‖w‖ *
        (((heatScale (t / 2)) ^ Module.finrank ℝ V)⁻¹ *
          (heatScale (t / 2))⁻¹ *
            (((2 : ℝ)⁻¹ *
                (Real.sqrt 2 * ((k + 1 : ℕ) : ℝ))) *
              ((baseHeatMass V)⁻¹ *
                Real.exp (-(4 : ℝ)⁻¹ * (k : ℝ) ^ 2)))) := by
  have hlo : (k : ℝ) ≤
      ‖(heatScale (t - s))⁻¹ • (x - y)‖ :=
    earlyScaled_lo ht hs hst (Nat.cast_nonneg k) hy.1
  have hhi : ‖(heatScale (t - s))⁻¹ • (x - y)‖ ≤
      Real.sqrt 2 * ((k + 1 : ℕ) : ℝ) :=
    earlyScaled_hi ht hs hst (by positivity) hy.2.le
  have hmaj := heatD1Maj_early (V := V) (t := t) (s := s)
    (R := (k : ℝ)) (Q := Real.sqrt 2 * ((k + 1 : ℕ) : ℝ))
    ht hs hst (Nat.cast_nonneg k) hlo hhi
  have hdiff : 0 < t - s := by linarith
  calc
    ‖heatD1 (t - s) w (x - y)‖ ≤
        ‖w‖ * heatD1Maj (t - s) (x - y) :=
      heatD1_bound hdiff w (x - y)
    _ ≤ ‖w‖ *
        (((heatScale (t / 2)) ^ Module.finrank ℝ V)⁻¹ *
          (heatScale (t / 2))⁻¹ *
            (((2 : ℝ)⁻¹ *
                (Real.sqrt 2 * ((k + 1 : ℕ) : ℝ))) *
              ((baseHeatMass V)⁻¹ *
                Real.exp (-(4 : ℝ)⁻¹ * (k : ℝ) ^ 2)))) := by
      exact mul_le_mul_of_nonneg_left hmaj (norm_nonneg w)

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
  [Nontrivial V] in
/-- The extra inverse heat scale in the first derivative kernel cancels the
extra spatial-time factor in `earlyFlux_l1_scale`. -/
theorem halfScale_cancel_succ {t : ℝ} (ht : 0 < t) :
    ((heatScale (t / 2)) ^ Module.finrank ℝ V)⁻¹ *
        (heatScale (t / 2))⁻¹ *
          (heatScale t) ^ (Module.finrank ℝ V + 1) =
      (Real.sqrt 2) ^ (Module.finrank ℝ V + 1) := by
  have hhalf : 0 < t / 2 := half_pos ht
  have hs : 0 < heatScale (t / 2) := heatScale_pos hhalf
  have hscale : heatScale t = Real.sqrt 2 * heatScale (t / 2) := by
    have ht_sq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
    have htwo_sq : (Real.sqrt 2) ^ 2 = 2 :=
      Real.sq_sqrt (by norm_num)
    have hhalf_sq : (Real.sqrt (t / 2)) ^ 2 = t / 2 :=
      Real.sq_sqrt hhalf.le
    have hprod_sq : (Real.sqrt 2 * Real.sqrt (t / 2)) ^ 2 = t := by
      rw [mul_pow, htwo_sq, hhalf_sq]
      ring
    unfold heatScale
    nlinarith [Real.sqrt_nonneg t, Real.sqrt_nonneg 2,
      Real.sqrt_nonneg (t / 2),
      mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg (t / 2))]
  rw [hscale, mul_pow, pow_succ]
  field_simp [hs.ne']
  ring

/-- The dimension-only first-derivative factor in the early flux value
estimate, before the cylinder-volume square root is inserted. -/
def earlyFluxD1C (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : ℝ :=
  (Real.sqrt 2) ^ (Module.finrank ℝ V + 1) *
    (((2 : ℝ)⁻¹ * Real.sqrt 2) * (baseHeatMass V)⁻¹)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem earlyFluxD1C_nonneg : 0 ≤ earlyFluxD1C V := by
  unfold earlyFluxD1C
  exact mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)
    (mul_nonneg
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
      (inv_nonneg.mpr (baseHeatMass_pos (V := V)).le))

/-- The full dimension-only early `Y¹ → L∞` value constant. -/
def earlyFluxC (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : ℝ≥0∞ :=
  ENNReal.ofReal (earlyFluxD1C V) *
    (heatBallVol V) ^ ((1 : ℝ) / 2)

variable [NormedSpace ℝ F] [CompleteSpace F]

/-- The scalar mass of one early divergence-source shell integrand. -/
def fluxShellMass (t : ℝ) (w : V) (f : ℝ × V → F)
    (x : V) (k : ℕ) : ℝ≥0∞ :=
  ∫⁻ z in fluxShellCyl t x k,
    ‖heatD1 (t - z.1) w (x - z.2) • f z‖ₑ
      ∂(stVolume : Measure (ℝ × V))

omit [CompleteSpace F] in
/-- Before the final scale cancellation, one shell is bounded by its finite
cover count, its local gradient-Carleson `L¹` mass, and the exact first heat
derivative Gaussian factor. -/
theorem fluxShellMass_raw {T t : ℝ} {C : ℝ≥0∞}
    (ht : 0 < t) (htT : t ≤ T) (w : V) (f : ℝ × V → F)
    (x : V) (k : ℕ) (s : Finset V)
    (hcover : fluxShell t x k ⊆
      ⋃ c ∈ s, Metric.ball c (heatScale t))
    (hsrc : GradCarl T C f) :
    fluxShellMass t w f x k ≤
      ENNReal.ofReal
        (‖w‖ *
          (((heatScale (t / 2)) ^ Module.finrank ℝ V)⁻¹ *
            (heatScale (t / 2))⁻¹ *
              (((2 : ℝ)⁻¹ *
                  (Real.sqrt 2 * ((k + 1 : ℕ) : ℝ))) *
                ((baseHeatMass V)⁻¹ *
                  Real.exp (-(4 : ℝ)⁻¹ * (k : ℝ) ^ 2))))) *
        ((s.card : ℝ≥0∞) *
          ((ENNReal.ofReal (heatScale t)) ^
              (Module.finrank ℝ V + 1) *
            (heatBallVol V) ^ ((1 : ℝ) / 2) *
              C ^ ((1 : ℝ) / 2))) := by
  let K : ℝ :=
    ‖w‖ *
      (((heatScale (t / 2)) ^ Module.finrank ℝ V)⁻¹ *
        (heatScale (t / 2))⁻¹ *
          (((2 : ℝ)⁻¹ *
              (Real.sqrt 2 * ((k + 1 : ℕ) : ℝ))) *
            ((baseHeatMass V)⁻¹ *
              Real.exp (-(4 : ℝ)⁻¹ * (k : ℝ) ^ 2))))
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (norm_nonneg w)
      (mul_nonneg
        (mul_nonneg
          (inv_nonneg.mpr (pow_nonneg (Real.sqrt_nonneg _) _))
          (inv_nonneg.mpr (Real.sqrt_nonneg _)))
        (mul_nonneg
          (mul_nonneg (by positivity)
            (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)))
          (mul_nonneg
            (inv_nonneg.mpr (baseHeatMass_pos (V := V)).le)
            (Real.exp_pos _).le)))
  have hsource :
      (∫⁻ z in fluxShellCyl t x k, ENNReal.ofReal ‖f z‖
          ∂(stVolume : Measure (ℝ × V))) ≤
        (s.card : ℝ≥0∞) *
          ((ENNReal.ofReal (heatScale t)) ^
              (Module.finrank ℝ V + 1) *
            (heatBallVol V) ^ ((1 : ℝ) / 2) *
              C ^ ((1 : ℝ) / 2)) := by
    simpa only [fluxShellCyl] using
      earlyFlux_cover_l1 ht htT f (fluxShell t x k) s hcover hsrc
  have hpoint : ∀ z ∈ fluxShellCyl t x k,
      ‖heatD1 (t - z.1) w (x - z.2) • f z‖ₑ ≤
        ENNReal.ofReal K * ENNReal.ofReal ‖f z‖ := by
    intro z hz
    have hk := heatD1_early_shell ht hz.1.1.le hz.1.2 w k hz.2
    rw [← ofReal_norm_eq_enorm, norm_smul,
      ENNReal.ofReal_mul (norm_nonneg _)]
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hk) _
  have hm : AEMeasurable (fun z : ℝ × V => ENNReal.ofReal ‖f z‖)
      ((stVolume : Measure (ℝ × V)).restrict (fluxShellCyl t x k)) :=
    (hsrc.ae.norm.aemeasurable.ennreal_ofReal).mono_measure
      Measure.restrict_le_self
  unfold fluxShellMass
  calc
    (∫⁻ z in fluxShellCyl t x k,
        ‖heatD1 (t - z.1) w (x - z.2) • f z‖ₑ
          ∂(stVolume : Measure (ℝ × V))) ≤
        ∫⁻ z in fluxShellCyl t x k,
          ENNReal.ofReal K * ENNReal.ofReal ‖f z‖
            ∂(stVolume : Measure (ℝ × V)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (fluxShellCyl_meas t x k)] with z hz
      exact hpoint z hz
    _ = ENNReal.ofReal K *
        (∫⁻ z in fluxShellCyl t x k, ENNReal.ofReal ‖f z‖
          ∂(stVolume : Measure (ℝ × V))) := by
      rw [lintegral_const_mul'' _ hm]
    _ ≤ ENNReal.ofReal K *
        ((s.card : ℝ≥0∞) *
          ((ENNReal.ofReal (heatScale t)) ^
              (Module.finrank ℝ V + 1) *
            (heatBallVol V) ^ ((1 : ℝ) / 2) *
              C ^ ((1 : ℝ) / 2))) :=
      mul_le_mul_right hsource _

omit [CompleteSpace F] in
/-- With the quantitative cover cardinality inserted, all heat scales cancel
from one shell.  Only polynomial cover growth, the radial `k+1` factor, and a
summable exponential remain. -/
theorem fluxShellMass_le {T t : ℝ} {C : ℝ≥0∞}
    (ht : 0 < t) (htT : t ≤ T) (w : V) (f : ℝ × V → F)
    (x : V) (k : ℕ) (s : Finset V)
    (hcard : s.card ≤ (5 * (k + 1)) ^ Module.finrank ℝ V)
    (hcover : fluxShell t x k ⊆
      ⋃ c ∈ s, Metric.ball c (heatScale t))
    (hsrc : GradCarl T C f) :
    fluxShellMass t w f x k ≤
      ENNReal.ofReal ‖w‖ * earlyFluxC V * C ^ ((1 : ℝ) / 2) *
        ENNReal.ofReal
          ((5 * ((k + 1 : ℕ) : ℝ)) ^ Module.finrank ℝ V *
            ((k + 1 : ℕ) : ℝ) *
              Real.exp (-(4 : ℝ)⁻¹ * (k : ℝ))) := by
  let G : ℝ := Real.exp (-(4 : ℝ)⁻¹ * (k : ℝ) ^ 2)
  let P : ℝ :=
    (5 * ((k + 1 : ℕ) : ℝ)) ^ Module.finrank ℝ V
  let q : ℝ := ((k + 1 : ℕ) : ℝ)
  let K : ℝ :=
    ‖w‖ *
      (((heatScale (t / 2)) ^ Module.finrank ℝ V)⁻¹ *
        (heatScale (t / 2))⁻¹ *
          (((2 : ℝ)⁻¹ * (Real.sqrt 2 * q)) *
            ((baseHeatMass V)⁻¹ * G)))
  have hG0 : 0 ≤ G := (Real.exp_pos _).le
  have hP0 : 0 ≤ P := by dsimp [P]; positivity
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (norm_nonneg w)
      (mul_nonneg
        (mul_nonneg
          (inv_nonneg.mpr (pow_nonneg (Real.sqrt_nonneg _) _))
          (inv_nonneg.mpr (Real.sqrt_nonneg _)))
        (mul_nonneg
          (mul_nonneg (by positivity)
            (mul_nonneg (Real.sqrt_nonneg _) hq0))
          (mul_nonneg
            (inv_nonneg.mpr (baseHeatMass_pos (V := V)).le) hG0)))
  have hscale : K * (heatScale t) ^ (Module.finrank ℝ V + 1) =
      ‖w‖ * earlyFluxD1C V * (q * G) := by
    dsimp [K, earlyFluxD1C]
    calc
      ‖w‖ *
            (((heatScale (t / 2)) ^ Module.finrank ℝ V)⁻¹ *
              (heatScale (t / 2))⁻¹ *
                ((2 : ℝ)⁻¹ * (Real.sqrt 2 * q) *
                  ((baseHeatMass V)⁻¹ * G))) *
              (heatScale t) ^ (Module.finrank ℝ V + 1) =
          ‖w‖ *
            ((((heatScale (t / 2)) ^ Module.finrank ℝ V)⁻¹ *
              (heatScale (t / 2))⁻¹ *
                (heatScale t) ^ (Module.finrank ℝ V + 1)) *
              ((2 : ℝ)⁻¹ * (Real.sqrt 2 * q) *
                ((baseHeatMass V)⁻¹ * G))) := by ring
      _ = ‖w‖ *
          ((Real.sqrt 2) ^ (Module.finrank ℝ V + 1) *
            ((2 : ℝ)⁻¹ * (Real.sqrt 2 * q) *
              ((baseHeatMass V)⁻¹ * G))) := by
        rw [halfScale_cancel_succ (V := V) ht]
      _ = ‖w‖ *
          ((Real.sqrt 2) ^ (Module.finrank ℝ V + 1) *
            (((2 : ℝ)⁻¹ * Real.sqrt 2) * (baseHeatMass V)⁻¹)) *
              (q * G) := by ring
  have hpow : ENNReal.ofReal
      ((heatScale t) ^ (Module.finrank ℝ V + 1)) =
      (ENNReal.ofReal (heatScale t)) ^ (Module.finrank ℝ V + 1) :=
    ENNReal.ofReal_pow (Real.sqrt_nonneg _) _
  have hcardE : (s.card : ℝ≥0∞) ≤ ENNReal.ofReal P := by
    rw [← ENNReal.ofReal_natCast s.card]
    apply ENNReal.ofReal_le_ofReal
    dsimp [P]
    exact_mod_cast hcard
  have hkSq : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
    cases k with
    | zero => norm_num
    | succ k =>
        have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
        nlinarith
  have hdecay : G ≤ Real.exp (-(4 : ℝ)⁻¹ * (k : ℝ)) := by
    dsimp [G]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hweight : P * (q * G) ≤
      P * (q * Real.exp (-(4 : ℝ)⁻¹ * (k : ℝ))) := by
    gcongr
  refine (fluxShellMass_raw ht htT w f x k s hcover hsrc).trans ?_
  change ENNReal.ofReal K *
      ((s.card : ℝ≥0∞) *
        ((ENNReal.ofReal (heatScale t)) ^ (Module.finrank ℝ V + 1) *
          (heatBallVol V) ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2))) ≤ _
  calc
    ENNReal.ofReal K *
          ((s.card : ℝ≥0∞) *
            ((ENNReal.ofReal (heatScale t)) ^ (Module.finrank ℝ V + 1) *
              (heatBallVol V) ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2))) =
        (ENNReal.ofReal K *
          (ENNReal.ofReal (heatScale t)) ^ (Module.finrank ℝ V + 1)) *
            (s.card : ℝ≥0∞) * (heatBallVol V) ^ ((1 : ℝ) / 2) *
              C ^ ((1 : ℝ) / 2) := by ac_rfl
    _ = ENNReal.ofReal
          (K * (heatScale t) ^ (Module.finrank ℝ V + 1)) *
            (s.card : ℝ≥0∞) * (heatBallVol V) ^ ((1 : ℝ) / 2) *
              C ^ ((1 : ℝ) / 2) := by
      rw [← hpow, ← ENNReal.ofReal_mul hK0]
    _ = ENNReal.ofReal (‖w‖ * earlyFluxD1C V * (q * G)) *
          (s.card : ℝ≥0∞) * (heatBallVol V) ^ ((1 : ℝ) / 2) *
            C ^ ((1 : ℝ) / 2) := by rw [hscale]
    _ = (ENNReal.ofReal ‖w‖ * ENNReal.ofReal (earlyFluxD1C V) *
          ENNReal.ofReal (q * G)) * (s.card : ℝ≥0∞) *
            (heatBallVol V) ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2) := by
      rw [ENNReal.ofReal_mul
          (mul_nonneg (norm_nonneg w) earlyFluxD1C_nonneg),
        ENNReal.ofReal_mul (norm_nonneg w)]
    _ ≤ (ENNReal.ofReal ‖w‖ * ENNReal.ofReal (earlyFluxD1C V) *
          ENNReal.ofReal (q * G)) * ENNReal.ofReal P *
            (heatBallVol V) ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2) := by
      gcongr
    _ = ENNReal.ofReal ‖w‖ * earlyFluxC V * C ^ ((1 : ℝ) / 2) *
          ENNReal.ofReal (P * (q * G)) := by
      rw [ENNReal.ofReal_mul hP0]
      unfold earlyFluxC
      ac_rfl
    _ ≤ ENNReal.ofReal ‖w‖ * earlyFluxC V * C ^ ((1 : ℝ) / 2) *
          ENNReal.ofReal
            (P * (q * Real.exp (-(4 : ℝ)⁻¹ * (k : ℝ)))) := by
      gcongr
    _ = ENNReal.ofReal ‖w‖ * earlyFluxC V * C ^ ((1 : ℝ) / 2) *
        ENNReal.ofReal
          ((5 * ((k + 1 : ℕ) : ℝ)) ^ Module.finrank ℝ V *
            ((k + 1 : ℕ) : ℝ) *
              Real.exp (-(4 : ℝ)⁻¹ * (k : ℝ))) := by
      dsimp [P, q]
      congr 2
      all_goals ring

/-- The actual Bochner potential of one divergence-source component on an
early heat-scale cylinder. -/
def heatEarly1Near (t : ℝ) (w : V) (f : ℝ × V → F) (x : V) : F :=
  ∫ z in earlyFluxCyl t x,
    heatD1 (t - z.1) w (x - z.2) • f z
      ∂(stVolume : Measure (ℝ × V))

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- On the near early cylinder, the directional first heat derivative is
bounded at the fixed scale `sqrt (t/2)`. -/
theorem heatD1_early_near {t s : ℝ} (ht : 0 < t) (hs : 0 ≤ s)
    (hst : s ≤ t / 2) (w : V) {x y : V}
    (hy : y ∈ Metric.ball x (heatScale t)) :
    ‖heatD1 (t - s) w (x - y)‖ ≤
      ‖w‖ *
        (((heatScale (t / 2)) ^ Module.finrank ℝ V)⁻¹ *
          (heatScale (t / 2))⁻¹ *
            (((2 : ℝ)⁻¹ * Real.sqrt 2) * (baseHeatMass V)⁻¹)) := by
  have hdiff : 0 < t - s := by linarith
  have hx : ‖x - y‖ ≤ (1 : ℝ) * heatScale t := by
    rw [one_mul, ← dist_eq_norm]
    simpa only [dist_comm] using (Metric.mem_ball.mp hy).le
  have hhi :
      ‖(heatScale (t - s))⁻¹ • (x - y)‖ ≤ Real.sqrt 2 := by
    have h := earlyScaled_hi (V := V) (t := t) (s := s) (Q := 1)
      ht hs hst (by norm_num) hx
    simpa using h
  have hmaj := heatD1Maj_early (V := V) (t := t) (s := s)
    (R := 0) (Q := Real.sqrt 2) ht hs hst (by norm_num)
      (norm_nonneg _) hhi
  calc
    ‖heatD1 (t - s) w (x - y)‖ ≤
        ‖w‖ * heatD1Maj (t - s) (x - y) :=
      heatD1_bound hdiff w (x - y)
    _ ≤ ‖w‖ *
        (((heatScale (t / 2)) ^ Module.finrank ℝ V)⁻¹ *
          (heatScale (t / 2))⁻¹ *
            (((2 : ℝ)⁻¹ * Real.sqrt 2) * (baseHeatMass V)⁻¹)) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg w)
      simpa [mul_assoc] using hmaj

omit [CompleteSpace F] in
/-- The early near part of one divergence-source potential has a uniform
pointwise value bound.  The source radius appears as the square root of its
gradient-Carleson mass. -/
theorem heatEarly1Near_norm {T t : ℝ} {C : ℝ≥0∞}
    (ht : 0 < t) (htT : t ≤ T) (w : V)
    (f : ℝ × V → F) (x : V) (hsrc : GradCarl T C f) :
    ‖heatEarly1Near t w f x‖ₑ ≤
      ENNReal.ofReal ‖w‖ * earlyFluxC V * C ^ ((1 : ℝ) / 2) := by
  let K : ℝ := ‖w‖ *
    (((heatScale (t / 2)) ^ Module.finrank ℝ V)⁻¹ *
      (heatScale (t / 2))⁻¹ *
        (((2 : ℝ)⁻¹ * Real.sqrt 2) * (baseHeatMass V)⁻¹))
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (norm_nonneg w)
      (mul_nonneg
        (mul_nonneg
          (inv_nonneg.mpr (pow_nonneg (Real.sqrt_nonneg _) _))
          (inv_nonneg.mpr (Real.sqrt_nonneg _)))
        (mul_nonneg
          (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
          (inv_nonneg.mpr (baseHeatMass_pos (V := V)).le)))
  have hpoint : ∀ z ∈ earlyFluxCyl t x,
      ‖heatD1 (t - z.1) w (x - z.2) • f z‖ₑ ≤
        ENNReal.ofReal K * ENNReal.ofReal ‖f z‖ := by
    intro z hz
    have hk := heatD1_early_near ht hz.1.1.le hz.1.2 w hz.2
    rw [← ofReal_norm_eq_enorm, norm_smul,
      ENNReal.ofReal_mul (norm_nonneg _)]
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hk) _
  have hm : AEMeasurable (fun z : ℝ × V => ENNReal.ofReal ‖f z‖)
      ((stVolume : Measure (ℝ × V)).restrict (earlyFluxCyl t x)) :=
    (hsrc.ae.norm.aemeasurable.ennreal_ofReal).mono_measure
      Measure.restrict_le_self
  have hraw : ‖heatEarly1Near t w f x‖ₑ ≤
      ENNReal.ofReal K *
        ((ENNReal.ofReal (heatScale t)) ^ (Module.finrank ℝ V + 1) *
          (heatBallVol V) ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2)) := by
    unfold heatEarly1Near
    calc
      ‖∫ z in earlyFluxCyl t x,
          heatD1 (t - z.1) w (x - z.2) • f z
            ∂(stVolume : Measure (ℝ × V))‖ₑ ≤
          ∫⁻ z in earlyFluxCyl t x,
            ‖heatD1 (t - z.1) w (x - z.2) • f z‖ₑ
              ∂(stVolume : Measure (ℝ × V)) :=
        enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ z in earlyFluxCyl t x,
          ENNReal.ofReal K * ENNReal.ofReal ‖f z‖
            ∂(stVolume : Measure (ℝ × V)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (earlyFluxCyl_meas t x)] with z hz
        exact hpoint z hz
      _ = ENNReal.ofReal K *
          (∫⁻ z in earlyFluxCyl t x, ENNReal.ofReal ‖f z‖
            ∂(stVolume : Measure (ℝ × V))) := by
        rw [lintegral_const_mul'' _ hm]
      _ ≤ ENNReal.ofReal K *
          ((ENNReal.ofReal (heatScale t)) ^ (Module.finrank ℝ V + 1) *
            (heatBallVol V) ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2)) :=
        mul_le_mul_right (earlyFlux_l1_scale ht htT f x hsrc) _
  have hKscale : K * (heatScale t) ^ (Module.finrank ℝ V + 1) =
      ‖w‖ * earlyFluxD1C V := by
    dsimp [K, earlyFluxD1C]
    calc
      ‖w‖ *
          (((heatScale (t / 2)) ^ Module.finrank ℝ V)⁻¹ *
            (heatScale (t / 2))⁻¹ *
              (((2 : ℝ)⁻¹ * Real.sqrt 2) * (baseHeatMass V)⁻¹)) *
            (heatScale t) ^ (Module.finrank ℝ V + 1) =
        ‖w‖ *
          ((((heatScale (t / 2)) ^ Module.finrank ℝ V)⁻¹ *
            (heatScale (t / 2))⁻¹ *
              (heatScale t) ^ (Module.finrank ℝ V + 1)) *
            (((2 : ℝ)⁻¹ * Real.sqrt 2) * (baseHeatMass V)⁻¹)) := by
          ring
      _ = ‖w‖ *
          ((Real.sqrt 2) ^ (Module.finrank ℝ V + 1) *
            (((2 : ℝ)⁻¹ * Real.sqrt 2) * (baseHeatMass V)⁻¹)) := by
        rw [halfScale_cancel_succ (V := V) ht]
  refine hraw.trans_eq ?_
  have hs0 : 0 ≤ heatScale t := Real.sqrt_nonneg _
  have hpow : ENNReal.ofReal
      ((heatScale t) ^ (Module.finrank ℝ V + 1)) =
      (ENNReal.ofReal (heatScale t)) ^ (Module.finrank ℝ V + 1) :=
    ENNReal.ofReal_pow hs0 _
  calc
    ENNReal.ofReal K *
        ((ENNReal.ofReal (heatScale t)) ^ (Module.finrank ℝ V + 1) *
          (heatBallVol V) ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2)) =
      (ENNReal.ofReal K *
        (ENNReal.ofReal (heatScale t)) ^ (Module.finrank ℝ V + 1)) *
          (heatBallVol V) ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2) := by
      ac_rfl
    _ = ENNReal.ofReal
          (K * (heatScale t) ^ (Module.finrank ℝ V + 1)) *
            (heatBallVol V) ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2) := by
      rw [← hpow, ← ENNReal.ofReal_mul hK0]
    _ = ENNReal.ofReal (‖w‖ * earlyFluxD1C V) *
          (heatBallVol V) ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2) := by
      rw [hKscale]
    _ = ENNReal.ofReal ‖w‖ * earlyFluxC V * C ^ ((1 : ℝ) / 2) := by
      rw [ENNReal.ofReal_mul (norm_nonneg w)]
      unfold earlyFluxC
      ac_rfl

omit [MeasurableSpace V] [BorelSpace V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Nontrivial V] in
/-- Every point lies in an integer observation-scale shell. -/
theorem mem_fluxShell_union {t : ℝ} (ht : 0 < t) (x y : V) :
    y ∈ ⋃ k : ℕ, fluxShell t x k := by
  let rho := heatScale t
  have hrho : 0 < rho := heatScale_pos ht
  let a : ℝ := ‖x - y‖ / rho
  have ha0 : 0 ≤ a := div_nonneg (norm_nonneg _) hrho.le
  let k : ℕ := ⌊a⌋₊
  have hklo : (k : ℝ) ≤ a := Nat.floor_le ha0
  have hkhi : a < (k : ℝ) + 1 := Nat.lt_floor_add_one a
  refine Set.mem_iUnion.2 ⟨k, ?_⟩
  constructor
  · exact (le_div_iff₀ hrho).1 hklo
  · have h := (div_lt_iff₀ hrho).1 hkhi
    simpa only [Nat.cast_add, Nat.cast_one] using h

omit [MeasurableSpace V] [BorelSpace V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Nontrivial V] in
/-- The full early slab is covered by the divergence-source shell cylinders. -/
theorem earlyFluxSlab_sub {t : ℝ} (ht : 0 < t) (x : V) :
    (Set.Ioc 0 (t / 2) ×ˢ (Set.univ : Set V)) ⊆
      ⋃ k : ℕ, fluxShellCyl t x k := by
  rintro z ⟨hzs, -⟩
  obtain ⟨k, hyk⟩ := Set.mem_iUnion.mp (mem_fluxShell_union ht x z.2)
  exact Set.mem_iUnion.2 ⟨k, hzs, hyk⟩

/-- The full early divergence-source heat potential. -/
def heatEarly1 (t : ℝ) (w : V) (f : ℝ × V → F) (x : V) : F :=
  ∫ z in (Set.Ioc 0 (t / 2) ×ˢ (Set.univ : Set V)),
    heatD1 (t - z.1) w (x - z.2) • f z
      ∂(stVolume : Measure (ℝ × V))

omit [CompleteSpace F] in
/-- A quantitative heat-scale cover on every shell and any majorant for the
resulting weight series give the global early divergence-source bound.  The
canonical Euclidean covering and summability APIs can be inserted later by a
short bridge. -/
theorem heatEarly1_norm {T t : ℝ} {C S : ℝ≥0∞}
    (ht : 0 < t) (htT : t ≤ T) (w : V) (f : ℝ × V → F) (x : V)
    (hcovers : ∀ k : ℕ, ∃ s : Finset V,
      s.card ≤ (5 * (k + 1)) ^ Module.finrank ℝ V ∧
        fluxShell t x k ⊆ ⋃ c ∈ s, Metric.ball c (heatScale t))
    (hsum : (∑' k : ℕ, ENNReal.ofReal
      ((5 * ((k + 1 : ℕ) : ℝ)) ^ Module.finrank ℝ V *
        ((k + 1 : ℕ) : ℝ) *
          Real.exp (-(4 : ℝ)⁻¹ * (k : ℝ)))) ≤ S)
    (hsrc : GradCarl T C f) :
    ‖heatEarly1 t w f x‖ₑ ≤
      ENNReal.ofReal ‖w‖ * earlyFluxC V * C ^ ((1 : ℝ) / 2) * S := by
  let q : ℝ × V → ℝ≥0∞ := fun z =>
    ‖heatD1 (t - z.1) w (x - z.2) • f z‖ₑ
  unfold heatEarly1
  calc
    ‖∫ z in (Set.Ioc 0 (t / 2) ×ˢ (Set.univ : Set V)),
        heatD1 (t - z.1) w (x - z.2) • f z
          ∂(stVolume : Measure (ℝ × V))‖ₑ ≤
        ∫⁻ z in (Set.Ioc 0 (t / 2) ×ˢ (Set.univ : Set V)), q z
          ∂(stVolume : Measure (ℝ × V)) :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ z in (⋃ k : ℕ, fluxShellCyl t x k), q z
        ∂(stVolume : Measure (ℝ × V)) :=
      lintegral_mono_set (earlyFluxSlab_sub ht x)
    _ ≤ ∑' k : ℕ, ∫⁻ z in fluxShellCyl t x k, q z
        ∂(stVolume : Measure (ℝ × V)) :=
      lintegral_iUnion_le _ _
    _ = ∑' k : ℕ, fluxShellMass t w f x k := by rfl
    _ ≤ ∑' k : ℕ,
        (ENNReal.ofReal ‖w‖ * earlyFluxC V * C ^ ((1 : ℝ) / 2)) *
          ENNReal.ofReal
            ((5 * ((k + 1 : ℕ) : ℝ)) ^ Module.finrank ℝ V *
              ((k + 1 : ℕ) : ℝ) *
                Real.exp (-(4 : ℝ)⁻¹ * (k : ℝ))) := by
      apply ENNReal.tsum_le_tsum
      intro k
      obtain ⟨s, hcard, hcover⟩ := hcovers k
      exact fluxShellMass_le ht htT w f x k s hcard hcover hsrc
    _ = (ENNReal.ofReal ‖w‖ * earlyFluxC V * C ^ ((1 : ℝ) / 2)) *
        (∑' k : ℕ, ENNReal.ofReal
          ((5 * ((k + 1 : ℕ) : ℝ)) ^ Module.finrank ℝ V *
            ((k + 1 : ℕ) : ℝ) *
              Real.exp (-(4 : ℝ)⁻¹ * (k : ℝ)))) := by
      rw [ENNReal.tsum_mul_left]
    _ ≤ (ENNReal.ofReal ‖w‖ * earlyFluxC V * C ^ ((1 : ℝ) / 2)) * S := by
      exact mul_le_mul_right hsum _
    _ = ENNReal.ofReal ‖w‖ * earlyFluxC V * C ^ ((1 : ℝ) / 2) * S := by
      rfl

end Cylinders

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
