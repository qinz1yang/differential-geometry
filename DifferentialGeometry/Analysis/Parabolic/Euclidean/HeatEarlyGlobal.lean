import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatEarlyNear
import DifferentialGeometry.Analysis.Parabolic.Euclidean.QuantCover
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The global early rough heat potential

The early Duhamel slab is decomposed into spatial shells of width `sqrt t`.
On shell `k`, Gaussian decay contributes `exp (-k^2/4)`, while a quantitative
ball cover contributes at most `(5(k+1))^n` source-Carleson cylinders.  We
weaken the Gaussian to `exp (-k/4)` and sum it with Mathlib's canonical
polynomial-times-exponential summability theorem.
-/

noncomputable section

open MeasureTheory Real Set Filter
open scoped ENNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

/-- The summable real majorant for the `k`-th heat shell in dimension `d`. -/
def shellWeight (d k : ℕ) : ℝ :=
  (5 * ((k + 1 : ℕ) : ℝ)) ^ d *
    Real.exp (-(4 : ℝ)⁻¹ * (k : ℝ))

/-- Polynomial shell growth is summable against the weakened exponential
decay. -/
theorem shellWeight_sum (d : ℕ) : Summable (shellWeight d) := by
  have hbase := Real.summable_pow_mul_exp_neg_nat_mul d
    (by norm_num : 0 < (4 : ℝ)⁻¹)
  have hsucc := hbase.comp_injective Nat.succ_injective
  have hmul := hsucc.mul_left
    ((5 : ℝ) ^ d * Real.exp (4 : ℝ)⁻¹)
  convert hmul using 1 with k
  unfold shellWeight
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.cast_succ]
  rw [mul_pow]
  calc
    5 ^ d * (k + 1 : ℝ) ^ d *
          Real.exp (-(4 : ℝ)⁻¹ * k) =
        (5 ^ d * Real.exp (4 : ℝ)⁻¹) *
          ((k + 1 : ℝ) ^ d *
            Real.exp (-(4 : ℝ)⁻¹ * (k + 1))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = _ := rfl

/-- The ENNReal mass of the shell majorant. -/
def shellSeries (d : ℕ) : ℝ≥0∞ :=
  ∑' k : ℕ, ENNReal.ofReal (shellWeight d k)

/-- The global early `Y⁰ -> C⁰` heat-potential constant. -/
def earlyHeatC (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : ℝ≥0∞ :=
  nearHeatC V * shellSeries (Module.finrank ℝ V)

theorem shellSeries_ne_top (d : ℕ) : shellSeries d ≠ ∞ :=
  (shellWeight_sum d).tsum_ofReal_ne_top

theorem earlyHeatC_ne_top (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] :
    earlyHeatC V ≠ ∞ := by
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (shellSeries_ne_top (Module.finrank ℝ V))

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The `k`-th spatial shell in observation-time heat units. -/
def heatShell (t : ℝ) (x : V) (k : ℕ) : Set V :=
  {y | ((k : ℕ) : ℝ) * heatScale t ≤ ‖x - y‖ ∧
    ‖x - y‖ < (((k + 1 : ℕ) : ℝ) * heatScale t)}

private theorem heatShell_meas (t : ℝ) (x : V) (k : ℕ) :
    MeasurableSet (heatShell t x k) := by
  have hnorm : Continuous (fun y : V ↦ ‖x - y‖) :=
    (continuous_const.sub continuous_id).norm
  exact (isClosed_le continuous_const hnorm).measurableSet.inter
    (isOpen_lt hnorm continuous_const).measurableSet

/-- The early space-time cylinder over one heat shell. -/
def shellCyl (t : ℝ) (x : V) (k : ℕ) : Set (ℝ × V) :=
  Set.Ioc 0 (t / 2) ×ˢ heatShell t x k

theorem shellCyl_meas (t : ℝ) (x : V) (k : ℕ) :
    MeasurableSet (shellCyl t x k) :=
  measurableSet_Ioc.prod (heatShell_meas t x k)

/-- Every spatial point lies in one integer heat shell. -/
theorem mem_shell_union {t : ℝ} (ht : 0 < t) (x y : V) :
    y ∈ ⋃ k : ℕ, heatShell t x k := by
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
  · have := (div_lt_iff₀ hrho).1 hkhi
    simpa only [Nat.cast_add, Nat.cast_one] using this

/-- The whole early Duhamel slab is covered by the shell cylinders. -/
theorem earlySlab_sub {t : ℝ} (ht : 0 < t) (x : V) :
    (Set.Ioc 0 (t / 2) ×ˢ (Set.univ : Set V)) ⊆
      ⋃ k : ℕ, shellCyl t x k := by
  rintro z ⟨hzs, -⟩
  obtain ⟨k, hyk⟩ := Set.mem_iUnion.mp (mem_shell_union ht x z.2)
  exact Set.mem_iUnion.2 ⟨k, hzs, hyk⟩

/-- A time-half ball cylinder is contained in the Carleson cylinder at the
observation-time heat radius. -/
theorem ballCyl_sub {t : ℝ} (ht : 0 < t) (c : V) :
    (Set.Ioc 0 (t / 2) ×ˢ Metric.ball c (heatScale t)) ⊆
      paraCyl c (heatScale t) := by
  rintro z ⟨hzs, hzy⟩
  refine ⟨⟨hzs.1, ?_⟩, hzy⟩
  have hhalf : t / 2 ≤ t := by linarith
  simpa [heatScale, Real.sq_sqrt ht.le] using hzs.2.trans hhalf

/-- The scalar ENNReal mass of the heat integrand on one shell. -/
def shellMass (t : ℝ) (f : ℝ × V → F) (x : V) (k : ℕ) : ℝ≥0∞ :=
  ∫⁻ z in shellCyl t x k,
    ‖heatKernel (t - z.1) (x - z.2) • f z‖ₑ
      ∂(stVolume : Measure (ℝ × V))

theorem nat_sq_ge (k : ℕ) : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
  cases k with
  | zero => norm_num
  | succ k =>
      have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
      nlinarith

/-- One shell is controlled by its polynomial cover count times a summable
exponential weight. -/
theorem shellMass_le {T t : ℝ} {C : ℝ≥0∞}
    (ht : 0 < t) (htT : t ≤ T) (f : ℝ × V → F) (x : V)
    (hsrc : SrcCarl T C f) (k : ℕ) :
    shellMass t f x k ≤
      nearHeatC V * C *
        ENNReal.ofReal (shellWeight (Module.finrank ℝ V) k) := by
  let rho := heatScale t
  have hrho : 0 < rho := heatScale_pos ht
  obtain ⟨s, hcard, hcover⟩ := exists_shell_cover x hrho k
  let U : V → Set (ℝ × V) := fun c ↦
    Set.Ioc 0 (t / 2) ×ˢ Metric.ball c rho
  have hcylCover : shellCyl t x k ⊆ ⋃ c ∈ s, U c := by
    rintro z ⟨hzs, hzy⟩
    have hyclosed : z.2 ∈
        Metric.closedBall x (((k + 1 : ℕ) : ℝ) * rho) := by
      rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
      exact hzy.2.le
    have hycov := hcover hyclosed
    rw [Set.mem_iUnion] at hycov
    obtain ⟨c, hycov⟩ := hycov
    rw [Set.mem_iUnion] at hycov
    obtain ⟨hc, hyc⟩ := hycov
    exact Set.mem_iUnion.2 ⟨c, Set.mem_iUnion.2 ⟨hc, hzs, hyc⟩⟩
  have hscaleT : rho ^ 2 ≤ T := by
    dsimp [rho]
    simpa [heatScale, Real.sq_sqrt ht.le] using htT
  have hsource :
      ∫⁻ z in shellCyl t x k, ENNReal.ofReal ‖f z‖
          ∂(stVolume : Measure (ℝ × V)) ≤
        (s.card : ℝ≥0∞) *
          (C * ENNReal.ofReal (rho ^ Module.finrank ℝ V)) := by
    calc
      (∫⁻ z in shellCyl t x k, ENNReal.ofReal ‖f z‖
          ∂(stVolume : Measure (ℝ × V))) ≤
          ∑ c ∈ s, ∫⁻ z in U c, ENNReal.ofReal ‖f z‖
            ∂(stVolume : Measure (ℝ × V)) :=
        DeGiorgi.lintegralOn_le_sum_lintegralOn_of_finite_cover hcylCover
      _ ≤ ∑ c ∈ s,
          C * ENNReal.ofReal (rho ^ Module.finrank ℝ V) := by
        apply Finset.sum_le_sum
        intro c hc
        exact (lintegral_mono_set (ballCyl_sub ht c)).trans
          (hsrc.bound c rho hrho hscaleT)
      _ = (s.card : ℝ≥0∞) *
          (C * ENNReal.ofReal (rho ^ Module.finrank ℝ V)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  let G : ℝ := Real.exp (-(4 : ℝ)⁻¹ * (k : ℝ) ^ 2)
  let K : ℝ :=
    ((heatScale (t / 2)) ^ Module.finrank ℝ V)⁻¹ *
      ((baseHeatMass V)⁻¹ * G)
  have hG0 : 0 ≤ G := (Real.exp_pos _).le
  have hK0 : 0 ≤ K := by
    exact mul_nonneg
      (inv_nonneg.mpr (pow_nonneg (Real.sqrt_nonneg _) _))
      (mul_nonneg (inv_nonneg.mpr (baseHeatMass_pos (V := V)).le) hG0)
  have hpoint : ∀ z ∈ shellCyl t x k,
      ‖heatKernel (t - z.1) (x - z.2) • f z‖ₑ ≤
        ENNReal.ofReal K * ENNReal.ofReal ‖f z‖ := by
    intro z hz
    have hhalf : t / 2 < t := by linarith
    have hdiff : 0 < t - z.1 :=
      sub_pos.mpr (hz.1.2.trans_lt hhalf)
    have hk0 : 0 ≤ heatKernel (t - z.1) (x - z.2) :=
      heatKernel_nonneg hdiff _
    have hk : heatKernel (t - z.1) (x - z.2) ≤ K := by
      exact heatKernel_early ht hz.1.1.le hz.1.2
        (Nat.cast_nonneg k) hz.2.1
    calc
      ‖heatKernel (t - z.1) (x - z.2) • f z‖ₑ =
          ENNReal.ofReal
            (heatKernel (t - z.1) (x - z.2) * ‖f z‖) := by
        rw [← ofReal_norm_eq_enorm, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg hk0]
      _ ≤ ENNReal.ofReal (K * ‖f z‖) :=
        ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right hk (norm_nonneg _))
      _ = ENNReal.ofReal K * ENNReal.ofReal ‖f z‖ :=
        ENNReal.ofReal_mul hK0
  have hm : AEMeasurable (fun z : ℝ × V ↦ ENNReal.ofReal ‖f z‖)
      ((stVolume : Measure (ℝ × V)).restrict (shellCyl t x k)) :=
    (hsrc.ae.norm.aemeasurable.ennreal_ofReal).mono_measure
      Measure.restrict_le_self
  have hraw : shellMass t f x k ≤
      ENNReal.ofReal K *
        ((s.card : ℝ≥0∞) *
          (C * ENNReal.ofReal (rho ^ Module.finrank ℝ V))) := by
    unfold shellMass
    calc
      (∫⁻ z in shellCyl t x k,
          ‖heatKernel (t - z.1) (x - z.2) • f z‖ₑ
            ∂(stVolume : Measure (ℝ × V))) ≤
          ∫⁻ z in shellCyl t x k,
            ENNReal.ofReal K * ENNReal.ofReal ‖f z‖
              ∂(stVolume : Measure (ℝ × V)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (shellCyl_meas t x k)] with z hz
        exact hpoint z hz
      _ = ENNReal.ofReal K *
          (∫⁻ z in shellCyl t x k, ENNReal.ofReal ‖f z‖
            ∂(stVolume : Measure (ℝ × V))) := by
        rw [lintegral_const_mul'' _ hm]
      _ ≤ ENNReal.ofReal K *
          ((s.card : ℝ≥0∞) *
            (C * ENNReal.ofReal (rho ^ Module.finrank ℝ V))) :=
        mul_le_mul_left' hsource _
  have hreal : K * rho ^ Module.finrank ℝ V =
      ((Real.sqrt 2) ^ Module.finrank ℝ V *
        (baseHeatMass V)⁻¹) * G := by
    dsimp [K]
    calc
      (((heatScale (t / 2)) ^ Module.finrank ℝ V)⁻¹ *
          ((baseHeatMass V)⁻¹ * G)) *
            rho ^ Module.finrank ℝ V =
          (((heatScale (t / 2)) ^ Module.finrank ℝ V)⁻¹ *
            rho ^ Module.finrank ℝ V) *
              ((baseHeatMass V)⁻¹ * G) := by ring
      _ = ((Real.sqrt 2) ^ Module.finrank ℝ V *
          (baseHeatMass V)⁻¹) * G := by
        dsimp [rho]
        rw [halfScale_cancel (V := V) ht]
        ring
  have hcardE : (s.card : ℝ≥0∞) ≤
      ENNReal.ofReal
        ((5 * ((k + 1 : ℕ) : ℝ)) ^ Module.finrank ℝ V) := by
    rw [← ENNReal.ofReal_natCast s.card]
    apply ENNReal.ofReal_le_ofReal
    exact_mod_cast hcard
  have hdecay : G ≤ Real.exp (-(4 : ℝ)⁻¹ * (k : ℝ)) := by
    dsimp [G]
    apply Real.exp_le_exp.mpr
    nlinarith [nat_sq_ge k]
  have hpoly0 : 0 ≤
      (5 * ((k + 1 : ℕ) : ℝ)) ^ Module.finrank ℝ V := by positivity
  refine hraw.trans ?_
  calc
    ENNReal.ofReal K *
        ((s.card : ℝ≥0∞) *
          (C * ENNReal.ofReal (rho ^ Module.finrank ℝ V))) =
      (ENNReal.ofReal K *
        ENNReal.ofReal (rho ^ Module.finrank ℝ V)) *
          (s.card : ℝ≥0∞) * C := by ac_rfl
    _ = ENNReal.ofReal
        (K * rho ^ Module.finrank ℝ V) *
          (s.card : ℝ≥0∞) * C := by
      rw [ENNReal.ofReal_mul hK0]
    _ = (nearHeatC V * ENNReal.ofReal G) *
          (s.card : ℝ≥0∞) * C := by
      rw [hreal, ENNReal.ofReal_mul (by positivity :
        0 ≤ (Real.sqrt 2) ^ Module.finrank ℝ V *
          (baseHeatMass V)⁻¹)]
      rfl
    _ ≤ (nearHeatC V * ENNReal.ofReal G) *
          ENNReal.ofReal
            ((5 * ((k + 1 : ℕ) : ℝ)) ^ Module.finrank ℝ V) * C := by
      gcongr
    _ = nearHeatC V * C * ENNReal.ofReal
          (((5 * ((k + 1 : ℕ) : ℝ)) ^ Module.finrank ℝ V) * G) := by
      rw [ENNReal.ofReal_mul hpoly0]
      ac_rfl
    _ ≤ nearHeatC V * C * ENNReal.ofReal
          (((5 * ((k + 1 : ℕ) : ℝ)) ^ Module.finrank ℝ V) *
            Real.exp (-(4 : ℝ)⁻¹ * (k : ℝ))) := by
      gcongr
    _ = nearHeatC V * C *
          ENNReal.ofReal (shellWeight (Module.finrank ℝ V) k) := rfl

/-- The actual Bochner heat potential over the full early Duhamel slab. -/
def heatEarly0 (t : ℝ) (f : ℝ × V → F) (x : V) : F :=
  ∫ z in (Set.Ioc 0 (t / 2) ×ˢ (Set.univ : Set V)),
    heatKernel (t - z.1) (x - z.2) • f z
      ∂(stVolume : Measure (ℝ × V))

/-- The unconditional global early `Y⁰ -> C⁰` heat-potential estimate. -/
theorem heatEarly0_norm {T t : ℝ} {C : ℝ≥0∞}
    (ht : 0 < t) (htT : t ≤ T) (f : ℝ × V → F) (x : V)
    (hsrc : SrcCarl T C f) :
    ‖heatEarly0 t f x‖ₑ ≤ earlyHeatC V * C := by
  let q : ℝ × V → ℝ≥0∞ := fun z ↦
    ‖heatKernel (t - z.1) (x - z.2) • f z‖ₑ
  unfold heatEarly0
  calc
    ‖∫ z in (Set.Ioc 0 (t / 2) ×ˢ (Set.univ : Set V)),
        heatKernel (t - z.1) (x - z.2) • f z
          ∂(stVolume : Measure (ℝ × V))‖ₑ ≤
      ∫⁻ z in (Set.Ioc 0 (t / 2) ×ˢ (Set.univ : Set V)), q z
        ∂(stVolume : Measure (ℝ × V)) :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ z in (⋃ k : ℕ, shellCyl t x k), q z
        ∂(stVolume : Measure (ℝ × V)) :=
      lintegral_mono_set (earlySlab_sub ht x)
    _ ≤ ∑' k : ℕ, ∫⁻ z in shellCyl t x k, q z
        ∂(stVolume : Measure (ℝ × V)) :=
      lintegral_iUnion_le _ _
    _ = ∑' k : ℕ, shellMass t f x k := by rfl
    _ ≤ ∑' k : ℕ,
        nearHeatC V * C *
          ENNReal.ofReal (shellWeight (Module.finrank ℝ V) k) := by
      exact ENNReal.tsum_le_tsum (shellMass_le ht htT f x hsrc)
    _ = earlyHeatC V * C := by
      rw [ENNReal.tsum_mul_left]
      unfold earlyHeatC shellSeries
      ac_rfl

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
