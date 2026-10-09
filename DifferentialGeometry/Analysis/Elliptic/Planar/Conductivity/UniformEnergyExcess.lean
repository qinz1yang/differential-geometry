import DifferentialGeometry.Analysis.Asymptotics.CoupledEnergyExcess
import DifferentialGeometry.Analysis.Elliptic.Planar.Conductivity.FrozenExcess
import DifferentialGeometry.Analysis.Elliptic.Planar.Conductivity.PrescribedFrozenReplacement
import DifferentialGeometry.External.DeGiorgi.Localization

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory InnerProductSpace
open scoped ENNReal InnerProductSpace

namespace DifferentialGeometry.Analysis

open DeGiorgi Laplacian.MetricExtension Parabolic.Euclidean

local notation "V" => EuclideanSpace ℝ (Fin 2)

/-- Uniform scale bounds for the literal supplied weak gradients of a family of
solutions. Coefficients may vary with the index, but coercivity, oscillation,
square-root distortion and the full-ball energy bound are common. -/
theorem exists_uniform_weakGrad_energy_excess_bounds
    {ι : Type*} {R lam L M N M₀ : ℝ} (hR : 0 < R)
    (A : ι → DeGiorgi.EllipticCoeff 2 (Metric.ball (0 : V) R))
    (hlam : 0 < lam) (hAlam : ∀ i, (A i).lam = lam)
    (u : ι → V → ℝ)
    (hu : ∀ i, DeGiorgi.IsHomogeneousWeakSolution (A i) (u i))
    (w : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (Metric.ball (0 : V) R))
    (hL : 0 ≤ L) (hM : 1 ≤ M) (hN : 1 ≤ N) (hM₀ : 0 ≤ M₀)
    (hAc : ∀ i, ∀ x ∈ Metric.ball (0 : V) R, ((A i).a x).PosDef)
    (hdet : ∀ i, ∀ x ∈ Metric.ball (0 : V) R, ((A i).a x).det = 1)
    (hcoer : ∀ i, ∀ x ∈ Metric.ball (0 : V) R, ∀ ξ : V,
      lam * ‖ξ‖ ^ 2 ≤ ⟪ξ, DeGiorgi.matMulE ((A i).a x) ξ⟫_ℝ)
    (hcoerInv : ∀ i, ∀ x ∈ Metric.ball (0 : V) R, ∀ ξ : V,
      (A i).Λ⁻¹ * ‖ξ‖ ^ 2 ≤ ⟪ξ, DeGiorgi.matMulE (((A i).a x)⁻¹) ξ⟫_ℝ)
    (hosc : ∀ i, ∀ x ∈ Metric.ball (0 : V) R, ∀ y ∈ Metric.ball (0 : V) R,
      ∀ ξ : V, ‖DeGiorgi.matMulE ((A i).a x) ξ - DeGiorgi.matMulE ((A i).a y) ξ‖ ≤
        L * dist x y * ‖ξ‖)
    (hMbound : ∀ i x (hx : x ∈ Metric.ball (0 : V) R),
      ‖(spdSqrtEquiv ((A i).a x) (hAc i x hx) : V →L[ℝ] V)‖ ≤ M)
    (hNbound : ∀ i x (hx : x ∈ Metric.ball (0 : V) R),
      ‖((spdSqrtEquiv ((A i).a x) (hAc i x hx)).symm : V →L[ℝ] V)‖ ≤ N)
    (henergy : ∀ i, (∫ x in Metric.ball (0 : V) R, ‖(w i).weakGrad x‖ ^ 2) ≤ M₀) :
    ∃ E K : ℝ, 0 ≤ E ∧ 0 ≤ K ∧
      ∀ i, ∀ c ∈ Metric.ball (0 : V) (R / 4), ∀ r ∈ Set.Ioc (0 : ℝ) (R / 4),
        (∫ x in Metric.ball c r, ‖(w i).weakGrad x‖ ^ 2) ≤ E * r ∧
        (∫ x in Metric.ball c r,
          ‖(w i).weakGrad x - ⨍ y in Metric.ball c r, (w i).weakGrad y‖ ^ 2) ≤ K * r ^ 3 := by
  let σ : ℝ := R / 4
  have hσ : 0 < σ := by dsimp only [σ]; positivity
  have hσR : σ ≤ R := by dsimp only [σ]; linarith
  have hclosed (c : V) (hc : c ∈ Metric.ball (0 : V) σ)
      {r : ℝ} (hr : r ≤ σ) : Metric.closedBall c r ⊆ Metric.ball (0 : V) R := by
    intro x hx
    have hc' := Metric.mem_ball.mp hc
    have hx' := Metric.mem_closedBall.mp hx
    have ht := dist_triangle x c (0 : V)
    apply Metric.mem_ball.mpr
    dsimp only [σ] at hc' hr
    linarith
  let J := ι × {c : V // c ∈ Metric.ball (0 : V) σ}
  let En : J → ℝ → ℝ := fun j r =>
    ∫ x in Metric.ball j.2.1 r, ‖(w j.1).weakGrad x‖ ^ 2
  let Ex : J → ℝ → ℝ := fun j r =>
    ∫ x in Metric.ball j.2.1 r,
      ‖(w j.1).weakGrad x - ⨍ y in Metric.ball j.2.1 r, (w j.1).weakGrad y‖ ^ 2
  have hgrad (j : J) {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) σ) :
      MemLp (w j.1).weakGrad 2 (volume.restrict (Metric.ball j.2.1 r)) :=
    (w j.1).weakGrad_memLp.mono_measure (Measure.restrict_mono_set volume
      (Metric.ball_subset_closedBall.trans (hclosed j.2.1 j.2.2 hr.2)))
  have hEn0 (j : J) (r : ℝ) : 0 ≤ En j r :=
    integral_nonneg fun _ => sq_nonneg _
  have hEx0 (j : J) (r : ℝ) : 0 ≤ Ex j r :=
    integral_nonneg fun _ => sq_nonneg _
  have hEnmono (j : J) : MonotoneOn (En j) (Ioc (0 : ℝ) σ) := by
    intro r _ s hs hrs
    exact setIntegral_mono_set (hgrad j hs).norm.integrable_sq
      (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall (Metric.ball_subset_ball hrs))
  have hExmono (j : J) : MonotoneOn (Ex j) (Ioc (0 : ℝ) σ) := by
    let : IsFiniteMeasure (volume.restrict (Metric.ball j.2.1 σ)) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    exact monotoneOn_integral_norm_sub_average_sq_ball (hgrad j ⟨hσ, le_rfl⟩)
  have hEnM (j : J) : En j σ ≤ M₀ := by
    apply le_trans ?_ (henergy j.1)
    exact setIntegral_mono_set (w j.1).weakGrad_memLp.norm.integrable_sq
      (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall
        (Metric.ball_subset_closedBall.trans (hclosed j.2.1 j.2.2 le_rfl)))
  have hExM (j : J) : Ex j σ ≤ M₀ := by
    let : IsFiniteMeasure (volume.restrict (Metric.ball j.2.1 σ)) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    have hh : Ex j σ ≤ En j σ := by
      simpa only [sub_zero] using
        integral_norm_sub_average_sq_le_integral_norm_sub_sq (hgrad j ⟨hσ, le_rfl⟩) (0 : V)
    exact hh.trans (hEnM j)
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hMN : 1 ≤ M * N := by
    simpa only [one_mul] using mul_le_mul hM hN zero_le_one hM0
  have hden : 0 < 8 * M * N := by nlinarith
  let η : ℝ := 1 / (8 * M * N)
  have hη : 0 < η := one_div_pos.mpr hden
  have hη1 : η ≤ 1 := by
    apply (div_le_one hden).2
    nlinarith
  let CE : ℝ := 256 * (M * N) ^ 4
  let CX : ℝ := 16384 * (M * N) ^ 6
  let D : ℝ := (2 + CE + CX) * (L / lam) ^ 2
  have hCE : 0 ≤ CE := by dsimp only [CE]; positivity
  have hCX : 0 ≤ CX := by dsimp only [CX]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hrec (j : J) (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) σ)
      (s : ℝ) (hs : 0 < s) (hsη : s ≤ η * r) :
      En j s ≤ CE * (s / r) ^ 2 * En j r + D * r ^ 2 * En j r ∧
      Ex j s ≤ CX * (s / r) ^ 4 * Ex j r + D * r ^ 2 * En j r := by
    let i := j.1
    let c := j.2.1
    have hc : c ∈ Metric.ball (0 : V) R := Metric.ball_subset_ball hσR j.2.2
    have hsub := hclosed j.2.1 j.2.2 hr.2
    let Ar : EllipticCoeff 2 (Metric.ball c r) :=
      (A i).restrict (Metric.ball_subset_closedBall.trans hsub)
    let wr : MemW1pWitness 2 (u i) (Metric.ball c r) :=
      (w i).restrict Metric.isOpen_ball (Metric.ball_subset_closedBall.trans hsub)
    have hur : IsHomogeneousWeakSolution Ar (u i) :=
      ((isHomogeneousWeakSolution_isSolution (hu i)).restrict_ball
        Metric.isOpen_ball hr.1 hsub).isHomogeneousWeakSolution Metric.isOpen_ball
    have hlamΛ : lam ≤ (A i).Λ := by rw [← hAlam i]; exact (A i).hΛ
    let Bc : EllipticCoeff 2 (Metric.ball c r) := ellipticCoeffOfPointwiseBounds
      Metric.isOpen_ball.measurableSet (fun _ => (A i).a c) lam (A i).Λ hlam hlamΛ
      (fun _ _ => measurable_const) (fun _ _ => hcoer i c hc)
      (fun _ _ => hcoerInv i c hc)
    have hBc : Bc.a = (fun _ => Ar.a c) := rfl
    have hoscBall : ∀ᵐ x ∂volume.restrict (Metric.ball c r), ∀ ξ : V,
        ‖matMulE (Ar.a x) ξ - matMulE (Ar.a c) ξ‖ ≤ (L * r) * ‖ξ‖ := by
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
      intro ξ
      have hxr := (Metric.mem_ball.mp hx).le
      calc
        _ ≤ L * dist x c * ‖ξ‖ :=
          hosc i x ((Metric.ball_subset_closedBall.trans hsub) hx) c hc ξ
        _ ≤ (L * r) * ‖ξ‖ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hxr hL) (norm_nonneg ξ)
    have hε : 0 ≤ L * r := mul_nonneg hL hr.1.le
    obtain ⟨h, wh, v, hh, htrace, _, _, _, hgradv, _, hharm⟩ :=
      exists_prescribed_frozen_harmonic_replacement_with_gradient_comparison
        (by norm_num) Ar Bc (hAc i c hc) hBc hur wr hε hoscBall
    have hsR : s ≤ r / (8 * M * N) := by
      calc
        s ≤ η * r := hsη
        _ = r / (8 * M * N) := by dsimp only [η]; ring
    have hraw := weakGrad_energy_and_excess_le_of_frozen_replacement hr.1 hs
      Ar Bc hBc (hAc i c hc) (hdet i c hc) hM hN
      (hMbound i c hc) (hNbound i c hc) hsR hur hh htrace wr wh hgradv hharm hε hoscBall
    change
      En j s ≤ (CE * (s / r) ^ 2 +
        (2 + CE * (s / r) ^ 2) * (L * r / lam) ^ 2) * En j r ∧
      Ex j s ≤ CX * (s / r) ^ 4 * Ex j r +
        (2 + CX * (s / r) ^ 4) * (L * r / lam) ^ 2 * En j r at hraw
    have hsr : s ≤ r := hsη.trans (mul_le_of_le_one_left hr.1.le hη1)
    have hratio0 : 0 ≤ s / r := div_nonneg hs.le hr.1.le
    have hratio1 : s / r ≤ 1 := (div_le_one hr.1).2 hsr
    have hpow2 : (s / r) ^ 2 ≤ 1 := pow_le_one₀ hratio0 hratio1
    have hpow4 : (s / r) ^ 4 ≤ 1 := pow_le_one₀ hratio0 hratio1
    have hEcoef : 2 + CE * (s / r) ^ 2 ≤ 2 + CE + CX := by
      have ht := mul_le_mul_of_nonneg_left hpow2 hCE
      nlinarith
    have hXcoef : 2 + CX * (s / r) ^ 4 ≤ 2 + CE + CX := by
      have ht := mul_le_mul_of_nonneg_left hpow4 hCX
      nlinarith
    have heps : (L * r / lam) ^ 2 = (L / lam) ^ 2 * r ^ 2 := by ring
    constructor
    · calc
        En j s ≤ (CE * (s / r) ^ 2 +
            (2 + CE * (s / r) ^ 2) * (L * r / lam) ^ 2) * En j r := hraw.1
        _ = CE * (s / r) ^ 2 * En j r +
            (2 + CE * (s / r) ^ 2) * (L * r / lam) ^ 2 * En j r := by ring
        _ ≤ CE * (s / r) ^ 2 * En j r +
            (2 + CE + CX) * (L * r / lam) ^ 2 * En j r :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hEcoef (sq_nonneg _)) (hEn0 j r))
        _ = CE * (s / r) ^ 2 * En j r + D * r ^ 2 * En j r := by
          rw [heps]
          dsimp only [D]
          ring
    · calc
        Ex j s ≤ CX * (s / r) ^ 4 * Ex j r +
            (2 + CX * (s / r) ^ 4) * (L * r / lam) ^ 2 * En j r := hraw.2
        _ ≤ CX * (s / r) ^ 4 * Ex j r +
            (2 + CE + CX) * (L * r / lam) ^ 2 * En j r :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hXcoef (sq_nonneg _)) (hEn0 j r))
        _ = CX * (s / r) ^ 4 * Ex j r + D * r ^ 2 * En j r := by
          rw [heps]
          dsimp only [D]
          ring
  obtain ⟨E, K, hE, hK, hbound⟩ := exists_uniform_linear_energy_cubic_excess_bounds
    En Ex hσ hη hCE hCX hD hM₀ hEnmono hExmono
    (fun j => ⟨hEn0 j σ, hEnM j⟩) (fun j => ⟨hEx0 j σ, hExM j⟩)
    (fun j r hr s hs hsη => (hrec j r hr s hs hsη).1)
    (fun j r hr s hs hsη => (hrec j r hr s hs hsη).2)
  refine ⟨E, K, hE, hK, ?_⟩
  intro i c hc r hr
  exact hbound (i, ⟨c, hc⟩) r hr

end DifferentialGeometry.Analysis
