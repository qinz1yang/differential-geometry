import DifferentialGeometry.Analysis.Integration.Measure.Gradient
import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensity
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import DifferentialGeometry.Analysis.Sobolev.Manifold.Lipschitz
noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal
namespace DifferentialGeometry.Analysis.Parabolic
open Geometry.Operator Integral.Measure
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem integral_inner_gradFun_sub_const_mul
    (g : SmoothRiemannianMetric I M) (u f h : M → ℝ) (B : ℝ) (μ : Measure M)
    (hf : ∀ᵐ x ∂μ, MDifferentiableAt I 𝓘(ℝ) f x)
    (hh : ∀ᵐ x ∂μ, MDifferentiableAt I 𝓘(ℝ) h x)
    (hfi : Integrable (fun x => g.inner x (gradFun g u x) (gradFun g f x)) μ)
    (hhi : Integrable (fun x => g.inner x (gradFun g u x) (gradFun g h x)) μ) :
    (∫ x, g.inner x (gradFun g u x) (gradFun g (fun y => B * f y - h y) x) ∂μ) =
      B * (∫ x, g.inner x (gradFun g u x) (gradFun g f x) ∂μ) -
        ∫ x, g.inner x (gradFun g u x) (gradFun g h x) ∂μ := by
  have heq : (fun x => g.inner x (gradFun g u x) (gradFun g (fun y => B * f y - h y) x))
      =ᵐ[μ] (fun x => B * g.inner x (gradFun g u x) (gradFun g f x) -
        g.inner x (gradFun g u x) (gradFun g h x)) := by
    filter_upwards [hf, hh] with x hfx hhx
    have hB : MDifferentiableAt I 𝓘(ℝ) (fun y => B * f y) x := mdifferentiableAt_const.mul hfx
    change (g.inner x (gradFun g u x)) (gradientFun g (fun y => B * f y - h y) x) = _
    rw [gradientFun_sub g hB hhx]
    have hgrad : gradientFun g (fun y => B * f y) x = B • gradientFun g f x :=
      gradientFun_const_smul g B hfx
    rw [hgrad, map_sub, map_smul, smul_eq_mul]
    rfl
  rw [integral_congr_ae heq, integral_sub (hfi.const_mul B) hhi, integral_const_mul]

theorem integral_tensor_test_eq_of_exhaustion
    (R : SmoothRiemannianMetric I M) (g : ℝ → SmoothRiemannianMetric I M)
    (u : ℝ → C(M, ℝ)) {J : Set ℝ}
    {ψ : ℝ → ℝ} (hψs : tsupport ψ ⊆ J)
    (hweak : ∀ (η : C(M, ℝ)), HasCompactSupport (η : M → ℝ) → (∀ x, 0 ≤ η x) →
      (∃ C : ℝ≥0, ∀ x y, edist (η x) (η y) ≤ C * riemannianEDistOf R x y) →
      Integrable (fun t => ψ t * ∫ x, (g t).inner x (gradFun (g t) (u t) x) (gradFun (g t) η x)
        ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) volume ∧
      Integrable (fun t => deriv ψ t * ∫ x, u t x * η x
        ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) volume ∧
      (∫ t, ψ t * ∫ x, (g t).inner x (gradFun (g t) (u t) x) (gradFun (g t) η x)
        ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) ≤
        ∫ t, deriv ψ t * ∫ x, u t x * η x
          ∂riemannianVolumeMeasure (I := I) (M := M) (g t))
    (χ : C(M, ℝ)) (hχc : HasCompactSupport (χ : M → ℝ)) (hχ0 : ∀ x, 0 ≤ χ x)
    (hχL : ∃ C : ℝ≥0, ∀ x y, edist (χ x) (χ y) ≤ C * riemannianEDistOf R x y)
    (hχi : ∀ t ∈ J, Integrable (fun x => (g t).inner x
      (gradFun (g t) (u t) x) (gradFun (g t) χ x))
      (riemannianVolumeMeasure (I := I) (M := M) (g t)))
    {ι : Type*} {l : Filter ι} [NeBot l] (ζ : ι → C(M, ℝ))
    (hζc : ∀ i, HasCompactSupport (ζ i : M → ℝ)) (hζ0 : ∀ i x, 0 ≤ ζ i x)
    (hζL : ∀ i, ∃ C : ℝ≥0, ∀ x y, edist (ζ i x) (ζ i y) ≤ C * riemannianEDistOf R x y)
    (hζi : ∀ i, ∀ t ∈ J, Integrable (fun x => (g t).inner x
      (gradFun (g t) (u t) x) (gradFun (g t) (ζ i) x))
      (riemannianVolumeMeasure (I := I) (M := M) (g t)))
    (hζ1 : ∀ᶠ i in l, ∀ x ∈ tsupport (χ : M → ℝ), ζ i x = 1)
    (hlim : Tendsto (fun i =>
      (∫ t, deriv ψ t * ∫ x, u t x * ζ i x
        ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) -
      ∫ t, ψ t * ∫ x, (g t).inner x (gradFun (g t) (u t) x) (gradFun (g t) (ζ i) x)
        ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) l (𝓝 0)) :
    (∫ t, ψ t * ∫ x, (g t).inner x (gradFun (g t) (u t) x) (gradFun (g t) χ x)
      ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) =
      ∫ t, deriv ψ t * ∫ x, u t x * χ x
        ∂riemannianVolumeMeasure (I := I) (M := M) (g t) := by
  let A (η : C(M, ℝ)) (t : ℝ) := ψ t * ∫ x,
    (g t).inner x (gradFun (g t) (u t) x) (gradFun (g t) η x)
      ∂riemannianVolumeMeasure (I := I) (M := M) (g t)
  let B (η : C(M, ℝ)) (t : ℝ) := deriv ψ t * ∫ x, u t x * η x
    ∂riemannianVolumeMeasure (I := I) (M := M) (g t)
  let D (η : C(M, ℝ)) := (∫ t, B η t) - ∫ t, A η t
  have hwχ := hweak χ hχc hχ0 hχL
  have hD0 : 0 ≤ D χ := sub_nonneg.mpr hwχ.2.2
  obtain ⟨K, hK⟩ := hχc.exists_bound_of_continuousOn χ.continuous.continuousOn
  let c : ℝ := max K 0
  have hc0 : 0 ≤ c := le_max_right K 0
  have hbound : ∀ x, χ x ≤ c := by
    intro x
    by_cases hx : x ∈ tsupport (χ : M → ℝ)
    · exact ((le_abs_self _).trans (hK x hx)).trans (le_max_left K 0)
    · rw [image_eq_zero_of_notMem_tsupport hx]
      exact hc0
  have hDle : ∀ᶠ i in l, D χ ≤ c * D (ζ i) := by
    filter_upwards [hζ1] with i hi
    let η : C(M, ℝ) := ⟨fun x => c * ζ i x - χ x,
      (continuous_const.mul (ζ i).continuous).sub χ.continuous⟩
    have hηc : HasCompactSupport (η : M → ℝ) := ((hζc i).mul_left).sub hχc
    have hη0 (x : M) : 0 ≤ η x := by
      change 0 ≤ c * ζ i x - χ x
      by_cases hx : x ∈ tsupport (χ : M → ℝ)
      · rw [hi x hx, mul_one]
        exact sub_nonneg.mpr (hbound x)
      · rw [image_eq_zero_of_notMem_tsupport hx, sub_zero]
        exact mul_nonneg hc0 (hζ0 i x)
    obtain ⟨Cχ, hCχ⟩ := hχL
    obtain ⟨Cζ, hCζ⟩ := hζL i
    have hηL : ∃ C : ℝ≥0, ∀ x y, edist (η x) (η y) ≤ C * riemannianEDistOf R x y := by
      refine ⟨‖c‖₊ * Cζ + Cχ, fun x y => ?_⟩
      change edist (c * ζ i x + -χ x) (c * ζ i y + -χ y) ≤ _
      calc
        _ ≤ edist (c * ζ i x) (c * ζ i y) + edist (-χ x) (-χ y) := edist_add_add_le _ _ _ _
        _ = (‖c‖₊ : ENNReal) * edist (ζ i x) (ζ i y) + edist (χ x) (χ y) := by
          rw [← smul_eq_mul c (ζ i x), ← smul_eq_mul c (ζ i y), edist_smul₀, edist_neg_neg]
          rfl
        _ ≤ (‖c‖₊ : ENNReal) * (Cζ * riemannianEDistOf R x y) + Cχ * riemannianEDistOf R x y :=
          add_le_add (mul_le_mul_right (hCζ x y) _) (hCχ x y)
        _ = _ := by simp only [ENNReal.coe_add, ENNReal.coe_mul, add_mul, mul_assoc]
    have hwζ := hweak (ζ i) (hζc i) (hζ0 i) ⟨Cζ, hCζ⟩
    have hwη := (hweak η hηc hη0 hηL).2.2
    have hAe (t : ℝ) : A η t = c * A (ζ i) t - A χ t := by
      by_cases ht : t ∈ J
      · have hμ : riemannianVolumeMeasure (I := I) (M := M) (g t) ≪
            riemannianVolumeMeasure (I := I) (M := M) R := by
          rw [riemannianVolumeMeasure_eq_withDensity R (g t)]
          exact withDensity_absolutelyContinuous _ _
        have hχd := hμ.ae_le (Sobolev.Chart.ae_mdiff_of_lip R hCχ)
        have hζd := hμ.ae_le (Sobolev.Chart.ae_mdiff_of_lip R hCζ)
        dsimp only [A, η, ContinuousMap.coe_mk]
        rw [integral_inner_gradFun_sub_const_mul (g t) (u t) (ζ i) χ c _ hζd hχd (hζi i t ht) (hχi t ht)]
        ring
      · have hz : ψ t = 0 := image_eq_zero_of_notMem_tsupport (fun h => ht (hψs h))
        simp only [A, hz, zero_mul, mul_zero, sub_zero]
    have hBe (t : ℝ) : B η t = c * B (ζ i) t - B χ t := by
      let _ := riemannianVolumeMeasure_isFiniteMeasureOnCompacts (g t)
      have hci : Integrable (fun x => u t x * χ x)
          (riemannianVolumeMeasure (I := I) (M := M) (g t)) := ((u t).continuous.mul χ.continuous).integrable_of_hasCompactSupport hχc.mul_left
      have hzi : Integrable (fun x => u t x * ζ i x)
          (riemannianVolumeMeasure (I := I) (M := M) (g t)) := ((u t).continuous.mul (ζ i).continuous).integrable_of_hasCompactSupport (hζc i).mul_left
      dsimp only [B, η, ContinuousMap.coe_mk]
      have heq : (fun x => u t x * (c * ζ i x - χ x)) =
          (fun x => c * (u t x * ζ i x) - u t x * χ x) := by funext x; ring
      rw [heq, integral_sub (hzi.const_mul c) hci, integral_const_mul]
      ring
    have hDA : (∫ t, A η t) = c * (∫ t, A (ζ i) t) - ∫ t, A χ t := by
      rw [integral_congr_ae (.of_forall hAe), integral_sub (hwζ.1.const_mul c) hwχ.1, integral_const_mul]
    have hDB : (∫ t, B η t) = c * (∫ t, B (ζ i) t) - ∫ t, B χ t := by
      rw [integral_congr_ae (.of_forall hBe), integral_sub (hwζ.2.1.const_mul c) hwχ.2.1, integral_const_mul]
    change (∫ t, A η t) ≤ ∫ t, B η t at hwη
    rw [hDA, hDB] at hwη
    dsimp only [D]
    linarith
  have hDc : D χ ≤ 0 := by
    have ht : Tendsto (fun i => c * D (ζ i)) l (𝓝 0) := by
      simpa only [mul_zero] using hlim.const_mul c
    exact ge_of_tendsto ht hDle
  exact sub_eq_zero.mp (le_antisymm hDc hD0) |>.symm

end DifferentialGeometry.Analysis.Parabolic
