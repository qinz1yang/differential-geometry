import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientGauge
import DifferentialGeometry.Analysis.Complex.FirstOrderSystems.UnitGauge
import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientZero
import DifferentialGeometry.Analysis.Complex.CauchyTransform.PointwiseEquation
import Mathlib.Analysis.Calculus.FDeriv.Prod

set_option autoImplicit false
noncomputable section

open Set Metric Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry
open scoped ContDiff Manifold Topology NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The single integral gauge constructed from an original Morrey disk yields an
analytic factor of its original chart gradient, with the same differential zero set. -/
theorem IsMorreyDisk.exists_analytic_complex_gradient_gauge
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u)
    {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) :
    ∃ (R : ℝ) (hR : 0 < R),
      closedBall a (2 * R) ⊆ ball (0 : ℂ) 1 ∧
      (∀ z ∈ closedBall a (2 * R),
        diskExtension u z ∈ (chartAt E (diskExtension u a)).source) ∧
      ∃ A_R : C(closedBall a R,
          (Fin (Module.finrank ℝ E) → ℂ) →L[ℂ]
            (Fin (Module.finrank ℝ E) → ℂ)),
        (∀ z : closedBall a R,
          A_R z = chartComplexGradientOperator g
            (diskExtension u a) (diskExtension u) (z : ℂ)) ∧
        4 * R * ‖A_R‖ < (1 / 4 : ℝ) ∧
        ∃ P : C(closedBall a R,
            (Fin (Module.finrank ℝ E) → ℂ) →L[ℂ]
              (Fin (Module.finrank ℝ E) → ℂ)),
          P = 1 + DifferentialGeometry.Analysis.diskCauchyTransform
            a R hR (A_R * P) ∧
          ‖P - 1‖ ≤ (4 * R * ‖A_R‖) / (1 - 4 * R * ‖A_R‖) ∧
          ‖P‖ ≤ 2 ∧
          (∀ z : closedBall a R, IsUnit (P z)) ∧
          (∀ z w : closedBall a R,
            ‖P z - P w‖ ≤
              16 * Real.sqrt R * ‖A_R * P‖ *
                Real.sqrt ‖(z : ℂ) - (w : ℂ)‖) ∧
          (∃ H : ℝ≥0,
            HolderWith H (1 / 2 : ℝ≥0)
              (fun z : closedBall a R => A_R z * P z)) ∧
          (let P₀ : ℂ →
              ((Fin (Module.finrank ℝ E) → ℂ) →L[ℂ]
                (Fin (Module.finrank ℝ E) → ℂ)) := fun z =>
            1 + (Real.pi : ℂ)⁻¹ •
              ∫ w : closedBall a R,
                (z - (w : ℂ))⁻¹ • (A_R w * P w)
                ∂(volume.comap ((↑) : closedBall a R → ℂ))
           let A : ℂ →
               ((Fin (Module.finrank ℝ E) → ℂ) →L[ℂ]
                 (Fin (Module.finrank ℝ E) → ℂ)) :=
             chartComplexGradientOperator g (diskExtension u a) (diskExtension u)
           let ξ : ℂ → (Fin (Module.finrank ℝ E) → ℂ) := fun q k =>
             chartComplexGradient (diskExtension u a) (diskExtension u) k q
           let F : ℂ → (Fin (Module.finrank ℝ E) → ℂ) := fun q =>
             (Ring.inverse (P₀ q) :
               (Fin (Module.finrank ℝ E) → ℂ) →L[ℂ]
                 (Fin (Module.finrank ℝ E) → ℂ)) (ξ q)
           (∀ z : closedBall a R, P₀ (z : ℂ) = P z) ∧
           (∀ z ∈ closedBall a R, IsUnit (P₀ z)) ∧
           ContDiffOn ℝ 1 P₀ (ball a R) ∧
           ContDiffOn ℝ ∞ ξ (ball a R) ∧
           (∀ q ∈ ball a R,
             (1 / 2 : ℂ) •
               (fderiv ℝ P₀ q (1 : ℂ) + Complex.I • fderiv ℝ P₀ q Complex.I) =
                 A q * P₀ q) ∧
           (∀ q ∈ ball a R,
             (1 / 2 : ℂ) •
               (fderiv ℝ ξ q (1 : ℂ) + Complex.I • fderiv ℝ ξ q Complex.I) =
                 A q (ξ q)) ∧
           AnalyticOnNhd ℂ F (ball a R) ∧
           (∀ q ∈ ball a R, ξ q = P₀ q (F q)) ∧
           (∀ q ∈ ball a R, F q = 0 ↔ ξ q = 0) ∧
           (∀ q ∈ ball a R,
             F q = 0 ↔ mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) q = 0)) := by
  obtain ⟨R, hR, hbuffer, hsrc, A_R, hA_R, hsmall, P, hP, hnear, hbound,
      hunit, hmodulus, hholder, hP₀⟩ :=
    hu.exists_small_ball_complex_gradient_gauge ha
  let U := diskExtension u
  let p := U a
  let V := Fin (Module.finrank ℝ E) → ℂ
  let A : ℂ → V →L[ℂ] V := chartComplexGradientOperator g p U
  let ξ : ℂ → V := fun q k => chartComplexGradient p U k q
  let f : C(closedBall a R, V →L[ℂ] V) := A_R * P
  let P₀ : ℂ → V →L[ℂ] V := fun z =>
    1 + (Real.pi : ℂ)⁻¹ •
      ∫ w : closedBall a R,
        (z - (w : ℂ))⁻¹ • (A_R w * P w)
        ∂(volume.comap ((↑) : closedBall a R → ℂ))
  change (∀ z : closedBall a R, P₀ (z : ℂ) = P z) ∧
    (∀ z ∈ closedBall a R, IsUnit (P₀ z)) at hP₀
  have hballbuffer : ball a R ⊆ closedBall a (2 * R) :=
    ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith : R ≤ 2 * R))
  have hinside : ball a R ⊆ ball (0 : ℂ) 1 := hballbuffer.trans hbuffer
  have hchart : ∀ q ∈ ball a R, U q ∈ (chartAt E p).source :=
    fun q hq => hsrc q (hballbuffer hq)
  obtain ⟨H, hH⟩ := hholder
  have hlocal : ∀ q ∈ ball a R, ∃ ε : ℝ, 0 < ε ∧ ∃ α K : ℝ≥0,
      closedBall q ε ⊆ ball a R ∧ 0 < α ∧ α ≤ 1 ∧
        HolderOnWith K α f {w : closedBall a R | (w : ℂ) ∈ closedBall q ε} := by
    intro q hq
    obtain ⟨ε, hε, hεball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
      (isOpen_ball.mem_nhds hq)
    refine ⟨ε, hε, (1 / 2 : ℝ≥0), H, hεball, by norm_num, by norm_num, ?_⟩
    exact hH.holderOnWith _
  obtain ⟨hT, hTdbar⟩ :=
    DifferentialGeometry.Analysis.contDiffOn_and_dbar_ambientCauchyIntegral_of_locally_holder
      f isOpen_ball (Subset.rfl) hlocal
  have hP₀reg : ContDiffOn ℝ 1 P₀ (ball a R) :=
    (contDiffOn_const (c := (1 : V →L[ℂ] V))).add hT
  have hD (q : ℂ) : fderiv ℝ P₀ q =
      fderiv ℝ (DifferentialGeometry.Analysis.ambientCauchyIntegral f) q := by
    change fderiv ℝ
      (fun z => (1 : V →L[ℂ] V) +
        DifferentialGeometry.Analysis.ambientCauchyIntegral f z) q = _
    exact fderiv_const_add 1
  have hhalf (B : V →L[ℂ] V) : (1 / 2 : ℂ) • B = (1 / 2 : ℝ) • B := by
    rw [show (1 / 2 : ℂ) = algebraMap ℝ ℂ (1 / 2 : ℝ) by norm_num,
      algebraMap_smul]
  have hPDE : ∀ q ∈ ball a R,
      (1 / 2 : ℂ) •
        (fderiv ℝ P₀ q (1 : ℂ) + Complex.I • fderiv ℝ P₀ q Complex.I) =
          A q * P₀ q := by
    intro q hq
    calc
      (1 / 2 : ℂ) •
          (fderiv ℝ P₀ q (1 : ℂ) + Complex.I • fderiv ℝ P₀ q Complex.I) =
          (1 / 2 : ℝ) •
            (fderiv ℝ (DifferentialGeometry.Analysis.ambientCauchyIntegral f)
                q (1 : ℂ) +
              Complex.I • fderiv ℝ
                (DifferentialGeometry.Analysis.ambientCauchyIntegral f) q Complex.I) := by
        rw [hD q, hhalf]
      _ = f ⟨q, ball_subset_closedBall hq⟩ := hTdbar q hq
      _ = A q * P₀ q := by
        change A_R ⟨q, ball_subset_closedBall hq⟩ * P ⟨q, ball_subset_closedBall hq⟩ = _
        rw [hA_R, ← hP₀.1 ⟨q, ball_subset_closedBall hq⟩]
  let X : ℂ → E := extChartAt 𝓘(ℝ, E) p ∘ U
  have hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U (ball a R) :=
    hu.smoothInterior.mono hinside
  have hX : ContDiffOn ℝ ∞ X (ball a R) := by
    intro q hq
    exact (((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞)
      (hchart q hq)).comp q (hU.contMDiffAt (isOpen_ball.mem_nhds hq))).contDiffAt).contDiffWithinAt
  have hξ : ContDiffOn ℝ ∞ ξ (ball a R) := by
    apply contDiffOn_pi.mpr
    intro k
    let xk : ℂ → ℝ := fun q =>
      DifferentialGeometry.Tensor.Coordinates.chartCoordCLM E k (X q)
    have hxk : ContDiffOn ℝ ∞ xk (ball a R) :=
      (DifferentialGeometry.Tensor.Coordinates.chartCoordCLM E k).contDiff.comp_contDiffOn hX
    have hd := hxk.fderiv_of_isOpen (m := ∞) isOpen_ball (by simp)
    have hd1 := hd.clm_apply (contDiffOn_const (c := (1 : ℂ)))
    have hdI := hd.clm_apply (contDiffOn_const (c := Complex.I))
    have hp := (hd1.mul (contDiffOn_const (c := (2 : ℝ)⁻¹))).prodMk
      (hdI.neg.mul (contDiffOn_const (c := (2 : ℝ)⁻¹)))
    refine (Complex.equivRealProdCLM.symm.contDiff.comp_contDiffOn hp).congr ?_
    intro q _
    change (⟨fderiv ℝ xk q 1 / 2, -fderiv ℝ xk q Complex.I / 2⟩ : ℂ) =
      Complex.equivRealProdCLM.symm
        (fderiv ℝ xk q 1 * (2 : ℝ)⁻¹, -fderiv ℝ xk q Complex.I * (2 : ℝ)⁻¹)
    apply Complex.ext <;> simp [Complex.equivRealProdCLM_symm_apply, div_eq_mul_inv]
  have hξDE : ∀ q ∈ ball a R,
      (1 / 2 : ℂ) •
        (fderiv ℝ ξ q (1 : ℂ) + Complex.I • fderiv ℝ ξ q Complex.I) =
          A q (ξ q) := by
    intro q hq
    have hξd : DifferentiableAt ℝ ξ q :=
      (hξ.contDiffAt (isOpen_ball.mem_nhds hq)).differentiableAt (by simp)
    funext k
    have hcomponent (v : ℂ) :
        fderiv ℝ (chartComplexGradient p U k) q v = (fderiv ℝ ξ q v) k := by
      exact congrArg (fun L : ℂ →L[ℝ] ℂ => L v) (fderiv_apply hξd k)
    have hk :
        (fderiv ℝ (chartComplexGradient p U k) q 1 +
          Complex.I * fderiv ℝ (chartComplexGradient p U k) q Complex.I) / 2 =
            ∑ j, chartComplexGradientCoefficient g p U k j q *
              chartComplexGradient p U j q := by
      apply chartComplexGradient_dbar_eq g
        ((hU.contMDiffAt (isOpen_ball.mem_nhds hq)).of_le (by norm_num)) (hchart q hq)
        (k := k)
      change diskMapTension g U q = 0
      exact hu.harmonic q (hinside hq)
    change (1 / 2 : ℂ) *
      ((fderiv ℝ ξ q (1 : ℂ)) k + Complex.I * (fderiv ℝ ξ q Complex.I) k) =
        chartComplexGradientOperator g p U q (ξ q) k
    rw [chartComplexGradientOperator_apply]
    calc
      (1 / 2 : ℂ) *
          ((fderiv ℝ ξ q (1 : ℂ)) k + Complex.I * (fderiv ℝ ξ q Complex.I) k) =
          (fderiv ℝ (chartComplexGradient p U k) q 1 +
            Complex.I * fderiv ℝ (chartComplexGradient p U k) q Complex.I) / 2 := by
        rw [← hcomponent 1, ← hcomponent Complex.I]
        ring
      _ = _ := hk
  obtain ⟨hhol, hfactor, hzero⟩ :=
    DifferentialGeometry.Analysis.analyticOnNhd_inverse_gauge_apply isOpen_ball
      P₀ A ξ hP₀reg (hξ.of_le (by simp))
      (fun q hq => hP₀.2 q (ball_subset_closedBall hq)) hPDE hξDE
  refine ⟨R, hR, hbuffer, hsrc, A_R, hA_R, hsmall, P, hP, hnear, hbound,
    hunit, hmodulus, ⟨H, hH⟩, ?_⟩
  refine ⟨hP₀.1, hP₀.2, hP₀reg, hξ, hPDE, hξDE, hhol, hfactor, hzero, ?_⟩
  intro q hq
  apply (hzero q hq).trans
  have hgradient := hu.chartComplexGradient_eq_zero_iff_mfderiv_eq_zero
    (hinside hq) (hchart q hq)
  constructor
  · intro hξzero
    apply hgradient.mp
    intro k
    exact congrFun hξzero k
  · intro hdzero
    funext k
    exact hgradient.mpr hdzero k

end DifferentialGeometry.Geometry
