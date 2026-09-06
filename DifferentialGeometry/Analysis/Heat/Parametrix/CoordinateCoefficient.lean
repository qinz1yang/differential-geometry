import DifferentialGeometry.Analysis.Integration.RadialIntegralSmoothness
import DifferentialGeometry.Geometry.Operator.LaplacianRegularity

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.HeatEquation

open Geometry.Connection Geometry.Operator
open DifferentialGeometry.Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def heatParametrixCoefficientInCoordinates (g : SmoothRiemannianMetric I M)
    (Φ : E → M) (Ψ : M → E) (J : E → ℝ) : ℕ → M → ℝ
  | 0, q => (Real.sqrt (J (Ψ q)))⁻¹
  | k + 1, q => (Real.sqrt (J (Ψ q)))⁻¹ *
      radialIntegral k (fun v : E => Real.sqrt (J v) *
        laplacian (LeviCivita g) g (heatParametrixCoefficientInCoordinates g Φ Ψ J k) (Φ v)) (Ψ q)

variable [I.Boundaryless] [T2Space M]

theorem contMDiffOn_heatParametrixCoefficientInCoordinates
    (g : SmoothRiemannianMetric I M) {Φ : E → M} {Ψ : M → E} {J : E → ℝ}
    {U : Set E} {V : Set M} (hU : IsOpen U) (hstar : StarConvex ℝ 0 U) (hV : IsOpen V)
    (hΦ : ContMDiffOn 𝓘(ℝ, E) I ∞ Φ U) (hΨ : ContMDiffOn I 𝓘(ℝ, E) ∞ Ψ V)
    (hΦV : MapsTo Φ U V) (hΨU : MapsTo Ψ V U)
    (hJ : ContDiffOn ℝ ∞ J U) (hJpos : ∀ v ∈ U, 0 < J v) (k : ℕ) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (heatParametrixCoefficientInCoordinates g Φ Ψ J k) V := by
  have hsqrt : ContDiffOn ℝ ∞ (fun v => Real.sqrt (J v)) U :=
    hJ.sqrt (fun v hv => (hJpos v hv).ne')
  have hinv : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun q => (Real.sqrt (J (Ψ q)))⁻¹) V :=
    (hsqrt.inv (fun v hv => (Real.sqrt_pos.mpr (hJpos v hv)).ne')).contMDiffOn.comp hΨ hΨU
  induction k with
  | zero => exact hinv
  | succ k ih =>
    have hΔ := contMDiffOn_laplacian_leviCivita g hV ih
    have hin : ContDiffOn ℝ ∞ (fun v => Real.sqrt (J v) *
        laplacian (LeviCivita g) g (heatParametrixCoefficientInCoordinates g Φ Ψ J k) (Φ v)) U :=
      hsqrt.mul (contMDiffOn_iff_contDiffOn.mp (hΔ.comp hΦ hΦV))
    have hrad := contDiffOn_radialIntegral (⊤ : ℕ∞) k hU hstar hin
    exact hinv.mul (hrad.contMDiffOn.comp hΨ hΨU)

end DifferentialGeometry.Analysis.HeatEquation
