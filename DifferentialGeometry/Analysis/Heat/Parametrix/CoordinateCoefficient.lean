import DifferentialGeometry.Analysis.Integration.RadialIntegralSmoothness
import DifferentialGeometry.Analysis.Integration.RadialIntegralParameter
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

namespace DifferentialGeometry.Analysis.HeatEquation

open DifferentialGeometry.Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]

private theorem contMDiffOn_sqrt_joint
    {S : Set P} {U : Set E} {J : P → E → ℝ}
    (hJ : ContMDiffOn (IP.prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry J) (S ×ˢ U))
    (hJpos : ∀ z ∈ S ×ˢ U, 0 < J z.1 z.2) :
    ContMDiffOn (IP.prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      (fun z : P × E => Real.sqrt (J z.1 z.2)) (S ×ˢ U) := by
  intro z hz
  have hsqrt : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Real.sqrt (J z.1 z.2) :=
    (Real.contDiffAt_sqrt (hJpos z hz).ne').contMDiffAt
  exact hsqrt.comp_contMDiffWithinAt z (hJ z hz)

variable [IsManifold I ∞ M] [I.Boundaryless]
  [IsManifold IP ∞ P] [IP.Boundaryless]

omit [IsManifold I ∞ M] [I.Boundaryless] in
private theorem contMDiffOn_weighted_radial_integral_comp
    {Φ : P → E → M} {Ψ : P → M → E} {J : P → E → ℝ} {F : P → M → ℝ}
    {S : Set P} {U : Set E} {D : Set (P × M)}
    (hS : IsOpen S) (hU : IsOpen U) (hstar : StarConvex ℝ 0 U)
    (hΦ : ContMDiffOn (IP.prod 𝓘(ℝ, E)) I ∞ (Function.uncurry Φ) (S ×ˢ U))
    (hΨ : ContMDiffOn (IP.prod I) 𝓘(ℝ, E) ∞ (Function.uncurry Ψ) D)
    (hJ : ContMDiffOn (IP.prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry J) (S ×ˢ U))
    (hJpos : ∀ z ∈ S ×ˢ U, 0 < J z.1 z.2)
    (hΦD : MapsTo (fun z : P × E => (z.1, Φ z.1 z.2)) (S ×ˢ U) D)
    (hΨU : MapsTo (fun z : P × M => (z.1, Ψ z.1 z.2)) D (S ×ˢ U))
    (k : ℕ)
    (hF : ContMDiffOn (IP.prod I) 𝓘(ℝ, ℝ) ∞ (Function.uncurry F) D) :
    ContMDiffOn (IP.prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : P × M => (Real.sqrt (J z.1 (Ψ z.1 z.2)))⁻¹ *
        radialIntegral k (fun v => Real.sqrt (J z.1 v) * F z.1 (Φ z.1 v)) (Ψ z.1 z.2)) D := by
  have hsqrt := contMDiffOn_sqrt_joint hJ hJpos
  have hA : ContMDiffOn (IP.prod 𝓘(ℝ, E)) (IP.prod I) ∞
      (fun z : P × E => (z.1, Φ z.1 z.2)) (S ×ˢ U) :=
    contMDiffOn_fst.prodMk hΦ
  have hFA : ContMDiffOn (IP.prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      (fun z : P × E => F z.1 (Φ z.1 z.2)) (S ×ˢ U) := hF.comp hA hΦD
  let f : P → E → ℝ := fun p v => Real.sqrt (J p v) * F p (Φ p v)
  have hf : ContMDiffOn (IP.prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry f) (S ×ˢ U) :=
    hsqrt.mul hFA
  have hrad : ContMDiffOn (IP.prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      (fun z : P × E => radialIntegral k (f z.1) z.2) (S ×ˢ U) :=
    contMDiffOn_radialIntegral_joint (IP := IP) (⊤ : ℕ∞) k hS hU hstar hf
  have hB : ContMDiffOn (IP.prod I) (IP.prod 𝓘(ℝ, E)) ∞
      (fun z : P × M => (z.1, Ψ z.1 z.2)) D :=
    contMDiffOn_fst.prodMk hΨ
  have hInv : ContMDiffOn (IP.prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      (fun z : P × E => (Real.sqrt (J z.1 z.2))⁻¹) (S ×ˢ U) :=
    hsqrt.inv₀ (fun z hz => (Real.sqrt_pos.mpr (hJpos z hz)).ne')
  have hinvB : ContMDiffOn (IP.prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : P × M => (Real.sqrt (J z.1 (Ψ z.1 z.2)))⁻¹) D := hInv.comp hB hΨU
  have hradB : ContMDiffOn (IP.prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : P × M => radialIntegral k (f z.1) (Ψ z.1 z.2)) D := hrad.comp hB hΨU
  exact hinvB.mul hradB

omit [I.Boundaryless] in
private theorem contMDiffOn_coefficient_succ_engine
    [FiniteDimensional ℝ E]
    (g : SmoothRiemannianMetric I M)
    {Φ : P → E → M} {Ψ : P → M → E} {J : P → E → ℝ}
    {S : Set P} {U : Set E} {D : Set (P × M)}
    (hS : IsOpen S) (hU : IsOpen U) (hstar : StarConvex ℝ 0 U)
    (hΦ : ContMDiffOn (IP.prod 𝓘(ℝ, E)) I ∞ (Function.uncurry Φ) (S ×ˢ U))
    (hΨ : ContMDiffOn (IP.prod I) 𝓘(ℝ, E) ∞ (Function.uncurry Ψ) D)
    (hJ : ContMDiffOn (IP.prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry J) (S ×ˢ U))
    (hJpos : ∀ z ∈ S ×ˢ U, 0 < J z.1 z.2)
    (hΦD : MapsTo (fun z : P × E => (z.1, Φ z.1 z.2)) (S ×ˢ U) D)
    (hΨU : MapsTo (fun z : P × M => (z.1, Ψ z.1 z.2)) D (S ×ˢ U))
    (k : ℕ)
    (hDelta : ContMDiffOn (IP.prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : P × M => Geometry.Operator.laplacian (Geometry.Connection.LeviCivita g) g
        (heatParametrixCoefficientInCoordinates g (Φ z.1) (Ψ z.1) (J z.1) k) z.2) D) :
    ContMDiffOn (IP.prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : P × M => heatParametrixCoefficientInCoordinates g
        (Φ z.1) (Ψ z.1) (J z.1) (k + 1) z.2) D :=
  contMDiffOn_weighted_radial_integral_comp
    (F := fun p q => Geometry.Operator.laplacian (Geometry.Connection.LeviCivita g) g
      (heatParametrixCoefficientInCoordinates g (Φ p) (Ψ p) (J p) k) q)
    hS hU hstar hΦ hΨ hJ hJpos hΦD hΨU k hDelta

theorem contMDiffOn_heatParametrixCoefficientInCoordinates_prod
    [FiniteDimensional ℝ E] [T2Space M] [FiniteDimensional ℝ EP] [T2Space P]
    (g : SmoothRiemannianMetric I M)
    {Φ : P → E → M} {Ψ : P → M → E} {J : P → E → ℝ}
    {S : Set P} {U : Set E} {D : Set (P × M)}
    (hD : IsOpen D) (hS : IsOpen S) (hU : IsOpen U) (hstar : StarConvex ℝ 0 U)
    (hΦ : ContMDiffOn (IP.prod 𝓘(ℝ, E)) I ∞ (Function.uncurry Φ) (S ×ˢ U))
    (hΨ : ContMDiffOn (IP.prod I) 𝓘(ℝ, E) ∞ (Function.uncurry Ψ) D)
    (hJ : ContMDiffOn (IP.prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry J) (S ×ˢ U))
    (hJpos : ∀ z ∈ S ×ˢ U, 0 < J z.1 z.2)
    (hΦD : MapsTo (fun z : P × E => (z.1, Φ z.1 z.2)) (S ×ˢ U) D)
    (hΨU : MapsTo (fun z : P × M => (z.1, Ψ z.1 z.2)) D (S ×ˢ U))
    (k : ℕ) :
    ContMDiffOn (IP.prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : P × M => heatParametrixCoefficientInCoordinates g
        (Φ z.1) (Ψ z.1) (J z.1) k z.2) D := by
  induction k with
  | zero =>
    have hsqrt := contMDiffOn_sqrt_joint hJ hJpos
    have hInv : ContMDiffOn (IP.prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
        (fun z : P × E => (Real.sqrt (J z.1 z.2))⁻¹) (S ×ˢ U) :=
      hsqrt.inv₀ (fun z hz => (Real.sqrt_pos.mpr (hJpos z hz)).ne')
    exact hInv.comp (contMDiffOn_fst.prodMk hΨ) hΨU
  | succ k ih =>
    let a : P → M → ℝ := fun p => heatParametrixCoefficientInCoordinates g (Φ p) (Ψ p) (J p) k
    have ha : ContMDiffOn (IP.prod I) 𝓘(ℝ, ℝ) ∞ (Function.uncurry a) D := ih
    have hDelta : ContMDiffOn (IP.prod I) 𝓘(ℝ, ℝ) ∞
        (fun z : P × M => Geometry.Operator.laplacian (Geometry.Connection.LeviCivita g) g
          (a z.1) z.2) D :=
      Geometry.Operator.contMDiffOn_laplacian_leviCivita_prod_of_isOpen
        (IP := IP) (I := I) (f := a) g hD ha
    exact contMDiffOn_coefficient_succ_engine g hS hU hstar hΦ hΨ hJ hJpos hΦD hΨU k hDelta

end DifferentialGeometry.Analysis.HeatEquation
