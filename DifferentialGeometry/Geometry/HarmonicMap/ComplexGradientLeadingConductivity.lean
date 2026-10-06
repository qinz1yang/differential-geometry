import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientLeadingPlane
import DifferentialGeometry.Analysis.Elliptic.Planar.Conductivity.Coefficients

set_option autoImplicit false

noncomputable section

open Set Manifold Bundle DifferentialGeometry
open DifferentialGeometry.Tensor.Coordinates
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry

private theorem isotropicSlopeConductivity_zero {κ : ℝ} (hκ : 0 < κ) :
    Analysis.planarConductivity κ κ 0 = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hs : Real.sqrt (κ * κ) = κ := by
    simpa only [pow_two] using Real.sqrt_sq hκ.le
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Analysis.planarConductivity, hs, hκ.ne']

private theorem isotropicSlopeConductivity_hasFDerivAt {κ : ℝ} (hκ : 0 < κ) :
    HasFDerivAt
      (fun ell : ℂ →L[ℝ] ℝ => Analysis.planarConductivity
        (κ + (ell 1) ^ 2) (κ + (ell Complex.I) ^ 2) (ell 1 * ell Complex.I))
      (0 : (ℂ →L[ℝ] ℝ) →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ)
      (0 : ℂ →L[ℝ] ℝ) := by
  let Ω : Set (ℝ × (ℝ × ℝ)) := {t | 0 < t.1 * t.2.1 - t.2.2 ^ 2}
  let outer : Fin 2 → Fin 2 → (ℝ × (ℝ × ℝ)) → ℝ := fun i j t =>
    Analysis.planarConductivity t.1 t.2.1 t.2.2 i j
  let inner : (ℂ →L[ℝ] ℝ) → ℝ × (ℝ × ℝ) := fun ell =>
    (κ + (ell 1) ^ 2, (κ + (ell Complex.I) ^ 2, ell 1 * ell Complex.I))
  have hΩ : IsOpen Ω := isOpen_lt continuous_const (by fun_prop)
  have hp : (κ, (κ, 0)) ∈ Ω := by
    change 0 < κ * κ - (0 : ℝ) ^ 2
    simpa using mul_pos hκ hκ
  have ha : ContDiffOn ℝ 1 (fun t : ℝ × (ℝ × ℝ) => t.1) Ω := by fun_prop
  have hb : ContDiffOn ℝ 1 (fun t : ℝ × (ℝ × ℝ) => t.2.1) Ω := by fun_prop
  have hc : ContDiffOn ℝ 1 (fun t : ℝ × (ℝ × ℝ) => t.2.2) Ω := by fun_prop
  have hout (i j : Fin 2) : ContDiffOn ℝ 1 (outer i j) Ω :=
    Analysis.contDiffOn_planarConductivity ha hb hc (fun t ht => ht) i j
  have h1 : HasFDerivAt (fun ell : ℂ →L[ℝ] ℝ => ell 1)
      (ContinuousLinearMap.apply ℝ ℝ (1 : ℂ)) (0 : ℂ →L[ℝ] ℝ) :=
    (ContinuousLinearMap.apply ℝ ℝ (1 : ℂ)).hasFDerivAt
  have hI : HasFDerivAt (fun ell : ℂ →L[ℝ] ℝ => ell Complex.I)
      (ContinuousLinearMap.apply ℝ ℝ Complex.I) (0 : ℂ →L[ℝ] ℝ) :=
    (ContinuousLinearMap.apply ℝ ℝ Complex.I).hasFDerivAt
  have hfirst : HasFDerivAt (fun ell : ℂ →L[ℝ] ℝ => κ + (ell 1) ^ 2)
      (0 : (ℂ →L[ℝ] ℝ) →L[ℝ] ℝ) (0 : ℂ →L[ℝ] ℝ) := by
    simpa using! (h1.pow 2).const_add κ
  have hsecond : HasFDerivAt (fun ell : ℂ →L[ℝ] ℝ => κ + (ell Complex.I) ^ 2)
      (0 : (ℂ →L[ℝ] ℝ) →L[ℝ] ℝ) (0 : ℂ →L[ℝ] ℝ) := by
    simpa using! (hI.pow 2).const_add κ
  have hcross : HasFDerivAt (fun ell : ℂ →L[ℝ] ℝ => ell 1 * ell Complex.I)
      (0 : (ℂ →L[ℝ] ℝ) →L[ℝ] ℝ) (0 : ℂ →L[ℝ] ℝ) := by
    simpa [Pi.mul_apply] using! h1.mul hI
  have hin : HasFDerivAt inner
      (0 : (ℂ →L[ℝ] ℝ) →L[ℝ] (ℝ × (ℝ × ℝ))) (0 : ℂ →L[ℝ] ℝ) := by
    simpa [inner] using! hfirst.prodMk (hsecond.prodMk hcross)
  have hin0 : inner (0 : ℂ →L[ℝ] ℝ) = (κ, (κ, 0)) := by simp [inner]
  have hd (i j : Fin 2) : DifferentiableAt ℝ (outer i j)
      (inner (0 : ℂ →L[ℝ] ℝ)) := by
    rw [hin0]
    exact ((hout i j).contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by norm_num)
  apply hasFDerivAt_pi'.mpr
  intro i
  apply hasFDerivAt_pi'.mpr
  intro j
  simpa [outer, inner, Function.comp_def] using!
    (hd i j).hasFDerivAt.comp (0 : ℂ →L[ℝ] ℝ) hin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- At the original chart center, the unaveraged conductivity of the literal
leading graph has identity value and zero derivative in the slope variable.
The normal, leading coefficient and target metric are the supplied ones. -/
theorem chartLeadingPlaneProjection_center_conductivity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {p x : M}
    (hsrc : x ∈ (chartAt E p).source)
    {b : Fin (Module.finrank ℝ E) → ℂ} (hb : b ≠ 0)
    (hnull : (∑ i, ∑ j, (chartGramMatrix g p x i j : ℂ) * b i * b j) = 0)
    {N : E} (hN : chartLeadingPlaneProjection g p x b N = 0)
    (hunit : chartGramBilin g p x N N = 1) :
    let lift : ℂ → E := fun w => (chartModelBasis E).equivFunL.symm
      (fun i => (2 : ℝ) * (w * b i).re)
    let G : (ℂ →L[ℝ] ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun ell i j =>
      chartGramBilin g p x
        (lift (![1, Complex.I] i) + ell (![1, Complex.I] i) • N)
        (lift (![1, Complex.I] j) + ell (![1, Complex.I] j) • N)
    let A : (ℂ →L[ℝ] ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun ell =>
      Analysis.planarConductivity (G ell 0 0) (G ell 1 1) (G ell 0 1)
    A 0 = 1 ∧ HasFDerivAt A
      (0 : (ℂ →L[ℝ] ℝ) →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ) (0 : ℂ →L[ℝ] ℝ) := by
  let lift : ℂ → E := fun w => (chartModelBasis E).equivFunL.symm
    (fun i => (2 : ℝ) * (w * b i).re)
  let G : (ℂ →L[ℝ] ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun ell i j =>
    chartGramBilin g p x
      (lift (![1, Complex.I] i) + ell (![1, Complex.I] i) • N)
      (lift (![1, Complex.I] j) + ell (![1, Complex.I] j) • N)
  let A : (ℂ →L[ℝ] ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun ell =>
    Analysis.planarConductivity (G ell 0 0) (G ell 1 1) (G ell 0 1)
  change A 0 = 1 ∧ HasFDerivAt A
    (0 : (ℂ →L[ℝ] ℝ) →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ) (0 : ℂ →L[ℝ] ℝ)
  obtain ⟨κ, hκ, hgram⟩ :=
    chartLeadingPlaneProjection_lift_normal_gram g hsrc hb hnull hN hunit
  have h00 (ell : ℂ →L[ℝ] ℝ) : G ell 0 0 = κ + (ell 1) ^ 2 := by
    simpa [G, lift, pow_two] using hgram 1 1 (ell 1) (ell 1)
  have h11 (ell : ℂ →L[ℝ] ℝ) : G ell 1 1 = κ + (ell Complex.I) ^ 2 := by
    simpa [G, lift, pow_two] using
      hgram Complex.I Complex.I (ell Complex.I) (ell Complex.I)
  have h01 (ell : ℂ →L[ℝ] ℝ) : G ell 0 1 = ell 1 * ell Complex.I := by
    simpa [G, lift] using hgram 1 Complex.I (ell 1) (ell Complex.I)
  have hA : A = fun ell => Analysis.planarConductivity
      (κ + (ell 1) ^ 2) (κ + (ell Complex.I) ^ 2) (ell 1 * ell Complex.I) := by
    funext ell
    dsimp only [A]
    rw [h00, h11, h01]
  rw [hA]
  constructor
  · simpa using isotropicSlopeConductivity_zero hκ
  · exact isotropicSlopeConductivity_hasFDerivAt hκ

end DifferentialGeometry.Geometry
