import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Measure.DensityTimeRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.CutoffTimeDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.LocalRate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.LocalRemainder
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.IntegrationByParts.WeightedLaplacian
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.CutoffDivergence

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.TensorMetric
  (metricDiffSq)

open DifferentialGeometry.Tensor.Coordinates
open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Elliptic DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open scoped Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [I.Boundaryless] [SigmaCompactSpace M]

theorem forward_uniqueness_cutoff_energy_deriv_le_of_flux_remainder_bounds
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    (χ : C^∞⟮I, M; ℝ⟯) (hχ : HasCompactSupport (χ : M → ℝ))
    {a b : ℝ}
    (hjoint₁ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) α p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (hjoint₂ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₂ p.1) α p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (hpde₁ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₁ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₁ t) x v w) (Ici a) t)
    (hpde₂ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₂ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₂ t) x v w) (Ici a) t)
    {t : ℝ} (ht : t ∈ Ioo a b)
    (Q : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) 5)
    {C_U C_rem Λ BRic21 : ℝ}
    (hFlux : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₁ t) x 5
      ((forwardUniquenessUflux (I := I) g₁ g₂ t - Q) x) ≤
        C_U * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hRem : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₁ t) x 4
      (forwardUniquenessRem (I := I) g₁ g₂ t x + covDiv0SField (I := I) (g₁ t) Q x) ≤
        C_rem * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ x ∈ tsupport (χ : M → ℝ), ∀ v : TangentSpace I x,
      (g₁ t).inner x v v ≤ Λ * (g₂ t).inner x v v)
    (hBRic21 : ∀ x ∈ tsupport (χ : M → ℝ),
      normSq0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₂ t) x) ≤ BRic21)
    {Λric B₁ η ε δ : ℝ} (hη : 0 < η) (hε : 0 < ε) (hδ : 0 < δ)
    (hΛric : ∀ x ∈ tsupport (χ : M → ℝ),
      normSq0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x) ≤ Λric)
    (hB₁ : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₁ t) x 3
      (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.ricciSection (I := I) (metricCov (I := I) (g₂ t))
          (metricCov_smooth (I := I) (g₂ t))) x) ≤ B₁) :
    let n : Real := Module.finrank Real E
    let KA : ℝ := 2 * (200 * (n ^ 6 + 1))
    let C_A := max (8 * Λric + KA * ((1 + Λ) ^ 2 * (B₁ + BRic21))) KA
    let C_R := (4 * n ^ 6 + 6 * n ^ 8 + 8 * n ^ 10) * Real.sqrt Λric
    let C_rest := C_R + 4 * n ^ 4 + 1 + δ * C_A + δ⁻¹ + Real.sqrt (n * Λric)
    let S := forwardUniquenessSfield (I := I) g₁ g₂ t
    let A := metricNabla0S (I := I) (g₁ t) S
    let B := fun x => (covGradBundleEquiv (I := I) (M := M) 0 4 x
      ((mvfderiv (I := I) (χ : M → ℝ) x).smulRight
        (unitScalarRSLiftSection (I := I) (M := M) (fun y => S y) x)))
      (unitZeroSec (I := I) (M := M) x)
    let μ := riemannianVolumeMeasure (I := I) (M := M) (g₁ t)
    deriv (fun s => ∫ x, χ x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ s x
      ∂riemannianMeasureFamily g₁ s) t ≤
      (C_rest + C_rem + 1 + (ε⁻¹ + 2) * C_U) *
        (∫ x, χ x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x ∂μ) +
      (δ * C_A + 2 * η + ε - 2) *
        (∫ x, χ x ^ 2 * normSq0S (I := I) (g₁ t) x 5 (A x) ∂μ) +
      (2 * η⁻¹ + 2) * (∫ x, normSq0S (I := I) (g₁ t) x 5 (B x) ∂μ) := by
  classical
  let n : Real := Module.finrank Real E
  let KA : ℝ := 2 * (200 * (n ^ 6 + 1))
  let C_A := max (8 * Λric + KA * ((1 + Λ) ^ 2 * (B₁ + BRic21))) KA
  let C_R := (4 * n ^ 6 + 6 * n ^ 8 + 8 * n ^ 10) * Real.sqrt Λric
  let C_rest := C_R + 4 * n ^ 4 + 1 + δ * C_A + δ⁻¹ + Real.sqrt (n * Λric)
  let S := forwardUniquenessSfield (I := I) g₁ g₂ t
  let A := metricNabla0S (I := I) (g₁ t) S
  let B := fun x => (covGradBundleEquiv (I := I) (M := M) 0 4 x
    ((mvfderiv (I := I) (χ : M → ℝ) x).smulRight
      (unitScalarRSLiftSection (I := I) (M := M) (fun y => S y) x)))
    (unitZeroSec (I := I) (M := M) x)
  let μ := riemannianVolumeMeasure (I := I) (M := M) (g₁ t)
  let U := forwardUniquenessUflux (I := I) g₁ g₂ t - Q
  let F := fun x => forwardUniquenessRem (I := I) g₁ g₂ t x +
    covDiv0SField (I := I) (g₁ t) Q x
  let Adot := connSpeed (I := I) g₁ g₂ (forwardUniquenessAvec (I := I) g₁ g₂)
  let Sdot := rmSpeed (I := I) g₁ g₂ (forwardUniquenessSvec (I := I) g₁ g₂)
  let R := fun x => forwardUniqueDensityDot (I := I) g₁ g₂ Adot Sdot t x +
    (1 / 2) * traceTimeDerivMetric (I := I) g₁ t x * forwardUniqueDensity (I := I) g₁ g₂ t x
  have hab : a < b := ht.1.trans ht.2
  have hg₁ (α : M) (i j : Fin (Module.finrank ℝ E)) :=
    (hjoint₁ α i j).mono (Set.prod_mono Ioo_subset_Ico_self Subset.rfl)
  have hS₁ := forwardUniquenessIsSolution (I := I) g₁ hab hjoint₁ hpde₁
  have hS₂ := forwardUniquenessIsSolution (I := I) g₂ hab hjoint₂ hpde₂
  have hdotCont := forward_uniqueness_density_dot_continuous (I := I) g₁ g₂
    hjoint₁ hjoint₂ hpde₁ hpde₂ ht
  have htraceCont : Continuous (fun x => traceTimeDerivMetric (I := I) g₁ t x) := by
    have hslice : Continuous (fun x : M => (t, x)) := continuous_const.prodMk continuous_id
    have hmap : MapsTo (fun x : M => (t, x)) univ (Ioo a b ×ˢ (univ : Set M)) :=
      fun _ _ => ⟨ht, mem_univ _⟩
    have hcomp := (continuousOn_traceTimeDerivMetric_of_chartGram_contMDiffOn isOpen_Ioo hg₁).comp_continuous hslice (fun x => hmap (mem_univ x))
    simpa only [Function.comp_def] using hcomp
  have hRcont : Continuous R := hdotCont.add
    ((continuous_const.mul htraceCont).mul (dens_continuous (I := I) g₁ g₂ t))
  have hi {f : M → ℝ} (hf : Continuous f) : Integrable (fun x => χ x ^ 2 * f x) μ := by
    apply Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure (g₁ t)
      ((χ.contMDiff.continuous.pow 2).mul hf)
    apply HasCompactSupport.mono hχ
    intro x hx hzero
    apply hx
    simp [hzero]
  have hiR := hi hRcont
  have hiE := hi (dens_continuous (I := I) g₁ g₂ t)
  have hiD := hi (normSq0S_continuous (I := I) (g₁ t) A)
  have hiL := hi (inner0S_continuous (I := I) (g₁ t)
    (roughLap0SField (I := I) (g₁ t) S) S)
  have hiV := hi (inner0S_continuous (I := I) (g₁ t)
    (covDiv0SField (I := I) (g₁ t) U) S)
  have hdec := forwardUniquenessSdec (I := I) g₁ g₂ hS₁ hS₂ hpde₁ hpde₂ t ht
  have hdecQ (x : M) :
      rmSpeed (I := I) g₁ g₂ (forwardUniquenessSvec (I := I) g₁ g₂) t x =
        roughLap0SField (I := I) (g₁ t) S x +
          covDiv0SField (I := I) (g₁ t) U x + F x := by
    rw [hdec x]
    dsimp only [U, F]
    simp only [covDiv0SField_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
    abel
  have hpoint (x : M) : χ x ^ 2 * R x ≤
      2 * (χ x ^ 2 * inner0S (I := I) (g₁ t) x 4 (roughLap0SField (I := I) (g₁ t) S x) (S x)) +
      2 * (χ x ^ 2 * inner0S (I := I) (g₁ t) x 4 (covDiv0SField (I := I) (g₁ t) U x) (S x)) +
      (C_rest + C_rem + 1) * (χ x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x) +
      (δ * C_A) * (χ x ^ 2 * normSq0S (I := I) (g₁ t) x 5 (A x)) := by
    by_cases hx : x ∈ tsupport (χ : M → ℝ)
    · have hr : rateRest (I := I) g₁ g₂ Adot t x ≤
          C_rest * forwardUniqueDensity (I := I) g₁ g₂ t x +
          δ * C_A * normSq0S (I := I) (g₁ t) x 5 (A x) :=
        forward_uniqueness_rate_rest_le (I := I) g₁ g₂ hjoint₁ hjoint₂ hpde₁ hpde₂ ht x
          hδ (hΛric x hx) hΛ0 (hΛ x hx) (hB₁ x hx) (hBRic21 x hx)
      have hm : normSq0S (I := I) (g₁ t) x 4 (F x) ≤
          C_rem * forwardUniqueDensity (I := I) g₁ g₂ t x := hRem x hx
      have hpair := _root_.DifferentialGeometry.Tensor0SBundle.two_inner0S_le (I := I) (g₁ t) x 4 (F x) (S x)
      have hs : normSq0S (I := I) (g₁ t) x 4 (S x) ≤ forwardUniqueDensity (I := I) g₁ g₂ t x :=
        rmDiffSq_le_dens (I := I) g₁ g₂ t x
      have heq : R x = rateRest (I := I) g₁ g₂ Adot t x +
          2 * inner0S (I := I) (g₁ t) x 4 (roughLap0SField (I := I) (g₁ t) S x) (S x) +
          2 * inner0S (I := I) (g₁ t) x 4 (covDiv0SField (I := I) (g₁ t) U x) (S x) +
          2 * inner0S (I := I) (g₁ t) x 4 (F x) (S x) := by
        dsimp only [R]
        rw [rateIntegrand_eq]
        change rateRest (I := I) g₁ g₂ Adot t x +
          2 * inner0S (I := I) (g₁ t) x 4
            (rmSpeed (I := I) g₁ g₂ (forwardUniquenessSvec (I := I) g₁ g₂) t x) (S x) = _
        rw [hdecQ x, inner0S_add_left, inner0S_add_left]
        ring
      have hloc : R x ≤
          2 * inner0S (I := I) (g₁ t) x 4 (roughLap0SField (I := I) (g₁ t) S x) (S x) +
          2 * inner0S (I := I) (g₁ t) x 4 (covDiv0SField (I := I) (g₁ t) U x) (S x) +
          (C_rest + C_rem + 1) * forwardUniqueDensity (I := I) g₁ g₂ t x +
          δ * C_A * normSq0S (I := I) (g₁ t) x 5 (A x) := by
        rw [heq]
        linarith only [hr, hm, hpair, hs]
      simpa only [mul_add, mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left hloc (sq_nonneg (χ x))
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have himono := integral_mono hiR
    ((((hiL.const_mul 2).add (hiV.const_mul 2)).add (hiE.const_mul (C_rest + C_rem + 1))).add
      (hiD.const_mul (δ * C_A))) hpoint
  have heq₃ := integral_add
    (((hiL.const_mul 2).add (hiV.const_mul 2)).add (hiE.const_mul (C_rest + C_rem + 1)))
    (hiD.const_mul (δ * C_A))
  have heq₂ := integral_add ((hiL.const_mul 2).add (hiV.const_mul 2))
    (hiE.const_mul (C_rest + C_rem + 1))
  have heq₁ := integral_add (hiL.const_mul 2) (hiV.const_mul 2)
  simp only [Pi.add_apply] at himono heq₃ heq₂ heq₁
  rw [heq₃, heq₂, heq₁, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul] at himono
  have hprin := integral_sq_weighted_roughLap0SField_le_of_hasCompactSupport (I := I) (g₁ t) χ hχ S hη
  have hflux := integral_sq_weighted_covDiv0SField_le_of_hasCompactSupport (I := I)
    (g₁ t) χ hχ S U (dens_continuous (I := I) g₁ g₂ t) hε hFlux
  have hder := forward_uniqueness_cutoff_energy_hasDerivAt (I := I) g₁ g₂ χ hχ hjoint₁ hjoint₂ hpde₁ hpde₂ ht
  change deriv (fun s => ∫ x, χ x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ s x
      ∂riemannianMeasureFamily g₁ s) t ≤
    (C_rest + C_rem + 1 + (ε⁻¹ + 2) * C_U) *
      (∫ x, χ x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x ∂μ) +
    (δ * C_A + 2 * η + ε - 2) * (∫ x, χ x ^ 2 * normSq0S (I := I) (g₁ t) x 5 (A x) ∂μ) +
    (2 * η⁻¹ + 2) * (∫ x, normSq0S (I := I) (g₁ t) x 5 (B x) ∂μ)
  rw [hder.deriv]
  change (∫ x, χ x ^ 2 * R x ∂μ) ≤ _
  change (∫ x, χ x ^ 2 * inner0S (I := I) (g₁ t) x 4 (roughLap0SField (I := I) (g₁ t) S x) (S x) ∂μ) ≤
    (η - 1) * (∫ x, χ x ^ 2 * normSq0S (I := I) (g₁ t) x 5 (A x) ∂μ) +
    η⁻¹ * (∫ x, normSq0S (I := I) (g₁ t) x 5 (B x) ∂μ) at hprin
  change 2 * (∫ x, χ x ^ 2 * inner0S (I := I) (g₁ t) x 4 (covDiv0SField (I := I) (g₁ t) U x) (S x) ∂μ) ≤
    ε * (∫ x, χ x ^ 2 * normSq0S (I := I) (g₁ t) x 5 (A x) ∂μ) +
    (ε⁻¹ + 2) * C_U * (∫ x, χ x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x ∂μ) +
    2 * (∫ x, normSq0S (I := I) (g₁ t) x 5 (B x) ∂μ) at hflux
  nlinarith only [himono, hprin, hflux]

theorem forward_uniqueness_cutoff_energy_deriv_le
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    (χ : C^∞⟮I, M; ℝ⟯) (hχ : HasCompactSupport (χ : M → ℝ))
    {a b : ℝ}
    (hjoint₁ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) α p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (hjoint₂ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₂ p.1) α p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (hpde₁ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₁ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₁ t) x v w) (Ici a) t)
    (hpde₂ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₂ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₂ t) x v w) (Ici a) t)
    {t : ℝ} (ht : t ∈ Ioo a b)
    {Λ Ce BH BR1 BR2 BP BRic21 B5 B6 BP1 BP2 BR2g2 BRic2g2 B6g2 Background : ℝ}
    (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ x ∈ tsupport (χ : M → ℝ), ∀ v : TangentSpace I x, (g₁ t).inner x v v ≤ Λ * (g₂ t).inner x v v)
    (hCe : 1 ≤ Ce)
    (hEquiv : ∀ x ∈ tsupport (χ : M → ℝ), ∀ v : TangentSpace I x,
      Ce⁻¹ * (g₁ t).inner x v v ≤ (g₂ t).inner x v v ∧
        (g₂ t).inner x v v ≤ Ce * (g₁ t).inner x v v)
    (hBH : ∀ x ∈ tsupport (χ : M → ℝ), metricDiffSq (I := I) (g₁ t) (g₂ t) x ≤ BH)
    (hBR1 : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₁ t) x 4 (metricRm04At (I := I) (g₁ t) x) ≤ BR1)
    (hBR2 : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₁ t) x 4 (metricRm04At (I := I) (g₂ t) x) ≤ BR2)
    (hBP : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₁ t) x 4
      (CovariantDerivative.riemannCurvature04At (I := I) (g₁ t)
        (metricCov (I := I) (g₂ t)) (metricCov_smooth (I := I) (g₂ t)) x) ≤ BP)
    (hBRic21 : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₂ t) x) ≤ BRic21)
    (hB5 : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₁ t) x 5
      (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.rm04Section (I := I) (g₂ t)
          (metricCov (I := I) (g₂ t)) (metricCov_smooth (I := I) (g₂ t))) x) ≤ B5)
    (hB6 : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₁ t) x 6
      (metricNabla0S (I := I) (g₂ t) (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.rm04Section (I := I) (g₂ t)
          (metricCov (I := I) (g₂ t)) (metricCov_smooth (I := I) (g₂ t)))) x) ≤ B6)
    (hBP1 : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₁ t) x 5
      (metricNabla0S (I := I) (g₁ t)
        (CovariantDerivative.rm04Section (I := I) (g₁ t)
          (metricCov (I := I) (g₂ t)) (metricCov_smooth (I := I) (g₂ t))) x) ≤ BP1)
    (hBP2 : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₁ t) x 6
      (metricNabla0S (I := I) (g₁ t) (metricNabla0S (I := I) (g₁ t)
        (CovariantDerivative.rm04Section (I := I) (g₁ t)
          (metricCov (I := I) (g₂ t)) (metricCov_smooth (I := I) (g₂ t)))) x) ≤ BP2)
    (hBR2g2 : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₂ t) x 4 (metricRm04At (I := I) (g₂ t) x) ≤ BR2g2)
    (hBRic2g2 : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₂ t) x 2 (metricRicciAt (I := I) (g₂ t) x) ≤ BRic2g2)
    (hB6g2 : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₂ t) x 6
      (metricNabla0S (I := I) (g₂ t) (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.rm04Section (I := I) (g₂ t)
          (metricCov (I := I) (g₂ t)) (metricCov_smooth (I := I) (g₂ t)))) x) ≤ B6g2)
    (hBackground : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₁ t) x 2 (metricTensorField (I := I) (g₂ t) x) ≤ Background)
    {Λric B₁ η ε δ : ℝ} (hη : 0 < η) (hε : 0 < ε) (hδ : 0 < δ)
    (hΛric : ∀ x ∈ tsupport (χ : M → ℝ),
      normSq0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x) ≤ Λric)
    (hB₁ : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₁ t) x 3
      (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.ricciSection (I := I) (metricCov (I := I) (g₂ t))
          (metricCov_smooth (I := I) (g₂ t))) x) ≤ B₁) :
    let n : Real := Module.finrank Real E
    let KQ : Real :=
      16 * (4 * n ^ 14 * (2 + 2 * n ^ 6 * BP) * (BR1 + BR2) +
        2 * (6 * n ^ 18 * Λ ^ 2 + 4 * n ^ 22 * Λ ^ 4 * BH) * BR2 ^ 2)
    let KD : Real := 32 * n ^ 6 * (n ^ 4 * BR1 + BRic21)
    let KR0 : Real :=
      200 * n ^ 12 * B5 + 8 * n ^ 10 * Λ ^ 2 * B6 + 16 * KQ + 2 * KD
    let BSpeed : Real :=
      8 * n ^ 6 * B6g2 + 512 * n ^ 14 * BR2g2 ^ 2 +
        72 * n ^ 6 * (BRic2g2 * BR2g2)
    let KG : Real := 8 * n ^ 10 * BP + 2 * Ce ^ 6 * n ^ 6 * BSpeed
    let KL : Real := n ^ 12 * BP2
    let KT : Real := 4 * n ^ 17 * BP1 * Background
    let C_rem : Real := 8 * KR0 + 8 * KG + 4 * KL + 2 * KT
    let KA : ℝ := 2 * (200 * (n ^ 6 + 1))
    let C_A := max (8 * Λric + KA * ((1 + Λ) ^ 2 * (B₁ + BRic21))) KA
    let C_R := (4 * n ^ 6 + 6 * n ^ 8 + 8 * n ^ 10) * Real.sqrt Λric
    let C_rest := C_R + 4 * n ^ 4 + 1 + δ * C_A + δ⁻¹ + Real.sqrt (n * Λric)
    let C_U := 32 * n ^ 5 * BR2 + 8 * n ^ 10 * (BP * Background)
    let S := forwardUniquenessSfield (I := I) g₁ g₂ t
    let A := metricNabla0S (I := I) (g₁ t) S
    let B := fun x => (covGradBundleEquiv (I := I) (M := M) 0 4 x
      ((mvfderiv (I := I) (χ : M → ℝ) x).smulRight
        (unitScalarRSLiftSection (I := I) (M := M) (fun y => S y) x)))
      (unitZeroSec (I := I) (M := M) x)
    let μ := riemannianVolumeMeasure (I := I) (M := M) (g₁ t)
    deriv (fun s => ∫ x, χ x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ s x
      ∂riemannianMeasureFamily g₁ s) t ≤
      (C_rest + C_rem + 1 + (ε⁻¹ + 2) * C_U) *
        (∫ x, χ x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x ∂μ) +
      (δ * C_A + 2 * η + ε - 2) *
        (∫ x, χ x ^ 2 * normSq0S (I := I) (g₁ t) x 5 (A x) ∂μ) +
      (2 * η⁻¹ + 2) * (∫ x, normSq0S (I := I) (g₁ t) x 5 (B x) ∂μ) := by
  dsimp only
  refine forward_uniqueness_cutoff_energy_deriv_le_of_flux_remainder_bounds (I := I)
    g₁ g₂ χ hχ hjoint₁ hjoint₂ hpde₁ hpde₂ ht 0 ?_ ?_
    hΛ0 hΛ hBRic21 hη hε hδ hΛric hB₁
  · intro x hx
    have hB₂0 : 0 ≤ BR2 := (normSq0S_nonneg (I := I) (g₁ t) x 4 _).trans (hBR2 x hx)
    have hBP0 : 0 ≤ BP := (normSq0S_nonneg (I := I) (g₁ t) x 4 _).trans (hBP x hx)
    have hBackground0 : 0 ≤ Background :=
      (normSq0S_nonneg (I := I) (g₁ t) x 2 _).trans (hBackground x hx)
    have hBP' : normSq0S (I := I) (g₁ t) x 4
        ((forwardUniquenessTf (I := I) g₁ t - forwardUniquenessSfield (I := I) g₁ g₂ t) x) ≤ BP := by
      rw [forwardUniquenessP_eq]
      exact hBP x hx
    rw [sub_zero]
    exact fluxSlabLe (I := I) g₁ g₂ (forwardUniquenessTf (I := I) g₂)
      (fun z => forwardUniquenessTf (I := I) g₁ z - forwardUniquenessSfield (I := I) g₁ g₂ z)
      t x hB₂0 hBP0 hBackground0 (hBR2 x hx) hBP' (hBackground x hx)
  · intro x hx
    have hz : covDiv0SField (I := I) (g₁ t)
        (0 : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) 5) = 0 := by
      simpa only [sub_self] using covDiv0SField_sub (I := I) (g₁ t)
        (0 : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) 5) 0
    simpa [hz] using forward_uniqueness_remainder_norm_sq_le (I := I) g₁ g₂ t x
      hΛ0 (hΛ x hx) hCe (hEquiv x hx) (hBH x hx) (hBR1 x hx) (hBR2 x hx)
      (hBP x hx) (hBRic21 x hx) (hB5 x hx) (hB6 x hx) (hBP1 x hx) (hBP2 x hx)
      (hBR2g2 x hx) (hBRic2g2 x hx) (hB6g2 x hx) (hBackground x hx)

theorem forward_uniqueness_corrected_cutoff_energy_deriv_le
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    (χ : C^∞⟮I, M; ℝ⟯) (hχ : HasCompactSupport (χ : M → ℝ))
    {a b : ℝ}
    (hjoint₁ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) α p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (hjoint₂ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₂ p.1) α p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (hpde₁ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₁ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₁ t) x v w) (Ici a) t)
    (hpde₂ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₂ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₂ t) x v w) (Ici a) t)
    {t : ℝ} (ht : t ∈ Ioo a b)
    {Λ Ce BH BR1 BR2 BP BRic21 B5 B6 BR2g2 BRic2g2 B6g2 Background : ℝ}
    (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ x ∈ tsupport (χ : M → ℝ), ∀ v : TangentSpace I x, (g₁ t).inner x v v ≤ Λ * (g₂ t).inner x v v)
    (hCe : 1 ≤ Ce)
    (hEquiv : ∀ x ∈ tsupport (χ : M → ℝ), ∀ v : TangentSpace I x,
      Ce⁻¹ * (g₁ t).inner x v v ≤ (g₂ t).inner x v v ∧
        (g₂ t).inner x v v ≤ Ce * (g₁ t).inner x v v)
    (hBH : ∀ x ∈ tsupport (χ : M → ℝ), metricDiffSq (I := I) (g₁ t) (g₂ t) x ≤ BH)
    (hBR1 : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₁ t) x 4 (metricRm04At (I := I) (g₁ t) x) ≤ BR1)
    (hBR2 : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₁ t) x 4 (metricRm04At (I := I) (g₂ t) x) ≤ BR2)
    (hBP : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₁ t) x 4
      (CovariantDerivative.riemannCurvature04At (I := I) (g₁ t)
        (metricCov (I := I) (g₂ t)) (metricCov_smooth (I := I) (g₂ t)) x) ≤ BP)
    (hBRic21 : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₂ t) x) ≤ BRic21)
    (hB5 : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₁ t) x 5
      (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.rm04Section (I := I) (g₂ t)
          (metricCov (I := I) (g₂ t)) (metricCov_smooth (I := I) (g₂ t))) x) ≤ B5)
    (hB6 : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₁ t) x 6
      (metricNabla0S (I := I) (g₂ t) (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.rm04Section (I := I) (g₂ t)
          (metricCov (I := I) (g₂ t)) (metricCov_smooth (I := I) (g₂ t)))) x) ≤ B6)
    (hBR2g2 : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₂ t) x 4 (metricRm04At (I := I) (g₂ t) x) ≤ BR2g2)
    (hBRic2g2 : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₂ t) x 2 (metricRicciAt (I := I) (g₂ t) x) ≤ BRic2g2)
    (hB6g2 : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₂ t) x 6
      (metricNabla0S (I := I) (g₂ t) (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.rm04Section (I := I) (g₂ t)
          (metricCov (I := I) (g₂ t)) (metricCov_smooth (I := I) (g₂ t)))) x) ≤ B6g2)
    (hBackground : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₁ t) x 2 (metricTensorField (I := I) (g₂ t) x) ≤ Background)
    {Λric B₁ η ε δ : ℝ} (hη : 0 < η) (hε : 0 < ε) (hδ : 0 < δ)
    (hΛric : ∀ x ∈ tsupport (χ : M → ℝ),
      normSq0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x) ≤ Λric)
    (hB₁ : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₁ t) x 3
      (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.ricciSection (I := I) (metricCov (I := I) (g₂ t))
          (metricCov_smooth (I := I) (g₂ t))) x) ≤ B₁) :
    let n : Real := Module.finrank Real E
    let KQ : Real :=
      16 * (4 * n ^ 14 * (2 + 2 * n ^ 6 * BP) * (BR1 + BR2) +
        2 * (6 * n ^ 18 * Λ ^ 2 + 4 * n ^ 22 * Λ ^ 4 * BH) * BR2 ^ 2)
    let KD : Real := 32 * n ^ 6 * (n ^ 4 * BR1 + BRic21)
    let KR0 : Real :=
      200 * n ^ 12 * B5 + 8 * n ^ 10 * Λ ^ 2 * B6 + 16 * KQ + 2 * KD
    let BSpeed : Real :=
      8 * n ^ 6 * B6g2 + 512 * n ^ 14 * BR2g2 ^ 2 +
        72 * n ^ 6 * (BRic2g2 * BR2g2)
    let KG : Real := 8 * n ^ 10 * BP + 2 * Ce ^ 6 * n ^ 6 * BSpeed
    let C_rem : Real := 2 * KR0 + 2 * KG
    let KA : ℝ := 2 * (200 * (n ^ 6 + 1))
    let C_A := max (8 * Λric + KA * ((1 + Λ) ^ 2 * (B₁ + BRic21))) KA
    let C_R := (4 * n ^ 6 + 6 * n ^ 8 + 8 * n ^ 10) * Real.sqrt Λric
    let C_rest := C_R + 4 * n ^ 4 + 1 + δ * C_A + δ⁻¹ + Real.sqrt (n * Λric)
    let C_U := 32 * n ^ 5 * BR2 + 8 * n ^ 10 * (BP * Background)
    let C_V := 4 * n ^ 15 * Ce ^ 7 * (Ce ^ 5 * B5) +
      (16 * n ^ 18 * Ce ^ 8 + 32 * n ^ 19 * Ce ^ 6) * BR2g2 * BH
    let S := forwardUniquenessSfield (I := I) g₁ g₂ t
    let A := metricNabla0S (I := I) (g₁ t) S
    let B := fun x => (covGradBundleEquiv (I := I) (M := M) 0 4 x
      ((mvfderiv (I := I) (χ : M → ℝ) x).smulRight
        (unitScalarRSLiftSection (I := I) (M := M) (fun y => S y) x)))
      (unitZeroSec (I := I) (M := M) x)
    let μ := riemannianVolumeMeasure (I := I) (M := M) (g₁ t)
    deriv (fun s => ∫ x, χ x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ s x
      ∂riemannianMeasureFamily g₁ s) t ≤
      (C_rest + C_rem + 1 + (ε⁻¹ + 2) * (2 * C_U + 2 * C_V)) *
        (∫ x, χ x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x ∂μ) +
      (δ * C_A + 2 * η + ε - 2) *
        (∫ x, χ x ^ 2 * normSq0S (I := I) (g₁ t) x 5 (A x) ∂μ) +
      (2 * η⁻¹ + 2) * (∫ x, normSq0S (I := I) (g₁ t) x 5 (B x) ∂μ) := by
  dsimp only
  refine forward_uniqueness_cutoff_energy_deriv_le_of_flux_remainder_bounds (I := I)
    g₁ g₂ χ hχ hjoint₁ hjoint₂ hpde₁ hpde₂ ht
    (forwardUniquenessReloweringFlux (I := I) g₁ g₂ t) ?_ ?_
    hΛ0 hΛ hBRic21 hη hε hδ hΛric hB₁
  · intro x hx
    have hB5g2 : normSq0S (I := I) (g₂ t) x 5
        (metricNabla0S (I := I) (g₂ t)
          (CovariantDerivative.rm04Section (I := I) (g₂ t)
            (metricCov (I := I) (g₂ t)) (metricCov_smooth (I := I) (g₂ t))) x) ≤ Ce ^ 5 * B5 :=
      (normSq0S_upper_le_of_equiv (I := I) (g₁ t) (g₂ t) x 5 hCe (hEquiv x hx) _).trans
        (mul_le_mul_of_nonneg_left (hB5 x hx) (pow_nonneg (zero_le_one.trans hCe) 5))
    exact forward_uniqueness_corrected_flux_norm_sq_le (I := I) g₁ g₂ t x hCe (hEquiv x hx)
      (hBH x hx) (hBR2g2 x hx) hB5g2 (hBR2 x hx) (hBP x hx) (hBackground x hx)
  · intro x hx
    exact forward_uniqueness_algebraic_remainder_norm_sq_le (I := I) g₁ g₂ t x
      hΛ0 (hΛ x hx) hCe (hEquiv x hx) (hBH x hx) (hBR1 x hx) (hBR2 x hx)
      (hBP x hx) (hBRic21 x hx) (hB5 x hx) (hB6 x hx)
      (hBR2g2 x hx) (hBRic2g2 x hx) (hB6g2 x hx)

end DifferentialGeometry.PDE.RicciFlow
