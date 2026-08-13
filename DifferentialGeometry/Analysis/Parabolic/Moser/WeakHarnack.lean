import DifferentialGeometry.Analysis.Parabolic.Moser.Crossover
import DifferentialGeometry.Analysis.Parabolic.Moser.LocalBoundedness
import DifferentialGeometry.Analysis.Parabolic.Moser.ReverseHolder

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem weak_harnack_of_localized_crossover
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p a τ t₁ A C : ℝ} (hp : 2 ≤ p) (haτ : a < τ) (hτt₁ : τ ≤ t₁)
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hpde : ∀ t ∈ Icc a t₁, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (hcrossover :
      A * moserLocalizedMass (I := I) (M := M) (Module.finrank ℝ E) rho
          (fun s y => (u s y)⁻¹) p a τ t₁ 0 ≤ C) :
    ∀ t ∈ Ioo τ t₁, ∀ x : M, 1 < rho.toFun x →
      A ^ (1 / p) ≤
        C ^ (1 / p) *
          moserLocalBoundFactor (I := I) (M := M) g hdim rho p a τ t₁ * u t x := by
  let D := moserLocalizedMass (I := I) (M := M) (Module.finrank ℝ E) rho
    (fun s y => (u s y)⁻¹) p a τ t₁ 0
  let B := moserLocalBoundFactor (I := I) (M := M) g hdim rho p a τ t₁
  have hp_pos : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hD : 0 ≤ D := by
    exact moserLocalizedMass_nonneg (I := I) (M := M) (Module.finrank ℝ E) rho
      (fun s y => (u s y)⁻¹) haτ hτt₁ (fun s y => (inv_pos.mpr (hpos s y)).le) 0
  have hB : 0 ≤ B := (Real.exp_pos _).le
  intro t ht x hx
  have hreciprocal := reciprocal_local_boundedness_of_supersolution
    (I := I) (M := M) g hdim rho u hu hpos hp haτ hτt₁ hpde t ht x hx
  have hreciprocal' :
      (u t x)⁻¹ ≤ B * D ^ (1 / p) := by
    simpa only [moserLocalBound, moserNormalizedMass,
      parabolicMoserExponent_zero, D, B] using hreciprocal
  simpa only [D, B, mul_assoc] using
    weak_harnack_of_crossover (hpos t x) hA hD hB hC hp_pos
      hcrossover hreciprocal'

theorem weak_harnack_of_localized_rpow_crossover
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p a τ t₁ A C : ℝ} (hp : 0 < p) (haτ : a < τ) (hτt₁ : τ ≤ t₁)
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hpde : ∀ t ∈ Icc a t₁, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (hcrossover :
      A * localizedSpacetimeRpowMoment (I := I) (M := M)
        (spatialMoserCutoff rho 0) u (-p) a t₁ ≤ C) :
    let B := moserLocalBoundFactor (I := I) (M := M)
      g hdim rho 2 a τ t₁
    ∀ t ∈ Ioo τ t₁, ∀ x : M, 1 < rho.toFun x →
      A ^ (1 / p) ≤ C ^ (1 / p) * B ^ (2 / p) * u t x := by
  let v : ℝ → M → ℝ := fun t x => u t x ^ (-p / 2)
  let D := moserLocalizedMass (I := I) (M := M) (Module.finrank ℝ E)
    rho v 2 a τ t₁ 0
  let B := moserLocalBoundFactor (I := I) (M := M)
    g hdim rho 2 a τ t₁
  change ∀ t ∈ Ioo τ t₁, ∀ x : M, 1 < rho.toFun x →
    A ^ (1 / p) ≤ C ^ (1 / p) * B ^ (2 / p) * u t x
  have hD_eq : D = localizedSpacetimeRpowMoment (I := I) (M := M)
      (spatialMoserCutoff rho 0) u (-p) a t₁ := by
    simpa only [D, v, neg_div] using
      (moserLocalizedMass_rpow_half_eq_localizedSpacetimeRpowMoment
        (I := I) (M := M) (Module.finrank ℝ E) rho u hu hpos
          (p := -p) (τ := τ) (haτ.le.trans hτt₁))
  have hcrossover' : A * D ≤ C := by
    rw [hD_eq]
    exact hcrossover
  have hD : 0 ≤ D := by
    exact moserLocalizedMass_nonneg (I := I) (M := M) (Module.finrank ℝ E)
      rho v haτ hτt₁
        (fun t x => (Real.rpow_pos_of_pos (hpos t x) (-p / 2)).le) 0
  have hB : 0 ≤ B ^ (2 / p) :=
    Real.rpow_nonneg (Real.exp_pos _).le _
  intro t ht x hx
  have hreciprocal := reciprocal_local_boundedness_of_supersolution_rpow
    (I := I) (M := M) g hdim rho u hu hpos hp haτ hτt₁ hpde
  have hreciprocal' : (u t x)⁻¹ ≤ B ^ (2 / p) * D ^ (1 / p) := by
    simpa only [v, B, D] using hreciprocal t ht x hx
  simpa only [mul_assoc] using
    (weak_harnack_of_crossover (hpos t x) hA hD hB hC hp
      hcrossover' hreciprocal')

theorem harnack_of_localized_crossover
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p a τ t₁ C : ℝ} (hp : 2 ≤ p) (haτ : a < τ) (hτt₁ : τ ≤ t₁)
    (hC : 0 ≤ C)
    (hpde : ∀ t ∈ Icc a t₁, ∀ x : M,
      deriv (fun s => u s x) t =
        Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x)
    (hcrossover :
      moserLocalizedMass (I := I) (M := M) (Module.finrank ℝ E)
          rho u p a τ t₁ 0 *
        moserLocalizedMass (I := I) (M := M) (Module.finrank ℝ E)
          rho (fun s y => (u s y)⁻¹) p a τ t₁ 0 ≤ C) :
    let B := moserLocalBoundFactor (I := I) (M := M)
      g hdim rho p a τ t₁
    ∀ t ∈ Ioo τ t₁, ∀ x : M, 1 < rho.toFun x →
      ∀ q ∈ Ioo τ t₁, ∀ y : M, 1 < rho.toFun y →
        u t x ≤ B ^ 2 * C ^ (1 / p) * u q y := by
  let Dplus := moserLocalizedMass (I := I) (M := M)
    (Module.finrank ℝ E) rho u p a τ t₁ 0
  let Dminus := moserLocalizedMass (I := I) (M := M)
    (Module.finrank ℝ E) rho (fun s y => (u s y)⁻¹) p a τ t₁ 0
  let B := moserLocalBoundFactor (I := I) (M := M)
    g hdim rho p a τ t₁
  change ∀ t ∈ Ioo τ t₁, ∀ x : M, 1 < rho.toFun x →
    ∀ q ∈ Ioo τ t₁, ∀ y : M, 1 < rho.toFun y →
      u t x ≤ B ^ 2 * C ^ (1 / p) * u q y
  have hDplus : 0 ≤ Dplus :=
    moserLocalizedMass_nonneg (I := I) (M := M) (Module.finrank ℝ E)
      rho u haτ hτt₁ (fun t x => (hpos t x).le) 0
  have hB : 0 ≤ B := (Real.exp_pos _).le
  intro t ht x hx q hq y hy
  have hlocal : u t x ≤ B * Dplus ^ (1 / p) := by
    simpa only [moserLocalBound, moserNormalizedMass,
      parabolicMoserExponent_zero, Dplus, B] using
      local_boundedness_of_subsolution
        (I := I) (M := M) g hdim rho u hu hpos hp haτ hτt₁
          (fun s hs z => (hpde s hs z).le) t ht x hx
  have hweak : Dplus ^ (1 / p) ≤ C ^ (1 / p) * B * u q y := by
    simpa only [Dplus, Dminus, B] using
      weak_harnack_of_localized_crossover
        (I := I) (M := M) g hdim rho u hu hpos hp haτ hτt₁
          hDplus hC (fun s hs z => (hpde s hs z).ge)
          (by simpa only [Dplus, Dminus] using hcrossover) q hq y hy
  calc
    u t x ≤ B * Dplus ^ (1 / p) := hlocal
    _ ≤ B * (C ^ (1 / p) * B * u q y) :=
      mul_le_mul_of_nonneg_left hweak hB
    _ = B ^ 2 * C ^ (1 / p) * u q y := by ring

end DifferentialGeometry.Analysis.Parabolic.Moser

end
