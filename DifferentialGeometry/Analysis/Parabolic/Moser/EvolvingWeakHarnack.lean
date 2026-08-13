import DifferentialGeometry.Analysis.Parabolic.Moser.Crossover
import DifferentialGeometry.Analysis.Parabolic.Moser.EvolvingLocalBoundedness

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem evolving_weak_harnack_of_localized_crossover_of_volume_le
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    {q : SmoothRiemannianMetric I M} (rho : SmoothScalar q)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M ↦ u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p a τ t₁ B C G A K s₀ : ℝ}
    (hp : 2 ≤ p) (haτ : a < τ) (hτt₁ : τ ≤ t₁)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hg : MetricFamilyRegularAt (I := I) g s₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun z : ℝ × M ↦
          chartGramMatrix (I := I) (g z.1) x₀ z.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hSobolev : ∀ t ∈ Icc a t₁,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (hpde : ∀ t ∈ Icc a t₁, ∀ x : M,
      Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun s ↦ u s x) t)
    (htrace : ∀ t ∈ Icc a t₁, ∀ x : M,
      traceTimeDerivMetric (I := I) g t x ≤ B)
    (hgradient : ∀ k t, t ∈ Icc a t₁ → ∀ x : M,
      (g t).inner x
          (gradientFun (I := I) (g t)
            (spatialMoserCutoff rho (2 * k + 1)).toFun x)
          (gradientFun (I := I) (g t)
            (spatialMoserCutoff rho (2 * k + 1)).toFun x) ≤
        evolvingMoserSpatialGradientCost G k *
          (spatialMoserCutoff rho (2 * k)).toFun x ^ 2)
    (V : ℝ≥0∞) (hV : V ≠ ⊤)
    (hvolume : ∀ t ∈ Icc a t₁,
      riemannianVolumeMeasure (I := I) (M := M) q ≤
        V • riemannianMeasureFamily (I := I) (M := M) g t)
    (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hcrossover :
      A * evolvingMoserLocalizedMass
        (I := I) (M := M) (Module.finrank ℝ E) g rho
          (fun s y ↦ (u s y)⁻¹) p a τ t₁ 0 ≤ K) :
    ∀ t ∈ Ioo τ t₁, ∀ x : M, 1 < rho.toFun x →
      A ^ (1 / p) ≤
        K ^ (1 / p) *
          (max 1 V.toReal * evolvingMoserLocalBoundFactor
            (Module.finrank ℝ E) C G B p a τ t₁) * u t x := by
  let D := evolvingMoserLocalizedMass
    (I := I) (M := M) (Module.finrank ℝ E) g rho
      (fun s y ↦ (u s y)⁻¹) p a τ t₁ 0
  let F := max 1 V.toReal * evolvingMoserLocalBoundFactor
    (Module.finrank ℝ E) C G B p a τ t₁
  have hp_pos : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hD : 0 ≤ D :=
    evolvingMoserLocalizedMass_nonneg
      (I := I) (M := M) (Module.finrank ℝ E) g rho
        (fun s y ↦ (u s y)⁻¹) haτ hτt₁
          (fun s y ↦ (inv_pos.mpr (hpos s y)).le) 0
  have hF : 0 ≤ F := mul_nonneg
    (zero_le_one.trans (le_max_left 1 V.toReal)) (Real.exp_pos _).le
  intro t ht x hx
  have hreciprocal :=
    evolving_reciprocal_local_boundedness_of_supersolution_of_volume_le
      (I := I) (M := M) g hdim rho u hu hpos hp haτ hτt₁
        hB hC hG hg hgram hSobolev hpde htrace hgradient V hV hvolume
          t ht x hx
  have hreciprocal' : (u t x)⁻¹ ≤ F * D ^ (1 / p) := by
    simpa only [evolvingMoserLocalBound, evolvingMoserNormalizedMass,
      parabolicMoserExponent_zero, D, F, mul_assoc] using hreciprocal
  simpa only [D, F, mul_assoc] using
    weak_harnack_of_crossover (hpos t x) hA hD hF hK hp_pos
      hcrossover hreciprocal'

theorem evolving_weak_harnack_of_localized_rpow_crossover_of_volume_le
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    {q : SmoothRiemannianMetric I M} (rho : SmoothScalar q)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M ↦ u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p a τ t₁ B C G A K s₀ : ℝ}
    (hp : 0 < p) (haτ : a < τ) (hτt₁ : τ ≤ t₁)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hg : MetricFamilyRegularAt (I := I) g s₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun z : ℝ × M ↦
          chartGramMatrix (I := I) (g z.1) x₀ z.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hSobolev : ∀ t ∈ Icc a t₁,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (hpde : ∀ t ∈ Icc a t₁, ∀ x : M,
      Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun s ↦ u s x) t)
    (htrace : ∀ t ∈ Icc a t₁, ∀ x : M,
      traceTimeDerivMetric (I := I) g t x ≤ B)
    (hgradient : ∀ k t, t ∈ Icc a t₁ → ∀ x : M,
      (g t).inner x
          (gradientFun (I := I) (g t)
            (spatialMoserCutoff rho (2 * k + 1)).toFun x)
          (gradientFun (I := I) (g t)
            (spatialMoserCutoff rho (2 * k + 1)).toFun x) ≤
        evolvingMoserSpatialGradientCost G k *
          (spatialMoserCutoff rho (2 * k)).toFun x ^ 2)
    (V : ℝ≥0∞) (hV : V ≠ ⊤)
    (hvolume : ∀ t ∈ Icc a t₁,
      riemannianVolumeMeasure (I := I) (M := M) q ≤
        V • riemannianMeasureFamily (I := I) (M := M) g t)
    (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hcrossover :
      A * evolvingMoserLocalizedMass
        (I := I) (M := M) (Module.finrank ℝ E) g rho
          (fun s y ↦ u s y ^ (-p / 2)) 2 a τ t₁ 0 ≤ K) :
    ∀ t ∈ Ioo τ t₁, ∀ x : M, 1 < rho.toFun x →
      A ^ (1 / p) ≤ K ^ (1 / p) *
        (max 1 V.toReal * evolvingMoserLocalBoundFactor
          (Module.finrank ℝ E) C G B 2 a τ t₁) ^ (2 / p) * u t x := by
  let v : ℝ → M → ℝ := fun t x ↦ u t x ^ (-p / 2)
  let D := evolvingMoserLocalizedMass
    (I := I) (M := M) (Module.finrank ℝ E) g rho v 2 a τ t₁ 0
  let F := max 1 V.toReal * evolvingMoserLocalBoundFactor
    (Module.finrank ℝ E) C G B 2 a τ t₁
  have hD : 0 ≤ D :=
    evolvingMoserLocalizedMass_nonneg
      (I := I) (M := M) (Module.finrank ℝ E) g rho v haτ hτt₁
        (fun t x ↦ (Real.rpow_pos_of_pos (hpos t x) (-p / 2)).le) 0
  have hF : 0 ≤ F ^ (2 / p) :=
    Real.rpow_nonneg
      (mul_nonneg (zero_le_one.trans (le_max_left 1 V.toReal))
        (Real.exp_pos _).le) _
  intro t ht x hx
  have hreciprocal :=
    evolving_reciprocal_local_boundedness_of_supersolution_rpow_of_volume_le
      (I := I) (M := M) g hdim rho u hu hpos hp haτ hτt₁
        hB hC hG hg hgram hSobolev hpde htrace hgradient V hV hvolume
          t ht x hx
  have hreciprocal' : (u t x)⁻¹ ≤ F ^ (2 / p) * D ^ (1 / p) := by
    simpa only [v, D, F] using hreciprocal
  simpa only [D, F, v, mul_assoc] using
    weak_harnack_of_crossover (hpos t x) hA hD hF hK hp
      hcrossover hreciprocal'

theorem evolving_harnack_of_localized_crossover_of_volume_le
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    {q : SmoothRiemannianMetric I M} (rho : SmoothScalar q)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M ↦ u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p a τ t₁ B C G K s₀ : ℝ}
    (hp : 2 ≤ p) (haτ : a < τ) (hτt₁ : τ ≤ t₁)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hG : 0 ≤ G) (hK : 0 ≤ K)
    (hg : MetricFamilyRegularAt (I := I) g s₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun z : ℝ × M ↦
          chartGramMatrix (I := I) (g z.1) x₀ z.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hSobolev : ∀ t ∈ Icc a t₁,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (hpde : ∀ t ∈ Icc a t₁, ∀ x : M,
      deriv (fun s ↦ u s x) t =
        Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x)
    (htrace : ∀ t ∈ Icc a t₁, ∀ x : M,
      traceTimeDerivMetric (I := I) g t x ≤ B)
    (hgradient : ∀ k t, t ∈ Icc a t₁ → ∀ x : M,
      (g t).inner x
          (gradientFun (I := I) (g t)
            (spatialMoserCutoff rho (2 * k + 1)).toFun x)
          (gradientFun (I := I) (g t)
            (spatialMoserCutoff rho (2 * k + 1)).toFun x) ≤
        evolvingMoserSpatialGradientCost G k *
          (spatialMoserCutoff rho (2 * k)).toFun x ^ 2)
    (V : ℝ≥0∞) (hV : V ≠ ⊤)
    (hvolume : ∀ t ∈ Icc a t₁,
      riemannianVolumeMeasure (I := I) (M := M) q ≤
        V • riemannianMeasureFamily (I := I) (M := M) g t)
    (hcrossover :
      evolvingMoserLocalizedMass
          (I := I) (M := M) (Module.finrank ℝ E) g rho u p a τ t₁ 0 *
        evolvingMoserLocalizedMass
          (I := I) (M := M) (Module.finrank ℝ E) g rho
            (fun s y ↦ (u s y)⁻¹) p a τ t₁ 0 ≤ K) :
    ∀ t ∈ Ioo τ t₁, ∀ x : M, 1 < rho.toFun x →
      ∀ s ∈ Ioo τ t₁, ∀ y : M, 1 < rho.toFun y →
        u t x ≤
          (max 1 V.toReal * evolvingMoserLocalBoundFactor
            (Module.finrank ℝ E) C G B p a τ t₁) ^ 2 *
              K ^ (1 / p) * u s y := by
  let Dplus := evolvingMoserLocalizedMass
    (I := I) (M := M) (Module.finrank ℝ E) g rho u p a τ t₁ 0
  let Dminus := evolvingMoserLocalizedMass
    (I := I) (M := M) (Module.finrank ℝ E) g rho
      (fun s y ↦ (u s y)⁻¹) p a τ t₁ 0
  let F := max 1 V.toReal * evolvingMoserLocalBoundFactor
    (Module.finrank ℝ E) C G B p a τ t₁
  have hDplus : 0 ≤ Dplus :=
    evolvingMoserLocalizedMass_nonneg
      (I := I) (M := M) (Module.finrank ℝ E) g rho u haτ hτt₁
        (fun t x ↦ (hpos t x).le) 0
  have hF : 0 ≤ F := mul_nonneg
    (zero_le_one.trans (le_max_left 1 V.toReal)) (Real.exp_pos _).le
  intro t ht x hx s hs y hy
  have hlocal : u t x ≤ F * Dplus ^ (1 / p) := by
    have h := evolving_local_boundedness_of_subsolution_of_volume_le
      (I := I) (M := M) g hdim rho u hu hpos hp haτ hτt₁
        hB hC hG hg hgram hSobolev
          (fun r hr z ↦ (hpde r hr z).le) htrace hgradient V hV hvolume
            t ht x hx
    simpa only [evolvingMoserLocalBound, evolvingMoserNormalizedMass,
      parabolicMoserExponent_zero, Dplus, F, mul_assoc] using h
  have hweak : Dplus ^ (1 / p) ≤ K ^ (1 / p) * F * u s y := by
    simpa only [Dplus, Dminus, F, mul_assoc] using
      evolving_weak_harnack_of_localized_crossover_of_volume_le
        (I := I) (M := M) g hdim rho u hu hpos hp haτ hτt₁
          hB hC hG hg hgram hSobolev
            (fun r hr z ↦ (hpde r hr z).ge) htrace hgradient V hV hvolume
              hDplus hK (by simpa only [Dplus, Dminus] using hcrossover)
                s hs y hy
  calc
    u t x ≤ F * Dplus ^ (1 / p) := hlocal
    _ ≤ F * (K ^ (1 / p) * F * u s y) :=
      mul_le_mul_of_nonneg_left hweak hF
    _ = F ^ 2 * K ^ (1 / p) * u s y := by ring

end DifferentialGeometry.Analysis.Parabolic.Moser

end
