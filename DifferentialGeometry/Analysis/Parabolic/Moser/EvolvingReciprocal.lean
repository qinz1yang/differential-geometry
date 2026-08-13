import DifferentialGeometry.Analysis.Parabolic.Moser.EvolvingForwardIteration
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

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

def evolvingReciprocalReverseCost
    (n : ℕ) (Vfixed Vmoving : ℝ≥0∞)
    (C G B a τ t₁ : ℝ) : ℝ :=
  (max 1 Vfixed.toReal *
      evolvingMoserLocalBoundFactor n C G B 2 a τ t₁) ^ (2 : ℝ) *
    Vmoving.toReal

theorem localizedSpacetimeRpowNorm_inv_le_evolvingReciprocalReverseCost_of_volume_le
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    {qMetric : SmoothRiemannianMetric I M}
    (rho inner : SmoothScalar qMetric)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p q a τ t₁ c d B C G s₀ : ℝ}
    (hp : 0 < p) (hpq : p ≤ q)
    (haτ : a < τ) (hτt₁ : τ ≤ t₁)
    (hac : a ≤ c) (hτc : τ < c) (hcd : c ≤ d) (hdt₁ : d < t₁)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hg : MetricFamilyRegularAt (I := I) g s₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun z : ℝ × M =>
          chartGramMatrix (I := I) (g z.1) x₀ z.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hSobolev : ∀ t ∈ Icc a t₁,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (hpde : ∀ t ∈ Icc a t₁, ∀ x : M,
      Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
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
    (Vfixed Vmoving : ℝ≥0∞)
    (hVfixedTop : Vfixed ≠ ⊤)
    (hVmovingZero : Vmoving ≠ 0) (hVmovingTop : Vmoving ≠ ⊤)
    (hfixedVolume : ∀ t ∈ Icc a t₁,
      riemannianVolumeMeasure (I := I) (M := M) qMetric ≤
        Vfixed • riemannianMeasureFamily (I := I) (M := M) g t)
    (hmovingVolume : ∀ t ∈ Icc a t₁,
      riemannianMeasureFamily (I := I) (M := M) g t ≤
        Vmoving • riemannianVolumeMeasure (I := I) (M := M) qMetric)
    (hinner : ∀ x, inner.toFun x ≠ 0 → 1 < rho.toFun x)
    (hcutoff : ∀ x,
      inner.toFun x ^ 2 ≤ (spatialMoserCutoff rho 0).toFun x ^ 2)
    (hmeasure : localizedSpacetimeMeasure (I := I) (M := M)
      (spatialMoserCutoff rho 0) a t₁ ≠ 0) :
    localizedSpacetimeRpowNorm (I := I) (M := M) inner
        (fun t x => (u t x)⁻¹) q c d ≤
      evolvingReciprocalReverseCost (Module.finrank ℝ E)
          Vfixed Vmoving C G B a τ t₁ ^ (1 / p - 1 / q) *
        localizedSpacetimeRpowNorm (I := I) (M := M)
          (spatialMoserCutoff rho 0) (fun t x => (u t x)⁻¹) p a t₁ := by
  let n := Module.finrank ℝ E
  let cutoff := spatialMoserCutoff rho 0
  let f : ℝ → M → ℝ := fun t x => (u t x)⁻¹
  let v : ℝ → M → ℝ := fun t x => u t x ^ (-p / 2)
  let F := max 1 Vfixed.toReal *
    evolvingMoserLocalBoundFactor n C G B 2 a τ t₁
  let D := evolvingMoserLocalizedMass
    (I := I) (M := M) n g rho v 2 a τ t₁ 0
  let P := localizedSpacetimeRpowMoment (I := I) (M := M)
    cutoff f p a t₁
  let N := localizedSpacetimeRpowNorm (I := I) (M := M)
    cutoff f p a t₁
  let R := evolvingReciprocalReverseCost n Vfixed Vmoving C G B a τ t₁
  let S := R ^ (1 / p) * N
  change localizedSpacetimeRpowNorm (I := I) (M := M) inner f q c d ≤
    R ^ (1 / p - 1 / q) * N
  have hf : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M => f z.1 z.2) := by
    simpa only [f, Real.rpow_neg_one] using
      contMDiff_rpow_of_pos hu hpos (-1 : ℝ)
  have hfpos : ∀ t x, 0 < f t x := fun t x => inv_pos.mpr (hpos t x)
  have hP : 0 < P := localizedSpacetimeRpowMoment_pos
    (I := I) (M := M) cutoff f hf.continuous hfpos p a t₁ hmeasure
  have hN : 0 < N := by
    exact localizedSpacetimeRpowNorm_pos hP
  have hF : 0 < F := mul_pos
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (Real.exp_pos _)
  have hVmoving : 0 < Vmoving.toReal :=
    ENNReal.toReal_pos hVmovingZero hVmovingTop
  have hR : 0 < R := by
    dsimp only [R, evolvingReciprocalReverseCost, F]
    exact mul_pos (Real.rpow_pos_of_pos hF _) hVmoving
  have hS : 0 < S := mul_pos (Real.rpow_pos_of_pos hR _) hN
  have hintegrand : Continuous (fun z : ℝ × M =>
      cutoff.toFun z.2 ^ 2 * f z.1 z.2 ^ p) :=
    (cutoff.smooth.continuous.comp continuous_snd).pow 2 |>.mul
      (hf.continuous.rpow_const fun z => Or.inl (hfpos z.1 z.2).ne')
  have hcompare := intervalIntegral_moving_le_fixed_of_volume_le
    (I := I) (M := M) qMetric g
      (fun t x => cutoff.toFun x ^ 2 * f t x ^ p) hintegrand
      (fun t x => mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (hfpos t x).le _))
      (haτ.le.trans hτt₁) hg Vmoving hVmovingTop hmovingVolume
  have hD_eq : D =
      ∫ t in a..t₁, ∫ x, cutoff.toFun x ^ 2 * f t x ^ p
        ∂(riemannianMeasureFamily (I := I) (M := M) g t) := by
    rw [show D = evolvingMoserLocalizedMass
      (I := I) (M := M) n g rho v 2 a τ t₁ 0 by rfl,
      evolvingMoserLocalizedMass, moserTimeLevel_zero]
    apply intervalIntegral.integral_congr
    intro t _
    apply integral_congr_ae
    filter_upwards with x
    simp only [parabolicMoserExponent_zero, cutoff, v, f]
    congr 1
    calc
      (u t x ^ (-p / 2)) ^ (2 : ℝ) = u t x ^ ((-p / 2) * 2) :=
        (Real.rpow_mul (hpos t x).le _ _).symm
      _ = u t x ^ (-p) := by congr 1; ring
      _ = (u t x)⁻¹ ^ p := Real.rpow_neg_eq_inv_rpow _ _
  have hfixed_eq :
      (∫ t in a..t₁, ∫ x, cutoff.toFun x ^ 2 * f t x ^ p
        ∂(riemannianVolumeMeasure (I := I) (M := M) qMetric)) = P := by
    dsimp only [P]
    rw [localizedSpacetimeRpowMoment_eq_intervalIntegral_of_continuous_pos
      (I := I) (M := M) cutoff f hf.continuous hfpos
        (haτ.le.trans hτt₁)]
  have hD : 0 ≤ D := evolvingMoserLocalizedMass_nonneg
    (I := I) (M := M) n g rho v haτ hτt₁
      (fun t x => (Real.rpow_pos_of_pos (hpos t x) _).le) 0
  have hDP : D ≤ Vmoving.toReal * P := by
    calc
      D = ∫ t in a..t₁, ∫ x, cutoff.toFun x ^ 2 * f t x ^ p
          ∂(riemannianMeasureFamily (I := I) (M := M) g t) := hD_eq
      _ ≤ Vmoving.toReal *
          (∫ t in a..t₁, ∫ x, cutoff.toFun x ^ 2 * f t x ^ p
            ∂(riemannianVolumeMeasure (I := I) (M := M) qMetric)) := by
        simpa only [] using hcompare
      _ = Vmoving.toReal * P := congrArg (fun z => Vmoving.toReal * z) hfixed_eq
  have hN_eq : P ^ (1 / p) = N := rfl
  have hroot : D ^ (1 / p) ≤ (Vmoving.toReal * P) ^ (1 / p) :=
    Real.rpow_le_rpow hD hDP (div_nonneg zero_le_one hp.le)
  have hroot' : D ^ (1 / p) ≤ Vmoving.toReal ^ (1 / p) * N := by
    calc
      D ^ (1 / p) ≤ (Vmoving.toReal * P) ^ (1 / p) := hroot
      _ = Vmoving.toReal ^ (1 / p) * P ^ (1 / p) := by
        rw [Real.mul_rpow hVmoving.le hP.le]
      _ = Vmoving.toReal ^ (1 / p) * N := by rw [hN_eq]
  have hfactor : F ^ (2 / p) * Vmoving.toReal ^ (1 / p) = R ^ (1 / p) := by
    change F ^ (2 / p) * Vmoving.toReal ^ (1 / p) =
      (F ^ (2 : ℝ) * Vmoving.toReal) ^ (1 / p)
    rw [Real.mul_rpow (Real.rpow_nonneg hF.le _) hVmoving.le,
      ← Real.rpow_mul hF.le]
    congr 1
    field_simp [hp.ne']
  have hpoint : ∀ t ∈ Icc c d, ∀ x,
      inner.toFun x ≠ 0 → f t x ≤ S := by
    intro t ht x hx
    have htInterior : t ∈ Ioo τ t₁ :=
      ⟨hτc.trans_le ht.1, ht.2.trans_lt hdt₁⟩
    have hlocal :=
      evolving_reciprocal_local_boundedness_of_supersolution_rpow_of_volume_le
        (I := I) (M := M) g hdim rho u hu hpos hp haτ hτt₁
          hB hC hG hg hgram hSobolev hpde htrace hgradient
          Vfixed hVfixedTop hfixedVolume t htInterior x (hinner x hx)
    have hlocal' : f t x ≤ F ^ (2 / p) * D ^ (1 / p) := by
      simpa only [f, F, D, v, n] using hlocal
    calc
      f t x ≤ F ^ (2 / p) * D ^ (1 / p) := hlocal'
      _ ≤ F ^ (2 / p) * (Vmoving.toReal ^ (1 / p) * N) :=
        mul_le_mul_of_nonneg_left hroot' (Real.rpow_nonneg hF.le _)
      _ = S := by rw [← mul_assoc, hfactor]
  have hinterpolation := localizedSpacetimeRpowNorm_le_of_bound_on_cutoff
    (I := I) (M := M) inner f hf.continuous hfpos hp hpq hcd hS hpoint
  have hmono : localizedSpacetimeRpowNorm (I := I) (M := M)
      inner f p c d ≤ N := by
    simpa only [N, cutoff] using
      (localizedSpacetimeRpowNorm_mono_measure
        (I := I) (M := M) f hf.continuous hfpos hp hac hdt₁.le hcutoff)
  have hratio : 0 ≤ p / q := div_nonneg hp.le (hp.trans_le hpq).le
  have hsratio : 0 ≤ 1 - p / q :=
    sub_nonneg.mpr ((div_le_one (hp.trans_le hpq)).2 hpq)
  have hinnerNorm : 0 ≤
      localizedSpacetimeRpowNorm (I := I) (M := M) inner f p c d :=
    localizedSpacetimeRpowNorm_nonneg (I := I) (M := M)
      inner f (fun t x => (hfpos t x).le) p c d
  have hfirst :
      localizedSpacetimeRpowNorm (I := I) (M := M) inner f p c d ^ (p / q) ≤
        N ^ (p / q) := Real.rpow_le_rpow hinnerNorm hmono hratio
  calc
    localizedSpacetimeRpowNorm (I := I) (M := M) inner f q c d ≤
        localizedSpacetimeRpowNorm (I := I) (M := M) inner f p c d ^ (p / q) *
          S ^ (1 - p / q) := hinterpolation
    _ ≤ N ^ (p / q) * S ^ (1 - p / q) :=
      mul_le_mul_of_nonneg_right hfirst (Real.rpow_nonneg hS.le _)
    _ = R ^ (1 / p - 1 / q) * N := by
      dsimp only [S]
      rw [Real.mul_rpow (Real.rpow_nonneg hR.le _) hN.le,
        ← Real.rpow_mul hR.le]
      have hsum : p / q + (1 - p / q) = 1 := by ring
      calc
        N ^ (p / q) *
              (R ^ (1 / p * (1 - p / q)) * N ^ (1 - p / q)) =
            R ^ (1 / p * (1 - p / q)) *
              (N ^ (p / q) * N ^ (1 - p / q)) := by ring
        _ = R ^ (1 / p * (1 - p / q)) * N := by
          rw [← Real.rpow_add_of_nonneg hN.le hratio hsratio, hsum,
            Real.rpow_one]
        _ = R ^ (1 / p - 1 / q) * N := by
          congr 1
          field_simp [hp.ne', (hp.trans_le hpq).ne']

end DifferentialGeometry.Analysis.Parabolic.Moser

end
