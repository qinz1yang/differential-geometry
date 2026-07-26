import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckQuasilinearExistence
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.StrongDuhamelBack

/-!
# Strong uniqueness for the mixed Ricci--DeTurck forcing contraction

The concrete Ricci--DeTurck nonlinearity need not have a globally small
`H^{a+2} → H^a` Lipschitz constant.  Its live maximal-regularity solver instead
uses `nemytskiiMixedForcingMap`, which is contractive on a small forcing ball by
the refined critical/subcritical estimate.  This file supplies the matching
uniqueness theorem for two arbitrary fixed points in that ball and combines it
with reverse Duhamel realization for independently supplied strong pairs.
-/

noncomputable section

open Bundle MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- Two fixed points of the concrete mixed-view forcing map in the same force
ball coincide whenever its exported mixed Lipschitz modulus is less than one. -/
theorem mixForce_unique
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {L : ℝ≥0}
    {Nfun : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)}
    (hLip : LipschitzWith L Nfun) {C₁ C₂ : ℝ≥0}
    (hsingle : ∀ (u u' : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)),
      ‖Nfun u - Nfun u'‖ ≤
        (C₁ : ℝ) * max
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u‖
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u'‖ * ‖u - u'‖ +
          (C₂ : ℝ) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u - u')‖)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hsmall :
      (C₁ : ℝ) * Real.sqrt (1 + T) * ρ * (1 + T) +
          (C₂ : ℝ) * (2 * Real.sqrt T) < 1)
    {force₁ force₂ : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T}
    (hball₁ : ‖force₁‖ ≤ ρ) (hball₂ : ‖force₂‖ ≤ ρ)
    (hfix₁ : force₁ = nemytskii (I := I) (M := M) hLip
      (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) force₁))
    (hfix₂ : force₂ = nemytskii (I := I) (M := M) hLip
      (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) force₂)) :
    force₁ = force₂ := by
  have hdist := nemytskiiMixedForcingMap_dist_le (I := I) (M := M)
    g₀ a hLip hsingle hT hT1 hρ force₁ force₂ hball₁ hball₂
  rw [nemytskiiMixedForcingMap_apply, nemytskiiMixedForcingMap_apply,
    ← hfix₁, ← hfix₂] at hdist
  by_contra hne
  have hnorm : 0 < ‖force₁ - force₂‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hgap : 0 <
      (1 - ((C₁ : ℝ) * Real.sqrt (1 + T) * ρ * (1 + T) +
        (C₂ : ℝ) * (2 * Real.sqrt T))) * ‖force₁ - force₂‖ :=
    mul_pos (sub_pos.mpr hsmall) hnorm
  nlinarith

/-- Local uniqueness for two independently supplied zero-trace strong
Ricci--DeTurck perturbation pairs under the same mixed forcing-ball budgets.
The pairs need not have been constructed by the fixed-point solver. -/
theorem deTurckStrong_unique
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {L : ℝ≥0}
    {Nfun : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)}
    (hLip : LipschitzWith L Nfun) {C₁ C₂ : ℝ≥0}
    (hsingle : ∀ (u u' : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)),
      ‖Nfun u - Nfun u'‖ ≤
        (C₁ : ℝ) * max
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u‖
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u'‖ * ‖u - u'‖ +
          (C₂ : ℝ) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u - u')‖)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hsmall :
      (C₁ : ℝ) * Real.sqrt (1 + T) * ρ * (1 + T) +
          (C₂ : ℝ) * (2 * Real.sqrt T) < 1)
    (force₁ force₂ : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (u₁ u₂ : timeH1 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (field₁ field₂ :
      timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) T)
    (htrace₁ : timeH1.trace0 _ T u₁ = 0)
    (htrace₂ : timeH1.trace0 _ T u₂ = 0)
    (hlink₁ :
      timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) field₁ =
        timeH1.toTimeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T u₁)
    (hlink₂ :
      timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) field₂ =
        timeH1.toTimeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T u₂)
    (heq₁ : timeH1.timeDeriv _ T u₁ =
      timeScaleLaplacian (I := I) (M := M) (a : ℝ) field₁ + force₁)
    (heq₂ : timeH1.timeDeriv _ T u₂ =
      timeScaleLaplacian (I := I) (M := M) (a : ℝ) field₂ + force₂)
    (hforce₁ : force₁ = nemytskii (I := I) (M := M) hLip field₁)
    (hforce₂ : force₂ = nemytskii (I := I) (M := M) hLip field₂)
    (hball₁ : ‖force₁‖ ≤ ρ) (hball₂ : ‖force₂‖ ≤ ρ) :
    force₁ = force₂ ∧ field₁ = field₂ ∧ u₁ = u₂ := by
  let u₀ : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) := 0
  have hcompact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  have htrace₁' : timeH1.trace0 _ T u₁ =
      tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) u₀ := by
    simpa only [u₀, map_zero] using htrace₁
  have htrace₂' : timeH1.trace0 _ T u₂ =
      tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) u₀ := by
    simpa only [u₀, map_zero] using htrace₂
  have hfix₁ := strongNemy_fixed (I := I) (M := M) hT hT1 hcompact
    u₀ force₁ u₁ field₁ hLip htrace₁' hlink₁ heq₁ hforce₁
  have hfix₂ := strongNemy_fixed (I := I) (M := M) hT hT1 hcompact
    u₀ force₂ u₂ field₂ hLip htrace₂' hlink₂ heq₂ hforce₂
  have hforces : force₁ = force₂ :=
    mixForce_unique (I := I) (M := M) g₀ a hLip hsingle hT hT1 hρ hsmall
      hball₁ hball₂ hfix₁ hfix₂
  rcases strongPair_eq_duh (I := I) (M := M) hT hT1 hcompact
      u₀ force₁ u₁ field₁ htrace₁' hlink₁ heq₁ with ⟨hfield₁, hu₁⟩
  rcases strongPair_eq_duh (I := I) (M := M) hT hT1 hcompact
      u₀ force₂ u₂ field₂ htrace₂' hlink₂ heq₂ with ⟨hfield₂, hu₂⟩
  refine ⟨hforces, ?_, ?_⟩
  · calc
      field₁ = maxRegDuhamelSolField (I := I) (M := M)
          (a : ℝ) hT hT1 u₀ force₁ := hfield₁
      _ = maxRegDuhamelSolField (I := I) (M := M)
          (a : ℝ) hT hT1 u₀ force₂ := by rw [hforces]
      _ = field₂ := hfield₂.symm
  · calc
      u₁ = maxRegDuhamelMap (I := I) (M := M)
          (a : ℝ) hT hT1 u₀ force₁ := hu₁
      _ = maxRegDuhamelMap (I := I) (M := M)
          (a : ℝ) hT hT1 u₀ force₂ := by rw [hforces]
      _ = u₂ := hu₂.symm

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
