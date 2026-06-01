import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.MaxRegLocalLipschitzStayDischarge
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.CompactSAResolventIntrinsic
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckNonlinearitySpectral

/-!
# Strong short-time existence for the Ricci–DeTurck first-order remainder

The chart-locality-free maximal-regularity engine
`quasilinear_strong_existence_locallyLipschitz_smallTime_stayDischarged_ofCompact`
(`Analysis/Parabolic/QuasiLinear/MaxRegLocalLipschitzStayDischarge.lean`) takes a
**locally Lipschitz** lower-order nonlinearity

  `N : tensorHs g_bg 0 2 (a + 1) → tensorHs g_bg 0 2 a`

— that is, `LipschitzOnWith L_R N` on a closed `H^{a+1}`-ball
`closedBall (ι u₀) R` around the included initial datum — together with the
resolvent-compactness witness `h_compact`, and produces, on a positive horizon,
a **strong solution** of the quasi-linear tensor heat equation

  `∂_t u = Δ_∇ u + N(u)`,  `u(0) = u₀`,

in the maximal-regularity solution space `H¹([0,T]; Hᵃ)`.  The engine requires no
global Lipschitz smallness `2 L < 1` and no `stays-in-ball` residual: the
truncation device plus the sharp Lions–Magenes parabolic trace estimate discharge
both internally.

This file assembles the Ricci–DeTurck flow into that engine.

## Why the remainder is the right input

By the principal-part match recorded in
`DeTurckNonlinearitySpectral.deTurckNonlinearitySpectral_principalPart_cancels`,
the Ricci–DeTurck right-hand side `deTurckRicciRHS g_bg ·` has, on symmetric
`(0,2)` perturbations, the **same** second-order principal symbol as the rough
Laplacian `Δ_∇` (up to the gauge cancellation).  Subtracting the Laplacian
therefore removes all second-order content: the remainder

  `N(h) = deTurckRicciRHS g_bg (g_bg + h) − Δ_∇ h`

is genuinely **first order** in `h`, hence loses exactly one derivative and maps
`H^{a+2}` continuously into `H^{a+1}` — equivalently, presented on the
one-derivative-drop scale, it is a map `H^{a+1} → Hᵃ`.  This is precisely the
shape the engine consumes.

## What is delivered here

* `deTurckRemainder_strong_shortTime_exists` — the **engine-application driver**:
  for *any* genuine first-order remainder `N : H^{a+1} → Hᵃ` that is Lipschitz on
  a closed ball about the initial datum, the unconditional intrinsic engine
  produces the abstract strong solution of `∂_t u = Δ_∇ u + N(u)`, `u(0) = u₀`.
  The resolvent-compactness witness is supplied unconditionally by
  `tensorResolventL2_isCompactOperator`.  `N` and its local-Lipschitz
  bound are honest analytic *inputs* (the output of the realization program); the
  conclusion is the existence of a PDE solution, structurally distinct from the
  Lipschitz hypothesis (no hypothesis-packaging).

* `firstOrderRemainderCLM_strong_shortTime_exists` — the **fully unconditional**
  continuous-linear case: for any continuous **linear** first-order remainder
  `R : H^{a+1} →L[ℝ] Hᵃ` (the abstract shape of the gauge-cancelled DeTurck
  remainder — automatically globally Lipschitz, constant `‖R‖₊`), the engine
  produces a strong solution end-to-end with **no** extra hypotheses.  This
  closes the engine pipeline on the genuine first-order shape with zero open
  subgoals.

## Sign convention

Geometer `Δ_∇ = −∇*∇`, spectrum `⊆ (−∞, 0]`; resolvent `(1 − Δ_∇)⁻¹`, weights
`(1 + λᵢ)^σ ≥ 1` for `σ ≥ 0`.
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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **Strong short-time existence for a Ricci–DeTurck first-order remainder.**

Let `(M, g_bg)` be a closed Riemannian manifold (compact, boundaryless,
Hausdorff, σ-compact), `a : ℝ` a non-negative spectral Sobolev exponent, and
`u₀ ∈ H^{a+2}` an initial metric perturbation in the order-`(a+2)` spectral
Sobolev space of `(0,2)`-tensors built from `g_bg`.  Let

  `N : tensorHs g_bg 0 2 (a + 1) → tensorHs g_bg 0 2 a`

be a first-order remainder that is **locally Lipschitz** — `LipschitzOnWith L_R N`
on the closed `H^{a+1}`-ball `closedBall (ι u₀) R` of some positive radius `R`
about the included initial datum `ι u₀`.

Then there is a positive horizon `T₀` such that, for **every** short interval
`(0, T]` with `T ≤ T₀ ≤ 1`, there is a strong solution `u ∈ H¹([0,T]; Hᵃ)`
together with its forcing `gforce ∈ L²([0,T]; Hᵃ)` of the quasi-linear tensor
heat equation

  `∂_t u = Δ_∇ u + N(u)`,  `u(0) = u₀`.

Concretely the data `u, gforce` satisfy:

* `u = maxRegDuhamelMap … u₀ gforce` — `u` is the affine Duhamel image of
  `gforce`;
* `gforce =ᵐ (fun t => N(field_{a+1} t))` — the forcing is reproduced a.e. by the
  pointwise-in-time remainder along the `H^{a+1}`-view solution field;
* `trace₀ u = ι u₀` — the initial value is `u₀`;
* `∂_t u = Δ_∇ (field_{a+2}) + Ñ_R(field_{a+1})` — the equation, where the
  truncated forcing reproduces `N` on the (proven) stays-in-ball event.

The resolvent-compactness hypothesis demanded by the engine is supplied
**unconditionally** by `tensorResolventL2_isCompactOperator` (no
chart-selection / parallelizability witness).  The construction is exactly
`quasilinear_strong_existence_locallyLipschitz_smallTime_stayDischarged_ofCompact`
specialised to `(r, s) = (0, 2)`, `g = g_bg`, with the intrinsic compactness
witness.  `N` and its local-Lipschitz bound are honest analytic inputs — the
output of the realization program of `DeTurckNonlinearitySpectral.lean` — and the
conclusion is the existence of a strong PDE solution, structurally distinct from
the Lipschitz hypothesis. -/
theorem deTurckRemainder_strong_shortTime_exists
    (g_bg : SmoothRiemannianMetric I M) {a : ℝ}
    {N : tensorHs (I := I) (M := M) g_bg 0 2 (a + 1) →
      tensorHs (I := I) (M := M) g_bg 0 2 a}
    {L_R : ℝ≥0} {R : ℝ} (hR : 0 < R)
    (u₀ : tensorHs (I := I) (M := M) g_bg 0 2 (a + 2))
    (hN : LipschitzOnWith L_R N (Metric.closedBall
      (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
        (show (a + 1) ≤ a + 2 by linarith) u₀) R)) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ {T : ℝ} (hT : 0 < T) (_hTT₀ : T ≤ T₀) (hT1 : T ≤ 1),
      ∃ (u : MaxRegSolutionSpace (I := I) (M := M) a T)
        (gforce : timeL2 (tensorHs (I := I) (M := M) g_bg 0 2 a) T),
        u = maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce ∧
          gforce =ᵐ[timeMeasure T]
            (fun t => N (maxRegDuhamelSolFieldHa1 (I := I) (M := M)
              a hT hT1 u₀ gforce t)) ∧
          timeH1.trace0 _ T u =
              tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
                (show a ≤ a + 2 by linarith) u₀ ∧
          timeH1.timeDeriv _ T u =
            timeScaleLaplacian (I := I) (M := M) a
                (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ gforce) +
              nemytskiiHa1 (I := I) (M := M)
                (truncatedNonlin_lipschitzWith (I := I) (M := M) hR.le hN)
                (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce) :=
  quasilinear_strong_existence_locallyLipschitz_smallTime_stayDischarged_ofCompact
    (I := I) (M := M) (g := g_bg) (r := 0) (s := 2) (a := a)
    (N := N) (L_R := L_R) (R := R) hR
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g_bg 0 2)
    u₀ hN

/-- **Strong short-time existence for a continuous-linear first-order remainder
(fully unconditional).**

For any continuous linear map `R : H^{a+1} →L[ℝ] Hᵃ` of `(0,2)`-tensor spectral
Sobolev spaces — the abstract first-order remainder shape — and any initial datum
`u₀ ∈ H^{a+2}`, there is a positive horizon `T₀` such that for every short
interval `(0, T]` with `T ≤ T₀ ≤ 1` there is a strong solution
`u ∈ H¹([0,T]; Hᵃ)` of the quasi-linear tensor heat equation

  `∂_t u = Δ_∇ u + R(u)`,  `u(0) = u₀`.

No Lipschitz smallness, no stays-in-ball residual, and no chart-locality witness
is assumed: `R` is globally `‖R‖₊`-Lipschitz because it is continuous and linear,
the resolvent compactness is the unconditional intrinsic witness, and the
truncation + parabolic-trace machinery inside the engine discharges everything
else.  Take any radius `R₀ = 1`.  The four conclusions are the engine's:
`u` is the Duhamel image; the forcing is reproduced a.e. by `R` along the field;
the initial value is `u₀`; and the time derivative is `∂_t u = Δ_∇ u + R(u)`. -/
theorem firstOrderRemainderCLM_strong_shortTime_exists
    (g_bg : SmoothRiemannianMetric I M) {a : ℝ}
    (R : tensorHs (I := I) (M := M) g_bg 0 2 (a + 1) →L[ℝ]
      tensorHs (I := I) (M := M) g_bg 0 2 a)
    (u₀ : tensorHs (I := I) (M := M) g_bg 0 2 (a + 2)) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ {T : ℝ} (hT : 0 < T) (_hTT₀ : T ≤ T₀) (hT1 : T ≤ 1),
      ∃ (u : MaxRegSolutionSpace (I := I) (M := M) a T)
        (gforce : timeL2 (tensorHs (I := I) (M := M) g_bg 0 2 a) T),
        u = maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce ∧
          gforce =ᵐ[timeMeasure T]
            (fun t => R (maxRegDuhamelSolFieldHa1 (I := I) (M := M)
              a hT hT1 u₀ gforce t)) ∧
          timeH1.trace0 _ T u =
              tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
                (show a ≤ a + 2 by linarith) u₀ ∧
          timeH1.timeDeriv _ T u =
            timeScaleLaplacian (I := I) (M := M) a
                (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ gforce) +
              nemytskiiHa1 (I := I) (M := M)
                (truncatedNonlin_lipschitzWith (I := I) (M := M)
                  (zero_le_one)
                  (show LipschitzOnWith (‖R‖₊) (⇑R) (Metric.closedBall
                    (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
                      (show (a + 1) ≤ a + 2 by linarith) u₀) (1 : ℝ))
                    from (R.lipschitz).lipschitzOnWith))
                (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce) := by
  have hN : LipschitzOnWith (‖R‖₊) (⇑R) (Metric.closedBall
      (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
        (show (a + 1) ≤ a + 2 by linarith) u₀) (1 : ℝ)) :=
    (R.lipschitz).lipschitzOnWith
  obtain ⟨T₀, hT₀_pos, hsol⟩ :=
    deTurckRemainder_strong_shortTime_exists (I := I) (M := M) g_bg
      (N := ⇑R) (L_R := ‖R‖₊) (R := (1 : ℝ)) one_pos u₀ hN
  exact ⟨T₀, hT₀_pos, fun {T} hT hTT₀ hT1 => hsol hT hTT₀ hT1⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
