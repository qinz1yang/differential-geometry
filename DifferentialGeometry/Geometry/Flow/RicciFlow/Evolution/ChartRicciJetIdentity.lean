import DifferentialGeometry.Geometry.Curvature.Riemann.Defs
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChristoffelPerturbation
import DifferentialGeometry.Geometry.Operator.HessianTrace
import DifferentialGeometry.Geometry.Connection.ChartBridge.RiemannBasisIdentityOffCentre
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.JetPartialDeriv
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.JetGlueParam
import DifferentialGeometry.Analysis.Calculus.TimeJetEvolution

/-!
# `chartRicci = Φ(jet2 chartGram)` (Lemma 3, the standalone-operator identity)

The geometric coordinate Ricci tensor `chartRicciTensor` equals the abstract Ricci-flow operator
`jetRicci` of `ChartRicciJet.lean` applied to the spatial `2`-jet of the chart-Gram field (taken in
the `Pi` representation `Fin n → Fin n → ℝ`), with the jet partials read along the canonical chart
model basis. This is the identity feeding the Ricci-flow time-jet match (`hglue` corollary (a)):
together with the Ricci-flow PDE it gives the evolution `∂ₜ(chartGram) = Φ(jet2 chartGram)`.

The proof matches the two formulas term-by-term through:
* the jet ↔ entry bridges `fderiv_matEntry` / `fderiv2_matEntry` (jet slots → `partialDeriv`),
* `partialDeriv_chartChristoffel_eq` / `partialDeriv_chartInvGramOnE_eq` (the chart `∂Γ` / `∂(g⁻¹)`
  expansions), and the Cramer inverse `Matrix.of (chartGram) = chartGramMatrix`.

This file currently builds the jet ↔ chart-Gram conversion layer; the Christoffel/Riemann/Ricci
term-matching is layered on top. See `Analysis/Calculus/SmoothExtension/JetGlueParam.md`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix
open DifferentialGeometry.Analysis DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.Integral.Connection

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The chart-Gram field of `g` at `α`, as a `Pi`(matrix)-valued map `E → (Fin n → Fin n → ℝ)`
(the value space of the `jet2` used by the abstract operator `jetRicci`). -/
def chartGramPi (g : SmoothRiemannianMetric I M) (α : M) :
    E → (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) :=
  fun w l m => chartGramOnE (I := I) g α l m w

@[simp] theorem chartGramPi_apply (g : SmoothRiemannianMetric I M) (α : M) (w : E)
    (l m : Fin (Module.finrank ℝ E)) :
    chartGramPi (I := I) g α w l m = chartGramOnE (I := I) g α l m w := rfl

/-- First-derivative jet slot of the chart-Gram equals the chart partial of the entry field. -/
theorem jet2_chartGram_d1 (g : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hG : DifferentiableAt ℝ (chartGramPi (I := I) g α) y)
    (i l m : Fin (Module.finrank ℝ E)) :
    (jet2 (chartGramPi (I := I) g α) y).2.1 (chartModelBasis E i) l m
      = partialDeriv (E := E) i (chartGramOnE (I := I) g α l m) y := by
  simp only [jet2]
  rw [fderiv_matEntry hG (chartModelBasis E i) l m]
  rfl

/-- Second-derivative jet slot of the chart-Gram equals the iterated chart partial of the entry
field. Needs the chart-Gram differentiable near `y` and its derivative differentiable at `y`. -/
theorem jet2_chartGram_d2 (g : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hG1 : ∀ᶠ w in nhds y, DifferentiableAt ℝ (chartGramPi (I := I) g α) w)
    (hG2 : DifferentiableAt ℝ (fun w => fderiv ℝ (chartGramPi (I := I) g α) w) y)
    (m i l j : Fin (Module.finrank ℝ E)) :
    (jet2 (chartGramPi (I := I) g α) y).2.2 (chartModelBasis E m) (chartModelBasis E i) l j
      = partialDeriv (E := E) m (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j)) y := by
  simp only [jet2]
  rw [fderiv2_matEntry hG2 (chartModelBasis E m) (chartModelBasis E i) l j]
  have hinner : (fun w => (fderiv ℝ (chartGramPi (I := I) g α) w) (chartModelBasis E i) l j)
      =ᶠ[nhds y] partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) := by
    filter_upwards [hG1] with w hw
    rw [fderiv_matEntry hw (chartModelBasis E i) l j]
    rfl
  rw [hinner.fderiv_eq]
  rfl

/-- The value jet slot's inverse equals the chart inverse-Gram (Cramer; the value matrix IS the
chart-Gram matrix). -/
theorem jet2_chartGram_invGram (g : SmoothRiemannianMetric I M) (α : M) (y : E)
    (k l : Fin (Module.finrank ℝ E)) :
    (Matrix.of (jet2 (chartGramPi (I := I) g α) y).1)⁻¹ k l = chartInvGramOnE (I := I) g α k l y := by
  have hmat : Matrix.of (jet2 (chartGramPi (I := I) g α) y).1
      = chartGramMatrix (I := I) g α ((extChartAt I α).symm y) := by
    ext a b
    simp only [jet2, chartGramPi, chartGramOnE_def, Matrix.of_apply]
  rw [hmat, chartInvGramOnE_def]
  simp only [chartInvGramMatrix]

/-- **Christoffel identity:** the geometric chart Christoffel symbol equals the abstract
`jetChristoffel` of the chart-Gram jet (along the chart model basis). -/
theorem chartChristoffel_eq_jet (g : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hG : DifferentiableAt ℝ (chartGramPi (I := I) g α) y) (i j k : Fin (Module.finrank ℝ E)) :
    chartChristoffel (I := I) g α i j k y
      = jetChristoffel (chartModelBasis E) (jet2 (chartGramPi (I := I) g α) y) i j k := by
  rw [chartChristoffel_def]
  simp only [jetChristoffel]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [jet2_chartGram_invGram g α y k l, chartInvGramOnE_def,
    jet2_chartGram_d1 g α hG i l j, jet2_chartGram_d1 g α hG j l i, jet2_chartGram_d1 g α hG l i j]

/-- **Christoffel-derivative identity:** the chart partial of the Christoffel symbol equals the
abstract `jetChristoffelDeriv` of the chart-Gram jet. Combines `partialDeriv_chartChristoffel_eq` and
`partialDeriv_chartInvGramOnE_eq` (the chart `∂Γ` / `∂(g⁻¹)` expansions) with the jet conversions. -/
theorem chartChristoffelDeriv_eq_jet (g : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    (hG : DifferentiableAt ℝ (chartGramPi (I := I) g α) y)
    (hG1 : ∀ᶠ w in nhds y, DifferentiableAt ℝ (chartGramPi (I := I) g α) w)
    (hG2 : DifferentiableAt ℝ (fun w => fderiv ℝ (chartGramPi (I := I) g α) w) y)
    (m i j k : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) m (chartChristoffel (I := I) g α i j k) y
      = jetChristoffelDeriv (chartModelBasis E) (jet2 (chartGramPi (I := I) g α) y) m i j k := by
  rw [partialDeriv_chartChristoffel_eq g α m i j k hy]
  simp only [jetChristoffelDeriv]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [partialDeriv_chartInvGramOnE_eq g α y m k l hy]
  simp only [gramBracket, gramBracketDeriv, jet2_chartGram_invGram g α y,
    jet2_chartGram_d1 g α hG, jet2_chartGram_d2 g α hG1 hG2]

/-- **Riemann identity:** the geometric chart Riemann tensor equals the abstract `jetRiemann` of the
chart-Gram jet (assembled from the Christoffel and Christoffel-derivative identities). -/
theorem chartRiemann_eq_jet (g : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    (hG : DifferentiableAt ℝ (chartGramPi (I := I) g α) y)
    (hG1 : ∀ᶠ w in nhds y, DifferentiableAt ℝ (chartGramPi (I := I) g α) w)
    (hG2 : DifferentiableAt ℝ (fun w => fderiv ℝ (chartGramPi (I := I) g α) w) y)
    (i j k l : Fin (Module.finrank ℝ E)) :
    chartRiemannTensor (I := I) g α i j k l y
      = jetRiemann (chartModelBasis E) (jet2 (chartGramPi (I := I) g α) y) i j k l := by
  rw [chartRiemannTensor_def]
  simp only [jetRiemann]
  rw [chartChristoffelDeriv_eq_jet g α hy hG hG1 hG2 j i k l,
    chartChristoffelDeriv_eq_jet g α hy hG hG1 hG2 k i j l]
  congr 1
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [chartChristoffel_eq_jet g α hG j m l, chartChristoffel_eq_jet g α hG i k m,
    chartChristoffel_eq_jet g α hG k m l, chartChristoffel_eq_jet g α hG i j m]

/-- **Ricci identity (Lemma 3):** the geometric chart Ricci tensor equals the abstract `jetRicci` of
the chart-Gram `2`-jet. The contraction `∑_j` of the Riemann identity. -/
theorem chartRicci_eq_jet (g : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    (hG : DifferentiableAt ℝ (chartGramPi (I := I) g α) y)
    (hG1 : ∀ᶠ w in nhds y, DifferentiableAt ℝ (chartGramPi (I := I) g α) w)
    (hG2 : DifferentiableAt ℝ (fun w => fderiv ℝ (chartGramPi (I := I) g α) w) y)
    (i k : Fin (Module.finrank ℝ E)) :
    chartRicciTensor (I := I) g α i k y
      = jetRicci (chartModelBasis E) (jet2 (chartGramPi (I := I) g α) y) i k := by
  rw [chartRicciTensor_def]
  simp only [jetRicci]
  exact Finset.sum_congr rfl (fun j _ => chartRiemann_eq_jet g α hy hG hG1 hG2 i j k j)

/-- **Ricci-flow operator identity:** `Φ(jet2 chartGram) = -2·chartRicci`. Together with the
Ricci-flow PDE this gives the chart-Gram evolution `∂ₜ(chartGram) = Φ(jet2 chartGram)` fed to
`jetMatch_of_evolution` (corollary (a)). -/
theorem jetRicciFlow_chartGram (g : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    (hG : DifferentiableAt ℝ (chartGramPi (I := I) g α) y)
    (hG1 : ∀ᶠ w in nhds y, DifferentiableAt ℝ (chartGramPi (I := I) g α) w)
    (hG2 : DifferentiableAt ℝ (fun w => fderiv ℝ (chartGramPi (I := I) g α) w) y)
    (i k : Fin (Module.finrank ℝ E)) :
    jetRicciFlow (chartModelBasis E) (jet2 (chartGramPi (I := I) g α) y) i k
      = -2 * chartRicciTensor (I := I) g α i k y := by
  rw [jetRicciFlow, chartRicci_eq_jet g α hy hG hG1 hG2 i k]

/-- **Time-jet match for two Ricci-flow chart-Gram families (corollary (a) applied).** Two metric
time-families `g₁`, `g₂` whose chart-Gram fields are jointly `C∞` on the closed half-slabs (the BBS /
DeTurck gates), are positive-definite at the seam, satisfy the chart-Gram Ricci-flow evolution
`∂ₜ(chartGram) = Φ(jet2 chartGram)` (`Φ = jetRicciFlow`), and agree at the seam, have EQUAL one-sided
normal time-jets there. This feeds the joint hyperplane splice (`contDiffOn_glue_of_jet_param`'s
`hjet`). The `hΦ` hypothesis of `jetMatch_of_evolution` is discharged by `contDiffAt_jetRicciFlow`. -/
theorem ricciFlowChartGram_jetMatch (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) (α : M)
    {V : Set E} {sL sR : Set ℝ}
    (hsL : UniqueDiffOn ℝ sL) (haccL : sL ⊆ closure (interior sL)) (h0L : (0 : ℝ) ∈ sL)
    (hsR : UniqueDiffOn ℝ sR) (haccR : sR ⊆ closure (interior sR)) (h0R : (0 : ℝ) ∈ sR)
    (hV : IsOpen V)
    (hGL : ContDiffOn ℝ ∞ (Function.uncurry (fun t => chartGramPi (I := I) (g₁ t) α)) (sL ×ˢ V))
    (hGR : ContDiffOn ℝ ∞ (Function.uncurry (fun t => chartGramPi (I := I) (g₂ t) α)) (sR ×ˢ V))
    (hcurveL : ∀ w ∈ V,
      ContDiffWithinAt ℝ ∞ (fun t => jet2 (chartGramPi (I := I) (g₁ t) α) w) sL 0)
    (hcurveR : ∀ w ∈ V,
      ContDiffWithinAt ℝ ∞ (fun t => jet2 (chartGramPi (I := I) (g₂ t) α) w) sR 0)
    (hdet : ∀ w ∈ V, (Matrix.of (jet2 (chartGramPi (I := I) (g₁ 0) α) w).1).det ≠ 0)
    (hevolL : ∀ t ∈ sL, ∀ w ∈ V, derivWithin (fun s => chartGramPi (I := I) (g₁ s) α w) sL t
      = jetRicciFlow (chartModelBasis E) (jet2 (chartGramPi (I := I) (g₁ t) α) w))
    (hevolR : ∀ t ∈ sR, ∀ w ∈ V, derivWithin (fun s => chartGramPi (I := I) (g₂ s) α w) sR t
      = jetRicciFlow (chartModelBasis E) (jet2 (chartGramPi (I := I) (g₂ t) α) w))
    (hbdry : Set.EqOn (chartGramPi (I := I) (g₁ 0) α) (chartGramPi (I := I) (g₂ 0) α) V) :
    ∀ (n : ℕ), ∀ w ∈ V,
      iteratedDerivWithin n (fun s => chartGramPi (I := I) (g₁ s) α w) sL 0
        = iteratedDerivWithin n (fun s => chartGramPi (I := I) (g₂ s) α w) sR 0 :=
  jetMatch_of_evolution hsL haccL h0L hsR haccR h0R hV hGL hGR
    (fun w hw => contDiffAt_jetRicciFlow (chartModelBasis E) (hdet w hw))
    hcurveL hcurveR hevolL hevolR hbdry

/-- **Chart-Gram evolution in `Φ`-form (discharges `hevol`).** From the chart-Gram entry Ricci-flow
PDE `∂ₜ(chartGram_{ik}) = −2·chartRicci_{ik}` (which the construction supplies from the metric PDE
`∂ₜg = −2Ric` via `chartGramMatrix = g.inner(chartBasisVecFiber)` and the off-centre α-chart Ricci
bridge), the `Pi`-valued chart-Gram satisfies `∂ₜ(chartGram) = Φ(jet2 chartGram)` with `Φ = jetRicciFlow`.
The `Pi` time-derivative distributes over the entries (`hasDerivWithinAt_pi`), then `jetRicciFlow_chartGram`
converts `−2·chartRicci` to `Φ`. -/
theorem chartGramEvolution_of_pde (g : ℝ → SmoothRiemannianMetric I M) (α : M) {y : E} {sL : Set ℝ}
    {t : ℝ} (hsL : UniqueDiffWithinAt ℝ sL t)
    (hy : y ∈ interior (extChartAt I α).target)
    (hG : DifferentiableAt ℝ (chartGramPi (I := I) (g t) α) y)
    (hG1 : ∀ᶠ w in nhds y, DifferentiableAt ℝ (chartGramPi (I := I) (g t) α) w)
    (hG2 : DifferentiableAt ℝ (fun w => fderiv ℝ (chartGramPi (I := I) (g t) α) w) y)
    (hpde : ∀ i k : Fin (Module.finrank ℝ E),
      HasDerivWithinAt (fun s => chartGramOnE (I := I) (g s) α i k y)
        (-2 * chartRicciTensor (I := I) (g t) α i k y) sL t) :
    derivWithin (fun s => chartGramPi (I := I) (g s) α y) sL t
      = jetRicciFlow (chartModelBasis E) (jet2 (chartGramPi (I := I) (g t) α) y) := by
  have hderiv : HasDerivWithinAt (fun s => chartGramPi (I := I) (g s) α y)
      (fun i k => -2 * chartRicciTensor (I := I) (g t) α i k y) sL t := by
    rw [hasDerivWithinAt_pi]
    intro i
    rw [hasDerivWithinAt_pi]
    intro k
    exact hpde i k
  rw [hderiv.derivWithin hsL]
  funext i k
  exact (jetRicciFlow_chartGram (g t) α hy hG hG1 hG2 i k).symm

/-- **Chart-Gram entry PDE from the metric PDE.** From the Ricci-flow metric PDE evaluated on the
fixed (time-independent) chart-basis fiber vectors at `ϕ_α⁻¹ y` — `∂ₜ((g s).inner v_i v_k) =
−2·ricciTensor (g t) v_i v_k` — derive the chart-Gram entry PDE `∂ₜ(chartGram_{ik}) =
−2·chartRicci_{ik}` (the `hpde` hypothesis of `chartGramEvolution_of_pde`). `chartGramMatrix = g.inner
(chartBasisVecFiber)` makes the functions definitionally equal; the off-centre α-chart Ricci bridge
`ricciTensor_chartBasisVec_alpha_eq` (needs `ϕ_α⁻¹ y ∈ chartLeviCivitaGoodSet α`) converts the
derivative. -/
theorem chartGramEntryPDE_of_metricPDE [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    (g : ℝ → SmoothRiemannianMetric I M) (α : M) {y : E} {sL : Set ℝ} {t : ℝ}
    (hgs : (extChartAt I α).symm y ∈ chartLeviCivitaGoodSet (I := I) α)
    (hyt : extChartAt I α ((extChartAt I α).symm y) = y) (i k : Fin (Module.finrank ℝ E))
    (hmpde : HasDerivWithinAt
      (fun s => (g s).inner ((extChartAt I α).symm y)
        (chartBasisVecFiber (I := I) α i ((extChartAt I α).symm y))
        (chartBasisVecFiber (I := I) α k ((extChartAt I α).symm y)))
      (-2 * ricciTensor (I := I) (g t) ((extChartAt I α).symm y)
        (chartBasisVecFiber (I := I) α i ((extChartAt I α).symm y))
        (chartBasisVecFiber (I := I) α k ((extChartAt I α).symm y))) sL t) :
    HasDerivWithinAt (fun s => chartGramOnE (I := I) (g s) α i k y)
      (-2 * chartRicciTensor (I := I) (g t) α i k y) sL t := by
  have hbridge : ricciTensor (I := I) (g t) ((extChartAt I α).symm y)
        (chartBasisVecFiber (I := I) α i ((extChartAt I α).symm y))
        (chartBasisVecFiber (I := I) α k ((extChartAt I α).symm y))
      = chartRicciTensor (I := I) (g t) α i k y := by
    rw [ricciTensor_chartBasisVec_alpha_eq (g t) α i k hgs, hyt]
  rw [← hbridge]
  exact hmpde

/-- **The glued chart-Gram is jointly `C∞` across the seam (the `gram_smooth` content).** Given two
metric families `g₁`, `g₂` whose chart-Gram fields are jointly `C∞` on the half-slabs `Iic 0 ×ˢ V` /
`Ici 0 ×ˢ V` (the BBS / DeTurck gates), positive-definite at the seam, satisfying the chart-Gram
Ricci-flow evolution and agreeing at the seam, the spliced family
`if t ≤ 0 then chartGram(g₁) else chartGram(g₂)` is `C∞` on `univ ×ˢ V`. This is
`contDiffOn_glue_of_jet_param` (the joint hyperplane splice) fed by `ricciFlowChartGram_jetMatch`
(the time-jet match). The two cross-lane gates discharge `hL`/`hR`/`hcurve`. -/
theorem chartGramGlue_contDiffOn (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) (α : M) {V : Set E}
    (hV : IsOpen V)
    (hL : ContDiffOn ℝ ∞ (Function.uncurry (fun t => chartGramPi (I := I) (g₁ t) α))
      (Set.Iic 0 ×ˢ V))
    (hR : ContDiffOn ℝ ∞ (Function.uncurry (fun t => chartGramPi (I := I) (g₂ t) α))
      (Set.Ici 0 ×ˢ V))
    (hcurveL : ∀ w ∈ V,
      ContDiffWithinAt ℝ ∞ (fun t => jet2 (chartGramPi (I := I) (g₁ t) α) w) (Set.Iic 0) 0)
    (hcurveR : ∀ w ∈ V,
      ContDiffWithinAt ℝ ∞ (fun t => jet2 (chartGramPi (I := I) (g₂ t) α) w) (Set.Ici 0) 0)
    (hdet : ∀ w ∈ V, (Matrix.of (jet2 (chartGramPi (I := I) (g₁ 0) α) w).1).det ≠ 0)
    (hevolL : ∀ t ∈ Set.Iic (0 : ℝ), ∀ w ∈ V,
      derivWithin (fun s => chartGramPi (I := I) (g₁ s) α w) (Set.Iic 0) t
        = jetRicciFlow (chartModelBasis E) (jet2 (chartGramPi (I := I) (g₁ t) α) w))
    (hevolR : ∀ t ∈ Set.Ici (0 : ℝ), ∀ w ∈ V,
      derivWithin (fun s => chartGramPi (I := I) (g₂ s) α w) (Set.Ici 0) t
        = jetRicciFlow (chartModelBasis E) (jet2 (chartGramPi (I := I) (g₂ t) α) w))
    (hbdry : Set.EqOn (chartGramPi (I := I) (g₁ 0) α) (chartGramPi (I := I) (g₂ 0) α) V) :
    ContDiffOn ℝ ∞
      (fun q : ℝ × E => if q.1 ≤ 0 then Function.uncurry (fun t => chartGramPi (I := I) (g₁ t) α) q
        else Function.uncurry (fun t => chartGramPi (I := I) (g₂ t) α) q)
      (Set.univ ×ˢ V) := by
  have heqL : closure (interior (Set.Iic (0 : ℝ))) = Set.Iic 0 := by rw [interior_Iic, closure_Iio]
  have heqR : closure (interior (Set.Ici (0 : ℝ))) = Set.Ici 0 := by rw [interior_Ici, closure_Ioi]
  refine SmoothExtension.contDiffOn_glue_of_jet_param hV _ _ hL hR (fun i w hw => ?_)
  exact ricciFlowChartGram_jetMatch g₁ g₂ α (uniqueDiffOn_Iic 0) heqL.ge (Set.mem_Iic.mpr le_rfl)
    (uniqueDiffOn_Ici 0) heqR.ge (Set.mem_Ici.mpr le_rfl) hV hL hR hcurveL hcurveR hdet
    hevolL hevolR hbdry i w hw

end DivergenceTheorem
end Integral
end DifferentialGeometry

end
