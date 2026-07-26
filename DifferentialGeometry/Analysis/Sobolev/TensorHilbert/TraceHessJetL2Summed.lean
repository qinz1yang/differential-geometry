import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffL2JetMoser

/-!
# Summed data-weighted jet-L2 bound for the trace-Hessian coefficient field

This file proves the **trace-Hessian coefficient** analogue of the arm / connDiff / Lie summed
bounds (`ArmBaseCoeffJetL2Summed.lean`, `ConnDiffJetL2Summed.lean`, `LieFieldJetL2Summed.lean`): a
single top-separated data-weighted jet-L2 bound for the `(4,2)` field
`traceHessianCoeff g₀ g₁` (= `ricciCometricFourTraceCastG0`), realized at the convex family
`g₁ = realizedFam g₀ T T' hδ hδ' s`.

The end shape (matching the sibling constituents, both windows landing at order `a+2`):
```
∑_{i ≤ a} ‖∇^i (traceHessianCoeff g₀ (realizedFam …))‖²
  ≤ Ktop · (∑_{j < a+2} (‖∇^j T‖² + ‖∇^j T'‖²))
  +  Kc  · (1 + ∑_{j < a+2} (‖∇^j T‖² + ‖∇^j T'‖²))
```

## Why `Ktop = 0` here (structural, NOT a mask)

Unlike the connection-difference / Lie / curvature-arm constituents, `traceHessianCoeff g₀ g₁` is a
purely **algebraic** coefficient in the cometric `g₁⁻¹` (`traceHessianFib = cometricDoubleTraceFib ∘
domDomCongrFib`; see `RicciLinearizationArmFields.lean`).  It carries **no covariant-derivative
gain**: its committed jet bound routes through the metric-inverse difference `gInvDiffSlotCoeff`
(`traceHessianCoeff_sub_background_jetL2_le_gInvDiffSlotCoeff_jetL2`,
`RemainderCoeffL2JetMoser.lean:365`), whose order-`i` jet is controlled by `∇^{≤i} P` — the *same*
order, with no shift.  Consequently the field produces **no top-window difference term at order
`a+1`/`a+2`** (the window the `Ktop` discipline protects).  Its highest-order contribution sits at
order `≤ a`, strictly below the protected window, and is legitimately part of the low/`Kc` data.  So
the honest top-split coefficient is `Ktop = 0` (trivially `(g₀,hδ₀)`-only): there is nothing at the
top for `R` to hide in.  This is the reason the three `(0,4)` curvature-difference engines
(`riemannLoweredBackgroundDifference` / `ricEndoBackgroundDifferenceField` /
`riemannG1LoweringDifference`) — which are for the *curvature* / kernel side of the linearization and
do carry a genuine `∇^{i+2}` top — do **not** enter here: there is no committed identity relating
`traceHessianCoeff` to them, and none is mathematically expected.

The full accounting (including the identified data-weighted refinement of `Kc`, which needs the
metric-inverse tame machinery and is a larger follow-up) is in `TraceHessJetL2Summed.md` and
`RemainderCoeffTopSeparated.md`.  This is constituent 5-of-5 of the data-weighted threeArm precursor
(R1τ item (2)); the black box `ricci_flow_unif_existence` remains 0%.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.style.setOption false

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
  (gFibreOpBound ccTensorBilinSymm ccTensorBilin ccTensorBilin_apply ccTensorModel
    ccTensorMultilinear ccTensorBilinSymm_contMDiff ccTensorBilinSymm_apply ccTensorBilinSymm_symm)
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedFam)

/-! ### Pure `Finset` summation helpers (no geometry). -/

/-- Shifted-range domination for a nonnegative sequence (copied verbatim from
`ConnDiffJetL2Summed.lean`, itself from `ArmBaseCoeffJetL2Summed.lean`). -/
private lemma sum_shift_le (g : ℕ → ℝ) (hg : ∀ j, 0 ≤ g j) (m c : ℕ) :
    ∑ i ∈ Finset.range m, g (i + c) ≤ ∑ j ∈ Finset.range (m + c), g j := by
  classical
  have hsub :
      (Finset.range m).map ⟨fun i => i + c, fun a b h => by simpa using h⟩ ⊆
        Finset.range (m + c) := by
    intro j hj
    rw [Finset.mem_map] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    rw [Finset.mem_range] at hi ⊢
    simp only [Function.Embedding.coeFn_mk]
    omega
  calc ∑ i ∈ Finset.range m, g (i + c)
      = ∑ j ∈ (Finset.range m).map ⟨fun i => i + c, fun a b h => by simpa using h⟩, g j := by
        rw [Finset.sum_map]; rfl
    _ ≤ ∑ j ∈ Finset.range (m + c), g j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hg j)

/-- Summation of a per-order top-separated bound with **independent** top offset `p` and low-window
offset `q` (copied verbatim from `ConnDiffJetL2Summed.lean`).  The trace-Hessian field uses `p = 1`,
`q = 2` to land in the same window shape as the connDiff / Lie constituents (its own `Ktop = 0`, so
the `p` value is immaterial to the bound but is kept for a uniform drop-in shape). -/
private lemma jetL2_sum_lowShift
    (a p q : ℕ) (Ktop : ℝ) (hKtop : 0 ≤ Ktop) (Kc : ℕ → ℝ) (hKc : ∀ i, 0 ≤ Kc i)
    (f w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hper : ∀ i, i ≤ a →
        f i ≤ Ktop * w (i + p) + Kc i * (1 + ∑ j ∈ Finset.range (i + q), w j)) :
    ∑ i ∈ Finset.range (a + 1), f i ≤
      Ktop * (∑ j ∈ Finset.range (a + 1 + p), w j) +
      (∑ i ∈ Finset.range (a + 1), Kc i) * (1 + ∑ j ∈ Finset.range (a + q), w j) := by
  refine le_trans (Finset.sum_le_sum (fun i hi =>
    hper i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))) ?_
  rw [Finset.sum_add_distrib]
  have hB : (∑ i ∈ Finset.range (a + 1), Ktop * w (i + p)) ≤
      Ktop * ∑ j ∈ Finset.range (a + 1 + p), w j := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_shift_le w hw (a + 1) p) hKtop
  have hA : (∑ i ∈ Finset.range (a + 1), Kc i * (1 + ∑ j ∈ Finset.range (i + q), w j)) ≤
      (∑ i ∈ Finset.range (a + 1), Kc i) * (1 + ∑ j ∈ Finset.range (a + q), w j) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hi' : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    refine mul_le_mul_of_nonneg_left ?_ (hKc i)
    have hsub : Finset.range (i + q) ⊆ Finset.range (a + q) := by
      intro x hx; rw [Finset.mem_range] at hx ⊢; omega
    have hss : ∑ j ∈ Finset.range (i + q), w j ≤ ∑ j ∈ Finset.range (a + q), w j :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hw j)
    linarith
  linarith [hA, hB]

/-! ### Geometry setting. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ### `realizedFam` per-order and summed top-separated bounds (`Ktop = 0`). -/

set_option linter.unusedVariables false in
/-- **Per-order** top-separated jet-L2 bound for the trace-Hessian coefficient field, realized at the
convex family.  Since the coefficient carries no derivative gain, the top-split coefficient is
`Ktop = 0` (the top window `∇^{i+1}` term drops out); the ball-uniform per-order constant of
`traceHessianCoeff_realizedFam_jetL2_perOrder_ballUniform` becomes the lumped low coefficient `Kc i`
(house `R`-pattern).  The window shape (top `i+1`, low `i+2`) is kept identical to the connDiff / Lie
constituents so this is a uniform drop-in for the downstream threeArm decomposition. -/
theorem traceHessianCoeff_realizedFam_jetL2_perOrder_topSeparated
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (traceHessianCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤
            Ktop * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T'‖ ^ 2) +
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  obtain ⟨P, hP_nn, hP⟩ :=
    traceHessianCoeff_realizedFam_jetL2_perOrder_ballUniform
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨0, le_refl 0, P, hP_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs i hi
  have hb := hP T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs
  have hlow_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
      (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
    Finset.sum_nonneg (fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have htop_nn : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T‖ ^ 2 +
      ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T'‖ ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  nlinarith [hb, hP_nn i, hlow_nn, htop_nn,
    mul_nonneg (hP_nn i) hlow_nn]

set_option linter.unusedVariables false in
/-- **Summed** top-separated jet-L2 bound for the trace-Hessian coefficient field (constituent
5-of-5 of the data-weighted threeArm precursor).  Summing the per-order bound over `i ≤ a` lands both
data windows at order `a+2`, with `Ktop = 0` (structural — the coefficient has no derivative gain)
and `Kc = ∑_{i≤a} Kc_perOrder i` following the accepted house `R`-pattern. -/
theorem traceHessianCoeff_realizedFam_jetL2_summed_topSeparated
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℝ, 0 ≤ Kc ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ∑ i ∈ Finset.range (a + 1),
              ‖iteratedCovGrad (I := I) g₀ 4 2 i
                (traceHessianCoeff (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤
            Ktop * (∑ j ∈ Finset.range (a + 2),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) +
            Kc * (1 + ∑ j ∈ Finset.range (a + 2),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  obtain ⟨Ktop, hKtop_nn, Kc, hKc_nn, hper⟩ :=
    traceHessianCoeff_realizedFam_jetL2_perOrder_topSeparated
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨Ktop, hKtop_nn, ∑ i ∈ Finset.range (a + 1), Kc i,
    Finset.sum_nonneg (fun i _ => hKc_nn i), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs
  exact jetL2_sum_lowShift a 1 2 Ktop hKtop_nn Kc hKc_nn
    (fun i => ‖iteratedCovGrad (I := I) g₀ 4 2 i
      (traceHessianCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2)
    (fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)
    (fun j => add_nonneg (sq_nonneg _) (sq_nonneg _))
    (fun i hi => hper T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs i hi)

end DifferentialGeometry.Integral.Connection
