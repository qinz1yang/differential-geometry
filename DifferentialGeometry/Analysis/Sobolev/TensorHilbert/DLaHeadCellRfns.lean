import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffL2JetMoser
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciConnDiffOrder1TameEnvelope

/-!
# Pointwise (`rfns`) top-separated head cell for the DLa 8-summand triangle

The DeTurck-Lie DLa coefficient field `deTurckLieDLaCoeffField g₀ g₁ g_bg : SmoothCcTensor g₀ 2 2`
is (through the private pairTrace/bicontraction bridge in `DeTurckLieKernelL2JetBound.lean`) built
from the raised `(1,3)` kernel `dLaKernelRaisedCc`, which splits into **8 summands**
```
A1 = covGrad (connDiffSection g₁ g₀)            -- the isolated top
A2 = covGrad (connDiffSection g_bg g₀)          -- g_bg, T-independent ⇒ Kc
+ 6 dLaQuadCc terms                              -- product-order i+2, factors ≤ ∇^{i+1}T ⇒ Kc
```
The committed reduction `exists_rfns_dLaKernelRaised_tgrid` proves this triangle **grid-collapsed**
(the `A1` head is dissolved into a raw `∇T`-product grid via the connDiffSection *grid* engine at
order `i+1`).  Top-separating the field keeps the `A1` head cell separate: for `A1` alone one uses
the connDiffSection *top-separated* engine `rfns_iteratedCovGrad_connDiffSection_topSeparated_le` at
order `i+1` in place of the grid engine, giving an `R`-independent top coefficient on `∇^{i+2}P`.

This file provides that **pointwise head cell** as a standalone reusable lemma.  It is the
un-integrated (`riemannianFiberNormSq`-level, pointwise in `x`) form of the head atom proved in
`DLaTopSeparated.lean`; the integrated head atom exposes only the `L²` bound, whereas the 8-summand
triangle consumes pointwise `rfns` bounds per summand.  So this is exactly the shape the `A1` slot of
the (future) DLa top-separated triangle needs.

Route (identical to `DLaTopSeparated.lean`'s internal pointwise step, but exported):
* the commutation identity `rfns_iteratedCovGrad_covGrad_comm_rs` turns
  `rfns (∇^i (covGrad Φ)) = rfns (∇^{i+1} Φ)` — an equality (no `finrank²`);
* the top-separated engine at order `j = i+1` splits the section jet into a top head
  `10·S 0 · rfns (∇^{i+2}P)` (`R`-independent) and a `boundedFactorGridWindow` remainder.

NOTE / scope: this is a **compiling prefix** of the DLa Step-2 sub-brick, not the full deliverable.
The full `deTurckLieDLaCoeffField` top-separated bound requires the private bridge machinery
(`deTurckLieDLaCoeffField_eq_pairTrace`, `dLaKernelRaisedCc`, `dLaSymCc`, `pairTraceOpDla`,
`dLaQuadCc`, all `_tgrid` grid bounds) that lives `private` inside the dirty (Codex-owned)
`DeTurckLieKernelL2JetBound.lean`, and so cannot be reached from a leaf file.  See
`DLaHeadCellRfns.md` and `UNIF_EXISTENCE_PLAN.md`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

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

/-! ### Pure real / `Finset` / combinatorial helper (no geometry). -/

/-- Copied verbatim (pure combinatorial, only `Combinatorics.*` deps) from the private
`tsResSum_le_boundedWindow` of `CurvatureCoefficientDifferenceJetTower.lean` (identically in
`ConnDiffJetL2Summed.lean` and `DLaTopSeparated.lean`).  Reshapes the engine remainder sum into a
`boundedFactorGridWindow`. -/
private lemma tsResSum_le_boundedWindow (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (j : ℕ) :
    ∑ k ∈ Finset.range j, b (j - k) * Combinatorics.antidiagonalTupleGrid b (k + 1) ≤
      (j : ℝ) * Combinatorics.boundedFactorGridWindow b j (j + 2) := by
  calc ∑ k ∈ Finset.range j, b (j - k) * Combinatorics.antidiagonalTupleGrid b (k + 1)
      ≤ ∑ _k ∈ Finset.range j, Combinatorics.boundedFactorGridWindow b j (j + 2) := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        rw [Finset.mem_range] at hk
        rw [Combinatorics.antidiagonalTupleGrid_eq_boundedFactorGrid b
          (show k + 1 ≤ j from by omega)]
        refine le_trans (Combinatorics.single_factor_mul_boundedFactorGrid_le b hb
          (k + 1) (j - k) (by omega) (by omega)) ?_
        rw [show (k + 1) + (j - k) = j + 1 from by omega]
        exact Combinatorics.boundedFactorGrid_le_boundedFactorGridWindow b hb (by omega)
    _ = (j : ℝ) * Combinatorics.boundedFactorGridWindow b j (j + 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ### Geometry setting. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ### Pointwise (`rfns`) top-separated head cell for `covGrad (connDiffSection)`. -/

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **Pointwise head cell** — the `riemannianFiberNormSq`, pointwise-in-`x` top-separated bound for
`covGrad (connDiffSection g₁ g₀)`, the `A1` top of the DLa 8-summand kernel.  The top coefficient
`2·Kt0` (`Kt0` the engine head `10·S 0`) is `R`-independent; the remainder is a
`boundedFactorGridWindow` of the pointwise `∇^{≤ i+1}P` weights, lumped with `Kc i`.  This is the
pointwise sibling of `covGradConnDiffSection_perOrder_l2_topSeparated_generic` (which integrates it),
in the shape the 8-summand triangle's `A1` slot consumes. -/
theorem covGradConnDiffSection_perOrder_rfns_topSeparated
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + 1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i
              (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))).toSection x) ≤
          Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) +
          Kc i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  classical
  obtain ⟨Kt0, hKt0_nn, Kc0, hKc0_nn, hbot⟩ :=
    rfns_iteratedCovGrad_connDiffSection_topSeparated_le (I := I) (M := M) g₀ hδ₀
  refine ⟨2 * Kt0, mul_nonneg (by norm_num) hKt0_nn,
    fun i => 2 * Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ),
    fun i => mul_nonneg (mul_nonneg (by norm_num) (hKc0_nn (i + 1))) (Nat.cast_nonneg (i + 1)), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ i x
  -- commutation identity: `rfns (∇^i (covGrad Φ)) = rfns (∇^{i+1} Φ)` (an equality)
  rw [rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 1 2 i
    (connDiffSection (I := I) g₁ g₀) x]
  -- engine split of the section jet at order `i+1`
  have heng := hbot g₁ P htie hδ_le hδ0 hδ (i + 1) x
  -- fold the engine head into `Hd`
  set Hd : SmoothCcTensor g₀ 1 (2 + (i + 1)) :=
    appCcRS (I := I) (M := M) g₀ 1 1 (2 + (i + 1))
      (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (raisedKoszul (I := I) g₀ g₁))
      (sharpFlatEndoCc (I := I) g₀ g₁)
  -- engine head bound, re-ascribed to the clean `i+2` index (defeq `(i+1)+1 = i+2`)
  have hhead : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i + 1)) x (Hd.toSection x) ≤
      Kt0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) := heng.1
  have hrem := heng.2
  -- `∇^{i+1} sec = Hd + (∇^{i+1} sec - Hd)`
  have hsplit : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
      ((iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i + 1)) x (Hd.toSection x) +
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
        ((iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connDiffSection (I := I) g₁ g₀) -
          Hd).toSection x) := by
    have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
      (Hd.toSection x)
      ((iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connDiffSection (I := I) g₁ g₀) -
        Hd).toSection x)
    have key :
        (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connDiffSection (I := I) g₁ g₀)).toSection x =
          Hd.toSection x +
            (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connDiffSection (I := I) g₁ g₀) -
              Hd).toSection x := by
      simp only [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
      abel
    rw [key]
    exact hadd
  -- reshape the remainder into a bounded-factor grid window (no widening needed at order `i+1`)
  have hrem_reshaped : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
      ((iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connDiffSection (I := I) g₁ g₀) -
        Hd).toSection x) ≤
      Kc0 (i + 1) * (((i + 1 : ℕ) : ℝ) * Combinatorics.boundedFactorGridWindow
        (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)) := by
    refine le_trans hrem ?_
    refine mul_le_mul_of_nonneg_left ?_ (hKc0_nn (i + 1))
    exact tsResSum_le_boundedWindow
      (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x))
      (fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _) (i + 1)
  -- combine and re-shape the constants
  have hcombined : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
      ((iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
      2 * (Kt0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) +
      2 * (Kc0 (i + 1) * (((i + 1 : ℕ) : ℝ) * Combinatorics.boundedFactorGridWindow
        (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3))) := by
    linarith [hsplit, hhead, hrem_reshaped]
  refine le_trans hcombined (le_of_eq ?_)
  ring

-- Axiom audit (temporary; must be exactly [propext, Classical.choice, Quot.sound]).

end DifferentialGeometry.Integral.Connection
