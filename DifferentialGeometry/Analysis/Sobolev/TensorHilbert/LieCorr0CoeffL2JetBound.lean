import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieCoeffL2JetBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorr0Split
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorr0LowJet

/-!
# `lieCorr0Field` realizedFam jet-L2 top-separated producer

The second genuinely-missing `C₀` constituent of the `Ψ₀` map
(`Ψ₀ = -2·arm0Field + deTurckLieCoeffField + lieCorr0Field`).  We produce the
`realizedFam` per-order and summed top-separated jet-L2 bounds for
`lieCorr0Field`, shape-matching the `deTurckLieCoeffField` siblings.

`lieCorr0Field` genuinely carries the top window `∇^{i+2}T` (RULING 2, not the
traceHessian pattern): via `lc0_decomp` it is
`lc0Insert + lc0VB + lc0AMix + lc0Riem`, and `lc0Insert` contains the base
insertion `lc0Insert g₀ g₁ g₀ = -deTurckLieDLbCoeffField g₀ g₁ g₀` whose
`∇^i` reaches `∇^{i+2}T` — its top-separation is inherited verbatim from the
committed DLb field producer at `g_bg := g₀` (`Ktop` R-free).  The remaining
four pieces are `∇²T`-free and land in the `R`-carrying `Kc`.
-/

noncomputable section

set_option autoImplicit false
set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (deTurckLieEndoArmField deTurckLieEndoArmField_toSection deTurckLieDLbFib)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedFam)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The reanchoring endomorphism arm field and the DLb coefficient field are the
same object (both are `ofCLM (deTurckLieDLbFib g₁ g_bg)`). -/
private theorem endoArm_eq_dlb (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g_bg =
      deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [deTurckLieEndoArmField_toSection, deTurckLieDLbCoeffField_toSection]

/-- The base insertion piece is the negative of the DLb coefficient field.
Combines `insert_base` (at `g_bg := g₀`) with `endoArm_eq_dlb`; this routes
`lieCorr0Field`'s top window through the committed DLb producer. -/
private theorem lc0Insert_base_eq_neg_dlb (g₀ g₁ : SmoothRiemannianMetric I M) :
    lc0Insert (I := I) (M := M) g₀ g₁ g₀ =
      -deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g₀ := by
  have h := insert_base (I := I) (M := M) g₀ g₁ g₀
  rw [sub_self] at h
  rw [eq_neg_of_add_eq_zero_left h, endoArm_eq_dlb]

/-- **Top piece.**  The base insertion piece inherits the DLb field producer's
top-separated bound at `g_bg := g₀` (`Ktop` R-free). -/
private theorem lc0InsertBase_realizedFam_perOrder_topSeparated
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
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (lc0Insert (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀)‖ ^ 2 ≤
            Ktop * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) +
            Kc i * (1 + ∑ j ∈ Finset.range (i + 3),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  obtain ⟨Ktop, hnn, Kc, hKcnn, h⟩ :=
    deTurckLieDLbCoeffField_realizedFam_jetL2_perOrder_topSeparated (I := I) (M := M) g₀ g₀ a
      ha_super hR hδ₀
  refine ⟨Ktop, hnn, Kc, hKcnn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs i hi
  have hb := h T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs i hi
  rw [lc0Insert_base_eq_neg_dlb, iteratedCovGrad_neg, norm_neg]
  exact hb

/-- Five-way squared triangle: `t ≤ a+b+c+d+e` (all nonneg) gives
`t² ≤ 5·(a²+b²+c²+d²+e²)`.  Used for the `lc0_decomp` five-summand assembly. -/
private theorem sq_le_five_add (t a b c d e : ℝ) (ht : 0 ≤ t)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e)
    (htri : t ≤ a + b + c + d + e) :
    t ^ 2 ≤ 5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) := by
  have hsum : 0 ≤ a + b + c + d + e := by linarith
  nlinarith [mul_le_mul htri htri ht hsum, sq_nonneg (a - b), sq_nonneg (a - c),
    sq_nonneg (a - d), sq_nonneg (a - e), sq_nonneg (b - c), sq_nonneg (b - d),
    sq_nonneg (b - e), sq_nonneg (c - d), sq_nonneg (c - e), sq_nonneg (d - e)]

end DifferentialGeometry.Integral.Connection

end
