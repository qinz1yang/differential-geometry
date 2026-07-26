import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.FineInvGram
import DifferentialGeometry.Analysis.Parabolic.Euclidean.RetractionParametrix

/-!
# The uniformly small principal freezing error

The diagonal chart heat operator is only a local parametrix for the genuine
Ricci--DeTurck principal operator.  Its second-order error is the oscillation
of the inverse Gram coefficients away from the point where they were frozen.

This file makes the spatial smallness choice before the time horizon is
chosen.  The radius depends only on the fixed chart-buffer radius and the
family-uniform inverse-Gram derivative bound.  In particular, it is
independent of the member of the metric family and of the later time horizon.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped ContDiff Manifold Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [T2Space M] [SigmaCompactSpace M]

/-- A fixed fine radius determined only by a chart-buffer radius, a
family-uniform first-derivative bound for inverse Gram entries, and the
uniform maximal-regularity Hessian constant `K₂`. -/
def fineOscRadius (r₀ L K₂ : ℝ) : ℝ :=
  min (r₀ / 2) (1 / (8 * (L + 1) * (K₂ + 1)))

/-- The fine oscillation radius is positive whenever the outer buffer radius
is positive and the derivative bound is nonnegative. -/
theorem fineOscRadius_pos {r₀ L K₂ : ℝ}
    (hr₀ : 0 < r₀) (hL : 0 ≤ L) (hK₂ : 0 ≤ K₂) :
    0 < fineOscRadius r₀ L K₂ := by
  have hLp : 0 < L + 1 := by linarith
  have hKp : 0 < K₂ + 1 := by linarith
  have hden : 0 < (8 : ℝ) * (L + 1) * (K₂ + 1) :=
    mul_pos (mul_pos (by norm_num) hLp) hKp
  rw [fineOscRadius]
  exact lt_min (by linarith) (one_div_pos.mpr hden)

/-- The chosen fine radius stays inside the chart buffer. -/
theorem fineOscRadius_le {r₀ L K₂ : ℝ} (hr₀ : 0 < r₀) :
    fineOscRadius r₀ L K₂ ≤ r₀ := by
  calc
    fineOscRadius r₀ L K₂ ≤ r₀ / 2 := min_le_left _ _
    _ ≤ r₀ := by linarith

/-- The coefficient oscillation itself is strictly smaller than one quarter. -/
theorem fineOsc_coeff_lt {r₀ L K₂ : ℝ}
    (hL : 0 ≤ L) (hK₂ : 0 ≤ K₂) :
    L * fineOscRadius r₀ L K₂ < (1 : ℝ) / 4 := by
  have hLp : 0 < L + 1 := by linarith
  have hKp : 0 < K₂ + 1 := by linarith
  have hden : 0 < (8 : ℝ) * (L + 1) * (K₂ + 1) :=
    mul_pos (mul_pos (by norm_num) hLp) hKp
  have hR : fineOscRadius r₀ L K₂ ≤
      1 / (8 * (L + 1) * (K₂ + 1)) :=
    min_le_right _ _
  calc
    L * fineOscRadius r₀ L K₂ ≤
        L * (1 / (8 * (L + 1) * (K₂ + 1))) :=
      mul_le_mul_of_nonneg_left hR hL
    _ = L / (8 * (L + 1) * (K₂ + 1)) := by ring
    _ < (1 : ℝ) / 4 := by
      rw [div_lt_iff₀ hden]
      nlinarith [mul_nonneg hL hK₂]

/-- After the maximal-regularity Hessian constant is inserted, the complete
principal coefficient remains strictly smaller than one quarter. -/
theorem fineOsc_mul_lt {r₀ L K₂ : ℝ}
    (hL : 0 ≤ L) (hK₂ : 0 ≤ K₂) :
    (L * fineOscRadius r₀ L K₂) * K₂ < (1 : ℝ) / 4 := by
  have hLp : 0 < L + 1 := by linarith
  have hKp : 0 < K₂ + 1 := by linarith
  have hden : 0 < (8 : ℝ) * (L + 1) * (K₂ + 1) :=
    mul_pos (mul_pos (by norm_num) hLp) hKp
  have hR : fineOscRadius r₀ L K₂ ≤
      1 / (8 * (L + 1) * (K₂ + 1)) :=
    min_le_right _ _
  have hLK : 0 ≤ L * K₂ := mul_nonneg hL hK₂
  calc
    (L * fineOscRadius r₀ L K₂) * K₂ =
        (L * K₂) * fineOscRadius r₀ L K₂ := by ring
    _ ≤ (L * K₂) * (1 / (8 * (L + 1) * (K₂ + 1))) :=
      mul_le_mul_of_nonneg_left hR hLK
    _ = (L * K₂) / (8 * (L + 1) * (K₂ + 1)) := by ring
    _ < (1 : ℝ) / 4 := by
      rw [div_lt_iff₀ hden]
      nlinarith

/-- On the fixed fine ball every inverse-Gram coefficient differs from its
frozen value by at most `L` times the fixed fine radius, uniformly over the
metric family.  Retaining this constant is what later yields a strict
operator-norm bound rather than merely a pointwise quarter estimate. -/
theorem invGramOscBound
    {ι : Type*}
    (gSeq : ι → SmoothRiemannianMetric I M)
    (α : M) {K : Set M}
    {r₀ L K₂ : ℝ} (hr₀ : 0 < r₀) (hL_nn : 0 ≤ L) (hK₂_nn : 0 ≤ K₂)
    (hcollar : Metric.cthickening r₀ ((extChartAt I α) '' K) ⊆
      (extChartAt I α).target)
    (hL : ∀ k : ι,
      ∀ b ∈ chartBuffer (extChartAt I α) K r₀,
        ∀ i j : Fin (Module.finrank ℝ E),
          ‖fderiv ℝ (chartInvGramOnE (I := I) (gSeq k) α i j)
            (extChartAt I α b)‖ ≤ L)
    (k : ι) {x : M} (hx : x ∈ K) {y : E}
    (hy : y ∈ Metric.closedBall (extChartAt I α x)
      (fineOscRadius r₀ L K₂))
    (i j : Fin (Module.finrank ℝ E)) :
    |chartInvGramOnE (I := I) (gSeq k) α i j y -
        chartInvGramOnE (I := I) (gSeq k) α i j
          (extChartAt I α x)| ≤ L * fineOscRadius r₀ L K₂ := by
  have hRpos : 0 < fineOscRadius r₀ L K₂ :=
    fineOscRadius_pos hr₀ hL_nn hK₂_nn
  have hLip := invGram_freeze_lip (I := I) (M := M) gSeq α
    (hR_nn := le_of_lt hRpos) (hR := fineOscRadius_le hr₀)
    hcollar hL k hx hy i j
  have hynorm : ‖y - extChartAt I α x‖ ≤ fineOscRadius r₀ L K₂ := by
    simpa only [dist_eq_norm] using hy
  calc
    |chartInvGramOnE (I := I) (gSeq k) α i j y -
        chartInvGramOnE (I := I) (gSeq k) α i j
          (extChartAt I α x)|
        ≤ L * ‖y - extChartAt I α x‖ := hLip
    _ ≤ L * fineOscRadius r₀ L K₂ :=
      mul_le_mul_of_nonneg_left hynorm hL_nn

/-- On the fixed fine ball every inverse-Gram coefficient differs from its
frozen value by strictly less than one quarter, uniformly over the metric
family. -/
theorem invGramOscQuarter
    {ι : Type*}
    (gSeq : ι → SmoothRiemannianMetric I M)
    (α : M) {K : Set M}
    {r₀ L K₂ : ℝ} (hr₀ : 0 < r₀) (hL_nn : 0 ≤ L) (hK₂_nn : 0 ≤ K₂)
    (hcollar : Metric.cthickening r₀ ((extChartAt I α) '' K) ⊆
      (extChartAt I α).target)
    (hL : ∀ k : ι,
      ∀ b ∈ chartBuffer (extChartAt I α) K r₀,
        ∀ i j : Fin (Module.finrank ℝ E),
          ‖fderiv ℝ (chartInvGramOnE (I := I) (gSeq k) α i j)
            (extChartAt I α b)‖ ≤ L)
    (k : ι) {x : M} (hx : x ∈ K) {y : E}
    (hy : y ∈ Metric.closedBall (extChartAt I α x)
      (fineOscRadius r₀ L K₂))
    (i j : Fin (Module.finrank ℝ E)) :
    |chartInvGramOnE (I := I) (gSeq k) α i j y -
        chartInvGramOnE (I := I) (gSeq k) α i j
          (extChartAt I α x)| < (1 : ℝ) / 4 :=
  (invGramOscBound (I := I) (M := M) gSeq α hr₀ hL_nn hK₂_nn hcollar hL
    k hx hy i j).trans_lt (fineOsc_coeff_lt hL_nn hK₂_nn)

section PrincipalArray

variable {n : ℕ}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The pointwise principal freezing error acting on a finite Hessian array. -/
def principalOsc
    (a a₀ : Fin n → Fin n → ℝ) (D²u : Fin n → Fin n → F) : F :=
  ∑ i, ∑ j, (a i j - a₀ i j) • D²u i j

/-- Triangle inequality for the principal freezing error, before inserting
any coefficient-smallness estimate. -/
theorem principalOsc_bound
    (a a₀ : Fin n → Fin n → ℝ) (D²u : Fin n → Fin n → F) :
    ‖principalOsc a a₀ D²u‖ ≤
      ∑ i, ∑ j, |a i j - a₀ i j| * ‖D²u i j‖ := by
  classical
  rw [principalOsc]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]

/-- A common nonnegative entrywise coefficient bound controls the complete
second-order freezing arm against the `ℓ¹` Hessian size. -/
theorem principalOsc_const
    (a a₀ : Fin n → Fin n → ℝ) (D²u : Fin n → Fin n → F)
    {δ : ℝ}
    (ha : ∀ i j, |a i j - a₀ i j| ≤ δ) :
    ‖principalOsc a a₀ D²u‖ ≤
      δ * ∑ i, ∑ j, ‖D²u i j‖ := by
  refine (principalOsc_bound a a₀ D²u).trans ?_
  calc
    ∑ i, ∑ j, |a i j - a₀ i j| * ‖D²u i j‖
        ≤ ∑ i, ∑ j, δ * ‖D²u i j‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_right (ha i j) (norm_nonneg _)
    _ = ∑ i, δ * ∑ j, ‖D²u i j‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ = δ * ∑ i, ∑ j, ‖D²u i j‖ := by
      rw [Finset.mul_sum]

/-- Entrywise coefficient oscillation at most one quarter makes the complete
second-order freezing arm at most one quarter of the `ℓ¹` Hessian size. -/
theorem principalOscQuarter
    (a a₀ : Fin n → Fin n → ℝ) (D²u : Fin n → Fin n → F)
    (ha : ∀ i j, |a i j - a₀ i j| ≤ (1 : ℝ) / 4) :
    ‖principalOsc a a₀ D²u‖ ≤
      ((1 : ℝ) / 4) * ∑ i, ∑ j, ‖D²u i j‖ :=
  principalOsc_const a a₀ D²u ha

/-- The actual inverse-Gram freezing arm retains the strict uniform constant
`L * fineOscRadius r₀ L K₂`. -/
theorem invGramB2Bound
    {ι : Type*}
    (gSeq : ι → SmoothRiemannianMetric I M)
    (α : M) {K : Set M}
    {r₀ L K₂ : ℝ} (hr₀ : 0 < r₀) (hL_nn : 0 ≤ L) (hK₂_nn : 0 ≤ K₂)
    (hcollar : Metric.cthickening r₀ ((extChartAt I α) '' K) ⊆
      (extChartAt I α).target)
    (hL : ∀ k : ι,
      ∀ b ∈ chartBuffer (extChartAt I α) K r₀,
        ∀ i j : Fin (Module.finrank ℝ E),
          ‖fderiv ℝ (chartInvGramOnE (I := I) (gSeq k) α i j)
            (extChartAt I α b)‖ ≤ L)
    (k : ι) {x : M} (hx : x ∈ K) {y : E}
    (hy : y ∈ Metric.closedBall (extChartAt I α x)
      (fineOscRadius r₀ L K₂))
    (D²u : Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → F) :
    ‖principalOsc
        (fun i j => chartInvGramOnE (I := I) (gSeq k) α i j y)
        (fun i j => chartInvGramOnE (I := I) (gSeq k) α i j
          (extChartAt I α x)) D²u‖ ≤
      (L * fineOscRadius r₀ L K₂) * ∑ i, ∑ j, ‖D²u i j‖ := by
  apply principalOsc_const
  intro i j
  exact invGramOscBound (I := I) (M := M) gSeq α
    hr₀ hL_nn hK₂_nn hcollar hL k hx hy i j

/-- The actual inverse-Gram freezing arm has the uniform one-quarter bound on
the fixed fine ball.  This is the pointwise `B₂` estimate used by the
retraction--coretraction parametrix. -/
theorem invGramB2Quarter
    {ι : Type*}
    (gSeq : ι → SmoothRiemannianMetric I M)
    (α : M) {K : Set M}
    {r₀ L K₂ : ℝ} (hr₀ : 0 < r₀) (hL_nn : 0 ≤ L) (hK₂_nn : 0 ≤ K₂)
    (hcollar : Metric.cthickening r₀ ((extChartAt I α) '' K) ⊆
      (extChartAt I α).target)
    (hL : ∀ k : ι,
      ∀ b ∈ chartBuffer (extChartAt I α) K r₀,
        ∀ i j : Fin (Module.finrank ℝ E),
          ‖fderiv ℝ (chartInvGramOnE (I := I) (gSeq k) α i j)
            (extChartAt I α b)‖ ≤ L)
    (k : ι) {x : M} (hx : x ∈ K) {y : E}
    (hy : y ∈ Metric.closedBall (extChartAt I α x)
      (fineOscRadius r₀ L K₂))
    (D²u : Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → F) :
    ‖principalOsc
        (fun i j => chartInvGramOnE (I := I) (gSeq k) α i j y)
        (fun i j => chartInvGramOnE (I := I) (gSeq k) α i j
          (extChartAt I α x)) D²u‖ ≤
      ((1 : ℝ) / 4) * ∑ i, ∑ j, ‖D²u i j‖ := by
  calc
    ‖principalOsc
        (fun i j => chartInvGramOnE (I := I) (gSeq k) α i j y)
        (fun i j => chartInvGramOnE (I := I) (gSeq k) α i j
          (extChartAt I α x)) D²u‖
        ≤ (L * fineOscRadius r₀ L K₂) * ∑ i, ∑ j, ‖D²u i j‖ :=
          invGramB2Bound (I := I) (M := M) gSeq α hr₀ hL_nn hK₂_nn
            hcollar hL k hx hy D²u
    _ ≤ ((1 : ℝ) / 4) * ∑ i, ∑ j, ‖D²u i j‖ :=
      mul_le_mul_of_nonneg_right (fineOsc_coeff_lt hL_nn hK₂_nn).le
        (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _)

end PrincipalArray

section PrincipalOperator

open DifferentialGeometry.Analysis.Parabolic.Euclidean

variable
    {Y U V J₂ : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup J₂] [NormedSpace ℝ J₂]

/-- Once the actual coefficient multiplier and frozen-solver Hessian maps are
measured in the chosen forcing norm, the fine radius makes the concrete
principal error operator strictly smaller than one quarter. -/
theorem b2Error_quarter
    {r₀ L K₂ : ℝ} (hr₀ : 0 < r₀) (hL : 0 ≤ L) (hK₂ : 0 ≤ K₂)
    (E : Y →L[ℝ] V) (H : V →L[ℝ] U)
    (D₂ : U →L[ℝ] J₂) (C₂ : J₂ →L[ℝ] Y)
    (hC₂ : ‖C₂‖ ≤ L * fineOscRadius r₀ L K₂)
    (hD₂ : ‖D₂.comp (H.comp E)‖ ≤ K₂) :
    ‖principalError E H D₂ C₂‖ < (1 : ℝ) / 4 := by
  refine (principalError_le E H D₂ C₂ ?_ hC₂ hD₂).trans_lt
    (fineOsc_mul_lt hL hK₂)
  exact mul_nonneg hL (fineOscRadius_pos hr₀ hL hK₂).le

end PrincipalOperator

end DifferentialGeometry.PDE.RicciFlow
