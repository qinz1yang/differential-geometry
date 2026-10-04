import DifferentialGeometry.Geometry.Metric.Approximation.FiniteMetric.Curvature
import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.UniformConvergenceLower

/-!
# Sectional lower bounds on compact sets pass to `C²`-close smooth metrics

Lane CM-A (CM5.a). B7's `eventually_curvature_control` needs `sec_g ≥ 0` on a compact manifold.
Here the manifold is arbitrary, the finite-order bound is `sec_g ≥ κ` only on a compact set `C`,
and the smooth metrics converge to `g` in chart coefficients (`C²`) on every compact subset of
every chart target. Conclusion: for every `ε > 0`, eventually `sec(gSeq k) ≥ κ - ε` on `C`.

* `coefficientRm04_chart_lower_of_sectional`: the chart form of `κ ≤ sec_g` at a point
  (`κ · Gram ≤ Rm` for the chart coefficients); the bound forces `κ ≤ 0` (degenerate pairs).
* `eventually_sectionalBoundedBelowAt_of_chartCoeff_tendsto`: the compact-set transfer.
-/

set_option autoImplicit false

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Geometry.MetricSmoothing

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Analysis (coefficientRm04 coefficientSectional coefficientSectional_def
  bilin_gram_pos_of_linearIndependent bilin_gram_nonneg)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A finite-order sectional lower bound `κ ≤ sec_g` at `x` gives `κ · Gram ≤ Rm` for the chart
coefficients at the chart image of `x`, in every chart containing `x`. -/
theorem coefficientRm04_chart_lower_of_sectional {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hn : (2 : ℕ∞ω) ≤ n)
    (q : M) {x : M} (hx : x ∈ (extChartAt I q).source) {κ : ℝ}
    (hsec : ∀ v w : TangentSpace I x, κ ≤ g.sectionalCurvature x v w) (V W : E) :
    κ * (chartCoeff g q (extChartAt I q x) V V * chartCoeff g q (extChartAt I q x) W W -
      (chartCoeff g q (extChartAt I q x) V W) ^ 2) ≤
      coefficientRm04 (chartCoeff g q) (extChartAt I q x) V W W V := by
  have hy := (extChartAt I q).map_source hx
  have hcy : ContDiffAt ℝ 2 (chartCoeff g q) (extChartAt I q x) :=
    (contDiffOn_chartCoeff g hn q).contDiffAt ((isOpen_extChartAt_target q).mem_nhds hy)
  have hsy : ∀ᶠ z in 𝓝 (extChartAt I q x), ∀ u v : E,
      chartCoeff g q z u v = chartCoeff g q z v u :=
    Eventually.of_forall fun z u v => chartCoeff_symm g q z u v
  have hco := isCoercive_chartCoeff g q hy
  have hκ : κ ≤ 0 := by
    have h := hsec 0 0
    rwa [Bundle.ContMDiffRiemannianMetric.sectionalCurvature_zero_left] at h
  by_cases hind : LinearIndependent ℝ ![V, W]
  · have hsurj : ∀ U : E, (mfderiv I 𝓘(ℝ, E) (extChartAt I q) x : E →L[ℝ] E)
        ((mfderiv 𝓘(ℝ, E) I (extChartAt I q).symm (extChartAt I q x) : E →L[ℝ] E) U) = U := by
      intro U
      have h := mfderiv_extChartAt_apply_mfderiv_symm (I := I) q hy U
      rwa [(extChartAt I q).left_inv hx] at h
    let v : TangentSpace I x :=
      (mfderiv 𝓘(ℝ, E) I (extChartAt I q).symm (extChartAt I q x) : E →L[ℝ] E) V
    let w : TangentSpace I x :=
      (mfderiv 𝓘(ℝ, E) I (extChartAt I q).symm (extChartAt I q x) : E →L[ℝ] E) W
    have e : g.sectionalCurvature x v w =
        coefficientSectional (chartCoeff g q) (extChartAt I q x) V W :=
      (sectionalCurvature_eq_chart g hn q hx v w).trans
        (congrArg₂ (fun a b : E => coefficientSectional (chartCoeff g q) (extChartAt I q x) a b)
          (hsurj V) (hsurj W))
    have hK : κ ≤ coefficientSectional (chartCoeff g q) (extChartAt I q x) V W := e ▸ hsec v w
    have hden := bilin_gram_pos_of_linearIndependent
      (fun a b => chartCoeff_symm g q (extChartAt I q x) a b) hco hind
    rw [coefficientSectional_def, le_div_iff₀ hden] at hK
    exact hK
  · rw [coefficientRm04_eq_zero_of_not_linearIndependent hcy hsy hco hind]
    refine mul_nonpos_of_nonpos_of_nonneg hκ (bilin_gram_nonneg
      (fun a b => chartCoeff_symm g q (extChartAt I q x) a b) (fun u => ?_) V W)
    by_cases hu : u = 0
    · simp [hu]
    · exact (chartCoeff_pos g q hy hu).le

/-- **Compact-set curvature transfer.** If smooth metrics converge to a `C^n` metric `g`
(`2 ≤ n`) in chart coefficients, in `C²` on every compact subset of every chart target, and
`κ ≤ sec_g` on a compact set `C`, then for every `ε > 0` eventually `sec(gSeq k) ≥ κ - ε` on
`C`. -/
theorem eventually_sectionalBoundedBelowAt_of_chartCoeff_tendsto [T2Space M] {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hn : (2 : ℕ∞ω) ≤ n)
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hconv : ∀ (q : M) (L : Set E), IsCompact L → L ⊆ (extChartAt I q).target →
      MapCPConvergenceOn L 2 (fun k => chartCoeff (gSeq k) q) (chartCoeff g q))
    {C : Set M} (hC : IsCompact C) {κ ε : ℝ} (hε : 0 < ε)
    (hsec : ∀ x ∈ C, ∀ v w : TangentSpace I x, κ ≤ g.sectionalCurvature x v w) :
    ∀ᶠ k in atTop, ∀ x ∈ C,
      DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelowAt (gSeq k) x (κ - ε) := by
  have hr : ∀ x : M, ∃ r : ℝ, 0 < r ∧
      Metric.closedBall (extChartAt I x x) r ⊆ (extChartAt I x).target := by
    intro x
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (isOpen_extChartAt_target (I := I) x) _
      (mem_extChartAt_target (I := I) x)
    exact ⟨r / 2, half_pos hr, (Metric.closedBall_subset_ball (half_lt_self hr)).trans hball⟩
  choose r hr0 hrt using hr
  let O : M → Set M := fun x =>
    (extChartAt I x).source ∩ extChartAt I x ⁻¹' Metric.ball (extChartAt I x x) (r x)
  have hO : ∀ x ∈ C, O x ∈ 𝓝 x := fun x _ =>
    (isOpen_extChartAt_preimage' x Metric.isOpen_ball).mem_nhds
      ⟨mem_extChartAt_source x, Metric.mem_ball_self (hr0 x)⟩
  obtain ⟨t, -, hcover⟩ := hC.elim_nhds_subcover O hO
  let L : M → Set E := fun x =>
    Metric.closedBall (extChartAt I x x) (r x) ∩ (extChartAt I x).symm ⁻¹' C
  have hLt : ∀ x, L x ⊆ (extChartAt I x).target := fun x => inter_subset_left.trans (hrt x)
  have hLc : ∀ x, IsCompact (L x) := fun x =>
    (isCompact_closedBall _ _).of_isClosed_subset
      (((continuousOn_extChartAt_symm x).mono (hrt x)).preimage_isClosed_of_isClosed
        Metric.isClosed_closedBall hC.isClosed) inter_subset_left
  have hev : ∀ x ∈ t, ∀ᶠ k in atTop, ∀ y ∈ L x, ∀ V W : E,
      (κ - ε) * (chartCoeff (gSeq k) x y V V * chartCoeff (gSeq k) x y W W -
        (chartCoeff (gSeq k) x y V W) ^ 2) ≤ coefficientRm04 (chartCoeff (gSeq k) x) y V W W V := by
    intro x _
    refine DifferentialGeometry.Analysis.eventually_coefficientRm04_lower_of_level
      (isOpen_extChartAt_target x) (hLc x) (hLt x)
      (fun k => contDiffOn_chartCoeff (gSeq k) (by simp) x) (contDiffOn_chartCoeff g hn x)
      (fun k y _ v w => chartCoeff_symm (gSeq k) x y v w) (fun y hy v hv => chartCoeff_pos g x hy hv)
      (hconv x (L x) (hLc x) (hLt x)) ?_ ε hε
    intro y hy V W
    have hyt := hLt x hy
    have h := coefficientRm04_chart_lower_of_sectional g hn x ((extChartAt I x).map_target hyt)
      (hsec _ hy.2) V W
    rwa [(extChartAt I x).right_inv hyt] at h
  filter_upwards [(Filter.eventually_all_finset t).2 hev] with k hk z hz
  obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.mp (hcover hz)
  have hzL : extChartAt I x z ∈ L x :=
    ⟨Metric.ball_subset_closedBall hzx.2, by
      change (extChartAt I x).symm (extChartAt I x z) ∈ C
      rw [(extChartAt I x).left_inv hzx.1]
      exact hz⟩
  exact sectionalBoundedBelowAt_of_chart (gSeq k) x hzx.1 fun V W => hk x hxt _ hzL V W

end DifferentialGeometry.Geometry.MetricSmoothing
