import DifferentialGeometry.Geometry.Metric.Approximation.FiniteMetric.SmoothingConvergence
import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.UniformConvergence
import DifferentialGeometry.Geometry.Curvature.Riemann.FiniteMetricSmooth
import DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric
import DifferentialGeometry.Geometry.Curvature.Algebraic.Polarization
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import DifferentialGeometry.Geometry.Comparison.RadialHessianLowerBound

/-!
# Curvature control of the smooth approximants (LFR50, parts A2 and A3)

Bridges between the chart coefficients `chartCoeff` and curvature:
* `chartCoeff_mfderiv`: chart coefficients read the metric;
* `metricRm04StandardAt_eq_chart`: for a smooth metric, the sectional numerator
  `Rm(v, w, w, v)` equals the coefficient numerator `coefficientRm04` in ANY extended chart;
* `sectionalCurvature_nonneg_iff_chart_numerator_nonneg`: the finite-order normalized sectional
  curvature `Bundle.ContMDiffRiemannianMetric.sectionalCurvature` is nonnegative iff all chart
  numerators are (this is the bridge to the numerator form `metric2Rm04StandardAt ≥ 0` of the
  design; the two conditions coincide);
* `sectionalBoundedBelowAt_of_chart`, `sqrt_normSq0S_metricRm04_le_of_chart`: chart inequalities
  give `SectionalBoundedBelowAt` and a bound of the full curvature norm `|Rm|` (polarization).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Geometry.MetricSmoothing

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Analysis (coefficientRm04 coefficientSectional coefficientSectional_def
  bilin_gram_pos_of_linearIndependent bilin_gram_nonneg coefficientRm04_change_of_basis)

section Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The coefficient numerator vanishes on linearly dependent pairs. -/
theorem coefficientRm04_eq_zero_of_not_linearIndependent {b : E → E →L[ℝ] E →L[ℝ] ℝ} {y : E}
    (hb : ContDiffAt ℝ 2 b y) (hsymm : ∀ᶠ z in 𝓝 y, ∀ u v : E, b z u v = b z v u)
    (hco : IsCoercive (b y)) {V W : E} (hdep : ¬LinearIndependent ℝ ![V, W]) :
    coefficientRm04 b y V W W V = 0 := by
  by_cases hV : V = 0
  · have h := coefficientRm04_change_of_basis hb hsymm hco 0 0 1 0 W W
    simp only [zero_smul, add_zero, one_smul, mul_zero, sub_zero, zero_mul] at h
    rw [hV]
    simpa using h
  · obtain ⟨a, ha⟩ : ∃ a : ℝ, a • V = W := by
      simpa only [LinearIndependent.pair_iff' hV, not_forall, not_not] using hdep
    have h := coefficientRm04_change_of_basis hb hsymm hco 1 0 a 0 V V
    simp only [zero_smul, add_zero, one_smul, mul_zero, zero_mul, sub_zero] at h
    rw [← ha]
    simpa using h

end Coordinates

section Bridges

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] in
theorem mfderiv_extChartAt_symm_apply_mfderiv (q : M) {x : M}
    (hx : x ∈ (extChartAt I q).source) (v : TangentSpace I x) :
    (mfderiv 𝓘(ℝ, E) I (extChartAt I q).symm (extChartAt I q x) : E →L[ℝ] E)
      ((mfderiv I 𝓘(ℝ, E) (extChartAt I q) x : E →L[ℝ] E) v) = v := by
  have h1 : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I q) x :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hx)
  have h2 := mdifferentiableAt_extChartAt_symm_of_mem (I := I) q ((extChartAt I q).map_source hx)
  have heq : (extChartAt I q).symm ∘ (extChartAt I q) =ᶠ[𝓝 x] id := by
    filter_upwards [(isOpen_extChartAt_source q).mem_nhds hx] with z hz
    exact (extChartAt I q).left_inv hz
  have hc := (mfderiv_comp x h2 h1).symm.trans (heq.mfderiv_eq.trans mfderiv_id)
  exact congrArg (fun L => L v) hc

omit [FiniteDimensional ℝ E] in
theorem mfderiv_extChartAt_apply_mfderiv_symm (q : M) {y : E}
    (hy : y ∈ (extChartAt I q).target) (V : E) :
    (mfderiv I 𝓘(ℝ, E) (extChartAt I q) ((extChartAt I q).symm y) : E →L[ℝ] E)
      ((mfderiv 𝓘(ℝ, E) I (extChartAt I q).symm y : E →L[ℝ] E) V) = V := by
  have hc := mfderiv_extChartAt_comp_symm (I := I) q q
    (show y ∈ transitionDomain (I := I) q q from ⟨hy, (extChartAt I q).map_target hy⟩)
  have heq : chartTransition (I := I) q q =ᶠ[𝓝 y] id := by
    filter_upwards [(isOpen_extChartAt_target q).mem_nhds hy] with z hz
    exact (extChartAt I q).right_inv hz
  rw [heq.fderiv_eq, fderiv_id] at hc
  exact congrArg (fun L => L V) hc

omit [FiniteDimensional ℝ E] in
/-- Chart coefficients read the metric. -/
theorem chartCoeff_mfderiv {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (q : M) {x : M}
    (hx : x ∈ (extChartAt I q).source) (v w : TangentSpace I x) :
    chartCoeff g q (extChartAt I q x) (mfderiv I 𝓘(ℝ, E) (extChartAt I q) x v)
      (mfderiv I 𝓘(ℝ, E) (extChartAt I q) x w) = g.inner x v w := by
  calc chartCoeff g q (extChartAt I q x) (mfderiv I 𝓘(ℝ, E) (extChartAt I q) x v)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I q) x w)
      = (g.inner ((extChartAt I q).symm (extChartAt I q x)) : E →L[ℝ] E →L[ℝ] ℝ) v w :=
        congrArg₂ (fun a b : E =>
          (g.inner ((extChartAt I q).symm (extChartAt I q x)) : E →L[ℝ] E →L[ℝ] ℝ) a b)
          (mfderiv_extChartAt_symm_apply_mfderiv (I := I) q hx v)
          (mfderiv_extChartAt_symm_apply_mfderiv (I := I) q hx w)
    _ = g.inner x v w := congrArg (fun z : M => (g.inner z : E →L[ℝ] E →L[ℝ] ℝ) v w)
        ((extChartAt I q).left_inv hx)

theorem isCoercive_chartCoeff {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (q : M) {y : E}
    (hy : y ∈ (extChartAt I q).target) : IsCoercive (chartCoeff g q y) :=
  ContinuousLinearMap.isCoercive_of_posDef _ fun _ hv => chartCoeff_pos g q hy hv

theorem sectionalCurvature_eq_chart {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hn : (2 : ℕ∞ω) ≤ n)
    (q : M) {x : M} (hx : x ∈ (extChartAt I q).source) (v w : TangentSpace I x) :
    g.sectionalCurvature x v w = coefficientSectional (chartCoeff g q) (extChartAt I q x)
      (mfderiv I 𝓘(ℝ, E) (extChartAt I q) x v) (mfderiv I 𝓘(ℝ, E) (extChartAt I q) x w) :=
  Bundle.ContMDiffRiemannianMetric.sectionalCurvature_eq_coefficientSectional g hn
    (DifferentialGeometry.PartialDiffeomorph.extChartAt I 3 q) hx v w

/-- **Numerator bridge.** For a smooth metric the sectional numerator `Rm(v, w, w, v)` is the
coefficient numerator in any extended chart containing the point. -/
theorem metricRm04StandardAt_eq_chart [T2Space M] (h : SmoothRiemannianMetric I M) (q : M)
    {x : M} (hx : x ∈ (extChartAt I q).source) (v w : TangentSpace I x) :
    DifferentialGeometry.Geometry.Curvature.metricRm04StandardAt h x v w w v =
      coefficientRm04 (chartCoeff h q) (extChartAt I q x)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I q) x v) (mfderiv I 𝓘(ℝ, E) (extChartAt I q) x w)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I q) x w) (mfderiv I 𝓘(ℝ, E) (extChartAt I q) x v) := by
  have hy := (extChartAt I q).map_source hx
  have hcy : ContDiffAt ℝ 2 (chartCoeff h q) (extChartAt I q x) :=
    (contDiffOn_chartCoeff h (by simp) q).contDiffAt ((isOpen_extChartAt_target q).mem_nhds hy)
  have hsy : ∀ᶠ z in 𝓝 (extChartAt I q x), ∀ u v : E,
      chartCoeff h q z u v = chartCoeff h q z v u :=
    Eventually.of_forall fun z u v => chartCoeff_symm h q z u v
  have hco := isCoercive_chartCoeff h q hy
  by_cases hind : LinearIndependent ℝ ![v, w]
  · have hden : 0 < h.inner x v v * h.inner x w w - (h.inner x v w) ^ 2 :=
      bilin_gram_pos_of_linearIndependent (B := (h.inner x : E →L[ℝ] E →L[ℝ] ℝ))
        (fun a b => h.symm x a b)
        (ContinuousLinearMap.isCoercive_of_posDef _ fun a ha => h.pos x a ha) hind
    have e1 := Bundle.ContMDiffRiemannianMetric.sectionalCurvature_eq_smooth h x v w
    rw [sectionalCurvature_eq_chart h (by simp) q hx v w,
      DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_def,
      DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureNumerator_eq_metricRm04StandardAt,
      DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_def] at e1
    unfold DifferentialGeometry.Analysis.coefficientSectional at e1
    rw [chartCoeff_mfderiv h q hx, chartCoeff_mfderiv h q hx, chartCoeff_mfderiv h q hx] at e1
    exact ((div_left_inj' hden.ne').mp e1).symm
  · have hdep : ¬LinearIndependent ℝ ![mfderiv I 𝓘(ℝ, E) (extChartAt I q) x v,
        mfderiv I 𝓘(ℝ, E) (extChartAt I q) x w] := by
      intro hli
      apply hind
      rw [LinearIndependent.pair_iff] at hli ⊢
      intro s t hst
      apply hli s t
      have h0 := congrArg (mfderiv I 𝓘(ℝ, E) (extChartAt I q) x) hst
      rw [map_add, map_smul, map_smul, map_zero] at h0
      exact h0
    rw [coefficientRm04_eq_zero_of_not_linearIndependent hcy hsy hco hdep]
    exact DifferentialGeometry.Geometry.metricRm04StandardAt_eq_zero_of_not_linearIndependent
      h x v w hind

/-- Nonnegative finite-order sectional curvature at `x` gives nonnegative coefficient numerators
at the chart image of `x`, in every chart containing `x`. -/
theorem coefficientRm04_chart_nonneg_of_sectional {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hn : (2 : ℕ∞ω) ≤ n)
    (q : M) {x : M} (hx : x ∈ (extChartAt I q).source)
    (hsec : ∀ v w : TangentSpace I x, 0 ≤ g.sectionalCurvature x v w) (V W : E) :
    0 ≤ coefficientRm04 (chartCoeff g q) (extChartAt I q x) V W W V := by
  have hy := (extChartAt I q).map_source hx
  have hcy : ContDiffAt ℝ 2 (chartCoeff g q) (extChartAt I q x) :=
    (contDiffOn_chartCoeff g hn q).contDiffAt ((isOpen_extChartAt_target q).mem_nhds hy)
  have hsy : ∀ᶠ z in 𝓝 (extChartAt I q x), ∀ u v : E,
      chartCoeff g q z u v = chartCoeff g q z v u :=
    Eventually.of_forall fun z u v => chartCoeff_symm g q z u v
  have hco := isCoercive_chartCoeff g q hy
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
    have hK : 0 ≤ coefficientSectional (chartCoeff g q) (extChartAt I q x) V W :=
      e ▸ hsec v w
    have hden := bilin_gram_pos_of_linearIndependent
      (fun a b => chartCoeff_symm g q (extChartAt I q x) a b) hco hind
    rw [coefficientSectional_def] at hK
    have h := mul_nonneg hK hden.le
    rwa [div_mul_cancel₀ _ hden.ne'] at h
  · rw [coefficientRm04_eq_zero_of_not_linearIndependent hcy hsy hco hind]

/-- **Bridge to the numerator notion of the design.** Nonnegativity of the finite-order
normalized sectional curvature is equivalent to nonnegativity of all chart numerators
`Rm(V, W, W, V)`, i.e. to the numerator condition `metric2Rm04StandardAt g x v w w v ≥ 0` of
design §1 (the two hypotheses define the same class of metrics). -/
theorem sectionalCurvature_nonneg_iff_chart_numerator_nonneg {n : ℕ∞ω}
    {g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)} (hn : (2 : ℕ∞ω) ≤ n) :
    (∀ x (v w : TangentSpace I x), 0 ≤ g.sectionalCurvature x v w) ↔
      ∀ q x : M, x ∈ (extChartAt I q).source → ∀ V W : E,
        0 ≤ coefficientRm04 (chartCoeff g q) (extChartAt I q x) V W W V := by
  constructor
  · intro hsec q x hx V W
    exact coefficientRm04_chart_nonneg_of_sectional g hn q hx (hsec x) V W
  · intro hnum x v w
    rw [sectionalCurvature_eq_chart g hn x (mem_extChartAt_source x) v w]
    unfold DifferentialGeometry.Analysis.coefficientSectional
    refine div_nonneg (hnum x x (mem_extChartAt_source x) _ _) ?_
    refine bilin_gram_nonneg (fun a b => chartCoeff_symm g x _ a b) (fun u => ?_) _ _
    by_cases hu : u = 0
    · simp [hu]
    · exact (chartCoeff_pos g x ((extChartAt I x).map_source (mem_extChartAt_source x)) hu).le

/-- A chart lower bound for the coefficient numerators gives a sectional lower bound. -/
theorem sectionalBoundedBelowAt_of_chart [T2Space M] (h : SmoothRiemannianMetric I M) (q : M)
    {x : M} (hx : x ∈ (extChartAt I q).source) {κ : ℝ}
    (hk : ∀ V W : E, κ * (chartCoeff h q (extChartAt I q x) V V *
        chartCoeff h q (extChartAt I q x) W W - (chartCoeff h q (extChartAt I q x) V W) ^ 2) ≤
      coefficientRm04 (chartCoeff h q) (extChartAt I q x) V W W V) :
    DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelowAt h x κ := by
  intro v w
  have hvw := hk (mfderiv I 𝓘(ℝ, E) (extChartAt I q) x v) (mfderiv I 𝓘(ℝ, E) (extChartAt I q) x w)
  rw [chartCoeff_mfderiv h q hx, chartCoeff_mfderiv h q hx, chartCoeff_mfderiv h q hx] at hvw
  rw [metricRm04StandardAt_eq_chart h q hx v w]
  exact hvw

/-- A chart bound for the coefficient numerators and a chart coercivity constant bound the full
curvature norm `|Rm|` (polarization of the algebraic curvature form). -/
theorem sqrt_normSq0S_metricRm04_le_of_chart [T2Space M] (h : SmoothRiemannianMetric I M)
    (q : M) {x : M} (hx : x ∈ (extChartAt I q).source) {C lam : ℝ} (hC : 0 ≤ C)
    (hlam : 0 < lam)
    (hk : ∀ V W : E, |coefficientRm04 (chartCoeff h q) (extChartAt I q x) V W W V| ≤
      C * ‖V‖ ^ 2 * ‖W‖ ^ 2)
    (hco : ∀ V : E, lam * ‖V‖ ^ 2 ≤ chartCoeff h q (extChartAt I q x) V V) :
    Real.sqrt (DifferentialGeometry.Tensor0SBundle.normSq0S h x 4
        (DifferentialGeometry.Geometry.Curvature.metricRm04 h x)) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * (18 * C * lam⁻¹ ^ 2) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis h x
  have hinv := DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal h basis hON
  have hB : DifferentialGeometry.Geometry.Curvature.IsAlgCurvForm
      (fun a b c d : TangentSpace I x =>
        DifferentialGeometry.Geometry.Curvature.metricRm04StandardAt h x a b c d) := by
    change DifferentialGeometry.Geometry.Curvature.IsAlgCurvForm
      (DifferentialGeometry.Geometry.Curvature.tensor04StandardAt
        (DifferentialGeometry.Geometry.Curvature.metricRm04At h x))
    exact DifferentialGeometry.Geometry.Curvature.mem_algebraicCurvatureTensorSubmodule.mp
      (DifferentialGeometry.Geometry.Curvature.metricRm04At_mem_algebraicCurvatureTensorSubmodule
        h x)
  let D : E →L[ℝ] E := mfderiv I 𝓘(ℝ, E) (extChartAt I q) x
  let N : TangentSpace I x → ℝ := fun u => ‖D u‖
  have hN : ∀ u, 0 ≤ N u := fun u => norm_nonneg _
  have hNadd : ∀ u u', N (u + u') ≤ N u + N u' := fun u u' => by
    have hadd : D (u + u') = D u + D u' := map_add D u u'
    change ‖D (u + u')‖ ≤ ‖D u‖ + ‖D u'‖
    rw [hadd]
    exact norm_add_le _ _
  have hk' : ∀ u w : TangentSpace I x,
      |DifferentialGeometry.Geometry.Curvature.metricRm04StandardAt h x u w w u| ≤
        C * N u ^ 2 * N w ^ 2 := by
    intro u w
    rw [metricRm04StandardAt_eq_chart h q hx u w]
    exact hk _ _
  have hr : ∀ a, N (basis a) ≤ Real.sqrt lam⁻¹ := by
    intro a
    refine (abs_of_nonneg (hN _)).symm.le.trans (Real.abs_le_sqrt ?_)
    have h1 := hco (mfderiv I 𝓘(ℝ, E) (extChartAt I q) x (basis a))
    have hee : h.inner x (basis a) (basis a) = 1 := by simp [hON a a]
    rw [chartCoeff_mfderiv h q hx, hee] at h1
    change ‖D (basis a)‖ ^ 2 ≤ lam⁻¹
    calc ‖D (basis a)‖ ^ 2 = lam⁻¹ * (lam * ‖D (basis a)‖ ^ 2) := by
          field_simp
      _ ≤ lam⁻¹ * 1 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hlam.le)
      _ = lam⁻¹ := mul_one _
  have hr4 : Real.sqrt lam⁻¹ ^ 4 = lam⁻¹ ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (inv_nonneg.mpr hlam.le)]
  have hcomp : ∀ slots : Fin 4 → Fin (Module.finrank ℝ (TangentSpace I x)),
      |DifferentialGeometry.Tensor0SBundle.component0S basis
        (DifferentialGeometry.Geometry.Curvature.metricRm04 h x) slots| ≤
        18 * C * lam⁻¹ ^ 2 := by
    intro slots
    have hvec : (fun a => basis (slots a)) = DifferentialGeometry.Geometry.Curvature.vec4
        (basis (slots 0)) (basis (slots 1)) (basis (slots 2)) (basis (slots 3)) := by
      funext a
      fin_cases a <;> rfl
    have hval : DifferentialGeometry.Tensor0SBundle.component0S basis
        (DifferentialGeometry.Geometry.Curvature.metricRm04 h x) slots =
        DifferentialGeometry.Geometry.Curvature.metricRm04StandardAt h x
          (basis (slots 0)) (basis (slots 1)) (basis (slots 2)) (basis (slots 3)) := by
      rw [DifferentialGeometry.Tensor0SBundle.component0S,
        DifferentialGeometry.Geometry.Curvature.metricRm04_apply, hvec]
      rfl
    rw [hval, ← hr4]
    exact hB.abs_le_of_abs_sectional_le N hN hNadd hC hk' (hr _) (hr _) (hr _) (hr _)
  have hbound := DifferentialGeometry.Tensor0SBundle.sqrt_normSq0S_le_card_of_component_bound
    h x 4 basis hinv (DifferentialGeometry.Geometry.Curvature.metricRm04 h x)
    (18 * C * lam⁻¹ ^ 2) (by positivity) hcomp
  have hcard : Real.sqrt (Fintype.card (Fin 4 → Fin (Module.finrank ℝ (TangentSpace I x))) : ℝ) =
      (Module.finrank ℝ E : ℝ) ^ 2 := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    have : ((Module.finrank ℝ (TangentSpace I x) ^ 4 : ℕ) : ℝ) =
        ((Module.finrank ℝ E : ℝ) ^ 2) ^ 2 := by
      change ((Module.finrank ℝ E ^ 4 : ℕ) : ℝ) = _
      push_cast
      ring
    rw [this, Real.sqrt_sq (by positivity)]
  rwa [hcard] at hbound

end Bridges

section Control

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- **LFR50 part A2, eventual form.** If smooth metrics converge in chart coefficients (`C²` on
compact chart sets covering the manifold) to a `C^n` metric with nonnegative finite-order
sectional curvature, then for every `δ > 0` eventually `sec ≥ -δ`, and eventually `|Rm|` is
bounded by one constant. -/
theorem eventually_curvature_control {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hn : (2 : ℕ∞ω) ≤ n)
    (t : Finset M) (L : t → Set E) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hL : ∀ i : t, IsCompact (L i) ∧ L i ⊆ (extChartAt I (i : M)).target)
    (hcover : ∀ x : M, ∃ i : t, x ∈ (extChartAt I (i : M)).source ∧ extChartAt I (i : M) x ∈ L i)
    (hconv : ∀ i : t, MapCPConvergenceOn (L i) 2 (fun k => chartCoeff (gSeq k) (i : M))
      (chartCoeff g (i : M)))
    (hsec : ∀ x (v w : TangentSpace I x), 0 ≤ g.sectionalCurvature x v w) :
    (∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop,
      DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow (gSeq k) (-δ)) ∧
    ∃ B : ℝ, ∀ᶠ k in atTop, ∀ x : M,
      Real.sqrt (DifferentialGeometry.Tensor0SBundle.normSq0S (gSeq k) x 4
        (DifferentialGeometry.Geometry.Curvature.metricRm04 (gSeq k) x)) ≤ B := by
  have hU : ∀ i : t, IsOpen (extChartAt I (i : M)).target := fun i => isOpen_extChartAt_target _
  have hc : ∀ i : t, ∀ k, ContDiffOn ℝ 2 (chartCoeff (gSeq k) (i : M))
      (extChartAt I (i : M)).target := fun i k => contDiffOn_chartCoeff (gSeq k) (by simp) _
  have hc₀ : ∀ i : t, ContDiffOn ℝ 2 (chartCoeff g (i : M)) (extChartAt I (i : M)).target :=
    fun i => contDiffOn_chartCoeff g hn _
  have hsymm : ∀ i : t, ∀ k, ∀ y ∈ (extChartAt I (i : M)).target, ∀ v w : E,
      chartCoeff (gSeq k) (i : M) y v w = chartCoeff (gSeq k) (i : M) y w v :=
    fun i k y _ v w => chartCoeff_symm _ _ y v w
  have hpos : ∀ i : t, ∀ y ∈ (extChartAt I (i : M)).target, ∀ v : E, v ≠ 0 →
      0 < chartCoeff g (i : M) y v v := fun i y hy v hv => chartCoeff_pos g _ hy hv
  have hnonneg : ∀ i : t, ∀ y ∈ L i, ∀ v w : E,
      0 ≤ coefficientRm04 (chartCoeff g (i : M)) y v w w v := by
    intro i y hy v w
    have hyt := (hL i).2 hy
    have h := coefficientRm04_chart_nonneg_of_sectional g hn (i : M)
      ((extChartAt I (i : M)).map_target hyt) (hsec _) v w
    rwa [(extChartAt I (i : M)).right_inv hyt] at h
  constructor
  · intro δ hδ
    have hev : ∀ i : t, ∀ᶠ k in atTop, ∀ y ∈ L i, ∀ v w : E,
        -δ * (chartCoeff (gSeq k) (i : M) y v v * chartCoeff (gSeq k) (i : M) y w w -
          (chartCoeff (gSeq k) (i : M) y v w) ^ 2) ≤
          coefficientRm04 (chartCoeff (gSeq k) (i : M)) y v w w v := fun i =>
      DifferentialGeometry.Analysis.eventually_coefficientRm04_lower (hU i) (hL i).1 (hL i).2
        (hc i) (hc₀ i) (hsymm i) (hpos i) (hconv i) (hnonneg i) δ hδ
    filter_upwards [Filter.eventually_all.2 hev] with k hk x
    obtain ⟨i, hxi, hxL⟩ := hcover x
    exact sectionalBoundedBelowAt_of_chart (gSeq k) (i : M) hxi
      (fun V W => hk i _ hxL V W)
  · have hup : ∀ i : t, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop, ∀ y ∈ L i, ∀ v w : E,
        |coefficientRm04 (chartCoeff (gSeq k) (i : M)) y v w w v| ≤ C * ‖v‖ ^ 2 * ‖w‖ ^ 2 :=
      fun i => DifferentialGeometry.Analysis.exists_eventually_abs_coefficientRm04_le (hU i)
        (hL i).1 (hL i).2 (hc i) (hc₀ i) (hpos i) (hconv i)
    have hco : ∀ i : t, ∃ lam : ℝ, 0 < lam ∧ ∀ᶠ k in atTop, ∀ y ∈ L i, ∀ v : E,
          lam * ‖v‖ ^ 2 ≤ chartCoeff (gSeq k) (i : M) y v v := fun i => by
      obtain ⟨lam, hlam, -, hev⟩ := DifferentialGeometry.Analysis.exists_eventually_coercive
        (hL i).1 (hL i).2 (hc₀ i) (hconv i) (hpos i)
      exact ⟨lam, hlam, hev⟩
    choose C hC hCev using hup
    choose lam hlam hlamev using hco
    refine ⟨∑ i, (Module.finrank ℝ E : ℝ) ^ 2 * (18 * C i * (lam i)⁻¹ ^ 2), ?_⟩
    filter_upwards [Filter.eventually_all.2 hCev, Filter.eventually_all.2 hlamev] with k hk1 hk2 x
    obtain ⟨i, hxi, hxL⟩ := hcover x
    refine (sqrt_normSq0S_metricRm04_le_of_chart (gSeq k) (i : M) hxi (hC i) (hlam i)
      (fun V W => hk1 i _ hxL V W) (fun V => hk2 i _ hxL V)).trans ?_
    exact Finset.single_le_sum (f := fun j : t =>
        (Module.finrank ℝ E : ℝ) ^ 2 * (18 * C j * (lam j)⁻¹ ^ 2))
      (fun j _ => by have := hC j; positivity) (Finset.mem_univ i)

end Control

section Main

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M]

/-- **LFR50 part A (A1–A3).** On a compact manifold with a boundaryless model, a `C^n` metric
`g`, `2 ≤ n`, with nonnegative finite-order sectional curvature is approximated by smooth metrics
`gSeq k` (chart-coefficient `C²` convergence on a finite family of compact chart sets covering
the manifold) such that, for one `B`, one `gRef`, one `Λ` and errors `0 ≤ ε k → 0`:
`|Rm(gSeq k)| ≤ B`, `sec(gSeq k) ≥ -ε k`, and `gSeq k` is `Λ`-bilipschitz to `gRef`. The
sequence is the A1 sequence with a finite prefix dropped and then reindexed. -/
theorem exists_smooth_approximants_of_sectional_nonneg {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hn : (2 : ℕ∞ω) ≤ n)
    (hsec : ∀ x (v w : TangentSpace I x), 0 ≤ g.sectionalCurvature x v w) :
    ∃ (gSeq : ℕ → SmoothRiemannianMetric I M) (B : ℝ) (ε : ℕ → ℝ)
      (gRef : SmoothRiemannianMetric I M) (Λ : ℝ),
      (∀ k (x : M), Real.sqrt (DifferentialGeometry.Tensor0SBundle.normSq0S (gSeq k) x 4
        (DifferentialGeometry.Geometry.Curvature.metricRm04 (gSeq k) x)) ≤ B) ∧
      (∀ k, 0 ≤ ε k) ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ k, DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow (gSeq k) (-ε k)) ∧
      0 < Λ ∧ (∀ k (x : M) (w : TangentSpace I x),
        (gSeq k).inner x w w ≤ Λ * gRef.inner x w w ∧
          gRef.inner x w w ≤ Λ * (gSeq k).inner x w w) ∧
      ∃ (t : Finset M) (L : t → Set E),
        (∀ i : t, IsCompact (L i) ∧ L i ⊆ (extChartAt I (i : M)).target) ∧
        (∀ x : M, ∃ i : t, x ∈ (extChartAt I (i : M)).source ∧
          extChartAt I (i : M) x ∈ L i) ∧
        ∀ i : t, MapCPConvergenceOn (L i) 2 (fun k => chartCoeff (gSeq k) (i : M))
          (chartCoeff g (i : M)) := by
  obtain ⟨t, L, gSeq, Λ, hL, hcover, hconv, hΛ, hbil⟩ := exists_smooth_metric_approximation g hn
  obtain ⟨hlow, B, hB⟩ := eventually_curvature_control g hn t L gSeq hL hcover hconv hsec
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((hlow 1 one_pos).and hB)
  let S : ℕ → Set ℝ := fun k => {δ | 0 ≤ δ ∧
    DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow (gSeq (k + N)) (-δ)}
  have hS1 : ∀ k, (1 : ℝ) ∈ S k := fun k => ⟨zero_le_one, (hN (k + N) (by omega)).1⟩
  have hSbdd : ∀ k, BddBelow (S k) := fun k => ⟨0, fun δ hδ => hδ.1⟩
  let ε : ℕ → ℝ := fun k => sInf (S k)
  have hε0 : ∀ k, 0 ≤ ε k := fun k => Real.sInf_nonneg fun δ hδ => hδ.1
  have hεsec : ∀ k,
      DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow (gSeq (k + N)) (-ε k) := by
    intro k x v w
    obtain ⟨u, -, hu, huS⟩ := exists_seq_tendsto_sInf ⟨1, hS1 k⟩ (hSbdd k)
    have hlim : Tendsto (fun j => -u j * ((gSeq (k + N)).inner x v v *
        (gSeq (k + N)).inner x w w - (gSeq (k + N)).inner x v w ^ 2)) atTop
        (𝓝 (-ε k * ((gSeq (k + N)).inner x v v * (gSeq (k + N)).inner x w w -
          (gSeq (k + N)).inner x v w ^ 2))) := hu.neg.mul_const _
    exact le_of_tendsto hlim (Eventually.of_forall fun j => (huS j).2 x v w)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨K, hK⟩ := eventually_atTop.1 (hlow (δ / 2) (by positivity))
    refine ⟨K, fun k hk => ?_⟩
    have hmem : δ / 2 ∈ S k := ⟨by positivity, hK (k + N) (by omega)⟩
    have hle := csInf_le (hSbdd k) hmem
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hε0 k)]
    change sInf (S k) < δ
    linarith
  exact ⟨fun k => gSeq (k + N), B, ε, gSeq 0, Λ, fun k x => (hN (k + N) (by omega)).2 x, hε0,
    hεlim, hεsec, hΛ, fun k x w => hbil (k + N) x w, t, L, hL, hcover,
    fun i => (hconv i).comp_tendsto_atTop (tendsto_add_atTop_nat N)⟩

end Main

end DifferentialGeometry.Geometry.MetricSmoothing
