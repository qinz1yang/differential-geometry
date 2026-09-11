import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.CompleteManifoldExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.SpeedBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.SmoothExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.JointRegularity
import DifferentialGeometry.Geometry.Operator.Gradient.NormSquaredTime
import DifferentialGeometry.Geometry.Exponential.GaussLemma.Pullback
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs

set_option autoImplicit false

noncomputable section

open Bundle Set MeasureTheory
open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow

section LocalHelpers

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

theorem lScalarGradient_bound_on_compact
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {a b : ℝ} (hreg : Icc a b ⊆ D.regular)
    {Cpt : Set M} (hCpt : IsCompact Cpt) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t ∈ Icc a b, ∀ y ∈ Cpt, ∀ v : TangentSpace I y,
        |(S.base.metric t).inner y
            (gradientFun (I := I) (S.base.metric t) (S.scalar t) y) v| ≤
          C * Real.sqrt ((S.base.metric t).inner y v v) := by
  classical
  let q : ℝ × M → ℝ := fun p ↦
    (S.base.metric p.1).inner p.2
      (gradientFun (I := I) (S.base.metric p.1) (S.scalar p.1) p.2)
      (gradientFun (I := I) (S.base.metric p.1) (S.scalar p.1) p.2)
  have hgram : ∀ (y₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M ↦
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (S.base.metric p.1) y₀ p.2 i j)
        (D.regular ×ˢ (trivializationAt E (TangentSpace I) y₀).baseSet) := by
    intro y₀ i j
    let e := trivializationAt E (TangentSpace I : M → Type _) y₀
    let basis := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E
    let frame : Fin (Module.finrank ℝ E) → ∀ y, TangentSpace I y :=
      e.localFrame basis
    have hframe : IsLocalFrameOn I E ∞ frame e.baseSet := by
      simpa only [frame] using e.isLocalFrameOn_localFrame_baseSet I ∞ basis
    have hcomp := hS.smoothMetric.frameCompSmooth frame hframe i j
    refine hcomp.congr ?_
    intro p hp
    have hframe_eq (k : Fin (Module.finrank ℝ E)) :
        frame k p.2 = DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) y₀ k p.2 := by
      dsimp only [frame]
      rw [e.localFrame_apply_of_mem_baseSet basis hp.2]
      change (e.linearEquivAt ℝ p.2 hp.2).symm (basis k) =
        e.symmL ℝ p.2 ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)
      dsimp only [basis]
      rw [e.linearEquivAt_symm_apply, e.symmL_apply hp.2]
    simp only [DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply, SolutionOn.family_metric]
    rw [hframe_eq i, hframe_eq j]
  have hq : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ q
      (D.regular ×ˢ (univ : Set M)) := by
    simpa only [q, SolutionOn.family_metric] using
      gradSq_joint (I := I) S.family.metric D.regular_isOpen hgram
        S.scalar (scalar_joint (I := I) S hS)
  let f : ℝ × M → ℝ := fun p ↦ Real.sqrt (q p)
  have hf : ContinuousOn f (Icc a b ×ˢ Cpt) := by
    have hcomp := Real.continuous_sqrt.continuousOn.comp
      (hq.continuousOn.mono (Set.prod_mono hreg (subset_univ Cpt)))
      (fun _ _ ↦ mem_univ _)
    exact hcomp
  obtain ⟨C₀, hC₀⟩ :=
    bddAbove_def.mp ((isCompact_Icc.prod hCpt).bddAbove_image hf)
  refine ⟨max 0 C₀, le_max_left _ _, ?_⟩
  intro t ht y hy v
  have hgrad : Real.sqrt (q (t, y)) ≤ max 0 C₀ :=
    (hC₀ (f (t, y)) ⟨(t, y), ⟨ht, hy⟩, rfl⟩).trans (le_max_right _ _)
  have hcs :=
    DifferentialGeometry.Analysis.Laplacian.abs_metric_inner_le_sqrt_metric_quadratic
      (I := I) (M := M) (S.base.metric t) y
      (gradientFun (I := I) (S.base.metric t) (S.scalar t) y) v
  exact hcs.trans (mul_le_mul_of_nonneg_right
    (by simpa only [q] using hgrad) (Real.sqrt_nonneg _))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lRegCurve_reference_integrable [I.Boundaryless]
    (gRef : SmoothRiemannianMetric I M)
    {S : SolutionOn (I := I) (M := M) D} {T : ℝ}
    {alpha : ℝ → M} {x : M} {Z : TangentSpace I x} {b : ℝ}
    (halpha : IsLRegularizedCurveOn S T alpha (Icc (0 : ℝ) b) x Z) :
    IntegrableOn
      (fun s ↦ gRef.inner (alpha s)
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s))
      (Icc (0 : ℝ) b) := by
  have hstate : ContinuousOn
      (fun s ↦ (TotalSpace.mk' E (alpha s)
        (lVelocity (I := I) alpha s) : TangentBundle I M))
      (Icc (0 : ℝ) b) := by
    apply sectionAlongCurve_continuousOn_totalSpace (I := I)
    · intro s hs
      exact (halpha.2.2 s hs).2.1.continuousAt.continuousWithinAt
    · intro s hs
      exact (halpha.2.2 s hs).2.2.1
  let cg : ContinuousRiemannianMetric E
      (TangentSpace I : M → Type _) := gRef.toContinuousRiemannianMetric
  let rb : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  have hcont : ContinuousOn
      (fun s ↦ gRef.inner (alpha s)
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s))
      (Icc (0 : ℝ) b) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hinner := Continuous.inner_bundle (F := E) (B := M)
      (E := (TangentSpace I : M → Type _))
      (b := fun s : Icc (0 : ℝ) b ↦ alpha s)
      (v := fun s : Icc (0 : ℝ) b ↦ lVelocity (I := I) alpha s)
      (w := fun s : Icc (0 : ℝ) b ↦ lVelocity (I := I) alpha s)
      hstate.domRestrict hstate.domRestrict
    exact hinner.congr fun _ ↦ rfl
  exact hcont.integrableOn_compact isCompact_Icc

end LocalHelpers

section InitialVectors

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  {D : RealTimeInterval}

theorem lRegInit_bound_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T : ℝ)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x : M) (b A : ℝ) (hb : 0 < b)
    (hreg : Icc (T - b ^ 2) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (T - b ^ 2) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4
        (S.base.rm04 t y) ≤ K)
    (Z : ℕ → TangentSpace I x)
    (hdom : ∀ n, b ∈ lRegularizedDomain S T x (Z n))
    (hact : ∀ n,
      lRegularizedAction S T (lRegularizedCurve S T x (Z n)) 0 b ≤ A) :
    Bornology.IsBounded (range Z) := by
  classical
  let alpha : ℕ → ℝ → M := fun n ↦ lRegularizedCurve S T x (Z n)
  have hback (s : ℝ) (hs : s ∈ Icc (0 : ℝ) b) :
      T - s ^ 2 ∈ Icc (T - b ^ 2) T := by
    have hs2 : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.1 hb.le).2 hs.2
    exact ⟨sub_le_sub_left hs2 T, sub_le_self T (sq_nonneg s)⟩
  have hclock (s : ℝ) (hs : s ∈ Icc (0 : ℝ) b) :
      T - s ^ 2 ∈ D.regular := hreg (hback s hs)
  have hcurve (n : ℕ) :
      IsLRegularizedCurveOn S T (alpha n) (Icc (0 : ℝ) b) x (Z n) := by
    simpa only [alpha, uIcc_of_le hb.le] using
      lRegularizedCurve_isLRegularizedCurveOn (I := I) S hS T x (Z n) hb (hdom n)
  have hc1 (n : ℕ) :
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 (alpha n) (Icc (0 : ℝ) b) :=
    lRegularizedCurve_c1On (I := I) S hS T x (Z n) (hdom n)
  have hE (n : ℕ) : IntegrableOn
      (fun s ↦ (S.base.metric T).inner (alpha n s)
        (lVelocity (I := I) (alpha n) s) (lVelocity (I := I) (alpha n) s))
      (Icc (0 : ℝ) b) :=
    lRegCurve_reference_integrable (S.base.metric T) (hcurve n)
  have hkin (n : ℕ) :
      IntervalIntegrable (lRegularizedSpeedSq S T (alpha n)) volume 0 b :=
    intervalIntegrable_lRegularizedSpeedSq_of_contMDiffOn_one (I := I) S hS.smoothMetric ⟨hS.scalarCont⟩
      T 0 b hb.le (alpha n) (hc1 n) hclock
  have hLag (n : ℕ) :
      IntervalIntegrable (lRegularizedLagrangian S T (alpha n)) volume 0 b :=
    intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one (I := I) S hS.smoothMetric ⟨hS.scalarCont⟩
      T 0 b hb.le (alpha n) (hc1 n) hclock
  obtain ⟨Cpt, hCpt, himage⟩ :=
    lRegularizedRanges_of_rm (I := I) S hS K T hg alpha x 0 b A
      (by norm_num) hb.le hreg hRm
      (fun n ↦ by simp only [alpha, lRegularizedCurve_zero])
      hc1 hE hkin hLag (fun n ↦ hact n)
  obtain ⟨Cg, hCg, hgrad⟩ :=
    lScalarGradient_bound_on_compact S hS hreg hCpt
  let P : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K
  let C : ℝ := max Cg P
  have hC : 0 ≤ C := hCg.trans (le_max_left Cg P)
  have hquad := twoTensorQuadBound_of_solutions (I := I)
    (fun _ : ℕ ↦ S) univ (T - b ^ 2) T K
    (fun _ t ht y _ ↦ hRm t ht y)
  have hpot (n : ℕ) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) b) :
      -2 * b ^ 2 * P ≤ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha n s) :=
    lRegularizedPot_lower_rm (I := I) S K T b hb.le hRm s hs (alpha n s)
  let Bkin : ℝ := 2 * (A - (-2 * b ^ 2 * P) * b)
  have hkinBound (n : ℕ) :
      (∫ s in 0..b, lRegularizedSpeedSq S T (alpha n) s) ≤ Bkin := by
    have h := lRegularizedKinetic_le (I := I) S T (alpha n) 0 b A
      (-2 * b ^ 2 * P) hb.le (hpot n) (hkin n) (hLag n) (hact n)
    simpa only [sub_zero, Bkin] using h
  let Q : ℝ :=
    Real.exp ((1 + 2 * C * b ^ 2 + 4 * C * b) * b) *
      (Bkin + b * ((1 + 2 * C * b ^ 2) /
        (1 + 2 * C * b ^ 2 + 4 * C * b)))
  have hmetric (n : ℕ) :
      4 * b * (S.base.metric T).inner x (Z n) (Z n) ≤ Q := by
    apply lRegularizedInitialVector_inner_le_of_integral_speedSq_le (I := I) S hS T b b C b Bkin
      hb le_rfl le_rfl hC (hcurve n)
    · intro s hs
      have hy : alpha n s ∈ Cpt := himage n ⟨s, hs, rfl⟩
      have h := hgrad (T - s ^ 2) (hback s hs) (alpha n s) hy
        (lVelocity (I := I) (alpha n) s)
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_left Cg P)
        (Real.sqrt_nonneg _))
    · intro s hs
      have h := hquad.2 0 (T - s ^ 2) (hback s hs)
        (alpha n s) (mem_univ _) (lVelocity (I := I) (alpha n) s)
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_right Cg P)
        (lRegularizedSpeedSq_nonneg (I := I) S T (alpha n) s))
    · exact hkinBound n
  let c : ℝ := metricCoerciveConst (I := I) (S.base.metric T) x
  have hc : 0 < c := metricCoerciveConst_pos (I := I) (S.base.metric T) x
  let d : ℝ := 4 * b * c
  have hd : 0 < d := mul_pos (mul_pos (by norm_num) hb) hc
  have hnorm (n : ℕ) : ‖(Z n : E)‖ ≤ Real.sqrt (Q / d) := by
    have hcoerc : c * ‖(Z n : E)‖ ^ 2 ≤
        (S.base.metric T).inner x (Z n) (Z n) :=
      metricCoerciveConst_le (I := I) (S.base.metric T) x (Z n)
    have hscaled : d * ‖(Z n : E)‖ ^ 2 ≤ Q := by
      calc
        d * ‖(Z n : E)‖ ^ 2 = (4 * b) * (c * ‖(Z n : E)‖ ^ 2) := by
          dsimp only [d]
          ring
        _ ≤ (4 * b) * (S.base.metric T).inner x (Z n) (Z n) :=
          mul_le_mul_of_nonneg_left hcoerc (mul_nonneg (by norm_num) hb.le)
        _ ≤ Q := hmetric n
    have hsq : ‖(Z n : E)‖ ^ 2 ≤ Q / d := by
      apply (le_div_iff₀ hd).2
      simpa only [mul_comm] using hscaled
    have h := Real.sqrt_le_sqrt hsq
    simpa only [Real.sqrt_sq (norm_nonneg (Z n : E))] using h
  refine (Metric.isBounded_iff_subset_closedBall (0 : TangentSpace I x)).2
    ⟨Real.sqrt (Q / d), ?_⟩
  rintro z ⟨n, rfl⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm n

end InitialVectors

end DifferentialGeometry.PDE.RicciFlow

end
