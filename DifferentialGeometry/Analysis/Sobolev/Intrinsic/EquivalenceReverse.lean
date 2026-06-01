import DifferentialGeometry.Analysis.Sobolev.Intrinsic.EquivalenceFull
import DifferentialGeometry.Analysis.Sobolev.Manifold.MeasureBridgeUniform

/-!
# Reverse bridge: intrinsic-`L^p` Sobolev components to chart-based norm

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)`
modelled on a finite-dimensional real inner-product space `E`, and an exponent
`1 ≤ p < ∞`, this file provides the reverse direction of the chart-based to
intrinsic-`L^p` Sobolev norm comparison: a uniform-in-`u` bound

  `wkpNormChart g 1 p u ≤ ENNReal.ofReal C *
      (eLpNorm u p μ_g + eLpNorm √g(∇u, ∇u) p μ_g)`

for every smooth `u : M → ℝ`. The constant `C ≥ 0` depends only on `g`, `p`,
and the canonical chart-atlas partition of unity, and is otherwise uniform in
`u`.

The forward direction (uniform-in-`u`) is delivered in `EquivalenceFull.lean`
via `w1pNormIntrinsicLp_le_const_mul_wkpNormChart_smooth_uniform_full`.

## Mathematical strategy

For each chart `α` in the canonical finite POU finset, we bound the per-α
component of `wkpNormChart` by the manifold L^p norms on the chart-α support.

The L^p part `eLpNorm (chartPushed ρ α u) p (volume.restrict ChTE)` is bounded
via the existing reverse chart-density bridge
`eLpNorm_chartPushedRaw_le_const_mul_eLpNorm_riemannianMeasure_uniform_of_subset`.

The gradient part requires a direct estimate: for `y` in the chart target,
the partial derivative `(∂_i chartSmoothExt α (ρ_α u))(y)` is, by the chain rule,
a manifold derivative `mfderiv (ρ_α u) x w_i(x)` where `w_i(x)` is the
pushforward of the standard Euclidean basis vector `e_i` through the chart
inverse to a tangent vector at `x`. By Cauchy-Schwarz on the metric:
`|mfderiv (ρ_α u) x w_i(x)| = |g.inner x (gradFun (ρ_α u) x) w_i(x)|
  ≤ √g(grad, grad)(x) · √g(w_i(x), w_i(x))`. The factor `√g(w_i(x), w_i(x))`
is a continuous function of `x`, bounded above on the compact support of
`ρ_α`. The Leibniz rule on `ρ_α u` then bounds `√g(grad(ρ_α u), grad(ρ_α u))`
by a constant times `√g(grad u, grad u) + |u|`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace EquivalenceReverse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.Chart

local notation "EuclN_E" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- Cauchy-Schwarz inequality for the metric inner product `g.inner x` at a
fixed point `x`. The proof uses the standard polynomial argument applied to
`t ↦ g.inner x (v + t • w) (v + t • w) ≥ 0`. -/
private lemma g_inner_cauchy_schwarz_sq
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    (g.inner x v w)^2 ≤ g.inner x v v * g.inner x w w := by
  have h_inner_self_nn : ∀ z : TangentSpace I x, 0 ≤ g.inner x z z := by
    intro z
    by_cases hz : z = 0
    · rw [hz]
      change ((g.inner x) (0 : TangentSpace I x)) (0 : TangentSpace I x) ≥ 0
      rw [(g.inner x).map_zero]
      change (0 : TangentSpace I x →L[ℝ] ℝ) (0 : TangentSpace I x) ≥ 0
      simp
    · exact (g.pos x z hz).le
  have hsym : g.inner x v w = g.inner x w v := g.symm x v w
  have h_expand : ∀ t : ℝ, g.inner x (v + t • w) (v + t • w) =
      g.inner x v v + 2 * t * g.inner x v w + t^2 * g.inner x w w := by
    intro t
    have h1 : (g.inner x) (v + t • w) =
        (g.inner x) v + (g.inner x) (t • w) :=
      (g.inner x).map_add v (t • w)
    have h2 : (g.inner x) (t • w) = t • ((g.inner x) w) :=
      (g.inner x).map_smul t w
    have h_step :
        g.inner x (v + t • w) (v + t • w) =
          (g.inner x v) (v + t • w) + (g.inner x) (t • w) (v + t • w) := by
      have happly : g.inner x (v + t • w) =
          (g.inner x) v + (g.inner x) (t • w) := h1
      rw [show g.inner x (v + t • w) (v + t • w) =
            ((g.inner x) (v + t • w)) (v + t • w) from rfl, happly]
      rfl
    rw [h_step]
    rw [(g.inner x v).map_add, (g.inner x v).map_smul]
    rw [h2]
    rw [show ((t • (g.inner x) w) : TangentSpace I x →L[ℝ] ℝ) (v + t • w)
          = t * ((g.inner x w) (v + t • w)) from by
      change t • ((g.inner x) w) (v + t • w) = t * ((g.inner x w) (v + t • w))
      rw [smul_eq_mul]]
    rw [(g.inner x w).map_add, (g.inner x w).map_smul]
    rw [hsym]
    simp only [smul_eq_mul]
    ring
  have h_polynom : ∀ t : ℝ, 0 ≤
      g.inner x v v + 2 * t * g.inner x v w + t^2 * g.inner x w w := fun t => by
    rw [← h_expand t]; exact h_inner_self_nn _
  have h_v_nn : 0 ≤ g.inner x v v := h_inner_self_nn v
  have h_w_nn : 0 ≤ g.inner x w w := h_inner_self_nn w
  by_cases h_w_zero : g.inner x w w = 0
  · have h_zero : g.inner x v w = 0 := by
      by_contra h_ne
      set t₀ : ℝ := -(g.inner x v v + 1) / (2 * g.inner x v w)
      have h_poly_t₀ := h_polynom t₀
      rw [h_w_zero] at h_poly_t₀
      have h_simp :
          g.inner x v v + 2 * t₀ * g.inner x v w + t₀^2 * 0 =
            g.inner x v v + 2 * t₀ * g.inner x v w := by ring
      rw [h_simp] at h_poly_t₀
      have h_eval : 2 * t₀ * g.inner x v w = -(g.inner x v v + 1) := by
        change 2 * (-(g.inner x v v + 1) / (2 * g.inner x v w)) *
            g.inner x v w = -(g.inner x v v + 1)
        field_simp
      linarith
    rw [h_zero]
    have h_prod_nn : 0 ≤ g.inner x v v * g.inner x w w :=
      mul_nonneg h_v_nn h_w_nn
    have hzero_sq : (0 : ℝ)^2 ≤ g.inner x v v * g.inner x w w := by
      rw [zero_pow (Nat.succ_ne_zero 1)]
      exact h_prod_nn
    exact hzero_sq
  · have h_w_pos : 0 < g.inner x w w :=
      lt_of_le_of_ne h_w_nn (Ne.symm h_w_zero)
    set t₀ : ℝ := -g.inner x v w / g.inner x w w
    have h_poly_t₀ := h_polynom t₀
    have h_eval :
        g.inner x v v + 2 * t₀ * g.inner x v w + t₀^2 * g.inner x w w =
          g.inner x v v - (g.inner x v w)^2 / g.inner x w w := by
      change g.inner x v v +
          2 * (-g.inner x v w / g.inner x w w) * g.inner x v w +
          (-g.inner x v w / g.inner x w w)^2 * g.inner x w w =
        g.inner x v v - (g.inner x v w)^2 / g.inner x w w
      field_simp
      ring
    rw [h_eval] at h_poly_t₀
    have h_step : (g.inner x v w)^2 / g.inner x w w ≤ g.inner x v v := by linarith
    rw [div_le_iff₀ h_w_pos] at h_step
    linarith

/-- Square-root form of the metric Cauchy-Schwarz inequality. -/
private lemma abs_g_inner_le_sqrt_mul_sqrt
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    |g.inner x v w| ≤ Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) := by
  have h_inner_self_nn : ∀ z : TangentSpace I x, 0 ≤ g.inner x z z := by
    intro z
    by_cases hz : z = 0
    · rw [hz]
      change ((g.inner x) (0 : TangentSpace I x)) (0 : TangentSpace I x) ≥ 0
      rw [(g.inner x).map_zero]
      change (0 : TangentSpace I x →L[ℝ] ℝ) (0 : TangentSpace I x) ≥ 0
      simp
    · exact (g.pos x z hz).le
  have h_sq := g_inner_cauchy_schwarz_sq (I := I) g x v w
  have h_v_nn : 0 ≤ g.inner x v v := h_inner_self_nn v
  have h_w_nn : 0 ≤ g.inner x w w := h_inner_self_nn w
  have h_abs_sq : |g.inner x v w|^2 = (g.inner x v w)^2 := sq_abs _
  have h_sqrt_le :
      Real.sqrt (|g.inner x v w|^2) ≤
        Real.sqrt (g.inner x v v * g.inner x w w) := by
    rw [h_abs_sq]
    exact Real.sqrt_le_sqrt h_sq
  rw [Real.sqrt_sq (abs_nonneg _)] at h_sqrt_le
  rw [Real.sqrt_mul h_v_nn] at h_sqrt_le
  exact h_sqrt_le

/-- The "chart-target unit" tangent vector at `x` corresponding to the
standard Euclidean basis vector `e_i` (transported back through `toEuclidean`
and through the chart trivialization). This is the chart pushforward of
`(toEuclidean.symm) e_i ∈ E` to a tangent vector at `x`. -/
private noncomputable def chartTargetUnitFiber (α : M)
    (i : Fin (Module.finrank ℝ E)) (x : M) : TangentSpace I x :=
  (trivializationAt E (TangentSpace I) α).symm x
    ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E).symm
      (EuclideanSpace.single i (1 : ℝ)))

private lemma chartTargetUnit_smoothOn (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (chartTargetUnitFiber (I := I) α i x))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  set v_E : E := (toEuclidean (E := E) : E ≃L[ℝ] EuclN_E).symm
    (EuclideanSpace.single i (1 : ℝ)) with hv_E_def
  have hiff :=
    ((trivializationAt E (TangentSpace I) α)).contMDiffOn_section_baseSet_iff
      (IB := I) (n := ∞)
      (s := fun x : M => (trivializationAt E (TangentSpace I) α).symm x v_E)
  refine hiff.mpr ?_
  have hconst : ContMDiffOn I 𝓘(ℝ, E) ∞ (fun _ : M => v_E)
      (trivializationAt E (TangentSpace I) α).baseSet := contMDiffOn_const
  refine hconst.congr ?_
  intro x hx
  exact congrArg Prod.snd
    ((trivializationAt E (TangentSpace I) α).apply_mk_symm hx v_E)

/-- The function `x ↦ g.inner x (w_i(x)) (w_i(x))` is continuous on the chart
base set. -/
private lemma g_inner_chartTargetUnit_continuousOn
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) (i : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun x : M => g.inner x
        (chartTargetUnitFiber (I := I) α i x)
        (chartTargetUnitFiber (I := I) α i x))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  have hg : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        b (g.inner b))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    g.contMDiff.contMDiffOn
  have hv := chartTargetUnit_smoothOn (I := I) α i
  have happ :
      ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun m : M => (⟨m,
            g.inner m
              (chartTargetUnitFiber (I := I) α i m)
              (chartTargetUnitFiber (I := I) α i m)⟩ :
              TotalSpace ℝ (Bundle.Trivial M ℝ)))
        (trivializationAt E (TangentSpace I) α).baseSet :=
    ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (b := id) hg hv hv
  intro x hx
  have hpx := happ x hx
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpx
  exact (hpx.2.continuousWithinAt)

/-- Bound on `g.inner x (w_i(x)) (w_i(x))` over the compact `tsupport(ρ_α)`,
summed over `i`. -/
private noncomputable def chartTargetUnitSqSumSupOnPouTsupport
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) : ℝ := by
  classical
  set Kα : Set M := tsupport
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKα_def
  by_cases hKα_ne : Kα.Nonempty
  · have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
    have hKα_sub : Kα ⊆ (chartAt H α).source :=
      DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
    have hKα_base : Kα ⊆ (trivializationAt E (TangentSpace I) α).baseSet := by
      intro x hx
      rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]
      exact hKα_sub hx
    have h_cont : ContinuousOn
        (fun x : M => ∑ i : Fin (Module.finrank ℝ E),
          g.inner x
            (chartTargetUnitFiber (I := I) α i x)
            (chartTargetUnitFiber (I := I) α i x)) Kα := by
      apply continuousOn_finset_sum
      intro i _
      exact (g_inner_chartTargetUnit_continuousOn (I := I) g α i).mono hKα_base
    exact (hKα_compact.image_of_continuousOn h_cont).bddAbove.choose
  · exact 0

private lemma chartTargetUnitSqSumSupOnPouTsupport_nonneg
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) :
    0 ≤ chartTargetUnitSqSumSupOnPouTsupport (I := I) (M := M) g α := by
  classical
  unfold chartTargetUnitSqSumSupOnPouTsupport
  set Kα : Set M := tsupport
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKα_def
  by_cases hKα_ne : Kα.Nonempty
  · rw [dif_pos hKα_ne]
    have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
    have hKα_sub : Kα ⊆ (chartAt H α).source :=
      DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
    have hKα_base : Kα ⊆ (trivializationAt E (TangentSpace I) α).baseSet := by
      intro x hx
      rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]
      exact hKα_sub hx
    have h_cont : ContinuousOn
        (fun x : M => ∑ i : Fin (Module.finrank ℝ E),
          g.inner x
            (chartTargetUnitFiber (I := I) α i x)
            (chartTargetUnitFiber (I := I) α i x)) Kα := by
      apply continuousOn_finset_sum
      intro i _
      exact (g_inner_chartTargetUnit_continuousOn (I := I) g α i).mono hKα_base
    set hImg :=
      (hKα_compact.image_of_continuousOn h_cont).bddAbove
    obtain ⟨x₀, hx₀⟩ := hKα_ne
    have h_val_nn : (0 : ℝ) ≤
        ∑ i : Fin (Module.finrank ℝ E),
          g.inner x₀
            (chartTargetUnitFiber (I := I) α i x₀)
            (chartTargetUnitFiber (I := I) α i x₀) := by
      apply Finset.sum_nonneg
      intro i _
      by_cases hzero : chartTargetUnitFiber (I := I) α i x₀ = 0
      · rw [hzero]
        change ((g.inner x₀) (0 : TangentSpace I x₀)) (0 : TangentSpace I x₀) ≥ 0
        rw [(g.inner x₀).map_zero]
        change (0 : TangentSpace I x₀ →L[ℝ] ℝ) (0 : TangentSpace I x₀) ≥ 0
        simp
      · exact (g.pos x₀ _ hzero).le
    have hx₀_val :
        (∑ i : Fin (Module.finrank ℝ E),
          g.inner x₀
            (chartTargetUnitFiber (I := I) α i x₀)
            (chartTargetUnitFiber (I := I) α i x₀)) ∈
        (fun x : M => ∑ i : Fin (Module.finrank ℝ E),
          g.inner x
            (chartTargetUnitFiber (I := I) α i x)
            (chartTargetUnitFiber (I := I) α i x)) '' Kα :=
      ⟨x₀, hx₀, rfl⟩
    have h_le := hImg.choose_spec hx₀_val
    exact le_trans h_val_nn h_le
  · rw [dif_neg hKα_ne]

/-- For `x ∈ tsupport ρ_α`, the sum `∑ᵢ g.inner x (w_i(x)) (w_i(x))` is bounded by
the chosen sup. -/
private lemma chartTargetUnitSqSum_le_sup
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) {x : M}
    (hx : x ∈ tsupport
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :
    ∑ i : Fin (Module.finrank ℝ E),
        g.inner x
          (chartTargetUnitFiber (I := I) α i x)
          (chartTargetUnitFiber (I := I) α i x) ≤
      chartTargetUnitSqSumSupOnPouTsupport (I := I) (M := M) g α := by
  classical
  unfold chartTargetUnitSqSumSupOnPouTsupport
  set Kα : Set M := tsupport
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKα_def
  have hKα_ne : Kα.Nonempty := ⟨x, hx⟩
  rw [dif_pos hKα_ne]
  have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
  have hKα_sub : Kα ⊆ (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
  have hKα_base : Kα ⊆ (trivializationAt E (TangentSpace I) α).baseSet := by
    intro y hy
    rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]
    exact hKα_sub hy
  have h_cont : ContinuousOn
      (fun y : M => ∑ i : Fin (Module.finrank ℝ E),
        g.inner y
          (chartTargetUnitFiber (I := I) α i y)
          (chartTargetUnitFiber (I := I) α i y)) Kα := by
    apply continuousOn_finset_sum
    intro i _
    exact (g_inner_chartTargetUnit_continuousOn (I := I) g α i).mono hKα_base
  set hImg :=
    (hKα_compact.image_of_continuousOn h_cont).bddAbove
  exact hImg.choose_spec ⟨x, hx, rfl⟩

/-- `mfderiv (extChartAt α) x` applied to `(triv.symm x v_E)` returns `v_E`,
for `x` in the trivialization base set and `v_E ∈ E`. -/
private lemma mfderiv_extChartAt_apply_triv_symm
    (α : M) {x : M} (hxchart : x ∈ (chartAt H α).source) (v_E : E) :
    mfderiv I 𝓘(ℝ, E) (extChartAt I α) x
      ((trivializationAt E (TangentSpace I) α).symm x v_E) = v_E := by
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]
    exact hxchart
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I)
    (x₀ := α) (x := x) hxchart]
  have h_symm_eq : ((trivializationAt E (TangentSpace I) α).symm x
        : E → TangentSpace I x) v_E
      = ((trivializationAt E (TangentSpace I) α).symmL ℝ x : E →L[ℝ] TangentSpace I x) v_E := rfl
  rw [h_symm_eq]
  exact Trivialization.continuousLinearMapAt_symmL
    (R := ℝ) (trivializationAt E (TangentSpace I) α) hbase v_E

/-- General chain-rule identity (mirrors
`mfderiv_chartBasisVecFiber_of_mdifferentiableAt` with a constant vector
parameter): for `f` mdifferentiable at `x`, `x` in the chart source,
`extChartAt α x` in the interior of the chart target, and any `v_E ∈ E`,
`mfderiv f x ((triv.symm x) v_E) = fderiv (scalarOnE α f) (φ x) v_E`. -/
private lemma mfderiv_triv_symm_const_eq_fderiv_scalarOnE
    (α : M) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hxchart : x ∈ (chartAt H α).source)
    (hx_int : extChartAt I α x ∈ interior (extChartAt I α).target) (v_E : E) :
    mfderiv I 𝓘(ℝ, ℝ) f x
        ((trivializationAt E (TangentSpace I) α).symm x v_E) =
      fderiv ℝ
        (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
          (I := I) α f) (extChartAt I α x) v_E := by
  classical
  set φ := extChartAt I α
  have hxsrc : x ∈ φ.source := by
    rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
      (I := I)]; exact hxchart
  have hcomp_eq : ∀ᶠ y in 𝓝 x, f y =
      (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
        (I := I) α f) (φ y) := by
    have hsrc_nhd : φ.source ∈ 𝓝 x :=
      (isOpen_extChartAt_source (I := I) α).mem_nhds hxsrc
    filter_upwards [hsrc_nhd] with y hy
    rw [DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_def, φ.left_inv hy]
  have hcong : f =ᶠ[𝓝 x]
      (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
        (I := I) α f) ∘ (extChartAt I α) := hcomp_eq
  have hmfderiv_cong : mfderiv I 𝓘(ℝ, ℝ) f x =
      mfderiv I 𝓘(ℝ, ℝ)
        ((DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
          (I := I) α f) ∘ (extChartAt I α)) x :=
    Filter.EventuallyEq.mfderiv_eq hcong
  rw [hmfderiv_cong]
  have hphi_mdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I α) x :=
    mdifferentiableAt_extChartAt (I := I) (x := α) hxchart
  have hphi_symm_mdiff :
      MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I α).symm (φ x) := by
    have hcontMDiffOn : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
        (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
    have htgt_int : (extChartAt I α).target ∈ 𝓝 (φ x) := by
      have hint_open : IsOpen (interior (extChartAt I α).target) := isOpen_interior
      exact mem_nhds_iff.mpr ⟨interior _, interior_subset, hint_open, hx_int⟩
    have hcont_at : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I α).symm (φ x) :=
      (hcontMDiffOn (φ x) (interior_subset hx_int)).contMDiffAt htgt_int
    exact hcont_at.mdifferentiableAt (by simp)
  have hsymm_at_x : (extChartAt I α).symm (φ x) = x := φ.left_inv hxsrc
  have hf_at_symm : MDifferentiableAt I 𝓘(ℝ, ℝ) f ((extChartAt I α).symm (φ x)) := by
    rw [hsymm_at_x]; exact hf
  have hf_comp_symm : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
      (f ∘ (extChartAt I α).symm) (φ x) :=
    hf_at_symm.comp (φ x) hphi_symm_mdiff
  have hscalar_eq :
      (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
        (I := I) α f) = f ∘ (extChartAt I α).symm := by
    funext y; rfl
  have hg_mdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
      (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
        (I := I) α f) (φ x) := by
    rw [hscalar_eq]; exact hf_comp_symm
  have hchain :
      mfderiv I 𝓘(ℝ, ℝ)
          ((DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
            (I := I) α f) ∘ (extChartAt I α)) x =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
          (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
            (I := I) α f) (φ x)).comp
          (mfderiv I 𝓘(ℝ, E) (extChartAt I α) x) :=
    mfderiv_comp x hg_mdiff hphi_mdiff
  rw [hchain]
  rw [show mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
      (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
        (I := I) α f) (φ x)
      = fderiv ℝ
        (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
          (I := I) α f) (φ x) from
        mfderiv_eq_fderiv (𝕜 := ℝ)
          (f := DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
            (I := I) α f)]
  change (fderiv ℝ
          (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
            (I := I) α f) (φ x))
        ((mfderiv I 𝓘(ℝ, E) (extChartAt I α) x)
          ((trivializationAt E (TangentSpace I) α).symm x v_E)) =
      (fderiv ℝ
          (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
            (I := I) α f) (φ x)) v_E
  rw [mfderiv_extChartAt_apply_triv_symm (I := I) α hxchart v_E]

/-- Chain rule: `fderiv (chartSmoothExt α f) y (e_i)` equals
`fderiv (scalarOnE α f) (toEuclidean.symm y) (toEuclidean.symm e_i)`
for `y ∈ chartTargetEuclid α`, where `e_i = EuclideanSpace.single i 1`. -/
private lemma fderiv_chartSmoothExt_apply_eq_fderiv_scalarOnE
    [I.Boundaryless]
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (_hf_supp : tsupport f ⊆ (chartAt H α).source)
    (_hf_compact : IsCompact (tsupport f))
    {y : EuclN_E}
    (hy : y ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α)
    (i : Fin (Module.finrank ℝ E)) :
    fderiv ℝ
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α f) y (EuclideanSpace.single i (1 : ℝ)) =
      fderiv ℝ
        (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
          (I := I) α f) ((toEuclidean (E := E)).symm y)
          ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E).symm
            (EuclideanSpace.single i (1 : ℝ))) := by
  classical
  have h_chartTarget_open :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) (α := α)
  have h_chartTarget_nhds :
      DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α ∈ 𝓝 y :=
    h_chartTarget_open.mem_nhds hy
  have h_eqf : (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
      (I := I) (M := M) α f) =ᶠ[𝓝 y]
      ((DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
        (I := I) α f) ∘
        (fun z' : EuclN_E => (toEuclidean (E := E)).symm z')) := by
    filter_upwards [h_chartTarget_nhds] with z' hz'
    have hz'_target : (toEuclidean (E := E)).symm z' ∈ (extChartAt I α).target := by
      rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_eq_preimage_symm
        (I := I) (M := M)] at hz'
      exact hz'
    change (if (toEuclidean (E := E)).symm z' ∈ (extChartAt I α).target then
          f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z'))
        else (0 : ℝ)) = _
    rw [if_pos hz'_target]
    rfl
  have hsymm_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_eq_preimage_symm
      (I := I) (M := M)] at hy
    exact hy
  have h_scalar_smooth :=
    DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_contDiffOn
      (I := I) α hf
  have h_target_open : IsOpen (extChartAt I α).target :=
    isOpen_extChartAt_target (I := I) α
  have h_sym_y_target_nhds : (extChartAt I α).target ∈ 𝓝
      ((toEuclidean (E := E)).symm y) :=
    h_target_open.mem_nhds hsymm_target
  have h_scalar_diffAt : DifferentiableAt ℝ
      (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
        (I := I) α f) ((toEuclidean (E := E)).symm y) := by
    have h_at : ContDiffAt ℝ ∞
        (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
          (I := I) α f) ((toEuclidean (E := E)).symm y) :=
      (h_scalar_smooth.contDiffWithinAt hsymm_target).contDiffAt h_sym_y_target_nhds
    exact h_at.differentiableAt (by simp)
  have h_TE_symm_diffAt : DifferentiableAt ℝ
      (fun z' : EuclN_E => (toEuclidean (E := E)).symm z') y :=
    ((toEuclidean (E := E)).symm).differentiable.differentiableAt
  have h_fderiv_eq :
      fderiv ℝ
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α f) y =
        (fderiv ℝ
          (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
            (I := I) α f) ((toEuclidean (E := E)).symm y)).comp
          (fderiv ℝ
            (fun z' : EuclN_E => (toEuclidean (E := E)).symm z') y) := by
    rw [h_eqf.fderiv_eq]
    exact fderiv_comp y h_scalar_diffAt h_TE_symm_diffAt
  have h_TE_symm_fderiv :
      fderiv ℝ (fun z' : EuclN_E => (toEuclidean (E := E)).symm z') y =
        ((toEuclidean (E := E)).symm : EuclN_E →L[ℝ] E) :=
    ((toEuclidean (E := E)).symm).fderiv
  rw [h_TE_symm_fderiv] at h_fderiv_eq
  rw [h_fderiv_eq]
  rfl

/-- For smooth `f` with `tsupport f ⊆ tsupport(ρ_α)`, and `y ∈ chartTargetEuclid α`
with `x = (extChartAt α)^{-1}(toEuclidean.symm y)`:
`(fderiv (chartSmoothExt α f) y (e_i))² ≤ g(grad,grad)(x) · g(w_i,w_i)(x)`. -/
private lemma sq_fderiv_chartSmoothExt_apply_le_g_inner_mul
    [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_supp_chart : tsupport f ⊆ (chartAt H α).source)
    (hf_compact : IsCompact (tsupport f))
    {y : EuclN_E}
    (hy : y ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α)
    (i : Fin (Module.finrank ℝ E)) :
    let x := (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
    (fderiv ℝ
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α f) y
        (EuclideanSpace.single i (1 : ℝ)))^2 ≤
      g.inner x
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
            (I := I) g f x)
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
            (I := I) g f x) *
        g.inner x
          (chartTargetUnitFiber (I := I) α i x)
          (chartTargetUnitFiber (I := I) α i x) := by
  classical
  intro x
  have hsymm_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_eq_preimage_symm
      (I := I) (M := M)] at hy
    exact hy
  have hx_source : x ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hsymm_target
  have hxchart : x ∈ (chartAt H α).source := by
    rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
      (I := I) (M := M)] at hx_source
    exact hx_source
  have hx_int : extChartAt I α x ∈ interior (extChartAt I α).target := by
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
    exact (extChartAt I α).map_source hx_source
  have hxy : extChartAt I α x = (toEuclidean (E := E)).symm y := by
    change extChartAt I α ((extChartAt I α).symm
        ((toEuclidean (E := E)).symm y)) = (toEuclidean (E := E)).symm y
    exact (extChartAt I α).right_inv hsymm_target
  have hf_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) f x :=
    hf.mdifferentiable (by simp) x
  have h_fderiv_eq_chain := fderiv_chartSmoothExt_apply_eq_fderiv_scalarOnE
    (I := I) (M := M) α hf hf_supp_chart hf_compact (y := y) hy i
  set v_E : E := (toEuclidean (E := E) : E ≃L[ℝ] EuclN_E).symm
    (EuclideanSpace.single i (1 : ℝ)) with hv_E_def
  have h_mfderiv_eq :
      fderiv ℝ
          (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
            (I := I) α f) ((toEuclidean (E := E)).symm y) v_E =
        mfderiv I 𝓘(ℝ, ℝ) f x
          ((trivializationAt E (TangentSpace I) α).symm x v_E) := by
    rw [← hxy]
    exact (mfderiv_triv_symm_const_eq_fderiv_scalarOnE (I := I)
      α hf_diff hxchart hx_int v_E).symm
  have h_combined :
      fderiv ℝ
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α f) y
          (EuclideanSpace.single i (1 : ℝ)) =
        mfderiv I 𝓘(ℝ, ℝ) f x
          ((trivializationAt E (TangentSpace I) α).symm x v_E) := by
    rw [h_fderiv_eq_chain, h_mfderiv_eq]
  have h_triv_symm_eq :
      (trivializationAt E (TangentSpace I) α).symm x v_E =
        chartTargetUnitFiber (I := I) α i x := rfl
  rw [h_combined, h_triv_symm_eq]
  rw [← DifferentialGeometry.Integral.DivergenceTheorem.inner_gradFun
    (I := I) g f x (chartTargetUnitFiber (I := I) α i x)]
  exact g_inner_cauchy_schwarz_sq (I := I) g x
    (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
      (I := I) g f x)
    (chartTargetUnitFiber (I := I) α i x)

/-- Leibniz: `gradFun g (ρ · u) x = ρ(x) · gradFun g u x + u(x) · gradFun g ρ x`. -/
private lemma gradFun_mul_pointwise
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {ρ u : M → ℝ} {x : M}
    (hρ : MDifferentiableAt I 𝓘(ℝ, ℝ) ρ x)
    (hu : MDifferentiableAt I 𝓘(ℝ, ℝ) u x) :
    DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g
      (fun y : M => ρ y * u y) x =
    ρ x • DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x +
    u x • DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g ρ x := by
  classical
  apply DifferentialGeometry.Integral.DivergenceTheorem.metricFlatLinear_injective
    (I := I) g x
  ext v
  change g.inner x
      (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g
        (fun y : M => ρ y * u y) x) v =
    g.inner x
      (ρ x • DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x +
        u x • DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g ρ x) v
  rw [DifferentialGeometry.Integral.DivergenceTheorem.inner_gradFun (I := I) g _ x v]
  have h_fun_eq : (fun y : M => ρ y * u y) = ρ * u := by funext y; rfl
  set d_ρ : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) ρ x with hd_ρ_def
  set d_u : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) u x with hd_u_def
  have h_mfderiv_mul : mfderiv I 𝓘(ℝ, ℝ) (fun y : M => ρ y * u y) x v =
      ρ x * d_u v + u x * d_ρ v := by
    rw [h_fun_eq]
    have h_ρ_at : HasMFDerivAt I 𝓘(ℝ, ℝ) ρ x d_ρ := hρ.hasMFDerivAt
    have h_u_at : HasMFDerivAt I 𝓘(ℝ, ℝ) u x d_u := hu.hasMFDerivAt
    have hAt : HasMFDerivAt I 𝓘(ℝ, ℝ) (ρ * u) x
        ((ρ x • d_u + u x • d_ρ : TangentSpace I x →L[ℝ] ℝ)) :=
      h_ρ_at.mul h_u_at
    rw [hAt.mfderiv]
    change ((ρ x • d_u + u x • d_ρ : TangentSpace I x →L[ℝ] ℝ)) v =
        ρ x * d_u v + u x * d_ρ v
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smul_apply]
    simp [smul_eq_mul]
  rw [h_mfderiv_mul]
  symm
  have h1 : (g.inner x)
      (ρ x • DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x +
       u x • DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g ρ x) =
      (g.inner x) (ρ x • DifferentialGeometry.Integral.DivergenceTheorem.gradFun
        (I := I) g u x) +
      (g.inner x) (u x • DifferentialGeometry.Integral.DivergenceTheorem.gradFun
        (I := I) g ρ x) :=
    (g.inner x).map_add _ _
  change ((g.inner x)
      (ρ x • DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x +
       u x • DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g ρ x)) v =
    ρ x * d_u v + u x * d_ρ v
  rw [h1]
  rw [show (((g.inner x) (ρ x • DifferentialGeometry.Integral.DivergenceTheorem.gradFun
      (I := I) g u x)) + ((g.inner x) (u x •
      DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g ρ x))) v =
      ((g.inner x) (ρ x • DifferentialGeometry.Integral.DivergenceTheorem.gradFun
        (I := I) g u x)) v +
      ((g.inner x) (u x • DifferentialGeometry.Integral.DivergenceTheorem.gradFun
        (I := I) g ρ x)) v from rfl]
  rw [(g.inner x).map_smul, (g.inner x).map_smul]
  rw [show (ρ x • (g.inner x) (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
        (I := I) g u x)) v = ρ x • ((g.inner x)
        (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)) v from rfl]
  rw [show (u x • (g.inner x) (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
        (I := I) g ρ x)) v = u x • ((g.inner x)
        (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g ρ x)) v from rfl]
  simp only [smul_eq_mul]
  rw [show ((g.inner x) (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
        (I := I) g u x)) v = d_u v from by
    rw [hd_u_def]
    exact DifferentialGeometry.Integral.DivergenceTheorem.inner_gradFun (I := I) g u x v]
  rw [show ((g.inner x) (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
        (I := I) g ρ x)) v = d_ρ v from by
    rw [hd_ρ_def]
    exact DifferentialGeometry.Integral.DivergenceTheorem.inner_gradFun (I := I) g ρ x v]

/-- For closed Riemannian manifolds and smooth `f`, the function
`x ↦ √g(grad f, grad f)(x)` is continuous. -/
private lemma continuous_sqrt_g_inner_gradFun_self
    [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    Continuous (fun x : M => Real.sqrt
      (g.inner x
        (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g f x)
        (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g f x))) := by
  have hcont := TangentBundle.continuous_g_inner_of_smooth_sections
    (I := I) (M := M) g
    (DifferentialGeometry.Integral.DivergenceTheorem.grad_g (I := I) g hf)
    (DifferentialGeometry.Integral.DivergenceTheorem.grad_g (I := I) g hf)
  have hcoe : (fun x : M => g.inner x
        ((DifferentialGeometry.Integral.DivergenceTheorem.grad_g (I := I) g hf :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((DifferentialGeometry.Integral.DivergenceTheorem.grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) =
      (fun x : M => g.inner x
        (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g f x)
        (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g f x)) := by
    funext x
    rw [DifferentialGeometry.Integral.DivergenceTheorem.grad_g_apply (I := I) g hf x]
  rw [hcoe] at hcont
  exact Real.continuous_sqrt.comp hcont

/-- A continuous function on a closed (compact) manifold has a finite sup. -/
private lemma exists_continuous_sup_of_compactSpace
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {f : M → ℝ} (hf : Continuous f) (hf_nn : ∀ x, 0 ≤ f x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, f x ≤ C := by
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
    have hrange : IsCompact (Set.range f) := isCompact_range hf
    obtain ⟨C, hC_le⟩ := hrange.bddAbove
    refine ⟨C, ?_, fun x => hC_le ⟨x, rfl⟩⟩
    exact le_trans (hf_nn x₀) (hC_le ⟨x₀, rfl⟩)
  · refine ⟨0, le_refl _, fun x => (hM ⟨x⟩).elim⟩

/-- Continuous sup bound on `|ρ_α(x)|` over compact M. Since `0 ≤ ρ_α ≤ 1`, the
bound is `1`. -/
private lemma chartAtlasPOU_le_one
    [T2Space M] [SigmaCompactSpace M] (α : M) (x : M) :
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ≤ 1 := by
  exact (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).le_one α x

private lemma chartAtlasPOU_nonneg
    [T2Space M] [SigmaCompactSpace M] (α : M) (x : M) :
    0 ≤ ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) x :=
  (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).nonneg α x

private lemma abs_chartAtlasPOU_le_one
    [T2Space M] [SigmaCompactSpace M] (α : M) (x : M) :
    |((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) x| ≤ 1 :=
  abs_le.mpr ⟨by linarith [chartAtlasPOU_nonneg (I := I) (M := M) α x],
    chartAtlasPOU_le_one (I := I) (M := M) α x⟩

/-- The Leibniz pointwise bound on the metric norm of `grad(ρ_α u)`. -/
private lemma sqrt_g_inner_gradFun_pou_mul_le
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      Real.sqrt
        (g.inner x
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g
            (fun y : M => ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) : M → ℝ) y * u y) x)
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g
            (fun y : M => ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) : M → ℝ) y * u y) x)) ≤
        K * (|u x| +
          Real.sqrt
            (g.inner x
              (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
              (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x))) := by
  classical
  set ρ : C^∞⟮I, M; ℝ⟯ :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
  obtain ⟨K_grad_ρ, hK_grad_ρ_nn, hK_grad_ρ⟩ :=
    exists_continuous_sup_of_compactSpace (M := M)
      (f := fun x : M => Real.sqrt
        (g.inner x
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g
            ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g
            ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)))
      (continuous_sqrt_g_inner_gradFun_self (I := I) (M := M) g ρ.contMDiff)
      (fun _ => Real.sqrt_nonneg _)
  refine ⟨max 1 K_grad_ρ, le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro x
  have hρ_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x :=
    ρ.contMDiff.mdifferentiable (by simp) x
  have hu_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) u x :=
    hu.mdifferentiable (by simp) x
  have h_grad_eq := gradFun_mul_pointwise (I := I) g (ρ := (ρ : M → ℝ)) (u := u)
    (x := x) hρ_diff hu_diff
  rw [h_grad_eq]
  set gu : TangentSpace I x :=
    DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x with hgu_def
  set gρ : TangentSpace I x :=
    DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g
      ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x with hgρ_def
  set a : TangentSpace I x := ((ρ : M → ℝ)) x • gu
  set b : TangentSpace I x := u x • gρ
  have ha_self_eq : g.inner x a a = ((ρ : M → ℝ) x)^2 * g.inner x gu gu := by
    change (g.inner x ((((ρ : M → ℝ) x)) • gu)) ((((ρ : M → ℝ) x)) • gu) =
      _ * g.inner x gu gu
    rw [(g.inner x).map_smul, ContinuousLinearMap.smul_apply]
    rw [(g.inner x gu).map_smul]
    simp [smul_eq_mul, sq]
    ring
  have hb_self_eq : g.inner x b b = (u x)^2 * g.inner x gρ gρ := by
    change (g.inner x ((u x) • gρ)) ((u x) • gρ) =
      _ * g.inner x gρ gρ
    rw [(g.inner x).map_smul, ContinuousLinearMap.smul_apply]
    rw [(g.inner x gρ).map_smul]
    simp [smul_eq_mul, sq]
    ring
  have h_sym : g.inner x a b = g.inner x b a := g.symm x a b
  have h_inner_self_nn : ∀ z : TangentSpace I x, 0 ≤ g.inner x z z := by
    intro z
    by_cases hz : z = 0
    · rw [hz]
      change ((g.inner x) (0 : TangentSpace I x)) (0 : TangentSpace I x) ≥ 0
      rw [(g.inner x).map_zero]
      change (0 : TangentSpace I x →L[ℝ] ℝ) (0 : TangentSpace I x) ≥ 0
      simp
    · exact (g.pos x z hz).le
  have h_a_nn : 0 ≤ g.inner x a a := h_inner_self_nn _
  have h_b_nn : 0 ≤ g.inner x b b := h_inner_self_nn _
  have h_apb_nn : 0 ≤ g.inner x (a + b) (a + b) := h_inner_self_nn _
  have h_apb_eq : g.inner x (a + b) (a + b) =
      g.inner x a a + 2 * g.inner x a b + g.inner x b b := by
    have h_step : g.inner x (a + b) (a + b) =
        g.inner x a (a + b) + g.inner x b (a + b) := by
      have h1 : (g.inner x) (a + b) = (g.inner x) a + (g.inner x) b :=
        (g.inner x).map_add a b
      change ((g.inner x) (a + b)) (a + b) = _
      rw [h1]
      rfl
    rw [h_step, (g.inner x a).map_add, (g.inner x b).map_add]
    rw [h_sym]
    ring
  have h_CS_ab := abs_g_inner_le_sqrt_mul_sqrt (I := I) g x a b
  have h_apb_le_sum_sq :
      g.inner x (a + b) (a + b) ≤
        (Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b))^2 := by
    rw [h_apb_eq]
    have h_sqrt_a_sq : Real.sqrt (g.inner x a a)^2 = g.inner x a a :=
      Real.sq_sqrt h_a_nn
    have h_sqrt_b_sq : Real.sqrt (g.inner x b b)^2 = g.inner x b b :=
      Real.sq_sqrt h_b_nn
    have h_2ab_le : 2 * g.inner x a b ≤
        2 * (Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)) := by
      have h_le_abs : g.inner x a b ≤ |g.inner x a b| := le_abs_self _
      linarith
    nlinarith [h_2ab_le, h_sqrt_a_sq, h_sqrt_b_sq,
      Real.sqrt_nonneg (g.inner x a a), Real.sqrt_nonneg (g.inner x b b)]
  have h_sum_nn : 0 ≤ Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h_sqrt_apb_le : Real.sqrt (g.inner x (a + b) (a + b)) ≤
      Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b) := by
    have h := Real.sqrt_le_sqrt h_apb_le_sum_sq
    rw [Real.sqrt_sq h_sum_nn] at h
    exact h
  refine h_sqrt_apb_le.trans ?_
  have h_sqrt_a : Real.sqrt (g.inner x a a) =
      |((ρ : M → ℝ)) x| * Real.sqrt (g.inner x gu gu) := by
    rw [ha_self_eq]
    have hgu_nn : 0 ≤ g.inner x gu gu := h_inner_self_nn _
    rw [Real.sqrt_mul (sq_nonneg _)]
    rw [Real.sqrt_sq_eq_abs]
  have h_sqrt_b : Real.sqrt (g.inner x b b) =
      |u x| * Real.sqrt (g.inner x gρ gρ) := by
    rw [hb_self_eq]
    have hgρ_nn : 0 ≤ g.inner x gρ gρ := h_inner_self_nn _
    rw [Real.sqrt_mul (sq_nonneg _)]
    rw [Real.sqrt_sq_eq_abs]
  rw [h_sqrt_a, h_sqrt_b]
  have hρ_abs : |((ρ : M → ℝ)) x| ≤ 1 := abs_chartAtlasPOU_le_one (I := I) (M := M) α x
  have hsqrt_gu_nn : 0 ≤ Real.sqrt (g.inner x gu gu) := Real.sqrt_nonneg _
  have hsqrt_gρ_nn : 0 ≤ Real.sqrt (g.inner x gρ gρ) := Real.sqrt_nonneg _
  have h_term1 : |((ρ : M → ℝ)) x| * Real.sqrt (g.inner x gu gu) ≤
      Real.sqrt (g.inner x gu gu) := by
    calc |((ρ : M → ℝ)) x| * Real.sqrt (g.inner x gu gu)
        ≤ 1 * Real.sqrt (g.inner x gu gu) :=
          mul_le_mul_of_nonneg_right hρ_abs hsqrt_gu_nn
      _ = Real.sqrt (g.inner x gu gu) := one_mul _
  have h_term2 : |u x| * Real.sqrt (g.inner x gρ gρ) ≤
      |u x| * K_grad_ρ := by
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact hK_grad_ρ x
  have hM := le_max_left (1 : ℝ) K_grad_ρ
  have hM' := le_max_right (1 : ℝ) K_grad_ρ
  set K := max (1 : ℝ) K_grad_ρ
  have hK_nn : 0 ≤ K := le_trans zero_le_one hM
  have h_step1 : Real.sqrt (g.inner x gu gu) ≤ K * Real.sqrt (g.inner x gu gu) := by
    have := mul_le_mul_of_nonneg_right hM hsqrt_gu_nn
    linarith
  have h_step2 : K_grad_ρ * |u x| ≤ K * |u x| :=
    mul_le_mul_of_nonneg_right hM' (abs_nonneg _)
  calc |((ρ : M → ℝ)) x| * Real.sqrt (g.inner x gu gu) +
        |u x| * Real.sqrt (g.inner x gρ gρ)
      ≤ Real.sqrt (g.inner x gu gu) + |u x| * K_grad_ρ :=
        add_le_add h_term1 h_term2
    _ = Real.sqrt (g.inner x gu gu) + K_grad_ρ * |u x| := by ring
    _ ≤ K * Real.sqrt (g.inner x gu gu) + K * |u x| :=
        add_le_add h_step1 h_step2
    _ = K * (|u x| + Real.sqrt (g.inner x gu gu)) := by ring

/-- `chartSmoothExt α (ρ_α u) y` agrees with `chartPushed (chartAtlasPOU) α u y` on
the chart target. -/
lemma chartSmoothExt_eq_chartPushed_pou_on_target
    [T2Space M] [SigmaCompactSpace M] (α : M) (u : M → ℝ)
    {y : EuclN_E}
    (hy : y ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α
        (fun x : M => ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * u x) y =
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u y := by
  classical
  have hsymm_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_eq_preimage_symm
      (I := I) (M := M)] at hy
    exact hy
  unfold DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
  change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          u ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      else (0 : ℝ)) =
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
      u ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
  rw [if_pos hsymm_target]

lemma chartSmoothExt_eq_chartPushed_pou_ae
    [T2Space M] [SigmaCompactSpace M] (α : M) (u : M → ℝ) :
    DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α
        (fun x : M => ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * u x) =ᵐ[
        (volume : Measure EuclN_E).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)]
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u := by
  filter_upwards [self_mem_ae_restrict
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_measurableSet
      (I := I) (M := M) α)] with y hy
  exact chartSmoothExt_eq_chartPushed_pou_on_target (I := I) (M := M) α u hy

/-- For closed manifolds and smooth `u`, the function
`chartSmoothExt α (ρ_α u)` is C^∞ on EuclN. -/
lemma contDiff_chartSmoothExt_pou_mul_local_reverse
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    ContDiff ℝ ∞
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α
        (fun y : M => ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) y * u y)) := by
  classical
  set ρ : C^∞⟮I, M; ℝ⟯ :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
  set f : M → ℝ := fun y : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) y * u y
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := ρ.contMDiff.mul hu
  have hf_supp_chart : tsupport f ⊆ (chartAt H α).source := by
    have h1 : tsupport f ⊆ tsupport
        ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      have h_eq : f = (fun y : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) y • u y) := by
        funext y; rfl
      rw [h_eq]
      exact tsupport_smul_subset_left
        (f := fun y : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) y) (g := u)
    exact h1.trans
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α)
  have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  rw [contDiff_iff_contDiffAt]
  intro y
  set form : EuclN_E → ℝ := fun z =>
    f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
  have h_target_open :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) (α := α)
  have h_form_contDiffOn : ContDiffOn ℝ ∞ form
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
    have hscalar : ContDiffOn ℝ ∞
        (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
          (I := I) α f) (extChartAt I α).target :=
      DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_contDiffOn
        (I := I) α hf_smooth
    have htoEuc_symm_smooth : ContDiff ℝ ∞ ((toEuclidean (E := E)).symm) :=
      ContinuousLinearEquiv.contDiff _
    have hmaps : Set.MapsTo ((toEuclidean (E := E)).symm)
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)
        (extChartAt I α).target := by
      intro y' hy'
      obtain ⟨z, hz_target, rfl⟩ := hy'
      have h_eq : (toEuclidean (E := E)).symm
          ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) z) = z :=
        (toEuclidean (E := E)).symm_apply_apply z
      rw [h_eq]
      exact hz_target
    have h_eq_form : form = (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
        (I := I) α f) ∘ (fun z : EuclN_E => (toEuclidean (E := E)).symm z) := by
      funext z; rfl
    rw [h_eq_form]
    exact hscalar.comp htoEuc_symm_smooth.contDiffOn hmaps
  by_cases hy_target : y ∈
      DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α
  · have h_at : ContDiffAt ℝ ∞ form y :=
      (h_form_contDiffOn.contDiffWithinAt hy_target).contDiffAt
        (h_target_open.mem_nhds hy_target)
    apply h_at.congr_of_eventuallyEq
    filter_upwards [h_target_open.mem_nhds hy_target] with z hz
    obtain ⟨w, hw_target, hw_eq⟩ := hz
    have hsymm_eq : (toEuclidean (E := E)).symm z = w := by
      rw [← hw_eq]
      exact (toEuclidean (E := E)).symm_apply_apply w
    have htarget_at_z : (toEuclidean (E := E)).symm z ∈ (extChartAt I α).target := by
      rw [hsymm_eq]; exact hw_target
    change DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α f z =
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
    change (if (toEuclidean (E := E)).symm z ∈ (extChartAt I α).target then
        f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
      else (0 : ℝ)) =
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
    rw [if_pos htarget_at_z]
  · set K : Set EuclN_E := (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f))
    have hK_compact : IsCompact K := by
      have h_extChart_cont : ContinuousOn (extChartAt I α) (tsupport f) :=
        (continuousOn_extChartAt α).mono (by
          intro x hx
          rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
            (I := I) (M := M)]
          exact hf_supp_chart hx)
      have h1 : IsCompact ((extChartAt I α) '' (tsupport f)) :=
        hf_compact.image_of_continuousOn h_extChart_cont
      exact h1.image (toEuclidean (E := E)).continuous
    have hK_subset : K ⊆
        DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α := by
      rintro y' ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      have hxsource : x ∈ (extChartAt I α).source := by
        rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
          (I := I) (M := M)]
        exact hf_supp_chart hx
      exact ⟨extChartAt I α x, (extChartAt I α).map_source hxsource, rfl⟩
    have hy_off_K : y ∉ K := fun hy_in => hy_target (hK_subset hy_in)
    have hK_compl_open : IsOpen Kᶜ := hK_compact.isClosed.isOpen_compl
    apply ContDiffAt.congr_of_eventuallyEq (f := fun _ : EuclN_E => (0 : ℝ)) contDiffAt_const
    filter_upwards [hK_compl_open.mem_nhds hy_off_K] with z hz
    classical
    by_cases hz_target : (toEuclidean (E := E)).symm z ∈ (extChartAt I α).target
    · have hsymm_source : (extChartAt I α).symm
          ((toEuclidean (E := E)).symm z) ∈ (extChartAt I α).source :=
        (extChartAt I α).map_target hz_target
      have hxsupp : (extChartAt I α).symm ((toEuclidean (E := E)).symm z) ∉ tsupport f := by
        intro hin
        apply hz
        refine ⟨(toEuclidean (E := E)).symm z, ?_, ?_⟩
        · refine ⟨(extChartAt I α).symm ((toEuclidean (E := E)).symm z), hin, ?_⟩
          exact (extChartAt I α).right_inv hz_target
        · exact (toEuclidean (E := E)).apply_symm_apply z
      have hf_zero : f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) = 0 :=
        image_eq_zero_of_notMem_tsupport hxsupp
      change (if (toEuclidean (E := E)).symm z ∈ (extChartAt I α).target then
                f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
              else (0 : ℝ)) = 0
      rw [if_pos hz_target, hf_zero]
    · change (if (toEuclidean (E := E)).symm z ∈ (extChartAt I α).target then
                f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
              else (0 : ℝ)) = 0
      rw [if_neg hz_target]

private lemma eLpNorm_chartPushed_le_const_mul_eLpNorm_u
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
      eLpNorm (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u) p
          ((volume : Measure EuclN_E).restrict
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α)) ≤
        ENNReal.ofReal C *
          eLpNorm u p
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) := by
  classical
  set ρ : C^∞⟮I, M; ℝ⟯ :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α with hρ_def
  set Kα : Set M := tsupport ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKα_def
  have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
  have hKα_sub : Kα ⊆ (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
  obtain ⟨C_K, hC_K_pos, hC_K_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_chartPushedRaw_le_const_mul_eLpNorm_riemannianMeasure_uniform_of_subset
      (I := I) (M := M) g α hKα_compact hKα_sub hp_one hp_top
  refine ⟨C_K, hC_K_pos.le, ?_⟩
  intro u hu
  set f : M → ℝ := fun y : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) y * u y with hf_def
  have hf_meas : Measurable f := (ρ.contMDiff.continuous.measurable).mul hu.continuous.measurable
  have hf_supp : tsupport f ⊆ Kα := by
    have h_eq : f = (fun y : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) y • u y) := by
      funext y; rfl
    rw [h_eq]
    exact tsupport_smul_subset_left
      (f := fun y : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) y) (g := u)
  have h_step1 := hC_K_bound hf_meas hf_supp
  rw [← DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_def
    (I := I) (M := M) g] at h_step1
  have h_ae :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_eq_chartPushedRaw_pou_ae
      (I := I) (M := M) (ρ := DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
      α u
  rw [eLpNorm_congr_ae h_ae]
  refine h_step1.trans ?_
  gcongr
  apply eLpNorm_mono
  intro x
  have h_abs_f : ‖f x‖ = |((ρ : M → ℝ) x) * u x| := Real.norm_eq_abs _
  have h_abs_u : ‖u x‖ = |u x| := Real.norm_eq_abs _
  rw [h_abs_f, h_abs_u, abs_mul]
  have hρ_abs : |((ρ : M → ℝ) x)| ≤ 1 := abs_chartAtlasPOU_le_one (I := I) (M := M) α x
  calc |((ρ : M → ℝ) x)| * |u x|
      ≤ 1 * |u x| := by gcongr
    _ = |u x| := one_mul _

/-- Pointwise bound for `|fderiv chartSmoothExt α (ρ_α u) y e_i|`:
`≤ K · (chartPushedRaw α (|u| + √g(grad u, grad u))) y`,
with `K` uniform in `u`. -/
private lemma abs_fderiv_chartSmoothExt_apply_pou_mul_le
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
      ∀ (i : Fin (Module.finrank ℝ E)) (y : EuclN_E),
        |fderiv ℝ
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α
            (fun z : M => ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)) y
            (EuclideanSpace.single i (1 : ℝ))| ≤
          K *
            DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
              (fun x : M => |u x| +
                Real.sqrt
                  (g.inner x
                    (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
                      (I := I) g u x)
                    (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
                      (I := I) g u x))) y := by
  classical
  set M_α : ℝ := chartTargetUnitSqSumSupOnPouTsupport (I := I) (M := M) g α with hM_α_def
  have hM_α_nn : 0 ≤ M_α := chartTargetUnitSqSumSupOnPouTsupport_nonneg
    (I := I) (M := M) g α
  set ρ : C^∞⟮I, M; ℝ⟯ :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α with hρ_def
  obtain ⟨K_grad_ρ, hK_grad_ρ_nn, hK_grad_ρ_bound⟩ :=
    exists_continuous_sup_of_compactSpace (M := M)
      (f := fun x : M => Real.sqrt
        (g.inner x
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g
            ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g
            ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)))
      (continuous_sqrt_g_inner_gradFun_self (I := I) (M := M) g ρ.contMDiff)
      (fun _ => Real.sqrt_nonneg _)
  set K_grad := max (1 : ℝ) K_grad_ρ
  have hK_grad_nn : 0 ≤ K_grad := le_trans zero_le_one (le_max_left _ _)
  refine ⟨K_grad * Real.sqrt M_α, mul_nonneg hK_grad_nn (Real.sqrt_nonneg _), ?_⟩
  intro u hu i y
  set f : M → ℝ := fun z : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z with hf_def
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := ρ.contMDiff.mul hu
  have hf_supp_chart : tsupport f ⊆ (chartAt H α).source := by
    have h1 : tsupport f ⊆ tsupport ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      have h_eq : f = (fun z : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) z • u z) := by
        funext z; rfl
      rw [h_eq]
      exact tsupport_smul_subset_left
        (f := fun z : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) z) (g := u)
    exact h1.trans
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α)
  have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  have hK_grad_bound : ∀ x : M, Real.sqrt
        (g.inner x
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g f x)
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g f x)) ≤
      K_grad *
        (|u x| + Real.sqrt
          (g.inner x
            (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
            (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x))) := by
    intro x
    obtain ⟨K', hK'_nn, hK'_bound⟩ := sqrt_g_inner_gradFun_pou_mul_le (I := I) (M := M) g α hu
    have hρ_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x :=
      ρ.contMDiff.mdifferentiable (by simp) x
    have hu_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) u x :=
      hu.mdifferentiable (by simp) x
    have h_grad_eq := gradFun_mul_pointwise (I := I) g (ρ := (ρ : M → ℝ)) (u := u)
      (x := x) hρ_diff hu_diff
    set gu : TangentSpace I x :=
      DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x
    set gρ : TangentSpace I x :=
      DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g
        ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x
    set a : TangentSpace I x := ((ρ : M → ℝ)) x • gu
    set b : TangentSpace I x := u x • gρ
    rw [h_grad_eq]
    have h_inner_self_nn : ∀ z : TangentSpace I x, 0 ≤ g.inner x z z := by
      intro z
      by_cases hz : z = 0
      · rw [hz]
        change ((g.inner x) (0 : TangentSpace I x)) (0 : TangentSpace I x) ≥ 0
        rw [(g.inner x).map_zero]
        change (0 : TangentSpace I x →L[ℝ] ℝ) (0 : TangentSpace I x) ≥ 0
        simp
      · exact (g.pos x z hz).le
    have h_a_nn : 0 ≤ g.inner x a a := h_inner_self_nn _
    have h_b_nn : 0 ≤ g.inner x b b := h_inner_self_nn _
    have hsym : g.inner x a b = g.inner x b a := g.symm x a b
    have h_apb_eq : g.inner x (a + b) (a + b) =
        g.inner x a a + 2 * g.inner x a b + g.inner x b b := by
      have h_step : g.inner x (a + b) (a + b) =
          g.inner x a (a + b) + g.inner x b (a + b) := by
        have h1 : (g.inner x) (a + b) = (g.inner x) a + (g.inner x) b :=
          (g.inner x).map_add a b
        change ((g.inner x) (a + b)) (a + b) = _
        rw [h1]
        rfl
      rw [h_step, (g.inner x a).map_add, (g.inner x b).map_add]
      rw [hsym]; ring
    have h_CS_ab := abs_g_inner_le_sqrt_mul_sqrt (I := I) g x a b
    have h_apb_le_sum_sq :
        g.inner x (a + b) (a + b) ≤
          (Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b))^2 := by
      rw [h_apb_eq]
      have h_sqrt_a_sq : Real.sqrt (g.inner x a a)^2 = g.inner x a a :=
        Real.sq_sqrt h_a_nn
      have h_sqrt_b_sq : Real.sqrt (g.inner x b b)^2 = g.inner x b b :=
        Real.sq_sqrt h_b_nn
      have h_2ab_le : 2 * g.inner x a b ≤
          2 * (Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)) := by
        have h_le_abs : g.inner x a b ≤ |g.inner x a b| := le_abs_self _
        linarith
      nlinarith [h_2ab_le, h_sqrt_a_sq, h_sqrt_b_sq,
        Real.sqrt_nonneg (g.inner x a a), Real.sqrt_nonneg (g.inner x b b)]
    have h_sum_nn : 0 ≤ Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b) :=
      add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have h_sqrt_apb_le : Real.sqrt (g.inner x (a + b) (a + b)) ≤
        Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b) := by
      have h := Real.sqrt_le_sqrt h_apb_le_sum_sq
      rw [Real.sqrt_sq h_sum_nn] at h
      exact h
    refine h_sqrt_apb_le.trans ?_
    have h_sqrt_a : Real.sqrt (g.inner x a a) =
        |((ρ : M → ℝ)) x| * Real.sqrt (g.inner x gu gu) := by
      have h_a_self_eq : g.inner x a a = ((ρ : M → ℝ) x)^2 * g.inner x gu gu := by
        change (g.inner x ((((ρ : M → ℝ) x)) • gu)) ((((ρ : M → ℝ) x)) • gu) =
          _ * g.inner x gu gu
        rw [(g.inner x).map_smul, ContinuousLinearMap.smul_apply]
        rw [(g.inner x gu).map_smul]
        simp [smul_eq_mul, sq]; ring
      rw [h_a_self_eq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
    have h_sqrt_b : Real.sqrt (g.inner x b b) =
        |u x| * Real.sqrt (g.inner x gρ gρ) := by
      have h_b_self_eq : g.inner x b b = (u x)^2 * g.inner x gρ gρ := by
        change (g.inner x ((u x) • gρ)) ((u x) • gρ) = _ * g.inner x gρ gρ
        rw [(g.inner x).map_smul, ContinuousLinearMap.smul_apply]
        rw [(g.inner x gρ).map_smul]
        simp [smul_eq_mul, sq]; ring
      rw [h_b_self_eq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
    rw [h_sqrt_a, h_sqrt_b]
    have hρ_abs : |((ρ : M → ℝ)) x| ≤ 1 := abs_chartAtlasPOU_le_one (I := I) (M := M) α x
    have hsqrt_gu_nn : 0 ≤ Real.sqrt (g.inner x gu gu) := Real.sqrt_nonneg _
    have hsqrt_gρ_nn : 0 ≤ Real.sqrt (g.inner x gρ gρ) := Real.sqrt_nonneg _
    have h_term1 : |((ρ : M → ℝ)) x| * Real.sqrt (g.inner x gu gu) ≤
        Real.sqrt (g.inner x gu gu) := by
      calc |((ρ : M → ℝ)) x| * Real.sqrt (g.inner x gu gu)
          ≤ 1 * Real.sqrt (g.inner x gu gu) :=
            mul_le_mul_of_nonneg_right hρ_abs hsqrt_gu_nn
        _ = Real.sqrt (g.inner x gu gu) := one_mul _
    have h_term2 : |u x| * Real.sqrt (g.inner x gρ gρ) ≤ |u x| * K_grad_ρ :=
      mul_le_mul_of_nonneg_left (hK_grad_ρ_bound x) (abs_nonneg _)
    have hM := le_max_left (1 : ℝ) K_grad_ρ
    have hM' := le_max_right (1 : ℝ) K_grad_ρ
    have h_step1 : Real.sqrt (g.inner x gu gu) ≤ K_grad * Real.sqrt (g.inner x gu gu) := by
      have := mul_le_mul_of_nonneg_right hM hsqrt_gu_nn
      linarith
    have h_step2 : K_grad_ρ * |u x| ≤ K_grad * |u x| :=
      mul_le_mul_of_nonneg_right hM' (abs_nonneg _)
    calc |((ρ : M → ℝ)) x| * Real.sqrt (g.inner x gu gu) +
          |u x| * Real.sqrt (g.inner x gρ gρ)
        ≤ Real.sqrt (g.inner x gu gu) + |u x| * K_grad_ρ :=
          add_le_add h_term1 h_term2
      _ = Real.sqrt (g.inner x gu gu) + K_grad_ρ * |u x| := by ring
      _ ≤ K_grad * Real.sqrt (g.inner x gu gu) + K_grad * |u x| :=
          add_le_add h_step1 h_step2
      _ = K_grad * (|u x| + Real.sqrt (g.inner x gu gu)) := by ring
  by_cases hy_in : y ∈
      DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α
  · set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
    have h_sq_bound := sq_fderiv_chartSmoothExt_apply_le_g_inner_mul (I := I) (M := M) g
      α hf_smooth hf_supp_chart hf_compact (y := y) hy_in i
    have h_lhs_nn : 0 ≤ |fderiv ℝ
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α f) y (EuclideanSpace.single i (1 : ℝ))| := abs_nonneg _
    have h_grad_f_nn : 0 ≤ g.inner x
        (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g f x)
        (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g f x) := by
      by_cases hzero :
          DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g f x = 0
      · rw [hzero]
        change ((g.inner x) (0 : TangentSpace I x)) (0 : TangentSpace I x) ≥ 0
        rw [(g.inner x).map_zero]
        change (0 : TangentSpace I x →L[ℝ] ℝ) (0 : TangentSpace I x) ≥ 0
        simp
      · exact (g.pos x _ hzero).le
    have h_abs_le_sqrt :
        |fderiv ℝ
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
              (I := I) (M := M) α f) y
            (EuclideanSpace.single i (1 : ℝ))| ≤
          Real.sqrt
            (g.inner x
              (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g f x)
              (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g f x)) *
            Real.sqrt
              (g.inner x
                (chartTargetUnitFiber (I := I) α i x)
                (chartTargetUnitFiber (I := I) α i x)) := by
      have h := Real.sqrt_le_sqrt h_sq_bound
      rw [Real.sqrt_sq_eq_abs] at h
      rw [Real.sqrt_mul h_grad_f_nn] at h
      exact h
    refine h_abs_le_sqrt.trans ?_
    by_cases hx_pou : x ∈ tsupport ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
    · have h_w_nn : ∀ j : Fin (Module.finrank ℝ E), 0 ≤
          g.inner x
            (chartTargetUnitFiber (I := I) α j x)
            (chartTargetUnitFiber (I := I) α j x) := fun j => by
        by_cases hzero : chartTargetUnitFiber (I := I) α j x = 0
        · rw [hzero]
          rw [(g.inner x).map_zero]
          change (0 : ℝ) ≤ (0 : TangentSpace I x →L[ℝ] ℝ) (0 : TangentSpace I x)
          simp
        · exact (g.pos x _ hzero).le
      have h_w_i_le_sum : g.inner x
          (chartTargetUnitFiber (I := I) α i x)
          (chartTargetUnitFiber (I := I) α i x) ≤
          ∑ j : Fin (Module.finrank ℝ E),
            g.inner x
              (chartTargetUnitFiber (I := I) α j x)
              (chartTargetUnitFiber (I := I) α j x) :=
        Finset.single_le_sum (s := Finset.univ)
          (f := fun j : Fin (Module.finrank ℝ E) =>
            g.inner x
              (chartTargetUnitFiber (I := I) α j x)
              (chartTargetUnitFiber (I := I) α j x))
          (fun j _ => h_w_nn j) (Finset.mem_univ i)
      have h_w_i_le_M : g.inner x
          (chartTargetUnitFiber (I := I) α i x)
          (chartTargetUnitFiber (I := I) α i x) ≤ M_α :=
        h_w_i_le_sum.trans (chartTargetUnitSqSum_le_sup (I := I) (M := M) g α hx_pou)
      have h_sqrt_w_le_sqrt_M :
          Real.sqrt
            (g.inner x
              (chartTargetUnitFiber (I := I) α i x)
              (chartTargetUnitFiber (I := I) α i x)) ≤ Real.sqrt M_α :=
        Real.sqrt_le_sqrt h_w_i_le_M
      have h_sqrt_grad_f_nn : 0 ≤ Real.sqrt
          (g.inner x
            (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g f x)
            (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g f x)) :=
        Real.sqrt_nonneg _
      calc Real.sqrt
            (g.inner x
              (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g f x)
              (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g f x)) *
            Real.sqrt
              (g.inner x
                (chartTargetUnitFiber (I := I) α i x)
                (chartTargetUnitFiber (I := I) α i x))
          ≤ Real.sqrt
              (g.inner x
                (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g f x)
                (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g f x)) *
              Real.sqrt M_α :=
            mul_le_mul_of_nonneg_left h_sqrt_w_le_sqrt_M h_sqrt_grad_f_nn
        _ ≤ K_grad * (|u x| +
              Real.sqrt
                (g.inner x
                  (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
                  (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x))) *
              Real.sqrt M_α :=
            mul_le_mul_of_nonneg_right (hK_grad_bound x) (Real.sqrt_nonneg _)
        _ = K_grad * Real.sqrt M_α * (|u x| +
              Real.sqrt
                (g.inner x
                  (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
                  (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x))) := by ring
        _ = K_grad * Real.sqrt M_α *
              DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
                (fun z : M => |u z| +
                  Real.sqrt
                    (g.inner z
                      (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u z)
                      (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u z))) y := by
            rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
              (I := I) α (fun z : M => |u z| +
                Real.sqrt
                  (g.inner z
                    (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u z)
                    (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u z))) hy_in]
    · have hx_off_f : x ∉ tsupport f :=
        fun hin => hx_pou ((tsupport_smul_subset_left
          (f := fun z : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) z) (g := u)) hin)
      have h_grad_f_zero : DifferentialGeometry.Integral.DivergenceTheorem.gradFun
          (I := I) g f x = 0 := by
        have hopen : IsOpen (tsupport f)ᶜ := (isClosed_tsupport _).isOpen_compl
        have h_nhds : (tsupport f)ᶜ ∈ 𝓝 x := hopen.mem_nhds hx_off_f
        have heqz : f =ᶠ[𝓝 x] (fun _ : M => (0 : ℝ)) := by
          filter_upwards [h_nhds] with y hy
          exact image_eq_zero_of_notMem_tsupport hy
        have h_mfd_eq : mfderiv I 𝓘(ℝ, ℝ) f x = 0 := by
          rw [heqz.mfderiv_eq]; exact mfderiv_const
        exact DifferentialGeometry.Integral.DivergenceTheorem.gradFun_eq_zero_of_mfderiv_eq_zero
          g f h_mfd_eq
      have h_grad_f_inner_zero : g.inner x
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g f x)
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g f x) = 0 := by
        rw [h_grad_f_zero]
        rw [(g.inner x).map_zero]
        change (0 : TangentSpace I x →L[ℝ] ℝ) (0 : TangentSpace I x) = 0
        simp
      rw [h_grad_f_inner_zero, Real.sqrt_zero, zero_mul]
      apply mul_nonneg (mul_nonneg hK_grad_nn (Real.sqrt_nonneg _))
      rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
        (I := I) α (fun z : M => |u z| +
          Real.sqrt
            (g.inner z
              (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u z)
              (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u z))) hy_in]
      exact add_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  · have h_chartSmoothExt_smooth : ContDiff ℝ ∞
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α f) :=
      contDiff_chartSmoothExt_pou_mul_local_reverse (I := I) (M := M) α hu
    set K : Set EuclN_E := (toEuclidean (E := E)) ''
      ((extChartAt I α) '' (tsupport f)) with hK_def
    have hK_compact : IsCompact K := by
      have h_extChart_cont : ContinuousOn (extChartAt I α) (tsupport f) :=
        (continuousOn_extChartAt α).mono (by
          intro x hx
          rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
            (I := I) (M := M)]
          exact hf_supp_chart hx)
      have h1 : IsCompact ((extChartAt I α) '' (tsupport f)) :=
        hf_compact.image_of_continuousOn h_extChart_cont
      exact h1.image (toEuclidean (E := E)).continuous
    have hK_subset : K ⊆
        DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α := by
      rintro y' ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      have hxsource : x ∈ (extChartAt I α).source := by
        rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
          (I := I) (M := M)]
        exact hf_supp_chart hx
      exact ⟨extChartAt I α x, (extChartAt I α).map_source hxsource, rfl⟩
    have hy_off_K : y ∉ K := fun hy_in_K => hy_in (hK_subset hy_in_K)
    have hK_compl_open : IsOpen Kᶜ := hK_compact.isClosed.isOpen_compl
    have h_nhds : Kᶜ ∈ 𝓝 y := hK_compl_open.mem_nhds hy_off_K
    have h_eqz : (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α f) =ᶠ[𝓝 y] (fun _ : EuclN_E => (0 : ℝ)) := by
      filter_upwards [h_nhds] with z hz
      classical
      by_cases hz_target : (toEuclidean (E := E)).symm z ∈ (extChartAt I α).target
      · have hsymm_source : (extChartAt I α).symm
            ((toEuclidean (E := E)).symm z) ∈ (extChartAt I α).source :=
          (extChartAt I α).map_target hz_target
        have hxsupp : (extChartAt I α).symm ((toEuclidean (E := E)).symm z) ∉ tsupport f := by
          intro hin
          apply hz
          refine ⟨(toEuclidean (E := E)).symm z, ?_, ?_⟩
          · refine ⟨(extChartAt I α).symm ((toEuclidean (E := E)).symm z), hin, ?_⟩
            exact (extChartAt I α).right_inv hz_target
          · exact (toEuclidean (E := E)).apply_symm_apply z
        have hf_zero : f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) = 0 :=
          image_eq_zero_of_notMem_tsupport hxsupp
        change (if (toEuclidean (E := E)).symm z ∈ (extChartAt I α).target then
                  f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
                else (0 : ℝ)) = 0
        rw [if_pos hz_target, hf_zero]
      · change (if (toEuclidean (E := E)).symm z ∈ (extChartAt I α).target then
                  f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
                else (0 : ℝ)) = 0
        rw [if_neg hz_target]
    have h_fderiv_zero : fderiv ℝ
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α f) y = 0 := by
      rw [h_eqz.fderiv_eq]
      exact fderiv_const_apply 0
    rw [h_fderiv_zero]
    change |((0 : EuclN_E →L[ℝ] ℝ) (EuclideanSpace.single i (1 : ℝ)))| ≤ _
    rw [ContinuousLinearMap.zero_apply, abs_zero]
    apply mul_nonneg (mul_nonneg hK_grad_nn (Real.sqrt_nonneg _))
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_notMem
      (I := I) α (fun z : M => |u z| +
        Real.sqrt
          (g.inner z
            (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u z)
            (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u z))) hy_in]

/-- Refinement of `abs_fderiv_chartSmoothExt_apply_pou_mul_le` using the indicator of
`tsupport ρ_α`. Since the LHS vanishes off the chart pushforward of `tsupport ρ_α`,
the bound holds with the indicator-truncated `v`. -/
private lemma abs_fderiv_chartSmoothExt_apply_pou_mul_le_indicator
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
      ∀ (i : Fin (Module.finrank ℝ E)) (y : EuclN_E),
        |fderiv ℝ
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α
            (fun z : M => ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)) y
            (EuclideanSpace.single i (1 : ℝ))| ≤
          K *
            DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
              (Set.indicator
                (tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
                  : C^∞⟮I, M; ℝ⟯) : M → ℝ))
                (fun x : M => |u x| +
                  Real.sqrt
                    (g.inner x
                      (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
                        (I := I) g u x)
                      (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
                        (I := I) g u x)))) y := by
  classical
  obtain ⟨K, hK_nn, hK_bound⟩ :=
    abs_fderiv_chartSmoothExt_apply_pou_mul_le (I := I) (M := M) g α
  refine ⟨K, hK_nn, ?_⟩
  intro u hu i y
  by_cases hy_in : y ∈
      DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α
  · have h_full := hK_bound (u := u) hu i y
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) α _ hy_in] at h_full
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) α _ hy_in]
    set ρ : C^∞⟮I, M; ℝ⟯ :=
      DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α with hρ_def
    set Kα : Set M := tsupport ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKα_def
    set v : M → ℝ := fun x : M => |u x| +
      Real.sqrt
        (g.inner x
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x))
      with hv_def
    set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
    by_cases hx_Kα : x ∈ Kα
    · change _ ≤ K * (Set.indicator Kα v) x
      rw [Set.indicator_of_mem hx_Kα]
      exact h_full
    · change _ ≤ K * (Set.indicator Kα v) x
      rw [Set.indicator_of_notMem hx_Kα, mul_zero]
      set f : M → ℝ := fun z : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z with hf_def
      have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := ρ.contMDiff.mul hu
      have hf_supp : tsupport f ⊆ Kα := by
        have h_eq : f = (fun z : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) z • u z) := by
          funext z; rfl
        rw [h_eq]
        exact tsupport_smul_subset_left
          (f := fun z : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) z) (g := u)
      have hf_supp_chart : tsupport f ⊆ (chartAt H α).source :=
        hf_supp.trans (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α)
      have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
      have hx_off_f : x ∉ tsupport f := fun hin => hx_Kα (hf_supp hin)
      have h_grad_zero : DifferentialGeometry.Integral.DivergenceTheorem.gradFun
          (I := I) g f x = 0 := by
        have hopen : IsOpen (tsupport f)ᶜ := (isClosed_tsupport _).isOpen_compl
        have h_nhds : (tsupport f)ᶜ ∈ 𝓝 x := hopen.mem_nhds hx_off_f
        have heqz : f =ᶠ[𝓝 x] (fun _ : M => (0 : ℝ)) := by
          filter_upwards [h_nhds] with y' hy' using image_eq_zero_of_notMem_tsupport hy'
        have h_mfd_eq : mfderiv I 𝓘(ℝ, ℝ) f x = 0 := by
          rw [heqz.mfderiv_eq]; exact mfderiv_const
        exact DifferentialGeometry.Integral.DivergenceTheorem.gradFun_eq_zero_of_mfderiv_eq_zero
          g f h_mfd_eq
      have h_sq := sq_fderiv_chartSmoothExt_apply_le_g_inner_mul (I := I) (M := M) g
        α hf_smooth hf_supp_chart hf_compact (y := y) hy_in i
      simp only at h_sq
      have h_inner_zero : g.inner x
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g f x)
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g f x) = 0 := by
        rw [h_grad_zero]
        rw [(g.inner x).map_zero]
        change (0 : TangentSpace I x →L[ℝ] ℝ) (0 : TangentSpace I x) = 0
        simp
      rw [h_inner_zero, zero_mul] at h_sq
      have h_sq_eq : (fderiv ℝ
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α f) y (EuclideanSpace.single i (1 : ℝ)))^2 = 0 :=
        le_antisymm h_sq (sq_nonneg _)
      have h_zero : fderiv ℝ
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α f) y (EuclideanSpace.single i (1 : ℝ)) = 0 :=
        pow_eq_zero_iff (two_ne_zero) |>.mp h_sq_eq
      change |fderiv ℝ
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α f) y (EuclideanSpace.single i (1 : ℝ))| ≤ 0
      rw [h_zero, abs_zero]
  · have h_full := hK_bound (u := u) hu i y
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_notMem
      (I := I) α _ hy_in] at h_full
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_notMem
      (I := I) α _ hy_in]
    exact h_full

/-- Per-α gradient L^p bound: for each α and smooth `u`, the L^p norm on the
chart target of the partial `e_i` of the chart-pushed function is bounded by a
constant times the manifold L^p norm of `|u| + √g(grad u, grad u)`,
with constant uniform in `u`. -/
theorem eLpNorm_fderiv_chartSmoothExt_apply_le_const_mul
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
      ∀ i : Fin (Module.finrank ℝ E),
        eLpNorm (fun y : EuclN_E => fderiv ℝ
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
              (I := I) (M := M) α
              (fun z : M => ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)) y
              (EuclideanSpace.single i (1 : ℝ))) p
            ((volume : Measure EuclN_E).restrict
              (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
                (I := I) (M := M) α)) ≤
          ENNReal.ofReal C *
            (eLpNorm u p
                (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) +
              eLpNorm (fun x : M => Real.sqrt
                  (g.inner x
                    (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
                    (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x))) p
                (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g)) := by
  classical
  set ρ : C^∞⟮I, M; ℝ⟯ :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
  set Kα : Set M := tsupport ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
  have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
  have hKα_sub : Kα ⊆ (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
  obtain ⟨K, hK_nn, hK_bound⟩ :=
    abs_fderiv_chartSmoothExt_apply_pou_mul_le_indicator (I := I) (M := M) g α
  obtain ⟨C_K, hC_K_pos, hC_K_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_chartPushedRaw_le_const_mul_eLpNorm_riemannianMeasure_uniform_of_subset
      (I := I) (M := M) g α hKα_compact hKα_sub hp_one hp_top
  refine ⟨K * C_K, mul_nonneg hK_nn hC_K_pos.le, ?_⟩
  intro u hu i
  set v : M → ℝ := fun x : M => |u x| +
    Real.sqrt
      (g.inner x
        (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
        (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x))
  set v_α : M → ℝ := Set.indicator Kα v
  have hv_meas : Measurable v := by
    have h_abs_meas : Measurable (fun x : M => |u x|) := hu.continuous.measurable.abs
    have h_grad_meas : Measurable (fun x : M => Real.sqrt
      (g.inner x
        (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
        (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x))) :=
      (continuous_sqrt_g_inner_gradFun_self (I := I) (M := M) g hu).measurable
    exact h_abs_meas.add h_grad_meas
  have hv_α_meas : Measurable v_α :=
    Measurable.indicator hv_meas (isClosed_tsupport _).measurableSet
  have hv_α_supp : tsupport v_α ⊆ Kα := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro x hx
    by_contra hxc
    apply hx
    change (Set.indicator Kα v) x = 0
    rw [Set.indicator_of_notMem hxc]
  have h_pt : ∀ y : EuclN_E, ‖fderiv ℝ
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α
          (fun z : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)) y
          (EuclideanSpace.single i (1 : ℝ))‖ ≤
      K * DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α v_α y := by
    intro y
    rw [Real.norm_eq_abs]
    exact hK_bound (u := u) hu i y
  have h_eLp_le : eLpNorm (fun y : EuclN_E => fderiv ℝ
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α
          (fun z : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)) y
          (EuclideanSpace.single i (1 : ℝ))) p
        ((volume : Measure EuclN_E).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)) ≤
      eLpNorm (fun y : EuclN_E => K *
        DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α v_α y) p
        ((volume : Measure EuclN_E).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)) := eLpNorm_mono_real h_pt
  refine h_eLp_le.trans ?_
  have h_pull_K : eLpNorm (fun y : EuclN_E => K *
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α v_α y) p
      ((volume : Measure EuclN_E).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) =
    ENNReal.ofReal K *
    eLpNorm (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α v_α) p
      ((volume : Measure EuclN_E).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) := by
    have h_eq_smul : (fun y : EuclN_E => K *
        DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α v_α y) =
      K • (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α v_α) := by
      funext y
      change K * _ = K • _
      rw [smul_eq_mul]
    rw [h_eq_smul]
    rw [eLpNorm_const_smul (𝕜 := ℝ) (c := K)
      (f := DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α v_α)]
    have hK_enorm : ‖K‖ₑ = ENNReal.ofReal K := Real.enorm_eq_ofReal hK_nn
    rw [hK_enorm]
  rw [h_pull_K]
  have h_step2 := hC_K_bound hv_α_meas hv_α_supp
  rw [← DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_def
    (I := I) (M := M) g] at h_step2
  have h_v_α_le : ∀ x, ‖v_α x‖ ≤ |u x| +
      Real.sqrt
        (g.inner x
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)) := by
    intro x
    change ‖(Set.indicator Kα v) x‖ ≤ _
    rw [Real.norm_eq_abs]
    by_cases hx : x ∈ Kα
    · rw [Set.indicator_of_mem hx]
      have hv_nn : 0 ≤ v x := add_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
      rw [abs_of_nonneg hv_nn]
    · rw [Set.indicator_of_notMem hx, abs_zero]
      exact add_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have h_v_α_eLp_le : eLpNorm v_α p
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) ≤
    eLpNorm u p
        (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) +
      eLpNorm (fun x : M => Real.sqrt
          (g.inner x
            (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
            (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x))) p
        (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) := by
    refine (eLpNorm_mono_real h_v_α_le).trans ?_
    have h_aesm_u : AEStronglyMeasurable (fun x : M => |u x|)
        (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) :=
      hu.continuous.measurable.abs.aestronglyMeasurable
    have h_aesm_grad : AEStronglyMeasurable (fun x : M => Real.sqrt
        (g.inner x
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)))
        (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) :=
      (continuous_sqrt_g_inner_gradFun_self (I := I) (M := M) g hu).aestronglyMeasurable
    refine (eLpNorm_add_le h_aesm_u h_aesm_grad hp_one).trans ?_
    have h_eLp_u_eq : eLpNorm (fun x : M => |u x|) p
        (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) =
        eLpNorm u p
          (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) := by
      have h_eq : (fun x : M => |u x|) = fun x : M => ‖u x‖ := by
        funext x; rw [Real.norm_eq_abs]
      rw [h_eq]
      exact eLpNorm_norm u
    rw [h_eLp_u_eq]
  calc ENNReal.ofReal K *
        eLpNorm (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α v_α) p
          ((volume : Measure EuclN_E).restrict
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α))
      ≤ ENNReal.ofReal K *
          (ENNReal.ofReal C_K *
            eLpNorm v_α p
              (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g)) := by
        gcongr
    _ ≤ ENNReal.ofReal K *
          (ENNReal.ofReal C_K *
            (eLpNorm u p
                (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) +
              eLpNorm (fun x : M => Real.sqrt
                  (g.inner x
                    (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
                    (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x))) p
                (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g))) := by
        gcongr
    _ = ENNReal.ofReal (K * C_K) *
          (eLpNorm u p
              (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) +
            eLpNorm (fun x : M => Real.sqrt
                (g.inner x
                  (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
                  (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x))) p
              (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hK_nn]

/-- The classical partial of `chartSmoothExt α (ρ_α u)` agrees a.e. on
`volume.restrict ChTE` with `chosenWeakPartial' p i (chartPushed ρ α u) ChTE`. -/
lemma chosenWeakPartial_chartPushed_ae_eq_fderiv
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (α : M) {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (i : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p i
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)
      =ᵐ[(volume : Measure EuclN_E).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)]
      (fun y : EuclN_E => fderiv ℝ
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α
          (fun z : M => ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)) y
          (EuclideanSpace.single i (1 : ℝ))) := by
  classical
  set ρ : C^∞⟮I, M; ℝ⟯ :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
  set ψ : EuclN_E → ℝ := DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
    (I := I) (M := M) α
    (fun z : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)
  set f : M → ℝ := fun z : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := ρ.contMDiff.mul hu
  have hf_supp_chart : tsupport f ⊆ (chartAt H α).source := by
    have h1 : tsupport f ⊆ tsupport ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      have h_eq : f = (fun z : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) z • u z) := by
        funext z; rfl
      rw [h_eq]
      exact tsupport_smul_subset_left
        (f := fun z : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) z) (g := u)
    exact h1.trans
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α)
  have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  have hψ_smooth : ContDiff ℝ ∞ ψ :=
    contDiff_chartSmoothExt_pou_mul_local_reverse (I := I) (M := M) α hu
  have hψ_supp : tsupport ψ ⊆
      DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α := by
    set K_eucl : Set EuclN_E := (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f))
    have hK_compact : IsCompact K_eucl := by
      have h_extChart_cont : ContinuousOn (extChartAt I α) (tsupport f) :=
        (continuousOn_extChartAt α).mono (by
          intro x hx
          rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
            (I := I) (M := M)]
          exact hf_supp_chart hx)
      have h1 : IsCompact ((extChartAt I α) '' (tsupport f)) :=
        hf_compact.image_of_continuousOn h_extChart_cont
      exact h1.image (toEuclidean (E := E)).continuous
    have hK_subset : K_eucl ⊆
        DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α := by
      rintro y' ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      have hxsource : x ∈ (extChartAt I α).source := by
        rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
          (I := I) (M := M)]
        exact hf_supp_chart hx
      exact ⟨extChartAt I α x, (extChartAt I α).map_source hxsource, rfl⟩
    have h_sub_image : tsupport ψ ⊆ K_eucl := by
      apply closure_minimal _ hK_compact.isClosed
      intro y hy
      by_contra hy_off
      apply hy
      classical
      by_cases hz_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target
      · have hxsupp : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∉ tsupport f := by
          intro hin
          apply hy_off
          refine ⟨(toEuclidean (E := E)).symm y, ?_, ?_⟩
          · refine ⟨(extChartAt I α).symm ((toEuclidean (E := E)).symm y), hin, ?_⟩
            exact (extChartAt I α).right_inv hz_target
          · exact (toEuclidean (E := E)).apply_symm_apply y
        have hf_zero : f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = 0 :=
          image_eq_zero_of_notMem_tsupport hxsupp
        change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
                  f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
                else (0 : ℝ)) = 0
        rw [if_pos hz_target, hf_zero]
      · change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
                  f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
                else (0 : ℝ)) = 0
        rw [if_neg hz_target]
    exact h_sub_image.trans hK_subset
  have hψ_compact_supp : HasCompactSupport ψ := by
    set K_eucl : Set EuclN_E := (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f))
    have hK_compact : IsCompact K_eucl := by
      have h_extChart_cont : ContinuousOn (extChartAt I α) (tsupport f) :=
        (continuousOn_extChartAt α).mono (by
          intro x hx
          rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
            (I := I) (M := M)]
          exact hf_supp_chart hx)
      have h1 : IsCompact ((extChartAt I α) '' (tsupport f)) :=
        hf_compact.image_of_continuousOn h_extChart_cont
      exact h1.image (toEuclidean (E := E)).continuous
    have h_sub_image : tsupport ψ ⊆ K_eucl := by
      apply closure_minimal _ hK_compact.isClosed
      intro y hy
      by_contra hy_off
      apply hy
      classical
      by_cases hz_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target
      · have hxsupp : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∉ tsupport f := by
          intro hin
          apply hy_off
          refine ⟨(toEuclidean (E := E)).symm y, ?_, ?_⟩
          · refine ⟨(extChartAt I α).symm ((toEuclidean (E := E)).symm y), hin, ?_⟩
            exact (extChartAt I α).right_inv hz_target
          · exact (toEuclidean (E := E)).apply_symm_apply y
        have hf_zero : f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = 0 :=
          image_eq_zero_of_notMem_tsupport hxsupp
        change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
                  f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
                else (0 : ℝ)) = 0
        rw [if_pos hz_target, hf_zero]
      · change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
                  f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
                else (0 : ℝ)) = 0
        rw [if_neg hz_target]
    exact hK_compact.of_isClosed_subset (isClosed_tsupport _) h_sub_image
  have hψ_mem_W1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) p ψ
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
    have h := DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport_pub
      (d := Module.finrank ℝ E)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
        (I := I) (M := M) α)
      hψ_smooth hψ_compact_supp hψ_supp hp_one 1
    exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p).mp h
  have h_ae_chartPushed : DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
      (I := I) (M := M) (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u
      =ᵐ[(volume : Measure EuclN_E).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)]
      ψ := (chartSmoothExt_eq_chartPushed_pou_ae (I := I) (M := M) α u).symm
  have h_classical_isWeak :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (fun y : EuclN_E => fderiv ℝ ψ y (EuclideanSpace.single i 1)) ψ
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) :=
    DeGiorgi.HasWeakPartialDeriv.of_contDiff
      (Ω := DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α)
      (i := i) (f := ψ)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
        (I := I) (M := M) α)
      (hψ_smooth.of_le (by norm_cast))
  have h_chosen_isWeak :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) p i ψ
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)) ψ
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
      hψ_mem_W1p i
  have h_classical_loc : LocallyIntegrable
      (fun y : EuclN_E => fderiv ℝ ψ y (EuclideanSpace.single i (1 : ℝ)))
      ((volume : Measure EuclN_E).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) := by
    have h_cont : Continuous
        (fun y : EuclN_E => fderiv ℝ ψ y (EuclideanSpace.single i (1 : ℝ))) :=
      (hψ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
    exact h_cont.locallyIntegrable.mono_measure Measure.restrict_le_self
  have h_chosen_loc : LocallyIntegrable
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p i ψ
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))
      ((volume : Measure EuclN_E).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) :=
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
      hψ_mem_W1p i).locallyIntegrable hp_one
  have h_chosen_psi_ae :
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p i ψ
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))
        =ᵐ[(volume : Measure EuclN_E).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)]
        (fun y : EuclN_E => fderiv ℝ ψ y (EuclideanSpace.single i (1 : ℝ))) :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq
      (Ω := DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
        (I := I) (M := M) α)
      h_chosen_isWeak h_classical_isWeak
      h_chosen_loc h_classical_loc
  have h_chartPushed_mem_W1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) p
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
    have h := DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p (d := Module.finrank ℝ E) (p := p)
      (u := DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
      (Ω := DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α)
    refine h.mp ?_
    have h_psi_mem : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 1 p ψ
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) :=
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p).mpr hψ_mem_W1p
    exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
      (d := Module.finrank ℝ E) hp_one
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
        (I := I) (M := M) α) h_ae_chartPushed).mpr h_psi_mem
  have h_chosen_chartPushed_isWeak :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) p i
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
            (I := I) (M := M) (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
      h_chartPushed_mem_W1p i
  have h_chosen_chartPushed_isWeak_psi :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) p i
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
            (I := I) (M := M) (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α))
        ψ
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) := by
    intro φ hφ_smooth hφ_compact hφ_supp
    have h_lhs := h_chosen_chartPushed_isWeak φ hφ_smooth hφ_compact hφ_supp
    rw [show (∫ x in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α,
            ψ x * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) =
          ∫ x in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α,
            DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
              (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u x *
              (fderiv ℝ φ x) (EuclideanSpace.single i 1) from ?_]
    · exact h_lhs
    · refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [h_ae_chartPushed] with x hx
      rw [hx]
  have h_chosen_chartPushed_loc : LocallyIntegrable
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p i
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))
      ((volume : Measure EuclN_E).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) :=
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
      h_chartPushed_mem_W1p i).locallyIntegrable hp_one
  exact DeGiorgi.HasWeakPartialDeriv.ae_eq
    (Ω := DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α)
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α)
    h_chosen_chartPushed_isWeak_psi h_classical_isWeak
    h_chosen_chartPushed_loc h_classical_loc

/-- Sum over `Fin 1 → Fin d` indexed via the natural equivalence. -/
private lemma sum_Fin1_eq_sum_Fin (d : ℕ)
    (f : Fin (d) → ℝ≥0∞) :
    ∑ β : Fin 1 → Fin d, f (β 0) = ∑ i : Fin d, f i := by
  classical
  let e : (Fin 1 → Fin d) ≃ Fin d :=
    { toFun := fun β => β 0
      invFun := fun i _ => i
      left_inv := fun β => by funext j; have hj : j = 0 := Subsingleton.elim _ _; rw [hj]
      right_inv := fun _ => rfl }
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- For each α and smooth `u`, the per-α `wkpNorm` term is bounded by
`C_α · (eLpNorm u + eLpNorm √g(grad u, grad u))`, with `C_α` uniform in `u`. -/
private lemma wkpNorm_chartPushed_le_const_mul_per_α
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 1 p
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
            (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) ≤
        ENNReal.ofReal C *
          (eLpNorm u p
              (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) +
            eLpNorm (fun x : M => Real.sqrt
                (g.inner x
                  (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
                  (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x))) p
              (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g)) := by
  classical
  obtain ⟨C_Lp, hC_Lp_nn, hC_Lp_bound⟩ :=
    eLpNorm_chartPushed_le_const_mul_eLpNorm_u (I := I) (M := M) g α hp_one hp_top
  obtain ⟨C_grad, hC_grad_nn, hC_grad_bound⟩ :=
    eLpNorm_fderiv_chartSmoothExt_apply_le_const_mul (I := I) (M := M) g α hp_one hp_top
  refine ⟨C_Lp + (Module.finrank ℝ E : ℝ) * C_grad,
    add_nonneg hC_Lp_nn (mul_nonneg (Nat.cast_nonneg _) hC_grad_nn), ?_⟩
  intro u hu
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_eq_sum]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  haveI : Unique (Fin 0 → Fin (Module.finrank ℝ E)) :=
    { default := fun i : Fin 0 => i.elim0
      uniq := fun β => by funext j; exact j.elim0 }
  rw [Fintype.sum_unique]
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_zero]
  have h_j1_eq : (∑ β : Fin 1 → Fin (Module.finrank ℝ E),
      eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
          (d := Module.finrank ℝ E) p 1 β
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
            (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))
        p
        ((volume : Measure EuclN_E).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))) =
      ∑ i : Fin (Module.finrank ℝ E),
        eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) p i
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
              (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))
          p
          ((volume : Measure EuclN_E).restrict
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)) := by
    have h_unfold : ∀ β : Fin 1 → Fin (Module.finrank ℝ E),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
            (d := Module.finrank ℝ E) p 1 β
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
              (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α) =
          DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) p (β 0)
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
              (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α) := by
      intro β
      rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_succ]
      simp [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_zero]
    rw [Finset.sum_congr rfl (fun β _ => congrArg (fun ψ : EuclN_E → ℝ =>
      eLpNorm ψ p
        ((volume : Measure EuclN_E).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)))
      (h_unfold β))]
    exact sum_Fin1_eq_sum_Fin (Module.finrank ℝ E) (fun i =>
      eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) p i
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
            (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))
        p
        ((volume : Measure EuclN_E).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)))
  rw [h_j1_eq]
  have h_Lp := hC_Lp_bound (u := u) hu
  have h_Lp_step :
      eLpNorm (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u) p
          ((volume : Measure EuclN_E).restrict
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)) ≤
        ENNReal.ofReal C_Lp *
          (eLpNorm u p
              (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) +
            eLpNorm (fun x : M => Real.sqrt
                (g.inner x
                  (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
                  (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x))) p
              (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g)) := by
    refine h_Lp.trans ?_; gcongr; exact le_self_add
  have h_chosenWP_eq : ∀ i : Fin (Module.finrank ℝ E),
      eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) p i
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
            (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))
        p
        ((volume : Measure EuclN_E).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)) =
      eLpNorm
        (fun y : EuclN_E => fderiv ℝ
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α
            (fun z : M => ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)) y
            (EuclideanSpace.single i (1 : ℝ)))
        p
        ((volume : Measure EuclN_E).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)) :=
    fun i => eLpNorm_congr_ae
      (chosenWeakPartial_chartPushed_ae_eq_fderiv (I := I) (M := M) α hp_one hu i)
  rw [Finset.sum_congr rfl (fun i _ => h_chosenWP_eq i)]
  have h_grad_each : ∀ i : Fin (Module.finrank ℝ E),
      eLpNorm
        (fun y : EuclN_E => fderiv ℝ
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α
            (fun z : M => ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)) y
            (EuclideanSpace.single i (1 : ℝ)))
        p
        ((volume : Measure EuclN_E).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)) ≤
      ENNReal.ofReal C_grad *
        (eLpNorm u p
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) +
          eLpNorm (fun x : M => Real.sqrt
              (g.inner x
                (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
                (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x))) p
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g)) :=
    fun i => hC_grad_bound (u := u) hu i
  have h_grad_sum_le := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) => h_grad_each i)
  have h_const_sum :
      (∑ _ : Fin (Module.finrank ℝ E), ENNReal.ofReal C_grad *
        (eLpNorm u p
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) +
          eLpNorm (fun x : M => Real.sqrt
              (g.inner x
                (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
                (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x))) p
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g))) =
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ) * C_grad) *
        (eLpNorm u p
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) +
          eLpNorm (fun x : M => Real.sqrt
              (g.inner x
                (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
                (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x))) p
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g)) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [nsmul_eq_mul, ← mul_assoc]
    congr 1
    rw [show ((Module.finrank ℝ E : ℕ) : ℝ≥0∞) = ENNReal.ofReal (Module.finrank ℝ E : ℝ) from by
      rw [ENNReal.ofReal_natCast]]
    rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  have h_grad_total :
      (∑ i : Fin (Module.finrank ℝ E),
        eLpNorm
          (fun y : EuclN_E => fderiv ℝ
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
              (I := I) (M := M) α
              (fun z : M => ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)) y
              (EuclideanSpace.single i (1 : ℝ)))
          p
          ((volume : Measure EuclN_E).restrict
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))) ≤
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ) * C_grad) *
        (eLpNorm u p
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) +
          eLpNorm (fun x : M => Real.sqrt
              (g.inner x
                (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
                (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x))) p
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g)) := by
    refine h_grad_sum_le.trans ?_
    rw [h_const_sum]
  refine (add_le_add h_Lp_step h_grad_total).trans ?_
  rw [← add_mul]
  gcongr
  rw [ENNReal.ofReal_add hC_Lp_nn (mul_nonneg (Nat.cast_nonneg _) hC_grad_nn)]

private lemma chartPushed_eq_zero_of_pou_zero
    [T2Space M] [SigmaCompactSpace M] (α : M) (u : M → ℝ)
    (h_pou_zero : ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) = (fun _ : M => (0 : ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u =
      (fun _ : EuclN_E => (0 : ℝ)) := by
  funext y
  simp only [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed]
  rw [show ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = 0 from by rw [h_pou_zero]]
  simp

/-- Reverse direction (uniform-in-`u`). For a closed Riemannian manifold
modelled on a finite-dim real inner-product space and an exponent
`1 ≤ p < ∞`, there is a finite constant `C ≥ 0` (depending only on `g`, `p`,
and the canonical chart-atlas partition of unity) such that for every smooth
`u : M → ℝ`, the chart-based Sobolev norm is bounded by `ENNReal.ofReal C`
times the sum of the manifold L^p norm of `u` and the manifold L^p norm of
the metric norm of the Riemannian gradient of `u`. -/
theorem wkpNormChart_le_const_mul_intrinsicLpComponents_smooth_uniform
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
        wkpNormChart (I := I) (M := M) g 1 p u ≤
          ENNReal.ofReal C *
            (eLpNorm u p
                (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) +
              eLpNorm (fun x : M => Real.sqrt
                  (g.inner x
                    (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
                      (I := I) g u x)
                    (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
                      (I := I) g u x))) p
                (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g)) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  set S : Finset M :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M)
  set Cα : M → ℝ := fun α => Classical.choose
    (wkpNorm_chartPushed_le_const_mul_per_α (I := I) (M := M) g α hp_one hp_top)
  have hCα_nn : ∀ α : M, 0 ≤ Cα α :=
    fun α => (Classical.choose_spec
      (wkpNorm_chartPushed_le_const_mul_per_α (I := I) (M := M) g α hp_one hp_top)).1
  refine ⟨∑ α ∈ S, Cα α, Finset.sum_nonneg (fun α _ => hCα_nn α), ?_⟩
  intro u hu
  have h_def : wkpNormChart (I := I) (M := M) g 1 p u =
      ∑' α : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 1 p
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
            (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) := rfl
  rw [h_def]
  have h_outside_zero : ∀ α : M, α ∉ S →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 1 p
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) = 0 := by
    intro α hα
    have h_supp_empty : Function.support
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) = ∅ := by
      have h := (DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset_mem
        (I := I) (M := M) (α := α)).not.mp hα
      rw [Set.not_nonempty_iff_eq_empty] at h
      exact h
    have hρ_zero : ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) = (fun _ : M => (0 : ℝ)) := by
      funext y
      have hy_notSupp : y ∉ Function.support
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by rw [h_supp_empty]; simp
      exact Function.notMem_support.mp hy_notSupp
    have h_chartPushed_zero := chartPushed_eq_zero_of_pou_zero (I := I) (M := M) α u hρ_zero
    rw [h_chartPushed_zero]
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero_fun_zero
      (d := Module.finrank ℝ E) hp_one
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
        (I := I) (M := M) α)
  rw [tsum_eq_sum (s := S) h_outside_zero]
  have h_per_α : ∀ α ∈ S,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 1 p
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) ≤
      ENNReal.ofReal (Cα α) *
        (eLpNorm u p
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) +
          eLpNorm (fun x : M => Real.sqrt
              (g.inner x
                (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
                (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x))) p
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g)) :=
    fun α _ => (Classical.choose_spec
      (wkpNorm_chartPushed_le_const_mul_per_α (I := I) (M := M) g α hp_one hp_top)).2 hu
  refine (Finset.sum_le_sum h_per_α).trans ?_
  rw [← Finset.sum_mul]
  gcongr
  rw [show (∑ α ∈ S, ENNReal.ofReal (Cα α)) = ENNReal.ofReal (∑ α ∈ S, Cα α) from
    (ENNReal.ofReal_sum_of_nonneg (fun α _ => hCα_nn α)).symm]

end EquivalenceReverse
end Sobolev
end Analysis
end DifferentialGeometry
