import DifferentialGeometry.Geometry.Riemannian.Exponential.Definition
import DifferentialGeometry.Geometry.Riemannian.Exponential.Unconditional
import DifferentialGeometry.Geometry.Riemannian.Exponential.FinalClosure
import DifferentialGeometry.Geometry.Riemannian.Exponential.ChainedFlowContinuity

set_option linter.unusedSectionVars false

/-!
# Off-zero `ContMDiffAt 1` regularity of `expMap`

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`
modelled on a complete inner-product space `E`, this file records the
off-zero (`v ≠ 0`) analogue of the at-zero smoothness lemma
`expMap_contMDiffAt_zero_of_chartFlowGeodesicMatchData`.

Away from the zero vector the regularity of the exponential map is
unconditional: the `HasChartFlowGeodesicMatchData` hypothesis required at
the zero vector is not needed once `v ≠ 0`, because the geodesic flow is
jointly smooth in `(t, v)` along any orbit with non-zero initial velocity.

## Main result

* `expMap_contMDiffAt_of_ne_zero` — for `v ≠ 0`, the exponential map
  `fun w : E => expMap g p w` is `ContMDiffAt 𝓘(ℝ, E) I 1` at `v`.

## Single-chart building blocks (M1 / M2)

The off-zero argument is the analogue of the at-zero argument with the
fixed home chart `extChartAt I p` replaced by a chain of charts along the
geodesic arc `[0, 1] ∋ s ↦ maximalGeodesic g p v s`. Two of its
ingredients are single-chart and are recorded here, fully proven:

* **M1 (single-chart slice C¹).** The chart-flow candidate
  `chartFlowCandidate Φ p t'` produced by the unified packaging is
  `ContMDiffAt 𝓘(ℝ, E) I 1` *at every* `v₁` in the spatial ball of the
  unified data, not only at `v₁ = 0`. This is `private`
  `chartFlowCandidate_contMDiffAt_of_mem_ball` below; it generalises the
  zero-point lemma `chartFlowCandidate_contMDiffAt_zero_at_origin` to an
  arbitrary interior point of the ball, by evaluating the `ContDiffOn 1`
  flow at that point rather than at the centre.

* **M2 (single-curve identification by uniqueness).** Along a single
  home chart, `(chartFlowOrbitLiftRescaled Φ p t' v 1).proj =
  expMap g p (t' • v)` — the rescaled-lift projection identity at `s = 1`
  (`chartFlowOrbitLiftRescaled_proj_at_one`, proven in `RescaledLift.lean`
  via preconnected propagation against the chosen maximal-geodesic curve).
  Combined with M1 this yields the *small-vector* off-zero statement
  `expMap_contMDiffAt_of_norm_lt` below: `w ↦ expMap g p w` is
  `ContMDiffAt 𝓘(ℝ, E) I 1` at every `w` with `‖w‖ < t' * ρ` (a
  punctured ball whose closure stays inside the home chart's reach).

These two are the single-chart skeleton of the off-zero argument. The
remaining content — reaching an arbitrary fixed `v ≠ 0` whose geodesic
leaves the home chart — is genuinely cross-chart and is supplied by the
re-basing and chart-cover gluing recorded as separate obligations
(`Geodesic.bm_c_gc_cross_vf_projection_uniqueness` and the chained-flow
joint regularity); see the proof of `expMap_contMDiffAt_of_ne_zero`.
-/

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section SliceAtBallPoint

/-- **Slice `C¹` at a general ball point.** For a chart-flow `Φ`,
`ContDiffOn ℝ 1` on `ball ((x₀, 0), ρ) ×ˢ Ioo (-T) T`, and `v₁` with
`‖v₁‖ < ρ`, `t' ∈ Ioo (-T) T`, the velocity slice
`v ↦ (Φ((x₀, v), t')).1` is `ContDiffAt ℝ 1` at `v₁`. -/
private lemma contDiffAt_chartFlow_slice_fst_of_mem_ball
    {Φ : (E × E) × ℝ → E × E} {x₀ : E} {ρ T t' : ℝ} {v₁ : E}
    (hv₁ : ‖v₁‖ < ρ) (ht' : t' ∈ Set.Ioo (-T) T)
    (hcd : ContDiffOn ℝ 1 Φ
      ((Metric.ball ((x₀, (0 : E)) : E × E) ρ) ×ˢ Set.Ioo (-T) T)) :
    ContDiffAt ℝ 1 (fun v : E => (Φ (((x₀, v) : E × E), t')).1) v₁ := by
  classical
  have hpair_cd : ContDiff ℝ 1 (fun v : E => (((x₀, v) : E × E), t')) := by
    have h_const_x₀ : ContDiff ℝ 1 (fun _ : E => x₀) := contDiff_const
    have h_id : ContDiff ℝ 1 (fun v : E => v) := contDiff_id
    have h_pair_E2 : ContDiff ℝ 1 (fun v : E => ((x₀, v) : E × E)) :=
      h_const_x₀.prodMk h_id
    have h_const_t : ContDiff ℝ 1 (fun _ : E => t') := contDiff_const
    exact h_pair_E2.prodMk h_const_t
  have hmem : (((x₀, v₁) : E × E), t') ∈
      (Metric.ball ((x₀, (0 : E)) : E × E) ρ) ×ˢ Set.Ioo (-T) T := by
    refine ⟨?_, ht'⟩
    rw [Metric.mem_ball, Prod.dist_eq]
    simp only [dist_self, dist_zero_right]
    have : max (0 : ℝ) ‖v₁‖ = ‖v₁‖ := max_eq_right (norm_nonneg v₁)
    rw [this]; exact hv₁
  have hopen : IsOpen
      ((Metric.ball ((x₀, (0 : E)) : E × E) ρ) ×ˢ Set.Ioo (-T) T) :=
    Metric.isOpen_ball.prod isOpen_Ioo
  have hΦ_cda : ContDiffAt ℝ 1 Φ (((x₀, v₁) : E × E), t') :=
    hcd.contDiffAt (hopen.mem_nhds hmem)
  have hslice : ContDiffAt ℝ 1 (fun v : E => Φ (((x₀, v) : E × E), t')) v₁ :=
    hΦ_cda.comp v₁ hpair_cd.contDiffAt
  have hfst : ContDiff ℝ 1 (Prod.fst : E × E → E) := contDiff_fst
  exact hfst.contDiffAt.comp v₁ hslice

/-- **Slice `C^2` at a general ball point.** The `C^2` analogue of
`contDiffAt_chartFlow_slice_fst_of_mem_ball`: for a chart-flow `Φ`,
`ContDiffOn ℝ 2` on `ball ((x₀, 0), ρ) ×ˢ Ioo (-T) T`, and `v₁` with
`‖v₁‖ < ρ`, `t' ∈ Ioo (-T) T`, the velocity slice
`v ↦ (Φ((x₀, v), t')).1` is `ContDiffAt ℝ 2` at `v₁`. -/
private lemma contDiffAt_chartFlow_slice_fst_of_mem_ball_two
    {Φ : (E × E) × ℝ → E × E} {x₀ : E} {ρ T t' : ℝ} {v₁ : E}
    (hv₁ : ‖v₁‖ < ρ) (ht' : t' ∈ Set.Ioo (-T) T)
    (hcd : ContDiffOn ℝ 2 Φ
      ((Metric.ball ((x₀, (0 : E)) : E × E) ρ) ×ˢ Set.Ioo (-T) T)) :
    ContDiffAt ℝ 2 (fun v : E => (Φ (((x₀, v) : E × E), t')).1) v₁ := by
  classical
  have hpair_cd : ContDiff ℝ 2 (fun v : E => (((x₀, v) : E × E), t')) := by
    have h_const_x₀ : ContDiff ℝ 2 (fun _ : E => x₀) := contDiff_const
    have h_id : ContDiff ℝ 2 (fun v : E => v) := contDiff_id
    have h_pair_E2 : ContDiff ℝ 2 (fun v : E => ((x₀, v) : E × E)) :=
      h_const_x₀.prodMk h_id
    have h_const_t : ContDiff ℝ 2 (fun _ : E => t') := contDiff_const
    exact h_pair_E2.prodMk h_const_t
  have hmem : (((x₀, v₁) : E × E), t') ∈
      (Metric.ball ((x₀, (0 : E)) : E × E) ρ) ×ˢ Set.Ioo (-T) T := by
    refine ⟨?_, ht'⟩
    rw [Metric.mem_ball, Prod.dist_eq]
    simp only [dist_self, dist_zero_right]
    have : max (0 : ℝ) ‖v₁‖ = ‖v₁‖ := max_eq_right (norm_nonneg v₁)
    rw [this]; exact hv₁
  have hopen : IsOpen
      ((Metric.ball ((x₀, (0 : E)) : E × E) ρ) ×ˢ Set.Ioo (-T) T) :=
    Metric.isOpen_ball.prod isOpen_Ioo
  have hΦ_cda : ContDiffAt ℝ 2 Φ (((x₀, v₁) : E × E), t') :=
    hcd.contDiffAt (hopen.mem_nhds hmem)
  have hslice : ContDiffAt ℝ 2 (fun v : E => Φ (((x₀, v) : E × E), t')) v₁ :=
    hΦ_cda.comp v₁ hpair_cd.contDiffAt
  have hfst : ContDiff ℝ 2 (Prod.fst : E × E → E) := contDiff_fst
  exact hfst.contDiffAt.comp v₁ hslice

/-- **Slice `C^n` at a general ball point.** The finite-order analogue of
`contDiffAt_chartFlow_slice_fst_of_mem_ball`: for a chart-flow `Φ`,
`ContDiffOn ℝ n` on `ball ((x₀, 0), ρ) ×ˢ Ioo (-T) T`, and `v₁` with
`‖v₁‖ < ρ`, `t' ∈ Ioo (-T) T`, the velocity slice
`v ↦ (Φ((x₀, v), t')).1` is `ContDiffAt ℝ n` at `v₁`. -/
private lemma contDiffAt_chartFlow_slice_fst_of_mem_ball_nat
    {Φ : (E × E) × ℝ → E × E} {x₀ : E} {ρ T t' : ℝ} {v₁ : E} (n : ℕ)
    (hv₁ : ‖v₁‖ < ρ) (ht' : t' ∈ Set.Ioo (-T) T)
    (hcd : ContDiffOn ℝ (n : ℕ∞) Φ
      ((Metric.ball ((x₀, (0 : E)) : E × E) ρ) ×ˢ Set.Ioo (-T) T)) :
    ContDiffAt ℝ (n : ℕ∞) (fun v : E => (Φ (((x₀, v) : E × E), t')).1) v₁ := by
  classical
  have hpair_cd : ContDiff ℝ (n : ℕ∞) (fun v : E => (((x₀, v) : E × E), t')) := by
    have h_const_x₀ : ContDiff ℝ (n : ℕ∞) (fun _ : E => x₀) := contDiff_const
    have h_id : ContDiff ℝ (n : ℕ∞) (fun v : E => v) := contDiff_id
    have h_pair_E2 : ContDiff ℝ (n : ℕ∞) (fun v : E => ((x₀, v) : E × E)) :=
      h_const_x₀.prodMk h_id
    have h_const_t : ContDiff ℝ (n : ℕ∞) (fun _ : E => t') := contDiff_const
    exact h_pair_E2.prodMk h_const_t
  have hmem : (((x₀, v₁) : E × E), t') ∈
      (Metric.ball ((x₀, (0 : E)) : E × E) ρ) ×ˢ Set.Ioo (-T) T := by
    refine ⟨?_, ht'⟩
    rw [Metric.mem_ball, Prod.dist_eq]
    simp only [dist_self, dist_zero_right]
    have : max (0 : ℝ) ‖v₁‖ = ‖v₁‖ := max_eq_right (norm_nonneg v₁)
    rw [this]; exact hv₁
  have hopen : IsOpen
      ((Metric.ball ((x₀, (0 : E)) : E × E) ρ) ×ˢ Set.Ioo (-T) T) :=
    Metric.isOpen_ball.prod isOpen_Ioo
  have hΦ_cda : ContDiffAt ℝ (n : ℕ∞) Φ (((x₀, v₁) : E × E), t') :=
    hcd.contDiffAt (hopen.mem_nhds hmem)
  have hslice : ContDiffAt ℝ (n : ℕ∞)
      (fun v : E => Φ (((x₀, v) : E × E), t')) v₁ :=
    hΦ_cda.comp v₁ hpair_cd.contDiffAt
  have hfst : ContDiff ℝ (n : ℕ∞) (Prod.fst : E × E → E) := contDiff_fst
  exact hfst.contDiffAt.comp v₁ hslice

end SliceAtBallPoint

section CandidateAtBallPoint

variable [I.Boundaryless] [CompleteSpace E]

/-- **Candidate `ContMDiffAt 1` at a general ball point.** If the
chart-flow `Φ` is `ContDiffOn ℝ 1` on the velocity ball product, `v₁`
lies in the open ball of radius `ρ`, `t' ∈ Ioo (-T) T`, and the slice's
value at `v₁` lands in the chart target, then the manifold-valued
candidate `chartFlowCandidate Φ p t'` is `ContMDiffAt 𝓘(ℝ, E) I 1` at
`v₁`.

This is M1: the single-chart slice smoothness generalised from the centre
`v₁ = 0` of the at-zero argument to an arbitrary interior point. -/
private lemma chartFlowCandidate_contMDiffAt_of_mem_ball
    {p : M} {Φ : (E × E) × ℝ → E × E} {ρ T t' : ℝ} {v₁ : E}
    (hv₁ : ‖v₁‖ < ρ) (ht' : t' ∈ Set.Ioo (-T) T)
    (hcd : ContDiffOn ℝ 1 Φ
      ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ
        Set.Ioo (-T) T))
    (hval : (Φ (((extChartAt I p p, v₁) : E × E), t')).1 ∈
      interior (extChartAt I p).target) :
    ContMDiffAt 𝓘(ℝ, E) I 1
      (chartFlowCandidate (I := I) Φ p t') v₁ := by
  classical
  set x₀ : E := extChartAt I p p with hx₀_def
  have hslice :
      ContDiffAt ℝ 1 (fun v : E => (Φ (((x₀, v) : E × E), t')).1) v₁ :=
    contDiffAt_chartFlow_slice_fst_of_mem_ball (Φ := Φ) (x₀ := x₀)
      (ρ := ρ) (T := T) (t' := t') (v₁ := v₁) hv₁ ht' hcd
  have hval_target : (Φ (((x₀, v₁) : E × E), t')).1 ∈ (extChartAt I p).target :=
    interior_subset hval
  set s : E → E := fun v => (Φ (((x₀, v) : E × E), t')).1 with hs_def
  have hs_cmda : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 1 s v₁ :=
    hslice.contMDiffAt
  have hsymm_within : ContMDiffWithinAt 𝓘(ℝ, E) I 1
      (extChartAt I p).symm (extChartAt I p).target (s v₁) :=
    contMDiffWithinAt_extChartAt_symm_target (I := I) p hval_target
  have htarget_nhds : (extChartAt I p).target ∈ 𝓝 (s v₁) :=
    mem_nhds_iff.mpr ⟨interior (extChartAt I p).target, interior_subset,
      isOpen_interior, hval⟩
  have hsymm_at : ContMDiffAt 𝓘(ℝ, E) I 1 (extChartAt I p).symm (s v₁) :=
    hsymm_within.contMDiffAt htarget_nhds
  have hcand_eq : chartFlowCandidate (I := I) Φ p t' =
      (extChartAt I p).symm ∘ s := by
    funext v
    simp only [chartFlowCandidate_apply, Function.comp_apply, hs_def, hx₀_def]
  rw [hcand_eq]
  exact hsymm_at.comp v₁ hs_cmda

/-- **Candidate `ContMDiffAt 2` at a general ball point.** The `C^2`
analogue of `chartFlowCandidate_contMDiffAt_of_mem_ball`: if the
chart-flow `Φ` is `ContDiffOn ℝ 2` on the velocity ball product, `v₁`
lies in the open ball of radius `ρ`, `t' ∈ Ioo (-T) T`, and the slice's
value at `v₁` lands in the chart target, then the manifold-valued
candidate `chartFlowCandidate Φ p t'` is `ContMDiffAt 𝓘(ℝ, E) I 2` at
`v₁`.

This is the `C^2` strengthening of M1: the single-chart slice smoothness
at order `2`, generalised from the centre `v₁ = 0` to an arbitrary
interior point of the ball. -/
private lemma chartFlowCandidate_contMDiffAt2_of_mem_ball
    {p : M} {Φ : (E × E) × ℝ → E × E} {ρ T t' : ℝ} {v₁ : E}
    (hv₁ : ‖v₁‖ < ρ) (ht' : t' ∈ Set.Ioo (-T) T)
    (hcd : ContDiffOn ℝ 2 Φ
      ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ
        Set.Ioo (-T) T))
    (hval : (Φ (((extChartAt I p p, v₁) : E × E), t')).1 ∈
      interior (extChartAt I p).target) :
    ContMDiffAt 𝓘(ℝ, E) I 2
      (chartFlowCandidate (I := I) Φ p t') v₁ := by
  classical
  set x₀ : E := extChartAt I p p with hx₀_def
  have hslice :
      ContDiffAt ℝ 2 (fun v : E => (Φ (((x₀, v) : E × E), t')).1) v₁ :=
    contDiffAt_chartFlow_slice_fst_of_mem_ball_two (Φ := Φ) (x₀ := x₀)
      (ρ := ρ) (T := T) (t' := t') (v₁ := v₁) hv₁ ht' hcd
  have hval_target : (Φ (((x₀, v₁) : E × E), t')).1 ∈ (extChartAt I p).target :=
    interior_subset hval
  set s : E → E := fun v => (Φ (((x₀, v) : E × E), t')).1 with hs_def
  have hs_cmda : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 2 s v₁ :=
    hslice.contMDiffAt
  have hsymm_within : ContMDiffWithinAt 𝓘(ℝ, E) I 2
      (extChartAt I p).symm (extChartAt I p).target (s v₁) :=
    contMDiffWithinAt_extChartAt_symm_target (I := I) p hval_target
  have htarget_nhds : (extChartAt I p).target ∈ 𝓝 (s v₁) :=
    mem_nhds_iff.mpr ⟨interior (extChartAt I p).target, interior_subset,
      isOpen_interior, hval⟩
  have hsymm_at : ContMDiffAt 𝓘(ℝ, E) I 2 (extChartAt I p).symm (s v₁) :=
    hsymm_within.contMDiffAt htarget_nhds
  have hcand_eq : chartFlowCandidate (I := I) Φ p t' =
      (extChartAt I p).symm ∘ s := by
    funext v
    simp only [chartFlowCandidate_apply, Function.comp_apply, hs_def, hx₀_def]
  rw [hcand_eq]
  exact hsymm_at.comp v₁ hs_cmda

/-- **Candidate `ContMDiffAt n` at a general ball point.** The
finite-order analogue of `chartFlowCandidate_contMDiffAt_of_mem_ball`: if
the chart-flow `Φ` is `ContDiffOn ℝ n` on the velocity ball product, `v₁`
lies in the open ball of radius `ρ`, `t' ∈ Ioo (-T) T`, and the slice's
value at `v₁` lands in the chart target, then the manifold-valued
candidate `chartFlowCandidate Φ p t'` is `ContMDiffAt 𝓘(ℝ, E) I n` at
`v₁`.

This is the finite-order strengthening of M1: the single-chart slice
smoothness at order `n`, generalised from the centre `v₁ = 0` to an
arbitrary interior point of the ball. -/
private lemma chartFlowCandidate_contMDiffAt_nat_of_mem_ball
    {p : M} {Φ : (E × E) × ℝ → E × E} {ρ T t' : ℝ} {v₁ : E} (n : ℕ)
    (hv₁ : ‖v₁‖ < ρ) (ht' : t' ∈ Set.Ioo (-T) T)
    (hcd : ContDiffOn ℝ (n : ℕ∞) Φ
      ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ
        Set.Ioo (-T) T))
    (hval : (Φ (((extChartAt I p p, v₁) : E × E), t')).1 ∈
      interior (extChartAt I p).target) :
    ContMDiffAt 𝓘(ℝ, E) I ((n : ℕ∞) : WithTop ℕ∞)
      (chartFlowCandidate (I := I) Φ p t') v₁ := by
  classical
  set x₀ : E := extChartAt I p p with hx₀_def
  have hslice :
      ContDiffAt ℝ (n : ℕ∞) (fun v : E => (Φ (((x₀, v) : E × E), t')).1) v₁ :=
    contDiffAt_chartFlow_slice_fst_of_mem_ball_nat (Φ := Φ) (x₀ := x₀)
      (ρ := ρ) (T := T) (t' := t') (v₁ := v₁) n hv₁ ht' hcd
  have hval_target : (Φ (((x₀, v₁) : E × E), t')).1 ∈ (extChartAt I p).target :=
    interior_subset hval
  set s : E → E := fun v => (Φ (((x₀, v) : E × E), t')).1 with hs_def
  have hs_cmda : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ((n : ℕ∞) : WithTop ℕ∞) s v₁ :=
    hslice.contMDiffAt
  have hsymm_within : ContMDiffWithinAt 𝓘(ℝ, E) I ((n : ℕ∞) : WithTop ℕ∞)
      (extChartAt I p).symm (extChartAt I p).target (s v₁) :=
    contMDiffWithinAt_extChartAt_symm_target (I := I) p hval_target
  have htarget_nhds : (extChartAt I p).target ∈ 𝓝 (s v₁) :=
    mem_nhds_iff.mpr ⟨interior (extChartAt I p).target, interior_subset,
      isOpen_interior, hval⟩
  have hsymm_at : ContMDiffAt 𝓘(ℝ, E) I ((n : ℕ∞) : WithTop ℕ∞)
      (extChartAt I p).symm (s v₁) :=
    hsymm_within.contMDiffAt htarget_nhds
  have hcand_eq : chartFlowCandidate (I := I) Φ p t' =
      (extChartAt I p).symm ∘ s := by
    funext v
    simp only [chartFlowCandidate_apply, Function.comp_apply, hs_def, hx₀_def]
  rw [hcand_eq]
  exact hsymm_at.comp v₁ hs_cmda

end CandidateAtBallPoint

section SmallVector

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

/-- **Small-vector off-zero `C¹`.** There is a radius `δ > 0` such that
`w ↦ expMap g p w` is `ContMDiffAt 𝓘(ℝ, E) I 1` at every `w` with
`‖w‖ < δ`. This includes nonzero `w`: it is the off-zero analogue of the
at-zero headline, restricted to the single home chart `extChartAt I p`.

The proof reuses the unified chart-flow packaging
(`exists_unified_chartFlow_data`), M1
(`chartFlowCandidate_contMDiffAt_of_mem_ball`) for the candidate's `C¹`
smoothness on the whole spatial ball, and M2
(`chartFlowOrbitLiftRescaled_proj_at_one`) for the identification
`expMap g p (t' • v) = chartFlowCandidate Φ p t' v`, then transfers
through the smooth rescaling `w ↦ (1 / t') • w`. -/
theorem expMap_contMDiffAt_of_norm_lt
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : E, ‖w‖ < δ →
      ContMDiffAt 𝓘(ℝ, E) I 1
        (fun u : E => (expMap (I := I) g p (show TangentSpace I p from u) : M))
        w := by
  classical
  obtain ⟨Φ, ρ, T, T_match, hρ_pos, hT_pos, hT_match_pos, hT_match_le_T,
    hΦ_cd, hΦ_init0, hΦ_init_v, hΦ_target, hΦ_phase, hΦ_const_zero, _hF_int⟩ :=
    exists_unified_chartFlow_data (I := I) g p
  set t' : ℝ := T_match / 2 with ht'_def
  have ht'_pos : 0 < t' := by rw [ht'_def]; exact half_pos hT_match_pos
  have ht'_lt_T_match : t' < T_match := by
    rw [ht'_def]; exact half_lt_self hT_match_pos
  have ht'_lt_T : t' < T := lt_of_lt_of_le ht'_lt_T_match hT_match_le_T
  have ht'_in_Ioo : t' ∈ Set.Ioo (-T) T := ⟨by linarith, ht'_lt_T⟩
  have ht'_ne : t' ≠ 0 := ne_of_gt ht'_pos
  set x₀ : E := extChartAt I p p with hx₀_def
  have hmatch : ∀ v : E, v ∈ Metric.ball (0 : E) ρ →
      (expMap (I := I) g p (show TangentSpace I p from (t' • v)) : M) =
        chartFlowCandidate (I := I) Φ p t' v := by
    intro v hv_ball
    have hΦ_init_v_at : Φ (((x₀, v) : E × E), 0) = ((x₀, v) : E × E) :=
      hΦ_init_v v hv_ball
    have hΦ_target_v : ∀ s ∈ Set.Icc (-T) T,
        Φ (((x₀, v) : E × E), s) ∈
          (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
      intro s hs; exact hΦ_target v hv_ball s hs
    have hΦ_phase_v : ∀ s ∈ Set.Ioo (-T) T,
        HasDerivAt (fun s' : ℝ => Φ (((x₀, v) : E × E), s'))
          (chartPhaseVF (I := I) g p (Φ (((x₀, v) : E × E), s))) s := by
      intro s hs; exact hΦ_phase v hv_ball s hs
    have hproj1 :=
      chartFlowOrbitLiftRescaled_proj_at_one (I := I) (g := g) (p := p) (v := v)
        (T := T) (t' := t') ht'_pos ht'_lt_T (Φ := Φ)
        hΦ_init_v_at hΦ_target_v hΦ_phase_v
    have hΦ_target_t' : Φ (((x₀, v) : E × E), t' * 1) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
      rw [mul_one]
      exact hΦ_target_v t' (Set.Ioo_subset_Icc_self ht'_in_Ioo)
    have hproj_def :=
      chartFlowOrbitLiftRescaled_proj (I := I) (p := p) (v := v) (t' := t')
        (Φ := Φ) (s := 1) hΦ_target_t'
    have hcand_unfold : chartFlowCandidate (I := I) Φ p t' v =
        (extChartAt I p).symm (Φ (((x₀, v) : E × E), t')).1 := rfl
    have hproj_def' :
        (chartFlowOrbitLiftRescaled (I := I) Φ p t' v 1).proj =
          (extChartAt I p).symm (Φ (((x₀, v) : E × E), t')).1 := by
      rw [hproj_def, mul_one]
    rw [← hproj1, hproj_def', ← hcand_unfold]
  refine ⟨t' * ρ, by positivity, ?_⟩
  intro w hw
  set v₁ : E := (1 / t') • w with hv₁_def
  have hv₁_norm : ‖v₁‖ < ρ := by
    rw [hv₁_def, norm_smul]
    have h1t' : ‖(1 / t' : ℝ)‖ = 1 / t' := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [h1t']
    rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ ht'_pos]
    calc ‖w‖ < t' * ρ := hw
      _ = ρ * t' := by ring
  have hv₁_ball : v₁ ∈ Metric.ball (0 : E) ρ := by
    rw [Metric.mem_ball, dist_zero_right]; exact hv₁_norm
  have htv₁_eq_w : t' • v₁ = w := by
    rw [hv₁_def, smul_smul, mul_one_div, div_self ht'_ne, one_smul]
  have hval_int : (Φ (((x₀, v₁) : E × E), t')).1 ∈
      interior (extChartAt I p).target := by
    have := hΦ_target v₁ hv₁_ball t' (Set.Ioo_subset_Icc_self ht'_in_Ioo)
    exact this.1
  have hcand_cd : ContMDiffAt 𝓘(ℝ, E) I 1
      (chartFlowCandidate (I := I) Φ p t') v₁ :=
    chartFlowCandidate_contMDiffAt_of_mem_ball (I := I) (p := p) (Φ := Φ)
      (ρ := ρ) (T := T) (t' := t') (v₁ := v₁) hv₁_norm ht'_in_Ioo hΦ_cd hval_int
  have hsmul_cd : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 (fun u : E => (1 / t') • u) := by
    have h0 : ContDiff ℝ ∞ (fun u : E => (1 / t') • u) :=
      contDiff_const.smul contDiff_id
    have h1 : ContDiff ℝ 1 (fun u : E => (1 / t') • u) :=
      h0.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
    exact h1.contMDiff
  have hsmul_at : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 1
      (fun u : E => (1 / t') • u) w := hsmul_cd.contMDiffAt
  have hsmul_w_eq : (fun u : E => (1 / t') • u) w = v₁ := by
    rw [hv₁_def]
  have hcand_cd' : ContMDiffAt 𝓘(ℝ, E) I 1
      (chartFlowCandidate (I := I) Φ p t')
      ((fun u : E => (1 / t') • u) w) := by
    rw [hsmul_w_eq]; exact hcand_cd
  have hcomp : ContMDiffAt 𝓘(ℝ, E) I 1
      ((chartFlowCandidate (I := I) Φ p t') ∘ (fun u : E => (1 / t') • u)) w :=
    hcand_cd'.comp w hsmul_at
  have hev :
      (fun u : E => (expMap (I := I) g p (show TangentSpace I p from u) : M))
        =ᶠ[𝓝 w]
      ((chartFlowCandidate (I := I) Φ p t') ∘ (fun u : E => (1 / t') • u)) := by
    have hsmul_cont : Continuous (fun u : E => (1 / t') • u) :=
      continuous_const.smul continuous_id
    have hpre : (fun u : E => (1 / t') • u) ⁻¹' Metric.ball (0 : E) ρ ∈ 𝓝 w := by
      have hnhd : Metric.ball (0 : E) ρ ∈ 𝓝 ((fun u : E => (1 / t') • u) w) := by
        rw [hsmul_w_eq]; exact Metric.isOpen_ball.mem_nhds hv₁_ball
      exact hsmul_cont.continuousAt.preimage_mem_nhds hnhd
    filter_upwards [hpre] with u hu
    have hheq := hmatch ((1 / t') • u) hu
    have htu_eq : t' • ((1 / t') • u) = u := by
      rw [smul_smul, mul_one_div, div_self ht'_ne, one_smul]
    rw [htu_eq] at hheq
    change (expMap (I := I) g p (show TangentSpace I p from u) : M) = _
    simp only [Function.comp_apply]
    exact hheq
  exact hcomp.congr_of_eventuallyEq hev

/-- **Unified `C^2` chart-flow packaging.** The `C^2` analogue of
`exists_unified_chartFlow_data`: a single chart-pushed flow
`Φ : (E × E) × ℝ → E × E` together with uniform radii `(ρ, T, T_match)`
supplying joint `ContDiffOn ℝ 2` regularity on
`ball ((x₀, 0)) ρ × Ioo (-T) T` and the same family of order-agnostic
properties (initial conditions, chart-target confinement, the genuine
chart-phase ODE, and the manifold-lift integral-curve property) as the
`C^1` packaging.  Here `x₀ := extChartAt I p p`. -/
private theorem exists_unified_chartFlow_data_two
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ (Φ : (E × E) × ℝ → E × E) (ρ T T_match : ℝ),
      0 < ρ ∧ 0 < T ∧ 0 < T_match ∧ T_match ≤ T ∧
      ContDiffOn ℝ 2 Φ
        ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ
          Set.Ioo (-T) T) ∧
      Φ (((extChartAt I p p, (0 : E)) : E × E), 0) =
        ((extChartAt I p p, (0 : E)) : E × E) ∧
      (∀ v ∈ Metric.ball (0 : E) ρ,
        Φ (((extChartAt I p p, v) : E × E), 0) =
          ((extChartAt I p p, v) : E × E)) ∧
      (∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Icc (-T) T,
        Φ (((extChartAt I p p, v) : E × E), s) ∈
          (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)) ∧
      (∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Ioo (-T) T,
        HasDerivAt (fun s' : ℝ => Φ (((extChartAt I p p, v) : E × E), s'))
          (chartPhaseVF (I := I) g p
            (Φ (((extChartAt I p p, v) : E × E), s))) s) ∧
      (∀ s ∈ Set.Ioo (-T_match) T_match,
        Φ (((extChartAt I p p, (0 : E)) : E × E), s) =
          ((extChartAt I p p, (0 : E)) : E × E)) ∧
      (∀ v ∈ Metric.ball (0 : E) ρ,
        IsMIntegralCurveOn (chartFlowOrbitLift (I := I) Φ p v)
          (geodesicVectorFieldChart (I := I) g p) (Set.Ioo (-T) T)) := by
  classical
  set x₀ : E := extChartAt I p p with hx₀_def
  have hx₀_src : p ∈ (extChartAt I p).source :=
    mem_extChartAt_source (I := I) p
  have hx₀_target : x₀ ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source hx₀_src
  have hx₀_interior : x₀ ∈ interior (extChartAt I p).target :=
    DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) p hx₀_target
  obtain ⟨b, r, ε, ρ_V4, T_V4, Φ, hr, hε, hρ_V4_pos, hT_V4_pos, hb_sub, hΦ_ILF,
    hΦ_cd_V4_two, hΦ_init0⟩ :=
    Geodesic.exists_chartPhase_contDiffOn_isLocalFlow_combined_two
      (I := I) (g := g) (α := p) (x₀ := x₀) (v₀ := (0 : E)) hx₀_interior
  have hΦ_cd_V4 : ContDiffOn ℝ 1 Φ
      ((Metric.ball ((x₀, (0 : E)) : E × E) ρ_V4) ×ˢ Set.Ioo (-T_V4) T_V4) :=
    hΦ_cd_V4_two.of_le (by norm_num)
  obtain ⟨ρ₀, T₀, hρ₀_pos, hT₀_pos, hρ₀_le_V4, hT₀_lt_V4, h_orbit_in⟩ :=
    exists_uniform_orbit_in_inner_ball (I := I) (g := g) (p := p)
      (x₀ := x₀) hx₀_def
      (b := b) (ρ_V4 := ρ_V4) (T_V4 := T_V4) hρ_V4_pos hT_V4_pos
      (Φ := Φ) hΦ_cd_V4 hΦ_init0
  set ρ : ℝ := min ρ₀ ((r : ℝ) / 2) with hρ_def
  have hρ_pos : 0 < ρ := by
    apply lt_min hρ₀_pos
    have : (0 : ℝ) < (r : ℝ) := hr
    linarith
  have hρ_le_ρ₀ : ρ ≤ ρ₀ := min_le_left _ _
  have hρ_le_ρ_V4 : ρ ≤ ρ_V4 := le_trans hρ_le_ρ₀ hρ₀_le_V4
  have hρ_le_r : ρ ≤ (r : ℝ) := by
    rw [hρ_def]
    have h1 : min ρ₀ ((r : ℝ) / 2) ≤ (r : ℝ) / 2 := min_le_right _ _
    have h2 : (r : ℝ) / 2 ≤ (r : ℝ) := by
      have hrnn : (0 : ℝ) ≤ (r : ℝ) := r.coe_nonneg
      linarith
    linarith
  set T : ℝ := min T₀ (ε / 2) with hT_def
  have hT_pos : 0 < T :=
    lt_min hT₀_pos (by linarith)
  have hT_le_T₀ : T ≤ T₀ := min_le_left _ _
  have hT_lt_ε : T < ε := by
    have h1 : min T₀ (ε / 2) ≤ ε / 2 := min_le_right _ _
    have : T = min T₀ (ε / 2) := hT_def
    rw [this]; linarith
  have hT_lt_T_V4 : T < T_V4 := lt_of_le_of_lt hT_le_T₀ hT₀_lt_V4
  have hΦ_cd : ContDiffOn ℝ 2 Φ
      ((Metric.ball ((x₀, (0 : E)) : E × E) ρ) ×ˢ Set.Ioo (-T) T) := by
    apply hΦ_cd_V4_two.mono
    intro w hw
    refine ⟨?_, ?_⟩
    · exact (Metric.ball_subset_ball hρ_le_ρ_V4) hw.1
    · refine ⟨?_, ?_⟩
      · linarith [hw.2.1]
      · linarith [hw.2.2]
  have hΦ_init_v : ∀ v ∈ Metric.ball (0 : E) ρ,
      Φ (((x₀, v) : E × E), 0) = ((x₀, v) : E × E) := by
    intro v hv
    have hr_nn : (0 : ℝ) ≤ (r : ℝ) := r.coe_nonneg
    have hv_in : ((x₀, v) : E × E) ∈
        Metric.closedBall ((x₀, (0 : E)) : E × E) (r : ℝ) := by
      rw [Metric.mem_closedBall, Prod.dist_eq]
      simp only [dist_self, dist_zero_right]
      rw [Metric.mem_ball, dist_zero_right] at hv
      have hv_r : ‖v‖ ≤ (r : ℝ) := le_of_lt (lt_of_lt_of_le hv hρ_le_r)
      exact max_le hr_nn hv_r
    exact hΦ_ILF.apply_initial ((x₀, v) : E × E) hv_in
  have h_inner_T : ∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Icc (-T) T,
      Φ (((x₀, v) : E × E), s) ∈
        Metric.ball (((x₀, (0 : E)) : E × E)) b.rIn := by
    intro v hv s hs
    have hv_ρ₀ : v ∈ Metric.ball (0 : E) ρ₀ := by
      rw [Metric.mem_ball, dist_zero_right] at hv ⊢
      have : ‖v‖ < ρ := hv
      exact lt_of_lt_of_le this hρ_le_ρ₀
    have hs_T₀ : s ∈ Set.Icc (-T₀) T₀ := by
      refine ⟨?_, ?_⟩
      · linarith [hs.1]
      · linarith [hs.2]
    exact h_orbit_in v hv_ρ₀ s hs_T₀
  have hΦ_target : ∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Icc (-T) T,
      Φ (((x₀, v) : E × E), s) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
    intro v hv s hs
    have h_in_ball := h_inner_T v hv s hs
    have h_in_closed : Φ (((x₀, v) : E × E), s) ∈
        Metric.closedBall ((x₀, (0 : E)) : E × E) b.rIn :=
      Metric.ball_subset_closedBall h_in_ball
    have h_inner_le_outer : b.rIn ≤ b.rOut := le_of_lt b.rIn_lt_rOut
    have h_in_outer : Φ (((x₀, v) : E × E), s) ∈
        Metric.closedBall ((x₀, (0 : E)) : E × E) b.rOut :=
      Metric.closedBall_subset_closedBall h_inner_le_outer h_in_closed
    exact hb_sub h_in_outer
  have hΦ_phase : ∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Ioo (-T) T,
      HasDerivAt (fun s' : ℝ => Φ (((x₀, v) : E × E), s'))
        (chartPhaseVF (I := I) g p (Φ (((x₀, v) : E × E), s))) s := by
    intro v hv s hs
    exact orbit_hasDerivAt_chartPhaseVF_uniform
      (I := I) (g := g) (p := p) (x₀ := x₀) hx₀_def
      (b := b) (r := r) (ε := ε) hr hε
      (Φ := Φ) hΦ_ILF hb_sub
      (ρ := ρ) (T := T) hρ_pos hT_pos hT_lt_ε hρ_le_r h_inner_T v hv s hs
  have hconst_ev : ∀ᶠ s in 𝓝 (0 : ℝ),
      Φ (((x₀, (0 : E)) : E × E), s) = ((x₀, (0 : E)) : E × E) := by
    change ∀ᶠ s in 𝓝 (0 : ℝ),
      Φ (((extChartAt I p p, (0 : E)) : E × E), s) =
        ((extChartAt I p p, (0 : E)) : E × E)
    exact chartFlow_zero_section_eventually_const (I := I) (g := g) (p := p)
      (Φ := Φ) (b := b) (r := r) (ε := ε) hΦ_ILF hb_sub hr hε
  rcases Filter.eventually_iff_exists_mem.mp hconst_ev with ⟨U, hU_nhds, hU⟩
  rcases _root_.mem_nhds_iff.mp hU_nhds with ⟨V, hVU, hV_open, hV_mem_zero⟩
  rcases (Metric.isOpen_iff.mp hV_open) (0 : ℝ) hV_mem_zero with
    ⟨δ_match, hδ_match_pos, hδ_sub⟩
  set T_match : ℝ := min δ_match T with hT_match_def
  have hT_match_pos : 0 < T_match := lt_min hδ_match_pos hT_pos
  have hT_match_le_T : T_match ≤ T := min_le_right _ _
  have hT_match_le_δ : T_match ≤ δ_match := min_le_left _ _
  have hΦ_const_zero_section :
      ∀ s ∈ Set.Ioo (-T_match) T_match,
        Φ (((x₀, (0 : E)) : E × E), s) = ((x₀, (0 : E)) : E × E) := by
    intro s hs
    have hs_in_V : s ∈ V := by
      apply hδ_sub
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      refine ⟨?_, ?_⟩
      · have h1 : -T_match < s := hs.1
        linarith
      · have h2 : s < T_match := hs.2
        linarith
    exact hU _ (hVU hs_in_V)
  have hF_int : ∀ v ∈ Metric.ball (0 : E) ρ,
      IsMIntegralCurveOn (chartFlowOrbitLift (I := I) Φ p v)
        (geodesicVectorFieldChart (I := I) g p) (Set.Ioo (-T) T) := by
    intro v hv
    exact chartFlowOrbitLift_isMIntegralCurveOn_Ioo (I := I) g p v
      (hΦ_target v hv) (hΦ_phase v hv)
  refine ⟨Φ, ρ, T, T_match, hρ_pos, hT_pos, hT_match_pos, hT_match_le_T, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ContDiffOn ℝ 2 Φ
      ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ Set.Ioo (-T) T)
    exact hΦ_cd
  · change Φ (((extChartAt I p p, (0 : E)) : E × E), 0) =
      ((extChartAt I p p, (0 : E)) : E × E)
    exact hΦ_init0
  · intro v hv
    change Φ (((extChartAt I p p, v) : E × E), 0) =
      ((extChartAt I p p, v) : E × E)
    exact hΦ_init_v v hv
  · intro v hv s hs
    change Φ (((extChartAt I p p, v) : E × E), s) ∈
      (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)
    exact hΦ_target v hv s hs
  · intro v hv s hs
    change HasDerivAt (fun s' : ℝ => Φ (((extChartAt I p p, v) : E × E), s'))
      (chartPhaseVF (I := I) g p
        (Φ (((extChartAt I p p, v) : E × E), s))) s
    exact hΦ_phase v hv s hs
  · intro s hs
    change Φ (((extChartAt I p p, (0 : E)) : E × E), s) =
      ((extChartAt I p p, (0 : E)) : E × E)
    exact hΦ_const_zero_section s hs
  · intro v hv
    exact hF_int v hv

/-- **Small-vector off-zero `C²`.** There is a radius `δ > 0` such that
`w ↦ expMap g p w` is `ContMDiffAt 𝓘(ℝ, E) I 2` at every `w` with
`‖w‖ < δ`.

This is the `C^2` strengthening of `expMap_contMDiffAt_of_norm_lt`,
obtained by reusing the unified `C^2` chart-flow packaging
(`exists_unified_chartFlow_data_two`), the `C^2` candidate slice
smoothness (`chartFlowCandidate_contMDiffAt2_of_mem_ball`), and the same
M2 rescaled-lift identification at `s = 1`
(`chartFlowOrbitLiftRescaled_proj_at_one`) used by the `C^1` version,
then transferring through the smooth rescaling `w ↦ (1 / t') • w`.  It is
the off-zero ingredient consumed by the Gauss lemma. -/
theorem expMap_contMDiffAt2_of_norm_lt
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : E, ‖w‖ < δ →
      ContMDiffAt 𝓘(ℝ, E) I 2
        (fun u : E => (expMap (I := I) g p (show TangentSpace I p from u) : M))
        w := by
  classical
  obtain ⟨Φ, ρ, T, T_match, hρ_pos, hT_pos, hT_match_pos, hT_match_le_T,
    hΦ_cd, hΦ_init0, hΦ_init_v, hΦ_target, hΦ_phase, hΦ_const_zero, _hF_int⟩ :=
    exists_unified_chartFlow_data_two (I := I) g p
  set t' : ℝ := T_match / 2 with ht'_def
  have ht'_pos : 0 < t' := by rw [ht'_def]; exact half_pos hT_match_pos
  have ht'_lt_T_match : t' < T_match := by
    rw [ht'_def]; exact half_lt_self hT_match_pos
  have ht'_lt_T : t' < T := lt_of_lt_of_le ht'_lt_T_match hT_match_le_T
  have ht'_in_Ioo : t' ∈ Set.Ioo (-T) T := ⟨by linarith, ht'_lt_T⟩
  have ht'_ne : t' ≠ 0 := ne_of_gt ht'_pos
  set x₀ : E := extChartAt I p p with hx₀_def
  have hmatch : ∀ v : E, v ∈ Metric.ball (0 : E) ρ →
      (expMap (I := I) g p (show TangentSpace I p from (t' • v)) : M) =
        chartFlowCandidate (I := I) Φ p t' v := by
    intro v hv_ball
    have hΦ_init_v_at : Φ (((x₀, v) : E × E), 0) = ((x₀, v) : E × E) :=
      hΦ_init_v v hv_ball
    have hΦ_target_v : ∀ s ∈ Set.Icc (-T) T,
        Φ (((x₀, v) : E × E), s) ∈
          (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
      intro s hs; exact hΦ_target v hv_ball s hs
    have hΦ_phase_v : ∀ s ∈ Set.Ioo (-T) T,
        HasDerivAt (fun s' : ℝ => Φ (((x₀, v) : E × E), s'))
          (chartPhaseVF (I := I) g p (Φ (((x₀, v) : E × E), s))) s := by
      intro s hs; exact hΦ_phase v hv_ball s hs
    have hproj1 :=
      chartFlowOrbitLiftRescaled_proj_at_one (I := I) (g := g) (p := p) (v := v)
        (T := T) (t' := t') ht'_pos ht'_lt_T (Φ := Φ)
        hΦ_init_v_at hΦ_target_v hΦ_phase_v
    have hΦ_target_t' : Φ (((x₀, v) : E × E), t' * 1) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
      rw [mul_one]
      exact hΦ_target_v t' (Set.Ioo_subset_Icc_self ht'_in_Ioo)
    have hproj_def :=
      chartFlowOrbitLiftRescaled_proj (I := I) (p := p) (v := v) (t' := t')
        (Φ := Φ) (s := 1) hΦ_target_t'
    have hcand_unfold : chartFlowCandidate (I := I) Φ p t' v =
        (extChartAt I p).symm (Φ (((x₀, v) : E × E), t')).1 := rfl
    have hproj_def' :
        (chartFlowOrbitLiftRescaled (I := I) Φ p t' v 1).proj =
          (extChartAt I p).symm (Φ (((x₀, v) : E × E), t')).1 := by
      rw [hproj_def, mul_one]
    rw [← hproj1, hproj_def', ← hcand_unfold]
  refine ⟨t' * ρ, by positivity, ?_⟩
  intro w hw
  set v₁ : E := (1 / t') • w with hv₁_def
  have hv₁_norm : ‖v₁‖ < ρ := by
    rw [hv₁_def, norm_smul]
    have h1t' : ‖(1 / t' : ℝ)‖ = 1 / t' := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [h1t']
    rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ ht'_pos]
    calc ‖w‖ < t' * ρ := hw
      _ = ρ * t' := by ring
  have hv₁_ball : v₁ ∈ Metric.ball (0 : E) ρ := by
    rw [Metric.mem_ball, dist_zero_right]; exact hv₁_norm
  have htv₁_eq_w : t' • v₁ = w := by
    rw [hv₁_def, smul_smul, mul_one_div, div_self ht'_ne, one_smul]
  have hval_int : (Φ (((x₀, v₁) : E × E), t')).1 ∈
      interior (extChartAt I p).target := by
    have := hΦ_target v₁ hv₁_ball t' (Set.Ioo_subset_Icc_self ht'_in_Ioo)
    exact this.1
  have hcand_cd : ContMDiffAt 𝓘(ℝ, E) I 2
      (chartFlowCandidate (I := I) Φ p t') v₁ :=
    chartFlowCandidate_contMDiffAt2_of_mem_ball (I := I) (p := p) (Φ := Φ)
      (ρ := ρ) (T := T) (t' := t') (v₁ := v₁) hv₁_norm ht'_in_Ioo hΦ_cd hval_int
  have hsmul_cd : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 2 (fun u : E => (1 / t') • u) := by
    have h0 : ContDiff ℝ (∞ : WithTop ℕ∞) (fun u : E => (1 / t') • u) :=
      contDiff_const.smul contDiff_id
    have hle : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
      have h2le : ((2 : ℕ∞) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) :=
        by exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
      simpa using h2le
    have h1 : ContDiff ℝ 2 (fun u : E => (1 / t') • u) := h0.of_le hle
    exact h1.contMDiff
  have hsmul_at : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 2
      (fun u : E => (1 / t') • u) w := hsmul_cd.contMDiffAt
  have hsmul_w_eq : (fun u : E => (1 / t') • u) w = v₁ := by
    rw [hv₁_def]
  have hcand_cd' : ContMDiffAt 𝓘(ℝ, E) I 2
      (chartFlowCandidate (I := I) Φ p t')
      ((fun u : E => (1 / t') • u) w) := by
    rw [hsmul_w_eq]; exact hcand_cd
  have hcomp : ContMDiffAt 𝓘(ℝ, E) I 2
      ((chartFlowCandidate (I := I) Φ p t') ∘ (fun u : E => (1 / t') • u)) w :=
    hcand_cd'.comp w hsmul_at
  have hev :
      (fun u : E => (expMap (I := I) g p (show TangentSpace I p from u) : M))
        =ᶠ[𝓝 w]
      ((chartFlowCandidate (I := I) Φ p t') ∘ (fun u : E => (1 / t') • u)) := by
    have hsmul_cont : Continuous (fun u : E => (1 / t') • u) :=
      continuous_const.smul continuous_id
    have hpre : (fun u : E => (1 / t') • u) ⁻¹' Metric.ball (0 : E) ρ ∈ 𝓝 w := by
      have hnhd : Metric.ball (0 : E) ρ ∈ 𝓝 ((fun u : E => (1 / t') • u) w) := by
        rw [hsmul_w_eq]; exact Metric.isOpen_ball.mem_nhds hv₁_ball
      exact hsmul_cont.continuousAt.preimage_mem_nhds hnhd
    filter_upwards [hpre] with u hu
    have hheq := hmatch ((1 / t') • u) hu
    have htu_eq : t' • ((1 / t') • u) = u := by
      rw [smul_smul, mul_one_div, div_self ht'_ne, one_smul]
    rw [htu_eq] at hheq
    change (expMap (I := I) g p (show TangentSpace I p from u) : M) = _
    simp only [Function.comp_apply]
    exact hheq
  exact hcomp.congr_of_eventuallyEq hev

/-- **Unified `C^n` chart-flow packaging (every finite order `n ≥ 1`).**
The finite-order analogue of `exists_unified_chartFlow_data`: a single
chart-pushed flow `Φ : (E × E) × ℝ → E × E` together with uniform radii
`(ρ, T, T_match)` supplying joint `ContDiffOn ℝ n` regularity on
`ball ((x₀, 0)) ρ × Ioo (-T) T` and the same family of order-agnostic
properties (initial conditions, chart-target confinement, the genuine
chart-phase ODE, and the manifold-lift integral-curve property) as the
`C^1` / `C^2` packagings.  Here `x₀ := extChartAt I p p`. -/
private theorem exists_unified_chartFlow_data_nat
    (g : SmoothRiemannianMetric I M) (p : M) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (Φ : (E × E) × ℝ → E × E) (ρ T T_match : ℝ),
      0 < ρ ∧ 0 < T ∧ 0 < T_match ∧ T_match ≤ T ∧
      ContDiffOn ℝ (n : ℕ∞) Φ
        ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ
          Set.Ioo (-T) T) ∧
      Φ (((extChartAt I p p, (0 : E)) : E × E), 0) =
        ((extChartAt I p p, (0 : E)) : E × E) ∧
      (∀ v ∈ Metric.ball (0 : E) ρ,
        Φ (((extChartAt I p p, v) : E × E), 0) =
          ((extChartAt I p p, v) : E × E)) ∧
      (∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Icc (-T) T,
        Φ (((extChartAt I p p, v) : E × E), s) ∈
          (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)) ∧
      (∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Ioo (-T) T,
        HasDerivAt (fun s' : ℝ => Φ (((extChartAt I p p, v) : E × E), s'))
          (chartPhaseVF (I := I) g p
            (Φ (((extChartAt I p p, v) : E × E), s))) s) ∧
      (∀ s ∈ Set.Ioo (-T_match) T_match,
        Φ (((extChartAt I p p, (0 : E)) : E × E), s) =
          ((extChartAt I p p, (0 : E)) : E × E)) ∧
      (∀ v ∈ Metric.ball (0 : E) ρ,
        IsMIntegralCurveOn (chartFlowOrbitLift (I := I) Φ p v)
          (geodesicVectorFieldChart (I := I) g p) (Set.Ioo (-T) T)) := by
  classical
  set x₀ : E := extChartAt I p p with hx₀_def
  have hx₀_src : p ∈ (extChartAt I p).source :=
    mem_extChartAt_source (I := I) p
  have hx₀_target : x₀ ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source hx₀_src
  have hx₀_interior : x₀ ∈ interior (extChartAt I p).target :=
    DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) p hx₀_target
  obtain ⟨b, r, ε, ρ_V4, T_V4, Φ, hr, hε, hρ_V4_pos, hT_V4_pos, hb_sub, hΦ_ILF,
    hΦ_cd_V4_n, hΦ_init0⟩ :=
    Geodesic.exists_chartPhase_contDiffOn_isLocalFlow_combined_nat
      (I := I) (g := g) (α := p) (x₀ := x₀) (v₀ := (0 : E)) n hn hx₀_interior
  have hΦ_cd_V4 : ContDiffOn ℝ 1 Φ
      ((Metric.ball ((x₀, (0 : E)) : E × E) ρ_V4) ×ˢ Set.Ioo (-T_V4) T_V4) := by
    apply hΦ_cd_V4_n.of_le
    have h1le : (1 : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast hn
    exact_mod_cast h1le
  obtain ⟨ρ₀, T₀, hρ₀_pos, hT₀_pos, hρ₀_le_V4, hT₀_lt_V4, h_orbit_in⟩ :=
    exists_uniform_orbit_in_inner_ball (I := I) (g := g) (p := p)
      (x₀ := x₀) hx₀_def
      (b := b) (ρ_V4 := ρ_V4) (T_V4 := T_V4) hρ_V4_pos hT_V4_pos
      (Φ := Φ) hΦ_cd_V4 hΦ_init0
  set ρ : ℝ := min ρ₀ ((r : ℝ) / 2) with hρ_def
  have hρ_pos : 0 < ρ := by
    apply lt_min hρ₀_pos
    have : (0 : ℝ) < (r : ℝ) := hr
    linarith
  have hρ_le_ρ₀ : ρ ≤ ρ₀ := min_le_left _ _
  have hρ_le_ρ_V4 : ρ ≤ ρ_V4 := le_trans hρ_le_ρ₀ hρ₀_le_V4
  have hρ_le_r : ρ ≤ (r : ℝ) := by
    rw [hρ_def]
    have h1 : min ρ₀ ((r : ℝ) / 2) ≤ (r : ℝ) / 2 := min_le_right _ _
    have h2 : (r : ℝ) / 2 ≤ (r : ℝ) := by
      have hrnn : (0 : ℝ) ≤ (r : ℝ) := r.coe_nonneg
      linarith
    linarith
  set T : ℝ := min T₀ (ε / 2) with hT_def
  have hT_pos : 0 < T :=
    lt_min hT₀_pos (by linarith)
  have hT_le_T₀ : T ≤ T₀ := min_le_left _ _
  have hT_lt_ε : T < ε := by
    have h1 : min T₀ (ε / 2) ≤ ε / 2 := min_le_right _ _
    have : T = min T₀ (ε / 2) := hT_def
    rw [this]; linarith
  have hT_lt_T_V4 : T < T_V4 := lt_of_le_of_lt hT_le_T₀ hT₀_lt_V4
  have hΦ_cd : ContDiffOn ℝ (n : ℕ∞) Φ
      ((Metric.ball ((x₀, (0 : E)) : E × E) ρ) ×ˢ Set.Ioo (-T) T) := by
    apply hΦ_cd_V4_n.mono
    intro w hw
    refine ⟨?_, ?_⟩
    · exact (Metric.ball_subset_ball hρ_le_ρ_V4) hw.1
    · refine ⟨?_, ?_⟩
      · linarith [hw.2.1]
      · linarith [hw.2.2]
  have hΦ_init_v : ∀ v ∈ Metric.ball (0 : E) ρ,
      Φ (((x₀, v) : E × E), 0) = ((x₀, v) : E × E) := by
    intro v hv
    have hr_nn : (0 : ℝ) ≤ (r : ℝ) := r.coe_nonneg
    have hv_in : ((x₀, v) : E × E) ∈
        Metric.closedBall ((x₀, (0 : E)) : E × E) (r : ℝ) := by
      rw [Metric.mem_closedBall, Prod.dist_eq]
      simp only [dist_self, dist_zero_right]
      rw [Metric.mem_ball, dist_zero_right] at hv
      have hv_r : ‖v‖ ≤ (r : ℝ) := le_of_lt (lt_of_lt_of_le hv hρ_le_r)
      exact max_le hr_nn hv_r
    exact hΦ_ILF.apply_initial ((x₀, v) : E × E) hv_in
  have h_inner_T : ∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Icc (-T) T,
      Φ (((x₀, v) : E × E), s) ∈
        Metric.ball (((x₀, (0 : E)) : E × E)) b.rIn := by
    intro v hv s hs
    have hv_ρ₀ : v ∈ Metric.ball (0 : E) ρ₀ := by
      rw [Metric.mem_ball, dist_zero_right] at hv ⊢
      have : ‖v‖ < ρ := hv
      exact lt_of_lt_of_le this hρ_le_ρ₀
    have hs_T₀ : s ∈ Set.Icc (-T₀) T₀ := by
      refine ⟨?_, ?_⟩
      · linarith [hs.1]
      · linarith [hs.2]
    exact h_orbit_in v hv_ρ₀ s hs_T₀
  have hΦ_target : ∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Icc (-T) T,
      Φ (((x₀, v) : E × E), s) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
    intro v hv s hs
    have h_in_ball := h_inner_T v hv s hs
    have h_in_closed : Φ (((x₀, v) : E × E), s) ∈
        Metric.closedBall ((x₀, (0 : E)) : E × E) b.rIn :=
      Metric.ball_subset_closedBall h_in_ball
    have h_inner_le_outer : b.rIn ≤ b.rOut := le_of_lt b.rIn_lt_rOut
    have h_in_outer : Φ (((x₀, v) : E × E), s) ∈
        Metric.closedBall ((x₀, (0 : E)) : E × E) b.rOut :=
      Metric.closedBall_subset_closedBall h_inner_le_outer h_in_closed
    exact hb_sub h_in_outer
  have hΦ_phase : ∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Ioo (-T) T,
      HasDerivAt (fun s' : ℝ => Φ (((x₀, v) : E × E), s'))
        (chartPhaseVF (I := I) g p (Φ (((x₀, v) : E × E), s))) s := by
    intro v hv s hs
    exact orbit_hasDerivAt_chartPhaseVF_uniform
      (I := I) (g := g) (p := p) (x₀ := x₀) hx₀_def
      (b := b) (r := r) (ε := ε) hr hε
      (Φ := Φ) hΦ_ILF hb_sub
      (ρ := ρ) (T := T) hρ_pos hT_pos hT_lt_ε hρ_le_r h_inner_T v hv s hs
  have hconst_ev : ∀ᶠ s in 𝓝 (0 : ℝ),
      Φ (((x₀, (0 : E)) : E × E), s) = ((x₀, (0 : E)) : E × E) := by
    change ∀ᶠ s in 𝓝 (0 : ℝ),
      Φ (((extChartAt I p p, (0 : E)) : E × E), s) =
        ((extChartAt I p p, (0 : E)) : E × E)
    exact chartFlow_zero_section_eventually_const (I := I) (g := g) (p := p)
      (Φ := Φ) (b := b) (r := r) (ε := ε) hΦ_ILF hb_sub hr hε
  rcases Filter.eventually_iff_exists_mem.mp hconst_ev with ⟨U, hU_nhds, hU⟩
  rcases _root_.mem_nhds_iff.mp hU_nhds with ⟨V, hVU, hV_open, hV_mem_zero⟩
  rcases (Metric.isOpen_iff.mp hV_open) (0 : ℝ) hV_mem_zero with
    ⟨δ_match, hδ_match_pos, hδ_sub⟩
  set T_match : ℝ := min δ_match T with hT_match_def
  have hT_match_pos : 0 < T_match := lt_min hδ_match_pos hT_pos
  have hT_match_le_T : T_match ≤ T := min_le_right _ _
  have hT_match_le_δ : T_match ≤ δ_match := min_le_left _ _
  have hΦ_const_zero_section :
      ∀ s ∈ Set.Ioo (-T_match) T_match,
        Φ (((x₀, (0 : E)) : E × E), s) = ((x₀, (0 : E)) : E × E) := by
    intro s hs
    have hs_in_V : s ∈ V := by
      apply hδ_sub
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      refine ⟨?_, ?_⟩
      · have h1 : -T_match < s := hs.1
        linarith
      · have h2 : s < T_match := hs.2
        linarith
    exact hU _ (hVU hs_in_V)
  have hF_int : ∀ v ∈ Metric.ball (0 : E) ρ,
      IsMIntegralCurveOn (chartFlowOrbitLift (I := I) Φ p v)
        (geodesicVectorFieldChart (I := I) g p) (Set.Ioo (-T) T) := by
    intro v hv
    exact chartFlowOrbitLift_isMIntegralCurveOn_Ioo (I := I) g p v
      (hΦ_target v hv) (hΦ_phase v hv)
  refine ⟨Φ, ρ, T, T_match, hρ_pos, hT_pos, hT_match_pos, hT_match_le_T, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ContDiffOn ℝ (n : ℕ∞) Φ
      ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ Set.Ioo (-T) T)
    exact hΦ_cd
  · change Φ (((extChartAt I p p, (0 : E)) : E × E), 0) =
      ((extChartAt I p p, (0 : E)) : E × E)
    exact hΦ_init0
  · intro v hv
    change Φ (((extChartAt I p p, v) : E × E), 0) =
      ((extChartAt I p p, v) : E × E)
    exact hΦ_init_v v hv
  · intro v hv s hs
    change Φ (((extChartAt I p p, v) : E × E), s) ∈
      (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)
    exact hΦ_target v hv s hs
  · intro v hv s hs
    change HasDerivAt (fun s' : ℝ => Φ (((extChartAt I p p, v) : E × E), s'))
      (chartPhaseVF (I := I) g p
        (Φ (((extChartAt I p p, v) : E × E), s))) s
    exact hΦ_phase v hv s hs
  · intro s hs
    change Φ (((extChartAt I p p, (0 : E)) : E × E), s) =
      ((extChartAt I p p, (0 : E)) : E × E)
    exact hΦ_const_zero_section s hs
  · intro v hv
    exact hF_int v hv

/-- **Small-vector off-zero `C^n` (every finite order `n ≥ 1`).** There
is a radius `δ > 0` such that
`w ↦ expMap g p w` is `ContMDiffAt 𝓘(ℝ, E) I n` at every `w` with
`‖w‖ < δ`.

This is the finite-order strengthening of `expMap_contMDiffAt2_of_norm_lt`,
obtained by reusing the unified `C^n` chart-flow packaging
(`exists_unified_chartFlow_data_nat`), the `C^n` candidate slice
smoothness (`chartFlowCandidate_contMDiffAt_nat_of_mem_ball`), and the
same M2 rescaled-lift identification at `s = 1`
(`chartFlowOrbitLiftRescaled_proj_at_one`) used by the `C^1` / `C^2`
versions, then transferring through the smooth rescaling `w ↦ (1 / t') • w`.
Since `n` is arbitrary, this is the effective `C^∞` smoothness of the
exponential map at small vectors (fixed basepoint). -/
theorem expMap_contMDiffAtN_of_norm_lt
    (g : SmoothRiemannianMetric I M) (p : M) (n : ℕ) (hn : 1 ≤ n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : E, ‖w‖ < δ →
      ContMDiffAt 𝓘(ℝ, E) I ((n : ℕ∞) : WithTop ℕ∞)
        (fun u : E => (expMap (I := I) g p (show TangentSpace I p from u) : M))
        w := by
  classical
  obtain ⟨Φ, ρ, T, T_match, hρ_pos, hT_pos, hT_match_pos, hT_match_le_T,
    hΦ_cd, hΦ_init0, hΦ_init_v, hΦ_target, hΦ_phase, hΦ_const_zero, _hF_int⟩ :=
    exists_unified_chartFlow_data_nat (I := I) g p n hn
  set t' : ℝ := T_match / 2 with ht'_def
  have ht'_pos : 0 < t' := by rw [ht'_def]; exact half_pos hT_match_pos
  have ht'_lt_T_match : t' < T_match := by
    rw [ht'_def]; exact half_lt_self hT_match_pos
  have ht'_lt_T : t' < T := lt_of_lt_of_le ht'_lt_T_match hT_match_le_T
  have ht'_in_Ioo : t' ∈ Set.Ioo (-T) T := ⟨by linarith, ht'_lt_T⟩
  have ht'_ne : t' ≠ 0 := ne_of_gt ht'_pos
  set x₀ : E := extChartAt I p p with hx₀_def
  have hmatch : ∀ v : E, v ∈ Metric.ball (0 : E) ρ →
      (expMap (I := I) g p (show TangentSpace I p from (t' • v)) : M) =
        chartFlowCandidate (I := I) Φ p t' v := by
    intro v hv_ball
    have hΦ_init_v_at : Φ (((x₀, v) : E × E), 0) = ((x₀, v) : E × E) :=
      hΦ_init_v v hv_ball
    have hΦ_target_v : ∀ s ∈ Set.Icc (-T) T,
        Φ (((x₀, v) : E × E), s) ∈
          (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
      intro s hs; exact hΦ_target v hv_ball s hs
    have hΦ_phase_v : ∀ s ∈ Set.Ioo (-T) T,
        HasDerivAt (fun s' : ℝ => Φ (((x₀, v) : E × E), s'))
          (chartPhaseVF (I := I) g p (Φ (((x₀, v) : E × E), s))) s := by
      intro s hs; exact hΦ_phase v hv_ball s hs
    have hproj1 :=
      chartFlowOrbitLiftRescaled_proj_at_one (I := I) (g := g) (p := p) (v := v)
        (T := T) (t' := t') ht'_pos ht'_lt_T (Φ := Φ)
        hΦ_init_v_at hΦ_target_v hΦ_phase_v
    have hΦ_target_t' : Φ (((x₀, v) : E × E), t' * 1) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
      rw [mul_one]
      exact hΦ_target_v t' (Set.Ioo_subset_Icc_self ht'_in_Ioo)
    have hproj_def :=
      chartFlowOrbitLiftRescaled_proj (I := I) (p := p) (v := v) (t' := t')
        (Φ := Φ) (s := 1) hΦ_target_t'
    have hcand_unfold : chartFlowCandidate (I := I) Φ p t' v =
        (extChartAt I p).symm (Φ (((x₀, v) : E × E), t')).1 := rfl
    have hproj_def' :
        (chartFlowOrbitLiftRescaled (I := I) Φ p t' v 1).proj =
          (extChartAt I p).symm (Φ (((x₀, v) : E × E), t')).1 := by
      rw [hproj_def, mul_one]
    rw [← hproj1, hproj_def', ← hcand_unfold]
  refine ⟨t' * ρ, by positivity, ?_⟩
  intro w hw
  set v₁ : E := (1 / t') • w with hv₁_def
  have hv₁_norm : ‖v₁‖ < ρ := by
    rw [hv₁_def, norm_smul]
    have h1t' : ‖(1 / t' : ℝ)‖ = 1 / t' := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [h1t']
    rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ ht'_pos]
    calc ‖w‖ < t' * ρ := hw
      _ = ρ * t' := by ring
  have hv₁_ball : v₁ ∈ Metric.ball (0 : E) ρ := by
    rw [Metric.mem_ball, dist_zero_right]; exact hv₁_norm
  have htv₁_eq_w : t' • v₁ = w := by
    rw [hv₁_def, smul_smul, mul_one_div, div_self ht'_ne, one_smul]
  have hval_int : (Φ (((x₀, v₁) : E × E), t')).1 ∈
      interior (extChartAt I p).target := by
    have := hΦ_target v₁ hv₁_ball t' (Set.Ioo_subset_Icc_self ht'_in_Ioo)
    exact this.1
  have hcand_cd : ContMDiffAt 𝓘(ℝ, E) I ((n : ℕ∞) : WithTop ℕ∞)
      (chartFlowCandidate (I := I) Φ p t') v₁ :=
    chartFlowCandidate_contMDiffAt_nat_of_mem_ball (I := I) (p := p) (Φ := Φ)
      (ρ := ρ) (T := T) (t' := t') (v₁ := v₁) n hv₁_norm ht'_in_Ioo hΦ_cd hval_int
  have hsmul_cd : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ((n : ℕ∞) : WithTop ℕ∞)
      (fun u : E => (1 / t') • u) := by
    have h0 : ContDiff ℝ (∞ : WithTop ℕ∞) (fun u : E => (1 / t') • u) :=
      contDiff_const.smul contDiff_id
    have hle : ((n : ℕ∞) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
      have hnle : ((n : ℕ∞) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
        have : (n : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
        exact_mod_cast this
      exact hnle
    have h1 : ContDiff ℝ ((n : ℕ∞) : WithTop ℕ∞)
        (fun u : E => (1 / t') • u) := h0.of_le hle
    exact h1.contMDiff
  have hsmul_at : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ((n : ℕ∞) : WithTop ℕ∞)
      (fun u : E => (1 / t') • u) w := hsmul_cd.contMDiffAt
  have hsmul_w_eq : (fun u : E => (1 / t') • u) w = v₁ := by
    rw [hv₁_def]
  have hcand_cd' : ContMDiffAt 𝓘(ℝ, E) I ((n : ℕ∞) : WithTop ℕ∞)
      (chartFlowCandidate (I := I) Φ p t')
      ((fun u : E => (1 / t') • u) w) := by
    rw [hsmul_w_eq]; exact hcand_cd
  have hcomp : ContMDiffAt 𝓘(ℝ, E) I ((n : ℕ∞) : WithTop ℕ∞)
      ((chartFlowCandidate (I := I) Φ p t') ∘ (fun u : E => (1 / t') • u)) w :=
    hcand_cd'.comp w hsmul_at
  have hev :
      (fun u : E => (expMap (I := I) g p (show TangentSpace I p from u) : M))
        =ᶠ[𝓝 w]
      ((chartFlowCandidate (I := I) Φ p t') ∘ (fun u : E => (1 / t') • u)) := by
    have hsmul_cont : Continuous (fun u : E => (1 / t') • u) :=
      continuous_const.smul continuous_id
    have hpre : (fun u : E => (1 / t') • u) ⁻¹' Metric.ball (0 : E) ρ ∈ 𝓝 w := by
      have hnhd : Metric.ball (0 : E) ρ ∈ 𝓝 ((fun u : E => (1 / t') • u) w) := by
        rw [hsmul_w_eq]; exact Metric.isOpen_ball.mem_nhds hv₁_ball
      exact hsmul_cont.continuousAt.preimage_mem_nhds hnhd
    filter_upwards [hpre] with u hu
    have hheq := hmatch ((1 / t') • u) hu
    have htu_eq : t' • ((1 / t') • u) = u := by
      rw [smul_smul, mul_one_div, div_self ht'_ne, one_smul]
    rw [htu_eq] at hheq
    change (expMap (I := I) g p (show TangentSpace I p from u) : M) = _
    simp only [Function.comp_apply]
    exact hheq
  exact hcomp.congr_of_eventuallyEq hev

section JointBasepointVector

variable [I.Boundaryless] [CompleteSpace E]

/-- **Joint slice `C^n` at a general phase-space point.** The genuine
*two-variable* analogue of `contDiffAt_chartFlow_slice_fst_of_mem_ball_nat`:
for a chart-flow `Φ` that is `ContDiffOn ℝ n` on the full phase-space
product `ball ((x₀, v₀), ρ) ×ˢ Ioo (-T) T`, the joint slice
`z ↦ (Φ(z, t')).1` (a map `E × E → E`, with `z = (chart-position,
velocity)`) is `ContDiffAt ℝ n` at every interior phase-point `z₁` of the
spatial ball.

Unlike the velocity-only slices, here **neither** component of `z` is
held fixed: this is exactly the joint dependence on (chart-position,
velocity) needed for the exponential to be smooth in both basepoint and
launch vector. -/
private lemma contDiffAt_chartFlow_jointSlice_fst_of_mem_ball_nat
    {Φ : (E × E) × ℝ → E × E} {z₀ : E × E} {ρ T t' : ℝ} {z₁ : E × E} (n : ℕ)
    (hz₁ : z₁ ∈ Metric.ball z₀ ρ) (ht' : t' ∈ Set.Ioo (-T) T)
    (hcd : ContDiffOn ℝ (n : ℕ∞) Φ
      ((Metric.ball z₀ ρ) ×ˢ Set.Ioo (-T) T)) :
    ContDiffAt ℝ (n : ℕ∞) (fun z : E × E => (Φ ((z, t') : (E × E) × ℝ)).1) z₁ := by
  classical
  have hpair_cd : ContDiff ℝ (n : ℕ∞) (fun z : E × E => ((z, t') : (E × E) × ℝ)) := by
    have h_id : ContDiff ℝ (n : ℕ∞) (fun z : E × E => z) := contDiff_id
    have h_const_t : ContDiff ℝ (n : ℕ∞) (fun _ : E × E => t') := contDiff_const
    exact h_id.prodMk h_const_t
  have hmem : ((z₁, t') : (E × E) × ℝ) ∈
      (Metric.ball z₀ ρ) ×ˢ Set.Ioo (-T) T := ⟨hz₁, ht'⟩
  have hopen : IsOpen ((Metric.ball z₀ ρ) ×ˢ Set.Ioo (-T) T) :=
    Metric.isOpen_ball.prod isOpen_Ioo
  have hΦ_cda : ContDiffAt ℝ (n : ℕ∞) Φ ((z₁, t') : (E × E) × ℝ) :=
    hcd.contDiffAt (hopen.mem_nhds hmem)
  have hslice : ContDiffAt ℝ (n : ℕ∞)
      (fun z : E × E => Φ ((z, t') : (E × E) × ℝ)) z₁ :=
    hΦ_cda.comp z₁ hpair_cd.contDiffAt
  have hfst : ContDiff ℝ (n : ℕ∞) (Prod.fst : E × E → E) := contDiff_fst
  exact hfst.contDiffAt.comp z₁ hslice

/-- **Joint slice `ContDiffOn n` on the whole phase ball.** The
`ContDiffOn` (whole-ball) packaging of
`contDiffAt_chartFlow_jointSlice_fst_of_mem_ball_nat`: the joint slice
`z ↦ (Φ(z, t')).1` is `ContDiffOn ℝ n` on `ball z₀ ρ`. -/
private lemma contDiffOn_chartFlow_jointSlice_fst_of_ball_nat
    {Φ : (E × E) × ℝ → E × E} {z₀ : E × E} {ρ T t' : ℝ} (n : ℕ)
    (ht' : t' ∈ Set.Ioo (-T) T)
    (hcd : ContDiffOn ℝ (n : ℕ∞) Φ
      ((Metric.ball z₀ ρ) ×ˢ Set.Ioo (-T) T)) :
    ContDiffOn ℝ (n : ℕ∞)
      (fun z : E × E => (Φ ((z, t') : (E × E) × ℝ)).1) (Metric.ball z₀ ρ) := by
  intro z₁ hz₁
  exact (contDiffAt_chartFlow_jointSlice_fst_of_mem_ball_nat
    (Φ := Φ) (z₀ := z₀) (ρ := ρ) (T := T) (t' := t') (z₁ := z₁) n
    hz₁ ht' hcd).contDiffWithinAt

/-- **Phase-ball inner-confinement.** The genuine *two-variable* analogue
of `exists_uniform_orbit_in_inner_ball`: from continuity of the joint-`C^1`
flow `Φ` at the base phase point `((x₀, 0), 0)` (where `Φ((x₀, 0), 0) =
(x₀, 0)`), there is a phase-ball radius `ρ` and a time radius `T` such
that every orbit starting at a phase point `z ∈ ball ((x₀, 0)) ρ` stays
in the inner ball `ball ((x₀, 0)) b.rIn` for `s ∈ Icc (-T) T`. Here the
**whole** phase point `z = (chart-position, velocity)` varies, not just
the velocity. -/
private lemma exists_phaseBall_orbit_in_inner_ball {x₀ : E}
    {b : ContDiffBump ((x₀, (0 : E)) : E × E)}
    {ρ_V T_V : ℝ} (hρ_V_pos : 0 < ρ_V) (hT_V_pos : 0 < T_V)
    {Φ : (E × E) × ℝ → E × E}
    (hΦ_cd : ContDiffOn ℝ 1 Φ
      ((Metric.ball ((x₀, (0 : E)) : E × E) ρ_V) ×ˢ Set.Ioo (-T_V) T_V))
    (hΦ_init0 : Φ (((x₀, (0 : E)) : E × E), 0) = (x₀, (0 : E))) :
    ∃ (ρ T : ℝ), 0 < ρ ∧ 0 < T ∧ ρ ≤ ρ_V ∧ T < T_V ∧
      ∀ z ∈ Metric.ball ((x₀, (0 : E)) : E × E) ρ, ∀ s ∈ Set.Icc (-T) T,
        Φ ((z, s) : (E × E) × ℝ) ∈
          Metric.ball ((x₀, (0 : E)) : E × E) b.rIn := by
  classical
  have h_open : IsOpen
      ((Metric.ball ((x₀, (0 : E)) : E × E) ρ_V) ×ˢ Set.Ioo (-T_V) T_V) :=
    Metric.isOpen_ball.prod isOpen_Ioo
  have hz₀_mem : (((x₀, (0 : E)) : E × E), (0 : ℝ)) ∈
      (Metric.ball ((x₀, (0 : E)) : E × E) ρ_V) ×ˢ Set.Ioo (-T_V) T_V :=
    ⟨Metric.mem_ball_self hρ_V_pos, ⟨by linarith, hT_V_pos⟩⟩
  have hΦ_cont : ContinuousAt Φ (((x₀, (0 : E)) : E × E), (0 : ℝ)) :=
    hΦ_cd.continuousOn.continuousAt (h_open.mem_nhds hz₀_mem)
  have h_preim : Φ ⁻¹' (Metric.ball ((x₀, (0 : E)) : E × E) b.rIn) ∈
      𝓝 (((x₀, (0 : E)) : E × E), (0 : ℝ)) := by
    apply hΦ_cont.preimage_mem_nhds
    rw [hΦ_init0]
    exact Metric.ball_mem_nhds _ b.rIn_pos
  obtain ⟨U, V, hU_open, hU_mem, hV_open, hV_mem, h_subset⟩ :=
    mem_nhds_prod_iff'.mp h_preim
  obtain ⟨ρ₁, hρ₁_pos, hρ₁_sub⟩ :=
    Metric.isOpen_iff.mp hU_open ((x₀, (0 : E)) : E × E) hU_mem
  obtain ⟨T₁, hT₁_pos, hT₁_sub⟩ :=
    Metric.isOpen_iff.mp hV_open (0 : ℝ) hV_mem
  have hT₁_Ioo : Set.Icc (-(min T₁ (T_V / 2) / 2)) (min T₁ (T_V / 2) / 2) ⊆ V := by
    intro s hs
    apply hT₁_sub
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    have hTmin_le : min T₁ (T_V / 2) / 2 < T₁ := by
      have h1 : min T₁ (T_V / 2) ≤ T₁ := min_le_left _ _
      have h2 : (0 : ℝ) < min T₁ (T_V / 2) := lt_min hT₁_pos (by linarith)
      have : min T₁ (T_V / 2) / 2 < min T₁ (T_V / 2) := by linarith
      linarith
    rw [abs_lt]
    refine ⟨by linarith [hs.1], by linarith [hs.2, hTmin_le]⟩
  refine ⟨min ρ₁ ρ_V / 2, min T₁ (T_V / 2) / 2, ?_, ?_, ?_, ?_, ?_⟩
  · have : (0 : ℝ) < min ρ₁ ρ_V := lt_min hρ₁_pos hρ_V_pos
    linarith
  · have : (0 : ℝ) < min T₁ (T_V / 2) := lt_min hT₁_pos (by linarith)
    linarith
  · have h1 : min ρ₁ ρ_V ≤ ρ_V := min_le_right _ _
    have h2 : (0 : ℝ) ≤ min ρ₁ ρ_V := le_of_lt (lt_min hρ₁_pos hρ_V_pos)
    linarith
  · have h1 : min T₁ (T_V / 2) ≤ T_V / 2 := min_le_right _ _
    have h2 : (0 : ℝ) ≤ min T₁ (T_V / 2) := le_of_lt (lt_min hT₁_pos (by linarith))
    linarith
  · intro z hz s hs
    have hz_U : z ∈ U := by
      apply hρ₁_sub
      have h1 : min ρ₁ ρ_V / 2 ≤ ρ₁ := by
        have h2 : min ρ₁ ρ_V ≤ ρ₁ := min_le_left _ _
        have h3 : (0 : ℝ) ≤ min ρ₁ ρ_V := le_of_lt (lt_min hρ₁_pos hρ_V_pos)
        linarith
      exact (Metric.ball_subset_ball h1) hz
    have hs_V : s ∈ V := hT₁_Ioo hs
    have hmem : ((z, s) : (E × E) × ℝ) ∈ U ×ˢ V := ⟨hz_U, hs_V⟩
    exact h_subset hmem

/-- **Chart-coordinate exponential, jointly in (chart-position, velocity).**
For a fixed chart center `α` and finite regularity order `n ≥ 1`, the
chart-coordinate exponential map
`(x, v) ↦ (Φ((x, v), t')).1` — the first component (the chart position of
the geodesic at the fixed time `t'`) of the combined chart-phase flow —
is jointly `ContDiffOn ℝ n` on a basic phase-ball
`ball ((x₀, 0)) ρ`, where `x₀ := extChartAt I α α`. Here both the
chart-position `x` and the velocity `v` vary jointly.

This is the **single-chart joint smoothness in basepoint AND launch
vector**, in chart coordinates. The flow `Φ` is the one produced by
`Geodesic.exists_chartPhase_contDiffOn_isLocalFlow_combined_nat`, and is
the genuine geodesic flow of the chart-coordinate phase-space vector
field `chartPhaseVF g α`: it satisfies the chart-phase ODE
`HasDerivAt (Φ((x, v), ·)) (chartPhaseVF g α (Φ((x, v), s))) s` on
`Ioo (-T) T` (clause `hΦ_phase`), with initial condition
`Φ((x, v), 0) = (x, v)` (clause `hΦ_init`), and stays in the chart-target
interior product (clause `hΦ_target`). At a basepoint `q` with
chart-position `x = extChartAt I α q` and a launch vector whose chart
coordinate is `v`, the chart position of the geodesic at time `t'` is
exactly `(Φ((x, v), t')).1`; this is the analytic content S5 lifts to the
manifold statement once the chart-independence of geodesics (the
moving-chart geodesic equation) supplies the basepoint-`≠`-`α`
identification of `Φ`'s base orbit with `maximalGeodesic g q`. -/
theorem exists_chartExp_jointContDiffOn_nat
    (g : SmoothRiemannianMetric I M) (α : M) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (Φ : (E × E) × ℝ → E × E) (ρ T t' : ℝ),
      0 < ρ ∧ 0 < T ∧ t' ∈ Set.Ioo (-T) T ∧ 0 < t' ∧
      ContDiffOn ℝ (n : ℕ∞)
        (fun z : E × E => (Φ ((z, t') : (E × E) × ℝ)).1)
        (Metric.ball ((extChartAt I α α, (0 : E)) : E × E) ρ) ∧
      (∀ z ∈ Metric.ball ((extChartAt I α α, (0 : E)) : E × E) ρ,
        Φ ((z, (0 : ℝ)) : (E × E) × ℝ) = z) ∧
      (∀ z ∈ Metric.ball ((extChartAt I α α, (0 : E)) : E × E) ρ,
        ∀ s ∈ Set.Ioo (-T) T,
        HasDerivAt (fun s' : ℝ => Φ ((z, s') : (E × E) × ℝ))
          (chartPhaseVF (I := I) g α (Φ ((z, s) : (E × E) × ℝ))) s) ∧
      (∀ z ∈ Metric.ball ((extChartAt I α α, (0 : E)) : E × E) ρ,
        ∀ s ∈ Set.Icc (-T) T,
        Φ ((z, s) : (E × E) × ℝ) ∈
          (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) ∧
      ContDiffOn ℝ (n : ℕ∞) Φ
        ((Metric.ball ((extChartAt I α α, (0 : E)) : E × E) ρ) ×ˢ Set.Ioo (-T) T) := by
  classical
  set x₀ : E := extChartAt I α α with hx₀_def
  have hx₀_src : α ∈ (extChartAt I α).source :=
    mem_extChartAt_source (I := I) α
  have hx₀_target : x₀ ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hx₀_src
  have hx₀_interior : x₀ ∈ interior (extChartAt I α).target :=
    DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) α hx₀_target
  obtain ⟨b, r, ε, ρ_V, T_V, Φ, hr, hε, hρ_V_pos, hT_V_pos, hb_sub, hΦ_ILF,
    hΦ_cd_V, hΦ_init0⟩ :=
    Geodesic.exists_chartPhase_contDiffOn_isLocalFlow_combined_nat
      (I := I) (g := g) (α := α) (x₀ := x₀) (v₀ := (0 : E)) n hn hx₀_interior
  have hΦ_cd_V1 : ContDiffOn ℝ 1 Φ
      ((Metric.ball ((x₀, (0 : E)) : E × E) ρ_V) ×ˢ Set.Ioo (-T_V) T_V) := by
    apply hΦ_cd_V.of_le
    have h1le : (1 : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast hn
    exact_mod_cast h1le
  obtain ⟨ρ₀, T₀, hρ₀_pos, hT₀_pos, hρ₀_le_V, hT₀_lt_V, h_orbit_in⟩ :=
    exists_phaseBall_orbit_in_inner_ball
      (x₀ := x₀)
      (b := b) (ρ_V := ρ_V) (T_V := T_V) hρ_V_pos hT_V_pos
      (Φ := Φ) hΦ_cd_V1 hΦ_init0
  set ρ : ℝ := min ρ₀ ((r : ℝ) / 2) with hρ_def
  have hρ_pos : 0 < ρ := by
    apply lt_min hρ₀_pos
    have : (0 : ℝ) < (r : ℝ) := hr
    linarith
  have hρ_le_ρ₀ : ρ ≤ ρ₀ := min_le_left _ _
  have hρ_le_ρ_V : ρ ≤ ρ_V := le_trans hρ_le_ρ₀ hρ₀_le_V
  have hρ_le_r : ρ ≤ (r : ℝ) := by
    rw [hρ_def]
    have h1 : min ρ₀ ((r : ℝ) / 2) ≤ (r : ℝ) / 2 := min_le_right _ _
    have h2 : (r : ℝ) / 2 ≤ (r : ℝ) := by
      have hrnn : (0 : ℝ) ≤ (r : ℝ) := r.coe_nonneg
      linarith
    linarith
  set T : ℝ := min T₀ (ε / 2) with hT_def
  have hT_pos : 0 < T := lt_min hT₀_pos (by linarith)
  have hT_le_T₀ : T ≤ T₀ := min_le_left _ _
  have hT_lt_T_V : T < T_V := lt_of_le_of_lt hT_le_T₀ hT₀_lt_V
  have hΦ_cd : ContDiffOn ℝ (n : ℕ∞) Φ
      ((Metric.ball ((x₀, (0 : E)) : E × E) ρ) ×ˢ Set.Ioo (-T) T) := by
    apply hΦ_cd_V.mono
    intro w hw
    refine ⟨?_, ?_⟩
    · exact (Metric.ball_subset_ball hρ_le_ρ_V) hw.1
    · refine ⟨?_, ?_⟩
      · linarith [hw.2.1]
      · linarith [hw.2.2]
  set t' : ℝ := T / 2 with ht'_def
  have ht'_pos : 0 < t' := by rw [ht'_def]; exact half_pos hT_pos
  have ht'_lt_T : t' < T := by rw [ht'_def]; exact half_lt_self hT_pos
  have ht'_in_Ioo : t' ∈ Set.Ioo (-T) T := ⟨by linarith, ht'_lt_T⟩
  have hjoint : ContDiffOn ℝ (n : ℕ∞)
      (fun z : E × E => (Φ ((z, t') : (E × E) × ℝ)).1)
      (Metric.ball ((x₀, (0 : E)) : E × E) ρ) :=
    contDiffOn_chartFlow_jointSlice_fst_of_ball_nat
      (Φ := Φ) (z₀ := ((x₀, (0 : E)) : E × E)) (ρ := ρ) (T := T) (t' := t') n
      ht'_in_Ioo hΦ_cd
  have hΦ_init_z : ∀ z ∈ Metric.ball ((x₀, (0 : E)) : E × E) ρ,
      Φ ((z, (0 : ℝ)) : (E × E) × ℝ) = z := by
    intro z hz
    have hz_cb : z ∈ Metric.closedBall ((x₀, (0 : E)) : E × E) (r : ℝ) := by
      have hball_sub : Metric.ball ((x₀, (0 : E)) : E × E) ρ ⊆
          Metric.closedBall ((x₀, (0 : E)) : E × E) (r : ℝ) := by
        intro w hw
        exact Metric.ball_subset_closedBall (Metric.ball_subset_ball hρ_le_r hw)
      exact hball_sub hz
    exact hΦ_ILF.apply_initial z hz_cb
  have h_inner_T : ∀ z ∈ Metric.ball ((x₀, (0 : E)) : E × E) ρ,
      ∀ s ∈ Set.Icc (-T) T,
      Φ ((z, s) : (E × E) × ℝ) ∈
        Metric.ball ((x₀, (0 : E)) : E × E) b.rIn := by
    intro z hz s hs
    have hz_ρ₀ : z ∈ Metric.ball ((x₀, (0 : E)) : E × E) ρ₀ :=
      (Metric.ball_subset_ball hρ_le_ρ₀) hz
    have hs_T₀ : s ∈ Set.Icc (-T₀) T₀ := by
      refine ⟨?_, ?_⟩
      · have : -T₀ ≤ -T := by simpa using hT_le_T₀
        linarith [hs.1]
      · linarith [hs.2, hT_le_T₀]
    exact h_orbit_in z hz_ρ₀ s hs_T₀
  have hT_lt_ε : T < ε := by
    have h1 : min T₀ (ε / 2) ≤ ε / 2 := min_le_right _ _
    have : T = min T₀ (ε / 2) := hT_def
    rw [this]; linarith
  have hΦ_phase_z : ∀ z ∈ Metric.ball ((x₀, (0 : E)) : E × E) ρ,
      ∀ s ∈ Set.Ioo (-T) T,
      HasDerivAt (fun s' : ℝ => Φ ((z, s') : (E × E) × ℝ))
        (chartPhaseVF (I := I) g α (Φ ((z, s) : (E × E) × ℝ))) s := by
    intro z hz s hs
    have hz_cb_r : z ∈ Metric.closedBall ((x₀, (0 : E)) : E × E) (r : ℝ) := by
      have : Metric.ball ((x₀, (0 : E)) : E × E) ρ ⊆
          Metric.closedBall ((x₀, (0 : E)) : E × E) (r : ℝ) := fun w hw =>
        Metric.ball_subset_closedBall (Metric.ball_subset_ball hρ_le_r hw)
      exact this hz
    have hs_Icc_ε : s ∈ Set.Icc (-ε) ε :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hs_Ioo_ε : s ∈ Set.Ioo (-ε) ε :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hs_Icc_T : s ∈ Set.Icc (-T) T := Set.Ioo_subset_Icc_self hs
    have hd_within := hΦ_ILF.hasDerivWithinAt z hz_cb_r s hs_Icc_ε
    have hVFTime_apply :
        chartPhaseVFTime (I := I) g α ((x₀, (0 : E)) : E × E) b s
          (Φ ((z, s) : (E × E) × ℝ)) =
        chartPhaseVFCutoff (I := I) g α ((x₀, (0 : E)) : E × E) b
          (Φ ((z, s) : (E × E) × ℝ)) := rfl
    rw [hVFTime_apply] at hd_within
    have hIcc_nhds : Set.Icc (-ε) ε ∈ 𝓝 s :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds hs_Ioo_ε) Set.Ioo_subset_Icc_self
    have hd_cutoff :
        HasDerivAt (fun s' : ℝ => Φ ((z, s') : (E × E) × ℝ))
          (chartPhaseVFCutoff (I := I) g α ((x₀, (0 : E)) : E × E) b
            (Φ ((z, s) : (E × E) × ℝ))) s := hd_within.hasDerivAt hIcc_nhds
    have h_in_closed : Φ ((z, s) : (E × E) × ℝ) ∈
        Metric.closedBall ((x₀, (0 : E)) : E × E) b.rIn :=
      Metric.ball_subset_closedBall (h_inner_T z hz s hs_Icc_T)
    have h_eq :
        chartPhaseVFCutoff (I := I) g α ((x₀, (0 : E)) : E × E) b
          (Φ ((z, s) : (E × E) × ℝ)) =
        chartPhaseVF (I := I) g α (Φ ((z, s) : (E × E) × ℝ)) :=
      chartPhaseVFCutoff_eq_of_mem_closedBall (I := I)
        (g := g) (α := α) (z₀ := ((x₀, (0 : E)) : E × E)) (b := b) h_in_closed
    rw [h_eq] at hd_cutoff
    exact hd_cutoff
  have hΦ_target_z : ∀ z ∈ Metric.ball ((x₀, (0 : E)) : E × E) ρ,
      ∀ s ∈ Set.Icc (-T) T,
      Φ ((z, s) : (E × E) × ℝ) ∈
        (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) := by
    intro z hz s hs
    have h_in_ball := h_inner_T z hz s hs
    have h_in_closed : Φ ((z, s) : (E × E) × ℝ) ∈
        Metric.closedBall ((x₀, (0 : E)) : E × E) b.rIn :=
      Metric.ball_subset_closedBall h_in_ball
    have h_in_outer : Φ ((z, s) : (E × E) × ℝ) ∈
        Metric.closedBall ((x₀, (0 : E)) : E × E) b.rOut :=
      Metric.closedBall_subset_closedBall (le_of_lt b.rIn_lt_rOut) h_in_closed
    exact hb_sub h_in_outer
  exact ⟨Φ, ρ, T, t', hρ_pos, hT_pos, ht'_in_Ioo, ht'_pos,
    hjoint, hΦ_init_z, hΦ_phase_z, hΦ_target_z, hΦ_cd⟩

end JointBasepointVector

end SmallVector

section OffZero

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

/-- **Exponential-map regularity away from the zero vector.** For a smooth
Riemannian metric `g`, base point `p : M`, and a nonzero tangent vector
`v ≠ 0`, the exponential map `fun w => expMap g p w` is `ContMDiffAt 𝓘(ℝ, E) I 1`
at `v`.

This is the off-zero analogue of `expMap_contMDiffAt_zero_of_chartFlowGeodesicMatchData`. At
the zero vector that statement assumes a `HasChartFlowGeodesicMatchData`
witness; here no such hypothesis is required, because away from `0` the
joint `C¹` smoothness in `(w, t)` of the chained geodesic flow yields the
regularity directly. The proof takes the `t = 1` slice of that joint flow:
it precomposes the flow `(w, t) ↦ maximalGeodesic g p w t` with the smooth
slice map `w ↦ (w, 1)` and uses `expMap g p w = maximalGeodesic g p w 1`. -/
theorem expMap_contMDiffAt_of_ne_zero
    (g : SmoothRiemannianMetric I M) (p : M) {v : E}
    (hv : (show TangentSpace I p from v) ≠ 0) :
    ContMDiffAt 𝓘(ℝ, E) I 1
      (fun w : E => (expMap (I := I) g p (show TangentSpace I p from w) : M))
      v := by
  classical
  obtain ⟨ρ, hρ, hjoint⟩ :=
    bm_c_expMap_chainedFlow_joint_contMDiff (I := I) g p v hv
  set F : E × ℝ → M :=
    fun vt => (maximalGeodesic (I := I) g p (show TangentSpace I p from vt.1) vt.2 : M)
    with hF_def
  set sl : E → E × ℝ := fun w => (w, 1) with hsl_def
  have hcomp_eq :
      (fun w : E => (expMap (I := I) g p (show TangentSpace I p from w) : M)) =
        F ∘ sl := by
    funext w
    simp only [Function.comp_apply, hF_def, hsl_def, expMap]
  rw [hcomp_eq]
  have hsl_within : ContMDiffWithinAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 1 sl
      (Metric.ball v ρ) v := by
    rw [hsl_def]
    exact (contMDiffWithinAt_id (I := 𝓘(ℝ, E))).prodMk
      (contMDiffWithinAt_const (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, ℝ)) (c := (1 : ℝ)))
  have hsl_maps : Set.MapsTo sl (Metric.ball v ρ)
      ((Metric.ball v ρ) ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro w hw
    exact ⟨hw, ⟨zero_le_one, le_refl 1⟩⟩
  have hF_within : ContMDiffWithinAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) I 1 F
      ((Metric.ball v ρ) ×ˢ Set.Icc (0 : ℝ) 1) (sl v) := by
    apply hjoint
    exact ⟨Metric.mem_ball_self hρ, ⟨zero_le_one, le_refl 1⟩⟩
  have hcw : ContMDiffWithinAt 𝓘(ℝ, E) I 1 (F ∘ sl) (Metric.ball v ρ) v :=
    hF_within.comp v hsl_within hsl_maps
  have hball_nhds : Metric.ball v ρ ∈ 𝓝 v :=
    Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ)
  exact hcw.contMDiffAt hball_nhds

end OffZero

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
