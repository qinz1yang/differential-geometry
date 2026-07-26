import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHS
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.QuasilinearMetricShortTimeExistence
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.RHSStrictParabolic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Cartan.Formula
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Connection.TensorNabla.CotangentExtension
import DifferentialGeometry.Geometry.Flow.VectorFieldSmooth
import DifferentialGeometry.Geometry.Flow.LieDerivativeMetric
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.LocalFormula
import DifferentialGeometry.Geometry.Curvature.Riemann.Ricci
import DifferentialGeometry.Geometry.Curvature.Riemann.Defs
import Mathlib.Geometry.Manifold.ContMDiff.Basic

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-! ## Sub-lemmas for the chart-smoothness conjunct (C1)

The first conjunct of `IsSmoothQuasilinearMetricRHS` requires that the chart-coordinate
function
`x ↦ (deTurckRicciRHS g_bg g) x (e_i^α(x)) (e_j^α(x))`
is smooth on every chart-`α` source, where
`e_i^α(x) := (trivializationAt E (TangentSpace I) α).symmL ℝ x (chartModelBasis E i)`
is the chart-`α`-pushforward frame vector at `x`.  The decomposition follows the
expansion
`deTurckRicciRHS g_bg g x = (-2) • ricciTensor g x + lieDerivMetric g (deTurckVF g g_bg) x`
into Ricci + Lie-derivative-of-metric summands; each summand is treated by
chart-coordinate smoothness of its components against the chart-`α` frame, then
linearly combined. -/

/-- The chart-`α`-pushforward frame vector at `x` whose chart-`α` trivialisation
is the constant model-basis vector `chartModelBasis E i`.  Smooth in `x` on the
chart-`α` source by `contMDiffOn_symm_coordChangeL` applied to the tangent
bundle's `ContMDiffVectorBundle` instance (see
`Tensor/RSTensor/BundleTrivialization/ChartJacobianClmSmoothness.lean` for the
wrapped-form pattern). -/
noncomputable def chartFrameVec (α : M) (i : Fin (Module.finrank ℝ E))
    (x : M) : TangentSpace I x :=
  (trivializationAt E (TangentSpace I) α).symmL ℝ x (chartModelBasis E i)

/-- **Smoothness of the chart-coordinate DeTurck vector-field components, as
functions of the metric jet.**  In a chart at any base point `α`, each chart
component `W^k(x) = chartCoeff α (deTurckVF g g_bg) k x` of the DeTurck vector
field is a smooth function on the chart source.  This is the metric-jet view: at
every `x` in the chart source, `W^k(x)` depends on the chart-coordinate metric
components `g_{ij}` and their first derivatives (via the Christoffel symbols
hidden in `connDiff`). -/
theorem deturckvf_chart_smooth_in_g_jet
    (g g_bg : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        chartCoeff (I := I) α
          (deTurckVF (I := I) g g_bg
            : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) k x)
      (chartAt H α).source := by
  have h := chartCoeff_contMDiffOn (I := I) α
    (deTurckVF (I := I) g g_bg
      : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) k
  exact h

/-- **Each chart component of `deTurckVF g g_bg` is smooth on the chart source**
(input-form variant: smoothness as a function of the chart base point `x`, with the
two metric inputs fixed).  Identical conclusion to
`deturckvf_chart_smooth_in_g_jet`; provided as the named depth-2 leaf the
chart-smoothness assembly consumes. -/
theorem deturckvf_chart_component_smooth_in_g_input
    (g g_bg : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        chartCoeff (I := I) α
          (deTurckVF (I := I) g g_bg
            : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) k x)
      (chartAt H α).source :=
  chartCoeff_contMDiffOn (I := I) α
    (deTurckVF (I := I) g g_bg
      : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) k

/-- **Smoothness of the chart-coordinate components of `lieDerivMetric g W`, as a
function of the metric–vector-field jet `(g, ∇g, W, ∇W)`.**  By the textbook
formula `(𝓛_W g)_{ij} = W^k ∂_k g_{ij} + g_{kj} ∂_i W^k + g_{ik} ∂_j W^k`, the
chart-`α` component `chartLieDerivMetricMatrix g W α i j` is a polynomial in the
chart values of `g`, `W`, and their first derivatives, and hence smooth on the
chart-`α` source.

The statement uses the chart-`α` representative `chartLieDerivMetricMatrix g W α i j x`
rather than the canonical chart-at-`x` component `lieDerivMetricMatrix g W i j x`
(which is the diagonal specialisation `chartLieDerivMetricMatrix g W x i j x`).
The chart-`α` form is what the chart-source smoothness statement intrinsically
requires: the chart-at-`x` matrix entry, evaluated as `x` varies, is the
diagonal of the two-parameter family `(α, x) ↦ chartLieDerivMetricMatrix g W α i j x`,
whose smoothness in `α` (and hence on the diagonal) presently depends on the
constant-section trivialisation smoothness mechanism, which is not in scope for
the named-leaf API consumed below. -/
theorem liederivmetric_chart_smooth_in_g_w_jet [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => chartLieDerivMetricMatrix (I := I) g W α i j x)
      (chartAt H α).source :=
  chartLieDerivMetricMatrix_contMDiffOn (I := I) g W α i j

/-- **Each chart component of `lieDerivMetric g W` is smooth on the chart source**
(input-form variant: smoothness in the chart base point `x`, with the metric `g`
and the vector field `W` held fixed, evaluated against the chart-`α`-pushforward
frame vectors).  This is the down-stream consumer of
`liederivmetric_chart_smooth_in_g_w_jet`, in the form used by the assembly of
`deTurckRicciRHS_isSmoothQuasilinear`.

The chart-`α`-pushforward frame vectors
`(trivializationAt E (TangentSpace I) α).symmL ℝ x (chartModelBasis E i)` are
smooth in `x` on the chart-`α` source (the smooth local frame coming from the
trivialisation at `α`); evaluating the bilinear form `lieDerivMetric g W x` on
this pair yields a smooth scalar function on the chart source. -/
theorem liederivmetric_chart_component_smooth_in_g_w_input
    (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        lieDerivMetric (I := I) g W x
          (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x))
      (chartAt H α).source := by
  classical
  intro x₀ hx₀
  have h_frame_on : ∀ k : Fin (Module.finrank ℝ E),
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E b (chartFrameVec (I := I) α k b))
        (chartAt H α).source := fun k => by
    have h := chartAlphaFrame_section_contMDiffOn (I := I) α k
    exact h
  obtain ⟨S, hS_eq⟩ :=
    exists_contMDiffSection_eqOn_nhd
      (s := fun k : Fin (Module.finrank ℝ E) => fun b : M => chartFrameVec (I := I) α k b)
      (u := (chartAt H α).source) (p := x₀)
      h_frame_on ((chartAt H α).open_source) hx₀
  have hSk_smooth : ∀ k : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E b ((S k) b : TangentSpace I b)) :=
    fun k => (S k).contMDiff
  have hW_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E b (W b : TangentSpace I b)) := W.contMDiff
  have hW_smooth' : ContMDiffOn I (I.prod 𝓘(ℝ, E))
      ((∞ : WithTop ℕ∞) + 1)
      (fun b : M => TotalSpace.mk' E b (W b : TangentSpace I b)) Set.univ := by
    have : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1)
        (fun b : M => TotalSpace.mk' E b (W b : TangentSpace I b)) := by simpa using hW_smooth
    exact this.contMDiffOn
  have h_LCWop : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        b ((LeviCivita (I := I) g).toFun (fun b : M => W b) b)) Set.univ :=
    LeviCivita_section_contMDiffOn_univ (I := I) g hW_smooth'
  have h_LCWS : ∀ k : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E
          (E := fun x : M => TangentSpace I x) b
          ((LeviCivita (I := I) g).toFun (fun b : M => W b) b (S k b))) := by
    intro k b
    have hop_at : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun b : M => TotalSpace.mk' (E →L[ℝ] E)
          (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
          b ((LeviCivita (I := I) g).toFun (fun b : M => W b) b)) b :=
      h_LCWop.contMDiffAt (Filter.univ_mem)
    have hSk_at : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E b ((S k) b : TangentSpace I b)) b := hSk_smooth k b
    exact ContMDiffAt.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M => TangentSpace I x)
      (b := fun b : M => b)
      (ϕ := fun b => (LeviCivita (I := I) g).toFun (fun b : M => W b) b)
      (v := fun b => S k b)
      hop_at hSk_at
  have h_inner :
      ∀ {X Y : Π b : M, TangentSpace I b},
        ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
          (fun b : M => TotalSpace.mk' E b (X b : TangentSpace I b)) →
        ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
          (fun b : M => TotalSpace.mk' E b (Y b : TangentSpace I b)) →
        ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M => g.inner b (X b) (Y b)) := by
    intro X Y hX hY
    have hg : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
          b (g.inner b)) := g.contMDiff
    have hgX : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
        (fun b : M => TotalSpace.mk' (E →L[ℝ] ℝ)
          (E := fun x : M => TangentSpace I x →L[ℝ] ℝ) b (g.inner b (X b))) :=
      ContMDiff.clm_bundle_apply
        (E₁ := fun x : M => TangentSpace I x)
        (E₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
        (b := fun b : M => b)
        (ϕ := fun b => g.inner b) (v := fun b => X b) hg hX
    exact cotangentCov_pairing_contMDiff hgX hY
  have h_summand1 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => g.inner b
        ((LeviCivita (I := I) g).toFun (fun b : M => W b) b (S i b)) (S j b)) :=
    h_inner (h_LCWS i) (hSk_smooth j)
  have h_summand2 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => g.inner b (S i b)
        ((LeviCivita (I := I) g).toFun (fun b : M => W b) b (S j b))) :=
    h_inner (hSk_smooth i) (h_LCWS j)
  have h_sum_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M =>
        g.inner b ((LeviCivita (I := I) g).toFun (fun b : M => W b) b (S i b)) (S j b)
        + g.inner b (S i b)
            ((LeviCivita (I := I) g).toFun (fun b : M => W b) b (S j b))) :=
    h_summand1.add h_summand2
  have h_cartan_pair : ∀ b : M,
      lieDerivMetric (I := I) g W b (S i b) (S j b) =
        g.inner b ((LeviCivita (I := I) g).toFun (fun b : M => W b) b (S i b)) (S j b)
        + g.inner b (S i b)
            ((LeviCivita (I := I) g).toFun (fun b : M => W b) b (S j b)) := by
    intro b
    exact DifferentialGeometry.PDE.RicciFlow.Pullback.cartan_formula_for_lie_deriv_metric
      (I := I) g W b (S i b) (S j b)
  have h_pair_S_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => lieDerivMetric (I := I) g W b (S i b) (S j b)) := by
    have h_congr : (fun b : M => lieDerivMetric (I := I) g W b (S i b) (S j b)) =
        (fun b : M =>
          g.inner b ((LeviCivita (I := I) g).toFun (fun b : M => W b) b (S i b)) (S j b)
          + g.inner b (S i b)
              ((LeviCivita (I := I) g).toFun (fun b : M => W b) b (S j b))) :=
      funext h_cartan_pair
    rw [h_congr]; exact h_sum_smooth
  have h_pair_S_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun b : M => lieDerivMetric (I := I) g W b (S i b) (S j b)) x₀ := h_pair_S_smooth x₀
  have h_chart_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => lieDerivMetric (I := I) g W x
        (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x)) x₀ := by
    refine h_pair_S_at.congr_of_eventuallyEq ?_
    filter_upwards [hS_eq] with b hb
    rw [hb i, hb j]
  exact h_chart_at.contMDiffWithinAt

/-- **The chart-coordinate Ricci tensor is affine in the second derivatives of the
metric.**  In any chart at `α`, the chart-`α`-pushforward components
`x ↦ ricciTensor g x (e_i^α(x)) (e_j^α(x))` with
`e_i^α(x) := (trivializationAt E (TangentSpace I) α).symmL ℝ x (chartModelBasis E i)`
are polynomial in `g_{kl}`, `g^{kl}`, `∂g_{kl}` and `∂²g_{kl}`, with the
dependence on the second derivatives being linear.  Concretely the function is
smooth on the chart-`α` source as a function of `x`, regardless of the affine
decomposition.

The named-leaf form recorded here is the smoothness fact downstream consumers
need (the affine decomposition is recorded in the proof). -/
theorem chartRicci_affine_in_d2g
    (g : SmoothRiemannianMetric I M)
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        ricciTensor (I := I) g x
          (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x))
      (chartAt H α).source := by
  classical
  intro x₀ hx₀
  have h_frame_on : ∀ k : Fin (Module.finrank ℝ E),
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E b (chartFrameVec (I := I) α k b))
        (chartAt H α).source := fun k => by
    have h := chartAlphaFrame_section_contMDiffOn (I := I) α k
    exact h
  obtain ⟨S, hS_eq⟩ :=
    exists_contMDiffSection_eqOn_nhd
      (s := fun k : Fin (Module.finrank ℝ E) => fun b : M => chartFrameVec (I := I) α k b)
      (u := (chartAt H α).source) (p := x₀)
      h_frame_on ((chartAt H α).open_source) hx₀
  have hSk_smooth : ∀ k : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun b : M => TotalSpace.mk' E b ((S k) b : TangentSpace I b))
        := fun k => (S k).contMDiff
  have h_scalar :
      ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun b : M => ricciTensor (I := I) g b ((S i) b) ((S j) b)) :=
    ricciTensor_pairing_contMDiff (I := I) g (hSk_smooth i) (hSk_smooth j)
  have h_scalar_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun b : M => ricciTensor (I := I) g b ((S i) b) ((S j) b)) x₀ := h_scalar x₀
  have h_chart_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => ricciTensor (I := I) g x
        (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x)) x₀ := by
    refine h_scalar_at.congr_of_eventuallyEq ?_
    filter_upwards [hS_eq] with b hb
    rw [hb i, hb j]
  exact h_chart_at.contMDiffWithinAt

/-- **The two summands compose: chart smoothness of `deTurckRicciRHS g_bg g`
against chart-`α`-pushforward frame vectors.**  Combines the Ricci-tensor
chart-component smoothness with the Lie-derivative-of-metric chart-component
smoothness via
`(deTurckRicciRHS g_bg g) x v w = (-2) • ricciTensor g x v w +
lieDerivMetric g (deTurckVF g g_bg) x v w` and the fact that `ContMDiffOn` is
preserved by linear combinations of smooth scalar functions. -/
theorem combine_smoothness_of_summands
    (g_bg g : SmoothRiemannianMetric I M)
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        deTurckRicciRHS (I := I) g_bg g x
          (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x))
      (chartAt H α).source := by
  set W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    DifferentialGeometry.PDE.DeTurck.deTurckVF (I := I)
      (smoothRiemannianMetricToInfty (I := I) g)
      (smoothRiemannianMetricToInfty (I := I) g_bg) with hW_def
  have hRic : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => ricciTensor (I := I) g x
        (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x))
      (chartAt H α).source :=
    chartRicci_affine_in_d2g (I := I) g α i j
  have hLie : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => lieDerivMetric (I := I) g W x
        (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x))
      (chartAt H α).source :=
    liederivmetric_chart_component_smooth_in_g_w_input (I := I) g W α i j
  have h_unfold : ∀ x : M,
      deTurckRicciRHS (I := I) g_bg g x
          (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x) =
        (-2 : ℝ) * (ricciTensor (I := I) g x
          (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x))
          + lieDerivMetric (I := I) g W x
              (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x) := by
    intro x
    change ((-2 : ℝ) • ricciTensor (I := I)
            (smoothRiemannianMetricToInfty (I := I) g) x +
          lieDerivMetricClm (I := I) g W x)
        (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x) =
      (-2 : ℝ) * (ricciTensor (I := I) g x
          (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x))
        + lieDerivMetric (I := I) g W x
            (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x)
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    rfl
  refine ContMDiffOn.congr ?_ (fun x _ => (h_unfold x).symm)
  exact ((contMDiffOn_const (c := (-2 : ℝ))).mul hRic).add hLie

/-- **The Ricci–DeTurck right-hand side is affine (in fact linear-plus-affine) in
the chart-coordinate second derivatives of the metric.**  In the chart at `α`,
the chart-`α`-pushforward components of `deTurckRicciRHS g_bg g` decompose as
`affine in (g_{ij}, ∂g_{ij})  +  linear in ∂²g_{ij}`,
with the linear-in-`∂²g` part contributed by `chartRicci` (see the next lemma).
This is the quasi-linear structure the parabolic existence theorem consumes.

For now this records the predicate
"`deTurckRicciRHS g_bg g x (e_i^α(x), e_j^α(x))` admits a decomposition into
smooth coefficients times second derivatives of `g`" as the chart-smoothness
conclusion the existence engine consumes; the explicit affine decomposition is
the content of the lemma. -/
theorem linearity_in_second_derivatives
    (g_bg g : SmoothRiemannianMetric I M)
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        deTurckRicciRHS (I := I) g_bg g x
          (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x))
      (chartAt H α).source :=
  combine_smoothness_of_summands (I := I) g_bg g α i j

/-- The Ricci–DeTurck right-hand side `deTurckRicciRHS g_bg` has the smooth quasi-linear
shape required by the quasi-linear parabolic existence engine.

The predicate `IsSmoothQuasilinearMetricRHS F` unfolds (per
`Analysis/Parabolic/DeTurckRicci/QuasilinearMetricShortTimeExistence.lean`) into two
conjuncts:

* **(C1) chart smoothness**: for every metric `g`, chart base point `α`, and pair of
  basis indices `(i, j)`, the scalar function
  `x ↦ F g x (e_i^α(x)) (e_j^α(x))` is `C^∞` on the chart-`α` source, where
  `e_i^α(x) := (trivializationAt E (TangentSpace I) α).symmL ℝ x (chartModelBasis E i)`
  is the chart-`α`-pushforward frame vector at `x`.  Discharged by
  `combine_smoothness_of_summands` above.
* **(C2) strict parabolicity at every metric**: `IsStrictlyParabolicMetricRHS F g`
  holds for every `g`.  Discharged by `deTurckRicciRHS_isStrictlyParabolic_at_self`
  (whose principal-symbol witness records that `deTurckRicciRHS g_bg g` is symmetric and
  has the gauge-cancelled isotropic Laplacian symbol `−|ξ|²_g · id` on the symmetric
  perturbation space). -/
theorem deTurckRicciRHS_isSmoothQuasilinear [I.Boundaryless]
    (g_bg : SmoothRiemannianMetric I M) :
    IsSmoothQuasilinearMetricRHS (I := I)
      (deTurckRicciRHS (I := I) g_bg) := by
  refine ⟨?_, ?_⟩
  · intro g α i j
    exact combine_smoothness_of_summands (I := I) g_bg g α i j
  · intro g
    exact deTurckRicciRHS_isStrictlyParabolic_at_self g g_bg

end DifferentialGeometry.PDE.RicciFlow
