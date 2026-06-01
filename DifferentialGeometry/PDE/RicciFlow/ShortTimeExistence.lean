import DifferentialGeometry.Metric.Basic
import DifferentialGeometry.Integral.Connection.Ricci
import DifferentialGeometry.PDE.ParabolicShortTime
import DifferentialGeometry.PDE.DeTurck.VectorField
import DifferentialGeometry.PDE.DeTurck.LieDerivativeMetric
import DifferentialGeometry.PDE.DeTurck.StrictParabolicity
import DifferentialGeometry.PDE.RicciFlow.DeTurckRHS
import DifferentialGeometry.PDE.RicciFlow.DeTurckShortTime
import DifferentialGeometry.PDE.RicciFlow.DeTurckVFTimeFamily
import DifferentialGeometry.PDE.RicciFlow.DeTurckSolutionC1
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow
import DifferentialGeometry.PDE.RicciFlow.Pullback.Metric
import DifferentialGeometry.PDE.RicciFlow.Pullback.RicciNaturality
import DifferentialGeometry.PDE.RicciFlow.Pullback.LieNaturality
import DifferentialGeometry.PDE.RicciFlow.Pullback.ChainRule
import Mathlib.Analysis.Calculus.Deriv.Basic
import DifferentialGeometry.PDE.RicciFlow.ShortTimeParabolic.DeTurckRicciPde
import DifferentialGeometry.PDE.RicciFlow.ShortTimeAssembly.ConjugatingDiffeoFamily
import DifferentialGeometry.PDE.RicciFlow.ShortTimeAssembly.FlatAssemblyInterior
import DifferentialGeometry.PDE.RicciFlow.ShortTimeAssembly.RicciFlowPdeAtZero
import DifferentialGeometry.PDE.RicciFlow.ShortTimeFlow.ConjugatingFlowData
import DifferentialGeometry.Integral.Measure.ChartDensity

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.ODE
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.Integral.Connection

/-! ## Short-time existence for the Ricci flow

Classical construction (Hamilton–DeTurck): given an initial smooth Riemannian
metric `g₀` on a closed manifold `M`, the Ricci flow `∂_t g = -2 Ric(g)` admits
a positive-time smooth solution with `g(0) = g₀`. The proof passes through:

1. Solve the (strictly parabolic) DeTurck–Ricci flow
   `∂_t g_DT = -2 Ric(g_DT) + 𝓛_{X_DT} g_DT` (where `X_DT = deTurckVF g_DT g_bg`)
   for time `[0, T_DT)`, via `deturck_ricci_flow_parabolic_short_time_existence` (here we take
   `g_bg := g₀` as the background metric).
2. Integrate the time-dependent vector field `-X_DT(t)` to obtain a smooth family
   of diffeomorphisms `Φ_t : M ≃ₘ M` with `Φ_0 = id` and `∂_t Φ_t = -X_DT ∘ Φ_t`.
3. Set `g_fam(t) := (Φ_t)^* (g_DT(t))`. Then `g_fam(0) = g₀` from
   `pullbackMetric_refl`, and by the chain rule + Ricci/Lie naturality
   the Lie-derivative term cancels, leaving `∂_t g_fam = -2 Ric(g_fam)`.

The conclusion is the genuine smooth Ricci flow on `[0, T)`: the family `g_fam`
is jointly `C∞` in `(t, x)` on the open interval `(0, T)` (at the level of the
chart-local Gram matrices, `Integral.Measure.chartGramMatrix`), jointly continuous
up to `t = 0`, satisfies `g_fam 0 = g₀`, and solves `∂_t g_fam = -2 Ric(g_fam)`
on `[0, T)`.

The DeTurck step is supplied by `deturck_ricci_flow_parabolic_short_time_existence` (the clean spectral
DeTurck–Ricci parabolic engine, which also exposes the DeTurck-field regularity and
the joint chart-Gram smoothness/continuity of `g_DT`); the conjugating
diffeomorphism family `Φ_fam` is built by `conjugating_diffeo_family` (integrating
the negated DeTurck field); the interior `∂_t g_fam = -2 Ric` identity is the flat
Hamilton–DeTurck assembly `flat_assembly_interior` and the `t = 0` endpoint the
continuity extension `ricci_flow_pde_at_zero`; the joint smoothness/continuity of
`g_fam = (Φ_fam)^* g_DT` follows from the conjugating-flow smooth-dependence data
(`conjugating_flow_*`, pinned to the genuine flow by its orbit ODE). The
construction step is assembled in `h_construct` below; it transits only those
faithful labeled inputs. -/
theorem ricci_flow_short_time_existence
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ T : ℝ, 0 < T ∧ ∃ g_fam : ℝ → SmoothRiemannianMetric I M,
      g_fam 0 = g₀ ∧
      (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
          (fun p : ℝ × M =>
            Integral.Measure.chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
          (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
      (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContinuousOn
          (fun p : ℝ × M =>
            Integral.Measure.chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
          (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
        HasDerivWithinAt (fun s : ℝ => (g_fam s).inner x v w)
          ((-2 : ℝ) *
            DifferentialGeometry.Integral.Connection.ricciTensor
              (I := I) (g_fam t) x v w) (Set.Ici 0) t) := by
  obtain ⟨T_DT, g_DT, hDT, h_reg, h_cont0, h_grad0, h_gram_DT, h_gram0_DT,
      h_gramOnE0_DT, h_C2_DT⟩ :=
    DifferentialGeometry.PDE.RicciFlow.deturck_ricci_flow_parabolic_short_time_existence
      (I := I) (M := M) g₀ g₀
  obtain ⟨hT_DT_pos, hDT_init, hDT_deriv⟩ := hDT
  have h_construct :
      ∃ T : ℝ, 0 < T ∧ ∃ g_fam : ℝ → SmoothRiemannianMetric I M,
        g_fam 0 = g₀ ∧
        (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
            (fun p : ℝ × M =>
              Integral.Measure.chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
            (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
        (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
          ContinuousOn
            (fun p : ℝ × M =>
              Integral.Measure.chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
            (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
        (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
          HasDerivWithinAt (fun s : ℝ => (g_fam s).inner x v w)
            ((-2 : ℝ) *
              DifferentialGeometry.Integral.Connection.ricciTensor
                (I := I) (g_fam t) x v w) (Set.Ici 0) t) := by
    have hDT_deriv' : ∀ t ∈ Set.Ico (0 : ℝ) T_DT, ∀ x : M, ∀ v w : TangentSpace I x,
        HasDerivWithinAt (fun s : ℝ => (g_DT s).inner x v w)
          (deTurckRicciRHS (I := I) g₀ (g_DT t) x v w)
          (Set.Ici 0) t := hDT_deriv
    obtain ⟨T, hT0, hT_le, Φ_fam, hΦ0, hΦode, hΦorbit0, hΦmfderiv0⟩ :=
      conjugating_diffeo_family
        (I := I) g_DT g₀ T_DT hT_DT_pos h_reg h_cont0 h_grad0
    have hΦode' : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
          (Set.Ici (0 : ℝ)) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (-(deTurckVF (I := I) (g_DT t) g₀ ((Φ_fam t : M → M) x)))) :=
      fun x t ht => hΦode x t ht
    have h_gram_DT_T : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
          (fun p : ℝ × M =>
            Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
          (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
      intro x₀ i j
      exact (h_gram_DT x₀ i j).mono
        (Set.prod_mono_left (Set.Ioo_subset_Ioo_right hT_le))
    have h_gram0_DT_T : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContinuousOn
          (fun p : ℝ × M =>
            Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
          (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
      intro x₀ i j
      exact (h_gram0_DT x₀ i j).mono
        (Set.prod_mono_left (Set.Ico_subset_Ico_right hT_le))
    have h_gramOnE0_T : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
        ContinuousOn
          (fun q : ℝ × M =>
            Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j
              (extChartAt I α q.2))
          (Set.Icc 0 T ×ˢ Set.univ) := by
      intro α i j
      exact (h_gramOnE0_DT α i j).mono
        (Set.prod_mono_left (Set.Icc_subset_Icc_right hT_le))
    have h_C2_T : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)) (k : ℕ), k ≤ 2 →
        ContinuousOn
          (fun q : ℝ × M => iteratedFDeriv ℝ k
            (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j)
            (extChartAt I α q.2))
          (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α) := by
      intro α i j k hk
      exact (h_C2_DT α i j k hk).mono
        (Set.prod_mono_left (Set.Icc_subset_Icc_right hT_le))
    have h_reg_T : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g₀ q.2)
          : TangentBundle I M))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) :=
      h_reg.mono (Set.prod_mono_left (Set.Ioo_subset_Ioo_right hT_le))
    obtain ⟨hΦ_orbit, hΦ_total⟩ :=
      conjugating_flow_orbit_pushforward_continuity_data (I := I) g_DT g₀ T hT0 Φ_fam hΦode'
        h_reg_T hΦorbit0 hΦmfderiv0
    obtain ⟨h_gram_fam, h_gram0_fam⟩ :=
      conjugating_flow_pullback_jointGram_data (I := I) g_DT g₀ T Φ_fam hΦode'
        h_gram_DT_T h_gram0_DT_T
    refine ⟨T, hT0, fun s => Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s),
      ?_, h_gram_fam, h_gram0_fam, ?_⟩
    · change Diffeomorph.pullbackMetric (g_DT 0) (Φ_fam 0) = g₀
      rw [hΦ0, Diffeomorph.pullbackMetric_refl, hDT_init]
    · have hDT_deriv_T : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
          HasDerivWithinAt (fun s : ℝ => (g_DT s).inner x v w)
            (deTurckRicciRHS (I := I) g₀ (g_DT t) x v w)
            (Set.Ici 0) t := by
        intro t ht x v w
        exact hDT_deriv' t ⟨le_of_lt ht.1, lt_of_lt_of_le ht.2 hT_le⟩ x v w
      have horbit : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
          HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
            (Set.Ici (0 : ℝ)) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (-(deTurckVF (I := I) (g_DT t) g₀ (Φ_fam t x)))) :=
        fun t ht x => hΦode x t ht
      have hDT_deriv_Ico : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ y : M, ∀ a b : TangentSpace I y,
          HasDerivWithinAt (fun u : ℝ => (g_DT u).inner y a b)
            (deTurckRicciRHS (I := I) g₀ (g_DT s) y a b) (Set.Ici 0) s := by
        intro s hs y a b
        exact hDT_deriv' s ⟨hs.1, lt_of_lt_of_le hs.2 hT_le⟩ y a b
      obtain ⟨T', P', hv_flat, hcorr, hbase, h_total_eval⟩ :=
        conjugating_flow_flat_data (I := I) g_DT g₀ T Φ_fam hDT_deriv_Ico hΦode
      have h_interior :=
        DifferentialGeometry.PDE.RicciFlow.flat_assembly_interior
          (I := I) g₀ g_DT T Φ_fam T' P' hDT_deriv_T hbase h_total_eval hv_flat hcorr
      intro t ht x v w
      rcases eq_or_lt_of_le ht.1 with h0 | h0
      · obtain ⟨h_cont, h_ric_cont⟩ :=
          conjugating_flow_t0_continuity_data (I := I) g_DT g₀ T hT0 Φ_fam hΦode
            hΦ0 hDT_init h_gramOnE0_T h_C2_T hΦ_orbit hΦ_total x v w
        subst_vars
        exact DifferentialGeometry.PDE.RicciFlow.ricci_flow_pde_at_zero
          (I := I) (fun s => Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)) hT0 x v w
          h_cont h_ric_cont (fun s hs => h_interior s hs x v w)
      · exact h_interior t ⟨h0, ht.2⟩ x v w
  exact h_construct

end DifferentialGeometry.PDE.RicciFlow
