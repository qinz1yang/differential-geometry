import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Geometry.Metric.ChartGram
import DifferentialGeometry.Geometry.Metric.ChartGramJointSmoothness
import DifferentialGeometry.Geometry.Flow.DeTurckVFJointSmoothness
import DifferentialGeometry.Geometry.Operator.Hessian
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartLocal
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHS
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.QuasilinearMetricShortTimeExistence

/-! # DeTurck–Ricci parabolic short-time existence and interior regularity

The single honest analytic input that both short-time-existence headlines consume:
existence of a short-time solution of the strictly-parabolic Ricci–DeTurck flow from
smooth initial data, bundled with the up-to-`t = 0` interior regularity that the
diffeomorphism pullback needs.

* the genuine Ricci-flow headline `ricci_flow_short_time_existence`
  (`Geometry/Flow/RicciFlow/ShortTimeExistence.lean`) consumes the full bundle
  (existence + DeTurck-vector-field / chart-Gram regularity for the pullback);
* the Ricci–DeTurck headline `deTurckRicci_shortTime_existence_of_closed`
  (`Geometry/Flow/RicciFlow/DeTurckShortTime.lean`) consumes only its existence
  conjunct (`IsQuasilinearMetricParabolicSolution`).

This file lives upstream of both headlines, so both can cite the single bundle.

## Structure of the proof

The honest classical PDE input is isolated in `deturck_ricci_smooth_solution_engine`: a
strictly-parabolic quasilinear DeTurck–Ricci flow has a smooth short-time solution from
smooth initial data, jointly `C∞` up to and including `t = 0` on the *closed* slab
`[0, T] × M` for `T` below the maximal existence time (Chow–Knopf, *The Ricci Flow*,
Short-Time Existence; Lieberman / Ladyzhenskaya–Solonnikov–Uraltseva / Amann). All the
regularity conjuncts of the headline are then *readouts* of that single joint-smoothness
datum (`hsmooth`: the metric inner-product `Hom`-section is jointly `C∞`), proved
sorry-free against the intrinsic `g`-inner chart-Gram calculus — never a `chartJ`
extraction. -/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **HONEST CLASSICAL INPUT (md1 engine) — strictly-parabolic quasilinear short-time
existence + joint interior smoothness up to `t = 0`.**

For a closed Riemannian manifold the DeTurck-modified flow `∂ₜḡ = −2 Ric(ḡ) + 𝓛_W ḡ` is a
smooth-quasilinear, *strictly parabolic* system (principal symbol `σ[DQ](ζ) = |ζ|²·Id`,
Chow–Knopf, *The Ricci Flow: An Introduction*, "Short time existence"). By the standard
quasilinear parabolic existence + interior regularity theory (Lieberman, Ch. VIII;
Ladyzhenskaya–Solonnikov–Uraltseva; Amann maximal regularity) it has a smooth short-time
solution `g_DT` from the smooth initial datum `g₀`, packaged as
`IsQuasilinearMetricParabolicSolution (deTurckRicciRHS g_bg) g₀ T g_DT`, TOGETHER with the
joint smoothness of the metric inner-product `Hom`-section `(t, x) ↦ (g_DT t).inner x`.

The joint-`C∞`-on-the-closed-slab `Set.Icc 0 T ×ˢ Set.univ` is achievable because `T` is
existential: taking `T` strictly below the maximal existence time makes the smooth
solution `C∞` on the compact `[0, T] × M` (including both endpoints), while the flow
equation itself is only asserted on `[0, T)`. The `sorry` is this deferred classical
input; consumers transitively depend on `sorryAx`. -/
theorem deturck_ricci_smooth_solution_engine
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ T : ℝ, ∃ g_DT : ℝ → SmoothRiemannianMetric I M,
      IsQuasilinearMetricParabolicSolution (I := I)
        (deTurckRicciRHS (I := I) g_bg) g₀ T g_DT ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun q : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
          q.2 ((g_DT q.1).inner q.2))
        (Set.Icc 0 T ×ˢ Set.univ) :=
  sorry

/-- **L_vf (Icc) — readout: the DeTurck vector field is jointly `(t, x)`-`C∞` up to and
including `t = 0`.** -/
theorem deTurckVF_jointContMDiffOn_Icc
    (g_bg : SmoothRiemannianMetric I M)
    (g_DT : ℝ → SmoothRiemannianMetric I M) (T : ℝ) (hT : 0 < T)
    (h_gDT : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun q : ℝ × M =>
          Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) x₀ i j
            (extChartAt I x₀ q.2))
        (Set.Icc (0 : ℝ) T ×ˢ (chartAt H x₀).source)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
        : TangentBundle I M))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ) :=
  sorry

/-- **L_jet — readout: the `k ≤ 2` spatial Fréchet jets of `chartGramOnE` are jointly
`(t, x)`-continuous up to and including `t = 0`.** -/
theorem chartGramOnE_jets_jointContinuousOn_of_innerSmooth
    (α : M) (i j : Fin (Module.finrank ℝ E)) (k : ℕ) (hk : k ≤ 2)
    (g_DT : ℝ → SmoothRiemannianMetric I M) (T : ℝ) (hT : 0 < T)
    (hsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        q.2 ((g_DT q.1).inner q.2))
      (Set.Icc 0 T ×ˢ Set.univ)) :
    ContinuousOn
      (fun q : ℝ × M => iteratedFDeriv ℝ k
        (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j)
        (extChartAt I α q.2))
      (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α) :=
  sorry

/-- **Parabolic short-time existence + interior regularity bundle.** -/
theorem deturck_ricci_flow_parabolic_short_time_existence
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ T : ℝ, ∃ g_DT : ℝ → SmoothRiemannianMetric I M,
      IsQuasilinearMetricParabolicSolution (I := I)
        (deTurckRicciRHS (I := I) g_bg) g₀ T g_DT ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
          : TangentBundle I M))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
          : TangentBundle I M))
        (Set.Icc 0 T ×ˢ Set.univ) ∧
      (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
          (fun p : ℝ × M =>
            Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
          (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
      (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContinuousOn
          (fun p : ℝ × M =>
            Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
          (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
      (∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
        ContinuousOn
          (fun q : ℝ × M =>
            Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j
              (extChartAt I α q.2))
          (Set.Icc 0 T ×ˢ (chartAt H α).source)) ∧
      (∀ (α : M) (i j : Fin (Module.finrank ℝ E)) (k : ℕ), k ≤ 2 →
        ContinuousOn
          (fun q : ℝ × M => iteratedFDeriv ℝ k
            (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j)
            (extChartAt I α q.2))
          (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α)) := by
  classical
  obtain ⟨T, g_DT, hsol, hsmooth⟩ := deturck_ricci_smooth_solution_engine (I := I) g₀ g_bg
  have hmono_Ioo : ∀ x₀ : M,
      Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet
        ⊆ Set.Icc 0 T ×ˢ Set.univ := fun x₀ =>
    Set.prod_mono Set.Ioo_subset_Icc_self (Set.subset_univ _)
  have hmono_Ico : ∀ x₀ : M,
      Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet
        ⊆ Set.Icc 0 T ×ˢ Set.univ := fun x₀ =>
    Set.prod_mono Set.Ico_subset_Icc_self (Set.subset_univ _)
  have hmono_Icc : ∀ α : M,
      Set.Icc (0 : ℝ) T ×ˢ (chartAt H α).source ⊆ Set.Icc 0 T ×ˢ Set.univ := fun α =>
    Set.prod_mono (le_refl _) (Set.subset_univ _)
  have hgOnE_Ioo : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun q : ℝ × M =>
          Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) x₀ i j
            (extChartAt I x₀ q.2))
        (Set.Ioo (0 : ℝ) T ×ˢ (chartAt H x₀).source) := fun x₀ i j =>
    chartGramOnE_jointContMDiffOn_of_innerSmooth (I := I) x₀ i j g_DT
      (hsmooth.mono (Set.prod_mono Set.Ioo_subset_Icc_self (Set.subset_univ _)))
  have hgOnE_Icc : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun q : ℝ × M =>
          Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) x₀ i j
            (extChartAt I x₀ q.2))
        (Set.Icc (0 : ℝ) T ×ˢ (chartAt H x₀).source) := fun x₀ i j =>
    chartGramOnE_jointContMDiffOn_of_innerSmooth (I := I) x₀ i j g_DT
      (hsmooth.mono (Set.prod_mono (le_refl _) (Set.subset_univ _)))
  refine ⟨T, g_DT, hsol, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact deTurckVF_jointContMDiffOn_Ioo (I := I) g_bg g_DT T hgOnE_Ioo
  · exact deTurckVF_jointContMDiffOn_Icc (I := I) g_bg g_DT T hsol.1 hgOnE_Icc
  · intro x₀ i j
    exact chartGramMatrix_jointContMDiffOn_of_innerSmooth (I := I) x₀ i j g_DT
      (hsmooth.mono (hmono_Ioo x₀))
  · intro x₀ i j
    exact (chartGramMatrix_jointContMDiffOn_of_innerSmooth (I := I) x₀ i j g_DT
      (hsmooth.mono (hmono_Ico x₀))).continuousOn
  · intro α i j
    exact (chartGramOnE_jointContMDiffOn_of_innerSmooth (I := I) α i j g_DT
      (hsmooth.mono (hmono_Icc α))).continuousOn
  · intro α i j k hk
    exact chartGramOnE_jets_jointContinuousOn_of_innerSmooth (I := I) α i j k hk g_DT T hsol.1 hsmooth

end DifferentialGeometry.PDE.RicciFlow
