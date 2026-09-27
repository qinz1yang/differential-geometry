import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalMetricCauchy
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.ReferenceChange

noncomputable section

open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ}

private local instance terminalSigmaCompact (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)
private local instance terminalC1 (G : P.IncomingSlab a s) :
    IsManifold ThreeModel 1 G.terminalRegularOpen := IsManifold.of_le (n := ∞) (by decide)
private local instance terminalC2 (G : P.IncomingSlab a s) :
    IsManifold ThreeModel 2 G.terminalRegularOpen := IsManifold.of_le (n := ∞) (by decide)

theorem IncomingSlab.exists_metric_limit_on_terminalRegularOpen
    (G : P.IncomingSlab a s) :
    ∃ gInf : SmoothRiemannianMetric ThreeModel G.terminalRegularOpen,
      ∀ K : Set G.terminalRegularOpen, IsCompact K → ∀ p : ℕ,
        ∀ ε : ℝ, 0 < ε → ∀ᶠ t in 𝓝[<] s, ∀ q ≤ p, ∀ x ∈ K,
          metricDerivNorm q ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen)
            gInf ((G.flow.base.metric a).restrictOpen G.terminalRegularOpen) x < ε := by
  classical
  cases isEmpty_or_nonempty G.terminalRegularOpen with
  | inl hEmpty =>
    let _ := hEmpty
    exact ⟨(G.flow.base.metric a).restrictOpen G.terminalRegularOpen,
      fun K _ p ε _ => Eventually.of_forall (fun t q hq x _ => isEmptyElim x)⟩
  | inr hne =>
    obtain ⟨τ, hτmono, hτmem, hτlim⟩ := exists_seq_strictMono_tendsto' G.lt
    have hτ : Tendsto τ atTop (𝓝[<] s) :=
      tendsto_nhdsWithin_iff.mpr ⟨hτlim, Eventually.of_forall (fun n => (hτmem n).2)⟩
    let gRef := (G.flow.base.metric a).restrictOpen G.terminalRegularOpen
    let gSeq := fun n => (G.flow.base.metric (τ n)).restrictOpen G.terminalRegularOpen
    obtain ⟨φ, hφ, gInf, hInf⟩ := G.exists_smooth_positive_metric_prelimit hne hτ
    obtain ⟨hbdd, hlow⟩ := G.terminal_metric_sequence_bounds hτ
    refine ⟨gInf, ?_⟩
    intro K hK p ε hε
    obtain ⟨ψ, hψ, gK, hKinner, hKjets⟩ :=
      exists_metric_subsequence_tendsto_on_compact_of_eventual_pointwise_lower
        hne K hK p gRef gSeq hbdd hlow
    have heq : gInf = gK := metricLimit_uniq gSeq gInf gK
      (fun x v w => G.metric_sequence_inner_cauchy hτ x v w) φ hφ ψ hψ hInf hKinner
    subst gK
    obtain ⟨c, hc, L, hL, hlip⟩ := G.exists_metric_time_lipschitz_on_terminalRegularOpen hK p
    let δ : ℝ := ε / (2 * (L + 1))
    have hδ : 0 < δ := div_pos hε (by positivity)
    have hLδ : L * δ < ε / 2 := by
      have he : 2 * (L + 1) * δ = ε := by dsimp [δ]; field_simp
      nlinarith
    obtain ⟨n₀, hn₀⟩ := hKjets (ε / 2) (by positivity)
    have hψτ : Tendsto (fun n => τ (ψ n)) atTop (𝓝[<] s) := hτ.comp hψ.tendsto_atTop
    have hnear : ∀ᶠ n in atTop, τ (ψ n) ∈ Ioo (max c (s - δ)) s :=
      hψτ.eventually (Ioo_mem_nhdsLT (max_lt hc.2 (by linarith)))
    obtain ⟨n, hn, hnt⟩ := ((eventually_ge_atTop n₀).and hnear).exists
    have hnTime : τ (ψ n) ∈ Ico c s :=
      ⟨((le_max_left _ _).trans_lt hnt.1).le, hnt.2⟩
    filter_upwards [Ioo_mem_nhdsLT (max_lt hc.2 (by linarith : s - δ < s))] with t ht
    intro q hq x hx
    have htTime : t ∈ Ico c s := ⟨((le_max_left _ _).trans_lt ht.1).le, ht.2⟩
    have habs : |t - τ (ψ n)| < δ := by
      apply abs_lt.mpr
      have htlow := (le_max_right c (s - δ)).trans_lt ht.1
      have hnlow := (le_max_right c (s - δ)).trans_lt hnt.1
      constructor <;> linarith [ht.2, hnt.2]
    have htime := hlip q hq t htTime (τ (ψ n)) hnTime x hx
    have hclose := hn₀ n hn q hq x hx
    have htriangle := metricDerivNorm_triangle q
      ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen)
      (gSeq (ψ n)) gInf gRef x
    have hprod := mul_le_mul_of_nonneg_left habs.le hL
    exact lt_of_le_of_lt htriangle (by change _ < ε; linarith)

theorem IncomingSlab.nonempty_terminalLimitMetric (G : P.IncomingSlab a s) :
    Nonempty G.TerminalLimitMetric := by
  obtain ⟨gInf, hconv⟩ := G.exists_metric_limit_on_terminalRegularOpen
  refine ⟨⟨gInf, ?_⟩⟩
  intro K hK p ε hε
  let gRef := (G.flow.base.metric a).restrictOpen G.terminalRegularOpen
  obtain ⟨D, hD, hcompare⟩ := exists_metric_deriv_norm_reference_bound hK gRef gInf p
  let δ : ℝ := ε / (2 * (D + 1) * ((p : ℝ) + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hevent : ∀ᶠ t in 𝓝[<] s, ∀ x ∈ K,
      metricDerivNorm p ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen)
        gInf gInf x < ε := by
    filter_upwards [hconv K hK p δ hδ] with t ht
    intro x hx
    have hsum : (∑ j ∈ Finset.range (p + 1), metricDerivNorm j
        ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen) gInf gRef x) ≤
        ((p : ℝ) + 1) * δ := by
      calc
        _ ≤ ∑ _j ∈ Finset.range (p + 1), δ := Finset.sum_le_sum (fun j hj =>
          (ht j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) x hx).le)
        _ = _ := by simp
    have hbound := hcompare ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen)
      gInf p le_rfl x hx
    have hsmall : D * (((p : ℝ) + 1) * δ) ≤ ε / 2 := by
      dsimp [δ]
      have hden : 0 < 2 * (D + 1) * ((p : ℝ) + 1) := by positivity
      rw [← mul_div_assoc, ← mul_div_assoc]
      apply (div_le_iff₀ hden).mpr
      nlinarith [mul_nonneg (show 0 ≤ (p : ℝ) by positivity) hε.le]
    exact ((hbound.trans (mul_le_mul_of_nonneg_left hsum hD)).trans hsmall).trans_lt
      (by linarith)
  exact (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset G.lt).mp hevent

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage
