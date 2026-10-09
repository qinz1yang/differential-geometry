import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.CompatibleChainLimits
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Congruence

set_option autoImplicit false
noncomputable section
open DifferentialGeometry.Geometry.Curvature
section

universe u uE uH

section

set_option autoImplicit false

namespace DifferentialGeometry.CheegerGromovCompactness

open scoped Manifold ContDiff
open Set TopologicalSpace

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : ℕ → Type u} [∀ j, MetricSpace (M j)] [∀ j, ChartedSpace H (M j)]
  [∀ j, IsManifold I ∞ (M j)] [∀ j, SigmaCompactSpace (M j)]

theorem chain_pullback_bounded_on
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (K : ∀ j, Set (M j)) {j : ℕ} (U : Opens (M j))
    (hUK : (U : Set (M j)) ⊆ K j)
    (D0 : ∀ k, PartialDiffeomorphMetricApproximation (I := I)
      (K j) (1 / 2) 0 (chainComp (I := I) (Mf := M) Ψ j k) (g j) (g (j + k)))
    (Dhi : ∀ p : ℕ, ∃ a : ℕ,
      (chainComp (I := I) (Mf := M) Ψ j a : M j → M (j + a)) ''
        (U : Set (M j)) ⊆ K (j + a) ∧
      ∀ c : ℕ, Nonempty (PartialDiffeomorphMetricApproximation (I := I)
        (K (j + a)) (1 / 2) p (chainComp (I := I) (Mf := M) Ψ (j + a) c)
        (g (j + a)) (g ((j + a) + c)))) :
    letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    let hU : ∀ k, (U : Set (M j)) ⊆ (chainComp (I := I) (Mf := M) Ψ j k).source :=
      fun k => hUK.trans (D0 k).source_sub
    let gSeq := chainPullbackSeq (I := I) Ψ g U hU
    ∃ gRef : ℕ → SmoothRiemannianMetric I U,
      (∀ r q : ℕ, q ≤ r → ∀ C : Set U, IsCompact C → ∃ B : ℝ,
        ∀ k : ℕ, ∀ z ∈ C,
          metricCovDerivNorm (I := I) q (gSeq k) (gRef r) z ≤ B) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ (k : ℕ) (x : U) (v : TangentSpace I x),
        c * ((g j).restrictOpen (I := I) U).inner x v v ≤ (gSeq k).inner x v v := by
  classical
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let hU : ∀ k, (U : Set (M j)) ⊆ (chainComp (I := I) (Mf := M) Ψ j k).source :=
    fun k => hUK.trans (D0 k).source_sub
  let gSeq := chainPullbackSeq (I := I) Ψ g U hU
  let a : ℕ → ℕ := fun r => (Dhi r).choose
  have himg : ∀ r,
      (chainComp (I := I) (Mf := M) Ψ j (a r) : M j → M (j + a r)) ''
        (U : Set (M j)) ⊆ K (j + a r) := fun r => (Dhi r).choose_spec.1
  have htail : ∀ r c, PartialDiffeomorphMetricApproximation (I := I)
      (K (j + a r)) (1 / 2) r
      (chainComp (I := I) (Mf := M) Ψ (j + a r) c)
      (g (j + a r)) (g ((j + a r) + c)) :=
    fun r c => Classical.choice ((Dhi r).choose_spec.2 c)
  let gRef : ℕ → SmoothRiemannianMetric I U := fun r => gSeq (a r)
  refine ⟨gRef, ?_, ?_⟩
  · intro r q hqr C hC
    apply cov_bdd_of_eventual (I := I) hC q gSeq (gRef r)
    refine ⟨a r, max (2 * Real.sqrt (Module.finrank ℝ E : ℝ)) (1 / 2), ?_⟩
    intro k hk z hz
    let c := k - a r
    have hdecomp : a r + c = k := by
      dsimp only [c]
      omega
    have hpre := hU (a r)
    have hnext :
        (chainComp (I := I) (Mf := M) Ψ j (a r) : M j → M (j + a r)) ''
          (U : Set (M j)) ⊆
          (chainComp (I := I) (Mf := M) Ψ (j + a r) c).source :=
      fun y hy => (htail r c).source_sub (himg r hy)
    have hfull : (U : Set (M j)) ⊆
        (chainCompAssoc (I := I) (Mf := M) Ψ j (a r) c).source := by
      rw [chainAssoc_source]
      exact hU (a r + c)
    by_cases hq0 : q = 0
    · subst q
      have hb := chain_prefix_metric_zero_cov_deriv_norm_le (I := I) Ψ U hpre hnext
        (himg r) hfull (g (j + a r)) (g ((j + a r) + c))
        (htail r c).forward (by norm_num) z
      rw [chain_pullback_assoc (I := I) Ψ g U hfull (hU (a r + c))] at hb
      rw [hdecomp] at hb
      have hb' : metricCovDerivNorm (I := I) 0 (gSeq k) (gRef r) z ≤
          2 * Real.sqrt (Module.finrank ℝ E : ℝ) := by
        simpa only [gSeq, gRef, chainPullbackSeq,
          SmoothRiemannianMetric.restrictOpen_inner] using hb
      exact hb'.trans (le_max_left _ _)
    · have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
      have hb := chain_prefix_metric_cov_deriv_norm_le (I := I) Ψ U hpre hnext
        (himg r) hfull (g (j + a r)) (g ((j + a r) + c)) (htail r c).forward hq1 hqr z
      rw [chain_pullback_assoc (I := I) Ψ g U hfull (hU (a r + c))] at hb
      rw [hdecomp] at hb
      have hb' : metricCovDerivNorm (I := I) q (gSeq k) (gRef r) z ≤ 1 / 2 := by
        simpa only [gSeq, gRef, chainPullbackSeq] using hb
      exact hb'.trans (le_max_right _ _)
  · refine ⟨1 / 2, by norm_num, fun k x v => ?_⟩
    have hb := pullback_metric_inner_lower (I := I)
      (chainComp (I := I) (Mf := M) Ψ j k) U (hU k) hUK
      (g j) (g (j + k)) (D0 k).forward x v
    norm_num at hb
    change (1 / 2 : ℝ) * (g j).inner (x : M j) v v ≤
      (PartialDiffeomorph.pullbackMetricOn (I := I)
        (chainComp (I := I) (Mf := M) Ψ j k) U (hU k) (g (j + k))).inner x v v
    exact hb

theorem exists_compatible_chain_pullback_metric_limits_on [I.Boundaryless]
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (K : ∀ j, Set (M j)) (U : ∀ j, Opens (M j)) (hne : ∀ j, Nonempty (U j))
    (hUK : ∀ j, (U j : Set (M j)) ⊆ K j)
    (hU : ∀ j k, (U j : Set (M j)) ⊆ (chainComp (I := I) (Mf := M) Ψ j k).source)
    (hmap : ∀ j, (chainComp (I := I) (Mf := M) Ψ j 1 : M j → M (j + 1)) ''
      (U j : Set (M j)) ⊆ (U (j + 1) : Set (M (j + 1))))
    (D0 : ∀ j k, PartialDiffeomorphMetricApproximation (I := I)
      (K j) (1 / 2) 0 (chainComp (I := I) (Mf := M) Ψ j k) (g j) (g (j + k)))
    (Dhi : ∀ j p : ℕ, ∃ a : ℕ,
      (chainComp (I := I) (Mf := M) Ψ j a : M j → M (j + a)) ''
        (U j : Set (M j)) ⊆ K (j + a) ∧
      ∀ c : ℕ, Nonempty (PartialDiffeomorphMetricApproximation (I := I)
        (K (j + a)) (1 / 2) p (chainComp (I := I) (Mf := M) Ψ (j + a) c)
        (g (j + a)) (g ((j + a) + c)))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ gInf : ∀ j, SmoothRiemannianMetric I (U j),
      (∀ j,
        letI : SigmaCompactSpace (U j) := isSigmaCompact_iff_sigmaCompactSpace.mp
          (Geometry.isSigmaCompact_of_isOpen I (U j).isOpen)
        MetricCInfConvergenceOnCompacts (I := I)
          (fun k => chainPullbackSeq (I := I) Ψ g (U j) (hU j) (φ k - j))
          (gInf j) ((g j).restrictOpen (I := I) (U j))) ∧
      ∀ j,
        let F : U j → U (j + 1) := PartialDiffeomorph.opensMap
          (chainComp (I := I) (Mf := M) Ψ j 1) (hmap j)
        ∀ (x : U j) (v w : TangentSpace I x),
          (gInf j).inner x v w =
            (gInf (j + 1)).inner (F x) (mfderiv I I F x v) (mfderiv I I F x w) := by
  classical
  let gSeq : ∀ n, ℕ → SmoothRiemannianMetric I (U n) :=
    fun n => chainPullbackSeq (I := I) Ψ g (U n) (hU n)
  let P : ℕ → (ℕ → ℕ) → Prop := fun n ξ =>
    letI : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
    ∃ gInf : SmoothRiemannianMetric I (U n),
      MetricCInfConvergenceOnCompacts (I := I)
        (fun k => gSeq n (ξ k - n)) gInf ((g n).restrictOpen (I := I) (U n))
  have metric_subseq : ∀ {N : Type u} [TopologicalSpace N] [ChartedSpace H N]
      [T2Space N] [IsManifold I ∞ N] [SigmaCompactSpace N]
      {gS : ℕ → SmoothRiemannianMetric I N} {gLim gBase : SmoothRiemannianMetric I N},
      MetricCInfConvergenceOnCompacts (I := I) gS gLim gBase →
      ∀ {ρ : ℕ → ℕ}, StrictMono ρ →
        MetricCInfConvergenceOnCompacts (I := I) (fun k => gS (ρ k)) gLim gBase := by
    intro N _ _ _ _ _ gS gLim gBase hconv ρ hρ C hC p ε hε
    obtain ⟨k₀, hk₀⟩ := hconv C hC p ε hε
    exact ⟨k₀, fun k hk => hk₀ (ρ k) (le_trans hk hρ.le_apply)⟩
  have metric_of_tail : ∀ {N : Type u} [TopologicalSpace N] [ChartedSpace H N]
      [T2Space N] [IsManifold I ∞ N] [SigmaCompactSpace N]
      {gS : ℕ → SmoothRiemannianMetric I N} {gLim gBase : SmoothRiemannianMetric I N},
      ∀ m : ℕ,
        MetricCInfConvergenceOnCompacts (I := I) (fun k => gS (k + m)) gLim gBase →
        MetricCInfConvergenceOnCompacts (I := I) gS gLim gBase := by
    intro N _ _ _ _ _ gS gLim gBase m hconv C hC p ε hε
    obtain ⟨k₀, hk₀⟩ := hconv C hC p ε hε
    refine ⟨k₀ + m, fun k hk => ?_⟩
    have hval := hk₀ (k - m) (by omega)
    simpa only [Nat.sub_add_cancel (show m ≤ k by omega)] using hval
  obtain ⟨φ, hφ, hPφ⟩ := exists_diag_subseq P
    (fun n ξ _ => by
      let _ : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
      obtain ⟨gRef, hbdd, hlow⟩ :=
        chain_pullback_bounded_on Ψ g K (U n) (hUK n) (D0 n) (Dhi n)
      have hbdd' : ∀ r q : ℕ, q ≤ r → ∀ C : Set (U n), IsCompact C → ∃ B : ℝ,
          ∀ k : ℕ, ∀ z ∈ C,
            metricCovDerivNorm (I := I) q (gSeq n (ξ k - n)) (gRef r) z ≤ B := by
        intro r q hqr C hC
        obtain ⟨B, hB⟩ := hbdd r q hqr C hC
        exact ⟨B, fun k z hz => hB (ξ k - n) z hz⟩
      obtain ⟨c, hc, hclow⟩ := hlow
      have hlow' : ∃ c : ℝ, 0 < c ∧ ∀ (k : ℕ) (x : U n) (v : TangentSpace I x),
          c * ((g n).restrictOpen (I := I) (U n)).inner x v v ≤
            (gSeq n (ξ k - n)).inner x v v :=
        ⟨c, hc, fun k => hclow (ξ k - n)⟩
      obtain ⟨ψ, hψ, gInf, hconv⟩ := metricCInf_refs (I := I) (hne n)
        ((g n).restrictOpen (I := I) (U n)) gRef
        (fun k => gSeq n (ξ k - n)) hbdd' hlow'
      exact ⟨ψ, hψ, gInf, by simpa only [Function.comp_apply] using hconv⟩)
    (fun n ξ ρ hρ hP => by
      let _ : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
      obtain ⟨gInf, hconv⟩ := hP
      exact ⟨gInf, metric_subseq hconv hρ⟩)
    (fun n ξ m hP => by
      let _ : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
      obtain ⟨gInf, hconv⟩ := hP
      exact ⟨gInf, metric_of_tail m hconv⟩)
  let gInf : ∀ n, SmoothRiemannianMetric I (U n) := fun n =>
    letI : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
    (hPφ n).choose
  have hconv : ∀ n,
      letI : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
      MetricCInfConvergenceOnCompacts (I := I)
        (fun k => chainPullbackSeq (I := I) Ψ g (U n) (hU n) (φ k - n))
        (gInf n) ((g n).restrictOpen (I := I) (U n)) := fun n => (hPφ n).choose_spec
  refine ⟨φ, hφ, gInf, hconv, fun n => ?_⟩
  let _ : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
  let _ : SigmaCompactSpace (U (n + 1)) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I (U (n + 1)).isOpen)
  let F : U n → U (n + 1) := PartialDiffeomorph.opensMap
    (chainComp (I := I) (Mf := M) Ψ n 1) (hmap n)
  change ∀ (x : U n) (v w : TangentSpace I x), (gInf n).inner x v w =
    (gInf (n + 1)).inner (F x) (mfderiv I I F x v) (mfderiv I I F x w)
  intro x v w
  have hleft := metricCInf_inner (I := I)
    (fun k => chainPullbackSeq (I := I) Ψ g (U n) (hU n) (φ k - n))
    (gInf n) ((g n).restrictOpen (I := I) (U n)) (hconv n) x v w
  have hright := metricCInf_inner (I := I)
    (fun k => chainPullbackSeq (I := I) Ψ g (U (n + 1)) (hU (n + 1)) (φ k - (n + 1)))
    (gInf (n + 1)) ((g (n + 1)).restrictOpen (I := I) (U (n + 1)))
    (hconv (n + 1)) (F x) (mfderiv I I F x v) (mfderiv I I F x w)
  have hevent :
      (fun k => (chainPullbackSeq (I := I) Ψ g (U n) (hU n) (φ k - n)).inner x v w)
        =ᶠ[Filter.atTop]
      (fun k => (chainPullbackSeq (I := I) Ψ g (U (n + 1)) (hU (n + 1))
        (φ k - (n + 1))).inner (F x) (mfderiv I I F x v) (mfderiv I I F x w)) := by
    filter_upwards [Filter.eventually_ge_atTop (n + 1)] with k hk
    have hφk : n + 1 ≤ φ k := le_trans hk (hφ.id_le k)
    have hlen : φ k - n = 1 + (φ k - (n + 1)) := by omega
    rw [hlen]
    simpa only [F] using chain_pullback_step (I := I) Ψ g (U n) (U (n + 1))
      (hU n) (hU (n + 1)) (hmap n) (φ k - (n + 1)) x v w
  have hleft' := Filter.Tendsto.congr' hevent hleft
  exact tendsto_nhds_unique hleft' hright

end DifferentialGeometry.CheegerGromovCompactness

end
