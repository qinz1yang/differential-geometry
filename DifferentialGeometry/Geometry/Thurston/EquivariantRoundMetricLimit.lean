import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricNormalization
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.Compactness
import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.Scalar
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Algebra
import DifferentialGeometry.Geometry.Curvature.DimensionTwo.RicciScalar
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling

/-!
# The rescaled limit of a surface flow

Chapter 7, surface lemma U1, route (a), steps a6 and a7 (lane U1E2) of the design note D17
(`docs/geometrization/handoffs/20261004-design-u1-ricci-flow-core.md`, §3 and §7, with the errata
after review 17). For a Ricci flow `g(t)` on `[0, Tm)` write `ĝ(t) = g(t) / (2 (Tm - t))`.
The input is the conclusion of a5 on a terminal interval `[t₀, Tm)`, taken as hypotheses:
fixed-background bounds of all orders for `ĝ(t)` against `h = g(0)`, a uniform lower bound
`c h ≤ ĝ(t)`, and the decay `|R̂ - 2| ≤ C (Tm - t)^δ` of `R̂ = 2 (Tm - t) R`.

* `surfaceFlow_exists_normalized_limit` (a6): along `t_k = Tm - (Tm - t₀) / (k + 2)` the
  fixed-manifold extraction
  `exists_metric_subsequence_tendsto_on_compact_of_eventual_pointwise_lower` (with `K = univ`,
  `p = 2`) gives times `τ k → Tm` and a limit metric: the bilinear data of `ĝ(τ k)` converge
  pointwise and its first two derivatives converge uniformly.
* `surfaceFlow_limit_round_of_a5` (a7, with a rate): the scalar curvature passes to the limit
  (`exists_abs_metricScalarAt_sub_le`), so `R = 2` there and, in dimension two
  (`metricRm04StdAt_eq_scalar_div_two_of_finrank_eq_two`), the limit has sectional curvature one.
  The conclusion is that of D17's `a7_limit_round`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.CheegerGromovCompactness
open Filter Topology Set
open scoped Manifold ContDiff

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M] [Nonempty M]

theorem surfaceFlow_exists_normalized_limit {Tm : ℝ} (hTm : 0 < Tm)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 Tm hTm)) {t₀ : ℝ}
    (ht₀ : t₀ < Tm)
    (hbdd : ∀ q : ℕ, ∃ C : ℝ, ∀ t (ht : t ∈ Ico t₀ Tm), ∀ z,
      metricCovDerivNorm q
        (scaleMetric (1 / (2 * (Tm - t))) (normalizedSurfaceMetric_pos ht.2) (S.family.metric t))
        (S.family.metric 0) z ≤ C)
    (hlow : ∃ c : ℝ, 0 < c ∧ ∀ t (ht : t ∈ Ico t₀ Tm), ∀ x (v : TangentSpace I x),
      c * (S.family.metric 0).inner x v v ≤
        (scaleMetric (1 / (2 * (Tm - t))) (normalizedSurfaceMetric_pos ht.2)
          (S.family.metric t)).inner x v v) :
    ∃ (τ : ℕ → ℝ) (hτ : ∀ k, τ k ∈ Ico (max t₀ 0) Tm) (hlim : SmoothRiemannianMetric I M),
      Tendsto τ atTop (𝓝[<] Tm) ∧
      (∀ x (v w : TangentSpace I x), Tendsto (fun k => 1 / (2 * (Tm - τ k)) *
        (S.family.metric (τ k)).inner x v w) atTop (𝓝 (hlim.inner x v w))) ∧
      ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ a : ℕ, a ≤ 2 → ∀ x,
        metricDerivNorm a (scaleMetric (1 / (2 * (Tm - τ k)))
          (normalizedSurfaceMetric_pos (hτ k).2) (S.family.metric (τ k))) hlim
          (S.family.metric 0) x < ε := by
  set s₀ := max t₀ 0 with hs₀
  have hs₀T : s₀ < Tm := max_lt ht₀ hTm
  let tk : ℕ → ℝ := fun k => Tm - (Tm - s₀) / ((k : ℝ) + 2)
  have htk : ∀ k, tk k ∈ Ico s₀ Tm := by
    intro k
    have hk : (1 : ℝ) ≤ (k : ℝ) + 2 := by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have hpos : 0 < (Tm - s₀) / ((k : ℝ) + 2) := div_pos (by linarith) (by linarith)
    have hle : (Tm - s₀) / ((k : ℝ) + 2) ≤ Tm - s₀ := div_le_self (by linarith) hk
    exact ⟨by simp only [tk]; linarith, by simp only [tk]; linarith⟩
  have hmem : ∀ k, tk k ∈ Ico t₀ Tm := fun k =>
    ⟨le_trans (le_max_left _ _) (htk k).1, (htk k).2⟩
  let gSeq : ℕ → SmoothRiemannianMetric I M := fun k =>
    scaleMetric (1 / (2 * (Tm - tk k))) (normalizedSurfaceMetric_pos (hmem k).2)
      (S.family.metric (tk k))
  have hbdd' : ∀ q : ℕ, ∀ K' : Set M, IsCompact K' → ∃ C : ℝ, ∀ k : ℕ, ∀ z, z ∈ K' →
      metricCovDerivNorm (I := I) q (gSeq k) (S.family.metric 0) z ≤ C := by
    intro q K' _
    obtain ⟨C, hC⟩ := hbdd q
    exact ⟨C, fun k z _ => hC (tk k) (hmem k) z⟩
  have hlow' : ∀ x : M, ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, ∀ v : TangentSpace I x,
      c * (S.family.metric 0).inner x v v ≤ (gSeq k).inner x v v := by
    intro x
    obtain ⟨c, hc, hcl⟩ := hlow
    exact ⟨c, hc, Eventually.of_forall fun k v => hcl (tk k) (hmem k) x v⟩
  obtain ⟨phi, hphi, hlim, hconv, hderiv⟩ :=
    exists_metric_subsequence_tendsto_on_compact_of_eventual_pointwise_lower (I := I)
      inferInstance univ isCompact_univ 2 (S.family.metric 0) gSeq hbdd' hlow'
  refine ⟨fun k => tk (phi k), fun k => htk (phi k), hlim, ?_, ?_, ?_⟩
  · have hden : Tendsto (fun k : ℕ => (k : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    have hlimt : Tendsto tk atTop (𝓝 Tm) := by
      have h := (tendsto_const_nhds (x := Tm - s₀)).div_atTop hden
      simpa [tk] using (tendsto_const_nhds (x := Tm)).sub h
    refine tendsto_nhdsWithin_iff.mpr ⟨hlimt.comp hphi.tendsto_atTop, ?_⟩
    exact Eventually.of_forall fun k => (htk (phi k)).2
  · intro x v w
    have hc : Continuous fun T : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ => T v w :=
      (ContinuousLinearMap.apply ℝ ℝ w).continuous.comp
        (ContinuousLinearMap.apply ℝ (TangentSpace I x →L[ℝ] ℝ) v).continuous
    exact (hc.tendsto _).comp (hconv x)
  · intro ε hε
    obtain ⟨k₀, hk₀⟩ := hderiv ε hε
    exact ⟨k₀, fun k hk a ha x => hk₀ k hk a ha x (mem_univ x)⟩

theorem surfaceFlow_limit_round_of_a5 (hdim : Module.finrank ℝ E = 2) {Tm : ℝ} (hTm : 0 < Tm)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 Tm hTm))
    (hfixed : ∃ t₀ < Tm, (∀ q : ℕ, ∃ C : ℝ, ∀ t (ht : t ∈ Ico t₀ Tm), ∀ z,
        metricCovDerivNorm q
          (scaleMetric (1 / (2 * (Tm - t))) (normalizedSurfaceMetric_pos ht.2)
            (S.family.metric t)) (S.family.metric 0) z ≤ C) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ t (ht : t ∈ Ico t₀ Tm), ∀ x (v : TangentSpace I x),
        c * (S.family.metric 0).inner x v v ≤
          (scaleMetric (1 / (2 * (Tm - t))) (normalizedSurfaceMetric_pos ht.2)
            (S.family.metric t)).inner x v v)
    (hdecay : ∃ t₀ < Tm, ∃ C δ : ℝ, 0 < δ ∧ ∀ t ∈ Ico t₀ Tm, ∀ x,
      |S.scalar t x * (2 * (Tm - t)) - 2| ≤ C * (Tm - t) ^ δ) :
    ∃ (τ : ℕ → ℝ) (hlim : SmoothRiemannianMetric I M), (∀ k, 0 ≤ τ k) ∧
      Tendsto τ atTop (𝓝[<] Tm) ∧
      (∀ x (v w : TangentSpace I x), Tendsto (fun k => (1 / (2 * (Tm - τ k))) *
        (S.family.metric (τ k)).inner x v w) atTop (𝓝 (hlim.inner x v w))) ∧
      ∀ (y : M) (X Y : TangentSpace I y), metricRm04StandardAt hlim y X Y Y X =
        1 * (hlim.inner y X X * hlim.inner y Y Y - hlim.inner y X Y * hlim.inner y X Y) := by
  obtain ⟨t₀, ht₀, hbdd, c, hc, hlow⟩ := hfixed
  obtain ⟨t₁, ht₁, Cd, δ, hδ, hdec⟩ := hdecay
  obtain ⟨τ, hτ, hlim, hτT, hconv, hderiv⟩ :=
    surfaceFlow_exists_normalized_limit hTm S ht₀ hbdd ⟨c, hc, hlow⟩
  set g0 := S.family.metric 0
  let gk : ℕ → SmoothRiemannianMetric I M := fun k =>
    scaleMetric (1 / (2 * (Tm - τ k))) (normalizedSurfaceMetric_pos (hτ k).2)
      (S.family.metric (τ k))
  have hτt₀ : ∀ k, τ k ∈ Ico t₀ Tm := fun k =>
    ⟨le_trans (le_max_left _ _) (hτ k).1, (hτ k).2⟩
  obtain ⟨C₀, hC₀⟩ := hbdd 0
  obtain ⟨C₁, hC₁⟩ := hbdd 1
  obtain ⟨C₂, hC₂⟩ := hbdd 2
  set B := max (max C₀ C₁) C₂
  have hB : ∀ k y, ∀ a : ℕ, a ≤ 2 → metricCovDerivNorm (I := I) a (gk k) g0 y ≤ B := by
    intro k y a ha
    interval_cases a
    · exact (hC₀ (τ k) (hτt₀ k) y).trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact (hC₁ (τ k) (hτt₀ k) y).trans ((le_max_right _ _).trans (le_max_left _ _))
    · exact (hC₂ (τ k) (hτt₀ k) y).trans (le_max_right _ _)
  obtain ⟨k₁, hk₁⟩ := hderiv 1 one_pos
  have hBlim : ∀ y, ∀ a : ℕ, a ≤ 2 → metricCovDerivNorm (I := I) a hlim g0 y ≤ B + 1 := by
    intro y a ha
    have h := covNorm_le_add (I := I) a hlim (gk k₁) g0 y
    rw [metricDerivNorm_symm] at h
    linarith [hB k₁ y a ha, hk₁ k₁ le_rfl a ha y]
  have hlowk : ∀ k, ∀ y ∈ (univ : Set M), ∀ ξ : TangentSpace I y,
      c * g0.inner y ξ ξ ≤ (gk k).inner y ξ ξ := fun k y _ ξ => hlow (τ k) (hτt₀ k) y ξ
  have hlowlim : ∀ y ∈ (univ : Set M), ∀ ξ : TangentSpace I y,
      c * g0.inner y ξ ξ ≤ hlim.inner y ξ ξ := fun y _ ξ =>
    ge_of_tendsto (hconv y ξ ξ) (Eventually.of_forall fun k => hlowk k y (mem_univ y) ξ)
  obtain ⟨Csc, hCsc, hsc⟩ := exists_abs_metricScalarAt_sub_le g0 isCompact_univ c (B + 1) hc
  have hscal2 : ∀ y, metricScalarAt hlim y = 2 := by
    intro y
    have hto_lim : Tendsto (fun k => metricScalarAt (gk k) y) atTop
        (𝓝 (metricScalarAt hlim y)) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨k₀, hk₀⟩ := hderiv (ε / (3 * Csc)) (by positivity)
      refine ⟨k₀, fun k hk => ?_⟩
      rw [Real.dist_eq]
      have h := hsc (gk k) hlim (hlowk k) hlowlim
        (fun y _ a ha => (hB k y a ha).trans (by linarith)) (fun y _ a ha => hBlim y a ha) y
        (mem_univ y)
      have hsum : ∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q (gk k) hlim g0 y <
          ∑ _q ∈ Finset.range 3, ε / (3 * Csc) :=
        Finset.sum_lt_sum_of_nonempty ⟨0, by simp⟩ fun q hq =>
          hk₀ k hk q (by simp at hq; omega) y
      have h3 : ∑ _q ∈ Finset.range 3, ε / (3 * Csc) = ε / Csc := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp
        ring
      rw [h3] at hsum
      calc |metricScalarAt (gk k) y - metricScalarAt hlim y|
          ≤ Csc * ∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q (gk k) hlim g0 y := h
        _ < Csc * (ε / Csc) := mul_lt_mul_of_pos_left hsum hCsc
        _ = ε := by field_simp
    have hto_two : Tendsto (fun k => metricScalarAt (gk k) y) atTop (𝓝 2) := by
      have hgap : Tendsto (fun k => Tm - τ k) atTop (𝓝 0) := by
        have h := (tendsto_const_nhds (x := Tm)).sub (tendsto_nhdsWithin_iff.mp hτT).1
        simpa using h
      have hpow : Tendsto (fun k => Cd * (Tm - τ k) ^ δ) atTop (𝓝 0) := by
        have h := ((Real.continuousAt_rpow_const 0 δ (Or.inr hδ.le)).tendsto.comp hgap)
        rw [Real.zero_rpow hδ.ne'] at h
        simpa using (tendsto_const_nhds (x := Cd)).mul h
      have hev : ∀ᶠ k in atTop, t₁ ≤ τ k :=
        (tendsto_nhdsWithin_iff.mp hτT).1.eventually (Ici_mem_nhds ht₁)
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) ?_ hpow
      filter_upwards [hev] with k hk
      rw [Real.norm_eq_abs]
      have hscale : metricScalarAt (gk k) y = S.scalar (τ k) y * (2 * (Tm - τ k)) := by
        change metricScalarAt (scaleMetric _ _ (S.family.metric (τ k))) y = _
        rw [metricScalarAt_scaleMetric, one_div, inv_inv, mul_comm]
        rfl
      rw [hscale]
      exact hdec (τ k) ⟨hk, (hτ k).2⟩ y
    exact tendsto_nhds_unique hto_lim hto_two
  refine ⟨τ, hlim, fun k => le_trans (le_max_right _ _) (hτ k).1, hτT, hconv, ?_⟩
  intro y X Y
  rw [metricRm04StdAt_eq_scalar_div_two_of_finrank_eq_two hlim hdim y X Y Y X, hscal2 y,
    hlim.symm y Y X]
  ring

end GC.Geometry
