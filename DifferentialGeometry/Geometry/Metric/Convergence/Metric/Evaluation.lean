import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Algebra
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Continuity
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence
import Mathlib.Topology.MetricSpace.UniformConvergence

noncomputable section

namespace DifferentialGeometry.SmoothRiemannianMetric

open scoped Manifold ContDiff Topology
open CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

theorem tendstoUniformlyOn_inner
    {ι Q : Type*} {F : Filter ι} {S : Set Q}
    (gSeq : ι → Q → SmoothRiemannianMetric I M) (gLim : Q → SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (x : Q → M)
    (v w : (q : Q) → TangentSpace I (x q))
    (hbound : BddAbove ((fun q =>
      Real.sqrt (gRef.inner (x q) (v q) (v q)) *
        Real.sqrt (gRef.inner (x q) (w q) (w q))) '' S))
    (hconv : TendstoUniformlyOn
      (fun i q => metricDerivNorm 0 (gSeq i q) (gLim q) gRef (x q)) (fun _ => 0) F S) :
    TendstoUniformlyOn (fun i q => (gSeq i q).inner (x q) (v q) (w q))
      (fun q => (gLim q).inner (x q) (v q) (w q)) F S := by
  obtain ⟨C, hC⟩ := hbound
  let B : ℝ := max 0 C + 1
  have hB : 0 < B := by
    dsimp only [B]
    linarith [le_max_left (0 : ℝ) C]
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hc := Metric.tendstoUniformlyOn_iff.mp hconv (ε / B) (div_pos hε hB)
  filter_upwards [hc] with i hi
  intro q hq
  have hn : 0 ≤ metricDerivNorm 0 (gSeq i q) (gLim q) gRef (x q) := Real.sqrt_nonneg _
  have hsmall : metricDerivNorm 0 (gSeq i q) (gLim q) gRef (x q) < ε / B := by
    simpa only [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hn] using hi q hq
  have hprod : Real.sqrt (gRef.inner (x q) (v q) (v q)) *
      Real.sqrt (gRef.inner (x q) (w q) (w q)) ≤ B :=
    (hC ⟨q, hq, rfl⟩).trans
      ((le_max_right 0 C).trans (le_add_of_nonneg_right zero_le_one))
  rw [Real.dist_eq, abs_sub_comm]
  calc
    |(gSeq i q).inner (x q) (v q) (w q) - (gLim q).inner (x q) (v q) (w q)| ≤
        metricDerivNorm 0 (gSeq i q) (gLim q) gRef (x q) *
          (Real.sqrt (gRef.inner (x q) (v q) (v q)) *
            Real.sqrt (gRef.inner (x q) (w q) (w q))) := by
      simpa only [mul_assoc] using metricDifference_abs_le (gSeq i q) (gLim q) gRef (x q) (v q) (w q)
    _ ≤ metricDerivNorm 0 (gSeq i q) (gLim q) gRef (x q) * B :=
      mul_le_mul_of_nonneg_left hprod hn
    _ < ε := (lt_div_iff₀ hB).mp hsmall

theorem tendstoUniformlyOn_inner_of_isCompact
    {ι Q : Type*} [TopologicalSpace Q] {F : Filter ι} {S : Set Q}
    (gSeq : ι → Q → SmoothRiemannianMetric I M) (gLim : Q → SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (x : Q → M)
    (v w : (q : Q) → TangentSpace I (x q))
    (hS : IsCompact S)
    (hv : ContinuousOn (fun q => Bundle.TotalSpace.mk' E (x q) (v q)) S)
    (hw : ContinuousOn (fun q => Bundle.TotalSpace.mk' E (x q) (w q)) S)
    (hconv : TendstoUniformlyOn
      (fun i q => metricDerivNorm 0 (gSeq i q) (gLim q) gRef (x q)) (fun _ => 0) F S) :
    TendstoUniformlyOn (fun i q => (gSeq i q).inner (x q) (v q) (w q))
      (fun q => (gLim q).inner (x q) (v q) (w q)) F S := by
  have hx : ContinuousOn x S := by
    intro q hq
    have h := hv q hq
    rw [FiberBundle.continuousWithinAt_totalSpace] at h
    exact h.1
  have hnorm (z : (q : Q) → TangentSpace I (x q))
      (hz : ContinuousOn (fun q => Bundle.TotalSpace.mk' E (x q) (z q)) S) :
      ContinuousOn (fun q => gRef.inner (x q) (z q) (z q)) S := by
    have h := (gRef.contMDiff.continuous.comp_continuousOn hx).clm_bundle_apply₂
      (F₁ := E) (F₂ := E) hz hz
    intro q hq
    have hh := h q hq
    simp only [FiberBundle.continuousWithinAt_totalSpace] at hh
    exact hh.2
  exact tendstoUniformlyOn_inner gSeq gLim gRef x v w
    (hS.bddAbove_image ((hnorm v hv).sqrt.mul (hnorm w hw).sqrt)) hconv

end DifferentialGeometry.SmoothRiemannianMetric

namespace DifferentialGeometry.CheegerGromovCompactness
open Set Filter
open scoped Manifold ContDiff Topology
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem MetricCPConvergenceOn.tendsto_inner
    {G : ℕ → SmoothRiemannianMetric I M} {g R : SmoothRiemannianMetric I M}
    {K : Set M} {p : ℕ} (hconv : MetricCPConvergenceOn K p G g R) (hK : IsCompact K)
    {x : M} (hx : x ∈ K) (v w : TangentSpace I x) :
    Tendsto (fun n => (G n).inner x v w) atTop (𝓝 (g.inner x v w)) := by
  let B := Real.sqrt (R.inner x v v) * Real.sqrt (R.inner x w w)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  apply Metric.tendsto_atTop.mpr
  intro e he
  obtain ⟨N, hN⟩ := hconv (e / (B + 1)) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hd := (derivNorm_le_sup hK (Nat.zero_le p) (G n) g R hx).trans_lt (hN n hn)
  have hbound := metricDifference_abs_le (G n) g R x v w
  rw [Real.dist_eq]
  have hprod : metricDerivNorm 0 (G n) g R x * (B + 1) < e :=
    (lt_div_iff₀ (by positivity : 0 < B + 1)).mp hd
  have hnonneg : 0 ≤ metricDerivNorm 0 (G n) g R x := Real.sqrt_nonneg _
  dsimp only [B] at hprod
  nlinarith [hbound]

variable {A : Type*} [PseudoMetricSpace A]

theorem metricCPConvergenceOn_of_uniform_approximation_of_lipschitz
    {G : ℕ → A → SmoothRiemannianMetric I M} {g : A → SmoothRiemannianMetric I M}
    (R : SmoothRiemannianMetric I M) {K : Set M} (hK : IsCompact K)
    {U : Set A} {p : ℕ} {L : ℝ} (hL : 0 ≤ L)
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i ≥ N, ∀ t ∈ U,
      metricDerivNormSupOn K p (G i t) (g t) R < ε)
    (hlip : ∀ s ∈ U, ∀ t ∈ U, ∀ q : ℕ, q ≤ p → ∀ x ∈ K,
      metricDerivNorm q (g s) (g t) R x ≤ L * dist s t)
    {t : ℕ → A} {a : A} (ht : ∀ᶠ i in atTop, t i ∈ U) (ha : a ∈ U)
    (hlim : Tendsto t atTop (𝓝 a)) :
    MetricCPConvergenceOn K p (fun i => G i (t i)) (g a) R := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  intro ε hε
  obtain ⟨N, hN⟩ := hconv (ε / 3) (by positivity)
  obtain ⟨N', hN'⟩ := Metric.tendsto_atTop.mp hlim (ε / (3 * (L + 1))) (by positivity)
  obtain ⟨N'', hN''⟩ := eventually_atTop.mp ht
  refine ⟨max N (max N' N''), fun i hi => ?_⟩
  have hti := hN'' i ((le_max_right N' N'').trans ((le_max_right _ _).trans hi))
  apply lt_of_le_of_lt (metricDerivNormSupOn_le_of_forall K p _ _ R (2 * ε / 3)
    (by positivity) ?_) (by linarith)
  intro q hq x hx
  have hsmall := (derivNorm_le_sup hK hq (G i (t i)) (g (t i)) R hx).trans_lt
    (hN i ((le_max_left _ _).trans hi) (t i) hti)
  have hdist := (lt_div_iff₀ (by positivity : 0 < 3 * (L + 1))).mp
    (hN' i ((le_max_left N' N'').trans ((le_max_right _ _).trans hi)))
  have htime := hlip (t i) hti a ha q hq x hx
  have htri := metricDerivNorm_triangle q (G i (t i)) (g (t i)) (g a) R x
  nlinarith [dist_nonneg (x := t i) (y := a)]

theorem metricCPConvergenceOn_at_terminal_times_of_time_lipschitz
    {G : ℕ → ℝ → SmoothRiemannianMetric I M} {g : ℝ → SmoothRiemannianMetric I M}
    (R : SmoothRiemannianMetric I M) {K : Set M} (hK : IsCompact K)
    {a b : ℝ} (hab : a < b) {p : ℕ} {L L' : ℝ} (hL : 0 ≤ L) (hL' : 0 ≤ L')
    (hconv : ∀ t ∈ Ico a b, MetricCPConvergenceOn K p (fun i => G i t) (g t) R)
    (hlip : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ q : ℕ, q ≤ p → ∀ x ∈ K,
      metricDerivNorm q (g s) (g t) R x ≤ L' * |s - t|)
    {time : ℕ → ℝ} (htime : Tendsto time atTop (𝓝 b))
    (hseq : ∀ᶠ i in atTop, ∀ s ∈ Icc a (time i), ∀ t ∈ Icc a (time i),
      ∀ q : ℕ, q ≤ p → ∀ x ∈ K,
        metricDerivNorm q (G i s) (G i t) R x ≤ L * |s - t|) :
    MetricCPConvergenceOn K p (fun i => G i (time i)) (g b) R := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  intro ε hε
  let δ := ε / (3 * (2 * L + L' + 1))
  have hden : 0 < 3 * (2 * L + L' + 1) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hbudget : (2 * L + L' + 1) * δ = ε / 3 := by
    dsimp only [δ]
    field_simp
  let c := max a (b - δ)
  have hac : a ≤ c := le_max_left _ _
  have hcb : c < b := max_lt hab (by linarith only [hδ])
  have hbc : b - c ≤ δ := by have := le_max_right a (b - δ); linarith only [this]
  obtain ⟨N₀, hN₀⟩ := hconv c ⟨hac, hcb⟩ (ε / 3) (by positivity)
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp htime δ hδ
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp
    (hseq.and (htime.eventually (Ioi_mem_nhds hcb)))
  refine ⟨max N₀ (max N₁ N₂), fun i hi => ?_⟩
  have hi₀ : N₀ ≤ i := (le_max_left _ _).trans hi
  have hi₁ : N₁ ≤ i := (le_max_left N₁ N₂).trans ((le_max_right _ _).trans hi)
  have hi₂ : N₂ ≤ i := (le_max_right N₁ N₂).trans ((le_max_right _ _).trans hi)
  have hdist : |time i - b| < δ := by simpa only [Real.dist_eq] using hN₁ i hi₁
  have hci : c < time i := (hN₂ i hi₂).2
  have hic : time i - c ≤ 2 * δ := by
    have hh := le_abs_self (time i - b)
    linarith only [hh, hdist, hbc]
  apply lt_of_le_of_lt (metricDerivNormSupOn_le_of_forall K p _ _ R (2 * ε / 3)
    (by positivity) ?_) (by linarith)
  intro q hq x hx
  have hmid := (derivNorm_le_sup hK hq (G i c) (g c) R hx).trans_lt (hN₀ i hi₀)
  have hfirst := (hN₂ i hi₂).1 (time i) ⟨hac.trans hci.le, le_rfl⟩ c ⟨hac, hci.le⟩ q hq x hx
  rw [abs_of_nonneg (sub_nonneg.mpr hci.le)] at hfirst
  have hlast := hlip c ⟨hac, hcb.le⟩ b ⟨hab.le, le_rfl⟩ q hq x hx
  rw [abs_of_nonpos (sub_nonpos.mpr hcb.le), neg_sub] at hlast
  have hbfirst := hfirst.trans (mul_le_mul_of_nonneg_left hic hL)
  have hblast := hlast.trans (mul_le_mul_of_nonneg_left hbc hL')
  have htri := metricDerivNorm_triangle q (G i (time i)) (G i c) (g b) R x
  have htri' := metricDerivNorm_triangle q (G i c) (g c) (g b) R x
  nlinarith only [htri, htri', hmid, hbfirst, hblast, hbudget, hδ]


end DifferentialGeometry.CheegerGromovCompactness
