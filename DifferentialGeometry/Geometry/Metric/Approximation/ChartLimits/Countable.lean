import DifferentialGeometry.Geometry.Metric.Approximation.ChartLimits.Basic
import DifferentialGeometry.Topology.Compactness.CountableSubsequence
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology



set_option autoImplicit false
noncomputable section

open Set Metric Filter
open scoped Topology UniformConvergence NNReal

namespace GC.MetricGeometry

private theorem exists_chart_limit_of_eventual_bilipschitz
    {A X : Type*} [MetricSpace A] [CompactSpace A] [MetricSpace X] [ProperSpace X]
    {Y : ℕ → Type*} [∀ n, MetricSpace (Y n)]
    (a : A) (p q : X) (o : ∀ n, Y n) (L C : ℝ≥0)
    {R ε : ℕ → ℝ} (F : ∀ n, PointedBallApprox (o n) p (R n) (ε n))
    (hR : Tendsto R atTop atTop) (hε : Tendsto ε atTop (𝓝 0))
    (c : ∀ n, A → Y n)
    (hcenter_mem : ∀ᶠ n in atTop, c n a ∈ closedBall (o n) (R n))
    (hcenter : Tendsto (fun n => (F n).extendToWholeSpace (c n a)) atTop (𝓝 q))
    (hbilip : ∀ᶠ n in atTop, LipschitzWith L (c n) ∧ AntilipschitzWith C (c n)) :
    ∃ (σ : ℕ → ℕ) (g : A → X), StrictMono σ ∧ LipschitzWith L g ∧
      AntilipschitzWith C g ∧ g a = q ∧
      (∀ n x, c (σ n) x ∈ closedBall (o (σ n)) (R (σ n))) ∧
      TendstoUniformly (fun n x => (F (σ n)).extendToWholeSpace (c (σ n) x)) g atTop ∧
      ∀ ρ : ℝ, (∀ᶠ n in atTop, ball (c n a) ρ ⊆ range (c n)) →
        ball q ρ ⊆ range g := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbilip
  obtain ⟨σ, g, hσ, hg, hg', hga, hmem, hconv, hcover⟩ :=
    exists_bilipschitz_chart_limit_of_approximations a p q (fun n => o (n + N)) L C
      (fun n => F (n + N)) (hR.comp (tendsto_add_atTop_nat N))
      (hε.comp (tendsto_add_atTop_nat N)) (fun n => c (n + N))
      ((tendsto_add_atTop_nat N).eventually hcenter_mem)
      (hcenter.comp (tendsto_add_atTop_nat N))
      (fun n => (hN (n + N) (Nat.le_add_left N n)).1)
      (fun n => (hN (n + N) (Nat.le_add_left N n)).2)
  refine ⟨fun n => σ n + N, g, fun i j hij => Nat.add_lt_add_right (hσ hij) N,
    hg, hg', hga, hmem, hconv, fun ρ hρ => ?_⟩
  exact hcover ρ ((tendsto_add_atTop_nat N).eventually hρ)


theorem exists_bilipschitz_chart_limits_of_approximations
    {ι : Type*} [Countable ι]
    {A : ι → Type*} [∀ a, MetricSpace (A a)] [∀ a, CompactSpace (A a)]
    {X : Type*} [MetricSpace X] [ProperSpace X]
    {Y : ℕ → Type*} [∀ n, MetricSpace (Y n)]
    (a₀ : ∀ a, A a) (p : X) (q : ι → X) (o : ∀ n, Y n) (L C : ι → ℝ≥0)
    {R ε : ℕ → ℝ} (F : ∀ n, PointedBallApprox (o n) p (R n) (ε n))
    (hR : Tendsto R atTop atTop) (hε : Tendsto ε atTop (𝓝 0))
    (c : ∀ n, ∀ a, A a → Y n)
    (hcenter_mem : ∀ a, ∀ᶠ n in atTop, c n a (a₀ a) ∈ closedBall (o n) (R n))
    (hcenter : ∀ a,
      Tendsto (fun n => (F n).extendToWholeSpace (c n a (a₀ a))) atTop (𝓝 (q a)))
    (hbilip : ∀ a, ∀ᶠ n in atTop,
      LipschitzWith (L a) (c n a) ∧ AntilipschitzWith (C a) (c n a)) :
    ∃ (φ : ℕ → ℕ) (g : ∀ a, A a → X), StrictMono φ ∧ ∀ a,
      LipschitzWith (L a) (g a) ∧ AntilipschitzWith (C a) (g a) ∧
      g a (a₀ a) = q a ∧
      (∀ᶠ k in atTop, ∀ x, c (φ k) a x ∈ closedBall (o (φ k)) (R (φ k))) ∧
      TendstoUniformly (fun k x => (F (φ k)).extendToWholeSpace (c (φ k) a x)) (g a) atTop ∧
      ∀ ρ : ℝ, (∀ᶠ n in atTop, ball (c n a (a₀ a)) ρ ⊆ range (c n a)) →
        ball (q a) ρ ⊆ range (g a) := by
  classical
  let f : ℕ → ∀ a, A a → X := fun n a x => (F n).extendToWholeSpace (c n a x)
  let P (a : ι) (g : A a → X) : Prop :=
    LipschitzWith (L a) g ∧ AntilipschitzWith (C a) g ∧ g (a₀ a) = q a ∧
      ∀ ρ : ℝ, (∀ᶠ n in atTop, ball (c n a (a₀ a)) ρ ⊆ range (c n a)) →
        ball (q a) ρ ⊆ range g
  have hex (a : ι) (σ : ℕ → ℕ) (hσ : StrictMono σ) :
      ∃ (τ : ℕ → ℕ) (g : A a → X), StrictMono τ ∧ P a g ∧
        (∀ k x, c (σ (τ k)) a x ∈ closedBall (o (σ (τ k))) (R (σ (τ k)))) ∧
        TendstoUniformly (fun k => f (σ (τ k)) a) g atTop := by
    obtain ⟨τ, g, hτ, hg, hg', hga, hmem, hconv, hcover⟩ :=
      exists_chart_limit_of_eventual_bilipschitz (a₀ a) p (q a) (fun n => o (σ n))
        (L a) (C a) (fun n => F (σ n)) (hR.comp hσ.tendsto_atTop)
        (hε.comp hσ.tendsto_atTop) (fun n => c (σ n) a)
        (hσ.tendsto_atTop.eventually (hcenter_mem a))
        ((hcenter a).comp hσ.tendsto_atTop) (hσ.tendsto_atTop.eventually (hbilip a))
    refine ⟨τ, g, hτ, ⟨hg, hg', hga, fun ρ hρ => ?_⟩, hmem, hconv⟩
    exact hcover ρ (hσ.tendsto_atTop.eventually hρ)
  have hdom (a : ι) : ∀ᶠ n in atTop, ∀ x, c n a x ∈ closedBall (o n) (R n) := by
    by_contra hnot
    have hfreq : ∃ᶠ n in atTop, ¬ ∀ x, c n a x ∈ closedBall (o n) (R n) := by
      simpa only [Filter.Frequently, not_not] using hnot
    obtain ⟨σ, hσ, hbad⟩ := extraction_of_frequently_atTop hfreq
    obtain ⟨τ, _, _, _, hmem, _⟩ := hex a σ hσ
    exact hbad (τ 0) (hmem 0)
  let u : ℕ → ∀ a, A a →ᵤ X := fun n a => UniformFun.ofFun (f n a)
  have hu : ∀ a (σ : ℕ → ℕ), StrictMono σ →
      ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ g : A a →ᵤ X,
        Tendsto (fun n => u (σ (τ n)) a) atTop (𝓝 g) := by
    intro a σ hσ
    obtain ⟨τ, g, hτ, _, _, hconv⟩ := hex a σ hσ
    exact ⟨τ, hτ, UniformFun.ofFun g, UniformFun.tendsto_iff_tendstoUniformly.mpr hconv⟩
  obtain ⟨φ, hφ, hlim⟩ := exists_subseq_tendsto_of_countable_coordinatewise_subseq u hu
  choose g hg using hlim
  refine ⟨φ, fun a => UniformFun.toFun (g a), hφ, fun a => ?_⟩
  have hconv : TendstoUniformly (fun n => f (φ n) a) (UniformFun.toFun (g a)) atTop :=
    UniformFun.tendsto_iff_tendstoUniformly.mp (hg a)
  obtain ⟨τ, g', hτ, hP, _, hconv'⟩ := hex a φ hφ
  have heq : UniformFun.toFun (g a) = g' := by
    funext x
    exact tendsto_nhds_unique ((hconv.tendsto_at x).comp hτ.tendsto_atTop)
      (hconv'.tendsto_at x)
  have hPg : P a (UniformFun.toFun (g a)) := by simpa only [heq] using hP
  exact ⟨hPg.1, hPg.2.1, hPg.2.2.1, hφ.tendsto_atTop.eventually (hdom a),
    hconv, hPg.2.2.2⟩

end GC.MetricGeometry
