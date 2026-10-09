import DifferentialGeometry.Topology.Compactness.AsymptoticLipschitz
import DifferentialGeometry.Geometry.Metric.Approximation.PointedBallApproximation.Distance
import DifferentialGeometry.Geometry.Metric.Approximation.MarkedPointEvaluation
import Mathlib.Topology.MetricSpace.Antilipschitz

set_option autoImplicit false
noncomputable section
open Filter Set Metric
open scoped Topology NNReal
namespace GC.MetricGeometry

theorem exists_bilipschitz_chart_limit_of_approximations
    {A X : Type*} [MetricSpace A] [CompactSpace A] [MetricSpace X] [ProperSpace X]
    {Y : ℕ → Type*} [∀ n, MetricSpace (Y n)]
    (a : A) (p q : X) (o : ∀ n, Y n) (L C : ℝ≥0)
    {R ε : ℕ → ℝ} (F : ∀ n, PointedBallApprox (o n) p (R n) (ε n))
    (hR : Tendsto R atTop atTop) (hε : Tendsto ε atTop (𝓝 0))
    (c : ∀ n, A → Y n)
    (hcenter_mem : ∀ᶠ n in atTop, c n a ∈ closedBall (o n) (R n))
    (hcenter : Tendsto (fun n => (F n).extendToWholeSpace (c n a)) atTop (𝓝 q))
    (hc : ∀ n, LipschitzWith L (c n)) (hc' : ∀ n, AntilipschitzWith C (c n)) :
    ∃ (σ : ℕ → ℕ) (g : A → X), StrictMono σ ∧ LipschitzWith L g ∧
      AntilipschitzWith C g ∧ g a = q ∧
      (∀ n x, c (σ n) x ∈ closedBall (o (σ n)) (R (σ n))) ∧
      TendstoUniformly (fun n x => (F (σ n)).extendToWholeSpace (c (σ n) x)) g atTop ∧
      ∀ ρ : ℝ, (∀ᶠ n in atTop, ball (c n a) ρ ⊆ range (c n)) →
        ball q ρ ⊆ range g := by
  classical
  have hcenter_bound : ∀ᶠ n in atTop, dist (c n a) (o n) ≤ dist q p + 1 := by
    have ht : Tendsto (fun n => dist ((F n).extendToWholeSpace (c n a)) p + ε n)
        atTop (𝓝 (dist q p)) := by
      simpa only [add_zero] using (hcenter.dist tendsto_const_nhds).add hε
    filter_upwards [hcenter_mem, ht.eventually (gt_mem_nhds (by linarith :
      dist q p < dist q p + 1))] with n hn hsmall
    have h := (F n).radial_lower ⟨c n a, hn⟩
    rw [← (F n).extendToWholeSpace_apply _ hn] at h
    linarith
  have hdom : ∀ᶠ n in atTop, ∀ x, c n x ∈ closedBall (o n) (R n) := by
    filter_upwards [hcenter_bound,
      hR.eventually_ge_atTop ((L : ℝ) * diam (univ : Set A) + dist q p + 1)]
      with n hn hnR x
    have h1 := (hc n).dist_le_mul x a
    have h2 : dist x a ≤ diam (univ : Set A) :=
      Metric.dist_le_diam_of_mem
        (isCompact_univ : IsCompact (univ : Set A)).isBounded (mem_univ x) (mem_univ a)
    have h3 := mul_le_mul_of_nonneg_left h2 L.coe_nonneg
    have h4 := dist_triangle (c n x) (c n a) (o n)
    change dist (c n x) (o n) ≤ R n
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp hdom
  have hmem (n : ℕ) (x : A) : c (n + N) x ∈ closedBall (o (n + N)) (R (n + N)) :=
    hN (n + N) (Nat.le_add_left N n) x
  let f (n : ℕ) (x : A) := (F (n + N)).extendToWholeSpace (c (n + N) x)
  have hf0 : Tendsto (fun n => f n a) atTop (𝓝 q) :=
    hcenter.comp (tendsto_add_atTop_nat N)
  have hf (n : ℕ) (x y : A) : dist (f n x) (f n y) ≤ L * dist x y + ε (n + N) := by
    dsimp only [f]
    rw [(F (n + N)).extendToWholeSpace_apply _ (hmem n x),
      (F (n + N)).extendToWholeSpace_apply _ (hmem n y)]
    have h := (F (n + N)).dist_image_lt_add_error ⟨c (n + N) x, hmem n x⟩
      ⟨c (n + N) y, hmem n y⟩
    exact h.le.trans (add_le_add ((hc (n + N)).dist_le_mul x y) le_rfl)
  obtain ⟨σ, g, hσ, hg, hg0, hlim⟩ := Metric.exists_uniformly_convergent_subsequence_of_asymptotic_lipschitz a q L f
    (fun n => ε (n + N)) (hε.comp (tendsto_add_atTop_nat N)) hf0 hf
  let τ : ℕ → ℕ := fun n => σ n + N
  have hτ : StrictMono τ := fun i j hij => Nat.add_lt_add_right (hσ hij) N
  have hconv : TendstoUniformly (fun n x => (F (τ n)).extendToWholeSpace (c (τ n) x)) g atTop := hlim
  have hanti : AntilipschitzWith C g := by
    apply AntilipschitzWith.of_le_mul_dist
    intro x y
    have ht : Tendsto (fun n => (C : ℝ) *
        (dist ((F (τ n)).extendToWholeSpace (c (τ n) x)) ((F (τ n)).extendToWholeSpace (c (τ n) y)) + ε (τ n)))
        atTop (𝓝 ((C : ℝ) * dist (g x) (g y))) := by
      simpa only [add_zero, Function.comp_def] using
        (((hconv.tendsto_at x).dist (hconv.tendsto_at y)).add
          (hε.comp hτ.tendsto_atTop)).const_mul (C : ℝ)
    apply le_of_tendsto_of_tendsto tendsto_const_nhds ht
    apply Eventually.of_forall
    intro n
    have h := (F (τ n)).dist_lt_image_add_error ⟨c (τ n) x, hmem (σ n) x⟩
      ⟨c (τ n) y, hmem (σ n) y⟩
    rw [← (F (τ n)).extendToWholeSpace_apply _ (hmem (σ n) x),
      ← (F (τ n)).extendToWholeSpace_apply _ (hmem (σ n) y)] at h
    exact ((hc' (τ n)).le_mul_dist x y).trans
      (mul_le_mul_of_nonneg_left h.le C.coe_nonneg)
  refine ⟨τ, g, hτ, hg, hanti, hg0, fun n => hmem (σ n), hconv, ?_⟩
  intro ρ hcov y hy
  have hclosed : IsClosed (range g) := (isCompact_range hg.continuous).isClosed
  apply hclosed.closure_subset
  apply Metric.mem_closure_iff.mpr
  intro δ hδ
  have hyρ : dist y q < ρ := hy
  have hεsmall : ∀ᶠ n in atTop,
      ε (τ n) < δ / 2 ∧ ε (τ n) < (ρ - dist y q) / 4 ∧ ε (τ n) < 1 := by
    filter_upwards [(hε.comp hτ.tendsto_atTop).eventually
      (gt_mem_nhds (half_pos hδ)), (hε.comp hτ.tendsto_atTop).eventually
      (gt_mem_nhds (by linarith : (0 : ℝ) < (ρ - dist y q) / 4)),
      (hε.comp hτ.tendsto_atTop).eventually (gt_mem_nhds zero_lt_one)] with n h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hcenter_small : ∀ᶠ n in atTop,
      dist ((F (τ n)).extendToWholeSpace (c (τ n) a)) q < (ρ - dist y q) / 4 :=
    Metric.tendsto_nhds.mp (hcenter.comp hτ.tendsto_atTop) _ (by linarith)
  have hunif := Metric.tendstoUniformlyOn_iff.mp (hconv.tendstoUniformlyOn (s := univ))
    (δ / 2) (half_pos hδ)
  obtain ⟨n, hnε, hnR, hncov, hncenter, hnconv⟩ := (hεsmall.and
    (((hR.comp hτ.tendsto_atTop).eventually_ge_atTop (dist y p + 1)).and
    ((hτ.tendsto_atTop.eventually hcov).and (hcenter_small.and hunif)))).exists
  have hymem : y ∈ closedBall p (R (τ n) - ε (τ n)) := by
    rw [mem_closedBall]
    dsimp only [Function.comp_def] at hnR
    linarith [hnε.2.2]
  obtain ⟨z, hz⟩ := (F (τ n)).coverage y hymem
  have hzrad := (F (τ n)).dist_lt_image_add_error
    ⟨c (τ n) a, hmem (σ n) a⟩ z
  rw [← (F (τ n)).extendToWholeSpace_apply _ (hmem (σ n) a)] at hzrad
  have htri := dist_triangle4 ((F (τ n)).extendToWholeSpace (c (τ n) a)) q y ((F (τ n)).toFun z)
  have hzρ : (z : Y (τ n)) ∈ ball (c (τ n) a) ρ := by
    rw [mem_ball, dist_comm]
    rw [dist_comm q y] at htri
    linarith [hnε.2.1]
  obtain ⟨x, hx⟩ := hncov hzρ
  refine ⟨g x, mem_range_self x, ?_⟩
  have hnx := hnconv x (mem_univ x)
  rw [hx, (F (τ n)).extendToWholeSpace_apply _ z.property] at hnx
  have hd := dist_triangle y ((F (τ n)).toFun z) (g x)
  rw [dist_comm (g x) ((F (τ n)).toFun z)] at hnx
  linarith [hnε.1]

end GC.MetricGeometry
