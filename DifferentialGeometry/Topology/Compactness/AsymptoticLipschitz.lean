import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Topology.UniformSpace.UniformConvergence

set_option autoImplicit false
noncomputable section
open Filter Set Metric
open scoped Topology NNReal

namespace Metric

private theorem uniform_of_additive_bound {A X : Type*}
    [MetricSpace A] [CompactSpace A] [MetricSpace X]
    {f : ℕ → A → X} {g : A → X} {L : ℝ≥0} (hg : LipschitzWith L g)
    {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (hpoint : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hbound : ∀ n x y, dist (f n x) (f n y) ≤ L * dist x y + e n) :
    TendstoUniformly f g atTop := by
  rw [← tendstoUniformlyOn_univ]
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let δ := ε / (4 * ((L : ℝ) + 1))
  have hδ : 0 < δ := by positivity
  obtain ⟨c, _, hcfin, hcover⟩ := (isCompact_univ : IsCompact (Set.univ : Set A)).finite_cover_balls hδ
  have hcenters : ∀ᶠ n in atTop, ∀ x ∈ c, dist (f n x) (g x) < ε / 4 :=
    hcfin.eventually_all.mpr fun x _ =>
      Metric.tendsto_nhds.mp (hpoint x) (ε / 4) (by positivity)
  have hsmall : ∀ᶠ n in atTop, e n < ε / 4 :=
    he.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 4))
  have hscale : 2 * (L : ℝ) * δ < ε / 2 := by
    dsimp [δ]
    have hpos : 0 < (L : ℝ) + 1 := by positivity
    have hh : 2 * (L : ℝ) < 2 * ((L : ℝ) + 1) := by linarith
    field_simp
    nlinarith
  filter_upwards [hcenters, hsmall] with n hn hne x _
  obtain ⟨y, hyc, hxy⟩ := mem_iUnion₂.mp (hcover (mem_univ x))
  have hd : dist x y < δ := hxy
  have h1 := hbound n x y
  have h2 := hg.dist_le_mul y x
  have h3 := hn y hyc
  have htri := dist_triangle4 (g x) (g y) (f n y) (f n x)
  rw [dist_comm (g x) (g y), dist_comm (g y) (f n y),
    dist_comm (f n y) (f n x)] at htri
  rw [dist_comm y x] at h2
  have hmul := mul_le_mul_of_nonneg_left hd.le L.coe_nonneg
  linarith

theorem exists_uniformly_convergent_subsequence_of_asymptotic_lipschitz {A X : Type*}
    [MetricSpace A] [CompactSpace A] [MetricSpace X] [ProperSpace X]
    (a : A) (p : X) (L : ℝ≥0) (f : ℕ → A → X) (e : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0)) (hbase : Tendsto (fun n => f n a) atTop (𝓝 p))
    (hbound : ∀ n x y, dist (f n x) (f n y) ≤ L * dist x y + e n) :
    ∃ (σ : ℕ → ℕ) (g : A → X), StrictMono σ ∧ LipschitzWith L g ∧
      g a = p ∧ TendstoUniformly (fun n => f (σ n)) g atTop := by
  classical
  obtain ⟨B, hB⟩ := he.isCompact_insert_range.bddAbove
  have hBn (n : ℕ) : e n ≤ B := hB (mem_insert_of_mem _ (mem_range_self n))
  have hbase_dist : Tendsto (fun n => dist (f n a) p) atTop (𝓝 0) := by
    simpa only [dist_self] using hbase.dist (tendsto_const_nhds (x := p))
  obtain ⟨B₀, hB₀⟩ := hbase_dist.isCompact_insert_range.bddAbove
  have hB₀n (n : ℕ) : dist (f n a) p ≤ B₀ :=
    hB₀ (mem_insert_of_mem _ (mem_range_self n))
  obtain ⟨s, hs, hd⟩ := TopologicalSpace.exists_countable_dense A
  let : Countable s := hs.to_subtype
  let K (x : s) : Set X := closedBall p ((L : ℝ) * dist (x : A) a + B + B₀)
  have hcompact : IsCompact (Set.pi univ K) :=
    isCompact_univ_pi fun x => isCompact_closedBall p _
  obtain ⟨b, _, σ, hσ, hlim⟩ := hcompact.tendsto_subseq
    (x := fun n (x : s) => f n x) (by
      intro n x _
      have h := hbound n x a
      have htri := dist_triangle (f n x) (f n a) p
      change dist (f n x) p ≤ _
      linarith [hBn n, hB₀n n])
  have hb (x : s) : Tendsto (fun n => f (σ n) x) atTop (𝓝 (b x)) :=
    ((continuous_apply x).tendsto b).comp hlim
  have hbl : LipschitzWith L b := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := le_of_tendsto_of_tendsto ((hb x).dist (hb y))
      (tendsto_const_nhds.add (he.comp hσ.tendsto_atTop))
      (Eventually.of_forall fun n => hbound (σ n) x y)
    simpa only [add_zero, Subtype.dist_eq] using h
  let g : A → X := hd.extend b
  have hgc : Continuous g := (hd.uniformContinuous_extend hbl.uniformContinuous).continuous
  have hgq (x : s) : g x = b x := hd.extend_of_ind hbl.uniformContinuous x
  have hgl : LipschitzWith L g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    refine hd.denseRange_val.induction_on₂
      (p := fun x y : A => dist (g x) (g y) ≤ L * dist x y) ?_ ?_ x y
    · exact isClosed_le ((hgc.comp continuous_fst).dist (hgc.comp continuous_snd))
        (continuous_const.mul (continuous_fst.dist continuous_snd))
    · intro x y
      simpa only [hgq, Subtype.dist_eq] using hbl.dist_le_mul x y
  have hpoint (x : A) : Tendsto (fun n => f (σ n) x) atTop (𝓝 (g x)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let δ := ε / (4 * ((L : ℝ) + 1))
    have hδ : 0 < δ := by positivity
    obtain ⟨y, hy⟩ := hd.denseRange_val.exists_dist_lt x hδ
    have hsmall := (he.comp hσ.tendsto_atTop).eventually
      (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 4))
    have hyconv := Metric.tendsto_nhds.mp (hb y) (ε / 4) (by positivity)
    have hscale : 2 * (L : ℝ) * δ < ε / 2 := by
      dsimp [δ]
      have hpos : 0 < (L : ℝ) + 1 := by positivity
      field_simp
      nlinarith
    filter_upwards [hsmall, hyconv] with n hn hny
    dsimp only [Function.comp_def] at hn
    have h1 := hbound (σ n) x y
    have h2 := hgl.dist_le_mul (y : A) x
    have htri := dist_triangle4 (f (σ n) x) (f (σ n) y) (g y) (g x)
    rw [hgq y] at htri h2
    rw [dist_comm (y : A) x] at h2
    have hmul := mul_le_mul_of_nonneg_left hy.le L.coe_nonneg
    linarith
  refine ⟨σ, g, hσ, hgl, ?_, ?_⟩
  · exact tendsto_nhds_unique (hpoint a) (hbase.comp hσ.tendsto_atTop)
  · exact uniform_of_additive_bound hgl (he.comp hσ.tendsto_atTop) hpoint
      (fun n => hbound (σ n))

end Metric
