import DifferentialGeometry.Geometry.Metric.Approximation.ChartLimits.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Bases
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Topology.Algebra.Group.ContinuousDiv
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

set_option autoImplicit false
noncomputable section
open Set Metric Filter Topology
open scoped Topology NNReal
namespace GC.MetricGeometry

theorem exists_approximating_centers {X : Type*} [MetricSpace X]
    {Y : ℕ → Type*} [∀ i, MetricSpace (Y i)]
    (p q : X) (o : ∀ i, Y i) {R ε : ℕ → ℝ}
    (F : ∀ i, PointedBallApprox (o i) p (R i) (ε i))
    (hR : Tendsto R atTop atTop) (hε : Tendsto ε atTop (𝓝 0))
    {S : ℝ} (hS : 0 < S) (hq : q ∈ ball p S) :
    ∃ z : ∀ i, Y i,
      (q = p → ∀ i, z i = o i) ∧
      (∀ i, z i ∈ closedBall (o i) (R i) ∧ z i ∈ ball (o i) (S + 1)) ∧
      Tendsto (fun i => (F i).extendToWholeSpace (z i)) atTop (𝓝 q) := by
  classical
  have hbase (i : ℕ) : o i ∈ closedBall (o i) (R i) :=
    mem_closedBall_self ((F i).error_pos.trans (F i).error_lt_radius).le
  by_cases hqp : q = p
  · subst q
    refine ⟨o, fun _ _ => rfl, fun i => ⟨hbase i, mem_ball_self (by linarith)⟩, ?_⟩
    have hb (i : ℕ) : (F i).extendToWholeSpace (o i) = p := by
      rw [(F i).extendToWholeSpace_apply (o i) (hbase i)]
      exact (F i).basepoint
    exact Filter.Tendsto.congr (fun i => (hb i).symm) tendsto_const_nhds
  have hgood : ∀ᶠ i in atTop, dist q p ≤ R i - ε i ∧ 2 * ε i < 1 := by
    filter_upwards [hR.eventually (eventually_ge_atTop (dist q p + 1)),
      hε.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with i hi hi'
    constructor <;> linarith
  have hex (i : ℕ) (hi : dist q p ≤ R i - ε i ∧ 2 * ε i < 1) :
      ∃ z : Y i, z ∈ closedBall (o i) (R i) ∧ z ∈ ball (o i) (S + 1) ∧
        dist ((F i).extendToWholeSpace z) q < ε i := by
    obtain ⟨z, hz⟩ := (F i).coverage q hi.1
    have hrad := (F i).radial_lower z
    have htri := dist_triangle ((F i).toFun z) q p
    have hz' : dist ((F i).toFun z) q < ε i := by
      rw [dist_comm]
      exact hz
    have hq' : dist q p < S := hq
    refine ⟨z.val, z.property, ?_, ?_⟩
    · rw [mem_ball]
      linarith [hi.2]
    · rw [(F i).extendToWholeSpace_apply z.val z.property]
      exact hz'
  let z (i : ℕ) : Y i := if hi : dist q p ≤ R i - ε i ∧ 2 * ε i < 1
    then (hex i hi).choose else o i
  refine ⟨z, fun h => (hqp h).elim, ?_, ?_⟩
  · intro i
    by_cases hi : dist q p ≤ R i - ε i ∧ 2 * ε i < 1
    · have hzi : z i = (hex i hi).choose := dite_eq_left hi
      rw [hzi]
      exact ⟨(hex i hi).choose_spec.1, (hex i hi).choose_spec.2.1⟩
    · have hzi : z i = o i := dite_eq_right hi
      rw [hzi]
      exact ⟨hbase i, mem_ball_self (by linarith)⟩
  · apply Metric.tendsto_nhds.mpr
    intro δ hδ
    filter_upwards [hgood, hε.eventually (gt_mem_nhds hδ)] with i hi hiε
    have hzi : z i = (hex i hi).choose := dite_eq_left hi
    rw [hzi]
    exact (hex i hi).choose_spec.2.2.trans hiε

theorem exists_radial_ball_homeomorph {E X : Type*} [NormedAddCommGroup E]
    [MetricSpace X] {a : ℝ} (ha : 0 < a) (q : X)
    (g : closedBall (0 : E) (a / 8) → X)
    (hlip : LipschitzWith 2 g) (hanti : AntilipschitzWith 2 g)
    (hzero : g ⟨0, mem_closedBall_self (div_nonneg ha.le (by norm_num))⟩ = q)
    (hrad : ∀ w, dist (g w) q = ‖(w : E)‖)
    (hcov : ball q (a / 8) ⊆ range g) :
    ∃ e : ball (0 : E) (a / 16) ≃ₜ ball q (a / 16),
      (e ⟨0, mem_ball_self (div_pos ha (by norm_num))⟩ : X) = q ∧
      LipschitzWith 2 e ∧ AntilipschitzWith 2 e ∧
      ∀ w, (e w : X) = g ⟨w, closedBall_subset_closedBall (by linarith [ha])
        (ball_subset_closedBall w.property)⟩ := by
  let j : ball (0 : E) (a / 16) → closedBall (0 : E) (a / 8) :=
    fun w => ⟨w, closedBall_subset_closedBall (by linarith [ha])
      (ball_subset_closedBall w.property)⟩
  let f : ball (0 : E) (a / 16) → ball q (a / 16) := fun w =>
    ⟨g (j w), by
      rw [mem_ball, hrad]
      exact mem_ball_zero_iff.mp w.property⟩
  have hf : LipschitzWith 2 f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact hlip.dist_le_mul (j x) (j y)
  have hf' : AntilipschitzWith 2 f := by
    apply AntilipschitzWith.of_le_mul_dist
    intro x y
    exact hanti.le_mul_dist (j x) (j y)
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨w, hw⟩ := hcov (ball_subset_ball (by linarith [ha]) y.property)
    have hw' : (w : E) ∈ ball (0 : E) (a / 16) := by
      rw [mem_ball_zero_iff, ← hrad, hw]
      exact y.property
    refine ⟨⟨w, hw'⟩, ?_⟩
    apply Subtype.ext
    exact hw
  let e := (hf'.isEmbedding hf.continuous).toHomeomorphOfSurjective hsurj
  exact ⟨e, hzero, hf, hf', fun _ => rfl⟩

private theorem range_restrict_eq_ball_of_radial {E X : Type*} [NormedAddCommGroup E] [MetricSpace X]
    {R ρ : ℝ} (hρR : ρ ≤ R) (q : X)
    (g : closedBall (0 : E) R → X)
    (hrad : ∀ u, dist (g u) q = ‖(u : E)‖)
    (hcover : ball q ρ ⊆ range g) :
    range (fun u : ball (0 : E) ρ =>
      g ⟨u, (ball_subset_closedBall.trans (closedBall_subset_closedBall hρR)) u.property⟩)
      = ball q ρ := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    rw [mem_ball, hrad]
    exact mem_ball_zero_iff.mp u.property
  · intro hx
    obtain ⟨u, rfl⟩ := hcover hx
    have hu : (u : E) ∈ ball (0 : E) ρ := by
      rw [mem_ball_zero_iff, ← hrad]
      exact hx
    exact ⟨⟨u, hu⟩, rfl⟩

theorem exists_radial_openPartialHomeomorph_of_closedBall {E X : Type*} [NormedAddCommGroup E]
    [MetricSpace X] {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R)
    (q : X) (g : closedBall (0 : E) R → X) {L C : ℝ≥0}
    (hg : LipschitzWith L g) (hgi : AntilipschitzWith C g)
    (hrad : ∀ u, dist (g u) q = ‖(u : E)‖)
    (hcover : ball q ρ ⊆ range g) :
    ∃ e : OpenPartialHomeomorph E X,
      e.source = ball 0 ρ ∧ e.target = ball q ρ ∧
      LipschitzWith L (fun u : ball (0 : E) ρ => e u) ∧
      AntilipschitzWith C (fun u : ball (0 : E) ρ => e u) ∧
      ∀ u : ball (0 : E) ρ,
        e u = g ⟨u, (ball_subset_closedBall.trans (closedBall_subset_closedBall hρR))
          u.property⟩ := by
  let U : TopologicalSpace.Opens E := ⟨ball 0 ρ, isOpen_ball⟩
  let inc : U → closedBall (0 : E) R := fun u =>
    ⟨u, (ball_subset_closedBall.trans (closedBall_subset_closedBall hρR)) u.property⟩
  let f : U → X := g ∘ inc
  have hfc : Continuous f := hg.continuous.comp (continuous_subtype_val.subtype_mk _)
  have hfa : AntilipschitzWith C f := fun u v => hgi (inc u) (inc v)
  have hrange : range f = ball q ρ := range_restrict_eq_ball_of_radial hρR q g hrad hcover
  have hfo : IsOpenEmbedding f := by
    refine ⟨hfa.isEmbedding hfc, ?_⟩
    rw [hrange]
    exact isOpen_ball
  have hU : Nonempty U := ⟨⟨0, mem_ball_self hρ⟩⟩
  let a := U.openPartialHomeomorphSubtypeCoe hU
  let b := hfo.toOpenPartialHomeomorph f
  have hmap (u : ball (0 : E) ρ) : (a.symm.trans b) u = f u := by
    change f (a.symm (u : E)) = f u
    have he : a.symm (u : E) = u := a.left_inv (by simp [a])
    rw [he]
  have hsrc : (a.symm.trans b).source = ball 0 ρ := by
    have h1 := OpenPartialHomeomorph.trans_source a.symm b
    have h2 : a.symm.source = ball 0 ρ :=
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target U hU
    have h3 : b.source = univ := rfl
    rw [h1, h2, h3, Set.preimage_univ, Set.inter_univ]
  have htgt : (a.symm.trans b).target = ball q ρ := by
    have h1 := OpenPartialHomeomorph.trans_target a.symm b
    have h2 : a.symm.target = univ := rfl
    have h3 : b.target = ball q ρ := Set.image_univ.trans hrange
    rw [h1, h2, Set.preimage_univ, Set.inter_univ, h3]
  refine ⟨a.symm.trans b, hsrc, htgt, ?_, ?_, hmap⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [hmap x, hmap y]
    exact hg.dist_le_mul (inc x) (inc y)
  · apply AntilipschitzWith.of_le_mul_dist
    intro x y
    rw [hmap x, hmap y]
    exact hgi.le_mul_dist (inc x) (inc y)

theorem dist_eq_norm_of_radial_chart_limit {E X : Type*} [NormedAddCommGroup E]
    [MetricSpace X] {Y : ℕ → Type*} [∀ i, MetricSpace (Y i)] {a : ℝ}
    (u₀ : closedBall (0 : E) a) (p q : X) (o : ∀ i, Y i) {R ε : ℕ → ℝ}
    (F : ∀ i, PointedBallApprox (o i) p (R i) (ε i))
    (hε : Tendsto ε atTop (𝓝 0)) (c : ∀ i, closedBall (0 : E) a → Y i)
    (g : closedBall (0 : E) a → X) (hzero : g u₀ = q)
    (hmem : ∀ᶠ i in atTop, ∀ v, c i v ∈ closedBall (o i) (R i))
    (hconv : TendstoUniformly (fun i v => (F i).extendToWholeSpace (c i v)) g atTop)
    (hrad : ∀ i v, dist (c i v) (c i u₀) = ‖(v : E)‖) (v : closedBall (0 : E) a) :
    dist (g v) q = ‖(v : E)‖ := by
  have hdist : Tendsto (fun i => dist ((F i).extendToWholeSpace (c i v))
      ((F i).extendToWholeSpace (c i u₀))) atTop (𝓝 (dist (g v) q)) := by
    have h := (hconv.tendsto_at v).dist (hconv.tendsto_at u₀)
    rw [hzero] at h
    exact h
  have hbd : ∀ᶠ i in atTop, |dist ((F i).extendToWholeSpace (c i v))
      ((F i).extendToWholeSpace (c i u₀)) - ‖(v : E)‖| ≤ ε i := by
    filter_upwards [hmem] with i hi
    rw [(F i).extendToWholeSpace_apply _ (hi v), (F i).extendToWholeSpace_apply _ (hi u₀)]
    have hh := (F i).distortion ⟨c i v, hi v⟩ ⟨c i u₀, hi u₀⟩
    change |dist ((F i).toFun ⟨c i v, hi v⟩) ((F i).toFun ⟨c i u₀, hi u₀⟩) -
      dist (c i v) (c i u₀)| < ε i at hh
    rw [hrad i v] at hh
    exact hh.le
  have habs : |dist (g v) q - ‖(v : E)‖| ≤ 0 :=
    le_of_tendsto_of_tendsto (hdist.sub_const _).abs hε hbd
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm habs (abs_nonneg _)))

end GC.MetricGeometry
