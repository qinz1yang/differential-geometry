import Mathlib.Analysis.Normed.Group.Basic
import DifferentialGeometry.Geometry.Metric.Approximation.MarkedPointEvaluation
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.Order.Compact



open Filter Set Metric Topology
open scoped NNReal
set_option autoImplicit false
noncomputable section
namespace GC.MetricGeometry

variable {ι E X : Type*} [NormedAddCommGroup E] [MetricSpace X]
  {l : Filter ι} {Y : ι → Type*} [∀ i, MetricSpace (Y i)]


theorem exists_chart_transition_limit_on_compact
    (p : X) (o : ∀ i, Y i) {R ε : ι → ℝ}
    (F : ∀ i, PointedBallApprox (o i) p (R i) (ε i))
    (hε : Tendsto ε l (𝓝 0))
    (a b : ∀ i, OpenPartialHomeomorph E (Y i))
    (α β : OpenPartialHomeomorph E X) (q : X) {ρ : ℝ} (hρ : 0 < ρ)
    (hβs : β.source = ball 0 ρ) (hβt : β.target = ball q ρ) (hβ0 : β 0 = q)
    (has : ∀ᶠ i in l, α.source ⊆ (a i).source)
    (hbrad : ∀ᶠ i in l, ∀ v, v ∈ (b i).source → dist (b i v) (b i 0) = ‖v‖)
    (hbcover : ∀ᶠ i in l, ball (b i 0) ρ ⊆ (b i).target)
    (hdom : ∀ᶠ i in l,
      (∀ u ∈ α.source, a i u ∈ closedBall (o i) (R i)) ∧
      (∀ v ∈ β.source, b i v ∈ closedBall (o i) (R i)))
    (ha : TendstoUniformlyOn (fun i u => (F i).extendToWholeSpace (a i u)) α l α.source)
    (hb : TendstoUniformlyOn (fun i v => (F i).extendToWholeSpace (b i v)) β l β.source)
    {C : ℝ≥0} (hβanti : AntilipschitzWith C (fun v : β.source => β v))
    (K : Set E) (hK : IsCompact K) (hKsub : K ⊆ (α.trans β.symm).source) :
    ∃ s : ℝ, 0 < s ∧ s < ρ ∧
      (∀ᶠ i in l, K ⊆ ((a i).trans (b i).symm).source ∧
        MapsTo (fun u => (b i).symm (a i u)) K (closedBall 0 s)) ∧
      TendstoUniformlyOn (fun i u => (b i).symm (a i u))
        (fun u => β.symm (α u)) l K := by
  have hKs : K ⊆ α.source := fun u hu => (hKsub hu).1
  have hKt : ∀ u ∈ K, α u ∈ β.target := fun u hu => (hKsub hu).2
  have h0 : (0 : E) ∈ β.source := hβs ▸ mem_ball_self hρ
  have hm : ∃ s₀ : ℝ, s₀ < ρ ∧ ∀ u ∈ K, dist (α u) q ≤ s₀ := by
    by_cases hne : K.Nonempty
    · obtain ⟨u, hu, hmax⟩ := hK.exists_isMaxOn hne
        (show ContinuousOn (fun u => dist (α u) q) K from
          fun u hu => ((α.continuousOn.mono hKs) u hu).dist tendsto_const_nhds)
      exact ⟨dist (α u) q, by simpa only [hβt, mem_ball] using hKt u hu, hmax⟩
    · exact ⟨0, hρ, fun u hu => (hne ⟨u, hu⟩).elim⟩
  obtain ⟨s₀, hs₀, hbound⟩ := hm
  let s := (max s₀ 0 + ρ) / 2
  have hs : 0 < s := by dsimp [s]; linarith [le_max_right s₀ 0]
  have hsρ : s < ρ := by dsimp [s]; have : max s₀ 0 < ρ := max_lt hs₀ hρ; linarith
  have hs₀s : s₀ < s := by dsimp [s]; linarith [le_max_left s₀ 0]
  let δ := (s - s₀) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hεsmall : ∀ᶠ i in l, ε i < δ := hε (gt_mem_nhds hδ)
  have hasmall := (Metric.tendstoUniformlyOn_iff.mp ha) δ hδ
  have hbsmall := (Metric.tendstoUniformlyOn_iff.mp hb) δ hδ
  have hbuf : ∀ᶠ i in l, K ⊆ ((a i).trans (b i).symm).source ∧
      MapsTo (fun u => (b i).symm (a i u)) K (closedBall 0 s) := by
    filter_upwards [has, hdom, hεsmall, hasmall, hbsmall, hbrad, hbcover]
      with i hsi hdi hei hai hbi hri hci
    have hdist (u : E) (hu : u ∈ K) : dist (a i u) (b i 0) < s := by
      have hd := (abs_lt.mp ((F i).distortion ⟨a i u, hdi.1 u (hKs hu)⟩
        ⟨b i 0, hdi.2 0 h0⟩)).1
      rw [← (F i).extendToWholeSpace_apply _ (hdi.1 u (hKs hu)),
        ← (F i).extendToWholeSpace_apply _ (hdi.2 0 h0)] at hd
      have htri := dist_triangle4 ((F i).extendToWholeSpace (a i u)) (α u) q ((F i).extendToWholeSpace (b i 0))
      have h1 := hai u (hKs hu)
      have h2 := hbi 0 h0
      rw [hβ0] at h2
      rw [dist_comm (α u)] at h1
      have hu' := hbound u hu
      dsimp [δ] at hei h1 h2
      change -ε i < dist ((F i).extendToWholeSpace (a i u))
        ((F i).extendToWholeSpace (b i 0)) - dist (a i u) (b i 0) at hd
      linarith
    have hmem (u : E) (hu : u ∈ K) : a i u ∈ (b i).target :=
      hci ((hdist u hu).trans hsρ)
    refine ⟨fun u hu => ⟨hsi (hKs hu), hmem u hu⟩, ?_⟩
    intro u hu
    have hv := (b i).map_target (hmem u hu)
    have hr := hri ((b i).symm (a i u)) hv
    rw [(b i).right_inv (hmem u hu)] at hr
    simpa only [mem_closedBall, dist_zero_right, ← hr] using (hdist u hu).le
  refine ⟨s, hs, hsρ, hbuf, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  let d := η / (2 * ((C : ℝ) + 1))
  have hd : 0 < d := by dsimp [d]; positivity
  filter_upwards [hbuf, Metric.tendstoUniformlyOn_iff.mp ha d hd,
    Metric.tendstoUniformlyOn_iff.mp hb d hd] with i hi hai hbi
  intro u hu
  have hit : a i u ∈ (b i).target := (hi.1 hu).2
  have hv : (b i).symm (a i u) ∈ β.source := by
    rw [hβs]
    exact (hi.2 hu).trans_lt hsρ
  have ht : β.symm (α u) ∈ β.source := β.map_target (hKt u hu)
  have hanti := hβanti.le_mul_dist ⟨β.symm (α u), ht⟩ ⟨(b i).symm (a i u), hv⟩
  have h1 := hai u (hKs hu)
  have h2 := hbi ((b i).symm (a i u)) hv
  rw [(b i).right_inv hit] at h2
  have htri := dist_triangle (α u) ((F i).extendToWholeSpace (a i u)) (β ((b i).symm (a i u)))
  rw [dist_comm (β ((b i).symm (a i u)))] at h2
  have hsum : dist (α u) (β ((b i).symm (a i u))) < 2 * d := by linarith
  have hprod : (C : ℝ) * (2 * d) < η := by
    dsimp [d]
    have hC : 0 ≤ (C : ℝ) := C.property
    field_simp
    nlinarith
  change dist (β.symm (α u)) ((b i).symm (a i u)) ≤
    (C : ℝ) * dist (β (β.symm (α u))) (β ((b i).symm (a i u))) at hanti
  rw [β.right_inv (hKt u hu)] at hanti
  exact hanti.trans_lt ((mul_le_mul_of_nonneg_left hsum.le C.property).trans_lt hprod)


private theorem compact_overlap_neighborhood [LocallyCompactSpace E]
    {K W : Set E} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ U : Set E, IsOpen U ∧ K ⊆ U ∧ IsCompact (closure U) ∧ closure U ⊆ W := by
  obtain ⟨V, hV, hKV, hVc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  obtain ⟨U, hU, hKU, hUV⟩ := hK.exists_isOpen_closure_subset
    ((hW.inter hV).mem_nhdsSet.mpr (subset_inter hKW hKV))
  exact ⟨U, hU, hKU, hVc.of_isClosed_subset isClosed_closure
    (fun x hx => subset_closure (hUV hx).2), fun x hx => (hUV hx).1⟩


theorem exists_buffered_chart_transition_limit [ProperSpace E]
    (p : X) (o : ∀ i, Y i) {R ε : ι → ℝ}
    (F : ∀ i, PointedBallApprox (o i) p (R i) (ε i))
    (hε : Tendsto ε l (𝓝 0))
    (a b : ∀ i, OpenPartialHomeomorph E (Y i))
    (α β : OpenPartialHomeomorph E X) (q : X) {ρ : ℝ} (hρ : 0 < ρ)
    (hβs : β.source = ball 0 ρ) (hβt : β.target = ball q ρ) (hβ0 : β 0 = q)
    (has : ∀ᶠ i in l, α.source ⊆ (a i).source)
    (hbrad : ∀ᶠ i in l, ∀ v, v ∈ (b i).source → dist (b i v) (b i 0) = ‖v‖)
    (hbcover : ∀ᶠ i in l, ball (b i 0) ρ ⊆ (b i).target)
    (hdom : ∀ᶠ i in l,
      (∀ u ∈ α.source, a i u ∈ closedBall (o i) (R i)) ∧
      (∀ v ∈ β.source, b i v ∈ closedBall (o i) (R i)))
    (ha : TendstoUniformlyOn (fun i u => (F i).extendToWholeSpace (a i u)) α l α.source)
    (hb : TendstoUniformlyOn (fun i v => (F i).extendToWholeSpace (b i v)) β l β.source)
    {C : ℝ≥0} (hβanti : AntilipschitzWith C (fun v : β.source => β v))
    (K : Set E) (hK : IsCompact K) (hKsub : K ⊆ (α.trans β.symm).source) :
    ∃ (U : Set E) (s : ℝ), IsOpen U ∧ K ⊆ U ∧ IsCompact (closure U) ∧
      closure U ⊆ (α.trans β.symm).source ∧ 0 < s ∧ s < ρ ∧
      IsCompact (closedBall (0 : E) s) ∧ closedBall (0 : E) s ⊆ β.source ∧
      (∀ᶠ i in l, closure U ⊆ ((a i).trans (b i).symm).source ∧
        MapsTo (fun u => (b i).symm (a i u)) (closure U) (closedBall 0 s)) ∧
      TendstoUniformlyOn (fun i u => (b i).symm (a i u))
        (fun u => β.symm (α u)) l (closure U) := by
  obtain ⟨U, hU, hKU, hUc, hUW⟩ := compact_overlap_neighborhood hK
    (α.trans β.symm).open_source hKsub
  obtain ⟨s, hs, hsρ, hbuf, hlim⟩ := exists_chart_transition_limit_on_compact p o F hε a b α β q hρ
    hβs hβt hβ0 has hbrad hbcover hdom ha hb hβanti (closure U) hUc hUW
  refine ⟨U, s, hU, hKU, hUc, hUW, hs, hsρ, isCompact_closedBall 0 s, ?_, hbuf, hlim⟩
  rw [hβs]
  exact closedBall_subset_ball hsρ

end GC.MetricGeometry
