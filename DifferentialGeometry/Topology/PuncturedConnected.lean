import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Piecewise
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.Separation.Basic

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology

theorem isPreconnected_compl_singleton_of_punctured_neighborhood
    {X : Type*} [TopologicalSpace X] [T1Space X] [PreconnectedSpace X]
    (p : X) {U : Set X} (hU : U ∈ 𝓝 p)
    (hc : IsConnected (U \ {p})) : IsPreconnected ({p}ᶜ : Set X) := by
  classical
  apply isPreconnected_of_forall_constant
  intro f hf x hx y hy
  obtain ⟨q, hq⟩ := hc.nonempty
  let g := Function.update f p (f q)
  have hfg (z : X) (hz : z ≠ p) : g z = f z := Function.update_of_ne hz _ _
  have hgU : ∀ z ∈ U, g z = f q := by
    intro z hz
    by_cases hzp : z = p
    · subst z
      simp [g]
    · rw [hfg z hzp]
      exact hc.isPreconnected.constant (hf.mono (by
        intro w hw
        exact hw.2)) ⟨hz, hzp⟩ hq
  have hg : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hzp : z = p
    · subst z
      apply continuousAt_const.congr
      exact Filter.eventuallyEq_of_mem hU fun z hz => (hgU z hz).symm
    · apply (continuousAt_update_of_ne hzp).mpr
      exact (hf z hzp).continuousAt (isOpen_compl_singleton.mem_nhds hzp)
  have hxy : g x = g y := IsPreconnected.constant isPreconnected_univ hg.continuousOn
    (mem_univ x) (mem_univ y)
  rwa [hfg x hx, hfg y hy] at hxy

theorem isPathConnected_compl_singleton_of_punctured_neighborhood
    {X : Type*} [TopologicalSpace X] [T1Space X] [PreconnectedSpace X]
    [LocallyPathConnectedSpace X] (p : X) {U : Set X} (hU : U ∈ 𝓝 p)
    (hc : IsConnected (U \ {p})) :
    IsPathConnected ({p}ᶜ : Set X) := by
  apply isOpen_compl_singleton.isConnected_iff_isPathConnected.mp
  obtain ⟨z, hz⟩ := hc.nonempty
  exact ⟨⟨z, hz.2⟩, isPreconnected_compl_singleton_of_punctured_neighborhood p hU hc⟩


theorem Metric.isPathConnected_ball_sdiff_singleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : 1 < Module.rank ℝ E) (x : E) {r : ℝ} (hr : 0 < r) :
    IsPathConnected (Metric.ball x r \ {x}) := by
  let e : OpenPartialHomeomorph E E := OpenPartialHomeomorph.univBall x r
  have heinj : Function.Injective e := by
    intro y z hyz
    exact e.injOn (by simp [e]) (by simp [e]) hyz
  have herange : Set.range e = Metric.ball x r := by
    simpa only [e, OpenPartialHomeomorph.univBall_source,
      OpenPartialHomeomorph.univBall_target x hr, Set.image_univ] using
      e.image_source_eq_target
  have heimage : e '' ({0}ᶜ : Set E) = Metric.ball x r \ {x} := by
    rw [Set.image_compl_eq_range_sdiff_image heinj, herange, Set.image_singleton]
    simp only [e, OpenPartialHomeomorph.univBall_apply_zero]
  rw [← heimage]
  exact (isPathConnected_compl_singleton_of_one_lt_rank h 0).image
    (OpenPartialHomeomorph.continuous_univBall x r)


noncomputable section

open Set
open scoped Topology

namespace DifferentialGeometry.Topology

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def normalize (w : E) : E := ‖w‖⁻¹ • w

private theorem norm_normalize {w : E} (hw : w ≠ 0) : ‖normalize w‖ = 1 := by
  rw [normalize, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg w)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]

private theorem normalize_eq_self {w : E} (hw : ‖w‖ = 1) : normalize w = w := by
  rw [normalize, hw, inv_one, one_smul]

private theorem continuousAt_normalize {w : E} (hw : w ≠ 0) : ContinuousAt normalize w := by
  have h : ContinuousAt (fun z : E => ‖z‖⁻¹) w :=
    continuous_norm.continuousAt.inv₀ (by simpa using hw)
  have h2 : ContinuousAt (fun z : E => ‖z‖⁻¹ • z) w := h.smul continuousAt_id
  exact h2

variable {M : Type*} [TopologicalSpace M]

private theorem image_closure_ball_eq (e : OpenPartialHomeomorph E M) [T2Space M] [ProperSpace E]
    (hball : Metric.closedBall 0 1 ⊆ e.source) :
    closure (e '' Metric.ball 0 1) = e '' Metric.closedBall 0 1 := by
  refine Subset.antisymm ?_ ?_
  · refine closure_minimal (Set.image_mono Metric.ball_subset_closedBall) ?_
    exact ((isCompact_closedBall (0 : E) 1).image_of_continuousOn
      (e.continuousOn_toFun.mono hball)).isClosed
  · rintro y ⟨z, hz, rfl⟩
    rw [_root_.mem_closure_iff]
    intro U hU hzU
    have hzcl : z ∈ closure (Metric.ball (0 : E) 1) := by
      rw [closure_ball (0 : E) one_ne_zero]
      exact hz
    have hzsrc : z ∈ e.source := hball hz
    have hopen : IsOpen (e.source ∩ e.toFun ⁻¹' U) :=
      e.continuousOn_toFun.isOpen_inter_preimage e.open_source hU
    have hzmem : z ∈ e.source ∩ e.toFun ⁻¹' U := ⟨hzsrc, hzU⟩
    obtain ⟨w, hw, hwb⟩ := _root_.mem_closure_iff.mp hzcl _ hopen hzmem
    exact ⟨e w, hw.2, ⟨w, hwb, rfl⟩⟩

private theorem closure_preimage_subset_preimage_closure {α : Type*} [TopologicalSpace α]
    {f : α → M} (hf : Continuous f) (s : Set M) : closure (f ⁻¹' s) ⊆ f ⁻¹' closure s := by
  intro a ha
  exact closure_mono (Set.image_preimage_subset f s) (mem_closure_image hf.continuousAt ha)

variable [T2Space M] [PreconnectedSpace M] [LocallyPathConnectedSpace M]
  [ProperSpace E]

theorem isPathConnected_compl_image_ball (e : OpenPartialHomeomorph E M)
    (hrank : 1 < Module.rank ℝ E) (hball : Metric.closedBall 0 1 ⊆ e.source) :
    IsPathConnected ((e '' Metric.ball 0 1)ᶜ : Set M) := by
  classical
  set B : Set M := e '' Metric.ball 0 1 with hB
  have hBopen : IsOpen B := by
    rw [hB]
    refine e.isOpen_image_of_subset_source Metric.isOpen_ball ?_
    intro w hw
    exact hball (Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hw)))
  have h0ball : (0 : E) ∈ Metric.ball 0 1 := Metric.mem_ball_self zero_lt_one
  have h0src : (0 : E) ∈ e.source := hball (Metric.mem_closedBall.mpr (by simp))
  set p : M := e 0 with hp
  have hpB : p ∈ B := ⟨0, h0ball, rfl⟩
  have hneigh : B ∈ 𝓝 p := hBopen.mem_nhds hpB
  have hdiff : B \ {p} = e '' (Metric.ball 0 1 \ {0}) := by
    rw [hB]
    refine Subset.antisymm ?_ ?_
    · rintro y ⟨⟨w, hw, rfl⟩, hy⟩
      refine ⟨w, ⟨hw, ?_⟩, rfl⟩
      rintro rfl
      exact hy (by simp [hp])
    · rintro y ⟨w, hw, rfl⟩
      refine ⟨⟨w, hw.1, rfl⟩, ?_⟩
      intro hy
      have hwsrc : w ∈ e.source :=
        hball (Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hw.1)))
      have hwe : e w = e 0 := by rw [Set.mem_singleton_iff.mp hy, hp]
      exact hw.2 (e.toPartialEquiv.injOn hwsrc h0src hwe)
  have hcon : IsConnected (B \ {p}) := by
    rw [hdiff]
    refine ((Metric.isPathConnected_ball_sdiff_singleton hrank 0 zero_lt_one).image' ?_).isConnected
    refine e.continuousOn_toFun.mono ?_
    intro w hw
    exact hball (Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hw.1)))
  have hcomp : IsPathConnected ({p}ᶜ : Set M) :=
    isPathConnected_compl_singleton_of_punctured_neighborhood p hneigh hcon
  have hnontriv : Nontrivial E := (rank_pos_iff_nontrivial (R := ℝ)).1 (zero_lt_one.trans hrank)
  obtain ⟨v, hv⟩ : ∃ v : E, v ≠ 0 := by
    obtain ⟨a, b, hab⟩ := hnontriv.exists_pair_ne
    by_cases ha : a = 0
    · exact ⟨b, fun hb => hab (by rw [ha, hb])⟩
    · exact ⟨a, ha⟩
  have hvn : ‖normalize v‖ = 1 := norm_normalize hv
  have hx0 : e (normalize v) ∈ Bᶜ := by
    rintro ⟨w, hw, hwe⟩
    have hwsrc : w ∈ e.source :=
      hball (Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hw)))
    have hnd : dist (normalize v) 0 = 1 := by rw [dist_eq_norm, sub_zero]; exact hvn
    have hnsrc : normalize v ∈ e.source := hball (Metric.mem_closedBall.mpr hnd.le)
    have hwinj : w = normalize v := e.toPartialEquiv.injOn hwsrc hnsrc hwe
    have hw1 : ‖w‖ = 1 := by rw [hwinj]; exact hvn
    exact absurd (Metric.mem_ball.mp hw) (by rw [dist_eq_norm, sub_zero, hw1]; norm_num)
  refine ⟨e (normalize v), hx0, ?_⟩
  intro y hy
  have hxp : e (normalize v) ≠ p := fun h => hx0 (h ▸ hpB)
  have hyp : y ≠ p := fun h => hy (h ▸ hpB)
  obtain ⟨δ, hδ⟩ := hcomp.joinedIn (e (normalize v)) hxp y hyp
  have hδp : ∀ t, δ t ≠ p := fun t => hδ t
  have hSopen : IsOpen (δ ⁻¹' B) := hBopen.preimage δ.continuous
  have hclosureB : closure B = e '' Metric.closedBall 0 1 := image_closure_ball_eq e hball
  let G : unitInterval → M := fun t => e (normalize (e.symm (δ t)))
  have hGfront : ∀ t ∈ frontier (δ ⁻¹' B), G t = δ t := by
    intro t ht
    have htcl : t ∈ closure (δ ⁻¹' B) := frontier_subset_closure ht
    have htint : t ∉ interior (δ ⁻¹' B) :=
      fun h => Set.disjoint_left.mp disjoint_interior_frontier h ht
    have hδcl : δ t ∈ closure B :=
      closure_preimage_subset_preimage_closure δ.continuous B htcl
    rw [hclosureB] at hδcl
    obtain ⟨z, hz, hze⟩ := hδcl
    have hzsrc : z ∈ e.source := hball hz
    have hzB : δ t ∉ B := by
      intro hmem
      rw [hSopen.interior_eq] at htint
      exact htint hmem
    have hznorm : ‖z‖ = 1 := by
      have hle : ‖z‖ ≤ 1 := by
        have h := Metric.mem_closedBall.mp hz
        rwa [dist_eq_norm, sub_zero] at h
      have hlt : ¬ (‖z‖ < 1) := by
        intro hlt
        refine hzB ⟨z, ?_, hze⟩
        rw [Metric.mem_ball, dist_eq_norm, sub_zero]
        exact hlt
      linarith
    have hsymm : e.symm (δ t) = z := by
      rw [← hze]
      exact e.left_inv hzsrc
    have hGt : G t = e z := by
      rw [show G t = e (normalize (e.symm (δ t))) from rfl, hsymm, normalize_eq_self hznorm]
    rw [hGt, hze]
  have hGcont : ContinuousOn G (closure (δ ⁻¹' B)) := by
    intro t ht
    have hδcl : δ t ∈ closure B :=
      closure_preimage_subset_preimage_closure δ.continuous B ht
    rw [hclosureB] at hδcl
    obtain ⟨z, hz, hze⟩ := hδcl
    have hzsrc : z ∈ e.source := hball hz
    have htgt : δ t ∈ e.target := hze ▸ e.mapsTo hzsrc
    have hsymm : e.symm (δ t) = z := by
      rw [← hze]
      exact e.left_inv hzsrc
    have hz0 : e.symm (δ t) ≠ 0 := by
      intro h0
      refine hδp t ?_
      have hpt : δ t = e 0 := by
        rw [← hze, ← hsymm, h0]
      rw [hpt, hp]
    have h1 : ContinuousAt (fun t' : unitInterval => e.symm (δ t')) t :=
      (e.continuousOn_symm.continuousAt (e.open_target.mem_nhds htgt)).comp
        δ.continuous.continuousAt
    have h2 : ContinuousAt (fun t' : unitInterval => normalize (e.symm (δ t'))) t :=
      ContinuousAt.comp (f := fun t' : unitInterval => e.symm (δ t')) (x := t)
        (continuousAt_normalize hz0) h1
    have hnsrc : normalize (e.symm (δ t)) ∈ e.source := by
      refine hball (Metric.mem_closedBall.mpr (le_of_eq ?_))
      rw [dist_eq_norm, sub_zero, hsymm]
      exact norm_normalize (by rw [← hsymm]; exact hz0)
    have h3 : ContinuousAt (fun t' : unitInterval => e (normalize (e.symm (δ t')))) t :=
      ContinuousAt.comp (f := fun t' : unitInterval => normalize (e.symm (δ t'))) (x := t)
        (e.continuousOn_toFun.continuousAt (e.open_source.mem_nhds hnsrc)) h2
    exact h3.continuousWithinAt
  have hmem : ∀ t, ((δ ⁻¹' B).piecewise G δ) t ∈ Bᶜ := by
    intro t
    by_cases ht : t ∈ δ ⁻¹' B
    · rw [Set.piecewise_eq_of_mem _ _ _ ht]
      rintro ⟨w', hw', hwe'⟩
      obtain ⟨w, hw, hwe⟩ := ht
      have hwsrc : w ∈ e.source :=
        hball (Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hw)))
      have hsymm : e.symm (δ t) = w := by
        rw [← hwe]
        exact e.left_inv hwsrc
      have hw0 : w ≠ 0 := by
        intro h0
        refine hδp t ?_
        rw [← hwe, h0, hp]
      have hn1 : ‖normalize (e.symm (δ t))‖ = 1 := by
        rw [hsymm]
        exact norm_normalize hw0
      have hnsrc : normalize (e.symm (δ t)) ∈ e.source :=
        hball (Metric.mem_closedBall.mpr (le_of_eq (by rw [dist_eq_norm, sub_zero]; exact hn1)))
      have hw'src : w' ∈ e.source :=
        hball (Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hw')))
      have hwinj : w' = normalize (e.symm (δ t)) := e.toPartialEquiv.injOn hw'src hnsrc hwe'
      have hw'1 : ‖w'‖ = 1 := by rw [hwinj]; exact hn1
      exact absurd (Metric.mem_ball.mp hw') (by rw [dist_eq_norm, sub_zero, hw'1]; norm_num)
    · rw [Set.piecewise_eq_of_notMem _ _ _ ht]
      exact ht
  have hcont : Continuous ((δ ⁻¹' B).piecewise G δ) :=
    continuous_piecewise hGfront hGcont δ.continuous.continuousOn
  have hsrc : ((δ ⁻¹' B).piecewise G δ) 0 = e (normalize v) := by
    have h0 : (0 : unitInterval) ∉ δ ⁻¹' B := by
      intro h0
      exact hx0 (by simpa only [Set.mem_preimage, δ.source] using h0)
    rw [Set.piecewise_eq_of_notMem _ _ _ h0]
    exact δ.source
  have htgt : ((δ ⁻¹' B).piecewise G δ) 1 = y := by
    have h1 : (1 : unitInterval) ∉ δ ⁻¹' B :=
      fun h => hy (by simpa only [Set.mem_preimage, δ.target] using h)
    rw [Set.piecewise_eq_of_notMem _ _ _ h1]
    exact δ.target
  exact ⟨Path.mk ⟨_, hcont⟩ hsrc htgt, hmem⟩

end Generic


end DifferentialGeometry.Topology
