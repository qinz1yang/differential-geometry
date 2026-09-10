import DifferentialGeometry.Topology.PlanarJordan.ArcAndSegment
import DifferentialGeometry.Topology.PlanarJordan.Regions
import DifferentialGeometry.Topology.PlanarJordan.ClosedInterior
import DifferentialGeometry.Topology.PlanarJordan.LocalSides
import DifferentialGeometry.Topology.Flow.ReturnArc
import DifferentialGeometry.Topology.Flow.ReturnBoundary

open Set Metric

namespace DifferentialGeometry.Topology.PlanarJordan

theorem exists_trapped_disk_of_transverse_return
    (φ : _root_.Flow ℝ ℂ) (σ : ℝ →ᵃ[ℝ] ℂ) {ε a b T : ℝ}
    (e : OpenPartialHomeomorph (ℝ × ℝ) ℂ)
    (hsource : e.source = Ioo (-ε) ε ×ˢ Ioo (-ε) ε)
    (he : ∀ p, e p = φ p.2 (σ p.1))
    (ha : a ∈ Ioo (-ε) ε) (hb : b ∈ Ioo (-ε) ε) (hT : 0 < T)
    (hreturn : φ T (σ a) = σ b)
    (hinj : InjOn (fun t ↦ φ t (σ a)) (Icc 0 T))
    (havoid : ∀ t ∈ Ioo 0 T, φ t (σ a) ∉ σ '' uIcc a b) :
    ∃ U : Set ℂ, IsOpen U ∧ IsConnected U ∧
      frontier U = (fun t ↦ φ t (σ a)) '' Icc 0 T ∪ segment ℝ (σ a) (σ b) ∧
      Nonempty (closedBall (0 : ℂ) 1 ≃ₜ closure U) ∧
      (IsForwardInvariant φ (closure U) ∨ IsForwardInvariant φ.reverse (closure U)) := by
  have hab : a ≠ b := by
    intro hab
    apply hT.ne
    apply hinj ⟨le_rfl, hT.le⟩ ⟨hT.le, le_rfl⟩
    simpa only [φ.map_zero_apply, hab] using hreturn.symm
  have hε : 0 < ε := by linarith [ha.1, ha.2]
  have hσ : Continuous σ := σ.continuous_of_finiteDimensional
  have hseg : σ '' uIcc a b = segment ℝ (σ a) (σ b) := by
    rw [← segment_eq_uIcc]
    exact image_segment ℝ σ a b
  obtain ⟨α, hα, hclose, hsimple, himage⟩ :=
    exists_simple_closed_curve_of_arc_and_segment (γ := fun t ↦ φ t (σ a)) hT
      (φ.continuous continuous_id continuous_const).continuousOn hinj (by
        simpa only [φ.map_zero_apply, hreturn, ← hseg] using havoid)
  simp only [φ.map_zero_apply, hreturn] at himage
  let C := (fun t ↦ φ t (σ a)) '' Icc 0 T ∪ σ '' uIcc a b
  have himageC : α '' Icc 0 1 = C := by rw [himage, ← hseg]
  obtain ⟨U, V, hU, hV, hconn, _, hUV, hcover, hfrU, hfrV, hcompact, _⟩ :=
    exists_regions_of_simple_closed_curve hα hclose hsimple
  have hdisk := nonempty_homeomorph_closedBall_closure
    hU hconn hcompact hα hclose hsimple hfrU
  rw [himageC] at hcover hfrU hfrV
  have hminmax : min a b < max a b := by
    rcases lt_or_gt_of_ne hab with hab | hba
    · simpa only [min_eq_left hab.le, max_eq_right hab.le] using hab
    · simpa only [min_eq_right hba.le, max_eq_left hba.le] using hba
  have hsmall {u : ℝ} (hu : u ∈ uIcc a b) : u ∈ Ioo (-ε) ε :=
    ⟨(lt_min ha.1 hb.1).trans_le hu.1, hu.2.trans_lt (max_lt ha.2 hb.2)⟩
  have hsrc : Ioo (min a b) (max a b) ×ˢ Ioo (-ε) ε ⊆ e.source := by
    intro p hp
    rw [hsource]
    exact ⟨hsmall ⟨hp.1.1.le, hp.1.2.le⟩, hp.2⟩
  have hdisj := DifferentialGeometry.Topology.Flow.disjoint_returnArc_flowBox_strip
    φ e hsource he ha hb hreturn havoid
  have hcurve (p : ℝ × ℝ) (hp : p ∈ Ioo (min a b) (max a b) ×ˢ Ioo (-ε) ε) :
      e p ∈ C ↔ p.2 = 0 := by
    constructor
    · rintro (harc | ⟨u, hu, heq⟩)
      · exact (disjoint_left.mp hdisj ⟨p, hp, rfl⟩ harc).elim
      · have hpu : (u, (0 : ℝ)) ∈ e.source := by
          rw [hsource]
          exact ⟨hsmall hu, neg_neg_of_pos hε, hε⟩
        have hequ : e p = e (u, 0) := by rw [he (u, 0), φ.map_zero_apply]; exact heq.symm
        exact congrArg Prod.snd (e.injOn (hsrc hp) hpu hequ)
    · intro hpzero
      apply Or.inr
      refine ⟨p.1, ⟨hp.1.1.le, hp.1.2.le⟩, ?_⟩
      rw [he, hpzero, φ.map_zero_apply]
  have hsides := flowBox_halves_in_opposite_regions hU hV hUV hcover hfrU hfrV
    e hminmax hε hsrc hcurve
  refine ⟨U, hU, hconn, ?_, hdisk, ?_⟩
  · simpa only [C, hseg] using hfrU
  rcases hsides with ⟨hpos, _⟩ | ⟨_, hneg⟩
  · apply Or.inl
    apply DifferentialGeometry.Topology.Flow.isForwardInvariant_of_returnArc_and_side
      φ hσ hab hε hreturn hfrU
    intro u hu t ht
    rw [← he (u, t)]
    exact hpos ⟨(u, t), ⟨hu, ht⟩, rfl⟩
  · apply Or.inr
    have hrev (t : ℝ) : φ.reverse t (σ b) = φ (T - t) (σ a) := by
      rw [φ.reverse_apply, ← hreturn, ← φ.map_add]
      congr 1
      ring
    have hrevreturn : φ.reverse T (σ b) = σ a := by
      rw [hrev, sub_self, φ.map_zero_apply]
    have hrevimage : (fun t ↦ φ.reverse t (σ b)) '' Icc 0 T =
        (fun t ↦ φ t (σ a)) '' Icc 0 T := by
      ext z
      constructor <;> rintro ⟨t, ht, rfl⟩
      · exact ⟨T - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, (hrev t).symm⟩
      · refine ⟨T - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
        simpa only [sub_sub_cancel] using hrev (T - t)
    apply DifferentialGeometry.Topology.Flow.isForwardInvariant_of_returnArc_and_side
      φ.reverse hσ hab.symm hε hrevreturn
      (by rw [hrevimage, uIcc_comm]; exact hfrU)
    intro u hu t ht
    rw [uIoo_comm] at hu
    rw [φ.reverse_apply, ← he (u, -t)]
    exact hneg ⟨(u, -t), ⟨hu, by constructor <;> linarith [ht.1, ht.2]⟩, rfl⟩

end DifferentialGeometry.Topology.PlanarJordan
