import DifferentialGeometry.Topology.Manifold.NormalOrientation

set_option autoImplicit false

open Filter Set Topology

noncomputable section

universe u v

namespace DifferentialGeometry.Topology

theorem continuousAt_realNormalSide {t : ℝ} (ht : t ≠ 0) :
    ContinuousAt realNormalSide t := by
  apply (continuousAt_const (y := realNormalSide t)).congr_of_eventuallyEq
  rcases lt_or_gt_of_ne ht with ht | ht
  · filter_upwards [Iio_mem_nhds ht] with s hs
    rw [realNormalSide_eq_true_of_neg hs, realNormalSide_eq_true_of_neg ht]
  · filter_upwards [Ioi_mem_nhds ht] with s hs
    rw [realNormalSide_eq_false_of_pos hs, realNormalSide_eq_false_of_pos ht]

namespace OpenPartialHomeomorph

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (e : OpenPartialHomeomorph (X × ℝ) (Y × ℝ))
  (hzero : ∀ q ∈ e.source, (e q).2 = 0 ↔ q.2 = 0)

noncomputable def extendedNormalParity (q : e.source) : Bool :=
  if ht : q.val.2 = 0 then
    normalSideFlipAt e hzero ⟨q.val.1, by
      have heq : (q.val.1, (0 : ℝ)) = q.val := Prod.ext rfl ht.symm
      change (q.val.1, (0 : ℝ)) ∈ e.source
      rw [heq]
      exact q.property⟩
  else Bool.xor (realNormalSide q.val.2) (realNormalSide (e q.val).2)

theorem extendedNormalParity_of_ne_zero (q : e.source) (ht : q.val.2 ≠ 0) :
    extendedNormalParity e hzero q =
      Bool.xor (realNormalSide q.val.2) (realNormalSide (e q.val).2) := by
  simp only [extendedNormalParity, dif_neg ht]

theorem extendedNormalParity_zero (x : X) (hx : (x, 0) ∈ e.source) :
    extendedNormalParity e hzero ⟨(x, 0), hx⟩ =
      normalSideFlipAt e hzero ⟨x, hx⟩ := by
  simp [extendedNormalParity]

private theorem continuousAt_extendedNormalParity_zero (x : X) (hx : (x, 0) ∈ e.source) :
    ContinuousAt (extendedNormalParity e hzero) ⟨(x, 0), hx⟩ := by
  let flip := normalSideFlipAt e hzero ⟨x, hx⟩
  have hflip := hasNormalSideFlipAt_normalSideFlipAt e hzero ⟨x, hx⟩
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp hflip
  have hnear : ∀ᶠ q : e.source in 𝓝 ⟨(x, 0), hx⟩, q.val ∈ U :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (hUopen.mem_nhds hxU)
  have heq : extendedNormalParity e hzero =ᶠ[𝓝 (⟨(x, 0), hx⟩ : e.source)]
      fun _ => flip := by
    filter_upwards [hnear] with q hqU
    by_cases ht : q.val.2 = 0
    · have hqeq : (q.val.1, (0 : ℝ)) = q.val := Prod.ext rfl ht.symm
      have hqsource : (q.val.1, (0 : ℝ)) ∈ e.source := by rw [hqeq]; exact q.property
      have hqUzero : (q.val.1, (0 : ℝ)) ∈ U := by rw [hqeq]; exact hqU
      have hcandidate : HasNormalSideFlipAt e q.val.1 flip := by
        apply mem_of_superset (hUopen.mem_nhds hqUzero)
        intro p hp
        exact hUsub hp
      have hcanonical := hasNormalSideFlipAt_normalSideFlipAt e hzero
        ⟨q.val.1, hqsource⟩
      have hparity := (existsUnique_hasNormalSideFlipAt e hqsource hzero).unique
        hcanonical hcandidate
      have hqsub : q = ⟨(q.val.1, 0), hqsource⟩ := Subtype.ext hqeq.symm
      rw [hqsub, extendedNormalParity_zero]
      exact hparity
    · rw [extendedNormalParity_of_ne_zero e hzero q ht]
      have hside := (hUsub hqU ht).2
      rw [hside, ← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]
  exact continuousAt_const.congr_of_eventuallyEq heq

theorem continuous_extendedNormalParity : Continuous (extendedNormalParity e hzero) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  by_cases ht : q.val.2 = 0
  · have hqeq : (q.val.1, (0 : ℝ)) = q.val := Prod.ext rfl ht.symm
    have hqsource : (q.val.1, (0 : ℝ)) ∈ e.source := by rw [hqeq]; exact q.property
    have hqsub : q = ⟨(q.val.1, 0), hqsource⟩ := Subtype.ext hqeq.symm
    rw [hqsub]
    exact continuousAt_extendedNormalParity_zero e hzero q.val.1 hqsource
  · have hout : (e q.val).2 ≠ 0 := fun hz => ht ((hzero q.val q.property).mp hz)
    have hfirst : ContinuousAt (fun p : e.source => realNormalSide p.val.2) q :=
      (continuousAt_realNormalSide ht).comp
        (f := fun p : e.source => p.val.2)
        (continuous_snd.comp continuous_subtype_val).continuousAt
    have hsecond : ContinuousAt (fun p : e.source => realNormalSide (e p.val).2) q :=
      (continuousAt_realNormalSide hout).comp
        (f := fun p : e.source => (e p.val).2)
        (((e.continuousAt q.property).comp continuous_subtype_val.continuousAt).snd)
    have hxor : Continuous (fun p : Bool × Bool => Bool.xor p.1 p.2) :=
      continuous_of_discreteTopology
    have hbase := hxor.continuousAt.comp (hfirst.prodMk hsecond)
    apply hbase.congr_of_eventuallyEq
    have hnear : ∀ᶠ p : e.source in 𝓝 q, p.val.2 ≠ 0 :=
      (continuous_snd.comp continuous_subtype_val).continuousAt.eventually_ne ht
    filter_upwards [hnear] with p hp
    exact extendedNormalParity_of_ne_zero e hzero p hp

end OpenPartialHomeomorph

end DifferentialGeometry.Topology
