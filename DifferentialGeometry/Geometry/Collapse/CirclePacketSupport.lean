import DifferentialGeometry.Geometry.Collapse.CirclePacketFamily

/-!
# Closed supports of the circle cutoffs lie strictly inside the packet domain

Blueprint `master207A.tex`, LPA06 (A:30591–30592): "all cutoffs have closed supports strictly
within their smooth domains". For the circle packets of `exists_circle_packet_at_scale` the
cutoff `ζ` satisfies `ζ x ≠ 0 → x ∈ B(q, 200) ∧ ‖η x‖ < 9`, and the enclosure
`‖η x‖ < 100 → x ∈ B(q, 102)` holds on `B(q, 200)`. Hence the CLOSED support of `ζ` lies in
`{x ∈ B(q, 200) | ‖η x‖ ≤ 9}`, inside the bundle domain `{x ∈ B(q, 200) | ‖η x‖ < 100}`.

* `tsupport_subset_of_circle_packet` (metric kernel): any space, any `η` continuous on `B(q, 200)`;
  applied to the CF2 packets in `CirclePacketFamilyLate.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open scoped Topology

namespace DifferentialGeometry.Geometry.Collapse

/-- **Closed support of a circle cutoff (kernel).** -/
theorem tsupport_subset_of_circle_packet {M F : Type*} [MetricSpace M] [NormedAddCommGroup F]
    {q : M} {η : M → F} {ζ : M → ℝ} (hη : ContinuousOn η (ball q 200))
    (h102 : ∀ x ∈ ball q 200, ‖η x‖ < 100 → x ∈ ball q 102)
    (hζ : ∀ x, ζ x ≠ 0 → x ∈ ball q 200 ∧ ‖η x‖ < 9) :
    tsupport ζ ⊆ {x | x ∈ ball q 200 ∧ ‖η x‖ ≤ 9} := by
  have hsupp : support ζ ⊆ ball q 102 ∩ {x | ‖η x‖ ≤ 9} := by
    intro x hx
    obtain ⟨h200, h9⟩ := hζ x hx
    exact ⟨h102 x h200 (by linarith), h9.le⟩
  intro x hx
  have hcl : x ∈ closure (ball q 102 ∩ {x | ‖η x‖ ≤ 9}) := closure_mono hsupp hx
  have hx102 : x ∈ closedBall q 102 :=
    closure_ball_subset_closedBall (closure_mono inter_subset_left hcl)
  have hx200 : x ∈ ball q 200 := mem_ball.mpr ((mem_closedBall.mp hx102).trans_lt (by norm_num))
  refine ⟨hx200, ?_⟩
  have hcont : ContinuousAt (fun y => ‖η y‖) x :=
    (hη.continuousAt (isOpen_ball.mem_nhds hx200)).norm
  have hfreq : ∃ᶠ y in 𝓝 x, ‖η y‖ ≤ 9 :=
    (mem_closure_iff_frequently.mp (closure_mono inter_subset_right hcl))
  exact le_of_tendsto_of_frequently hcont.tendsto hfreq

end DifferentialGeometry.Geometry.Collapse
