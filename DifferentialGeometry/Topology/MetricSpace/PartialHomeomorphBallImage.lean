import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Metric

namespace OpenPartialHomeomorph

theorem ball_subset_image_ball_of_radial_lower_bound
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [T2Space Y]
    (e : OpenPartialHomeomorph X Y) {p : X} {r R ε : ℝ}
    (hR : 0 < R) (hcompact : IsCompact (closedBall p R))
    (hsub : closedBall p R ⊆ e.source)
    (hconn : IsPreconnected (ball (e p) r))
    (hlower : ∀ x ∈ closedBall p R, dist x p ≤ dist (e x) (e p) + ε)
    (hmargin : r + ε < R) :
    ball (e p) r ⊆ e '' ball p R := by
  intro y hy
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg hy
  have hopen : IsOpen (e '' ball p R) :=
    e.isOpen_image_of_subset_source isOpen_ball (ball_subset_closedBall.trans hsub)
  have hclosed : IsClosed (e '' closedBall p R) :=
    (hcompact.image_of_continuousOn (e.continuousOn.mono hsub)).isClosed
  have hclosure : closure (e '' ball p R) ⊆ e '' closedBall p R :=
    closure_minimal (image_mono ball_subset_closedBall) hclosed
  have hcover : ball (e p) r ⊆ e '' ball p R := by
    apply hconn.subset_of_closure_inter_subset hopen
      ⟨e p, mem_ball_self hr, p, mem_ball_self hR, rfl⟩
    rintro z ⟨hz, hzr⟩
    obtain ⟨x, hx, rfl⟩ := hclosure hz
    refine ⟨x, ?_, rfl⟩
    have hdist : dist (e x) (e p) < r := hzr
    change dist x p < R
    linarith [hlower x hx]
  exact hcover hy

end OpenPartialHomeomorph
