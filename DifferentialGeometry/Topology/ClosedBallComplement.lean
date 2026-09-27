import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallMarking
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv

set_option autoImplicit false
noncomputable section
open Set Function Metric
open scoped Topology

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isConnected_ball_sdiff_closedBall (hdim : 1 < Module.rank ℝ E)
    {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    IsConnected (Metric.ball (0 : E) R \ Metric.closedBall (0 : E) r) := by
  have hs := (isPathConnected_sphere hdim (0 : E) zero_le_one).isConnected
  have hi := isConnected_Ioo hrR
  have heq : (fun p : E × ℝ => p.2 • p.1) ''
      (Metric.sphere (0 : E) 1 ×ˢ Ioo r R) = Metric.ball (0 : E) R \ Metric.closedBall (0 : E) r := by
    ext x
    constructor
    · rintro ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
      have hz' : ‖z‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
      have ht0 : 0 < t := hr.trans_lt ht.1
      rw [mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, dist_zero_right,
        norm_smul, Real.norm_of_nonneg ht0.le, hz', mul_one, not_le]
      exact ⟨ht.2, ht.1⟩
    · intro hx
      have hxR : ‖x‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hx.1
      have hxr : r < ‖x‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx.2
      have hxpos := hr.trans_lt hxr
      refine ⟨(‖x‖⁻¹ • x, ‖x‖), ⟨?_, hxr, hxR⟩, ?_⟩
      · rw [Metric.mem_sphere, dist_zero_right, norm_smul,
          Real.norm_of_nonneg (inv_nonneg.mpr hxpos.le), inv_mul_cancel₀ hxpos.ne']
      · change ‖x‖ • (‖x‖⁻¹ • x) = x
        rw [smul_smul, mul_inv_cancel₀ hxpos.ne', one_smul]
  rw [← heq]
  exact (hs.prod hi).image _ (by fun_prop)

variable {M : Type*} [TopologicalSpace M] [T2Space M] [PreconnectedSpace M]
  [LocallyPathConnectedSpace M] [ProperSpace E]

theorem isPathConnected_compl_image_closedBall
    (e : OpenPartialHomeomorph E M) (hdim : 1 < Module.rank ℝ E)
    {r : ℝ} (hr : 0 ≤ r) (hs : Metric.closedBall 0 r ⊆ e.source) :
    IsPathConnected ((e '' Metric.closedBall 0 r)ᶜ : Set M) := by
  obtain ⟨δ, hδ, hδsub⟩ := (isCompact_closedBall (0 : E) r).exists_thickening_subset_open e.open_source hs
  rw [thickening_closedBall hδ hr] at hδsub
  let R := r + δ / 2
  have hrR : r < R := by dsimp [R]; linarith
  have hRs : Metric.ball (0 : E) R ⊆ e.source :=
    (Metric.ball_subset_ball (by dsimp [R]; linarith : R ≤ δ + r)).trans hδsub
  let K := e '' Metric.closedBall (0 : E) r
  let V := e '' Metric.ball (0 : E) R
  have hK : IsCompact K := (isCompact_closedBall (0 : E) r).image_of_continuousOn
    (e.continuousOn_toFun.mono hs)
  have hV : IsOpen V := e.isOpen_image_of_subset_source Metric.isOpen_ball hRs
  have hKV : K ⊆ V := Set.image_mono (Metric.closedBall_subset_ball hrR)
  have hconn : IsConnected (V \ K) := by
    have hinj : InjOn e (Metric.ball (0 : E) R) := e.injOn.mono hRs
    have himage := hinj.image_sdiff_subset (Metric.closedBall_subset_ball hrR)
    change e '' (Metric.ball (0 : E) R \ Metric.closedBall (0 : E) r) = V \ K at himage
    rw [← himage]
    exact (isConnected_ball_sdiff_closedBall hdim hr hrR).image _
      (e.continuousOn_toFun.mono (fun _ hx => hRs hx.1))
  have hpre := isPreconnected_compl_iUnion_of_collar (X := M)
    (fun _ : Unit => K) (fun _ : Unit => V) (fun _ => hK.isClosed) (fun _ => hV)
    (fun _ => hKV) (fun i j hij => False.elim (hij (Subsingleton.elim i j))) (fun _ => hconn)
  have hpre' : IsPreconnected (Kᶜ : Set M) := by simpa only [iUnion_const] using hpre
  have hne : (Kᶜ : Set M).Nonempty := hconn.nonempty.mono (fun _ hx => hx.2)
  exact hK.isClosed.isOpen_compl.isConnected_iff_isPathConnected.mp ⟨hne, hpre'⟩

end DifferentialGeometry.Topology
