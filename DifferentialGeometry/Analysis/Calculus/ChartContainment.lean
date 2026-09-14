import DifferentialGeometry.Topology.FirstExit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set MeasureTheory

namespace OpenPartialHomeomorph

variable {X E : Type*} [TopologicalSpace X] [T2Space X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mapsTo_image_closedBall_of_integral_bound (e : OpenPartialHomeomorph X E)
    {γ : ℝ → X} {a b R : ℝ} {v : ℝ → ℝ} (hab : a ≤ b) (hR : 0 < R)
    (hγ : ContinuousOn γ (Icc a b)) (hstart : γ a ∈ e.source)
    (hcompact : IsCompact (Metric.closedBall (e (γ a)) R))
    (hsub : Metric.closedBall (e (γ a)) R ⊆ e.target)
    (hfd : ∀ t ∈ Ioo a b, γ t ∈ e.source → DifferentiableAt ℝ (e ∘ γ) t)
    (hv : IntervalIntegrable v volume a b) (hvn : ∀ t ∈ Icc a b, 0 ≤ v t)
    (hbound : ∀ t ∈ Ioo a b, γ t ∈ e.symm '' Metric.closedBall (e (γ a)) R →
      ‖deriv (e ∘ γ) t‖ ≤ v t)
    (hlen : ∫ t in a..b, v t < R) :
    MapsTo γ (Icc a b) (e.symm '' Metric.closedBall (e (γ a)) R) := by
  let K := e.symm '' Metric.closedBall (e (γ a)) R
  have hK : IsClosed K := (hcompact.image_of_continuousOn
    (e.symm.continuousOn.mono hsub)).isClosed
  have hKs : K ⊆ e.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact e.map_target (hsub hy)
  have hOpen : IsOpen (e.symm '' Metric.ball (e (γ a)) R) :=
    e.symm.isOpen_image_of_subset_source Metric.isOpen_ball
      (Metric.ball_subset_closedBall.trans hsub)
  have hzero : γ a ∈ interior K := by
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset
      (hOpen.mem_nhds ⟨e (γ a), Metric.mem_ball_self hR, e.left_inv hstart⟩)
      (Set.image_mono Metric.ball_subset_closedBall)
  intro y hy
  by_contra hyK
  have hay : a < y := by
    refine lt_of_le_of_ne hy.1 ?_
    intro heq
    exact hyK (heq ▸ interior_subset hzero)
  have hγshift : ContinuousOn (fun s => γ (a + s)) (Icc 0 (y - a)) := by
    apply hγ.comp (continuous_const.add continuous_id).continuousOn
    intro s hs
    change a + s ∈ Icc a b
    constructor <;> linarith only [hs.1, hs.2, hy.2]
  obtain ⟨τ, hτ, hstay, hfront⟩ := DifferentialGeometry.exists_first_exit_frontier hK
    (sub_pos.mpr hay) hγshift (by simpa using hzero)
    (by simpa only [K, show a + (y - a) = y by ring] using hyK)
  have hτa : a ≤ a + τ := by linarith only [hτ.1]
  have hτb : a + τ ≤ b := by linarith only [hτ.2, hy.2]
  have hstay' (s : ℝ) (hs : s ∈ Icc a (a + τ)) : γ s ∈ K := by
    have h := hstay (s - a) (by constructor <;> linarith only [hs.1, hs.2])
    simpa only [add_sub_cancel] using h
  have hτK : γ (a + τ) ∈ K := by
    exact hstay' _ ⟨hτa, le_rfl⟩
  obtain ⟨w, hw, hweq⟩ := hτK
  have hwnot : w ∉ Metric.ball (e (γ a)) R := by
    intro hwball
    have hwint : e.symm w ∈ interior K := by
      rw [mem_interior_iff_mem_nhds]
      exact Filter.mem_of_superset (hOpen.mem_nhds ⟨w, hwball, rfl⟩)
        (Set.image_mono Metric.ball_subset_closedBall)
    exact (mem_frontier_iff_notMem_interior (hstay' _ ⟨hτa, le_rfl⟩)).mp hfront (hweq ▸ hwint)
  have hint : IntervalIntegrable v volume a (a + τ) := by
    apply hv.mono_set
    rw [uIcc_of_le hab, uIcc_of_le hτa]
    exact Icc_subset_Icc le_rfl hτb
  have hfc : ContinuousOn (e ∘ γ) (Icc a (a + τ)) :=
    e.continuousOn.comp (hγ.mono (Icc_subset_Icc le_rfl hτb))
      (fun s hs => hKs (hstay' s hs))
  have hfd' : DifferentiableOn ℝ (e ∘ γ) (Ioo a (a + τ)) := by
    intro s hs
    exact (hfd s ⟨hs.1, hs.2.trans_le hτb⟩
      (hKs (hstay' s (Ioo_subset_Icc_self hs)))).differentiableWithinAt
  have hn := norm_sub_le_integral_of_norm_deriv_le_of_le hτa hfc hfd'
    (ae_of_all _ (fun s hs => hbound s ⟨hs.1, hs.2.trans_le hτb⟩
      (hstay' s (Ioo_subset_Icc_self hs)))) hint
  have hni : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioc a b)] v := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hvn s (Ioc_subset_Icc_self hs)
  have hlen' := (hn.trans (intervalIntegral.integral_mono_interval le_rfl hτa hτb hni hv)).trans_lt hlen
  have hew : e (γ (a + τ)) = w := by rw [← hweq, e.right_inv (hsub hw)]
  apply hwnot
  simpa only [Metric.mem_ball, dist_eq_norm, Function.comp_apply, hew] using hlen'

end OpenPartialHomeomorph
