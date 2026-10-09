import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Jacobian.EndpointContinuity

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature

open private not_mem_range_of_mem_Ioo from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Exponential.Regularity

universe u

variable {H : ObservedHistory.{u}} {last : Fin (H.eventCount + 1)} {T B : ℝ}
  {p : (H.stage last).Carrier}

theorem historyReducedJacobianAlong_le
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    {first : Fin (H.eventCount + 1)} {hle : first ≤ last} {v₂ : ℝ} (hv₂ : 0 < v₂)
    (hv₂k : T - v₂ ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (Z₂ : H.historyLExpDomain hle T v₂ p) (hZ₂ : Z₂.1 ∈ H.historyMinDomain hle T B v₂ p)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ v₂) (haF : T - a ^ 2 ∉ range H.time)
    (hbF : T - b ^ 2 ∉ range H.time) :
    H.historyReducedJacobianAlong Z₂ b ≤ H.historyReducedJacobianAlong Z₂ a := by
  classical
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  set S : Set ℝ := (fun t => Real.sqrt (T - t)) '' range H.time with hSdef
  have hS : S.Finite := (finite_range _).image _
  have hmemS : ∀ x, 0 < x → (x ∈ S ↔ T - x ^ 2 ∈ range H.time) := by
    intro x hx
    constructor
    · rintro ⟨t, ⟨j, rfl⟩, hjx⟩
      simp only at hjx
      refine ⟨j, ?_⟩
      have hpos : 0 < T - H.time j := by
        by_contra h
        rw [Real.sqrt_eq_zero'.2 (not_lt.1 h)] at hjx
        linarith
      rw [← hjx, Real.sq_sqrt hpos.le]
      ring
    · rintro ⟨j, hj⟩
      refine ⟨H.time j, ⟨j, rfl⟩, ?_⟩
      change Real.sqrt (T - H.time j) = x
      rw [hj, sub_sub_cancel, Real.sqrt_sq hx.le]
  have hcont : ∀ x, 0 < x → x < v₂ → T - x ^ 2 ∉ range H.time →
      ContinuousAt (H.historyReducedJacobianAlong Z₂) x := fun x hx hxv hxF => by
    obtain ⟨d, -, hd⟩ := exists_hasDerivAt_historyReducedJacobianAlong hfloor hv₂ Z₂ hZ₂ hv₂k hx hxv
      hxF
    exact hd.continuousAt
  refine le_of_hasDerivAt_nonpos_off_finite hS _ a b hab le_rfl
    (fun x hx hxS => exists_hasDerivAt_historyReducedJacobianAlong hfloor hv₂ Z₂ hZ₂ hv₂k
      (ha.trans hx.1) (hx.2.trans_le hb) fun h => hxS ((hmemS x (ha.trans hx.1)).2 h))
    (fun x hx hxS => exists_tendsto_seam_historyReducedJacobianAlong hfloor hv₂ Z₂ hZ₂ hv₂k
      (ha.trans hx.1) (hx.2.trans_le hb) ((hmemS x (ha.trans hx.1)).1 hxS)) ?_ ?_
  · exact (hcont a ha (hlt.trans_le hb) haF).continuousWithinAt
  · rcases eq_or_lt_of_le hb with h | h
    · rw [h]
      exact continuousWithinAt_historyReducedJacobianAlong hfloor hv₂ Z₂ hZ₂ hv₂k
    · exact (hcont b (ha.trans_le hab) h hbF).continuousWithinAt

theorem historyReducedJacobian_antitoneOn
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    {first : Fin (H.eventCount + 1)} {hle : first ≤ last} {v₂ : ℝ} (hv₂ : 0 < v₂)
    (hv₂k : T - v₂ ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (Z₂ : H.historyLExpDomain hle T v₂ p) (hZ₂ : Z₂.1 ∈ H.historyMinDomain hle T B v₂ p) :
    AntitoneOn (H.historyReducedJacobianAlong Z₂)
      {v | 0 < v ∧ v ≤ v₂ ∧ T - v ^ 2 ∉ range H.time} :=
  fun _ ha _ hb hab =>
    historyReducedJacobianAlong_le hfloor hv₂ hv₂k Z₂ hZ₂ ha.1 hab hb.2.1 ha.2.2 hb.2.2

theorem historyReducedJacobian_le_of_le_of_mem_Ioo
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    {k₁ k₂ : Fin (H.eventCount + 1)} (hk₁l : k₁ ≤ last) (hk₂l : k₂ ≤ last) {v₁ v₂ : ℝ}
    (hv₁ : 0 < v₁) (hv₁₂ : v₁ ≤ v₂)
    (hv₁k : T - v₁ ^ 2 ∈ Ioo (H.time k₁) (H.stageEndTime k₁))
    (hv₂k : T - v₂ ^ 2 ∈ Ioo (H.time k₂) (H.stageEndTime k₂))
    (Z₁ : H.historyLExpDomain hk₁l T v₁ p) (Z₂ : H.historyLExpDomain hk₂l T v₂ p)
    (hZ₂ : Z₂.1 ∈ H.historyMinDomain hk₂l T B v₂ p) (hZ : Z₁.1 = Z₂.1) :
    H.historyReducedJacobian hk₂l T v₂ p Z₂ ≤ H.historyReducedJacobian hk₁l T v₁ p Z₁ := by
  have hv₂ : 0 < v₂ := hv₁.trans_le hv₁₂
  rw [← historyReducedJacobianAlong_eq Z₂ hv₂ le_rfl hk₂l (H.mem_stageDomain_of_mem_Ioo hv₂k) Z₂
    rfl, ← historyReducedJacobianAlong_eq Z₂ hv₁ hv₁₂ hk₁l (H.mem_stageDomain_of_mem_Ioo hv₁k) Z₁
    hZ]
  exact historyReducedJacobianAlong_le hfloor hv₂ hv₂k Z₂ hZ₂ hv₁ hv₁₂ le_rfl
    (not_mem_range_of_mem_Ioo hv₁k) (not_mem_range_of_mem_Ioo hv₂k)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
