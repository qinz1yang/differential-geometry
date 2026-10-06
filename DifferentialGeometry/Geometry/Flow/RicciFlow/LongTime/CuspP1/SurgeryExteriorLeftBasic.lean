import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryExteriorSlice

/-!
# CP1-D8 (G4b): small lemmas for the left side of a surgery event
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

/-- kernels are unchanged by a homeomorphism of the ambient spaces carrying `SA` onto `SB` -/
theorem ker_comp_image_CPD8 {A B X : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace X] (e : A ≃ₜ B) (SA : Set A) (SB : Set B) (h : e '' SA = SB)
    (f : C(X, SA)) (f' : C(X, SB)) (hf : ∀ y, (f' y).1 = e (f y).1) (x : X) :
    (FundamentalGroup.map f' x).ker = (FundamentalGroup.map f x).ker := by
  let k : SA ≃ₜ SB := (e.image SA).trans (Homeomorph.setCongr h)
  have : f' = (k : C(SA, SB)).comp f := by
    ext y
    exact hf y
  rw [this]
  exact kernel_comp_homeomorph k f x

theorem agrees_cast_CPD8 {P : OrientedThreeStage.{u}} {g : P.Metric} (T : ObservationTower P g)
    {Hm : Type*} [TopologicalSpace Hm] {T₀ : ℝ}
    {m : ∀ t : ℝ, T₀ ≤ t → Hm → (postStage T t).Carrier} {N : ℕ} {J : Set ℝ} {U : Set Hm}
    {Fs Ls : Fin ((T.history N).eventCount + 1)} {hFL : Fs ≤ Ls}
    (D : LocalDatum_CPD6 T T₀ m N J U Fs Ls hFL) {u : ℝ} (hu : u ∈ J) {y : Hm} (hy : y ∈ U)
    {j : Fin ((T.history N).eventCount + 1)}
    (hj : (T.history N).activeStage ⟨u, (D.hJ u hu).2.1, (D.hJ u hu).2.2⟩ = j)
    (h1 : Fs ≤ j) (h2 : j ≤ Ls) :
    (T.history N).backwardSurvivorMap Fs Ls hFL j h1 h2 (D.z (u, y)) =
      carrierHomeo_CPD2 ((postStage_eq_stage_active_CPD2 T N ⟨u, (D.hJ u hu).2.1, (D.hJ u hu).2.2⟩).trans
        (congrArg (T.history N).stage hj)) (m u (D.hJ u hu).1 y) := by
  subst hj
  exact (carrierHomeo_eq_of_heq_CPD2 _ _ _ (D.agrees u hu y hy).symm).symm

theorem exists_event_split_CPD8 (H : ObservedHistory.{u}) {τ : ℝ} (hτ0 : 0 < τ) (h0 : 0 ≤ τ)
    (h1 : τ ≤ H.horizon) (k : Fin (H.eventCount + 1)) (hk : H.time k = τ) :
    ∃ j : Fin H.eventCount, H.time j.succ = τ ∧ H.activeStage ⟨τ, h0, h1⟩ = j.succ ∧
      ∀ (t : ℝ) (h0' : 0 ≤ t) (h1' : t ≤ H.horizon), H.time j.castSucc < t → t < τ →
        H.activeStage ⟨t, h0', h1'⟩ = j.castSucc := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [H.time_zero] at hk
    linarith
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hk0
  refine ⟨j, hk, ?_, ?_⟩
  · apply le_antisymm
    · by_contra hcon
      push Not at hcon
      have h2 := H.activeStage_time_le ⟨τ, h0, h1⟩
      have h3 := H.time_strictMono hcon
      simp only at h2
      linarith
    · exact H.le_activeStage ⟨τ, h0, h1⟩ _ (le_of_eq hk)
  · intro t h0' h1' hpt hlt
    apply le_antisymm
    · have h2 := H.activeStage_time_le ⟨t, h0', h1'⟩
      simp only at h2
      have h3 : H.time (H.activeStage ⟨t, h0', h1'⟩) < H.time j.succ := by linarith
      have h4 := H.time_strictMono.lt_iff_lt.mp h3
      exact Fin.le_castSucc_iff.mpr h4
    · exact H.le_activeStage ⟨t, h0', h1'⟩ _ hpt.le

end GC.LongTime.CuspP1
