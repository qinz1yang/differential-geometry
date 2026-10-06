import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.CompactPatchPatch

set_option autoImplicit false

/-!
# CP1-D6 (6): kernel constancy on the window of a glued datum
-/

noncomputable section
open Set Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Surgery GC.LongTime
open scoped Manifold ContDiff

namespace GC.LongTime.CuspP1

universe u v

section Window

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {T : ObservationTower P g}
  {X : Type v} [TopologicalSpace X] {T₀ : ℝ}
  {m : ∀ t : ℝ, T₀ ≤ t → X → (postStage T t).Carrier}

/-- the family `t ↦ z(t, ·)` as continuous maps into the survivor domain -/
def LocalDatum_CPD6.family {N : ℕ} {J : Set ℝ} {F L : Fin ((T.history N).eventCount + 1)}
    {hFL : F ≤ L} (D : LocalDatum_CPD6 T T₀ m N J univ F L hFL) {t₁ : ℝ} (ht₁ : t₁ ∈ J) (t : ℝ) :
    C(X, (T.history N).backwardSurvivorDomain F L hFL) := by
  classical
  refine ⟨fun y => D.z ((if t ∈ J then t else t₁), y), ?_⟩
  have ht : (if t ∈ J then t else t₁) ∈ J := by
    split_ifs with h
    · exact h
    · exact ht₁
  refine D.cont.comp_continuous (by fun_prop) ?_
  intro y
  exact ⟨ht, mem_univ _⟩

theorem LocalDatum_CPD6.family_apply {N : ℕ} {J : Set ℝ} {F L : Fin ((T.history N).eventCount + 1)}
    {hFL : F ≤ L} (D : LocalDatum_CPD6 T T₀ m N J univ F L hFL) {t₁ : ℝ} (ht₁ : t₁ ∈ J) {t : ℝ}
    (ht : t ∈ J) (y : X) : D.family ht₁ t y = D.z (t, y) := by
  simp [LocalDatum_CPD6.family, ht]

theorem LocalDatum_CPD6.family_continuousOn {N : ℕ} {J : Set ℝ}
    {F L : Fin ((T.history N).eventCount + 1)}
    {hFL : F ≤ L} (D : LocalDatum_CPD6 T T₀ m N J univ F L hFL) {t₁ : ℝ} (ht₁ : t₁ ∈ J) :
    ContinuousOn (fun q : ℝ × X => D.family ht₁ q.1 q.2) (J ×ˢ univ) := by
  refine D.cont.congr ?_
  rintro ⟨t, y⟩ ⟨ht, -⟩
  exact D.family_apply ht₁ ht y

/-- the actual map is the survivor map of the active stage composed with the family -/
theorem LocalDatum_CPD6.map_eq {N : ℕ} {J : Set ℝ}
    {F L : Fin ((T.history N).eventCount + 1)} {hFL : F ≤ L}
    (D : LocalDatum_CPD6 T T₀ m N J univ F L hFL) {t₁ : ℝ} (ht₁ : t₁ ∈ J)
    (mc : ∀ t (ht : T₀ ≤ t), C(X, (postStage T t).Carrier))
    (hm : ∀ t ht y, mc t ht y = m t ht y) {t : ℝ} (ht : t ∈ J) :
    mc t (D.hJ t ht).1 =
      ((carrierHomeo_CPD2 (postStage_eq_stage_active_CPD2 T N
          ⟨t, (D.hJ t ht).2.1, (D.hJ t ht).2.2⟩).symm :
        ((T.history N).stage ((T.history N).activeStage
          ⟨t, (D.hJ t ht).2.1, (D.hJ t ht).2.2⟩)).Carrier ≃ₜ (postStage T t).Carrier) :
        C(_, (postStage T t).Carrier)).comp
      ((survivorCM (T.history N) F L hFL ((T.history N).activeStage
          ⟨t, (D.hJ t ht).2.1, (D.hJ t ht).2.2⟩) (D.stages t ht).1 (D.stages t ht).2).comp
        (D.family ht₁ t)) := by
  ext y
  rw [hm t (D.hJ t ht).1 y]
  symm
  apply carrierHomeo_eq_of_heq_CPD2
  rw [ContinuousMap.comp_apply, D.family_apply ht₁ ht y]
  exact D.agrees t ht y (mem_univ _)

/-- IMS01 on a glued window: the kernel of `π₁ X → π₁ M_t` is constant for `t ∈ J`. -/
theorem LocalDatum_CPD6.kernel_const {N : ℕ} {J : Set ℝ}
    {F L : Fin ((T.history N).eventCount + 1)} {hFL : F ≤ L}
    (D : LocalDatum_CPD6 T T₀ m N J univ F L hFL) (hJ : J.OrdConnected) [PreconnectedSpace X]
    (mc : ∀ t (ht : T₀ ≤ t), C(X, (postStage T t).Carrier))
    (hm : ∀ t ht y, mc t ht y = m t ht y) (x : X) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) :
    (FundamentalGroup.map (mc s (D.hJ s hs).1) x).ker =
      (FundamentalGroup.map (mc t (D.hJ t ht).1) x).ker := by
  have hker : ∀ τ (hτ : τ ∈ J),
      (FundamentalGroup.map (mc τ (D.hJ τ hτ).1) x).ker =
      (FundamentalGroup.map ((survivorCM (T.history N) F L hFL ((T.history N).activeStage
          ⟨τ, (D.hJ τ hτ).2.1, (D.hJ τ hτ).2.2⟩) (D.stages τ hτ).1 (D.stages τ hτ).2).comp
        (D.family hs τ)) x).ker := by
    intro τ hτ
    rw [D.map_eq hs mc hm hτ]
    exact composite_kernel _ _ x (fundamentalGroup_map_homeomorph_injective _ _)
  rw [hker s hs, hker t ht]
  have h1 := kernel_const_of_family hJ (D.family hs) (D.family_continuousOn hs)
    (survivorCM (T.history N) F L hFL ((T.history N).activeStage
          ⟨s, (D.hJ s hs).2.1, (D.hJ s hs).2.2⟩) (D.stages s hs).1 (D.stages s hs).2) hs ht x
  refine h1.trans ?_
  exact kernel_survivor_indep_CPD2 (T.history N) F L hFL (D.family hs t) x _ _
    (D.stages s hs).1 (D.stages s hs).2 (D.stages t ht).1 (D.stages t ht).2

end Window

end GC.LongTime.CuspP1
