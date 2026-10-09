import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryKernelStep
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.StageTransportRaw

set_option autoImplicit false

/-!
# CP1-D2 (G4): surgery times in the history, stage versus slice, and the global kernel statement
-/

noncomputable section
open Set Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Surgery GC.LongTime
open DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff

namespace GC.LongTime.CuspP1

universe u v

section Survivor

variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
  {X : Type v} [TopologicalSpace X] [PreconnectedSpace X]
  (q : C(X, H.backwardSurvivorDomain first last hle)) (x : X)

/-- one surgery event: the kernel of the survivor map is unchanged from stage `i` to `i+1` -/
theorem kernel_survivor_step_CPD2 (i : Fin H.eventCount) (hf : first ≤ i.castSucc)
    (hl : i.succ ≤ last) :
    (FundamentalGroup.map ((survivorCM H first last hle i.castSucc hf
        (i.castSucc_lt_succ.le.trans hl)).comp q) x).ker =
    (FundamentalGroup.map ((survivorCM H first last hle i.succ
        (hf.trans i.castSucc_lt_succ.le) hl).comp q) x).ker := by
  apply kernel_eq_of_regularCrossing_CPD2 (H.event i)
  intro y
  exact H.backwardSurvivorMap_crossing first last hle i hf hl (q y)

/-- the kernel of the survivor map is the same at all stages of `[first, last]` -/
theorem kernel_survivor_indep_CPD2 (j j' : Fin (H.eventCount + 1)) (hj : first ≤ j) (hjl : j ≤ last)
    (hj' : first ≤ j') (hjl' : j' ≤ last) :
    (FundamentalGroup.map ((survivorCM H first last hle j hj hjl).comp q) x).ker =
    (FundamentalGroup.map ((survivorCM H first last hle j' hj' hjl').comp q) x).ker := by
  have key : ∀ (j j' : Fin (H.eventCount + 1)) (hj : first ≤ j) (hjl : j ≤ last)
      (hj' : first ≤ j') (hjl' : j' ≤ last), j ≤ j' →
      (FundamentalGroup.map ((survivorCM H first last hle j hj hjl).comp q) x).ker =
      (FundamentalGroup.map ((survivorCM H first last hle j' hj' hjl').comp q) x).ker := by
    intro j j'
    induction j' using Fin.induction with
    | zero =>
      intro hj hjl hj' hjl' hjj'
      have : j = 0 := le_antisymm hjj' (Fin.zero_le _)
      subst this
      rfl
    | succ i ih =>
      intro hj hjl hj' hjl' hjj'
      rcases eq_or_lt_of_le hjj' with h | h
      · subst h; rfl
      · have hji : j ≤ i.castSucc := by
          rw [Fin.le_iff_val_le_val]
          have : j.val < i.succ.val := h
          simp only [Fin.val_succ, Fin.val_castSucc] at this ⊢
          omega
        have h1 := ih hj hjl (hj.trans hji) (i.castSucc_lt_succ.le.trans hjl') hji
        have h2 := kernel_survivor_step_CPD2 H first last hle q x i (hj.trans hji) hjl'
        exact h1.trans h2
  rcases le_total j j' with h | h
  · exact key j j' hj hjl hj' hjl' h
  · exact (key j' j hj' hjl' hj hjl h).symm

end Survivor

section StageSlice

/-- identification of carriers along an equality of stages -/
def carrierHomeo_CPD2 {A B : OrientedThreeStage.{u}} (h : A = B) : A.Carrier ≃ₜ B.Carrier := by
  subst h
  exact Homeomorph.refl _

theorem carrierHomeo_heq_CPD2 {A B : OrientedThreeStage.{u}} (h : A = B) (a : A.Carrier) :
    HEq (carrierHomeo_CPD2 h a) a := by
  subst h
  rfl

theorem carrierHomeo_eq_of_heq_CPD2 {A B : OrientedThreeStage.{u}} (h : A = B) (a : A.Carrier)
    (b : B.Carrier) (hab : HEq a b) : carrierHomeo_CPD2 h a = b :=
  eq_of_heq ((carrierHomeo_heq_CPD2 h a).trans hab)

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- (gap 1 of CP1-D) The stage active at time `t` in the `n`-th history is the actual slice
`postStage t` of the observation tower. -/
theorem observe_stage_last_eq_CPD2 (T : ObservationTower P g) (n : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hbn : b ≤ (n : ℝ)) :
    (T.observe b hb).stage (Fin.last (T.observe b hb).eventCount) =
      (T.history n).stage ((T.history n).activeStage
        ⟨b, hb, by rw [T.horizon_eq]; exact hbn⟩) := by
  have R := (T.observe_eq_atIndex n b hb hbn).stage_eq (Fin.last (T.observe b hb).eventCount)
  refine R.trans ?_
  exact congrArg (T.history n).stage (Fin.ext (T.observe_eq_atIndex n b hb hbn).count_eq)

theorem postStage_eq_stage_active_CPD2 (T : ObservationTower P g) (n : ℕ)
    (t : Icc (0 : ℝ) (T.history n).horizon) :
    postStage T (t : ℝ) = (T.history n).stage ((T.history n).activeStage t) := by
  have hmax : max (t : ℝ) 0 = t := max_eq_left t.2.1
  have hbn : (t : ℝ) ≤ (n : ℝ) := le_of_le_of_eq t.2.2 (T.horizon_eq n)
  have hbn' : max (t : ℝ) 0 ≤ (n : ℝ) := by rw [hmax]; exact hbn
  have h := observe_stage_last_eq_CPD2 T n (max (t : ℝ) 0) (le_max_right _ _) hbn'
  have hsub : (⟨max (t : ℝ) 0, le_max_right _ _, le_of_le_of_eq hbn' (T.horizon_eq n).symm⟩ :
      Icc (0 : ℝ) (T.history n).horizon) = t := Subtype.ext hmax
  rw [hsub] at h
  exact h

end StageSlice

section Patch

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {H : FiniteVolumeHyperbolicModel.{u}} {T₀ : ℝ} {α : ℝ → ℝ}
  {domain : ℝ → TopologicalSpace.Opens H.Carrier}
  {f : (t : ℝ) → T₀ ≤ t → H.Carrier → (postStage F.observation t).Carrier}
  {t₀ : ℝ} {x₀ : H.Carrier} {X : Type v} [TopologicalSpace X]

/-- the time `τ ∈ (a, b)` as a point of the horizon interval of the patch history -/
def patchTime_CPD2 (p : PersistentModelPatch F H T₀ α domain f t₀ x₀) {τ : ℝ}
    (hτ : τ ∈ Ioo p.a p.b) : Icc (0 : ℝ) (F.tower.history p.n).horizon :=
  ⟨τ, p.a_nonneg.trans hτ.1.le, hτ.2.le.trans p.horizon⟩

/-- On the patch window, the actual map into the slice `postStage τ` is the survivor map of the
active stage composed with the patch family and the stage/slice identification. -/
theorem patch_map_eq_CPD2 (p : PersistentModelPatch F H T₀ α domain f t₀ x₀)
    (ι : C(X, H.Carrier)) (hι : ∀ y, ι y ∈ p.neighborhood)
    (m : ∀ t : ℝ, T₀ ≤ t → C(X, (postStage F.observation t).Carrier))
    (hm : ∀ t (hT : T₀ ≤ t) y, m t hT y = f t hT (ι y))
    {τ : ℝ} (hτ : τ ∈ Ioo p.a p.b) (hT : T₀ ≤ τ) :
    m τ hT = ((carrierHomeo_CPD2
        (postStage_eq_stage_active_CPD2 F.observation p.n (patchTime_CPD2 p hτ)).symm :
          (((F.tower.history p.n).toHistory.stage
            ((F.tower.history p.n).toHistory.activeStage (patchTime_CPD2 p hτ))).Carrier ≃ₜ
            (postStage F.observation τ).Carrier)) :
        C(((F.tower.history p.n).toHistory.stage
            ((F.tower.history p.n).toHistory.activeStage (patchTime_CPD2 p hτ))).Carrier,
          (postStage F.observation τ).Carrier)).comp
      ((survivorCM (F.tower.history p.n).toHistory p.first p.last p.ordered
          ((F.tower.history p.n).toHistory.activeStage (patchTime_CPD2 p hτ))
          (p.stages (patchTime_CPD2 p hτ) hτ).1 (p.stages (patchTime_CPD2 p hτ) hτ).2).comp
        (patchTorusMap p ι hι τ)) := by
  ext y
  rw [hm τ hT y]
  symm
  apply carrierHomeo_eq_of_heq_CPD2
  rw [ContinuousMap.comp_apply]
  rw [patchTorusMap_apply p ι hι hτ y]
  exact p.agrees (patchTime_CPD2 p hτ) hτ hT (ι y) (hι y)

/-- IMS01 on a patch window, with surgery times allowed: the kernel of `π₁ X → π₁ (M_t)`
induced by the actual cores `f t` is independent of `t ∈ (a, b)` (`t ≥ T₀`). -/
theorem patch_kernel_const_across_events_CPD2 [PreconnectedSpace X]
    (p : PersistentModelPatch F H T₀ α domain f t₀ x₀)
    (ι : C(X, H.Carrier)) (hι : ∀ y, ι y ∈ p.neighborhood)
    (m : ∀ t : ℝ, T₀ ≤ t → C(X, (postStage F.observation t).Carrier))
    (hm : ∀ t (hT : T₀ ≤ t) y, m t hT y = f t hT (ι y))
    {s t : ℝ} (hs : s ∈ Ioo p.a p.b) (ht : t ∈ Ioo p.a p.b) (hTs : T₀ ≤ s) (hTt : T₀ ≤ t)
    (x : X) :
    (FundamentalGroup.map (m s hTs) x).ker = (FundamentalGroup.map (m t hTt) x).ker := by
  have hker : ∀ τ (hτ : τ ∈ Ioo p.a p.b) (hT : T₀ ≤ τ),
      (FundamentalGroup.map (m τ hT) x).ker =
      (FundamentalGroup.map ((survivorCM (F.tower.history p.n).toHistory p.first p.last p.ordered
          ((F.tower.history p.n).toHistory.activeStage (patchTime_CPD2 p hτ))
          (p.stages (patchTime_CPD2 p hτ) hτ).1 (p.stages (patchTime_CPD2 p hτ) hτ).2).comp
        (patchTorusMap p ι hι τ)) x).ker := by
    intro τ hτ hT
    rw [patch_map_eq_CPD2 p ι hι m hm hτ hT]
    exact composite_kernel _ _ x (fundamentalGroup_map_homeomorph_injective _ _)
  rw [hker s hs hTs, hker t ht hTt]
  have h1 := patch_kernel_const p ι hι
    ((F.tower.history p.n).toHistory.activeStage (patchTime_CPD2 p hs))
    (p.stages (patchTime_CPD2 p hs) hs).1 (p.stages (patchTime_CPD2 p hs) hs).2 hs ht x
  refine h1.trans ?_
  exact kernel_survivor_indep_CPD2 (F.tower.history p.n).toHistory p.first p.last p.ordered
    (patchTorusMap p ι hι t) x _ _ (p.stages (patchTime_CPD2 p hs) hs).1
    (p.stages (patchTime_CPD2 p hs) hs).2 (p.stages (patchTime_CPD2 p ht) ht).1
    (p.stages (patchTime_CPD2 p ht) ht).2

/-- IMS01 on the whole half-line `[T₀, ∞)`: smooth segments (patch windows) and the finitely many
surgery times inside them.  The explicit hypothesis `hpatch` asks for a patch around every time
whose neighbourhood contains the compact image of the marked space `ι`. -/
theorem kernel_const_Ici_CPD2 [PreconnectedSpace X] (ι : C(X, H.Carrier))
    (m : ∀ t : ℝ, T₀ ≤ t → C(X, (postStage F.observation t).Carrier))
    (hm : ∀ t (hT : T₀ ≤ t) y, m t hT y = f t hT (ι y))
    (hpatch : ∀ τ : ℝ, T₀ ≤ τ → ∃ (x₀ : H.Carrier)
      (p : PersistentModelPatch F H T₀ α domain f τ x₀), ∀ y, ι y ∈ p.neighborhood)
    (x : X) {s t : ℝ} (hs : T₀ ≤ s) (ht : T₀ ≤ t) :
    (FundamentalGroup.map (m s hs) x).ker = (FundamentalGroup.map (m t ht) x).ker := by
  let K : Ici T₀ → Subgroup (FundamentalGroup X x) :=
    fun τ => (FundamentalGroup.map (m τ.1 τ.2) x).ker
  have hloc : IsLocallyConstant K := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro τ0
    obtain ⟨x₀, p, hp⟩ := hpatch τ0.1 τ0.2
    have hmem : τ0 ∈ (Subtype.val ⁻¹' Ioo p.a p.b : Set (Ici T₀)) := ⟨p.before, p.after⟩
    filter_upwards [(isOpen_Ioo.preimage continuous_subtype_val).mem_nhds hmem] with τ hτ
    exact patch_kernel_const_across_events_CPD2 p ι hp m hm hτ ⟨p.before, p.after⟩ τ.2 τ0.2 x
  have : PreconnectedSpace (Ici T₀) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ici
  exact hloc.apply_eq_of_preconnectedSpace ⟨s, hs⟩ ⟨t, ht⟩

end Patch

end GC.LongTime.CuspP1
