import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryExteriorLeft

/-!
# CP1-D8 (G4): the left side of a surgery time (Q5)

Main theorem `hresLeft_CPD8`.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {K : ℕ} {slices : ℕ → RegularSlice F.observation}

theorem hresLeft_CPD8 {L : LateCutFamily F K slices}
    (E : PersistentCuspExterior L.cores) (i : Fin L.cores.count)
    (q : Fin (E.truncation i).count) (x : Torus) (τ : Ici E.start)
    (hτ : L.cores.start < τ.1) (hne : ¬ NonSurgeryTime_CPD7 F.observation τ.1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : Ici E.start, τ.1 - ε < s.1 → s.1 < τ.1 →
      (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q s.1 s.2) x).ker ≤
        (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q τ.1 τ.2) x).ker := by
  classical
  have hcomp : ∀ j, IsCompact (range (E.truncation j).inclusion) := fun j =>
    isCompact_range (E.truncation j).inclusion.continuous
  have hdom : ∀ j, range (E.truncation j).inclusion ⊆ L.cores.domain j τ.1 := fun j y hy =>
    L.cores.advertised_ball j τ.1 (E.after_cores.trans τ.2) (E.in_ball j τ.1 τ.2 hy)
  obtain ⟨N, Fs, Ls, hFL, J, U, D, hτJ, hJo, hJstart, hJord, hUo, hSU, hUd, hJh, hst⟩ :=
    exists_smoothWindow_CPD7 L.cores hτ (fun j => range (E.truncation j).inclusion) hcomp hdom
  obtain ⟨ε0, hε0, hball⟩ := Metric.isOpen_iff.mp hJo τ.1 hτJ
  by_cases hevN : ∀ k, (F.observation.history N).time k ≠ τ.1
  · -- no event of the `N`-th history at `τ`: the smooth window works on both sides
    obtain ⟨δ, hδ, hconst⟩ := exists_const_activeStage_CPD7 (F.observation.history N)
      (hJh τ.1 hτJ).1 (hJh τ.1 hτJ).2 hevN
    refine ⟨min δ ε0, lt_min hδ hε0, fun s hs1 hs2 => ?_⟩
    have hsJ : s.1 ∈ J := hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [min_le_right δ ε0])
    have hsδ : |s.1 - τ.1| < δ := by
      rw [abs_lt]; constructor <;> linarith [min_le_left δ ε0]
    obtain ⟨e, he⟩ := exists_regionHomeo_of_window_CPD7 E N Fs Ls hFL J U D hJo hJstart hJord hUo
      hSU hUd hJh hst s.1 τ.1 s.2 τ.2 hsJ hτJ
      (hconst s.1 (hJh s.1 hsJ).1 (hJh s.1 hsJ).2 hsδ)
    have : portLoopRegionMap_CPD3 E i q τ.1 τ.2 =
        (e : C(E.region s.1, E.region τ.1)).comp (portLoopRegionMap_CPD3 E i q s.1 s.2) :=
      ContinuousMap.ext fun z => (he i q z).symm
    rw [this, kernel_comp_homeomorph]
  · -- `τ = time (j + 1)` is an event time of the `N`-th history
    push Not at hevN
    obtain ⟨k, hk⟩ := hevN
    have hτ0 : 0 < τ.1 := L.cores.start_pos.trans hτ
    obtain ⟨j, hjt, hact_q, hact_p⟩ := exists_event_split_CPD8 (F.observation.history N) hτ0
      (hJh τ.1 hτJ).1 (hJh τ.1 hτJ).2 k hk
    have hgap : (F.observation.history N).time j.castSucc < τ.1 :=
      hjt ▸ (F.observation.history N).time_strictMono (Fin.castSucc_lt_succ (i := j))
    have hqr := hst τ.1 (hJh τ.1 hτJ).1 (hJh τ.1 hτJ).2 hτJ
    have hq1 : Fs ≤ j.succ := le_of_le_of_eq hqr.1 hact_q
    have hq2 : j.succ ≤ Ls := le_of_eq_of_le hact_q.symm hqr.2
    refine ⟨min ε0 (τ.1 - (F.observation.history N).time j.castSucc),
      lt_min hε0 (by linarith), fun s hs1 hs2 => ?_⟩
    have hsJ : s.1 ∈ J := hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [min_le_left ε0 (τ.1 - (F.observation.history N).time j.castSucc)])
    have hsp : (F.observation.history N).time j.castSucc < s.1 := by
      linarith [min_le_right ε0 (τ.1 - (F.observation.history N).time j.castSucc)]
    have hacts : (F.observation.history N).activeStage
        ⟨s.1, (hJh s.1 hsJ).1, (hJh s.1 hsJ).2⟩ = j.castSucc :=
      hact_p s.1 (hJh s.1 hsJ).1 (hJh s.1 hsJ).2 hsp hs2
    have hsr := hst s.1 (hJh s.1 hsJ).1 (hJh s.1 hsJ).2 hsJ
    have hp1 : Fs ≤ j.castSucc := le_of_le_of_eq hsr.1 hacts
    have hp2 : j.castSucc ≤ Ls := le_of_eq_of_le hacts.symm hsr.2
    have hs' : L.cores.start ≤ s.1 := (hJstart hsJ).le
    have hτ' : L.cores.start ≤ τ.1 := hτ.le
    let T := F.observation
    let H := T.history N
    let Pd := H.backwardSurvivorDomain Fs Ls hFL
    let Φp := H.backwardSurvivorMap Fs Ls hFL j.castSucc hp1 hp2
    let Φq := H.backwardSurvivorMap Fs Ls hFL j.succ hq1 hq2
    have hΦpo : Topology.IsOpenEmbedding Φp := isOpenEmbedding_survivorMap_CPD7 _ _ _ _ _ _ _
    have hΦqo : Topology.IsOpenEmbedding Φq := isOpenEmbedding_survivorMap_CPD7 _ _ _ _ _ _ _
    have hcross : ∀ w, (H.event j).RegularCrossing (Φp w) (Φq w) := fun w =>
      H.backwardSurvivorMap_crossing Fs Ls hFL j hp1 hq2 w
    let cs : (postStage T s.1).Carrier ≃ₜ (H.stage j.castSucc).Carrier :=
      carrierHomeo_CPD2 ((postStage_eq_stage_active_CPD2 T N
        ⟨s.1, (hJh s.1 hsJ).1, (hJh s.1 hsJ).2⟩).trans (congrArg H.stage hacts))
    let cτ : (postStage T τ.1).Carrier ≃ₜ (H.stage j.succ).Carrier :=
      carrierHomeo_CPD2 ((postStage_eq_stage_active_CPD2 T N
        ⟨τ.1, (hJh τ.1 hτJ).1, (hJh τ.1 hτJ).2⟩).trans (congrArg H.stage hact_q))
    have hcastP : ∀ i' y, y ∈ U i' →
        Φp ((D i').z (s.1, y)) = cs (L.cores.map i' s.1 hs' y) := fun i' y hy =>
      agrees_cast_CPD8 T (D i').toLocalDatum_CPD6 hsJ hy hacts hp1 hp2
    have hcastQ : ∀ i' y, y ∈ U i' →
        Φq ((D i').z (τ.1, y)) = cτ (L.cores.map i' τ.1 hτ' y) := fun i' y hy =>
      agrees_cast_CPD8 T (D i').toLocalDatum_CPD6 hτJ hy hact_q hq1 hq2
    -- the region at time `s`, transported to the stage `j`
    have : Nonempty (TorusIdx_LTP1 E.truncation) := ⟨⟨i, q⟩⟩
    obtain ⟨σ, -, -, -, hAc, -⟩ := exists_bicollar_of_exterior_LTP1 E s.1 s.2
    let OP : Set (H.stage j.castSucc).Carrier := cs '' (E.region s.1)ᶜ
    have hOPo : IsOpen OP := cs.isOpenMap _ hAc.isOpen_compl
    have hOPc : OPᶜ = cs '' E.region s.1 := by
      show (cs '' (E.region s.1)ᶜ)ᶜ = _
      rw [cs.image_compl, compl_compl]
    have hLPC : LocallyPathConnectedSpace ↥(E.region s.1) :=
      locallyPathConnectedSpace_region_CPD8 E i q s.1 s.2
    let hA : ↥(E.region s.1) ≃ₜ ↥OPᶜ :=
      (cs.image (E.region s.1)).trans (Homeomorph.setCongr hOPc.symm)
    haveI : LocallyPathConnectedSpace ↥OPᶜ := hA.locallyPathConnectedSpace
    -- the cusp torus in the survivor domain
    let cz : C(Torus, (L.cores.model i).Carrier) :=
      ⟨fun z => (E.truncation i).cuspMap q (z, halfZero), continuous_cuspZero_CPD8 E i q⟩
    have hczr : ∀ z, ∃ c : (E.truncation i).core.Carrier, cz z = (E.truncation i).inclusion c :=
      fun z => ⟨_, (E.truncation i).cusp_zero q z⟩
    have hcz : ∀ z, cz z ∈ U i := fun z => by
      obtain ⟨c, hc⟩ := hczr z
      rw [hc]; exact hSU i ⟨c, rfl⟩
    let wz : Torus → Pd := fun z => (D i).z (s.1, cz z)
    have hwz : Continuous wz := (D i).cont.comp_continuous
      (continuous_const.prodMk cz.continuous) (fun z => ⟨hsJ, hcz z⟩)
    have hPz : ∀ z, Φp (wz z) = cs (portLoopMap_CPH E i q s.1 s.2 z) := fun z =>
      hcastP i (cz z) (hcz z)
    let OQ : Set (H.stage j.succ).Carrier := {q' | ∃ w : Pd, Φq w = q' ∧ Φp w ∈ OP}
    have hP : ∀ p ∈ OP, ∃ q', (H.event j).RegularCrossing p q' := by
      rintro p ⟨a, ha, rfl⟩
      obtain ⟨i', c, hc, hca⟩ := (notMem_region_iff_CPD8 E s.1 s.2 a).mp ha
      refine ⟨Φq ((D i').z (s.1, (E.truncation i').inclusion c)), ?_⟩
      have h1 := hcastP i' _ (hSU i' ⟨c, rfl⟩)
      have h2 : cs a = Φp ((D i').z (s.1, (E.truncation i').inclusion c)) := by
        rw [h1, ← hca]
      rw [h2]
      exact hcross _
    have hQ : ∀ q' ∈ OQ, ∃ p, (H.event j).RegularCrossing p q' := by
      rintro q' ⟨w, rfl, -⟩
      exact ⟨_, hcross w⟩
    have hQP : ∀ q' ∈ OQ, ∀ p, (H.event j).RegularCrossing p q' → p ∈ OP := by
      rintro q' ⟨w, rfl, hw⟩ p hp
      rw [(H.event j).regularCrossing_left_unique hp (hcross w)]
      exact hw
    let uC : C(Torus, ↥OPᶜ) := (hA : C(↥(E.region s.1), ↥OPᶜ)).comp
      (portLoopRegionMap_CPD3 E i q s.1 s.2)
    have huC : ∀ z, (uC z).1 = Φp (wz z) := fun z => (hPz z).symm
    have hvmem : ∀ z, Φq (wz z) ∈ OQᶜ := by
      intro z hz
      obtain ⟨w', hw', hw'P⟩ := hz
      have hw : w' = wz z := hΦqo.injective hw'
      rw [hw, hPz z] at hw'P
      obtain ⟨a, ha, haeq⟩ := hw'P
      have := cs.injective haeq
      exact ha (this ▸ portLoopMap_mem_region_CPD3 E i q s.1 s.2 z)
    let vv : C(Torus, ↥OQᶜ) :=
      ⟨fun z => ⟨Φq (wz z), hvmem z⟩,
        (hΦqo.continuous.comp hwz).subtype_mk _⟩
    have hcrossUV : ∀ z, (H.event j).RegularCrossing (uC z).1 (vv z).1 := fun z => by
      rw [huC z]; exact hcross _
    have key := kernel_le_exterior_of_regularCrossing_CPD8 (H.event j) OP OQ hOPo hP hQ hQP
      uC vv hcrossUV x
    have hk1 : (FundamentalGroup.map uC x).ker =
        (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q s.1 s.2) x).ker :=
      ker_comp_image_CPD8 cs (E.region s.1) OPᶜ hOPc.symm _ uC (fun z => rfl) x
    -- the ambient isotopy in the stage `j + 1`
    obtain ⟨Θ, hΘ⟩ := exists_ambient_stage_CPD8 E N Fs Ls hFL J U D hJo hJstart hJord hUo hSU hUd
      hJh hst s.1 τ.1 hsJ hτJ hs2.le j.succ hq1 hq2
    let gh : (H.stage j.succ).Carrier ≃ₜ (postStage T τ.1).Carrier := Θ.trans cτ.symm
    have hg3 : ∀ (i' : Fin L.cores.count) (c : (E.truncation i').core.Carrier),
        gh (Φq ((D i').z (s.1, (E.truncation i').inclusion c))) =
          L.cores.map i' τ.1 hτ' ((E.truncation i').inclusion c) := by
      intro i' c
      have h2 := hcastQ i' _ (hSU i' ⟨c, rfl⟩)
      show cτ.symm (Θ _) = _
      rw [hΘ i' c]
      exact (congrArg cτ.symm h2).trans (cτ.symm_apply_apply _)
    have hOQeq : ∀ q' : (H.stage j.succ).Carrier, q' ∈ OQ ↔
        ∃ (i' : Fin L.cores.count) (c : (E.truncation i').core.Carrier),
          c ∈ ((E.truncation i').core.interior : Set (E.truncation i').core.Carrier) ∧
          q' = Φq ((D i').z (s.1, (E.truncation i').inclusion c)) := by
      intro q'
      constructor
      · rintro ⟨w, rfl, ⟨a, ha, haeq⟩⟩
        obtain ⟨i', c, hc, hca⟩ := (notMem_region_iff_CPD8 E s.1 s.2 a).mp ha
        refine ⟨i', c, hc, ?_⟩
        have hw : w = (D i').z (s.1, (E.truncation i').inclusion c) := by
          apply hΦpo.injective
          rw [hcastP i' _ (hSU i' ⟨c, rfl⟩), ← haeq, ← hca]
        rw [hw]
      · rintro ⟨i', c, hc, rfl⟩
        refine ⟨_, rfl, ?_⟩
        refine ⟨L.cores.map i' s.1 hs' ((E.truncation i').inclusion c), ?_,
          (hcastP i' _ (hSU i' ⟨c, rfl⟩)).symm⟩
        exact (notMem_region_iff_CPD8 E s.1 s.2 _).mpr ⟨i', c, hc, rfl⟩
    have hgOQ : gh '' OQ = (E.region τ.1)ᶜ := by
      ext o
      constructor
      · rintro ⟨q', hq', rfl⟩
        obtain ⟨i', c, hc, rfl⟩ := (hOQeq q').mp hq'
        rw [hg3 i' c]
        exact (notMem_region_iff_CPD8 E τ.1 τ.2 _).mpr ⟨i', c, hc, rfl⟩
      · intro ho
        obtain ⟨i', c, hc, rfl⟩ := (notMem_region_iff_CPD8 E τ.1 τ.2 _).mp ho
        exact ⟨Φq ((D i').z (s.1, (E.truncation i').inclusion c)),
          (hOQeq _).mpr ⟨i', c, hc, rfl⟩, hg3 i' c⟩
    have hgOQc : gh '' OQᶜ = E.region τ.1 := by
      rw [gh.image_compl, hgOQ, compl_compl]
    have hk2 : (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q τ.1 τ.2) x).ker =
        (FundamentalGroup.map vv x).ker := by
      refine ker_comp_image_CPD8 gh OQᶜ (E.region τ.1) hgOQc vv
        (portLoopRegionMap_CPD3 E i q τ.1 τ.2) (fun z => ?_) x
      obtain ⟨c, hc⟩ := hczr z
      have := hg3 i c
      show L.cores.map i τ.1 (E.after_cores.trans τ.2) ((E.truncation i).cuspMap q (z, halfZero)) =
        gh (Φq (wz z))
      have h5 : wz z = (D i).z (s.1, (E.truncation i).inclusion c) := by
        show (D i).z (s.1, cz z) = _
        rw [hc]
      rw [h5, hg3 i c, ← hc]
      rfl
    rw [← hk1, hk2]
    exact key

end GC.LongTime.CuspP1
