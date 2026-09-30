import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCoreRetraction

set_option autoImplicit false

noncomputable section

open Set Topology Manifold
open scoped Manifold ContDiff ContinuousMap unitInterval

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

namespace TubeSystem

section ShrinkTime

theorem shrinkTime_le_one_of_le_one (s : I) {t : ℝ} (ht : t ≤ 1) :
    shrinkTime s t ≤ 1 := by
  rcases lt_or_ge 0 t with h | h
  · rw [shrinkTime_of_pos h]
    refine max_le ht ?_
    nlinarith [s.2.1, s.2.2, h, ht]
  · rw [shrinkTime_of_nonpos (not_lt.mpr h)]
    exact le_trans (min_le_left t ((1 - (s : ℝ)) * t - s)) ht

theorem neg_one_le_shrinkTime_of_neg_one_le (s : I) {t : ℝ} (ht : -1 ≤ t) :
    -1 ≤ shrinkTime s t := by
  rcases lt_or_ge 0 t with h | h
  · rw [shrinkTime_of_pos h]
    exact le_trans (by linarith) (le_max_left _ _)
  · rw [shrinkTime_of_nonpos (not_lt.mpr h)]
    refine le_min ht ?_
    have hs : (0 : ℝ) ≤ 1 - (s : ℝ) := by linarith [s.2.2]
    have h1 : (1 - (s : ℝ)) * (-1) ≤ (1 - (s : ℝ)) * t :=
      mul_le_mul_of_nonneg_left ht hs
    nlinarith

theorem shrinkTime_one_eq_neg_one_of_nonpos {u : ℝ} (h₁ : u ≤ 0) (h₂ : -1 ≤ u) :
    shrinkTime 1 u = -1 := by
  rw [shrinkTime_of_nonpos (not_lt.mpr h₁)]
  simp only [sub_self, zero_mul, zero_sub]
  exact min_eq_right h₂

theorem shrinkTime_one_eq_one_of_pos_of_le_one {u : ℝ} (h₁ : 0 < u) (h₂ : u ≤ 1) :
    shrinkTime 1 u = 1 := by
  rw [shrinkTime_of_pos h₁]
  simp only [sub_self, zero_mul, zero_add]
  exact max_eq_right h₂

theorem shrinkTime_one_comp_shrinkTime (s : I) (t : ℝ) :
    shrinkTime 1 (shrinkTime s t) = shrinkTime 1 t := by
  rcases lt_trichotomy t 0 with h | h | h
  · rcases lt_or_ge (-1 : ℝ) t with h₁ | h₁
    · have hle : shrinkTime s t ≤ 0 := by
        rw [shrinkTime_of_nonpos (not_lt.mpr h.le)]
        exact le_trans (min_le_left t ((1 - (s : ℝ)) * t - s)) h.le
      have hge : -1 ≤ shrinkTime s t := neg_one_le_shrinkTime_of_neg_one_le s (le_of_lt h₁)
      rw [shrinkTime_one_eq_neg_one_of_nonpos hle hge,
        shrinkTime_one_eq_neg_one_of_nonpos h.le (le_of_lt h₁)]
    · rw [shrinkTime_eq_self_of_le_neg_one s.2.1 h₁]
  · subst h
    have hle : shrinkTime s 0 ≤ 0 := by
      rw [shrinkTime_of_nonpos (not_lt.mpr le_rfl)]
      exact le_trans (min_le_left 0 ((1 - (s : ℝ)) * 0 - s)) le_rfl
    have hge : -1 ≤ shrinkTime s 0 := neg_one_le_shrinkTime_of_neg_one_le s (by norm_num)
    rw [shrinkTime_one_eq_neg_one_of_nonpos hle hge,
      shrinkTime_one_eq_neg_one_of_nonpos le_rfl (by norm_num)]
  · rcases lt_or_ge t 1 with h₁ | h₁
    · have hge : 0 < shrinkTime s t := by
        rw [shrinkTime_of_pos h]
        exact lt_of_lt_of_le h (le_max_left _ _)
      have hle : shrinkTime s t ≤ 1 := shrinkTime_le_one_of_le_one s (le_of_lt h₁)
      rw [shrinkTime_one_eq_one_of_pos_of_le_one hge hle,
        shrinkTime_one_eq_one_of_pos_of_le_one h (le_of_lt h₁)]
    · rw [shrinkTime_eq_self_of_one_le s.2.1 h₁]

theorem shrinkTube_one_comp_shrinkTube (s : I) (z : TubeDomain) :
    shrinkTube 1 (shrinkTube s z) = shrinkTube 1 z := by
  refine Prod.ext rfl (Subtype.ext ?_)
  exact shrinkTime_one_comp_shrinkTime s z.2.1

end ShrinkTime

section CoreFun

variable {M : Type*} [TopologicalSpace M] (T : TubeSystem M)

theorem coreFun_tube_one (a : T.Index) (z : TubeDomain) :
    T.coreFun ((1 : I), T.tube a z) = T.tube a (shrinkTube 1 z) := by
  classical
  by_cases hz : (-1 : ℝ) < z.2.1 ∧ z.2.1 < 1
  · rw [T.coreFun_eq_of_mem_removedBand (p := ((1 : I), T.tube a z)) ⟨z, hz, rfl⟩,
      T.tubeCoord_eq_of_eq_tube (x := T.tube a z) (mem_range_self z) rfl]
  · have hnotmem : ∀ a', T.tube a z ∉ T.removedBand a' := by
      intro a' ha'
      by_cases h : a' = a
      · subst a'
        obtain ⟨z', hz', hz'x⟩ := ha'
        have hzz : z' = z := (T.embedding a).injective hz'x
        exact hz (hzz ▸ hz')
      · exact (Set.disjoint_left.mp (T.disjoint h))
          (T.removedBand_subset_range a' ha') (Set.mem_range_self z)
    have hself : shrinkTube 1 z = z := by
      refine Prod.ext rfl (Subtype.ext ?_)
      have hle : z.2.1 ≤ -1 ∨ 1 ≤ z.2.1 := by
        by_cases h₁ : z.2.1 ≤ -1
        · exact Or.inl h₁
        · refine Or.inr ?_
          by_contra h₂
          exact hz ⟨not_le.mp h₁, not_le.mp h₂⟩
      rcases hle with h | h
      · exact shrinkTime_eq_self_of_le_neg_one (s := (1 : ℝ)) (by norm_num) h
      · exact shrinkTime_eq_self_of_one_le (s := (1 : ℝ)) (by norm_num) h
    rw [T.coreFun_eq_self_of_not_mem hnotmem, hself]

theorem coreFun_one_comp_coreFun (s : I) (x : M) :
    T.coreFun ((1 : I), T.coreFun (s, x)) = T.coreFun ((1 : I), x) := by
  classical
  by_cases h : ∃ a, x ∈ T.removedBand a
  · obtain ⟨a, ha⟩ := h
    set z := T.tubeCoord a x (T.removedBand_subset_range a ha) with hzdef
    have hxz : T.tube a z = x := T.tube_tubeCoord a x (T.removedBand_subset_range a ha)
    rw [← hxz]
    rw [T.coreFun_eq_of_mem_removedBand (p := (s, T.tube a z)) (by rw [hxz]; exact ha),
      T.tubeCoord_eq_of_eq_tube (x := T.tube a z) (mem_range_self z) rfl,
      T.coreFun_tube_one a (shrinkTube s z), T.coreFun_tube_one a z,
      shrinkTube_one_comp_shrinkTube]
  · rw [T.coreFun_eq_self_of_not_mem (p := (s, x)) fun a ha' => h ⟨a, ha'⟩]

theorem coreFun_one_comp_coreFun_of_mem_puncturedCore {x : M} (hx : x ∈ T.puncturedCore)
    (s : I) : T.coreFun ((1 : I), T.coreFun (s, x)) = T.coreFun ((1 : I), x) := by
  let _ := hx
  exact T.coreFun_one_comp_coreFun s x

end CoreFun


section Component

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] (T : TubeSystem M)

def puncturedCoreComponent (c : ConnectedComponents ↥T.core) : Set ↥T.puncturedCore :=
  {u | ConnectedComponents.mk ⟨T.coreFun ((1 : I), (u : M)),
    T.coreFun_mem_core (p := ((1 : I), (u : M))) u.2⟩ = c}

omit [T2Space M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem mem_puncturedCoreComponent_iff (c : ConnectedComponents ↥T.core)
    (u : ↥T.puncturedCore) :
    u ∈ T.puncturedCoreComponent c ↔
      ConnectedComponents.mk ⟨T.coreFun ((1 : I), (u : M)),
        T.coreFun_mem_core (p := ((1 : I), (u : M))) u.2⟩ = c :=
  Iff.rfl

omit [T2Space M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem mem_puncturedCoreComponent_of_mem_connectedComponents
    {c : ConnectedComponents ↥T.core} {x : ↥T.core} (hx : ConnectedComponents.mk x = c) :
    (⟨(x : M), T.core_subset_puncturedCore x.2⟩ : ↥T.puncturedCore) ∈
      T.puncturedCoreComponent c := by
  have h : (⟨T.coreFun ((1 : I), (x : M)),
      T.coreFun_mem_core (p := ((1 : I), (x : M)))
        (T.core_subset_puncturedCore x.2)⟩ : ↥T.core) = x :=
    Subtype.ext (T.coreFun_eq_self_of_mem_core x.2 1)
  exact (mem_puncturedCoreComponent_iff T c
    ⟨(x : M), T.core_subset_puncturedCore x.2⟩).mpr
    ((congrArg ConnectedComponents.mk h).trans hx)

omit [T2Space M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem coreFun_mem_puncturedCoreComponent {c : ConnectedComponents ↥T.core} (s : I)
    {u : ↥T.puncturedCore} (h : u ∈ T.puncturedCoreComponent c) :
    (⟨T.coreFun (s, (u : M)), T.coreFun_mem_puncturedCore u.2⟩ : ↥T.puncturedCore) ∈
      T.puncturedCoreComponent c := by
  have hpt : (⟨T.coreFun ((1 : I), T.coreFun (s, (u : M))),
      T.coreFun_mem_core (p := ((1 : I), T.coreFun (s, (u : M))))
        (T.coreFun_mem_puncturedCore u.2)⟩ : ↥T.core) =
      ⟨T.coreFun ((1 : I), (u : M)),
        T.coreFun_mem_core (p := ((1 : I), (u : M))) u.2⟩ :=
    Subtype.ext (T.coreFun_one_comp_coreFun s (u : M))
  exact (mem_puncturedCoreComponent_iff T c
    ⟨T.coreFun (s, (u : M)), T.coreFun_mem_puncturedCore u.2⟩).mpr
    ((congrArg ConnectedComponents.mk hpt).trans ((mem_puncturedCoreComponent_iff T c u).mp h))

noncomputable def coreComponentInclusion (c : ConnectedComponents ↥T.core) :
    C(ComponentCarrier c, ↥(T.puncturedCoreComponent c)) where
  toFun v := ⟨⟨(v.1 : M), T.core_subset_puncturedCore v.1.2⟩,
    T.mem_puncturedCoreComponent_of_mem_connectedComponents v.2⟩
  continuous_toFun := by
    have h₁ : Continuous fun v : ComponentCarrier c => (v.1 : M) :=
      continuous_subtype_val.comp continuous_subtype_val
    exact (h₁.subtype_mk fun v => T.core_subset_puncturedCore v.1.2).subtype_mk
      fun v => T.mem_puncturedCoreComponent_of_mem_connectedComponents v.2

noncomputable def coreComponentRetraction
    (hsm : ∀ a : T.Index, IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a))
    (c : ConnectedComponents ↥T.core) :
    C(↥(T.puncturedCoreComponent c), ComponentCarrier c) where
  toFun u := ⟨⟨T.coreFun ((1 : I), (u.1 : M)),
    T.coreFun_mem_core (p := ((1 : I), (u.1 : M))) u.1.2⟩,
    (mem_puncturedCoreComponent_iff T c u.1).mp u.2⟩
  continuous_toFun := by
    have h₂ : Continuous fun u : ↥(T.puncturedCoreComponent c) => (u.1 : ↥T.puncturedCore) :=
      continuous_subtype_val
    have h₁ : Continuous fun u : ↥(T.puncturedCoreComponent c) => ((1 : I), u.1) :=
      continuous_const.prodMk h₂
    have hmain : Continuous fun u : ↥(T.puncturedCoreComponent c) =>
        T.coreFun ((1 : I), (u.1 : M)) :=
      Continuous.comp (T.continuous_coreFun hsm) h₁
    exact (hmain.subtype_mk fun u =>
      T.coreFun_mem_core (p := ((1 : I), (u.1 : M))) u.1.2).subtype_mk
      fun u => (mem_puncturedCoreComponent_iff T c u.1).mp u.2

omit [IsManifold ThreeModel ∞ M] in
theorem coreComponentRetraction_comp_coreComponentInclusion
    (hsm : ∀ a : T.Index, IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a))
    (c : ConnectedComponents ↥T.core) :
    (coreComponentRetraction T hsm c).comp (coreComponentInclusion T c) =
      ContinuousMap.id (ComponentCarrier c) := by
  ext v
  exact T.coreFun_eq_self_of_mem_core v.1.2 1

noncomputable def coreComponentHomotopy
    (hsm : ∀ a : T.Index, IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a))
    (c : ConnectedComponents ↥T.core) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(T.puncturedCoreComponent c))
      ((coreComponentInclusion T c).comp (coreComponentRetraction T hsm c)) where
  toFun p := ⟨⟨T.coreFun (p.1, (p.2.1 : M)), T.coreFun_mem_puncturedCore p.2.1.2⟩,
    T.coreFun_mem_puncturedCoreComponent p.1 p.2.2⟩
  continuous_toFun := by
    have h₂ : Continuous fun p : I × ↥(T.puncturedCoreComponent c) =>
        (p.2.1 : ↥T.puncturedCore) :=
      continuous_subtype_val.comp continuous_snd
    have h₁ : Continuous fun p : I × ↥(T.puncturedCoreComponent c) => (p.1, p.2.1) :=
      continuous_fst.prodMk h₂
    have hmain : Continuous fun p : I × ↥(T.puncturedCoreComponent c) =>
        T.coreFun (p.1, (p.2.1 : M)) :=
      Continuous.comp (T.continuous_coreFun hsm) h₁
    exact (hmain.subtype_mk fun p => T.coreFun_mem_puncturedCore p.2.1.2).subtype_mk
      fun p => T.coreFun_mem_puncturedCoreComponent p.1 p.2.2
  map_zero_left u := by
    apply Subtype.ext
    apply Subtype.ext
    exact T.coreFun_zero ((0 : I), (u.1 : M))
  map_one_left u := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

omit [IsManifold ThreeModel ∞ M] in
theorem coreComponentInclusion_comp_coreComponentRetraction_homotopic_id
    (hsm : ∀ a : T.Index, IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a))
    (c : ConnectedComponents ↥T.core) :
    ((coreComponentInclusion T c).comp (coreComponentRetraction T hsm c)).Homotopic
      (ContinuousMap.id ↥(T.puncturedCoreComponent c)) :=
  ⟨(coreComponentHomotopy T hsm c).symm⟩

noncomputable def puncturedCoreComponentHomotopyEquivCoreComponent
    (hsm : ∀ a : T.Index, IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a))
    (c : ConnectedComponents ↥T.core) :
    ↥(T.puncturedCoreComponent c) ≃ₕ ComponentCarrier c :=
  (homotopyEquivOfRetraction (coreComponentInclusion T c) (coreComponentRetraction T hsm c)
    (coreComponentRetraction_comp_coreComponentInclusion T hsm c)
    (coreComponentInclusion_comp_coreComponentRetraction_homotopic_id T hsm c)).symm

omit [IsManifold ThreeModel ∞ M] in
theorem simplyConnectedSpace_puncturedCoreComponent_iff_coreComponent
    (hsm : ∀ a : T.Index, IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a))
    (c : ConnectedComponents ↥T.core) :
    SimplyConnectedSpace ↥(T.puncturedCoreComponent c) ↔
      SimplyConnectedSpace (ComponentCarrier c) :=
  (puncturedCoreComponentHomotopyEquivCoreComponent T hsm c).simplyConnectedSpace_iff

omit [IsManifold ThreeModel ∞ M] in
theorem simplyConnectedSpace_coreComponent_of_puncturedCoreComponent
    (hsm : ∀ a : T.Index, IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a))
    (c : ConnectedComponents ↥T.core)
    (h : SimplyConnectedSpace ↥(T.puncturedCoreComponent c)) :
    SimplyConnectedSpace (ComponentCarrier c) :=
  (puncturedCoreComponentHomotopyEquivCoreComponent T hsm c).simplyConnectedSpace_iff.mp h

end Component

end TubeSystem

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

theorem simplyConnectedSpace_childCore_of_puncturedCoreComponent
    (c : ConnectedComponents Q.Carrier)
    (h : SimplyConnectedSpace
      ↥(E.trace.tubes.puncturedCoreComponent (E.childCoreComponent c))) :
    SimplyConnectedSpace (E.ChildCore c) :=
  TubeSystem.simplyConnectedSpace_coreComponent_of_puncturedCoreComponent
    (T := E.trace.tubes) (fun a => E.tube_smooth a) (E.childCoreComponent c) h

noncomputable def childCoreInclusionRestrict (c : ConnectedComponents Q.Carrier)
    {U : Set (E.ChildCarrier c)} (hU : Set.range (E.childCoreInclusion c) ⊆ U) :
    C(E.ChildCore c, ↥U) :=
  ⟨fun x => ⟨E.childCoreInclusion c x, hU (Set.mem_range_self x)⟩,
    (E.childCoreInclusion c).continuous.subtype_mk _⟩

structure ChildCarrierCoreCapCover (c : ConnectedComponents Q.Carrier) : Type u where
  U : Set (E.ChildCarrier c)
  V : Set (E.ChildCarrier c)
  x₀ : E.ChildCarrier c
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  cover : U ∪ V = univ
  mem_x₀_U : x₀ ∈ U
  mem_x₀_V : x₀ ∈ V
  core_subset_U : Set.range (E.childCoreInclusion c) ⊆ U
  cap_subset_V : (⋃ b : E.ChildCapBoundary c, Set.range (E.childCap c b)) ⊆ V
  simplyConnected_V : SimplyConnectedSpace ↥V
  pathConnected_inter : PathConnectedSpace ↥(U ∩ V)
  retraction : C(↥U, E.ChildCore c)
  retraction_comp_inclusion :
    retraction.comp (childCoreInclusionRestrict E c core_subset_U) =
      ContinuousMap.id (E.ChildCore c)
  inclusion_comp_retraction_homotopic :
    ((childCoreInclusionRestrict E c core_subset_U).comp retraction).Homotopic
      (ContinuousMap.id ↥U)

theorem childCarrierOpenCover_of_childCarrierCoreCapCover
    (hd : ∀ c : ConnectedComponents Q.Carrier,
      SimplyConnectedSpace (P.component (E.childParent c)).Carrier →
        E.ChildCarrierCoreCapCover c)
    (hcore : ∀ c : ConnectedComponents Q.Carrier,
      SimplyConnectedSpace (P.component (E.childParent c)).Carrier →
        SimplyConnectedSpace (E.ChildCore c)) :
    E.childCarrierOpenCover := by
  intro c hpar
  let d := hd c hpar
  have hUsc : SimplyConnectedSpace ↥d.U :=
    (homotopyEquivOfRetraction (childCoreInclusionRestrict E c d.core_subset_U) d.retraction
      d.retraction_comp_inclusion d.inclusion_comp_retraction_homotopic).simplyConnectedSpace_iff.mp
      (hcore c hpar)
  exact ⟨d.U, d.V, d.x₀, d.isOpen_U, d.isOpen_V, d.cover, d.mem_x₀_U, d.mem_x₀_V,
    d.core_subset_U, d.cap_subset_V, hUsc, d.simplyConnected_V, d.pathConnected_inter⟩

theorem child_simplyConnected_of_childCarrierCoreCapCover
    (hd : ∀ c : ConnectedComponents Q.Carrier,
      SimplyConnectedSpace (P.component (E.childParent c)).Carrier →
        E.ChildCarrierCoreCapCover c)
    (hpc : ∀ c : ConnectedComponents Q.Carrier,
      SimplyConnectedSpace
        ↥(E.trace.tubes.puncturedCoreComponent (E.childCoreComponent c)))
    (c : ConnectedComponents Q.Carrier)
    [SimplyConnectedSpace (P.component (E.childParent c)).Carrier] :
    SimplyConnectedSpace (Q.component c).Carrier :=
  E.child_simplyConnected_of_childCarrierOpenCover
    (E.childCarrierOpenCover_of_childCarrierCoreCapCover hd
      fun c _ => E.simplyConnectedSpace_childCore_of_puncturedCoreComponent c (hpc c)) c

end SmoothCutCapTransition

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
