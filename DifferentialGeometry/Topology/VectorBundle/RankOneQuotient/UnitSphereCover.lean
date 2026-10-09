import DifferentialGeometry.Topology.VectorBundle.UnitTangentCover
import DifferentialGeometry.Topology.VectorBundle.RankOneQuotient.Basic
import DifferentialGeometry.Topology.Manifold.CoveringAtlas
import DifferentialGeometry.Geometry.Collapse.SublevelCore.OpenDiskBundle

/-!
# The unit sphere bundle of a rank-one bundle as a smooth surface

Lane LFR54-Q0, group G2. Let `V → B` be a smooth Riemannian vector bundle of rank one over a
manifold modelled on `EB`. Its unit sphere bundle `S(V) = {z // ‖z.2‖ = 1}` is a double cover of
`B`; X112's `unitTangentCoverHomeomorph` identifies it (for compact Hausdorff `B` and an oriented
total space) with the tangent orientation cover, so the projection is a local homeomorphism
(`isLocalHomeomorph_unitSphere_proj`). With the covering atlas of a local homeomorphism
`hp` (`coveringChartedSpace`):

* `S(V)` is a smooth manifold and the projection is a local diffeomorphism
  (`isLocalDiffeomorph_unitSphere_proj`) with identity differential (`mfderiv_unitSphere_proj`);
* the inclusion `S(V) → TotalSpace F V` is smooth (`contMDiff_unitSphere_val`): near a point it is
  the smooth unit frame through its value composed with the projection;
* the fibre involution `τ z = -z` (`unitSphereNeg`) is a smooth free involution with identity
  differential (`contMDiff_unitSphereNeg`, `mfderiv_unitSphereNeg`);
* `S(V)` is compact (`unitSphere_compactSpace`) and, when its carrier set is preconnected,
  connected (`unitSphere_connectedSpace`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Module Filter Set Function
open scoped Manifold ContDiff Topology InnerProductSpace

namespace DifferentialGeometry.Topology.VectorBundle.RankOneQuotient

open DifferentialGeometry.Topology.Manifold

section Involution

variable {F : Type*} {B : Type*} {V : B → Type*} [∀ b, NormedAddCommGroup (V b)]

/-- The fibre involution `z ↦ -z` of the unit sphere bundle. -/
def unitSphereNeg (z : {z : TotalSpace F V // ‖z.2‖ = 1}) : {z : TotalSpace F V // ‖z.2‖ = 1} :=
  ⟨⟨z.val.proj, -z.val.2⟩, by simpa using z.property⟩

@[simp] theorem unitSphereNeg_val_proj (z : {z : TotalSpace F V // ‖z.2‖ = 1}) :
    (unitSphereNeg z).val.proj = z.val.proj := rfl

theorem unitSphereNeg_val (z : {z : TotalSpace F V // ‖z.2‖ = 1}) :
    (unitSphereNeg z).val = ⟨z.val.proj, -z.val.2⟩ := rfl

@[simp] theorem unitSphereNeg_unitSphereNeg (z : {z : TotalSpace F V // ‖z.2‖ = 1}) :
    unitSphereNeg (unitSphereNeg z) = z := by
  apply Subtype.ext
  change (⟨z.val.proj, - -z.val.2⟩ : TotalSpace F V) = z.val
  rw [neg_neg]

theorem unitSphereNeg_ne [∀ b, NormedSpace ℝ (V b)] (z : {z : TotalSpace F V // ‖z.2‖ = 1}) :
    unitSphereNeg z ≠ z := by
  intro h
  have h2 : -z.val.2 = z.val.2 := by
    have h' := congrArg (fun w : {z : TotalSpace F V // ‖z.2‖ = 1} => w.val) h
    exact (TotalSpace.mk_inj (b := z.val.proj)).mp h'
  have hz : z.val.2 = 0 := by
    have h3 : (2 : ℝ) • z.val.2 = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h2]
      exact neg_add_cancel _
    exact (smul_eq_zero.mp h3).resolve_left two_ne_zero
  have hn := z.property
  rw [hz, norm_zero] at hn
  exact zero_ne_one hn

end Involution

section Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {B : Type*} [TopologicalSpace B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- A smooth Riemannian bundle is a continuous Riemannian bundle. -/
theorem isContinuousRiemannianBundle_of_contMDiff {EB : Type*} [NormedAddCommGroup EB]
    [NormedSpace ℝ EB] [ChartedSpace EB B] [IsContMDiffRiemannianBundle 𝓘(ℝ, EB) ∞ F V] :
    IsContinuousRiemannianBundle F V := by
  obtain ⟨g, hg, heq⟩ := IsContMDiffRiemannianBundle.exists_contMDiff
    (IB := 𝓘(ℝ, EB)) (n := ∞) (F := F) (E := V)
  exact ⟨g, hg.continuous, heq⟩

/-- The unit sphere bundle over a compact base is compact. -/
theorem unitSphere_compactSpace [FiniteDimensional ℝ F] [CompactSpace B]
    [IsContinuousRiemannianBundle F V] :
    CompactSpace {z : TotalSpace F V // ‖z.2‖ = 1} :=
  isCompact_iff_compactSpace.mp (isCompact_sphereBundle (F := F) (V := V) 1)

/-- A preconnected unit sphere bundle of a rank-one bundle over a nonempty base is connected. -/
theorem unitSphere_connectedSpace [Nonempty B] (h1 : finrank ℝ F = 1)
    (hS : IsPreconnected {z : TotalSpace F V | ‖z.2‖ = 1}) :
    ConnectedSpace {z : TotalSpace F V // ‖z.2‖ = 1} := by
  let unitPreconnected : PreconnectedSpace {z : TotalSpace F V // ‖z.2‖ = 1} :=
    isPreconnected_iff_preconnectedSpace.mp hS
  let x : B := Classical.choice inferInstance
  obtain ⟨u, hu⟩ := exists_norm_eq_one_of_finrank_eq_one
    ((finrank_fiber (F := F) (V := V) x).trans h1)
  exact { toPreconnectedSpace := unitPreconnected, toNonempty := ⟨⟨⟨x, u⟩, hu⟩⟩ }

/-- The fibre involution of `S(V)` is continuous. -/
theorem continuous_unitSphereNeg : Continuous (unitSphereNeg (F := F) (V := V)) := by
  refine Continuous.subtype_mk (continuous_iff_continuousAt.mpr fun z => ?_) _
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨((FiberBundle.continuous_proj F V).comp continuous_subtype_val).continuousAt, ?_⟩
  let e := trivializationAt F V z.val.proj
  have hz : z.val ∈ e.source := FiberBundle.mem_trivializationAt_proj_source
  have hc : ContinuousAt (fun w : {z : TotalSpace F V // ‖z.2‖ = 1} => -(e w.val).2) z :=
    ((e.continuousOn.continuousAt (e.open_source.mem_nhds hz)).comp
      continuousAt_subtype_val).snd.neg
  apply hc.congr
  have hU : ∀ᶠ w : {z : TotalSpace F V // ‖z.2‖ = 1} in 𝓝 z, w.val.proj ∈ e.baseSet :=
    ((FiberBundle.continuous_proj F V).continuousAt.comp continuousAt_subtype_val).eventually
      (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt F V z.val.proj))
  filter_upwards [hU] with w hw
  change -(e ⟨w.val.proj, w.val.2⟩).2 = (e ⟨w.val.proj, -w.val.2⟩).2
  exact ((e.linear ℝ hw).map_neg w.val.2).symm

end Topology

section LocalHomeomorph

variable {EB F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : Type*} [TopologicalSpace B] [ChartedSpace EB B] [IsManifold 𝓘(ℝ, EB) ∞ B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, EB)]

/-- **T1.** The projection of the unit sphere bundle of an oriented rank-one total space over a
compact Hausdorff two-dimensional base is a local homeomorphism (through X112's identification with
the tangent orientation cover). -/
theorem isLocalHomeomorph_unitSphere_proj [CompactSpace B] [T2Space B]
    [IsContinuousRiemannianBundle F V] (h2 : finrank ℝ EB = 2) (h1 : finrank ℝ F = 1)
    (o : ManifoldOrientation (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (TotalSpace F V) 3) :
    IsLocalHomeomorph (fun z : {z : TotalSpace F V // ‖z.2‖ = 1} => z.val.proj) :=
  (tangentOrientationProjection_isCoveringMap (M := B) h2).isLocalHomeomorph.comp
    (unitTangentCoverHomeomorph h2 h1 o).isLocalHomeomorph

end LocalHomeomorph

section Smooth

variable {EB F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {B : Type*} [TopologicalSpace B] [ChartedSpace EB B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ b, NormedAddCommGroup (V b)]
  (hp : IsLocalHomeomorph (fun z : {z : TotalSpace F V // ‖z.2‖ = 1} => z.val.proj))

/-- In the covering atlas the chart at `z` is the base chart at `proj z` composed with `proj`. -/
theorem unitSphere_extChartAt_eq (z : {z : TotalSpace F V // ‖z.2‖ = 1}) :
    letI := coveringChartedSpace (H := EB) hp
    (extChartAt 𝓘(ℝ, EB) z : {z : TotalSpace F V // ‖z.2‖ = 1} → EB) =
      fun w => extChartAt 𝓘(ℝ, EB) z.val.proj w.val.proj := by
  let _ := coveringChartedSpace (H := EB) hp
  funext w
  rw [extChartAt_coe, extChartAt_coe]
  change 𝓘(ℝ, EB) (coveringChart hp z w) = 𝓘(ℝ, EB) (chartAt EB z.val.proj w.val.proj)
  rw [coveringChart_apply]

/-- A self-map of `S(V)` over the identity of `B` is the identity in covering charts. -/
theorem unitSphere_writtenInExtChartAt_eq_of_proj
    {f : {z : TotalSpace F V // ‖z.2‖ = 1} → {z : TotalSpace F V // ‖z.2‖ = 1}}
    (hf : ∀ z, (f z).val.proj = z.val.proj) (z : {z : TotalSpace F V // ‖z.2‖ = 1}) :
    letI := coveringChartedSpace (H := EB) hp
    writtenInExtChartAt 𝓘(ℝ, EB) 𝓘(ℝ, EB) z f =
      writtenInExtChartAt 𝓘(ℝ, EB) 𝓘(ℝ, EB) z
        (fun w : {z : TotalSpace F V // ‖z.2‖ = 1} => w.val.proj) := by
  let _ := coveringChartedSpace (H := EB) hp
  funext y
  simp only [writtenInExtChartAt, Function.comp_apply]
  rw [unitSphere_extChartAt_eq (EB := EB) hp (f z)]
  simp only [hf]

/-- The projection written in covering charts is the identity near the base point. -/
theorem unitSphere_writtenInExtChartAt_proj_eventuallyEq
    (z : {z : TotalSpace F V // ‖z.2‖ = 1}) :
    letI := coveringChartedSpace (H := EB) hp
    writtenInExtChartAt 𝓘(ℝ, EB) 𝓘(ℝ, EB) z
        (fun w : {z : TotalSpace F V // ‖z.2‖ = 1} => w.val.proj) =ᶠ[𝓝 (extChartAt 𝓘(ℝ, EB) z z)]
      id := by
  let _ := coveringChartedSpace (H := EB) hp
  have hz : extChartAt 𝓘(ℝ, EB) z z ∈ (coveringChart hp z).target :=
    (coveringChart hp z).map_source (mem_coveringChart_source hp z)
  filter_upwards [(coveringChart hp z).open_target.mem_nhds hz] with y hy
  simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_coe, extChartAt_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_apply, id]
  change chartAt EB z.val.proj (((coveringChart hp z).symm y).val.proj) = y
  rw [coveringChart_symm_projects hp z hy]
  exact (chartAt EB z.val.proj).right_inv hy.1

variable [IsManifold 𝓘(ℝ, EB) ∞ B]

/-- `S(V)` with the covering atlas is a smooth manifold. -/
theorem unitSphere_isManifold :
    letI := coveringChartedSpace (H := EB) hp
    IsManifold 𝓘(ℝ, EB) ∞ {z : TotalSpace F V // ‖z.2‖ = 1} :=
  covering_isManifold hp 𝓘(ℝ, EB)

/-- The projection of `S(V)` is a local diffeomorphism. -/
theorem isLocalDiffeomorph_unitSphere_proj :
    letI := coveringChartedSpace (H := EB) hp
    IsLocalDiffeomorph 𝓘(ℝ, EB) 𝓘(ℝ, EB) ∞
      (fun z : {z : TotalSpace F V // ‖z.2‖ = 1} => z.val.proj) :=
  covering_projection_isLocalDiffeomorph hp 𝓘(ℝ, EB)

/-- The differential of the projection of `S(V)` is the identity in covering charts. -/
theorem mfderiv_unitSphere_proj (z : {z : TotalSpace F V // ‖z.2‖ = 1}) :
    letI := coveringChartedSpace (H := EB) hp
    mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, EB) (fun z : {z : TotalSpace F V // ‖z.2‖ = 1} => z.val.proj) z =
      ContinuousLinearMap.id ℝ EB := by
  let _ := coveringChartedSpace (H := EB) hp
  let _ := covering_isManifold hp 𝓘(ℝ, EB)
  have hd : MDifferentiableAt 𝓘(ℝ, EB) 𝓘(ℝ, EB)
      (fun z : {z : TotalSpace F V // ‖z.2‖ = 1} => z.val.proj) z :=
    (covering_projection_contMDiff hp 𝓘(ℝ, EB) z).mdifferentiableAt (by simp)
  rw [hd.mfderiv_abuse, modelWithCornersSelf_coe, range_id, fderivWithin_univ,
    (unitSphere_writtenInExtChartAt_proj_eventuallyEq (EB := EB) hp z).fderiv_eq, fderiv_id]

/-- A smooth self-map of `S(V)` over the identity of `B` has identity differential. -/
theorem mfderiv_unitSphere_eq_id_of_proj
    {f : {z : TotalSpace F V // ‖z.2‖ = 1} → {z : TotalSpace F V // ‖z.2‖ = 1}}
    (hf : ∀ z, (f z).val.proj = z.val.proj) (z : {z : TotalSpace F V // ‖z.2‖ = 1})
    (hfd : letI := coveringChartedSpace (H := EB) hp
      MDifferentiableAt 𝓘(ℝ, EB) 𝓘(ℝ, EB) f z) :
    letI := coveringChartedSpace (H := EB) hp
    mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, EB) f z = ContinuousLinearMap.id ℝ EB := by
  let _ := coveringChartedSpace (H := EB) hp
  let _ := covering_isManifold hp 𝓘(ℝ, EB)
  have hd : MDifferentiableAt 𝓘(ℝ, EB) 𝓘(ℝ, EB)
      (fun z : {z : TotalSpace F V // ‖z.2‖ = 1} => z.val.proj) z :=
    (covering_projection_contMDiff hp 𝓘(ℝ, EB) z).mdifferentiableAt (by simp)
  have h := mfderiv_unitSphere_proj (EB := EB) hp z
  rw [hd.mfderiv_abuse] at h
  rw [hfd.mfderiv_abuse, unitSphere_writtenInExtChartAt_eq_of_proj (EB := EB) hp hf z]
  exact h

variable [∀ b, InnerProductSpace ℝ (V b)] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- The fibre involution of `S(V)` is smooth. -/
theorem contMDiff_unitSphereNeg :
    letI := coveringChartedSpace (H := EB) hp
    ContMDiff 𝓘(ℝ, EB) 𝓘(ℝ, EB) ∞ (unitSphereNeg (F := F) (V := V)) := by
  let _ := coveringChartedSpace (H := EB) hp
  intro z
  apply covering_lift_contMDiffAt hp 𝓘(ℝ, EB)
    (continuous_unitSphereNeg.continuousAt)
  exact (covering_projection_contMDiff hp 𝓘(ℝ, EB)) z

/-- The fibre involution of `S(V)` has identity differential in covering charts. -/
theorem mfderiv_unitSphereNeg (z : {z : TotalSpace F V // ‖z.2‖ = 1}) :
    letI := coveringChartedSpace (H := EB) hp
    mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, EB) (unitSphereNeg (F := F) (V := V)) z =
      ContinuousLinearMap.id ℝ EB := by
  let _ := coveringChartedSpace (H := EB) hp
  exact mfderiv_unitSphere_eq_id_of_proj (EB := EB) (f := unitSphereNeg) hp (fun _ => rfl) z
    (((contMDiff_unitSphereNeg (EB := EB) hp) z).mdifferentiableAt (by simp))

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, EB)] [IsContMDiffRiemannianBundle 𝓘(ℝ, EB) ∞ F V]

/-- **The inclusion `S(V) → TotalSpace F V` is smooth** for the covering atlas: near a point it
agrees with the smooth unit frame through its value, composed with the projection. -/
theorem contMDiff_unitSphere_val (h1 : finrank ℝ F = 1) :
    letI := coveringChartedSpace (H := EB) hp
    ContMDiff 𝓘(ℝ, EB) (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) ∞
      (Subtype.val : {z : TotalSpace F V // ‖z.2‖ = 1} → TotalSpace F V) := by
  let _ := coveringChartedSpace (H := EB) hp
  have hcont : IsContinuousRiemannianBundle F V :=
    isContinuousRiemannianBundle_of_contMDiff (EB := EB)
  intro z
  have hv : Orthonormal ℝ (fun _ : Fin 1 => z.val.2) :=
    orthonormal_subsingleton_iff.mpr (fun _ => z.property)
  obtain ⟨U, hU, hb, e, he, hon, heq⟩ :=
    exists_contMDiff_orthonormal_sections (I := 𝓘(ℝ, EB)) (F := F) (V := V) (m := ∞)
      z.val.proj (fun _ : Fin 1 => z.val.2) hv
  have hπ : ContMDiffAt 𝓘(ℝ, EB) 𝓘(ℝ, EB) ∞
      (fun w : {z : TotalSpace F V // ‖z.2‖ = 1} => w.val.proj) z :=
    covering_projection_contMDiff hp 𝓘(ℝ, EB) z
  have hsec : ContMDiffAt 𝓘(ℝ, EB) (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) ∞
      (fun y => (⟨y, e 0 y⟩ : TotalSpace F V)) z.val.proj :=
    (he 0).contMDiffAt (hU.mem_nhds hb)
  have hcomp := hsec.comp z hπ
  have hval : ContinuousAt (fun w : {z : TotalSpace F V // ‖z.2‖ = 1} =>
      (⟨w.val.proj, w.val.2⟩ : TotalSpace F V)) z :=
    continuous_subtype_val.continuousAt
  have hinner : ContinuousAt (fun w : {z : TotalSpace F V // ‖z.2‖ = 1} =>
      ⟪w.val.2, e 0 w.val.proj⟫_ℝ) z :=
    hval.inner_bundle (hcomp.continuousAt : ContinuousAt (fun w : {z : TotalSpace F V // ‖z.2‖ = 1} =>
      (⟨w.val.proj, e 0 w.val.proj⟩ : TotalSpace F V)) z)
  have hpos : 0 < ⟪z.val.2, e 0 z.val.proj⟫_ℝ := by
    rw [heq 0, real_inner_self_eq_norm_sq, z.property, one_pow]
    exact zero_lt_one
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hπ.continuousAt (hU.mem_nhds hb), hinner.eventually (lt_mem_nhds hpos)]
    with w hwU hwp
  have hex : ‖e 0 w.val.proj‖ = 1 := (hon w.val.proj hwU).norm_eq_one 0
  have hrank : finrank ℝ (V w.val.proj) = 1 := (finrank_fiber (F := F) (V := V) _).trans h1
  rcases eq_or_eq_neg_of_finrank_eq_one hrank hex w.property with hh | hh
  · exact congrArg (fun v => (⟨w.val.proj, v⟩ : TotalSpace F V)) hh
  · have hn : ⟪w.val.2, e 0 w.val.proj⟫_ℝ = -1 := by
      rw [hh, inner_neg_left, real_inner_self_eq_norm_sq, hex, one_pow]
    rw [hn] at hwp
    norm_num at hwp

end Smooth

end DifferentialGeometry.Topology.VectorBundle.RankOneQuotient
