import DifferentialGeometry.Topology.VectorBundle.RankOneQuotient.UnitSphereCover

/-!
# The orientation of the unit sphere bundle induced by the total space

Lane LFR54-Q0, group G2. For a rank-one bundle `V` over a two-dimensional base with an oriented
total space, X112's `unitTangentOrientation` assigns to each unit vector `z` the orientation of
`T_{proj z} B` obtained by putting `z` first. In the covering atlas of `S(V)` the preferred chart
derivatives of `S(V)` are those of `B` at the projection (`unitSphere_preferredChartTangentEquiv`),
so this field is a smooth orientation of the surface `S(V)` (`unitSphereSmoothOrientation`), and
the fibre involution reverses it (`unitSphereSmoothOrientation_neg`): the unit sphere bundle is the
oriented orientation double cover, with the deck involution orientation reversing.
-/

set_option autoImplicit false

noncomputable section

open Bundle Module Filter Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.VectorBundle.RankOneQuotient

open DifferentialGeometry.Topology.Manifold

private theorem orientation_map_reindex_comm_LFR54Q0
    {W W' : Type*} [AddCommGroup W] [Module ℝ W] [AddCommGroup W'] [Module ℝ W']
    {ι κ : Type*} (e : W ≃ₗ[ℝ] W') (i : ι ≃ κ) (o : Orientation ℝ W ι) :
    Orientation.map κ e (Orientation.reindex ℝ W i o) =
      Orientation.reindex ℝ W' i (Orientation.map ι e o) := by
  induction o using Module.Ray.ind with
  | h v hv =>
    simp only [Orientation.map_apply, Orientation.reindex_apply]
    have heq : (v.domDomCongr i).compLinearMap (e.symm : W' →ₗ[ℝ] W) =
        (v.compLinearMap (e.symm : W' →ₗ[ℝ] W)).domDomCongr i := by
      ext x
      rfl
    simp only [heq]

section Charts

variable {EB F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {B : Type*} [TopologicalSpace B] [ChartedSpace EB B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ b, NormedAddCommGroup (V b)]
  (hp : IsLocalHomeomorph (fun z : {z : TotalSpace F V // ‖z.2‖ = 1} => z.val.proj))

omit [NormedSpace ℝ EB] in
/-- A point of the covering chart at `p` projects into the base chart at `proj p`. -/
theorem unitSphere_proj_mem_chart_source {p x : {z : TotalSpace F V // ‖z.2‖ = 1}}
    (hx : x ∈ (coveringChart (H := EB) hp p).source) :
    x.val.proj ∈ (chartAt EB p.val.proj).source := by
  have h := hx.2
  simpa only [OpenPartialHomeomorph.symm_symm, IsLocalHomeomorph.localInverseAt_symm,
    Set.mem_preimage] using h

variable [FiniteDimensional ℝ EB] [IsManifold 𝓘(ℝ, EB) ∞ B]

/-- The preferred chart derivatives of `S(V)` are those of the base at the projection. -/
theorem unitSphere_preferredChartTangentEquiv (p x : {z : TotalSpace F V // ‖z.2‖ = 1})
    (hx : x ∈ (coveringChart (H := EB) hp p).source) :
    letI := coveringChartedSpace (H := EB) hp
    letI : IsManifold 𝓘(ℝ, EB) ∞ {z : TotalSpace F V // ‖z.2‖ = 1} := unitSphere_isManifold hp
    preferredChartTangentEquiv 𝓘(ℝ, EB) p x hx =
      preferredChartTangentEquiv 𝓘(ℝ, EB) p.val.proj x.val.proj
        (unitSphere_proj_mem_chart_source hp hx) := by
  let _ := coveringChartedSpace (H := EB) hp
  let _ : IsManifold 𝓘(ℝ, EB) ∞ {z : TotalSpace F V // ‖z.2‖ = 1} := unitSphere_isManifold hp
  have hx' := unitSphere_proj_mem_chart_source hp hx
  ext v
  rw [preferredChartTangentEquiv_apply, preferredChartTangentEquiv_apply,
    unitSphere_extChartAt_eq (EB := EB) hp p]
  have hg : MDifferentiableAt 𝓘(ℝ, EB) 𝓘(ℝ, EB) (extChartAt 𝓘(ℝ, EB) p.val.proj) x.val.proj :=
    mdifferentiableAt_extChartAt hx'
  have hπ : MDifferentiableAt 𝓘(ℝ, EB) 𝓘(ℝ, EB)
      (fun w : {z : TotalSpace F V // ‖z.2‖ = 1} => w.val.proj) x :=
    (covering_projection_contMDiff hp 𝓘(ℝ, EB) x).mdifferentiableAt (by simp)
  have hcomp : (fun w : {z : TotalSpace F V // ‖z.2‖ = 1} =>
      extChartAt 𝓘(ℝ, EB) p.val.proj w.val.proj) =
      (extChartAt 𝓘(ℝ, EB) p.val.proj) ∘ (fun w : {z : TotalSpace F V // ‖z.2‖ = 1} =>
        w.val.proj) := rfl
  rw [hcomp, mfderiv_comp x hg hπ, mfderiv_unitSphere_proj (EB := EB) hp x]
  rfl

end Charts

section Orientation

variable {EB F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : Type*} [TopologicalSpace B] [ChartedSpace EB B] [IsManifold 𝓘(ℝ, EB) ∞ B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, EB)]
  (hp : IsLocalHomeomorph (fun z : {z : TotalSpace F V // ‖z.2‖ = 1} => z.val.proj))

attribute [local instance] DifferentialGeometry.VectorBundle.orientationTopology

/-- In the base chart at `c`, the orientation cover point of `z` has fibre coordinate the chart
transport of `unitTangentOrientation z`. -/
private theorem unitTangentCoverMap_localTriv_snd_LFR54Q0 (h2 : finrank ℝ EB = 2)
    (h1 : finrank ℝ F = 1) (o : ManifoldOrientation (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (TotalSpace F V) 3)
    (c : B) (z : {z : TotalSpace F V // ‖z.2‖ = 1}) (hz : z.val.proj ∈ (chartAt EB c).source) :
    ((DifferentialGeometry.VectorBundle.orientationCore (tangentBundleCore 𝓘(ℝ, EB) B) h2).localTriv
      (achart EB c) (unitTangentCoverMap (EB := EB) h2 h1 o z)).2 =
      Orientation.map (Fin 2) (preferredChartTangentEquiv 𝓘(ℝ, EB) c z.val.proj hz).toLinearEquiv
        (unitTangentOrientation (EB := EB) h2 h1 o z) := by
  have hh := (tangentOrientation_chart (E := EB) (M := B) h2 c z.val.proj hz
    (unitTangentOrientation (EB := EB) h2 h1 o z)).2
  have ht := continuousLinearEquivAt_trivializationAt_eq_preferredChartTangentEquiv
    (E := EB) (M := B) 𝓘(ℝ, EB) c z.val.proj hz
  exact hh.trans (congrArg (fun L : EB ≃L[ℝ] EB =>
      Orientation.map (Fin 2) L.toLinearEquiv (unitTangentOrientation (EB := EB) h2 h1 o z)) ht)

/-- The chart transport of `unitTangentOrientation` is locally constant on each base chart. -/
private theorem unitTangentOrientation_chart_isLocallyConstant_LFR54Q0 (h2 : finrank ℝ EB = 2)
    (h1 : finrank ℝ F = 1) (o : ManifoldOrientation (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (TotalSpace F V) 3)
    (c : B) (U : Set {z : TotalSpace F V // ‖z.2‖ = 1})
    (hU : ∀ z ∈ U, z.val.proj ∈ (chartAt EB c).source) :
    IsLocallyConstant (fun z : U =>
      Orientation.map (Fin 2)
        (preferredChartTangentEquiv 𝓘(ℝ, EB) c z.val.val.proj (hU z.val z.property)).toLinearEquiv
        (unitTangentOrientation (EB := EB) h2 h1 o z.val)) := by
  let Z := DifferentialGeometry.VectorBundle.orientationCore (tangentBundleCore 𝓘(ℝ, EB) B) h2
  let t := Z.localTriv (achart EB c)
  let orientationDiscrete_LFR54Q0 : DiscreteTopology (Orientation ℝ EB (Fin 2)) := ⟨rfl⟩
  have hmem : ∀ z : U, unitTangentCoverMap (EB := EB) h2 h1 o z.val ∈ t.source := fun z =>
    hU z.val z.property
  have hcont : Continuous (fun z : U => (t (unitTangentCoverMap (EB := EB) h2 h1 o z.val)).2) :=
    (t.continuousOn.comp_continuous
      ((unitTangentCoverMap_continuous h2 h1 o).comp continuous_subtype_val) hmem).snd
  have heq : (fun z : U => (t (unitTangentCoverMap (EB := EB) h2 h1 o z.val)).2) =
      fun z : U => Orientation.map (Fin 2)
        (preferredChartTangentEquiv 𝓘(ℝ, EB) c z.val.val.proj (hU z.val z.property)).toLinearEquiv
        (unitTangentOrientation (EB := EB) h2 h1 o z.val) := by
    funext z
    exact unitTangentCoverMap_localTriv_snd_LFR54Q0 h2 h1 o c z.val (hU z.val z.property)
  rw [← heq]
  exact (IsLocallyConstant.iff_continuous _).mpr hcont

/-- **T3.** The orientation of the surface `S(V)` (covering atlas) induced by the orientation of
the total space: at `z` it is X112's `unitTangentOrientation z`. -/
def unitSphereSmoothOrientation (h2 : finrank ℝ EB = 2) (h1 : finrank ℝ F = 1)
    (o : ManifoldOrientation (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (TotalSpace F V) 3) :
    letI := coveringChartedSpace (H := EB) hp
    letI : IsManifold 𝓘(ℝ, EB) ∞ {z : TotalSpace F V // ‖z.2‖ = 1} := unitSphere_isManifold hp
    SmoothOrientation 𝓘(ℝ, EB) {z : TotalSpace F V // ‖z.2‖ = 1} := by
  let _ := coveringChartedSpace (H := EB) hp
  let _ : IsManifold 𝓘(ℝ, EB) ∞ {z : TotalSpace F V // ‖z.2‖ = 1} := unitSphere_isManifold hp
  refine ⟨fun z => Orientation.reindex ℝ EB (finCongr h2.symm) (unitTangentOrientation (EB := EB) h2 h1 o z),
    fun p => ?_⟩
  have hU : ∀ z ∈ (chartAt EB p).source, z.val.proj ∈ (chartAt EB p.val.proj).source :=
    fun z hz => unitSphere_proj_mem_chart_source hp hz
  have hlc := (unitTangentOrientation_chart_isLocallyConstant_LFR54Q0 h2 h1 o p.val.proj
    (chartAt EB p).source hU).comp (Orientation.reindex ℝ EB (finCongr h2.symm))
  convert hlc using 1
  funext z
  simp only [Function.comp_apply]
  rw [unitSphere_preferredChartTangentEquiv hp p z.val z.property,
    orientation_map_reindex_comm_LFR54Q0]

theorem unitSphereSmoothOrientation_apply (h2 : finrank ℝ EB = 2) (h1 : finrank ℝ F = 1)
    (o : ManifoldOrientation (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (TotalSpace F V) 3)
    (z : {z : TotalSpace F V // ‖z.2‖ = 1}) :
    (unitSphereSmoothOrientation hp h2 h1 o).val z =
      Orientation.reindex ℝ EB (finCongr h2.symm) (unitTangentOrientation (EB := EB) h2 h1 o z) := rfl

/-- **T3, reversal.** The fibre involution reverses the induced orientation of `S(V)`. -/
theorem unitSphereSmoothOrientation_neg (h2 : finrank ℝ EB = 2) (h1 : finrank ℝ F = 1)
    (o : ManifoldOrientation (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (TotalSpace F V) 3)
    (z : {z : TotalSpace F V // ‖z.2‖ = 1}) :
    (unitSphereSmoothOrientation hp h2 h1 o).val (unitSphereNeg z) =
      -(unitSphereSmoothOrientation hp h2 h1 o).val z := by
  rw [unitSphereSmoothOrientation_apply, unitSphereSmoothOrientation_apply,
    ← Orientation.reindex_neg]
  exact congrArg (Orientation.reindex ℝ EB (finCongr h2.symm))
    (unitTangentOrientation_neg h2 h1 o z)

end Orientation

end DifferentialGeometry.Topology.VectorBundle.RankOneQuotient
