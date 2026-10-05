import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRoundedRegionPortShrink
import DifferentialGeometry.Topology.Manifold.OneManifold.CircleConsequences

/-!
# FC42 packet T3, part 2: the boundary circles of the rounded base and the level tori

The zero level `Λ = {b | rounding b = 0}` of the rounded base is a compact regular fibre of
`rounding : Base → ℝ` (`regularFiberChartedSpace`, `Topology/Manifold/SubmersionFiber.lean`), hence a
compact boundaryless `1`-manifold; it has finitely many components, each diffeomorphic to the circle
(`nonempty_circle_diffeomorph_of_finrank_eq_one`, `OneManifold/CircleClassification.lean`). Over the
component `c` lies the level torus `levelTorus c = val '' proj⁻¹(Γ_c)` in `W`; these are compact,
pairwise disjoint, and cover the new zero level `Z_R = roundedLevel`.

* `BaseLevel`, `baseLevelCharts` (the regular-fibre structure), `baseLevelComponent c`, `levelCircle c`;
* `exists_isOpen_inter_level_eq_levelCircle`: an open set of the base isolating `Γ_c` in the level;
* `levelTorus c`, `isCompact_levelTorus`, `iUnion_levelTorus`, `pairwise_disjoint_levelTorus`;
* `nonempty_circle_diffeomorph_baseLevelComponent`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace CircleRegion

variable {W : CompactCarrier.{u}} (R : CircleRegion W)

/-- A nonzero real linear functional is onto. -/
theorem surjective_of_ne_zero_real {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : E →L[ℝ] ℝ} (h : L ≠ 0) : Surjective L := by
  obtain ⟨v, hv⟩ : ∃ v, L v ≠ 0 := by
    by_contra hcon
    exact h (ContinuousLinearMap.ext fun v => not_not.mp fun hv => hcon ⟨v, hv⟩)
  intro t
  refine ⟨(t / L v) • v, ?_⟩
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ t hv]

theorem rounding_mfderiv_surjective (b : R.Base) (h : R.rounding b = 0) :
    Surjective (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) R.rounding b) :=
  surjective_of_ne_zero_real (R.rounding_regular b h)

/-- The model of the base level. -/
abbrev BaseLevelModel : Type :=
  Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) - Module.finrank ℝ ℝ) → ℝ

/-- The zero level of the rounding function. -/
abbrev BaseLevel : Type u :=
  {b : R.Base // R.rounding b = 0}

/-- The regular-fibre charts of the base level. -/
@[reducible]
def baseLevelCharts : ChartedSpace BaseLevelModel R.BaseLevel :=
  DifferentialGeometry.Topology.Manifold.regularFiberChartedSpace R.rounding 0 R.rounding_smooth
    R.rounding_mfderiv_surjective

theorem baseLevel_isManifold :
    letI := R.baseLevelCharts
    IsManifold 𝓘(ℝ, BaseLevelModel) ∞ R.BaseLevel :=
  DifferentialGeometry.Topology.Manifold.regularFiberIsManifold R.rounding 0 R.rounding_smooth
    R.rounding_mfderiv_surjective

theorem contMDiff_baseLevel_val :
    letI := R.baseLevelCharts
    ContMDiff 𝓘(ℝ, BaseLevelModel) (𝓡 2) ∞ (Subtype.val : R.BaseLevel → R.Base) :=
  DifferentialGeometry.Topology.Manifold.contMDiff_regularFiberInclusion R.rounding 0
    R.rounding_smooth R.rounding_mfderiv_surjective

variable {R} in
theorem contMDiff_baseLevel_iff {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    [TopologicalSpace HP] [TopologicalSpace P] [ChartedSpace HP P] {IP : ModelWithCorners ℝ EP HP}
    {g : P → R.BaseLevel} :
    letI := R.baseLevelCharts
    ContMDiff IP 𝓘(ℝ, BaseLevelModel) ∞ g ↔ ContMDiff IP (𝓡 2) ∞ (Subtype.val ∘ g) :=
  DifferentialGeometry.Topology.Manifold.contMDiff_regularFiber_iff R.rounding 0 R.rounding_smooth
    R.rounding_mfderiv_surjective g

theorem finrank_baseLevelModel : Module.finrank ℝ BaseLevelModel = 1 := by
  simp [BaseLevelModel]

theorem isCompact_level : IsCompact {b : R.Base | R.rounding b = 0} :=
  R.rounded_compact.of_isClosed_subset
    (isClosed_eq R.rounding_smooth.continuous continuous_const) fun _ hb => le_of_eq hb

instance baseLevel_compactSpace_ASMTOR : CompactSpace R.BaseLevel :=
  isCompact_iff_compactSpace.mp R.isCompact_level

instance baseLevel_locallyConnectedSpace_ASMTOR : LocallyConnectedSpace R.BaseLevel := by
  let _ := R.baseLevelCharts
  exact ChartedSpace.locallyConnectedSpace BaseLevelModel R.BaseLevel

/-! ## Components -/

/-- The connected component `c` of the base level, as an open subset. -/
def baseLevelComponent (c : ConnectedComponents R.BaseLevel) : TopologicalSpace.Opens R.BaseLevel :=
  ⟨ConnectedComponents.mk ⁻¹' {c}, (isOpen_discrete {c}).preimage ConnectedComponents.continuous_coe⟩

theorem isClosed_baseLevelComponent (c : ConnectedComponents R.BaseLevel) :
    IsClosed (R.baseLevelComponent c : Set R.BaseLevel) :=
  (isClosed_discrete {c}).preimage ConnectedComponents.continuous_coe

theorem isConnected_baseLevelComponent (c : ConnectedComponents R.BaseLevel) :
    IsConnected (R.baseLevelComponent c : Set R.BaseLevel) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  change IsConnected (ConnectedComponents.mk ⁻¹' {ConnectedComponents.mk x})
  rw [connectedComponents_preimage_singleton]
  exact isConnected_connectedComponent

instance baseLevelComponent_compactSpace_ASMTOR (c : ConnectedComponents R.BaseLevel) :
    CompactSpace (R.baseLevelComponent c) :=
  isCompact_iff_compactSpace.mp (R.isClosed_baseLevelComponent c).isCompact

instance baseLevelComponent_connectedSpace_ASMTOR (c : ConnectedComponents R.BaseLevel) :
    ConnectedSpace (R.baseLevelComponent c) :=
  Subtype.connectedSpace (R.isConnected_baseLevelComponent c)

/-- Every component of the base level is a circle. -/
theorem nonempty_circle_diffeomorph_baseLevelComponent (c : ConnectedComponents R.BaseLevel) :
    letI := R.baseLevelCharts
    Nonempty (Circle ≃ₘ⟮𝓡 1, 𝓘(ℝ, BaseLevelModel)⟯ (R.baseLevelComponent c)) := by
  let _ := R.baseLevelCharts
  have _ := R.baseLevel_isManifold
  exact DifferentialGeometry.Topology.Manifold.OneManifold.nonempty_circle_diffeomorph_of_finrank_eq_one
    BaseLevelModel BaseLevelModel (R.baseLevelComponent c) 𝓘(ℝ, BaseLevelModel)
    finrank_baseLevelModel

/-- The boundary circle `Γ_c ⊆ Base` of the component `c`. -/
def levelCircle (c : ConnectedComponents R.BaseLevel) : Set R.Base :=
  Subtype.val '' (R.baseLevelComponent c : Set R.BaseLevel)

theorem levelCircle_subset_level (c : ConnectedComponents R.BaseLevel) :
    R.levelCircle c ⊆ {b | R.rounding b = 0} := by
  rintro _ ⟨b, -, rfl⟩
  exact b.2

theorem isCompact_levelCircle (c : ConnectedComponents R.BaseLevel) :
    IsCompact (R.levelCircle c) :=
  (R.isClosed_baseLevelComponent c).isCompact.image continuous_subtype_val

theorem isConnected_levelCircle (c : ConnectedComponents R.BaseLevel) :
    IsConnected (R.levelCircle c) :=
  (R.isConnected_baseLevelComponent c).image _ continuous_subtype_val.continuousOn

theorem iUnion_levelCircle : (⋃ c, R.levelCircle c) = {b | R.rounding b = 0} := by
  apply Subset.antisymm (iUnion_subset R.levelCircle_subset_level)
  intro b hb
  exact mem_iUnion.mpr ⟨ConnectedComponents.mk ⟨b, hb⟩, ⟨b, hb⟩, rfl, rfl⟩

theorem pairwise_disjoint_levelCircle :
    Pairwise fun c c' : ConnectedComponents R.BaseLevel =>
      Disjoint (R.levelCircle c) (R.levelCircle c') := by
  intro c c' hcc'
  rw [Set.disjoint_left]
  rintro _ ⟨b, hb, rfl⟩ ⟨b', hb', hbb'⟩
  have : b' = b := Subtype.ext hbb'
  subst this
  exact hcc' (hb.symm.trans hb')

/-- An open set of the base isolating `Γ_c` in the level. -/
theorem exists_isOpen_inter_level_eq_levelCircle (c : ConnectedComponents R.BaseLevel) :
    ∃ G : Set R.Base, IsOpen G ∧ G ∩ {b | R.rounding b = 0} = R.levelCircle c := by
  obtain ⟨G, hG, hGeq⟩ := isOpen_induced_iff.mp (R.baseLevelComponent c).isOpen
  refine ⟨G, hG, ?_⟩
  ext b
  constructor
  · rintro ⟨hbG, hb⟩
    refine ⟨⟨b, hb⟩, ?_, rfl⟩
    change (⟨b, hb⟩ : R.BaseLevel) ∈ (R.baseLevelComponent c : Set R.BaseLevel)
    rw [← hGeq]
    exact hbG
  · rintro ⟨b', hb', rfl⟩
    refine ⟨?_, b'.2⟩
    have hb'' : b' ∈ (Subtype.val ⁻¹' G : Set R.BaseLevel) := by
      rw [hGeq]
      exact hb'
    exact hb''

/-! ## The level tori in `W` -/

/-- The level torus over `Γ_c`: the boundary component of the rounded circle region over it. -/
def levelTorus (c : ConnectedComponents R.BaseLevel) : Set W.Carrier :=
  Subtype.val '' (R.proj ⁻¹' R.levelCircle c)

theorem isCompact_levelTorus (c : ConnectedComponents R.BaseLevel) :
    IsCompact (R.levelTorus c) :=
  (R.isCompact_proj_preimage (R.isCompact_levelCircle c)).image continuous_subtype_val

theorem isConnected_levelTorus (c : ConnectedComponents R.BaseLevel) :
    IsConnected (R.levelTorus c) :=
  (R.isConnected_proj_preimage (R.isCompact_levelCircle c).isClosed
    (R.isConnected_levelCircle c)).image _ continuous_subtype_val.continuousOn

theorem levelTorus_subset_roundedLevel (c : ConnectedComponents R.BaseLevel) :
    R.levelTorus c ⊆ R.roundedLevel :=
  image_mono (preimage_mono (R.levelCircle_subset_level c))

theorem iUnion_levelTorus : (⋃ c, R.levelTorus c) = R.roundedLevel := by
  apply Subset.antisymm (iUnion_subset R.levelTorus_subset_roundedLevel)
  rintro _ ⟨y, hy, rfl⟩
  have hb : R.proj y ∈ ⋃ c, R.levelCircle c := by
    rw [R.iUnion_levelCircle]
    exact hy
  obtain ⟨c, hc⟩ := mem_iUnion.mp hb
  exact mem_iUnion.mpr ⟨c, y, hc, rfl⟩

theorem pairwise_disjoint_levelTorus :
    Pairwise fun c c' : ConnectedComponents R.BaseLevel =>
      Disjoint (R.levelTorus c) (R.levelTorus c') := by
  intro c c' hcc'
  rw [Set.disjoint_left]
  rintro _ ⟨y, hy, rfl⟩ ⟨y', hy', hyy'⟩
  have : y' = y := Subtype.ext hyy'
  subst this
  exact (R.pairwise_disjoint_levelCircle hcc').le_bot ⟨hy, hy'⟩

theorem levelTorus_subset_domain (c : ConnectedComponents R.BaseLevel) :
    R.levelTorus c ⊆ (R.domain : Set W.Carrier) := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

end CircleRegion

end GC.GraphManifold.Assembly
