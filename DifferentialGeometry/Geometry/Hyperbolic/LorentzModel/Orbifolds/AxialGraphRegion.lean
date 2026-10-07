import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Geodesic.AxialProduct
import DifferentialGeometry.Topology.GraphBand

noncomputable section

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.AxisGeometry

private theorem closure_strict_subgraph {X : Type*} [TopologicalSpace X]
    (α : X → ℝ) (hα : Continuous α) :
    closure {z : X × ℝ | z.2 < α z.1} = {z : X × ℝ | z.2 ≤ α z.1} := by
  let e := DifferentialGeometry.Topology.graphBandHomeomorph α (fun x => α x + 1)
    hα (hα.add_const 1) (fun x => by linarith)
  have hlt : e '' (Set.univ ×ˢ Set.Iio (0 : ℝ)) = {z : X × ℝ | z.2 < α z.1} := by
    rw [e.image_eq_preimage_symm]
    ext z
    change (True ∧ (z.2 - α z.1) / ((α z.1 + 1) - α z.1) < 0) ↔ z.2 < α z.1
    simp
  have hle : e '' (Set.univ ×ˢ Set.Iic (0 : ℝ)) = {z : X × ℝ | z.2 ≤ α z.1} := by
    rw [e.image_eq_preimage_symm]
    ext z
    change (True ∧ (z.2 - α z.1) / ((α z.1 + 1) - α z.1) ≤ 0) ↔ z.2 ≤ α z.1
    simp
  rw [← hlt, ← e.image_closure, closure_prod_eq, closure_univ, closure_Iio, hle]

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open HyperbolicBoundary (BoundaryH poBoundaryMulAction)

variable (m : ℕ) (P : Subgroup (PO (m + 1) 1))

local instance : MulAction P (HUpper (m + 1)) := EquivariantMap.subAction (by omega) P

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
local notation "Q" => MulAction.orbitRel.Quotient P (HUpper (m + 1))
local notation "q" => Quotient.mk (MulAction.orbitRel P (HUpper (m + 1)))

variable (ξ η : BoundaryH (m + 1)) (hne : ξ ≠ η)
  (hpair : ∀ γ : P,
    (poBoundaryMulAction (by omega : 1 ≤ m + 1)).smul (γ : PO (m + 1) 1) ξ ∈ ({ξ, η} : Set (BoundaryH (m + 1))) ∧
    (poBoundaryMulAction (by omega : 1 ≤ m + 1)).smul (γ : PO (m + 1) 1) η ∈ ({ξ, η} : Set (BoundaryH (m + 1))))

local notation "R" => quotientAxisDistance m P ξ η hne hpair
local notation "O" => axisOffCore m P ξ η hne hpair
local notation "S" => {z : Q // R z = Real.arsinh 1}
local notation "C" => q '' axis ξ η

variable [DiscreteTopology P] [IsCancelSMul P (HUpper (m + 1))]

local instance : ProperlyDiscontinuousSMul P (HUpper (m + 1)) :=
  OrbifoldCompactness.properlyDiscontinuous_subAction (by omega) P
    (isDiscrete_iff_discreteTopology.mpr inferInstance)
local instance : ContinuousConstSMul P (HUpper (m + 1)) :=
  ⟨fun γ => (HyperbolicAction.contMDiff_po_smul m ∞ (γ : PO (m + 1) 1)).continuous⟩
local instance : ContMDiffConstSMul I ∞ P (HUpper (m + 1)) :=
  ⟨fun γ => HyperbolicAction.contMDiff_po_smul m ∞ (γ : PO (m + 1) 1)⟩
local instance : ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) Q := MulAction.instChartedSpaceQuotient
local instance : ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) O :=
  @TopologicalSpace.Opens.instChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) Q _ _
    (inferInstanceAs (ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) Q)) O
local instance : ChartedSpace (Fin m → ℝ) S := axisSectionChartedSpace m P ξ η hne hpair


private def axisProductMap (z : S × ℝ) : Q :=
  ((axisProductDiffeomorph m P ξ η hne hpair).toEquiv.symm z).val

local notation "A" => axisProductMap m P ξ η hne hpair

private theorem axisProductMap_injective : Function.Injective A := by
  intro x y hxy
  exact (axisProductDiffeomorph m P ξ η hne hpair).toEquiv.symm.injective (Subtype.ext hxy)

private theorem continuous_axisProductMap : Continuous A :=
  continuous_subtype_val.comp (axisProductDiffeomorph m P ξ η hne hpair).toHomeomorph.symm.continuous

private theorem isOpenMap_axisProductMap : IsOpenMap A :=
  ((O).isOpen.isOpenMap_subtype_val).comp (axisProductDiffeomorph m P ξ η hne hpair).toHomeomorph.symm.isOpenMap

private theorem axisProductMap_not_mem_core (z : S × ℝ) : A z ∉ C :=
  ((axisProductDiffeomorph m P ξ η hne hpair).toEquiv.symm z).property

private theorem range_axisProductMap : Set.range A = Cᶜ := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact axisProductMap_not_mem_core m P ξ η hne hpair w
  · intro hz
    exact ⟨axisProductDiffeomorph m P ξ η hne hpair ⟨z, hz⟩,
      congrArg Subtype.val ((axisProductDiffeomorph m P ξ η hne hpair).symm_apply_apply ⟨z, hz⟩)⟩

def axisGraphInward (α : S → ℝ) : Set Q := C ∪ A '' {z : S × ℝ | z.2 < α z.1}

def axisGraphClosed (α : S → ℝ) : Set Q := C ∪ A '' {z : S × ℝ | z.2 ≤ α z.1}

def axisGraph (α : S → ℝ) : Set Q := Set.range (fun s : S => A (s, α s))

local notation "U" => axisGraphInward m P ξ η hne hpair
local notation "K" => axisGraphClosed m P ξ η hne hpair
local notation "G" => axisGraph m P ξ η hne hpair

private theorem mem_axisGraphInward_map_iff (α : S → ℝ) (z : S × ℝ) :
    A z ∈ U α ↔ z.2 < α z.1 := by
  rw [axisGraphInward, Set.mem_union]
  constructor
  · intro hz
    rcases hz with hz | ⟨w, hw, he⟩
    · exact (axisProductMap_not_mem_core m P ξ η hne hpair z hz).elim
    · rwa [axisProductMap_injective m P ξ η hne hpair he] at hw
  · intro hz
    exact Or.inr ⟨z, hz, rfl⟩

private theorem mem_axisGraphClosed_map_iff (α : S → ℝ) (z : S × ℝ) :
    A z ∈ K α ↔ z.2 ≤ α z.1 := by
  rw [axisGraphClosed, Set.mem_union]
  constructor
  · intro hz
    rcases hz with hz | ⟨w, hw, he⟩
    · exact (axisProductMap_not_mem_core m P ξ η hne hpair z hz).elim
    · rwa [axisProductMap_injective m P ξ η hne hpair he] at hw
  · intro hz
    exact Or.inr ⟨z, hz, rfl⟩

theorem axisGraphInward_subset_axisGraphClosed (α : S → ℝ) : U α ⊆ K α := by
  rintro z (hz | ⟨w, hw, rfl⟩)
  · exact Or.inl hz
  · exact Or.inr ⟨w, (show w.2 < α w.1 from hw).le, rfl⟩

theorem axisGraphClosed_diff_axisGraphInward (α : S → ℝ) : K α \ U α = G α := by
  ext z
  constructor
  · rintro ⟨hzK, hzU⟩
    rcases hzK with hzC | ⟨⟨s, t⟩, ht, rfl⟩
    · exact (hzU (Or.inl hzC)).elim
    · have hn : ¬t < α s := fun h => hzU (Or.inr ⟨(s, t), h, rfl⟩)
      have he : t = α s := le_antisymm ht (le_of_not_gt hn)
      exact ⟨s, congrArg (fun t => A (s, t)) he.symm⟩
  · rintro ⟨s, rfl⟩
    exact ⟨Or.inr ⟨(s, α s), (show α s ≤ α s from le_rfl), rfl⟩,
      fun hu => (lt_irrefl (α s)) ((mem_axisGraphInward_map_iff m P ξ η hne hpair α (s, α s)).mp hu)⟩

theorem isClosed_axisGraphClosed (α : S → ℝ) (hα : Continuous α) : IsClosed (K α) := by
  have he : (K α)ᶜ = A '' {z : S × ℝ | α z.1 < z.2} := by
    ext z
    constructor
    · intro hz
      have hzC : z ∉ C := fun h => hz (Or.inl h)
      have hzrange : z ∈ Set.range A := by
        rw [range_axisProductMap m P ξ η hne hpair]
        exact hzC
      obtain ⟨w, rfl⟩ := hzrange
      exact ⟨w, (show α w.1 < w.2 from lt_of_not_ge (fun h => hz (Or.inr ⟨w, h, rfl⟩))), rfl⟩
    · rintro ⟨w, hw, rfl⟩ hk
      exact (not_le_of_gt hw) ((mem_axisGraphClosed_map_iff m P ξ η hne hpair α w).mp hk)
  rw [← isOpen_compl_iff, he]
  exact isOpenMap_axisProductMap m P ξ η hne hpair _
    (isOpen_lt (hα.comp continuous_fst) continuous_snd)

theorem exists_pos_radius_sublevel_subset_axisGraphInward [CompactSpace S]
    (α : S → ℝ) (hα : Continuous α) :
    ∃ δ > 0, {z : Q | R z < δ} ⊆ U α := by
  obtain ⟨c, hc⟩ := (isCompact_range hα).bddBelow
  refine ⟨Real.arsinh (Real.exp c), Real.arsinh_pos_iff.mpr (Real.exp_pos c), ?_⟩
  intro z hz
  by_cases hzC : z ∈ C
  · exact Or.inl hzC
  · let w : O := ⟨z, hzC⟩
    let d := axisProductDiffeomorph m P ξ η hne hpair
    have ht : (d w).2 < c := by
      rw [axisProductDiffeomorph_snd]
      change Real.log (Real.sinh (R z)) < c
      have hpos : 0 < Real.sinh (R z) :=
        Real.sinh_pos_iff.mpr (quotientAxisDistance_pos_of_mem_axisOffCore m P ξ η hne hpair w)
      apply (Real.log_lt_iff_lt_exp hpos).mpr
      have hs := Real.sinh_lt_sinh.mpr hz
      rwa [Real.sinh_arsinh] at hs
    refine Or.inr ⟨d w, ht.trans_le (hc ⟨(d w).1, rfl⟩), ?_⟩
    exact congrArg Subtype.val (d.symm_apply_apply w)

theorem isOpen_axisGraphInward [CompactSpace S] (α : S → ℝ) (hα : Continuous α) : IsOpen (U α) := by
  obtain ⟨δ, hδ, hsub⟩ := exists_pos_radius_sublevel_subset_axisGraphInward m P ξ η hne hpair α hα
  have he : U α = {z : Q | R z < δ} ∪ A '' {z : S × ℝ | z.2 < α z.1} := by
    apply Set.Subset.antisymm
    · rintro z (hz | hz)
      · left
        change R z < δ
        rw [(quotientAxisDistance_eq_zero_iff_mem_image_axis m P ξ η hne hpair z).mpr hz]
        exact hδ
      · exact Or.inr hz
    · exact Set.union_subset hsub (fun z hz => Or.inr hz)
  rw [he]
  exact (isOpen_lt (continuous_quotientAxisDistance m P ξ η hne hpair) continuous_const).union
    (isOpenMap_axisProductMap m P ξ η hne hpair _ (isOpen_lt continuous_snd (hα.comp continuous_fst)))

theorem closure_axisGraphInward (α : S → ℝ) (hα : Continuous α) : closure (U α) = K α := by
  apply Set.Subset.antisymm
  · exact (isClosed_axisGraphClosed m P ξ η hne hpair α hα).closure_subset_iff.mpr
      (axisGraphInward_subset_axisGraphClosed m P ξ η hne hpair α)
  · rintro z (hz | ⟨w, hw, rfl⟩)
    · exact subset_closure (Or.inl hz)
    · apply closure_mono (show A '' {z : S × ℝ | z.2 < α z.1} ⊆ U α from fun z hz => Or.inr hz)
      have hmem : A w ∈ A '' closure {z : S × ℝ | z.2 < α z.1} :=
        ⟨w, by rwa [closure_strict_subgraph α hα], rfl⟩
      exact image_closure_subset_closure_image (continuous_axisProductMap m P ξ η hne hpair) hmem

theorem frontier_axisGraphInward [CompactSpace S] (α : S → ℝ) (hα : Continuous α) :
    frontier (U α) = G α := by
  rw [frontier, closure_axisGraphInward m P ξ η hne hpair α hα,
    (isOpen_axisGraphInward m P ξ η hne hpair α hα).interior_eq,
    axisGraphClosed_diff_axisGraphInward]

theorem mem_axisGraphInward_iff (α : S → ℝ) (z : Q) :
    z ∈ U α ↔ z ∈ C ∨ ∃ s : S, ∃ t : ℝ, t < α s ∧
      quotientAxisRadialFlow m P ξ η hne hpair t s.val = z := by
  change (z ∈ C ∨ ∃ w : S × ℝ, w.2 < α w.1 ∧ A w = z) ↔ _
  simp only [Prod.exists]
  rfl

theorem mem_axisGraphClosed_iff (α : S → ℝ) (z : Q) :
    z ∈ K α ↔ z ∈ C ∨ ∃ s : S, ∃ t : ℝ, t ≤ α s ∧
      quotientAxisRadialFlow m P ξ η hne hpair t s.val = z := by
  change (z ∈ C ∨ ∃ w : S × ℝ, w.2 ≤ α w.1 ∧ A w = z) ↔ _
  simp only [Prod.exists]
  rfl

theorem axisGraph_eq_range_flow (α : S → ℝ) :
    G α = Set.range (fun s : S => quotientAxisRadialFlow m P ξ η hne hpair (α s) s.val) := rfl

theorem mem_axisGraphInward_flow_iff (α : S → ℝ) (s : S) (t : ℝ) :
    quotientAxisRadialFlow m P ξ η hne hpair t s.val ∈ U α ↔ t < α s :=
  mem_axisGraphInward_map_iff m P ξ η hne hpair α (s, t)

theorem mem_axisGraphClosed_flow_iff (α : S → ℝ) (s : S) (t : ℝ) :
    quotientAxisRadialFlow m P ξ η hne hpair t s.val ∈ K α ↔ t ≤ α s :=
  mem_axisGraphClosed_map_iff m P ξ η hne hpair α (s, t)

end DifferentialGeometry.AxisGeometry
