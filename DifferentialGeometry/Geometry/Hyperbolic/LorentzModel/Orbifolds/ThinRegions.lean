/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Lattices.ElementaryEnds
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Lattices.ThickPoints
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.FiniteLocusCompactness

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.OrbifoldThinRegions

open Hyperbolic HyperbolicAction HyperbolicBoundary HyperbolicFaithful
open BoundaryStabilizer OrbifoldStrata ElementaryEnds

variable {n : ℕ}

def thinRegion (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (r : ℝ) (S : Set (BoundaryH n)) : Set (HUpper n) :=
  {x | Infinite (closedSmallSubgroup hn Γ r x) ∧
    HasEnds hn (closedSmallSubgroup hn Γ r x) S}

theorem closedSmallSubgroup_mono_group (hn : 1 ≤ n)
    {D E : Subgroup (PO n 1)} (hDE : D ≤ E) (r : ℝ) (x : HUpper n) :
    closedSmallSubgroup hn D r x ≤ closedSmallSubgroup hn E r x :=
  Subgroup.closure_mono (fun _ hg => ⟨hDE hg.1, hg.2⟩)

theorem closedSmallSubgroup_eq_of_le (hn : 1 ≤ n)
    {D E : Subgroup (PO n 1)} (hDE : D ≤ E) (r : ℝ) (x : HUpper n)
    (hle : closedSmallSubgroup hn E r x ≤ D) :
    closedSmallSubgroup hn D r x = closedSmallSubgroup hn E r x := by
  apply le_antisymm (closedSmallSubgroup_mono_group hn hDE r x)
  apply Subgroup.closure_mono
  intro g hg
  exact ⟨hle (Subgroup.subset_closure hg), hg.2⟩

theorem mem_thinRegion_not_finite {hn : 1 ≤ n} {Γ : Subgroup (PO n 1)}
    {r : ℝ} {S : Set (BoundaryH n)} {x : HUpper n}
    (hx : x ∈ thinRegion hn Γ r S) : x ∉ finiteLocus hn Γ r := by
  let := hx.1
  intro hf
  exact hf.false

theorem exists_thinRegion_of_not_finite (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (r : ℝ) (x : HUpper n) (hx : x ∉ finiteLocus hn Γ r)
    (hgeom : ElementaryGeometry hn (closedSmallSubgroup hn Γ r x)) :
    ∃ S : Set (BoundaryH n), x ∈ thinRegion hn Γ r S := by
  let : Infinite (closedSmallSubgroup hn Γ r x) := not_finite_iff_infinite.mp hx
  obtain ⟨S, hS⟩ := exists_ends hn _ hgeom
  exact ⟨S, inferInstance, hS⟩

theorem compl_finiteLocus_eq_iUnion (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (r : ℝ) (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (closedSmallSubgroup hn Γ r x)) :
    (finiteLocus hn Γ r)ᶜ = ⋃ S : Set (BoundaryH n), thinRegion hn Γ r S := by
  ext x
  constructor
  · intro hx
    exact mem_iUnion.mpr (exists_thinRegion_of_not_finite hn Γ r x hx (hgeom x))
  · intro hx
    obtain ⟨S, hxS⟩ := mem_iUnion.mp hx
    exact mem_thinRegion_not_finite hxS

theorem isClosed_thinRegion (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (r : ℝ)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (closedSmallSubgroup hn Γ r x))
    (S : Set (BoundaryH n)) : IsClosed (thinRegion hn Γ r S) := by
  apply isClosed_of_closure_subset
  intro x hx
  obtain ⟨y, hle, hy⟩ := mem_closure_iff_nhds.mp hx _
    (eventually_closedSmallSubgroup_le hn Γ hΓ r x)
  let := hy.1
  refine ⟨Infinite.of_injective (Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle), ?_⟩
  exact hy.2.of_le (hΓ.mono (closedSmallSubgroup_le hn Γ r x)) hle (hgeom x)

theorem finite_labels_meeting_compact (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (r : ℝ)
    {K : Set (HUpper n)} (hK : IsCompact K) :
    {S : Set (BoundaryH n) | (thinRegion hn Γ r S ∩ K).Nonempty}.Finite := by
  let A := (closedSmallSubgroup hn Γ r) '' K
  have hA : A.Finite := finite_closedSmallSubgroups_on_compact hn Γ hΓ r hK
  have hlabels (D : Subgroup (PO n 1)) (hD : D ∈ A) :
      {S : Set (BoundaryH n) | Infinite D ∧ HasEnds hn D S}.Finite := by
    obtain ⟨x, _, rfl⟩ := hD
    apply Set.Subsingleton.finite
    intro S hS T hT
    let := hS.1
    exact hS.2.unique (hΓ.mono (closedSmallSubgroup_le hn Γ r x)) hT.2
  apply (hA.biUnion hlabels).subset
  rintro S ⟨x, hxS, hxK⟩
  exact mem_iUnion₂.mpr ⟨closedSmallSubgroup hn Γ r x, ⟨x, hxK, rfl⟩, hxS⟩

theorem locallyFinite_thinRegion (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (r : ℝ) : LocallyFinite (thinRegion hn Γ r) := by
  intro x
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x zero_lt_one, ?_⟩
  apply (finite_labels_meeting_compact hn Γ hΓ r (isCompact_closedBall x 1)).subset
  rintro S ⟨y, hyS, hyball⟩
  exact ⟨y, hyS, Metric.ball_subset_closedBall hyball⟩

theorem closedSmallSubgroup_near_le (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    {r ε : ℝ} {x y : HUpper n} (hxy : 2 * dist x y + r < ε) :
    closedSmallSubgroup hn Γ r y ≤ Margulis.smallSubgroup hn Γ ε x := by
  let := poMulAction hn
  apply Subgroup.closure_mono
  intro g hg
  refine ⟨hg.1, ?_⟩
  have hd := dist_triangle (g • x) (g • y) x
  have hd' := dist_triangle (g • y) y x
  rw [po_dist_smul hn g x y] at hd
  rw [dist_comm y x] at hd'
  have hgy : dist (g • y) y ≤ r := hg.2
  change dist (g • x) x < ε
  linarith

theorem label_eq_of_dist_lt (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) {r ε : ℝ} (hr : r < ε)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x))
    {S T : Set (BoundaryH n)} {x y : HUpper n}
    (hx : x ∈ thinRegion hn Γ r S) (hy : y ∈ thinRegion hn Γ r T)
    (hxy : dist x y < (ε - r) / 2) : S = T := by
  let E := Margulis.smallSubgroup hn Γ ε x
  have hE : IsDiscrete (SetLike.coe E) := hΓ.mono (Margulis.smallSubgroup_le hn Γ ε x)
  have hxle : closedSmallSubgroup hn Γ r x ≤ E := closedSmallSubgroup_le_smallSubgroup hn Γ hr x
  have hyle : closedSmallSubgroup hn Γ r y ≤ E := closedSmallSubgroup_near_le hn Γ (by linarith)
  let := hx.1
  have hS : HasEnds hn E S := hx.2.of_le hE hxle (hgeom x)
  let := hy.1
  have hT : HasEnds hn E T := hy.2.of_le hE hyle (hgeom x)
  let : Infinite E := Infinite.of_injective (Subgroup.inclusion hxle) (Subgroup.inclusion_injective _)
  exact hS.unique hE hT

theorem separation (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) {r ε : ℝ} (hr : r < ε)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x))
    {S T : Set (BoundaryH n)} (hne : S ≠ T) {x y : HUpper n}
    (hx : x ∈ thinRegion hn Γ r S) (hy : y ∈ thinRegion hn Γ r T) :
    (ε - r) / 2 ≤ dist x y :=
  le_of_not_gt (fun h => hne (label_eq_of_dist_lt hn Γ hΓ hr hgeom hx hy h))

theorem thinRegion_ne_univ (hn : 1 ≤ n) (hdim : 2 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    {r : ℝ} (hr : 0 ≤ r) (S : Set (BoundaryH n)) :
    thinRegion hn Γ r S ≠ univ := by
  intro he
  have hx : basepointH ∈ thinRegion hn Γ r S := he.symm ▸ mem_univ _
  let E := Γ ⊓ setStabilizer hn S
  have hE : IsDiscrete (SetLike.coe E) := hΓ.mono inf_le_left
  obtain ⟨p, hp⟩ := ElementaryThickPoint.finiteLocus_nonempty_of_geometry hn hdim E hE hr
    (geometry_setStabilizer hn Γ hΓ hx.2)
  have hpS : p ∈ thinRegion hn Γ r S := he.symm ▸ mem_univ p
  have hle : closedSmallSubgroup hn Γ r p ≤ E :=
    le_inf (closedSmallSubgroup_le hn Γ r p) hpS.2.le_setStabilizer
  have heq := closedSmallSubgroup_eq_of_le hn (show E ≤ Γ from inf_le_left) r p hle
  let := hpS.1
  have hf : Finite (closedSmallSubgroup hn Γ r p) := heq ▸ hp
  exact hf.false

theorem frontier_subset_closure_finiteLocus (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    {r ε : ℝ} (hr : r < ε)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x))
    (S : Set (BoundaryH n)) :
    frontier (thinRegion hn Γ r S) ⊆ closure (finiteLocus hn Γ r) := by
  have hcgeom (x : HUpper n) := closedSmallSubgroup_geometry hn Γ hr x (hgeom x)
  have hc := isClosed_thinRegion hn Γ hΓ r hcgeom S
  intro x hx
  have hxS : x ∈ thinRegion hn Γ r S := hc.closure_eq ▸ hx.1
  by_contra hxf
  have hnS : thinRegion hn Γ r S ∈ 𝓝 x := by
    apply Filter.mem_of_superset
      (inter_mem (Metric.ball_mem_nhds x (by linarith : 0 < (ε - r) / 2))
        (isClosed_closure.isOpen_compl.mem_nhds hxf))
    rintro y ⟨hyball, hyf⟩
    have hyfinite : y ∉ finiteLocus hn Γ r := fun h => hyf (subset_closure h)
    obtain ⟨T, hyT⟩ := exists_thinRegion_of_not_finite hn Γ r y hyfinite (hcgeom y)
    have he := label_eq_of_dist_lt hn Γ hΓ hr hgeom hxS hyT
      (by simpa only [Metric.mem_ball, dist_comm] using hyball)
    rwa [he]
  exact hx.2 (mem_interior_iff_mem_nhds.mpr hnS)

theorem frontier_nonempty (hn : 1 ≤ n) (hdim : 2 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    {r : ℝ} (hr : 0 ≤ r) {S : Set (BoundaryH n)}
    (hS : (thinRegion hn Γ r S).Nonempty) :
    (frontier (thinRegion hn Γ r S)).Nonempty := by
  let := HyperbolicGeodesic.pathConnectedSpace hn
  exact nonempty_frontier_iff.mpr ⟨hS, thinRegion_ne_univ hn hdim Γ hΓ hr S⟩

theorem finiteLocus_nonempty (hn : 1 ≤ n) (hdim : 2 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    {r ε : ℝ} (hr : 0 ≤ r) (hre : r < ε)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x)) :
    (finiteLocus hn Γ r).Nonempty := by
  by_cases hx : basepointH ∈ finiteLocus hn Γ r
  · exact ⟨basepointH, hx⟩
  obtain ⟨S, hxS⟩ := exists_thinRegion_of_not_finite hn Γ r basepointH hx
    (closedSmallSubgroup_geometry hn Γ hre basepointH (hgeom basepointH))
  obtain ⟨x, hxf⟩ := frontier_nonempty hn hdim Γ hΓ hr ⟨basepointH, hxS⟩
  exact (show (closure (finiteLocus hn Γ r)).Nonempty from
    ⟨x, frontier_subset_closure_finiteLocus hn Γ hΓ hre hgeom S hxf⟩).of_closure

theorem smul_mem_thinRegion (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) (r : ℝ)
    {S : Set (BoundaryH n)} {x : HUpper n} (hx : x ∈ thinRegion hn Γ r S) (γ : Γ) :
    (poMulAction hn).smul (γ : PO n 1) x ∈ thinRegion hn Γ r
      ((fun ξ : BoundaryH n => (poBoundaryMulAction hn).smul (γ : PO n 1) ξ) '' S) := by
  let := hx.1
  have he := closedSmallSubgroup_map_conj hn Γ r x γ
  have hinf : Infinite ((closedSmallSubgroup hn Γ r x).map
      (MulAut.conj (γ : PO n 1)).toMonoidHom) :=
    ((closedSmallSubgroup hn Γ r x).equivMapOfInjective
      (MulAut.conj (γ : PO n 1)).toMonoidHom (MulAut.conj (γ : PO n 1)).injective).toEquiv.infinite_iff.mp
        inferInstance
  exact ⟨he ▸ hinf, he ▸ hx.2.conj γ⟩

theorem image_thinRegion (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) (r : ℝ)
    (S : Set (BoundaryH n)) (γ : Γ) :
    (fun x : HUpper n => (poMulAction hn).smul (γ : PO n 1) x) '' thinRegion hn Γ r S =
      thinRegion hn Γ r
        ((fun ξ : BoundaryH n => (poBoundaryMulAction hn).smul (γ : PO n 1) ξ) '' S) := by
  let := poMulAction hn
  let := poBoundaryMulAction hn
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact smul_mem_thinRegion hn Γ r hx γ
  · intro x hx
    have hi := smul_mem_thinRegion hn Γ r hx γ⁻¹
    change (γ : PO n 1)⁻¹ • x ∈ thinRegion hn Γ r
      ((fun ξ : BoundaryH n => (γ : PO n 1)⁻¹ • ξ) ''
        ((fun ξ : BoundaryH n => (γ : PO n 1) • ξ) '' S)) at hi
    simp only [image_image, inv_smul_smul, image_id'] at hi
    exact ⟨(γ : PO n 1)⁻¹ • x, hi, smul_inv_smul _ _⟩

theorem exists_finite_thin_representatives (hn : 1 ≤ n) (hdim : 2 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤)
    {r ε : ℝ} (hr : 0 < r) (hre : r < ε)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x)) :
    ∃ A : Set (Set (BoundaryH n)), A.Finite ∧
      ∀ S : Set (BoundaryH n), (thinRegion hn Γ r S).Nonempty →
        ∃ γ : Γ, (fun ξ : BoundaryH n => (poBoundaryMulAction hn).smul (γ : PO n 1) ξ) '' S ∈ A := by
  have hcgeom (x : HUpper n) := closedSmallSubgroup_geometry hn Γ hre x (hgeom x)
  obtain ⟨K, hK, _, hcover⟩ := FiniteLocusCompactness.exists_compact_finiteLocus_core
    hn hdim Γ hΓ hcov hr hcgeom
  refine ⟨{S | (thinRegion hn Γ r S ∩ K).Nonempty},
    finite_labels_meeting_compact hn Γ hΓ r hK, ?_⟩
  intro S hS
  obtain ⟨x, hx⟩ := frontier_nonempty hn hdim Γ hΓ hr.le hS
  obtain ⟨γ, hγ⟩ := hcover x (frontier_subset_closure_finiteLocus hn Γ hΓ hre hgeom S hx)
  have hxS : x ∈ thinRegion hn Γ r S :=
    (isClosed_thinRegion hn Γ hΓ r hcgeom S).closure_eq ▸ hx.1
  exact ⟨γ, (poMulAction hn).smul (γ : PO n 1) x, smul_mem_thinRegion hn Γ r hxS γ, hγ⟩

theorem parabolic_closedRegion_subset (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (r : ℝ)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (closedSmallSubgroup hn Γ r x))
    (ξ : BoundaryH n) :
    ParabolicRegions.closedRegion hn Γ r ξ ⊆ thinRegion hn Γ r {ξ} := by
  rintro x ⟨g, hg, hshort⟩
  let D := closedSmallSubgroup hn Γ r x
  let a : D := ⟨g, Subgroup.subset_closure ⟨g.property, hshort⟩⟩
  have hinf : Infinite D := not_finite_iff_infinite.mp (fun hf => by
    let := hf
    exact hg.infinite_order (D.subtype.isOfFinOrder (isOfFinOrder_of_finite a)))
  refine ⟨hinf, Or.inl ⟨ξ, rfl, ?_⟩⟩
  exact ParabolicRegions.horospherical_of_contains_parabolic hn D
    (hΓ.mono (closedSmallSubgroup_le hn Γ r x)) (hgeom x) a hg

theorem exists_finite_parabolic_representatives (hn : 1 ≤ n) (hdim : 2 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤)
    {r ε : ℝ} (hr : 0 < r) (hre : r < ε)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x)) :
    ∃ A : Set (BoundaryH n), A.Finite ∧ ∀ ξ : BoundaryH n,
      (∃ g : Γ, ParabolicRegions.IsParabolicAt hn (g : PO n 1) ξ) →
        ∃ γ : Γ, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ ∈ A := by
  obtain ⟨A, hA, hcover⟩ := exists_finite_thin_representatives hn hdim Γ hΓ hcov hr hre hgeom
  refine ⟨(fun ξ : BoundaryH n => ({ξ} : Set (BoundaryH n))) ⁻¹' A,
    hA.preimage singleton_injective.injOn, ?_⟩
  rintro ξ ⟨g, hg⟩
  obtain ⟨x, a, ha, hshort⟩ := ParabolicRegions.region_nonempty hn Γ hr g hg
  have hx : x ∈ thinRegion hn Γ r {ξ} := parabolic_closedRegion_subset hn Γ hΓ r
    (fun x => closedSmallSubgroup_geometry hn Γ hre x (hgeom x)) ξ ⟨a, ha, hshort.le⟩
  obtain ⟨γ, hγ⟩ := hcover {ξ} ⟨x, hx⟩
  exact ⟨γ, by simpa only [mem_preimage, image_singleton] using hγ⟩

end DifferentialGeometry.OrbifoldThinRegions
