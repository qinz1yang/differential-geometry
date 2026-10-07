import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.ThinRegions

namespace DifferentialGeometry.OrbifoldThinRegions

open Hyperbolic (HUpper)
open HyperbolicBoundary (BoundaryH)
open ProjectiveOrthogonalGroup (PO)
open BoundaryStabilizer (ElementaryGeometry)
open OrbifoldStrata (closedSmallSubgroup closedSmallSubgroup_le smallSubgroup_le_closedSmallSubgroup)

variable {n : ℕ}

theorem ball_subset_thinRegion
    (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    {r s : ℝ}
    (hgeom : ∀ y : HUpper n, ElementaryGeometry hn (closedSmallSubgroup hn Γ s y))
    {S : Set (BoundaryH n)} {x : HUpper n} (hx : x ∈ thinRegion hn Γ r S) :
    Metric.ball x ((s - r) / 2) ⊆ thinRegion hn Γ s S := by
  intro y hy
  have hd : 2 * dist y x + r < s := by
    have hxy : dist y x < (s - r) / 2 := hy
    linarith
  have hle : closedSmallSubgroup hn Γ r x ≤ closedSmallSubgroup hn Γ s y :=
    (closedSmallSubgroup_near_le hn Γ hd).trans (smallSubgroup_le_closedSmallSubgroup hn Γ s y)
  let _ := hx.1
  refine ⟨Infinite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle), ?_⟩
  exact hx.2.of_le (hΓ.mono (closedSmallSubgroup_le hn Γ s y)) hle (hgeom y)

theorem thinRegion_subset_interior
    (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    {r s : ℝ} (hrs : r < s)
    (hgeom : ∀ y : HUpper n, ElementaryGeometry hn (closedSmallSubgroup hn Γ s y))
    (S : Set (BoundaryH n)) :
    thinRegion hn Γ r S ⊆ interior (thinRegion hn Γ s S) := by
  intro x hx
  exact mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (Metric.ball_mem_nhds x (by linarith))
      (ball_subset_thinRegion hn Γ hΓ hgeom hx))

theorem exists_short_ne_one_of_mem_thinRegion
    (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) {r : ℝ} {y : HUpper n}
    {S : Set (BoundaryH n)} (hy : y ∈ thinRegion hn Γ r S) :
    ∃ a : Γ, a ≠ 1 ∧ dist ((HyperbolicAction.poMulAction hn).smul (a : PO n 1) y) y ≤ r := by
  classical
  by_contra hnone
  have hsmall : OrbifoldStrata.closedSmallElements hn Γ r y ⊆ (⊥ : Subgroup (PO n 1)) := by
    intro a ha
    have he : (⟨a, ha.1⟩ : Γ) = 1 := by
      by_contra hne
      exact hnone ⟨⟨a, ha.1⟩, hne, ha.2⟩
    exact congrArg Subtype.val he
  have hbot : closedSmallSubgroup hn Γ r y = ⊥ :=
    le_antisymm ((Subgroup.closure_le (⊥ : Subgroup (PO n 1))).mpr hsmall) bot_le
  have hfinite : Finite (closedSmallSubgroup hn Γ r y) := hbot ▸ inferInstance
  exact hy.1.false

theorem exists_thinRegion_of_short_infinite_order
    (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) {r : ℝ} (x : HUpper n)
    (hgeom : ElementaryGeometry hn (closedSmallSubgroup hn Γ r x))
    (γ : PO n 1) (hγ : γ ∈ Γ) (hinfinite : ¬ IsOfFinOrder γ)
    (hshort : dist ((HyperbolicAction.poMulAction hn).smul γ x) x ≤ r) :
    ∃ S : Set (BoundaryH n), x ∈ thinRegion hn Γ r S := by
  apply exists_thinRegion_of_not_finite hn Γ r x _ hgeom
  intro hfinite
  let _ : Finite (closedSmallSubgroup hn Γ r x) := hfinite
  have hmem : γ ∈ closedSmallSubgroup hn Γ r x := Subgroup.subset_closure ⟨hγ, hshort⟩
  exact hinfinite ((closedSmallSubgroup hn Γ r x).subtype.isOfFinOrder
    (isOfFinOrder_of_finite (⟨γ, hmem⟩ : closedSmallSubgroup hn Γ r x)))


theorem exists_thinRegion_of_isConnected
    (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    (r : ℝ)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (closedSmallSubgroup hn Γ r x))
    {C : Set (HUpper n)} (hC : IsConnected C)
    (hthin : C ⊆ (OrbifoldStrata.finiteLocus hn Γ r)ᶜ) :
    ∃ S : Set (BoundaryH n), C ⊆ thinRegion hn Γ r S := by
  classical
  obtain ⟨x, hx⟩ := hC.nonempty
  obtain ⟨S, hxS⟩ := exists_thinRegion_of_not_finite hn Γ r x (hthin hx) (hgeom x)
  let A := thinRegion hn Γ r S
  let B := ⋃ T : {T : Set (BoundaryH n) // T ≠ S}, thinRegion hn Γ r T.val
  have hA : IsClosed A := isClosed_thinRegion hn Γ hΓ r hgeom S
  have hB : IsClosed B :=
    ((locallyFinite_thinRegion hn Γ hΓ r).comp_injective Subtype.val_injective).isClosed_iUnion
      (fun T => isClosed_thinRegion hn Γ hΓ r hgeom T.val)
  have hd : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro y hyA hyB
    obtain ⟨T, hyT⟩ := Set.mem_iUnion.mp hyB
    let _ := hyA.1
    exact T.property (hyT.2.unique (hΓ.mono (closedSmallSubgroup_le hn Γ r y)) hyA.2)
  have hcover : C ⊆ A ∪ B := by
    intro y hy
    obtain ⟨T, hyT⟩ := exists_thinRegion_of_not_finite hn Γ r y (hthin hy) (hgeom y)
    by_cases hTS : T = S
    · left
      change y ∈ thinRegion hn Γ r S
      simpa only [hTS] using hyT
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨T, hTS⟩, hyT⟩)
  have hsep : C ∩ (A ∩ B) = ∅ := by
    rw [hd.inter_eq, Set.inter_empty]
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hC.isPreconnected
    A B hA hB hcover hsep with h | h
  · exact ⟨S, h⟩
  · exact False.elim (Set.disjoint_left.mp hd hxS (h hx))

end DifferentialGeometry.OrbifoldThinRegions
