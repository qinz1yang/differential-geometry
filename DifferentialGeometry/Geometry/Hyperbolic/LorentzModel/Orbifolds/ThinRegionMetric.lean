import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.ThinRegionQuotient
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Geodesic.Interpolation

noncomputable section

namespace DifferentialGeometry.OrbifoldThinRegions

open Hyperbolic (HUpper)
open HyperbolicBoundary (BoundaryH poBoundaryMulAction)
open HyperbolicAction (poMulAction)
open ProjectiveOrthogonalGroup (PO)
open OrbifoldStrata (closedSmallSubgroup_le)
open Set

variable {n : ℕ} (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
  (hΓ : IsDiscrete (SetLike.coe Γ)) (r : ℝ)

local notation "π" => Quotient.mk (@MulAction.orbitRel Γ (HUpper n) _ (EquivariantMap.subAction hn Γ))

include hΓ in
private theorem subset_interior_thinRegion_of_isPreconnected
    {C : Set (HUpper n)} (hC : IsPreconnected C) {S : Set (BoundaryH n)}
    (hmem : (C ∩ interior (thinRegion hn Γ r S)).Nonempty)
    (hcover : C ⊆ ⋃ T : Set (BoundaryH n), interior (thinRegion hn Γ r T)) :
    C ⊆ interior (thinRegion hn Γ r S) := by
  let A := interior (thinRegion hn Γ r S)
  let B := ⋃ T : {T : Set (BoundaryH n) // T ≠ S}, interior (thinRegion hn Γ r T.val)
  have hd : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro y hyA hyB
    obtain ⟨T, hyT⟩ := mem_iUnion.mp hyB
    have hys := interior_subset hyA
    have hyt := interior_subset hyT
    let _ := hys.1
    exact T.property (hyt.2.unique (hΓ.mono (closedSmallSubgroup_le hn Γ r y)) hys.2)
  have hcover' : C ⊆ A ∪ B := by
    intro y hy
    obtain ⟨T, hyT⟩ := mem_iUnion.mp (hcover hy)
    by_cases hTS : T = S
    · exact Or.inl (by change y ∈ interior (thinRegion hn Γ r S); rwa [hTS] at hyT)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨T, hTS⟩, hyT⟩)
  exact hC.subset_left_of_subset_union isOpen_interior (isOpen_iUnion fun _ => isOpen_interior)
    hd hcover' hmem

include hΓ in
theorem ball_subset_interior_thinRegion_of_quotient_image_subset
    (S : Set (BoundaryH n)) {p : HUpper n} (hp : p ∈ interior (thinRegion hn Γ r S))
    {R : ℝ}
    (hball : π '' Metric.ball p R ⊆ π '' interior (thinRegion hn Γ r S)) :
    Metric.ball p R ⊆ interior (thinRegion hn Γ r S) := by
  intro z hz
  by_cases hpz : p = z
  · exact hpz ▸ hp
  let c := HyperbolicConvexity.geodFromTo p z hpz
  let C : Set (HUpper n) := c '' Icc 0 (dist p z)
  have hc0 : c 0 = p := HyperbolicConvexity.geodFromTo_zero hpz
  have hc1 : c (dist p z) = z := HyperbolicConvexity.geodFromTo_dist hpz
  have hC : IsPreconnected C :=
    isPreconnected_Icc.image c (HyperbolicConvexity.continuous_geodFromTo hpz).continuousOn
  have hpC : p ∈ C := ⟨0, ⟨le_rfl, dist_nonneg⟩, hc0⟩
  have hzC : z ∈ C := ⟨dist p z, ⟨dist_nonneg, le_rfl⟩, hc1⟩
  have hCB : C ⊆ Metric.ball p R := by
    rintro y ⟨t, ht, rfl⟩
    have he : dist (c t) p = t := by
      rw [← hc0, HyperbolicConvexity.dist_geodFromTo]
      simpa only [sub_zero] using abs_of_nonneg ht.1
    change dist (c t) p < R
    rw [he]
    exact ht.2.trans_lt (by simpa only [Metric.mem_ball, dist_comm] using hz)
  have hcover : C ⊆ ⋃ T : Set (BoundaryH n), interior (thinRegion hn Γ r T) := by
    intro y hy
    obtain ⟨u, hu, heq⟩ := hball ⟨y, hCB hy, rfl⟩
    obtain ⟨γ, hγ⟩ := Quotient.exact heq.symm
    have hsmul : (poMulAction hn).smul (γ : PO n 1) u = y := hγ
    apply mem_iUnion.mpr
    refine ⟨(fun ξ : BoundaryH n => (poBoundaryMulAction hn).smul (γ : PO n 1) ξ) '' S, ?_⟩
    rw [← image_interior_thinRegion hn Γ r S γ]
    exact ⟨u, hu, hsmul⟩
  exact subset_interior_thinRegion_of_isPreconnected hn Γ hΓ r hC ⟨p, hpC, hp⟩ hcover hzC

include hΓ in
theorem eq_of_quotient_eq_of_mem_interior_thinRegion
    (S : Set (BoundaryH n)) (b : HUpper n → ℝ)
    (hinv : ∀ γ : CuspCrossSections.endStabilizer hn Γ S, ∀ z : HUpper n,
      b ((poMulAction hn).smul (γ : PO n 1) z) = b z)
    {p q : HUpper n} (hp : p ∈ interior (thinRegion hn Γ r S))
    (hq : q ∈ interior (thinRegion hn Γ r S)) (heq : π p = π q) : b p = b q := by
  obtain ⟨γ, hγ⟩ := Quotient.exact heq
  have hsmul : (poMulAction hn).smul (γ : PO n 1) q = p := hγ
  have hmem : (γ : PO n 1) ∈ CuspCrossSections.endStabilizer hn Γ S := by
    by_contra hnot
    exact Set.disjoint_left.mp ((precisely_invariant_interior_thinRegion hn Γ hΓ r S γ).2 hnot)
      ⟨q, hq, hsmul⟩ hp
  exact (congrArg b hsmul).symm.trans (hinv ⟨γ, hmem⟩ q)

end DifferentialGeometry.OrbifoldThinRegions
