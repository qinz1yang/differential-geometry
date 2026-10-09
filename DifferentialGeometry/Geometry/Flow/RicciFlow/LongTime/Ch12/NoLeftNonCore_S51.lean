import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.RealCutDecomposition_S31
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBoundaryBoundary_S39

/-!
# CH12-S51 G1: a non-core block of the real cut owns no left torus

For the real cut `sliceDec_S28 D ht C` of the component `C`, a block `j` that is not the core block
of any core `c` with `coreComp c = C` owns no left torus `σ_i(·, -1/2)`: otherwise the block, being an
open piece of the cut carrier, contains a point `σ_i(t', -ψ y)` (`0 < y < 1`) of the left half
collar, whose `rmapK` image `σ_i(t', -y)` lies in the core interior image
(`stageCollar_neg_mem_core_S19` + `corePhi_boundary_zeroSet_S28` + collar injectivity), contradicting
`blockCore_complement_S31`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold TopologicalSpace DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime GC.Topology
open scoped Manifold ContDiff

universe u

namespace GC.LongTime.Ch12

section Generic

variable {M : ConnectedClosedOrientedManifold.{u} 3} (F : CollaredTorusFamily_C2a M.Carrier)

theorem mem_signedSource_S51 {s : ℝ} (p : Torus) (h1 : -1 < s) (h2 : s < 1) :
    (p, s) ∈ signedCollarSource := by
  simp only [signedCollarSource, Set.mem_ofPred_eq]; exact ⟨h1, h2⟩

/-- Two collars of the family agree on `(p, 0)` and `(t', s)` only if same torus and `s = 0`. -/
theorem collar_eq_zero_S51 {k i : Fin F.count} {p t' : Torus} {s : ℝ} (h1 : -1 < s) (h2 : s < 1)
    (h : F.collar k (p, 0) = F.collar i (t', s)) : k = i ∧ s = 0 := by
  have hs0 : (p, (0 : ℝ)) ∈ (F.collar k).source := by
    rw [F.source_eq]; exact mem_signedSource_S51 p (by norm_num) (by norm_num)
  have hs1 : (t', s) ∈ (F.collar i).source := by
    rw [F.source_eq]; exact mem_signedSource_S51 t' h1 h2
  by_cases hki : k = i
  · subst hki
    have := (F.collar k).toPartialEquiv.injOn hs0 hs1 h
    exact ⟨rfl, (congrArg Prod.snd this).symm⟩
  · exact absurd h (fun h' => Set.disjoint_left.mp (F.disjoint hki) ((F.collar k).map_source hs0)
      (h' ▸ (F.collar i).map_source hs1))

/-- A point of the left half collar of `σ_i`, near a left-torus point lying in an open `U`. -/
theorem exists_left_interior_pt_S51 (i : Fin F.count) (t : Torus)
    {U : Set (cutCarrier_C2a F).Carrier} (hU : IsOpen U)
    (hx : sideTorus_C2a F i hL_C2a t ∈ U) :
    ∃ y : ℝ, 0 < y ∧ y < 1 ∧ ∃ z ∈ U, z ∈ (cutCarrier_C2a F).interior ∧
      rmapK_S12 F z = F.collar i (t, -y) := by
  have hcoord : ∀ y : ℝ, 0 ≤ y → (halfSpaceOneLift y).val 0 = y := fun y hy => GC.LongTime.CuspP1.lift_height_CPA2 hy
  have hcont : ContinuousOn
      (fun y : ℝ => sideCollar_S12 F i hL_C2a (t, halfSpaceOneLift y)) (Iio 1) := by
    refine (sideCollar_S12 F i hL_C2a).contMDiffOn.continuousOn.comp
      (Continuous.continuousOn (continuous_const.prodMk GC.LongTime.CuspP1.continuous_halfSpaceOneLift_CPA2)) ?_
    intro y hy
    change max y 0 < 1
    exact max_lt hy one_pos
  have hzero : halfSpaceOneLift 0 = halfZero := halfSpaceOneLift_coord_S34 halfZero
  have hg0 : sideCollar_S12 F i hL_C2a (t, halfSpaceOneLift 0) ∈ U := by
    rw [hzero, sideCollar_zero_S12]; exact hx
  have hca : ContinuousAt (fun y : ℝ => sideCollar_S12 F i hL_C2a (t, halfSpaceOneLift y)) 0 :=
    hcont.continuousAt (Iio_mem_nhds one_pos)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hca.preimage_mem_nhds (hU.mem_nhds hg0))
  set y : ℝ := min (ε / 2) (1 / 2) with hy
  have hy0 : 0 < y := lt_min (half_pos hε) (by norm_num)
  have hy1 : y < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hyb : y ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hy0]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hsrc : ((t, halfSpaceOneLift y) : Torus × EuclideanHalfSpace 1) ∈ halfCollarSource := by
    change (halfSpaceOneLift y).val 0 < 1
    rw [hcoord y hy0.le]; exact hy1
  have hval := sideCollar_val_S12 F i hL_C2a hsrc
  have hpsi : 1 / 2 < psi_S12 y := by
    have := strictMono_psi_S12 hy0
    rwa [psi_zero_S12] at this
  have hpsi1 : psi_S12 y < 1 := psi_lt_one_S12 hy1
  refine ⟨y, hy0, hy1, _, hball hyb, ?_, ?_⟩
  · rw [mem_interior_iff_S12]
    intro k
    have hz : (sideCollar_S12 F i hL_C2a (t, halfSpaceOneLift y)).1 =
        F.collar i (t, -1 * psi_S12 y) := by
      rw [hval]; simp only [hcoord y hy0.le]
    have hne : ∀ (s : ℝ) (t'' : Torus), |s| = 1 / 2 → F.collar k (t'', s) ≠ F.collar i (t, -1 * psi_S12 y) := by
      intro s t'' hs heq
      have hs1 : (t'', s) ∈ (F.collar k).source := by
        rw [F.source_eq]
        have := abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2) |>.mp hs
        exact mem_signedSource_S51 t'' (by rcases this with h | h <;> rw [h] <;> norm_num)
          (by rcases this with h | h <;> rw [h] <;> norm_num)
      have hs2 : (t, -1 * psi_S12 y) ∈ (F.collar i).source := by
        rw [F.source_eq]
        exact mem_signedSource_S51 t (by linarith) (by linarith)
      by_cases hki : k = i
      · subst hki
        have this := (F.collar k).toPartialEquiv.injOn hs1 hs2 heq
        have h2 := congrArg Prod.snd this
        simp only at h2
        have := abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2) |>.mp hs
        rcases this with h | h <;> rw [h] at h2 <;> linarith
      · exact Set.disjoint_left.mp (F.disjoint hki) ((F.collar k).map_source hs1)
          (heq ▸ (F.collar i).map_source hs2)
    rw [hz]
    exact ⟨fun t'' h => hne (1 / 2) t'' (by norm_num) h.symm,
      fun t'' h => hne (-1 / 2) t'' (by norm_num) h.symm⟩
  · rw [rmapK_leftCollar_S12 F i hsrc]
    simp only [hcoord y hy0.le]

end Generic

section Slice

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K} {t : ℝ}
  (D : TruncatedCutData_IF4 cores t) (ht : cores.start ≤ t)
  (hdom : ∀ i, range (D.truncation i).inclusion ⊆ (cores.domain i t : Set (cores.model i).Carrier))

omit hdom in
/-- A core boundary point of a core in `C` lies in the seam set of `C`'s family. -/
theorem corePhi_mem_zeroSet_S51
    (C : ConnectedComponents (postStage F.observation t).toClosedOrientedManifold.Carrier)
    (hdom : ∀ i, range (D.truncation i).inclusion ⊆ (cores.domain i t : Set (cores.model i).Carrier))
    (c : Fin cores.count) (hc : coreComp_S28 D ht c = C)
    {y : (D.truncation c).core.Carrier}
    (hy : y ∈ (D.truncation c).core.model.boundary (D.truncation c).core.Carrier)
    (z : (sliceM_S28 C).Carrier) (hz : z.1 = corePhi_S28 D ht c y) :
    z ∈ zeroSet_S12 (componentFamily_S19 D ht C) := by
  subst hc
  have h := corePhi_boundary_zeroSet_S28 D ht hdom c hy
  have hzz : z = corePhiComp_S28 D ht hdom c y := Subtype.ext hz
  rw [hzz]; exact h

include hdom in
/-- **G1b.** A block `j` of the real cut of `C` which is not the core block of any core `c` with
`coreComp c = C` owns no left torus. -/
theorem noleft_of_noncore_S51
    (C : ConnectedComponents (postStage F.observation t).toClosedOrientedManifold.Carrier)
    (j : Fin (sliceDec_S28 D ht C).components.count)
    (hj : ∀ c : Fin cores.count, coreComp_S28 D ht c = C →
      blockImage_S28 D ht C j ≠ corePhi_S28 D ht c '' ((D.truncation c).core.interior : Set _)) :
    ∀ x : ((sliceDec_S28 D ht C).component j).Carrier,
      ∀ (i : Fin (componentFamily_S19 D ht C).count) (t' : Torus),
        x.val.1 ≠ (componentFamily_S19 D ht C).collar i (t', -1 / 2) := by
  intro x i t' hx
  have hxs : x.val = sideTorus_C2a (componentFamily_S19 D ht C) i hL_C2a t' :=
    Subtype.ext (hx.trans (sideTorus_val_left_S12 _ i t').symm)
  have hxU : sideTorus_C2a (componentFamily_S19 D ht C) i hL_C2a t' ∈
      (sliceDec_S28 D ht C).components.piece j := hxs ▸ x.2
  obtain ⟨y, hy0, hy1, z, hzU, hzint, hzr⟩ := exists_left_interior_pt_S51
    (componentFamily_S19 D ht C) i t' ((sliceDec_S28 D ht C).components.piece j).isOpen hxU
  have hzB : (rmapK_S12 (componentFamily_S19 D ht C) z).1 ∈ blockImage_S28 D ht C j :=
    ⟨z, ⟨hzU, hzint⟩, rfl⟩
  set idx := (cidxEquiv_S19 D ht C).symm i with hidx
  have hsrc : (t', -y) ∈ (stageCollar_S19 D ht idx.1).source := by
    rw [stageCollar_source_S19]; exact mem_signedSource_S51 t' (by linarith) (by linarith)
  have hcol : (((componentFamily_S19 D ht C).collar i (t', -y)).val :
      (postStage F.observation t).Carrier) = stageCollar_S19 D ht idx.1 (t', -y) :=
    restrictCollar_apply_S19 _ _ _ (cidx_target_subset_S19 D ht _) (t', -y) hsrc
  obtain ⟨_, ⟨w, rfl⟩, hw⟩ := stageCollar_neg_mem_core_S19 D ht idx.1 t' (-y) (by linarith)
    (by linarith)
  have hc : coreComp_S28 D ht idx.1.1 = C := by
    have hmem := stageCollar_target_subset_comp_S19 D ht idx.1
      ((stageCollar_S19 D ht idx.1).map_source hsrc)
    rw [← hw] at hmem
    exact (corePhi_comp_S28 D ht hdom idx.1.1 w).symm.trans (hmem.trans idx.2)
  have hwcore : corePhi_S28 D ht idx.1.1 w =
      (((componentFamily_S19 D ht C).collar i (t', -y)).val : (postStage F.observation t).Carrier) :=
    hw.trans hcol.symm
  have hwint : w ∈ ((D.truncation idx.1.1).core.interior : Set _) := by
    by_contra hwi
    have hbd : w ∈ (D.truncation idx.1.1).core.model.boundary (D.truncation idx.1.1).core.Carrier := by
      rw [← ModelWithCorners.compl_interior]; exact hwi
    have hzs := corePhi_mem_zeroSet_S51 D ht C hdom idx.1.1 hc hbd
      ((componentFamily_S19 D ht C).collar i (t', -y)) hwcore.symm
    obtain ⟨k, ⟨⟨p, s⟩, ⟨-, hs⟩, hq⟩⟩ := mem_iUnion.mp hzs
    have hs0 : s = 0 := hs
    subst hs0
    obtain ⟨-, h0⟩ := collar_eq_zero_S51 (componentFamily_S19 D ht C) (by linarith) (by linarith)
      (congrArg Subtype.val hq |> fun h => Subtype.ext h)
    linarith
  have hdisj := blockCore_complement_S31 D ht hdom C j hj idx.1.1 hc
  refine Set.disjoint_left.mp hdisj hzB ⟨w, hwint, ?_⟩
  rw [hzr]; exact hwcore

end Slice

end GC.LongTime.Ch12
