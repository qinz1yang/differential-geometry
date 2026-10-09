import DifferentialGeometry.Topology.ThreeManifold.SphereInsideBall
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Boundary
import DifferentialGeometry.Topology.SphereSeparation.SideClosureDisjoint
import DifferentialGeometry.Topology.OpenPartialHomeomorph.CapFilling
import DifferentialGeometry.Topology.Manifold.SpherePolarCoordinates

noncomputable section
open Set Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.ThreeManifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]

private theorem outside_inner_ball_of_incident_outer_sphere
    (C B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (hC : closedBall (0 : E3) 1 ⊆ C.source)
    (hB : closedBall (0 : E3) 1 ⊆ B.source)
    (hnested : B '' closedBall (0 : E3) 1 ⊆ C '' ball (0 : E3) 1)
    {W : Set M} (hregular : closure (interior W) = W)
    (hconn : IsPreconnected (interior W))
    (hinner : B '' sphere (0 : E3) 1 ⊆ frontier W)
    (houter : (C '' sphere (0 : E3) 1 ∩ W).Nonempty) :
    Disjoint (B '' ball (0 : E3) 1) W := by
  have hBc : IsClosed (B '' closedBall (0 : E3) 1) :=
    ((isCompact_closedBall _ _).image_of_continuousOn (B.contMDiffOn_toFun.continuousOn.mono hB)).isClosed
  have hBi : interior (B '' closedBall (0 : E3) 1) = B '' ball (0 : E3) 1 := by
    have h := B.toOpenPartialHomeomorph.image_interior_of_subset_source hB
    rw [interior_closedBall _ one_ne_zero] at h
    exact h.symm
  have hBf : frontier (B '' closedBall (0 : E3) 1) = B '' sphere (0 : E3) 1 := by
    rw [← B.image_frontier_of_isCompact (isCompact_closedBall _ _) hB, frontier_closedBall _ one_ne_zero]
  have hav : interior W ⊆ (frontier (B '' closedBall (0 : E3) 1))ᶜ := by
    intro x hx hxf
    exact (hinner (hBf ▸ hxf)).2 hx
  have hsplit : (frontier (B '' closedBall (0 : E3) 1))ᶜ =
      interior (B '' closedBall (0 : E3) 1) ∪ (B '' closedBall (0 : E3) 1)ᶜ := by
    rw [compl_frontier_eq_union_interior, hBc.isOpen_compl.interior_eq]
  rcases hconn.subset_or_subset isOpen_interior hBc.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset) (hav.trans hsplit.subset) with hin | hout
  · have hWB : W ⊆ B '' closedBall (0 : E3) 1 := by
      rw [← hregular]
      exact closure_minimal (hin.trans interior_subset) hBc
    obtain ⟨z, ⟨q, hq, hqz⟩, hzW⟩ := houter
    obtain ⟨v, hv, hvz⟩ := hnested (hWB hzW)
    have he : v = q := C.toPartialEquiv.injOn (hC (ball_subset_closedBall hv))
      (hC (sphere_subset_closedBall hq)) (hvz.trans hqz.symm)
    exact ((mem_ball_zero_iff.mp (he ▸ hv)).ne (mem_sphere_zero_iff_norm.mp hq)).elim
  · have hWout : W ⊆ (B '' ball (0 : E3) 1)ᶜ := by
      rw [← hregular]
      have h := closure_mono hout
      rw [closure_compl, hBi] at h
      exact h
    exact disjoint_right.mpr (fun x hxW hxB => hWout hxW hxB)

theorem exists_pairwise_disjoint_ball_holes_of_spherical_frontier
    {ι : Type*} (C : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (hC : closedBall (0 : E3) 1 ⊆ C.source)
    {W : Set M} (hregular : closure (interior W) = W)
    (hconn : IsPreconnected (interior W))
    (e : ι → S2 → M) (he : ∀ i, IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (e i))
    (hinside : ∀ i, range (e i) ⊆ C '' ball (0 : E3) 1)
    (hfront : ∀ i, range (e i) ⊆ frontier W)
    (houter : (C '' sphere (0 : E3) 1 ∩ W).Nonempty)
    (hdis : Pairwise (fun i j => Disjoint (range (e i)) (range (e j)))) :
    ∃ B : ι → PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞,
      (∀ i, closedBall (0 : E3) 1 ⊆ (B i).source) ∧
      (∀ i, B i '' sphere (0 : E3) 1 = range (e i)) ∧
      (∀ i, B i '' closedBall (0 : E3) 1 ⊆ C '' ball (0 : E3) 1) ∧
      (∀ i, Disjoint (B i '' ball (0 : E3) 1) W) ∧
      Pairwise (fun i j => Disjoint (B i '' closedBall (0 : E3) 1)
        (B j '' closedBall (0 : E3) 1)) := by
  classical
  choose B hB hBs hBC using fun i =>
    exists_ball_chart_inside_ball_of_sphere_embedding C hC (e i) (he i) (hinside i)
  have hBW (i : ι) : Disjoint (B i '' ball (0 : E3) 1) W :=
    outside_inner_ball_of_incident_outer_sphere C (B i) hC (hB i) (hBC i)
      hregular hconn (hBs i ▸ hfront i) houter
  have hcl (i : ι) : closure (B i '' ball (0 : E3) 1) = B i '' closedBall (0 : E3) 1 :=
    DifferentialGeometry.Topology.Manifold.closure_image_ball_of_partialDiffeomorph (B i) (hB i)
  have hpair := DifferentialGeometry.Topology.SphereSeparation.pairwise_disjoint_closure_of_isOpen_side
    (C := W) (sphere := fun i => range (e i)) (side := fun i => B i '' ball (0 : E3) 1)
    (fun i => (B i).toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_ball
      (ball_subset_closedBall.trans (hB i)))
    (fun i => ((convex_ball (0 : E3) 1).isConnected ⟨0, by simp⟩).image (B i)
      ((B i).contMDiffOn_toFun.continuousOn.mono (ball_subset_closedBall.trans (hB i))))
    (fun i => (hfront i).trans ((hregular ▸ isClosed_closure).frontier_subset)) hBW
    (by
      intro i
      rw [hcl i, ← hBs i, ← image_union, ball_union_sphere])
    hdis (fun i => range_nonempty (e i))
  exact ⟨B, hB, hBs, hBC, hBW, fun i j hij => by simpa only [hcl] using hpair hij⟩

private theorem frontier_union_finite_family_subset
    {X ι : Type*} [TopologicalSpace X] (W : Set X) (B : ι → Set X) (s : Finset ι) :
    frontier (W ∪ ⋃ i ∈ s, B i) ⊆ frontier W ∪ ⋃ i ∈ s, frontier (B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have heq : W ∪ ⋃ j ∈ insert i s, B j = (W ∪ ⋃ j ∈ s, B j) ∪ B i := by
      ext x
      simp only [Finset.mem_insert, mem_union, mem_iUnion]
      aesop
    rw [heq]
    intro x hx
    rcases frontier_union_subset _ _ hx with h | h
    · rcases ih h.1 with hxW | hxB
      · exact Or.inl hxW
      · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxB
        exact Or.inr (mem_iUnion₂.mpr ⟨j, Finset.mem_insert_of_mem hj, hxj⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨i, Finset.mem_insert_self _ _, h.2⟩)

private theorem sphere_subset_interior_union_of_ball_boundary
    (B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (hB : closedBall (0 : E3) 1 ⊆ B.source)
    {W R : Set M} (hregular : closure (interior W) = W) (hR : IsClosed R)
    (hfront : frontier W = B '' sphere (0 : E3) 1 ∪ R)
    (hdis : Disjoint (B '' sphere (0 : E3) 1) R)
    (havoid : Disjoint (B '' ball (0 : E3) 1) W) :
    B '' sphere (0 : E3) 1 ⊆ interior (W ∪ B '' closedBall (0 : E3) 1) := by
  let v : S2 := ⟨EuclideanSpace.single 0 1, by simp⟩
  let _ : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  let shift : (S2 × ℝ) ≃ₜ (S2 × ℝ) :=
    { toFun := fun q => (q.1, 1 + q.2)
      invFun := fun q => (q.1, q.2 - 1)
      left_inv := by intro q; ext <;> simp
      right_inv := by intro q; ext <;> simp
      continuous_toFun := continuous_fst.prodMk (continuous_const.add continuous_snd)
      continuous_invFun := continuous_fst.prodMk (continuous_snd.sub continuous_const) }
  let T := shift.transOpenPartialHomeomorph
    ((DifferentialGeometry.Topology.Manifold.spherePolarChart (n := 2) v).trans B).toOpenPartialHomeomorph
  have hzero (q : S2) : T (q, 0) = B q.val := by
    change B ((1 + (0 : ℝ)) • q.val) = B q.val
    simp
  have hsrc (q : S2) : (q, 0) ∈ T.source := by
    change (q, 1 + (0 : ℝ)) ∈ ((DifferentialGeometry.Topology.Manifold.spherePolarChart (n := 2) v).trans B).source
    refine ⟨by norm_num [DifferentialGeometry.Topology.Manifold.spherePolarChart], ?_⟩
    change (1 + (0 : ℝ)) • q.val ∈ B.source
    simpa using hB (sphere_subset_closedBall q.property)
  have hrange : range (fun q : S2 => T (q, 0)) = B '' sphere (0 : E3) 1 := by
    simp only [hzero]
    change range ((B : E3 → M) ∘ (Subtype.val : S2 → E3)) = _
    rw [range_comp, Subtype.range_val]
  have hinterior : interior (B '' closedBall (0 : E3) 1) = B '' ball (0 : E3) 1 := by
    have h := B.toOpenPartialHomeomorph.image_interior_of_subset_source hB
    rw [interior_closedBall _ one_ne_zero] at h
    exact h.symm
  have hregB : closure (interior (B '' closedBall (0 : E3) 1)) = B '' closedBall (0 : E3) 1 := by
    rw [hinterior]
    exact DifferentialGeometry.Topology.Manifold.closure_image_ball_of_partialDiffeomorph B hB
  have hfrontB : frontier (B '' closedBall (0 : E3) 1) = B '' sphere (0 : E3) 1 := by
    rw [← B.image_frontier_of_isCompact (isCompact_closedBall _ _) hB, frontier_closedBall _ one_ne_zero]
  let _ : ConnectedSpace S2 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [E3])) (0 : E3) zero_le_one)
  have h := DifferentialGeometry.Topology.fill_of_shared_cylinder_boundary_of_disjoint_interiors
    T hsrc hregular hregB (by rw [hinterior]; exact havoid.symm.mono_left interior_subset)
    hR (by rw [hrange]; exact hfront) (hfrontB.trans hrange.symm) (hrange.symm ▸ hdis)
  exact hrange ▸ h.2.2.2

theorem exists_finite_disjoint_ball_holes_of_spherical_frontier
    {ι : Type*} [Finite ι]
    (C : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (hC : closedBall (0 : E3) 1 ⊆ C.source)
    {W : Set M} (hregular : closure (interior W) = W)
    (hconn : IsPreconnected (interior W)) (hW : W ⊆ C '' closedBall (0 : E3) 1)
    (e : ι → S2 → M) (he : ∀ i, IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (e i))
    (hinside : ∀ i, range (e i) ⊆ C '' ball (0 : E3) 1)
    (hfront : frontier W = C '' sphere (0 : E3) 1 ∪ ⋃ i, range (e i))
    (hdis : Pairwise (fun i j => Disjoint (range (e i)) (range (e j)))) :
    ∃ B : ι → PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞,
      (∀ i, closedBall (0 : E3) 1 ⊆ (B i).source) ∧
      (∀ i, B i '' sphere (0 : E3) 1 = range (e i)) ∧
      (∀ i, B i '' closedBall (0 : E3) 1 ⊆ C '' ball (0 : E3) 1) ∧
      Pairwise (fun i j => Disjoint (B i '' closedBall (0 : E3) 1)
        (B j '' closedBall (0 : E3) 1)) ∧
      W = C '' closedBall (0 : E3) 1 \ ⋃ i, B i '' ball (0 : E3) 1 := by
  classical
  let _ := Fintype.ofFinite ι
  have hWclosed : IsClosed W := hregular ▸ isClosed_closure
  have houterW : C '' sphere (0 : E3) 1 ⊆ W :=
    fun x hx => hWclosed.frontier_subset (hfront.symm ▸ Or.inl hx)
  let v : S2 := ⟨EuclideanSpace.single 0 1, by simp⟩
  have houter : (C '' sphere (0 : E3) 1 ∩ W).Nonempty :=
    ⟨C v.val, ⟨v.val, v.property, rfl⟩, houterW ⟨v.val, v.property, rfl⟩⟩
  obtain ⟨B, hB, hBs, hBC, hBW, hpair⟩ :=
    exists_pairwise_disjoint_ball_holes_of_spherical_frontier C hC hregular hconn e he hinside
      (fun i x hx => hfront.symm ▸ Or.inr (mem_iUnion.mpr ⟨i, hx⟩)) houter hdis
  let V := W ∪ ⋃ i, B i '' closedBall (0 : E3) 1
  have hBclosed (i : ι) : IsClosed (B i '' closedBall (0 : E3) 1) :=
    ((isCompact_closedBall _ _).image_of_continuousOn
      ((B i).contMDiffOn_toFun.continuousOn.mono (hB i))).isClosed
  have hBfront (i : ι) : frontier (B i '' closedBall (0 : E3) 1) = range (e i) := by
    rw [← (B i).image_frontier_of_isCompact (isCompact_closedBall _ _) (hB i),
      frontier_closedBall _ one_ne_zero, hBs i]
  have hCi : interior (C '' closedBall (0 : E3) 1) = C '' ball (0 : E3) 1 := by
    have h := C.toOpenPartialHomeomorph.image_interior_of_subset_source hC
    rw [interior_closedBall _ one_ne_zero] at h
    exact h.symm
  have hCsdis (i : ι) : Disjoint (range (e i)) (C '' sphere (0 : E3) 1) := by
    rw [disjoint_left]
    rintro x hxe ⟨q, hq, hqx⟩
    obtain ⟨z, hz, hzx⟩ := hinside i hxe
    have heq := C.toPartialEquiv.injOn (hC (ball_subset_closedBall hz))
      (hC (sphere_subset_closedBall hq)) (hzx.trans hqx.symm)
    exact (mem_ball_zero_iff.mp (heq ▸ hz)).ne (mem_sphere_zero_iff_norm.mp hq)
  have hfill (i : ι) : range (e i) ⊆ interior V := by
    let R := C '' sphere (0 : E3) 1 ∪ ⋃ j : {j // j ≠ i}, range (e j.val)
    have hRc : IsClosed R :=
      ((isCompact_sphere (0 : E3) 1).image_of_continuousOn
        (C.contMDiffOn_toFun.continuousOn.mono (sphere_subset_closedBall.trans hC))).isClosed.union
        (isClosed_iUnion_of_finite (fun j => (isCompact_range (he j.val).contMDiff.continuous).isClosed))
    have hfr : frontier W = (B i '' sphere (0 : E3) 1) ∪ R := by
      rw [hfront, hBs i]
      apply subset_antisymm
      · rintro x (hxC | hxE)
        · exact Or.inr (Or.inl hxC)
        · obtain ⟨j, hxj⟩ := mem_iUnion.mp hxE
          by_cases hji : j = i
          · subst j; exact Or.inl hxj
          · exact Or.inr (Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hxj⟩))
      · rintro x (hxi | hxC | hxE)
        · exact Or.inr (mem_iUnion.mpr ⟨i, hxi⟩)
        · exact Or.inl hxC
        · obtain ⟨j, hxj⟩ := mem_iUnion.mp hxE
          exact Or.inr (mem_iUnion.mpr ⟨j.val, hxj⟩)
    have hd : Disjoint (B i '' sphere (0 : E3) 1) R := by
      rw [hBs i]
      exact (hCsdis i).union_right (disjoint_iUnion_right.mpr
        (fun j => hdis j.property.symm))
    have hs := sphere_subset_interior_union_of_ball_boundary (B i) (hB i)
      hregular hRc hfr hd (hBW i)
    rw [hBs i] at hs
    apply hs.trans (interior_mono ?_)
    rintro z (hzW | hzB)
    · exact Or.inl hzW
    · exact Or.inr (mem_iUnion.mpr ⟨i, hzB⟩)
  have hVfront : frontier V ⊆ C '' sphere (0 : E3) 1 := by
    have hh := frontier_union_finite_family_subset W (fun i => B i '' closedBall (0 : E3) 1)
      (Finset.univ : Finset ι)
    simp only [Finset.mem_univ, iUnion_true] at hh
    intro x hx
    rcases hh hx with hxW | hxB
    · rcases hfront ▸ hxW with hxC | hxE
      · exact hxC
      · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxE
        exact (hx.2 (hfill i hxi)).elim
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxB
      exact (hx.2 (hfill i (hBfront i ▸ hxi))).elim
  have hVclosed : IsClosed V := hWclosed.union (isClosed_iUnion_of_finite hBclosed)
  have hVsub : V ⊆ C '' closedBall (0 : E3) 1 :=
    union_subset hW (iUnion_subset (fun i => (hBC i).trans (image_mono ball_subset_closedBall)))
  have hWne : W.Nonempty := ⟨houter.choose, houter.choose_spec.2⟩
  obtain ⟨x, hx⟩ := closure_nonempty_iff.mp (hregular.symm ▸ hWne)
  have hxC : x ∈ C '' ball (0 : E3) 1 := hCi ▸ interior_mono hW hx
  have hCpre : IsPreconnected (C '' ball (0 : E3) 1) :=
    (convex_ball (0 : E3) 1).isPreconnected.image C
      (C.contMDiffOn_toFun.continuousOn.mono (ball_subset_closedBall.trans hC))
  have hCavoid : Disjoint (C '' ball (0 : E3) 1) (frontier V) := by
    rw [disjoint_left]
    rintro z ⟨w, hw, hwz⟩ hzV
    obtain ⟨q, hq, hqz⟩ := hVfront hzV
    have heq := C.toPartialEquiv.injOn (hC (ball_subset_closedBall hw))
      (hC (sphere_subset_closedBall hq)) (hwz.trans hqz.symm)
    exact (mem_ball_zero_iff.mp (heq ▸ hw)).ne (mem_sphere_zero_iff_norm.mp hq)
  have hCinto : C '' ball (0 : E3) 1 ⊆ interior V :=
    DifferentialGeometry.Topology.subset_interior_of_isPreconnected_of_disjoint_frontier
      hCpre hCavoid ⟨x, hxC, interior_mono subset_union_left hx⟩
  have hCsubV : C '' closedBall (0 : E3) 1 ⊆ V := by
    rw [← DifferentialGeometry.Topology.Manifold.closure_image_ball_of_partialDiffeomorph C hC]
    exact closure_minimal (hCinto.trans interior_subset) hVclosed
  refine ⟨B, hB, hBs, hBC, hpair, ?_⟩
  apply subset_antisymm
  · intro z hzW
    exact ⟨hW hzW, fun hz => by
      obtain ⟨i, hzi⟩ := mem_iUnion.mp hz
      exact disjoint_left.mp (hBW i) hzi hzW⟩
  · rintro z ⟨hzC, hzholes⟩
    rcases hCsubV hzC with hzW | hzB
    · exact hzW
    · obtain ⟨i, w, hw, hwz⟩ := mem_iUnion.mp hzB
      have hwn : w ∉ ball (0 : E3) 1 := fun hwball =>
        hzholes (mem_iUnion.mpr ⟨i, w, hwball, hwz⟩)
      have hws : w ∈ sphere (0 : E3) 1 := by
        rw [mem_sphere_zero_iff_norm]
        exact le_antisymm (mem_closedBall_zero_iff.mp hw)
          (not_lt.mp (fun h => hwn (mem_ball_zero_iff.mpr h)))
      exact hWclosed.frontier_subset (hfront.symm ▸ Or.inr
        (mem_iUnion.mpr ⟨i, (hBs i) ▸ ⟨w, hws, hwz⟩⟩))

end DifferentialGeometry.Topology.ThreeManifold
