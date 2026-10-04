import DifferentialGeometry.Topology.PlanarJordan.InnermostDisk
import DifferentialGeometry.Topology.Surface.Recognition.DiskFaceRecognition
import DifferentialGeometry.Topology.Manifold.SpherePolarCoordinates
import DifferentialGeometry.Topology.Manifold.StereographicChart

/-! # Compact domains with a Jordan frontier -/

set_option autoImplicit false

open Set Metric Function

noncomputable section

namespace DifferentialGeometry.Topology.Surface

private theorem jordan_region_choice {D U : Set Schoenflies.Plane}
    (hD : IsClosed D) (hU : IsPreconnected U) (hfront : Disjoint U (frontier D)) :
    U ⊆ interior D ∨ U ⊆ Dᶜ := by
  apply hU.subset_or_subset isOpen_interior hD.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset)
  intro x hx
  by_cases hxd : x ∈ D
  · exact Or.inl (by
      by_contra hi
      exact disjoint_left.mp hfront hx ⟨hD.closure_eq.symm ▸ hxd, hi⟩)
  · exact Or.inr hxd

private theorem compact_eq_closure_inside {D C : Set Schoenflies.Plane}
    (hD : IsCompact D) (hint : (interior D).Nonempty)
    (hC : Schoenflies.IsSeparating C) (hfr : frontier D = C) :
    D = closure (Schoenflies.inside C) := by
  have hout : Schoenflies.outside C ⊆ Dᶜ := by
    rcases jordan_region_choice hD.isClosed hC.isConnected_outside.isPreconnected
        (hfr.symm ▸ disjoint_left.mpr fun x hx hc => Schoenflies.outside_subset_compl hx hc)
      with h | h
    · exact False.elim (hC.not_isBounded_outside
        (hD.isBounded.subset (h.trans interior_subset)))
    · exact h
  obtain ⟨x, hx⟩ := hint
  have hxC : x ∉ C := by
    rw [← hfr]
    exact fun h => h.2 hx
  have hxin : x ∈ Schoenflies.inside C := by
    have h := Schoenflies.inside_union_outside C
    have hm : x ∈ Schoenflies.inside C ∪ Schoenflies.outside C := h.symm ▸ hxC
    exact hm.resolve_right fun ho => hout ho (interior_subset hx)
  have hin : Schoenflies.inside C ⊆ interior D := by
    rcases jordan_region_choice hD.isClosed hC.isConnected_inside.isPreconnected
        (hfr.symm ▸ disjoint_left.mpr fun y hy hc => Schoenflies.inside_subset_compl hy hc)
      with h | h
    · exact h
    · exact False.elim (h hxin (interior_subset hx))
  have hi : interior D = Schoenflies.inside C := by
    apply Subset.antisymm _ hin
    intro y hy
    have hn : y ∉ C := by rw [← hfr]; exact fun h => h.2 hy
    have hm : y ∈ Schoenflies.inside C ∪ Schoenflies.outside C :=
      (Schoenflies.inside_union_outside C).symm ▸ hn
    exact hm.resolve_right fun ho => hout ho (interior_subset hy)
  rw [closure_eq_self_union_frontier, hC.frontier_inside,
    ← hi, ← hfr, ← closure_eq_interior_union_frontier, hD.isClosed.closure_eq]

theorem exists_disk_of_jordan_frontier_plane {D : Set Schoenflies.Plane}
    (hD : IsCompact D) (hint : (interior D).Nonempty)
    {c : Circle → Schoenflies.Plane} (hc : Continuous c) (hinj : Injective c)
    (hfr : frontier D = range c) :
    ∃ e : Disk 2 → Schoenflies.Plane, Topology.IsClosedEmbedding e ∧
      range e = D ∧ e '' diskSphere 2 = range c := by
  let r := Complex.orthonormalBasisOneI.repr
  let q : Circle ≃ₜ sphere (0 : Schoenflies.Plane) 1 :=
    r.toHomeomorph.subtype (fun z => by
      change z ∈ sphere (0 : ℂ) 1 ↔ r z ∈ sphere 0 1
      rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm, r.norm_map])
  let j := c ∘ q.symm
  have hj : Topology.IsEmbedding j :=
    (hc.comp q.symm.continuous).isClosedEmbedding (hinj.comp q.symm.injective) |>.isEmbedding
  have hr : range j = range c := by
    dsimp [j]
    rw [range_comp, q.symm.surjective.range_eq, image_univ]
  obtain ⟨F, hF, _, hclosed⟩ :=
    PlanarJordan.exists_homeomorph_extending_circle_embedding_image_ball hj
  have heq : F '' closedBall (0 : Schoenflies.Plane) 1 = D := by
    rw [hclosed]
    exact (compact_eq_closure_inside hD hint
      (Schoenflies.jordan_curve_theorem (PlanarJordan.isJordanCurve_range_of_isEmbedding_circle hj))
      (hfr.trans hr.symm)).symm
  let e : Disk 2 → Schoenflies.Plane := F ∘ Subtype.val
  refine ⟨e, (F.continuous.comp continuous_subtype_val).isClosedEmbedding
    (F.injective.comp Subtype.val_injective), ?_, ?_⟩
  · dsimp [e]
    rw [range_comp, Subtype.range_coe]
    exact heq
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hs : z.val ∈ sphere (0 : Schoenflies.Plane) 1 := hz
      exact hr ▸ ⟨⟨z.val, hs⟩, (hF ⟨z.val, hs⟩).symm⟩
    · intro hy
      obtain ⟨z, hz⟩ := mem_range.mp (hr.symm ▸ hy)
      refine ⟨⟨z.val, sphere_subset_closedBall z.property⟩, z.property, ?_⟩
      exact (hF z).trans hz

theorem exists_disk_of_jordan_frontier_openEmbedding
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (f : Y → Schoenflies.Plane) (hf : Topology.IsOpenEmbedding f)
    {D : Set Y} (hD : IsCompact D) (hint : (interior D).Nonempty)
    {c : Circle → Y} (hc : Continuous c) (hinj : Injective c)
    (hfr : frontier D = range c) :
    ∃ e : Disk 2 → Y, Topology.IsClosedEmbedding e ∧
      range e = D ∧ e '' diskSphere 2 = range c := by
  have hk : IsCompact (f '' D) := hD.image hf.continuous
  have hpre : f ⁻¹' (f '' D) = D := hf.injective.preimage_image D
  have hfront : frontier (f '' D) = f '' frontier D := by
    apply Subset.antisymm
    · intro x hx
      have hxD : x ∈ f '' D := hk.isClosed.closure_eq ▸ frontier_subset_closure hx
      obtain ⟨y, hy, rfl⟩ := hxD
      refine ⟨y, ?_, rfl⟩
      have hm : y ∈ f ⁻¹' frontier (f '' D) := hx
      rwa [hf.isOpenMap.preimage_frontier_eq_frontier_preimage hf.continuous, hpre] at hm
    · rintro x ⟨y, hy, rfl⟩
      change y ∈ f ⁻¹' frontier (f '' D)
      rwa [hf.isOpenMap.preimage_frontier_eq_frontier_preimage hf.continuous, hpre]
  have hint' : (interior (f '' D)).Nonempty := by
    obtain ⟨x, hx⟩ := hint
    refine ⟨f x, ?_⟩
    exact interior_maximal (image_mono interior_subset)
      (hf.isOpenMap _ isOpen_interior) (mem_image_of_mem f hx)
  have hcurve : frontier (f '' D) = range (f ∘ c) := by
    rw [hfront, hfr, range_comp]
  obtain ⟨e, he, her, heb⟩ := exists_disk_of_jordan_frontier_plane hk hint'
    (hf.continuous.comp hc) (hf.injective.comp hinj) hcurve
  have hpreim : ∀ z, ∃ y ∈ D, f y = e z := by
    intro z
    have hz : e z ∈ f '' D := her ▸ mem_range_self z
    exact hz
  choose a ha haf using hpreim
  have hcomp : f ∘ a = e := funext haf
  have hac : Continuous a := hf.isEmbedding.continuous_iff.mpr (hcomp ▸ he.continuous)
  have hai : Injective a := by
    intro x y h
    apply he.injective
    rw [← haf x, ← haf y, h]
  refine ⟨a, hac.isClosedEmbedding hai, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro x ⟨z, rfl⟩
      exact ha z
    · intro x hx
      obtain ⟨z, hz⟩ := mem_range.mp (her.symm ▸ mem_image_of_mem f hx)
      exact ⟨z, hf.injective ((haf z).trans hz)⟩
  · ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hm : f (a z) ∈ range (f ∘ c) := heb ▸ ⟨z, hz, (haf z).symm⟩
      obtain ⟨t, ht⟩ := hm
      exact ⟨t, hf.injective ht⟩
    · rintro ⟨t, rfl⟩
      obtain ⟨z, hz, hez⟩ := (heb.symm ▸ mem_range_self t)
      exact ⟨z, hz, hf.injective ((haf z).trans hez)⟩

theorem exists_disk_of_jordan_frontier_openChart
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (p : OpenPartialHomeomorph Y Schoenflies.Plane)
    {D : Set Y} (hD : IsCompact D) (hint : (interior D).Nonempty)
    {c : Circle → Y} (hc : Continuous c) (hinj : Injective c)
    (hfr : frontier D = range c) (hDs : D ⊆ p.source) :
    ∃ e : Disk 2 → Y, Topology.IsClosedEmbedding e ∧
      range e = D ∧ e '' diskSphere 2 = range c := by
  let U := p.source
  let D' : Set U := Subtype.val ⁻¹' D
  have hDc : IsCompact D' :=
    (Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage_iff
      (by simpa using hDs)).mpr hD
  let c' : Circle → U := fun t => ⟨c t, hDs (hD.isClosed.closure_eq ▸
    frontier_subset_closure (hfr.symm ▸ mem_range_self t))⟩
  have hi' : (interior D').Nonempty := by
    obtain ⟨x, hx⟩ := hint
    refine ⟨⟨x, hDs (interior_subset hx)⟩, ?_⟩
    have h := IsOpenMap.preimage_interior_eq_interior_preimage
      p.open_source.isOpenEmbedding_subtypeVal.isOpenMap continuous_subtype_val D
    exact h ▸ hx
  have hf' : frontier D' = range c' := by
    rw [← IsOpenMap.preimage_frontier_eq_frontier_preimage
      p.open_source.isOpenEmbedding_subtypeVal.isOpenMap continuous_subtype_val D, hfr]
    ext x
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, Subtype.ext ht⟩
    · rintro ⟨t, rfl⟩
      exact mem_range_self t
  obtain ⟨a, ha, har, hab⟩ := exists_disk_of_jordan_frontier_openEmbedding
    _ p.isOpenEmbedding_restrict hDc hi' (hc.subtype_mk _) (fun x y h =>
      hinj (congrArg Subtype.val h)) hf'
  let e := Subtype.val ∘ a
  refine ⟨e, (continuous_subtype_val.comp ha.continuous).isClosedEmbedding
    (Subtype.val_injective.comp ha.injective), ?_, ?_⟩
  · dsimp [e]
    rw [range_comp, har, image_preimage_eq_of_subset (by simpa using hDs)]
  · dsimp [e]
    rw [image_comp, hab, ← range_comp]
    rfl

private instance sphereThreeFinrank :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

theorem exists_disk_of_jordan_frontier_sphereTwo {D : Set SphereTwo}
    (hD : IsCompact D) (hint : (interior D).Nonempty)
    {c : Circle → SphereTwo} (hc : Continuous c) (hinj : Injective c)
    (hfr : frontier D = range c) :
    ∃ e : Disk 2 → SphereTwo, Topology.IsClosedEmbedding e ∧
      range e = D ∧ e '' diskSphere 2 = range c := by
  have hne : D ≠ univ := by
    intro h
    have hm : c 1 ∈ frontier D := hfr.symm ▸ mem_range_self 1
    simp [h] at hm
  obtain ⟨x, hx⟩ := not_forall.mp (fun h => hne (eq_univ_of_forall h))
  apply exists_disk_of_jordan_frontier_openChart (stereographic' 2 x) hD hint hc hinj hfr
  intro y hy
  rw [stereographic'_source]
  exact fun h => hx (h ▸ hy)

private def circlePlaneSphere : Circle ≃ₜ sphere (0 : Schoenflies.Plane) 1 :=
  Complex.orthonormalBasisOneI.repr.toHomeomorph.subtype (fun z => by
    change z ∈ sphere (0 : ℂ) 1 ↔ Complex.orthonormalBasisOneI.repr z ∈ sphere 0 1
    rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm,
      Complex.orthonormalBasisOneI.repr.norm_map])

private def cylinderPolarSource : Circle × ℝ ≃ₜ
    {p : sphere (0 : Schoenflies.Plane) 1 × ℝ | 0 < p.2} where
  toFun p := ⟨(circlePlaneSphere p.1, Real.exp p.2), Real.exp_pos _⟩
  invFun p := (circlePlaneSphere.symm p.val.1, Real.expOrderIso.symm ⟨p.val.2, p.property⟩)
  left_inv p := by
    apply Prod.ext
    · exact circlePlaneSphere.symm_apply_apply p.1
    · exact Real.expOrderIso.symm_apply_apply p.2
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact circlePlaneSphere.apply_symm_apply p.val.1
    · exact congrArg Subtype.val (Real.expOrderIso.apply_symm_apply ⟨p.val.2, p.property⟩)
  continuous_toFun :=
    ((circlePlaneSphere.continuous.comp continuous_fst).prodMk
      (Real.continuous_exp.comp continuous_snd)).subtype_mk _
  continuous_invFun :=
    (circlePlaneSphere.symm.continuous.comp continuous_subtype_val.fst).prodMk
      (Real.expOrderIso.symm.continuous.comp (continuous_subtype_val.snd.subtype_mk _))

def cylinderPlaneEmbedding (p : Circle × ℝ) : Schoenflies.Plane :=
  Real.exp p.2 • (circlePlaneSphere p.1 : Schoenflies.Plane)

private instance planeFinrank : Fact (Module.finrank ℝ Schoenflies.Plane = 1 + 1) :=
  ⟨by simp⟩

theorem cylinderPlaneEmbedding_isOpenEmbedding :
    Topology.IsOpenEmbedding cylinderPlaneEmbedding := by
  exact (OpenPartialHomeomorph.isOpenEmbedding_restrict
    (Manifold.spherePolarChart (n := 1) (circlePlaneSphere 1)).toOpenPartialHomeomorph).comp
      cylinderPolarSource.isOpenEmbedding

theorem exists_disk_of_jordan_frontier_cylinder {D : Set (Circle × ℝ)}
    (hD : IsCompact D) (hint : (interior D).Nonempty)
    {c : Circle → Circle × ℝ} (hc : Continuous c) (hinj : Injective c)
    (hfr : frontier D = range c) :
    ∃ e : Disk 2 → Circle × ℝ, Topology.IsClosedEmbedding e ∧
      range e = D ∧ e '' diskSphere 2 = range c :=
  exists_disk_of_jordan_frontier_openEmbedding cylinderPlaneEmbedding
    cylinderPlaneEmbedding_isOpenEmbedding hD hint hc hinj hfr

end DifferentialGeometry.Topology.Surface
