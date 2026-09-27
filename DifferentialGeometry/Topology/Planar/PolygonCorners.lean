import DifferentialGeometry.Topology.Planar.PolygonVertexCharts

open Set Metric

namespace Schoenflies

theorem PrePolygon.exists_vertex_eq_of_isCornerAt
    {m : ℕ} (P : PrePolygon m) {p : Plane} (hp : IsCornerAt P.carrier p) :
    ∃ i : ZMod (m + 3), P.vertex i = p := by
  obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hp.1
  by_cases hend : p = P.vertex i ∨ p = P.vertex (i + 1)
  · rcases hend with rfl | rfl
    exacts [⟨i, rfl⟩, ⟨i + 1, rfl⟩]
  · exfalso
    push Not at hend
    have hopen : p ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1)) :=
      mem_openSegment_of_ne_left_right (Ne.symm hend.1) (Ne.symm hend.2) hpi
    obtain ⟨r, hr, hball⟩ := exists_pos_forall_of_finite
      (S := {j : ZMod (m + 3) | j ≠ i}) (Set.toFinite _)
      (P := fun j ε => ∀ y ∈ ball p ε, y ∉ P.edge j)
      (fun _ _ _ _ hδε hQ y hy => hQ y (ball_subset_ball hδε hy))
      (fun j hj => by
        obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.mp
          (isCompact_segment (P.vertex j) (P.vertex (j + 1))).isClosed.isOpen_compl p
          (PrePolygon.notMem_edge_of_mem_openSegment hj hopen)
        exact ⟨ρ, hρ, fun y hy => hsub hy⟩)
    refine hp.2 ⟨P.vertex i, P.vertex (i + 1), hopen, r, hr, ?_⟩
    rintro z ⟨hzb, hzC⟩
    obtain ⟨j, hzj⟩ := Set.mem_iUnion.mp hzC
    by_cases hji : j = i
    · exact hji ▸ hzj
    · exact absurd hzj (hball j hji z hzb)

theorem IsCornerAt.of_local_subset
    {C D U : Set Plane} {p : Plane} (hp : IsCornerAt C p)
    (hU : IsOpen U) (hpU : p ∈ U) (hCD : ∀ x ∈ U, x ∈ C → x ∈ D) :
    IsCornerAt D p := by
  refine ⟨hCD p hpU hp.1, ?_⟩
  rintro ⟨a, b, hpab, r, hr, hsub⟩
  obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.mp hU p hpU
  apply hp.2
  refine ⟨a, b, hpab, min r ρ, lt_min hr hρ, ?_⟩
  rintro x ⟨hxb, hxC⟩
  exact hsub ⟨ball_subset_ball (min_le_left _ _) hxb,
    hCD x (hρU (ball_subset_ball (min_le_right _ _) hxb)) hxC⟩

theorem isCornerAt_of_local_segments {C U : Set Plane} {p a b : Plane}
    (hU : IsOpen U) (hpU : p ∈ U) (hcorner : Plane.det (a - p) (b - p) ≠ 0)
    (hlocal : ∀ x ∈ U, x ∈ segment ℝ p a ∪ segment ℝ p b → x ∈ C) :
    IsCornerAt C p := by
  refine ⟨hlocal p hpU (Or.inl (left_mem_segment ℝ p a)), ?_⟩
  rintro ⟨c, d, hpcd, r, hr, hsub⟩
  obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.mp hU p hpU
  let u := b - p
  let w := a - p
  let t := min 1 (min r ρ / (2 * (‖u‖ + ‖w‖ + 1)))
  have hM : (0 : ℝ) < ‖u‖ + ‖w‖ + 1 := by positivity
  have htpos : 0 < t := lt_min one_pos (by positivity)
  have htle : t ≤ 1 := min_le_left _ _
  have key (v : Plane) (hv : ‖v‖ ≤ ‖u‖ + ‖w‖ + 1) : t * ‖v‖ < min r ρ := by
    calc
      t * ‖v‖ ≤ (min r ρ / (2 * (‖u‖ + ‖w‖ + 1))) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg v)
      _ < min r ρ := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg v, lt_min hr hρ]
  have hstep (v : Plane) (hv : ‖v‖ ≤ ‖u‖ + ‖w‖ + 1) :
      p + t • v ∈ ball p (min r ρ) := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos htpos]
    exact key v hv
  have hxmem : p + t • u ∈ segment ℝ c d := by
    have hx := hstep u (by linarith [norm_nonneg w])
    refine hsub ⟨ball_subset_ball (min_le_left _ _) hx,
      hlocal _ (hρU (ball_subset_ball (min_le_right _ _) hx)) (Or.inr ?_)⟩
    refine ⟨1 - t, t, sub_nonneg.mpr htle, htpos.le, by ring, ?_⟩
    dsimp [u]
    module
  have hymem : p + t • w ∈ segment ℝ c d := by
    have hy := hstep w (by linarith [norm_nonneg u])
    refine hsub ⟨ball_subset_ball (min_le_left _ _) hy,
      hlocal _ (hρU (ball_subset_ball (min_le_right _ _) hy)) (Or.inl ?_)⟩
    refine ⟨1 - t, t, sub_nonneg.mpr htle, htpos.le, by ring, ?_⟩
    dsimp [w]
    module
  have hvmem : p ∈ segment ℝ c d := openSegment_subset_segment ℝ _ _ hpcd
  have hdet := det_eq_zero_of_mem_segment hymem hxmem hvmem
  rw [add_sub_cancel_left, add_sub_cancel_left, Plane.det_smul_left,
    Plane.det_smul_right] at hdet
  exact hcorner ((mul_eq_zero.mp ((mul_eq_zero.mp hdet).resolve_left htpos.ne')).resolve_left
    htpos.ne')

theorem PrePolygon.isCornerAt_vertex_of_det_ne_zero
    {m : ℕ} (P : PrePolygon m) (i : ZMod (m + 3))
    (hcorner : Plane.det (P.vertex (i - 1) - P.vertex i)
      (P.vertex (i + 1) - P.vertex i) ≠ 0) :
    IsCornerAt P.carrier (P.vertex i) := by
  apply isCornerAt_of_local_segments isOpen_univ (mem_univ _) hcorner
  rintro x _ (hprev | hnext)
  · apply P.edge_subset_carrier (i - 1)
    change x ∈ segment ℝ (P.vertex (i - 1)) (P.vertex (i - 1 + 1))
    rw [sub_add_cancel, segment_symm]
    exact hprev
  · exact P.edge_subset_carrier i hnext

theorem PrePolygon.isCornerAt_vertex_iff_det_ne_zero
    {m : ℕ} (P : PrePolygon m) (i : ZMod (m + 3)) :
    IsCornerAt P.carrier (P.vertex i) ↔
      Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0 := by
  refine ⟨?_, P.isCornerAt_vertex_of_det_ne_zero i⟩
  intro hcorner hdet
  have hbetween := P.mem_openSegment_of_det_eq_zero i hdet
  obtain ⟨r, hr, hlocal⟩ := P.exists_ball_carrier_eq_incident_edges i
  apply hcorner.2
  refine ⟨P.vertex (i - 1), P.vertex (i + 1), hbetween, r, hr, ?_⟩
  intro x hx
  have he := (hlocal ▸ hx).2
  have hc := openSegment_subset_segment ℝ _ _ hbetween
  rcases he with hprev | hnext
  · change x ∈ segment ℝ (P.vertex (i - 1)) (P.vertex (i - 1 + 1)) at hprev
    rw [sub_add_cancel] at hprev
    exact (convex_segment _ _).segment_subset (left_mem_segment ℝ _ _) hc hprev
  · exact (convex_segment _ _).segment_subset hc (right_mem_segment ℝ _ _) hnext

theorem isCornerAt_of_local_affine_graph
    {C U : Set Plane} {p : Plane} (e : Plane ≃ᵃ[ℝ] Plane) {d : ℝ}
    (hd : d ≠ 0) (hU : IsOpen U) (hpU : p ∈ U) (hep : e p = 0)
    (hgraph : ∀ x ∈ U, (e x) 1 = d * max ((e x) 0) 0 → x ∈ C) :
    IsCornerAt C p := by
  let a := e.symm (Plane.mk (-1) 0)
  let b := e.symm (Plane.mk 1 d)
  have hmap (x : Plane) : e.linear (x - p) = e x := by
    have h : e.linear (x - p) = e x - e p := e.toAffineMap.linearMap_vsub x p
    simpa only [hep, sub_zero] using h
  have haneq : a - p ≠ 0 := by
    intro h
    have hx := congrArg (fun q => (e q) 0) (sub_eq_zero.mp h)
    change (e (e.symm (Plane.mk (-1) 0))) 0 = (e p) 0 at hx
    rw [e.apply_symm_apply, hep] at hx
    norm_num [Plane.mk] at hx
  have hdet : Plane.det (a - p) (b - p) ≠ 0 := by
    intro h
    obtain ⟨r, hr⟩ := (Plane.det_eq_zero_iff_smul _ _ haneq).mp h
    have heq : Plane.mk 1 d = r • Plane.mk (-1) 0 := by
      have he := congrArg e.linear hr
      rw [map_smul, hmap, hmap] at he
      change e (e.symm (Plane.mk 1 d)) = r • e (e.symm (Plane.mk (-1) 0)) at he
      simpa only [e.apply_symm_apply] using he
    have hy := congrArg (fun q : Plane => q 1) heq
    exact hd (by simpa [Plane.mk] using hy)
  apply isCornerAt_of_local_segments hU hpU hdet
  intro x hx hseg
  apply hgraph x hx
  have himage : e x ∈ segment ℝ (Plane.mk (-1) 0) (Plane.mk 0 0) ∪
      segment ℝ (Plane.mk 0 0) (Plane.mk 1 d) := by
    have hpzero : e p = Plane.mk 0 0 := by
      rw [hep]
      ext j
      fin_cases j <;> rfl
    rcases hseg with hseg | hseg
    · have he := mem_image_of_mem e.toAffineMap hseg
      rw [image_segment] at he
      change e x ∈ segment ℝ (e p) (e (e.symm (Plane.mk (-1) 0))) at he
      rw [hpzero, e.apply_symm_apply, segment_symm] at he
      exact Or.inl he
    · have he := mem_image_of_mem e.toAffineMap hseg
      rw [image_segment] at he
      change e x ∈ segment ℝ (e p) (e (e.symm (Plane.mk 1 d))) at he
      rw [hpzero, e.apply_symm_apply] at he
      exact Or.inr he
  apply ((mem_union_segments_iff_max (d := d) zero_lt_one zero_lt_one).mp ?_).2
  simpa only [mul_one] using himage


theorem PrePolygon.exists_corner_equiv_of_local_affine_graphs
    {m : ℕ} (P : PrePolygon m) {ι : Type*} (p : ι → Plane) (hp : Function.Injective p)
    (U : ι → Set Plane) (e : ι → Plane ≃ᵃ[ℝ] Plane) (d : ι → ℝ) {S : Set Plane}
    (hU : ∀ j, IsOpen (U j)) (hpU : ∀ j, p j ∈ U j) (hep : ∀ j, e j (p j) = 0)
    (hgraph : ∀ j, ∀ x ∈ U j, (e j x) 1 = d j * max ((e j x) 0) 0 → x ∈ P.carrier)
    (hpS : ∀ j, d j ≠ 0 → p j ∈ S)
    (hcover : ∀ i, P.vertex i ∈ S →
      Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0 →
      ∃ j, P.vertex i = p j ∧ d j ≠ 0) :
    ∃ f : {j : ι // d j ≠ 0} ≃ {i : ZMod (m + 3) // P.vertex i ∈ S ∧
      Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0},
      ∀ j, P.vertex (f j) = p j := by
  classical
  let I := {j : ι // d j ≠ 0}
  let J := {i : ZMod (m + 3) // P.vertex i ∈ S ∧
    Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0}
  have hcorner (j : I) : IsCornerAt P.carrier (p j) :=
    isCornerAt_of_local_affine_graph (e j) j.property (hU j) (hpU j) (hep j) (hgraph j)
  have hi (j : I) : ∃ i : J, P.vertex i = p j := by
    obtain ⟨i, hi⟩ := P.exists_vertex_eq_of_isCornerAt (hcorner j)
    refine ⟨⟨i, hi.symm ▸ hpS j j.property, ?_⟩, hi⟩
    exact (P.isCornerAt_vertex_iff_det_ne_zero i).mp (hi.symm ▸ hcorner j)
  choose f hf using hi
  have hinj : Function.Injective f := by
    intro j k hjk
    apply Subtype.ext
    exact hp ((hf j).symm.trans ((congrArg (fun i : J => P.vertex i) hjk).trans (hf k)))
  have hsurj : Function.Surjective f := by
    intro i
    obtain ⟨j, hij, hdj⟩ := hcover i i.property.1 i.property.2
    refine ⟨⟨j, hdj⟩, Subtype.ext (P.vertex_inj ?_)⟩
    exact (hf ⟨j, hdj⟩).trans hij.symm
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩


end Schoenflies
