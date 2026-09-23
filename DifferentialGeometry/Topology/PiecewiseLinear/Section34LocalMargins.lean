import DifferentialGeometry.Topology.PiecewiseLinear.IsAnnulusOnCompact
import Mathlib.Topology.MetricSpace.Thickening

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem exists_image_separation_radius {X Y : Type*} [TopologicalSpace X]
    [MetricSpace Y] {U A B : Set X} {h : X → Y}
    (hh : Topology.IsEmbedding (U.domRestrict h)) (hA : IsCompact A) (hB : IsCompact B)
    (hAU : A ⊆ U) (hBU : B ⊆ U) (hd : Disjoint A B) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ A, ∀ y ∈ B, r < dist (h x) (h y) := by
  have hc : ContinuousOn h U := continuousOn_iff_continuous_domRestrict.mpr hh.continuous
  have hi : InjOn h U := fun x hx y hy hxy =>
    congrArg Subtype.val (@hh.injective ⟨x, hx⟩ ⟨y, hy⟩ hxy)
  have hdisj : Disjoint (h '' A) (h '' B) := by
    refine Set.disjoint_left.mpr ?_
    rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
    have hxy := hi (hAU hx) (hBU hy) (hxz.trans hyz.symm)
    exact Set.disjoint_left.mp hd hx (hxy.symm ▸ hy)
  obtain ⟨r, hr, hdist⟩ := Metric.exists_pos_forall_lt_edist
    (hA.image_of_continuousOn (hc.mono hAU))
    (hB.image_of_continuousOn (hc.mono hBU)).isClosed hdisj
  refine ⟨r, by exact_mod_cast hr, fun x hx y hy => ?_⟩
  have hd := hdist (h x) (mem_image_of_mem h hx) (h y) (mem_image_of_mem h hy)
  rw [edist_dist, ← ENNReal.ofReal_coe_nnreal] at hd
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.coe_nonneg).mp hd

private theorem isCompact_of_solid_torus {X : Type*} [TopologicalSpace X]
    {S : Set X} (hS : IsTopologicalSolidTorus S) : IsCompact S := by
  obtain ⟨φ⟩ := hS
  have : CompactSpace S := φ.symm.compactSpace
  exact isCompact_iff_compactSpace.mpr inferInstance

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [MetricSpace M₂]
  {U : Set M₁} {h : M₁ → M₂} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}

theorem exists_section34_local_margins
    (hh : Topology.IsEmbedding (U.domRestrict h))
    (hcc : ∀ w, IsPLCellOn 3 (Cc w) (CcBd w))
    (hcp : ∀ w, IsPLCellOn 3 (Cp w) (CpBd w)) (hCcU : ∀ w, Cc w ⊆ U)
    (hCpCc : ∀ w, Cp w ⊆ interior (Cc w))
    (hvertex : ∀ w, simplexBody 𝒦' w.1 ⊆ interior (Cp w))
    (hQ : ∀ w, h '' Cc w ⊆ interior (Q w))
    (hSn : ∀ e, IsTopologicalSolidTorus (Sn e))
    (hTn : ∀ e, IsTopologicalSolidTorus (Tn e))
    (hTS : ∀ e, Tn e ⊆ interior (Sn e))
    (hincident : ∀ e w, w = (ends e).1 ∨ w = (ends e).2 → Sn e ⊆ Cc w)
    (haa : ∀ e, Aa e = CpBd (ends e).1 ∩ Tn e ∧ IsAnnulusOn (Aa e) (Ab₀ e) (Ab₁ e))
    (hbb : ∀ e, Bb e ⊆ CpBd (ends e).2 ∧ IsAnnulusOn (Bb e) (Bb₀ e) (Bb₁ e))
    (htb : ∀ e, Tn e ∩ CpBd (ends e).2 ⊆ Bb e \ (Bb₀ e ∪ Bb₁ e))
    (hbs : ∀ e, Bb e ⊆ interior (Sn e) ∧ Bb₀ e ∪ Bb₁ e ⊆ Sn e \ Tn e)
    (hbc : ∀ e, IsAnnulusOn (Bc e) (Bc₀ e) (Bc₁ e) ∧
      Bc e ⊆ Bb e ∩ interior (Tn e))
    (hcircle : ∀ e, CpBd (ends e).1 ∩ CpBd (ends e).2 ⊆ Bc e \ (Bc₀ e ∪ Bc₁ e))
    (hab : ∀ e, Ab₀ e ⊆ interior (Cp (ends e).2) ∧ Ab₁ e ∩ Cp (ends e).2 = ∅) :
    ∃ (cap : Section34VertexIndex 𝒦 𝒦' → ℝ)
      (margin : Section34EdgeIndex 𝒦 𝒦' → ℝ),
      (∀ w, 0 < cap w) ∧ (∀ e, 0 < margin e) ∧
      (∀ w, ∀ x ∈ Cc w, Metric.ball (h x) (cap w) ⊆ interior (Q w)) ∧
      (∀ e, ∀ x ∈ Sn e, Metric.ball (h x) (margin e) ⊆
        interior (Q (ends e).1) ∩ interior (Q (ends e).2)) ∧
      (∀ w, ∀ x ∈ CcBd w, ∀ y ∈ h '' simplexBody 𝒦' w.1, cap w < dist (h x) y) ∧
      (∀ w, ∀ x ∈ CpBd w, ∀ y ∈ h '' simplexBody 𝒦' w.1, cap w < dist (h x) y) ∧
      (∀ e, ∀ x ∈ Bb₀ e ∪ Bb₁ e, ∀ y ∈ Tn e, margin e < dist (h x) (h y)) ∧
      (∀ e, ∀ x ∈ CpBd (ends e).1 \ (Aa e \ (Ab₀ e ∪ Ab₁ e)),
        ∀ y ∈ CpBd (ends e).2, margin e < dist (h x) (h y)) ∧
      (∀ e, ∀ x ∈ CpBd (ends e).1,
        ∀ y ∈ CpBd (ends e).2 \ (Bb e \ (Bb₀ e ∪ Bb₁ e)),
        margin e < dist (h x) (h y)) ∧
      (∀ e, ∀ x ∈ Ab₁ e, ∀ y ∈ Cp (ends e).2, margin e < dist (h x) (h y)) ∧
      (∀ e, ∀ x ∈ Bb e, ∀ y ∈ Cc (ends e).1 \ interior (Sn e),
        margin e < dist (h x) (h y)) ∧
      ∀ e, ∀ x ∈ Bc₀ e ∪ Bc₁ e, ∀ y ∈ Sn e \ interior (Tn e),
        margin e < dist (h x) (h y) := by
  have hCpU (w) : Cp w ⊆ U := (hCpCc w).trans (interior_subset.trans (hCcU w))
  have hBdU (w) : CpBd w ⊆ U := (hcp w).boundary_subset.trans (hCpU w)
  have hCBdU (w) : CcBd w ⊆ U := (hcc w).boundary_subset.trans (hCcU w)
  have hSU (e) : Sn e ⊆ U := (hincident e _ (Or.inl rfl)).trans (hCcU _)
  have hTU (e) : Tn e ⊆ U := (hTS e).trans (interior_subset.trans (hSU e))
  have hAaU (e) : Aa e ⊆ U := by
    rw [(haa e).1]
    exact inter_subset_left.trans (hBdU _)
  have hBbU (e) : Bb e ⊆ U := (hbb e).1.trans (hBdU _)
  have hBcU (e) : Bc e ⊆ U := (hbc e).2.trans (inter_subset_left.trans (hBbU e))
  have hBdc (w) : IsCompact (CpBd w) := by
    rw [(hcp w).boundary_eq_frontier]
    exact (hcp w).isCompact.of_isClosed_subset isClosed_frontier
      (frontier_subset_closure.trans (hcp w).isCompact.isClosed.closure_subset)
  have hCBdc (w) : IsCompact (CcBd w) := by
    rw [(hcc w).boundary_eq_frontier]
    exact (hcc w).isCompact.of_isClosed_subset isClosed_frontier
      (frontier_subset_closure.trans (hcc w).isCompact.isClosed.closure_subset)
  have hPc (w : Section34VertexIndex 𝒦 𝒦') : IsCompact (simplexBody 𝒦' w.1) :=
    (w.1.finite_toSet.isCompact_convexHull ℝ).image_of_continuousOn
      (𝒦'.continuousOn.mono (𝒦'.complex.convexHull_subset_space w.2.1))
  have hPU (w : Section34VertexIndex 𝒦 𝒦') : simplexBody 𝒦' w.1 ⊆ U :=
    (hvertex w).trans (interior_subset.trans (hCpU w))
  have hboundary (w) : Disjoint (CcBd w ∪ CpBd w) (simplexBody 𝒦' w.1) := by
    refine Set.disjoint_left.mpr ?_
    intro x hx hy
    rcases hx with hx | hx
    · have hi := hCpCc w (interior_subset (hvertex w hy))
      rw [(hcc w).boundary_eq_frontier] at hx
      exact Set.disjoint_left.mp disjoint_interior_frontier hi hx
    · rw [(hcp w).boundary_eq_frontier] at hx
      exact Set.disjoint_left.mp disjoint_interior_frontier (hvertex w hy) hx
  have hv := fun w => exists_image_separation_radius hh ((hCBdc w).union (hBdc w))
    (hPc w) (union_subset (hCBdU w) (hBdU w)) (hPU w) (hboundary w)
  choose v hv hvdist using hv
  have hc : ContinuousOn h U := continuousOn_iff_continuous_domRestrict.mpr hh.continuous
  have hq (w : Section34VertexIndex 𝒦 𝒦') :
      ∃ q : ℝ, 0 < q ∧ ∀ x ∈ Cc w, Metric.ball (h x) q ⊆ interior (Q w) := by
    obtain ⟨q, hq, hqQ⟩ := ((hcc w).isCompact.image_of_continuousOn
      (hc.mono (hCcU w))).exists_thickening_subset_open isOpen_interior (hQ w)
    exact ⟨q, hq, fun x hx =>
      (Metric.ball_subset_thickening (mem_image_of_mem h hx) q).trans hqQ⟩
  choose q hq hqQ using hq
  let A (e : Section34EdgeIndex 𝒦 𝒦') : Fin 6 → Set M₁ :=
    ![Bb₀ e ∪ Bb₁ e, (CpBd (ends e).1 \ interior (Tn e)) ∪ (Ab₀ e ∪ Ab₁ e),
      CpBd (ends e).1, Ab₁ e, Bb e, Bc₀ e ∪ Bc₁ e]
  let B (e : Section34EdgeIndex 𝒦 𝒦') : Fin 6 → Set M₁ :=
    ![Tn e, CpBd (ends e).2, CpBd (ends e).2 \ interior (Tn e), Cp (ends e).2,
      Cc (ends e).1 \ interior (Sn e), Sn e \ interior (Tn e)]
  have hAc (e) (i : Fin 6) : IsCompact (A e i) := by
    fin_cases i <;> dsimp [A]
    · exact (hbb e).2.isCompact_first.union (hbb e).2.isCompact_second
    · exact ((hBdc _).diff isOpen_interior).union
        ((haa e).2.isCompact_first.union (haa e).2.isCompact_second)
    · exact hBdc _
    · exact (haa e).2.isCompact_second
    · exact (hbb e).2.isCompact
    · exact (hbc e).1.isCompact_first.union (hbc e).1.isCompact_second
  have hBc (e) (i : Fin 6) : IsCompact (B e i) := by
    fin_cases i <;> dsimp [B]
    · exact isCompact_of_solid_torus (hTn e)
    · exact hBdc _
    · exact (hBdc _).diff isOpen_interior
    · exact (hcp _).isCompact
    · exact (hcc _).isCompact.diff isOpen_interior
    · exact (isCompact_of_solid_torus (hSn e)).diff isOpen_interior
  have hAU (e) (i : Fin 6) : A e i ⊆ U := by
    fin_cases i <;> dsimp [A]
    · exact union_subset ((hbb e).2.first_subset.trans (hBbU e))
        ((hbb e).2.second_subset.trans (hBbU e))
    · exact union_subset (sdiff_subset.trans (hBdU _))
        (union_subset ((haa e).2.first_subset.trans (hAaU e))
          ((haa e).2.second_subset.trans (hAaU e)))
    · exact hBdU _
    · exact (haa e).2.second_subset.trans (hAaU e)
    · exact hBbU e
    · exact union_subset ((hbc e).1.first_subset.trans (hBcU e))
        ((hbc e).1.second_subset.trans (hBcU e))
  have hBU (e) (i : Fin 6) : B e i ⊆ U := by
    fin_cases i <;> dsimp [B]
    · exact hTU e
    · exact hBdU _
    · exact sdiff_subset.trans (hBdU _)
    · exact hCpU _
    · exact sdiff_subset.trans (hCcU _)
    · exact sdiff_subset.trans (hSU e)
  have hcircleT (e) : CpBd (ends e).1 ∩ CpBd (ends e).2 ⊆ interior (Tn e) :=
    (hcircle e).trans (sdiff_subset.trans ((hbc e).2.trans inter_subset_right))
  have hdisj (e) (i : Fin 6) : Disjoint (A e i) (B e i) := by
    fin_cases i <;> dsimp [A, B] <;> apply Set.disjoint_left.mpr
    · exact fun x hx hy => (hbs e).2 hx |>.2 hy
    · intro x hx hy
      rcases hx with hx | hx | hx
      · exact hx.2 (hcircleT e ⟨hx.1, hy⟩)
      · rw [(hcp _).boundary_eq_frontier] at hy
        exact Set.disjoint_left.mp disjoint_interior_frontier ((hab e).1 hx) hy
      · have hmem : x ∈ Ab₁ e ∩ Cp (ends e).2 := ⟨hx, (hcp _).boundary_subset hy⟩
        rw [(hab e).2] at hmem
        exact hmem
    · exact fun x hx hy => hy.2 (hcircleT e ⟨hx, hy.1⟩)
    · intro x hx hy
      have hmem : x ∈ Ab₁ e ∩ Cp (ends e).2 := ⟨hx, hy⟩
      rw [(hab e).2] at hmem
      exact hmem
    · exact fun x hx hy => hy.2 ((hbs e).1 hx)
    · intro x hx hy
      have hxBc : x ∈ Bc e := hx.elim
        (fun hx => (hbc e).1.first_subset hx) (fun hx => (hbc e).1.second_subset hx)
      exact hy.2 ((hbc e).2 hxBc).2
  have hedge := fun e i => exists_image_separation_radius hh (hAc e i) (hBc e i)
    (hAU e i) (hBU e i) (hdisj e i)
  choose d hd hdist using hedge
  have hm (e) : ∃ m : ℝ, 0 < m ∧ ∀ i, m ≤ d e i := by
    obtain ⟨i, hi⟩ := Finite.exists_min (d e)
    exact ⟨d e i, hd e i, hi⟩
  choose m hm hmd using hm
  let cap (w : Section34VertexIndex 𝒦 𝒦') := min (q w) (v w)
  let margin (e : Section34EdgeIndex 𝒦 𝒦') := min (q (ends e).1) (min (q (ends e).2) (m e))
  have hmargin (e) : margin e ≤ m e :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hbound (e) (i : Fin 6) {x y : M₁} (hx : x ∈ A e i) (hy : y ∈ B e i) :
      margin e < dist (h x) (h y) :=
    ((hmargin e).trans (hmd e i)).trans_lt (hdist e i x hx y hy)
  refine ⟨cap, margin, fun w => lt_min (hq w) (hv w),
    fun e => lt_min (hq _) (lt_min (hq _) (hm e)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w x hx
    exact (Metric.ball_subset_ball (min_le_left _ _)).trans (hqQ w x hx)
  · intro e x hx y hy
    exact ⟨hqQ _ x (hincident e _ (Or.inl rfl) hx)
        (Metric.ball_subset_ball (min_le_left _ _) hy),
      hqQ _ x (hincident e _ (Or.inr rfl) hx)
        (Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hy)⟩
  · rintro w x hx y ⟨z, hz, rfl⟩
    exact (min_le_right _ _).trans_lt (hvdist w x (Or.inl hx) z hz)
  · rintro w x hx y ⟨z, hz, rfl⟩
    exact (min_le_right _ _).trans_lt (hvdist w x (Or.inr hx) z hz)
  · intro e x hx y hy
    exact hbound e 0 hx hy
  · intro e x hx y hy
    apply hbound e 1 ?_ hy
    by_cases hxT : x ∈ Tn e
    · apply Or.inr
      by_contra hxAb
      apply hx.2
      refine ⟨?_, hxAb⟩
      rw [(haa e).1]
      exact ⟨hx.1, hxT⟩
    · exact Or.inl ⟨hx.1, fun hi => hxT (interior_subset hi)⟩
  · intro e x hx y hy
    exact hbound e 2 hx ⟨hy.1, fun hi => hy.2 (htb e ⟨interior_subset hi, hy.1⟩)⟩
  · intro e x hx y hy
    exact hbound e 3 hx hy
  · intro e x hx y hy
    exact hbound e 4 hx hy
  · intro e x hx y hy
    exact hbound e 5 hx hy

end DifferentialGeometry.Topology.PiecewiseLinear
