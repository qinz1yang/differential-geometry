import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteSeparationScales
import DifferentialGeometry.Topology.PiecewiseLinear.Section34LensImages

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [MetricSpace M₂]
  {U : Set M₁} {h : M₁ → M₂} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {Cp CpBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn : Section34EdgeIndex 𝒦 𝒦' → Set M₁}

theorem exists_section34_separation_margins
    (hh : Topology.IsEmbedding (U.domRestrict h))
    (hends : ∀ e, (e.1 : Set Ea) =
      ((ends e).1.1 : Set Ea) ∪ ((ends e).2.1 : Set Ea))
    (hcp : ∀ w, IsPLCellOn 3 (Cp w) (CpBd w)) (hCpU : ∀ w, Cp w ⊆ U)
    (hCpLF : LocallyFinite fun w => {x : U | (x : M₁) ∈ Cp w})
    (hSn : ∀ e, IsCompact (Sn e)) (hSnU : ∀ e, Sn e ⊆ U)
    (hSnLF : LocallyFinite fun e => {x : U | (x : M₁) ∈ Sn e})
    (hcore : ∀ w, IsCompact (Kcore w) ∧ simplexBody 𝒦' w.1 ⊆ Kcore w ∧
      Kcore w ⊆ Cp w \ CpBd w)
    (hcover : graphSkeletonSpace 𝒦 ⊆ ⋃ w, Kcore w)
    (hSnK : ∀ e w, Disjoint (Sn e) (Kcore w))
    (hSnBd : ∀ e w, w ≠ (ends e).1 → w ≠ (ends e).2 → Disjoint (Sn e) (CpBd w))
    (hSnSn : ∀ e d, e ≠ d → Disjoint (Sn e) (Sn d))
    (hforeign : ∀ w w', w ≠ w' → Disjoint (Cp w') (simplexBody 𝒦' w.1))
    (cap : Section34VertexIndex 𝒦 𝒦' → ℝ) (hcap : ∀ w, 0 < cap w)
    (margin : Section34EdgeIndex 𝒦 𝒦' → ℝ) (hmargin : ∀ e, 0 < margin e) :
    ∃ ε : Section34VertexIndex 𝒦 𝒦' → ℝ,
      (∀ w, 0 < ε w) ∧ (∀ w, ε w < cap w) ∧
      (∀ e, ε (ends e).1 + ε (ends e).2 < margin e) ∧
      (∀ e w, w = (ends e).1 ∨ w = (ends e).2 → ∀ x ∈ Sn e,
        ∀ y ∈ graphSkeletonSpace 𝒦, ε w < dist (h x) (h y)) ∧
      (∀ e w, ∀ x ∈ Sn e, ∀ y ∈ simplexBody 𝒦' w.1,
        ε (ends e).1 + ε w < dist (h x) (h y)) ∧
      (∀ e w, w ≠ (ends e).1 → w ≠ (ends e).2 → ∀ x ∈ Sn e, ∀ y ∈ CpBd w,
        ε (ends e).1 + ε w < dist (h x) (h y)) ∧
      (∀ w w', Disjoint (Cp w) (Cp w') → ∀ x ∈ Cp w, ∀ y ∈ Cp w',
        ε w + ε w' < dist (h x) (h y)) ∧
      (∀ e d, e ≠ d → ∀ x ∈ Sn e, ∀ y ∈ Sn d,
        ε (ends e).1 + ε (ends d).1 < dist (h x) (h y)) ∧
      (∀ e w, ∀ x ∈ Sn e, ∀ y ∈ Kcore w,
        ε (ends e).1 + ε w < dist (h x) (h y)) ∧
      ∀ w w', w ≠ w' → ∀ x ∈ Cp w', ∀ y ∈ simplexBody 𝒦' w.1,
        ε w' < dist (h x) (h y) := by
  let P (w : Section34VertexIndex 𝒦 𝒦') := simplexBody 𝒦' w.1
  let J := Section34VertexIndex 𝒦 𝒦' ⊕ Section34VertexIndex 𝒦 𝒦' ⊕
    Section34VertexIndex 𝒦 𝒦' ⊕ Section34VertexIndex 𝒦 𝒦' ⊕ Section34EdgeIndex 𝒦 𝒦'
  let F : J → Set M₁ := Sum.elim Cp (Sum.elim CpBd (Sum.elim Kcore (Sum.elim P Sn)))
  let iCp (w : Section34VertexIndex 𝒦 𝒦') : J := .inl w
  let iBd (w : Section34VertexIndex 𝒦 𝒦') : J := .inr (.inl w)
  let iK (w : Section34VertexIndex 𝒦 𝒦') : J := .inr (.inr (.inl w))
  let iP (w : Section34VertexIndex 𝒦 𝒦') : J := .inr (.inr (.inr (.inl w)))
  let iSn (e : Section34EdgeIndex 𝒦 𝒦') : J := .inr (.inr (.inr (.inr e)))
  have hBdCp (w : Section34VertexIndex 𝒦 𝒦') : CpBd w ⊆ Cp w := (hcp w).boundary_subset
  have hKCp (w : Section34VertexIndex 𝒦 𝒦') : Kcore w ⊆ Cp w :=
    (hcore w).2.2.trans sdiff_subset
  have hPCp (w : Section34VertexIndex 𝒦 𝒦') : P w ⊆ Cp w :=
    (hcore w).2.1.trans (hKCp w)
  have hFC : ∀ i, IsCompact (F i) := by
    rintro (w | w | w | w | e)
    · exact (hcp w).isCompact
    · change IsCompact (CpBd w)
      rw [(hcp w).boundary_eq_frontier]
      exact (hcp w).isCompact.of_isClosed_subset isClosed_frontier
        (frontier_subset_closure.trans (hcp w).isCompact.isClosed.closure_subset)
    · exact (hcore w).1
    · exact (w.1.finite_toSet.isCompact_convexHull ℝ).image_of_continuousOn
        (𝒦'.continuousOn.mono (𝒦'.complex.convexHull_subset_space w.2.1))
    · exact hSn e
  have hFU : ∀ i, F i ⊆ U := by
    rintro (w | w | w | w | e)
    · exact hCpU w
    · exact (hBdCp w).trans (hCpU w)
    · exact (hKCp w).trans (hCpU w)
    · exact (hPCp w).trans (hCpU w)
    · exact hSnU e
  have hFLF : LocallyFinite fun i => {x : U | (x : M₁) ∈ F i} := by
    convert hCpLF.sumElim ((hCpLF.subset fun w _ hx => hBdCp w hx).sumElim
      ((hCpLF.subset fun w _ hx => hKCp w hx).sumElim
        ((hCpLF.subset fun w _ hx => hPCp w hx).sumElim hSnLF))) using 1
    funext i
    rcases i with (w | w | w | w | e) <;> rfl
  have hcont : ContinuousOn h U := continuousOn_iff_continuous_domRestrict.mpr hh.continuous
  have hinj : InjOn h U := fun x hx y hy hxy =>
    congrArg Subtype.val (@hh.injective ⟨x, hx⟩ ⟨y, hy⟩ hxy)
  have hImgLF := locallyFinite_image_of_embedding hh hFU hFLF
  obtain ⟨r, hr, -, hsep⟩ := exists_separation_scales_of_locallyFinite_on
    (fun i => (hFC i).image_of_continuousOn (hcont.mono (hFU i)))
    (fun i => image_mono (hFU i)) hImgLF (fun _ => zero_lt_one)
  have hdist (i j : J) (hd : Disjoint (F i) (F j)) {x y : M₁}
      (hx : x ∈ F i) (hy : y ∈ F j) : r i + r j < dist (h x) (h y) := by
    apply hsep i j ?_ (h x) (mem_image_of_mem h hx) (h y) (mem_image_of_mem h hy)
    refine Set.disjoint_left.mpr ?_
    rintro z ⟨a, ha, haz⟩ ⟨b, hb, hbz⟩
    have hab : a = b := hinj (hFU i ha) (hFU j hb) (haz.trans hbz.symm)
    exact Set.disjoint_left.mp hd ha (hab.symm ▸ hb)
  let c (w : Section34VertexIndex 𝒦 𝒦') :=
    min (cap w) (min (r (iCp w)) (min (r (iBd w)) (min (r (iK w)) (r (iP w)))))
  have hc : ∀ w, 0 < c w := fun w =>
    lt_min (hcap w) (lt_min (hr _) (lt_min (hr _) (lt_min (hr _) (hr _))))
  obtain ⟨ε, hε, hεc, hsum⟩ := exists_section34_vertex_scales_with_sum_margins hends c hc
    (fun e => min (margin e) (r (iSn e))) (fun e => lt_min (hmargin e) (hr _))
  have hεcap (w) : ε w < cap w := (hεc w).trans_le (min_le_left _ _)
  have hεCp (w) : ε w ≤ r (iCp w) :=
    (hεc w).le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεBd (w) : ε w ≤ r (iBd w) :=
    (hεc w).le.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hεK (w) : ε w ≤ r (iK w) :=
    (hεc w).le.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hεP (w) : ε w ≤ r (iP w) :=
    (hεc w).le.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hεSn (e w) (hw : w = (ends e).1 ∨ w = (ends e).2) : ε w ≤ r (iSn e) := by
    have he := (hsum e).trans_le (min_le_right _ _)
    rcases hw with rfl | rfl
    · linarith [hε (ends e).2]
    · linarith [hε (ends e).1]
  refine ⟨ε, hε, hεcap, fun e => (hsum e).trans_le (min_le_left _ _),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e w hw x hx y hy
    obtain ⟨v, hv⟩ := mem_iUnion.mp (hcover hy)
    have hd := hdist (iSn e) (iK v) (hSnK e v) hx hv
    linarith [hεSn e w hw, hr (iK v)]
  · intro e w x hx y hy
    exact (add_le_add (hεSn e _ (Or.inl rfl)) (hεP w)).trans_lt
      (hdist (iSn e) (iP w) ((hSnK e w).mono_right (hcore w).2.1) hx hy)
  · intro e w hwa hwb x hx y hy
    exact (add_le_add (hεSn e _ (Or.inl rfl)) (hεBd w)).trans_lt
      (hdist (iSn e) (iBd w) (hSnBd e w hwa hwb) hx hy)
  · intro w w' hd x hx y hy
    exact (add_le_add (hεCp w) (hεCp w')).trans_lt (hdist (iCp w) (iCp w') hd hx hy)
  · intro e d hed x hx y hy
    exact (add_le_add (hεSn e _ (Or.inl rfl)) (hεSn d _ (Or.inl rfl))).trans_lt
      (hdist (iSn e) (iSn d) (hSnSn e d hed) hx hy)
  · intro e w x hx y hy
    exact (add_le_add (hεSn e _ (Or.inl rfl)) (hεK w)).trans_lt
      (hdist (iSn e) (iK w) (hSnK e w) hx hy)
  · intro w w' hww x hx y hy
    have hd := hdist (iCp w') (iP w) (hforeign w w' hww) hx hy
    linarith [hεCp w', hr (iP w)]

end DifferentialGeometry.Topology.PiecewiseLinear
