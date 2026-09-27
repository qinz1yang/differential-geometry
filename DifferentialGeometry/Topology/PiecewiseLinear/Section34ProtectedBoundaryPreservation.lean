import DifferentialGeometry.Topology.PiecewiseLinear.Section34ProtectedLensPreservation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U W : Set M₁} {h : M₁ → M₂}
  {η ψ : M₁ → ℝ} {H : Finset Ea → Set M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ct : Section34SimplexIndex 𝒦 3 → OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3))}
  {Sd : Section34SimplexIndex 𝒦 3 → Set (EuclideanSpace ℝ (Fin 3))}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}


omit [FiniteDimensional ℝ Ea] in
private theorem mem_modified_image_iff
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (e₀ : Section34EdgeIndex 𝒦 𝒦')
    (hoff : ∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)})
    (hin : ∀ w, ∀ x ∈ Cp w, G w x ∈ interior (Sp e₀) → G' w x ∈ interior (Sp e₀))
    (w : Section34VertexIndex 𝒦 𝒦') {A : Set M₁} (hA : A ⊆ Cp w)
    {y : M₂} (hy : y ∉ interior (Sp e₀)) : y ∈ G' w '' A ↔ y ∈ G w '' A := by
  obtain ⟨-, -, hsub, -⟩ := hprep
  constructor
  · rintro ⟨x, hx, hxy⟩
    have hout : G w x ∉ interior (Sp e₀) := fun hxV => hy (hxy ▸ hin w x (hA hx) hxV)
    exact ⟨x, hx, (hoff w ⟨(hsub w).2.1 (hA hx), hout⟩).symm.trans hxy⟩
  · rintro ⟨x, hx, hxy⟩
    exact ⟨x, hx, (hoff w ⟨(hsub w).2.1 (hA hx), hxy ▸ hy⟩).trans hxy⟩

omit [FiniteDimensional ℝ Ea] in
private theorem mem_modified_interior_iff
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (e₀ : Section34EdgeIndex 𝒦 𝒦')
    (hoff : ∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)})
    (hin : ∀ w, ∀ x ∈ Cp w, G w x ∈ interior (Sp e₀) → G' w x ∈ interior (Sp e₀))
    (hG' : ∀ w, IsPLHomeomorphInto 3 (G' w) (Cp w))
    (w : Section34VertexIndex 𝒦 𝒦') {y : M₂} (hy : y ∉ interior (Sp e₀)) :
    y ∈ interior (G' w '' Cp w) ↔ y ∈ interior (G w '' Cp w) := by
  obtain ⟨-, -, -, -, hCp, -⟩ := id hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hG, -⟩ := hpack
  rw [← ((hCp w).image_boundary_interior (hG' w)).2,
    ← ((hCp w).image_boundary_interior (hG w)).2]
  exact mem_modified_image_iff hprep G' e₀ hoff hin w sdiff_subset hy

omit [FiniteDimensional ℝ Ea] in
private theorem first_annulus_image_subset_support
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') :
    G (ends e).1 '' Aa e ⊆ Sp e := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hTnSn, -, -, hAa, -⟩ := hprep
  obtain ⟨-, -, -, hSp, -⟩ := hpack
  rw [(hSp e).1, (hAa e).1]
  exact image_mono (inter_subset_right.trans ((hTnSn e).1.trans interior_subset))

omit [FiniteDimensional ℝ Ea] in
theorem section34Step_other_boundary_intersection
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (e₀ : Section34EdgeIndex 𝒦 𝒦')
    (hoff : ∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)})
    (hin : ∀ w, ∀ x ∈ Cp w, G w x ∈ interior (Sp e₀) → G' w x ∈ interior (Sp e₀))
    (e : Section34EdgeIndex 𝒦 𝒦') (he : e ≠ e₀) :
    G' (ends e).1 '' CpBd (ends e).1 ∩ G' (ends e).2 '' CpBd (ends e).2 =
      G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' CpBd (ends e).2 := by
  have hlens := section34Step_other_lens_eq hprep hpack G' e₀ hoff hin e he
  have hsep := section34_support_disjoint_other_lens hprep hpack e₀ e he.symm
  obtain ⟨-, -, -, -, hCp, -⟩ := id hprep
  have hmono (F : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) :
      F (ends e).1 '' CpBd (ends e).1 ∩ F (ends e).2 '' CpBd (ends e).2 ⊆
        F (ends e).1 '' Cp (ends e).1 ∩ F (ends e).2 '' Cp (ends e).2 :=
    inter_subset_inter (image_mono (hCp _).boundary_subset)
      (image_mono (hCp _).boundary_subset)
  ext y
  by_cases hy : y ∈ interior (Sp e₀)
  · have hold : y ∉ G (ends e).1 '' Cp (ends e).1 ∩ G (ends e).2 '' Cp (ends e).2 :=
      fun hmem => Set.disjoint_left.mp hsep (interior_subset hy) hmem
    have hnew : y ∉ G' (ends e).1 '' Cp (ends e).1 ∩ G' (ends e).2 '' Cp (ends e).2 := by
      rwa [hlens]
    exact iff_of_false (fun hmem => hnew (hmono G' hmem))
      (fun hmem => hold (hmono G hmem))
  · exact and_congr
      (mem_modified_image_iff hprep G' e₀ hoff hin _ (hCp _).boundary_subset hy)
      (mem_modified_image_iff hprep G' e₀ hoff hin _ (hCp _).boundary_subset hy)

omit [FiniteDimensional ℝ Ea] in
theorem section34Step_other_boundary_containment
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (e₀ : Section34EdgeIndex 𝒦 𝒦')
    (hoff : ∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)})
    (hin : ∀ w, ∀ x ∈ Cp w, G w x ∈ interior (Sp e₀) → G' w x ∈ interior (Sp e₀))
    (e : Section34EdgeIndex 𝒦 𝒦') (he : e ≠ e₀) :
    G' (ends e).1 '' CpBd (ends e).1 ∩ G' (ends e).2 '' CpBd (ends e).2 ⊆
      G' (ends e).1 '' (Aa e \ (Ab₀ e ∪ Ab₁ e)) ∩
        G' (ends e).2 '' (Bb e \ (Bb₀ e ∪ Bb₁ e)) ∩ interior (Tp e) := by
  rw [section34Step_other_boundary_intersection hprep hpack G' e₀ hoff hin e he]
  obtain ⟨hA, hB⟩ := section34Step_eqOn_other_annuli hprep hpack G' e₀ hoff e he
  rw [(hA.mono sdiff_subset).image_eq, (hB.mono sdiff_subset).image_eq]
  obtain ⟨-, -, -, -, -, -, hmeet, -⟩ := hpack
  exact hmeet e

omit [FiniteDimensional ℝ Ea] in
theorem section34Step_other_piercing_sides
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (e₀ : Section34EdgeIndex 𝒦 𝒦')
    (hoff : ∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)})
    (hin : ∀ w, ∀ x ∈ Cp w, G w x ∈ interior (Sp e₀) → G' w x ∈ interior (Sp e₀))
    (hG' : ∀ w, IsPLHomeomorphInto 3 (G' w) (Cp w))
    (e : Section34EdgeIndex 𝒦 𝒦') (he : e ≠ e₀) :
    G' (ends e).1 '' Ab₀ e ⊆ interior (G' (ends e).2 '' Cp (ends e).2) ∧
      Disjoint (G' (ends e).1 '' Ab₁ e) (G' (ends e).2 '' Cp (ends e).2) := by
  have hA := (section34Step_eqOn_other_annuli hprep hpack G' e₀ hoff e he).1
  have hASp := first_annulus_image_subset_support hprep hpack e
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hAa, -⟩ := id hprep
  obtain ⟨-, -, -, -, -, hdisj, -, hside, -⟩ := id hpack
  have hout : ∀ y ∈ G (ends e).1 '' Aa e, y ∉ interior (Sp e₀) :=
    fun y hy hyV => Set.disjoint_left.mp (hdisj e e₀ he) (hASp hy) (interior_subset hyV)
  rw [(hA.mono (hAa e).2.first_subset).image_eq,
    (hA.mono (hAa e).2.second_subset).image_eq]
  constructor
  · intro y hy
    exact (mem_modified_interior_iff hprep hpack G' e₀ hoff hin hG' _
      (hout y (image_mono (hAa e).2.first_subset hy))).mpr ((hside e).1 hy)
  · refine Set.disjoint_left.mpr ?_
    intro y hy hyCp
    have hyV := hout y (image_mono (hAa e).2.second_subset hy)
    exact Set.disjoint_left.mp (hside e).2 hy
      ((mem_modified_image_iff hprep G' e₀ hoff hin _ Subset.rfl hyV).mp hyCp)

omit [FiniteDimensional ℝ Ea] in
theorem section34Step_other_component_sets
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (e₀ : Section34EdgeIndex 𝒦 𝒦')
    (hoff : ∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)})
    (hin : ∀ w, ∀ x ∈ Cp w, G w x ∈ interior (Sp e₀) → G' w x ∈ interior (Sp e₀))
    (e : Section34EdgeIndex 𝒦 𝒦') (he : e ≠ e₀) :
    (G' (ends e).2 '' Bb e ∩ G' (ends e).1 '' Cp (ends e).1 =
      G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) ∧
      (G' (ends e).2 '' Bb e \ G' (ends e).1 '' Cp (ends e).1 =
        G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) := by
  rw [(section34Step_other_annulus_images hprep hpack G' e₀ hoff e he).2]
  obtain ⟨-, -, -, -, -, hdisj, -, -, hBb, -⟩ := hpack
  have hout : ∀ y ∈ G (ends e).2 '' Bb e, y ∉ interior (Sp e₀) :=
    fun y hy hyV => Set.disjoint_left.mp (hdisj e e₀ he)
      (interior_subset ((hBb e).1 hy)) (interior_subset hyV)
  constructor
  · ext y
    by_cases hy : y ∈ G (ends e).2 '' Bb e
    · exact and_congr Iff.rfl
        (mem_modified_image_iff hprep G' e₀ hoff hin _ Subset.rfl (hout y hy))
    · simp only [mem_inter_iff, hy, false_and]
  · ext y
    by_cases hy : y ∈ G (ends e).2 '' Bb e
    · exact and_congr Iff.rfl
        (not_congr (mem_modified_image_iff hprep G' e₀ hoff hin _ Subset.rfl (hout y hy)))
    · simp only [mem_sdiff, hy, false_and]

omit [FiniteDimensional ℝ Ea] in
theorem section34Step_support_disjoint_other_boundaries
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (e₀ : Section34EdgeIndex 𝒦 𝒦')
    (hoff : ∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)})
    (hin : ∀ w, ∀ x ∈ Cp w, G w x ∈ interior (Sp e₀) → G' w x ∈ interior (Sp e₀))
    (e : Section34EdgeIndex 𝒦 𝒦') (w : Section34VertexIndex 𝒦 𝒦')
    (hw₁ : w ≠ (ends e).1) (hw₂ : w ≠ (ends e).2) :
    Disjoint (Sp e) (G' w '' CpBd w) := by
  obtain ⟨-, -, -, -, hCp, -⟩ := id hprep
  obtain ⟨-, -, -, -, -, hdisj, -, -, -, -, -, -, hbd, -⟩ := id hpack
  by_cases he : e = e₀
  · subst e
    rw [((section34Step_eqOn_marker_and_boundary hprep hpack G' e₀ hoff).2 w hw₁ hw₂).image_eq]
    exact hbd e₀ w hw₁ hw₂
  · refine Set.disjoint_left.mpr ?_
    intro y hy hyBd
    have hyV : y ∉ interior (Sp e₀) :=
      fun hyV => Set.disjoint_left.mp (hdisj e e₀ he) hy (interior_subset hyV)
    exact Set.disjoint_left.mp (hbd e w hw₁ hw₂) hy
      ((mem_modified_image_iff hprep G' e₀ hoff hin w (hCp w).boundary_subset hyV).mp hyBd)

end DifferentialGeometry.Topology.PiecewiseLinear
