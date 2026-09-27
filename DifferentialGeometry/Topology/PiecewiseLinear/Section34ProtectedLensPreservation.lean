import DifferentialGeometry.Topology.PiecewiseLinear.Section34ProtectedCircleSupport
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ProtectedSupportIsolation

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
theorem section34Step_eqOn_other_cells
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (e₀ : Section34EdgeIndex 𝒦 𝒦')
    (hoff : ∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)})
    (w : Section34VertexIndex 𝒦 𝒦') (hw₁ : w ≠ (ends e₀).1) (hw₂ : w ≠ (ends e₀).2) :
    EqOn (G' w) (G w) (Cp w) := by
  have hdisj := section34_support_disjoint_other_cell hprep hpack e₀ w hw₁ hw₂
  obtain ⟨-, -, hsub, -⟩ := hprep
  exact eqOn_of_eqOn_off_support (hoff w) (hsub w).2.1
    (hdisj.symm.mono_right interior_subset)

omit [FiniteDimensional ℝ Ea] in
theorem section34Step_support_disjoint_other_lens
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (e₀ : Section34EdgeIndex 𝒦 𝒦')
    (hoff : ∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)})
    (e : Section34EdgeIndex 𝒦 𝒦') (he : e ≠ e₀) :
    Disjoint (Sp e₀)
      (G' (ends e).1 '' Cp (ends e).1 ∩ G' (ends e).2 '' Cp (ends e).2) := by
  have hisolate : ∀ w, w ≠ (ends e₀).1 → w ≠ (ends e₀).2 → Disjoint (Sp e₀) (G' w '' Cp w) := by
    intro w hw₁ hw₂
    rw [(section34Step_eqOn_other_cells hprep hpack G' e₀ hoff w hw₁ hw₂).image_eq]
    exact section34_support_disjoint_other_cell hprep hpack e₀ w hw₁ hw₂
  obtain ⟨-, -, -, -, -, -, -, -, hends, -⟩ := hprep
  by_cases hda : (ends e).1 = (ends e₀).1 ∨ (ends e).1 = (ends e₀).2
  · by_cases hdb : (ends e).2 = (ends e₀).1 ∨ (ends e).2 = (ends e₀).2
    · exfalso
      apply he
      apply Subtype.ext
      apply Finset.coe_injective
      rw [(hends e).2.1, (hends e₀).2.1]
      rcases hda with hda | hda <;> rcases hdb with hdb | hdb
      · exact ((hends e).1 (hda.trans hdb.symm)).elim
      · rw [hda, hdb]
      · rw [hda, hdb, union_comm]
      · exact ((hends e).1 (hda.trans hdb.symm)).elim
    · exact (hisolate _ (fun h => hdb (Or.inl h)) (fun h => hdb (Or.inr h))).mono_right
        inter_subset_right
  · exact (hisolate _ (fun h => hda (Or.inl h)) (fun h => hda (Or.inr h))).mono_right
      inter_subset_left

omit [FiniteDimensional ℝ Ea] in
theorem section34Step_other_lens_eq
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (e₀ : Section34EdgeIndex 𝒦 𝒦')
    (hoff : ∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)})
    (hin : ∀ w, ∀ x ∈ Cp w, G w x ∈ interior (Sp e₀) → G' w x ∈ interior (Sp e₀))
    (e : Section34EdgeIndex 𝒦 𝒦') (he : e ≠ e₀) :
    G' (ends e).1 '' Cp (ends e).1 ∩ G' (ends e).2 '' Cp (ends e).2 =
      G (ends e).1 '' Cp (ends e).1 ∩ G (ends e).2 '' Cp (ends e).2 := by
  have hdiff := section34Step_lens_diff_support hprep G' e₀ hoff hin e
  have hnew := section34Step_support_disjoint_other_lens hprep hpack G' e₀ hoff e he
  have hold := section34_support_disjoint_other_lens hprep hpack e₀ e he.symm
  rw [sdiff_eq_left.mpr (hnew.symm.mono_right interior_subset),
    sdiff_eq_left.mpr (hold.symm.mono_right interior_subset)] at hdiff
  exact hdiff

omit [FiniteDimensional ℝ Ea] in
theorem section34Step_lenses_disjoint
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (e₀ : Section34EdgeIndex 𝒦 𝒦')
    (hoff : ∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)})
    (hin : ∀ w, ∀ x ∈ Cp w, G w x ∈ interior (Sp e₀) → G' w x ∈ interior (Sp e₀)) :
    ∀ e d, e ≠ d →
      Disjoint (G' (ends e).1 '' Cp (ends e).1 ∩ G' (ends e).2 '' Cp (ends e).2)
        (G' (ends d).1 '' Cp (ends d).1 ∩ G' (ends d).2 '' Cp (ends d).2) := by
  have hdiff := section34Step_lens_diff_support hprep G' e₀ hoff hin
  have hnew := section34Step_support_disjoint_other_lens hprep hpack G' e₀ hoff
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hlens, -⟩ := hpack
  intro e d hed
  refine Set.disjoint_left.mpr ?_
  intro y hye hyd
  have hyoff : y ∉ interior (Sp e₀) := by
    by_cases he : e = e₀
    · exact fun hy => Set.disjoint_left.mp (hnew d (fun hd => hed (he.trans hd.symm)))
        (interior_subset hy) hyd
    · exact fun hy => Set.disjoint_left.mp (hnew e he) (interior_subset hy) hye
  exact Set.disjoint_left.mp (hlens e d hed)
    ((Set.ext_iff.mp (hdiff e) y).mp ⟨hye, hyoff⟩).1
    ((Set.ext_iff.mp (hdiff d) y).mp ⟨hyd, hyoff⟩).1

omit [FiniteDimensional ℝ Ea] in
theorem section34Step_disjoint_cells
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (e₀ : Section34EdgeIndex 𝒦 𝒦')
    (hoff : ∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)})
    (hin : ∀ w, ∀ x ∈ Cp w, G w x ∈ interior (Sp e₀) → G' w x ∈ interior (Sp e₀)) :
    ∀ w w', Disjoint (Cp w) (Cp w') → Disjoint (G' w '' Cp w) (G' w' '' Cp w') := by
  have hdiff := section34Step_cell_image_diff_support hprep G' e₀ hoff hin
  have hnew : ∀ w, w ≠ (ends e₀).1 → w ≠ (ends e₀).2 →
      Disjoint (Sp e₀) (G' w '' Cp w) := by
    intro w hw₁ hw₂
    rw [(section34Step_eqOn_other_cells hprep hpack G' e₀ hoff w hw₁ hw₂).image_eq]
    exact section34_support_disjoint_other_cell hprep hpack e₀ w hw₁ hw₂
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, -, hBb, -, -, -, -, -, hcomp, -⟩ := hprep
  obtain ⟨x, hx, -⟩ := (hcomp e₀).1
  have hxa : x ∈ Cp (ends e₀).1 := hx.2
  have hxb : x ∈ Cp (ends e₀).2 := (hCp _).boundary_subset ((hBb e₀).1 hx.1)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hsep, -⟩ := hpack
  intro w w' hww'
  refine Set.disjoint_left.mpr ?_
  intro y hyw hyw'
  have hyoff : y ∉ interior (Sp e₀) := by
    by_cases hw : w = (ends e₀).1 ∨ w = (ends e₀).2
    · by_cases hw' : w' = (ends e₀).1 ∨ w' = (ends e₀).2
      · exact (Set.disjoint_left.mp hww'
          (hw.elim (fun h => h.symm ▸ hxa) (fun h => h.symm ▸ hxb))
          (hw'.elim (fun h => h.symm ▸ hxa) (fun h => h.symm ▸ hxb))).elim
      · exact fun hy => Set.disjoint_left.mp
          (hnew w' (fun h => hw' (Or.inl h)) (fun h => hw' (Or.inr h)))
          (interior_subset hy) hyw'
    · exact fun hy => Set.disjoint_left.mp
        (hnew w (fun h => hw (Or.inl h)) (fun h => hw (Or.inr h)))
        (interior_subset hy) hyw
  exact Set.disjoint_left.mp (hsep w w' hww')
    ((Set.ext_iff.mp (hdiff w) y).mp ⟨hyw, hyoff⟩).1
    ((Set.ext_iff.mp (hdiff w') y).mp ⟨hyw', hyoff⟩).1

omit [FiniteDimensional ℝ Ea] in
theorem section34Step_marker_exclusion
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (e₀ : Section34EdgeIndex 𝒦 𝒦')
    (hoff : ∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)})
    (hin : ∀ w, ∀ x ∈ Cp w, G w x ∈ interior (Sp e₀) → G' w x ∈ interior (Sp e₀)) :
    ∀ w w', w ≠ w' → Disjoint (h '' simplexBody 𝒦' w.1) (G' w' '' Cp w') := by
  have hdiff := section34Step_cell_image_diff_support hprep G' e₀ hoff hin
  obtain ⟨-, -, -, -, -, -, -, -, -, hgraph, -, -, -, -, -, -, -, -, -, -, -, hmark⟩ := hpack
  intro w w' hww'
  refine Set.disjoint_left.mpr ?_
  intro y hy hyw'
  have hyoff : y ∉ interior (Sp e₀) := fun hys =>
    Set.disjoint_left.mp (hgraph e₀) (interior_subset hys) (image_mono w.2.2.2 hy)
  exact Set.disjoint_left.mp (hmark w w' hww') hy
    ((Set.ext_iff.mp (hdiff w') y).mp ⟨hyw', hyoff⟩).1

end DifferentialGeometry.Topology.PiecewiseLinear
