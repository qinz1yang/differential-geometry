import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame

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
theorem section34Core_of_eqOn_off_support (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂)
    (hcp : ∀ w, IsPLCellOn 3 (Cp w) (CpBd w)) (hCpCc : ∀ w, Cp w ⊆ Cc w)
    (hG : ∀ w, IsPLHomeomorphInto 3 (G w) (Cp w))
    (hG' : ∀ w, IsPLHomeomorphInto 3 (G' w) (Cp w))
    (hcore : ∀ w, h '' Kcore w ⊆ interior (G w '' Cp w))
    (hdisj : ∀ w e, Disjoint (h '' Kcore w) (Sp e))
    (hoff : ∀ w, EqOn (G' w) (G w) {x ∈ Cc w | ∀ e, G w x ∉ interior (Sp e)}) :
    ∀ w, h '' Kcore w ⊆ interior (G' w '' Cp w) := by
  intro w y hy
  have h1 : y ∈ G w '' (Cp w \ CpBd w) := by
    rw [((hcp w).image_boundary_interior (hG w)).2]
    exact hcore w hy
  obtain ⟨x, hx, hxy⟩ := h1
  have hoffx : x ∈ {x ∈ Cc w | ∀ e, G w x ∉ interior (Sp e)} := by
    refine ⟨hCpCc w hx.1, fun e hmem => ?_⟩
    have hmem' : y ∈ Sp e := by rw [← hxy]; exact interior_subset hmem
    exact Set.disjoint_left.mp (hdisj w e) hy hmem'
  rw [← ((hcp w).image_boundary_interior (hG' w)).2]
  exact ⟨x, hx, (hoff w hoffx).trans hxy⟩

omit [FiniteDimensional ℝ Ea] in
theorem section34Step_eqOn_marker_and_boundary
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (e₀ : Section34EdgeIndex 𝒦 𝒦')
    (hoff : ∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)}) :
    (∀ w, EqOn (G' w) (G w) (simplexBody 𝒦' w.1)) ∧
      ∀ w, w ≠ (ends e₀).1 → w ≠ (ends e₀).2 → EqOn (G' w) (G w) (CpBd w) := by
  obtain ⟨-, -, hsubs, -, hcpcell, hbody, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hmark, hbd, -⟩ := hpack
  have hcp : ∀ w, IsPLCellOn 3 (Cp w) (CpBd w) := hcpcell
  constructor
  · intro w
    refine eqOn_of_eqOn_off_support (hoff w) ?_ ?_
    · exact ((hbody w).trans interior_subset).trans (hsubs w).2.1
    · exact (hmark w e₀).mono_right interior_subset
  · intro w hw1 hw2
    refine eqOn_of_eqOn_off_support (hoff w) ?_ ?_
    · exact ((hcp w).boundary_subset).trans (hsubs w).2.1
    · exact ((hbd e₀ w hw1 hw2).symm).mono_right interior_subset

omit [FiniteDimensional ℝ Ea] in
theorem section34Step_eqOn_other_tubes
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (e₀ : Section34EdgeIndex 𝒦 𝒦')
    (hoff : ∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)})
    (e : Section34EdgeIndex 𝒦 𝒦') (he : e ≠ e₀) :
    EqOn (G' (ends e).1) (G (ends e).1) (Sn e) ∧
      EqOn (G' (ends e).1) (G (ends e).1) (Tn e) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hTnSn, hSnCc, -⟩ := hprep
  obtain ⟨-, -, -, hSp, -, hdisj, -⟩ := hpack
  have hfix : EqOn (G' (ends e).1) (G (ends e).1) (Sn e) := by
    refine eqOn_of_eqOn_off_support (hoff (ends e).1) (hSnCc e _ (Or.inl rfl)) ?_
    rw [← (hSp e).1]
    exact (hdisj e e₀ he).mono_right interior_subset
  exact ⟨hfix, hfix.mono ((hTnSn e).1.trans interior_subset)⟩

omit [FiniteDimensional ℝ Ea] in
theorem section34Step_eqOn_other_annuli
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (e₀ : Section34EdgeIndex 𝒦 𝒦')
    (hoff : ∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)})
    (e : Section34EdgeIndex 𝒦 𝒦') (he : e ≠ e₀) :
    EqOn (G' (ends e).1) (G (ends e).1) (Aa e) ∧
      EqOn (G' (ends e).2) (G (ends e).2) (Bb e) := by
  have hTn := (section34Step_eqOn_other_tubes hprep hpack G' e₀ hoff e he).2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hSnCc, -, hAa, -, -, hBb, -⟩ := hprep
  obtain ⟨-, -, -, -, -, hdisj, -, -, hBbSp, -⟩ := hpack
  constructor
  · apply hTn.mono
    rw [(hAa e).1]
    exact inter_subset_right
  · refine eqOn_of_eqOn_off_support (hoff (ends e).2) ?_ ?_
    · exact ((hBb e).1.trans interior_subset).trans (hSnCc e _ (Or.inr rfl))
    · exact (hdisj e e₀ he).mono ((hBbSp e).1.trans interior_subset) interior_subset

omit [FiniteDimensional ℝ Ea] in
theorem section34Step_other_tube_images
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (e₀ : Section34EdgeIndex 𝒦 𝒦')
    (hoff : ∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)})
    (e : Section34EdgeIndex 𝒦 𝒦') (he : e ≠ e₀) :
    Sp e = G' (ends e).1 '' Sn e ∧ Tp e = G' (ends e).1 '' Tn e := by
  obtain ⟨hSn, hTn⟩ := section34Step_eqOn_other_tubes hprep hpack G' e₀ hoff e he
  obtain ⟨-, -, -, hSp, -⟩ := hpack
  exact ⟨(hSp e).1.trans hSn.image_eq.symm, (hSp e).2.trans hTn.image_eq.symm⟩

omit [FiniteDimensional ℝ Ea] in
theorem section34Step_other_annulus_images
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (e₀ : Section34EdgeIndex 𝒦 𝒦')
    (hoff : ∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)}) :
    ∀ e, e ≠ e₀ → G' (ends e).1 '' Aa e = G (ends e).1 '' Aa e ∧
      G' (ends e).2 '' Bb e = G (ends e).2 '' Bb e := by
  intro e he
  obtain ⟨hAa, hBb⟩ := section34Step_eqOn_other_annuli hprep hpack G' e₀ hoff e he
  exact ⟨hAa.image_eq, hBb.image_eq⟩

omit [FiniteDimensional ℝ Ea] in
theorem section34Step_cell_image_diff_support
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (e₀ : Section34EdgeIndex 𝒦 𝒦')
    (hoff : ∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)})
    (hin : ∀ w, ∀ x ∈ Cp w, G w x ∈ interior (Sp e₀) → G' w x ∈ interior (Sp e₀))
    (w : Section34VertexIndex 𝒦 𝒦') :
    G' w '' Cp w \ interior (Sp e₀) = G w '' Cp w \ interior (Sp e₀) := by
  obtain ⟨-, -, hsub, -⟩ := hprep
  apply Subset.antisymm
  · rintro y ⟨⟨x, hx, rfl⟩, hy⟩
    have hxoff : G w x ∉ interior (Sp e₀) := fun hxin => hy (hin w x hx hxin)
    exact ⟨⟨x, hx, (hoff w ⟨(hsub w).2.1 hx, hxoff⟩).symm⟩, hy⟩
  · rintro y ⟨⟨x, hx, rfl⟩, hy⟩
    exact ⟨⟨x, hx, hoff w ⟨(hsub w).2.1 hx, hy⟩⟩, hy⟩

omit [FiniteDimensional ℝ Ea] in
theorem section34Step_lens_diff_support
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (e₀ : Section34EdgeIndex 𝒦 𝒦')
    (hoff : ∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)})
    (hin : ∀ w, ∀ x ∈ Cp w, G w x ∈ interior (Sp e₀) → G' w x ∈ interior (Sp e₀))
    (e : Section34EdgeIndex 𝒦 𝒦') :
    (G' (ends e).1 '' Cp (ends e).1 ∩ G' (ends e).2 '' Cp (ends e).2) \ interior (Sp e₀) =
      (G (ends e).1 '' Cp (ends e).1 ∩ G (ends e).2 '' Cp (ends e).2) \ interior (Sp e₀) := by
  have ha := section34Step_cell_image_diff_support hprep G' e₀ hoff hin (ends e).1
  have hb := section34Step_cell_image_diff_support hprep G' e₀ hoff hin (ends e).2
  ext y
  constructor
  · rintro ⟨⟨hya, hyb⟩, hy⟩
    exact ⟨⟨((Set.ext_iff.mp ha y).mp ⟨hya, hy⟩).1,
      ((Set.ext_iff.mp hb y).mp ⟨hyb, hy⟩).1⟩, hy⟩
  · rintro ⟨⟨hya, hyb⟩, hy⟩
    exact ⟨⟨((Set.ext_iff.mp ha y).mpr ⟨hya, hy⟩).1,
      ((Set.ext_iff.mp hb y).mpr ⟨hyb, hy⟩).1⟩, hy⟩

end DifferentialGeometry.Topology.PiecewiseLinear
