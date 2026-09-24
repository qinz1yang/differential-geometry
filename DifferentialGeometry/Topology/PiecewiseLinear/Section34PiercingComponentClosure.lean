import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingComponentTrapping

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem closure_component_eq_of_local_sides
    {X : Type*} [TopologicalSpace X] {U D : Set X} (hUD : U ⊆ D) (hD : IsClosed D)
    (hdense : D ⊆ closure U)
    (hlocal : ∀ y ∈ D, ∃ V : Set X, IsOpen V ∧ y ∈ V ∧ IsPreconnected (U ∩ V))
    {x : X} (hx : x ∈ U) : closure (connectedComponentIn U x) = connectedComponentIn D x := by
  have hCsub : closure (connectedComponentIn U x) ⊆ D :=
    closure_minimal ((connectedComponentIn_subset U x).trans hUD) hD
  have hdisj : Disjoint (closure (connectedComponentIn U x))
      (closure (D \ closure (connectedComponentIn U x))) := by
    refine Set.disjoint_left.mpr ?_
    intro y hy hyout
    obtain ⟨V, hVo, hyV, hconn⟩ := hlocal y (hCsub hy)
    obtain ⟨z, hzV, hzC⟩ := mem_closure_iff.mp hy V hVo hyV
    have hzU := connectedComponentIn_subset U x hzC
    have hUV : U ∩ V ⊆ connectedComponentIn U x := by
      rw [connectedComponentIn_eq hzC]
      exact hconn.subset_connectedComponentIn ⟨hzU, hzV⟩ inter_subset_left
    obtain ⟨w, hwV, hwD, hwout⟩ := mem_closure_iff.mp hyout V hVo hyV
    exact hwout (closure_mono hUV (hVo.closure_inter ⟨hdense hwD, hwV⟩))
  apply Subset.antisymm
  · exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn hx)) hCsub
  · have hcover : connectedComponentIn D x ⊆ closure (connectedComponentIn U x) ∪
        closure (D \ closure (connectedComponentIn U x)) := by
      intro y hy
      by_cases hyC : y ∈ closure (connectedComponentIn U x)
      · exact Or.inl hyC
      · exact Or.inr (subset_closure ⟨connectedComponentIn_subset D x hy, hyC⟩)
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp isPreconnected_connectedComponentIn
      _ _ isClosed_closure isClosed_closure hcover
      (by rw [hdisj.inter_eq, inter_empty]) with h | h
    · exact h
    · exact (Set.disjoint_left.mp hdisj (subset_closure (mem_connectedComponentIn hx))
        (h (mem_connectedComponentIn (hUD hx)))).elim


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
theorem section34_second_annulus_isCompact
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (e : Section34EdgeIndex 𝒦 𝒦') : IsCompact (G (ends e).2 '' Bb e) := by
  obtain ⟨-, -, hsub, -, hCp, -, -, -, -, -, -, -, -, -, -, hBb, -⟩ := hprep
  obtain ⟨hG, -⟩ := hpack
  obtain ⟨f, -, -⟩ := (hBb e).2
  have hcompact : IsCompact (Bb e) := isCompact_iff_compactSpace.mpr f.compactSpace
  exact hcompact.image_of_continuousOn ((hG _).continuousOn.mono
    (((hBb e).1.trans (hCp _).boundary_subset).trans (hsub _).2.1))

omit [FiniteDimensional ℝ Ea] in
theorem section34_trace_free_component_eq_inside
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (e : Section34EdgeIndex 𝒦 𝒦') (y : M₂)
    (hy : y ∈ G (ends e).2 '' Bb e ∩ interior (G (ends e).1 '' Cp (ends e).1)) :
    connectedComponentIn (G (ends e).2 '' Bb e \ G (ends e).1 '' CpBd (ends e).1) y =
      connectedComponentIn
        (G (ends e).2 '' Bb e ∩ interior (G (ends e).1 '' Cp (ends e).1)) y := by
  have hside := section34_trace_free_component_side hprep hpack e y
  obtain ⟨-, -, -, -, hCp, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hG, -⟩ := hpack
  have hfront := ((hCp (ends e).1).image_boundary_interior (hG (ends e).1)).1
  have hsub : G (ends e).2 '' Bb e ∩ interior (G (ends e).1 '' Cp (ends e).1) ⊆
      G (ends e).2 '' Bb e \ G (ends e).1 '' CpBd (ends e).1 := by
    intro z hz
    refine ⟨hz.1, fun hzBd => ?_⟩
    rw [hfront] at hzBd
    exact hzBd.2 hz.2
  have hycomp := mem_connectedComponentIn (hsub hy)
  apply Subset.antisymm
  · rcases hside with hin | hout
    · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn hycomp
        (fun z hz => ⟨(connectedComponentIn_subset _ _ hz).1, hin hz⟩)
    · exact (hout hycomp (interior_subset hy.2)).elim
  · exact connectedComponentIn_mono y hsub

omit [FiniteDimensional ℝ Ea] in
theorem section34_trace_free_component_eq_outside
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (e : Section34EdgeIndex 𝒦 𝒦') (y : M₂)
    (hy : y ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) :
    connectedComponentIn (G (ends e).2 '' Bb e \ G (ends e).1 '' CpBd (ends e).1) y =
      connectedComponentIn (G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) y := by
  have hside := section34_trace_free_component_side hprep hpack e y
  obtain ⟨-, -, -, -, hCp, -⟩ := hprep
  have hsub : G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1 ⊆
      G (ends e).2 '' Bb e \ G (ends e).1 '' CpBd (ends e).1 :=
    fun z hz => ⟨hz.1, fun hzBd => hz.2 (image_mono (hCp _).boundary_subset hzBd)⟩
  have hycomp := mem_connectedComponentIn (hsub hy)
  apply Subset.antisymm
  · rcases hside with hin | hout
    · exact (hy.2 (interior_subset (hin hycomp))).elim
    · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn hycomp
        (fun z hz => ⟨(connectedComponentIn_subset _ _ hz).1, hout hz⟩)
  · exact connectedComponentIn_mono y hsub

omit [FiniteDimensional ℝ Ea] in
theorem section34_inside_component_closure_eq_of_local_sides
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (e : Section34EdgeIndex 𝒦 𝒦')
    (hdense : G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1 ⊆
      closure (G (ends e).2 '' Bb e ∩ interior (G (ends e).1 '' Cp (ends e).1)))
    (hlocal : ∀ z ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1,
      ∃ V : Set M₂, IsOpen V ∧ z ∈ V ∧
        IsPreconnected ((G (ends e).2 '' Bb e ∩ interior (G (ends e).1 '' Cp (ends e).1)) ∩ V))
    (y : M₂) (hy : y ∈ G (ends e).2 '' Bb e ∩ interior (G (ends e).1 '' Cp (ends e).1)) :
    closure (connectedComponentIn
      (G (ends e).2 '' Bb e \ G (ends e).1 '' CpBd (ends e).1) y) =
      connectedComponentIn (G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) y := by
  rw [section34_trace_free_component_eq_inside hprep hpack e y hy]
  have hBclosed := (section34_second_annulus_isCompact hprep hpack e).isClosed
  obtain ⟨-, -, -, -, hCp, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hG, -⟩ := hpack
  have hCclosed := ((hCp (ends e).1).image (hG (ends e).1)).isCompact.isClosed
  exact closure_component_eq_of_local_sides
    (U := G (ends e).2 '' Bb e ∩ interior (G (ends e).1 '' Cp (ends e).1))
    (D := G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1)
    (fun z hz => ⟨hz.1, interior_subset hz.2⟩) (hBclosed.inter hCclosed) hdense hlocal hy

end DifferentialGeometry.Topology.PiecewiseLinear
