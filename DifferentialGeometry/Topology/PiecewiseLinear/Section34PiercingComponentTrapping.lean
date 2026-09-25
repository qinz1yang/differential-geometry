import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem isCompact_of_isTopologicalSolidTorus {M : Type*} [TopologicalSpace M]
    {S : Set M} (hS : IsTopologicalSolidTorus S) : IsCompact S := by
  obtain ⟨f⟩ := hS
  exact isCompact_iff_compactSpace.mpr f.symm.compactSpace

private theorem component_subset_of_outside_component {X : Type*} [TopologicalSpace X]
    {D T : Set X} {a y : X} (hout : ∀ z ∈ D, z ∉ T → z ∈ connectedComponentIn D a)
    (hyD : y ∈ D) (hy : y ∉ connectedComponentIn D a) : connectedComponentIn D y ⊆ T := by
  intro z hz
  by_contra hzT
  have hzA := hout z (connectedComponentIn_subset D y hz) hzT
  have heq := (connectedComponentIn_eq hz).trans (connectedComponentIn_eq hzA).symm
  exact hy (heq ▸ mem_connectedComponentIn hyD)

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
theorem section34_inner_tube_isCompact
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (e : Section34EdgeIndex 𝒦 𝒦') : IsCompact (Tp e) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, htor, hSnCc, -⟩ := hprep
  obtain ⟨hG, -, -, hSp, -⟩ := hpack
  rw [(hSp e).2]
  exact (isCompact_of_isTopologicalSolidTorus (htor e).2.2.1).image_of_continuousOn
    ((hG _).continuousOn.mono (((htor e).1.trans interior_subset).trans
      (hSnCc e _ (Or.inl rfl))))

omit [FiniteDimensional ℝ Ea] in
theorem section34_outer_tube_isCompact
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (e : Section34EdgeIndex 𝒦 𝒦') : IsCompact (Sp e) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, htor, hSnCc, -⟩ := hprep
  obtain ⟨hG, -, -, hSp, -⟩ := hpack
  rw [(hSp e).1]
  exact (isCompact_of_isTopologicalSolidTorus (htor e).2.1).image_of_continuousOn
    ((hG _).continuousOn.mono (hSnCc e _ (Or.inl rfl)))

omit [FiniteDimensional ℝ Ea] in
theorem section34_piercing_components_trapped
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (e : Section34EdgeIndex 𝒦 𝒦') :
    ∃ a ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1,
      ∃ b ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1,
      (∀ y ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1,
        y ∉ connectedComponentIn (G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) a →
        closure (connectedComponentIn
          (G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) y) ⊆ Tp e) ∧
      ∀ y ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1,
        y ∉ connectedComponentIn (G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) b →
        closure (connectedComponentIn
          (G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) y) ⊆ Tp e := by
  have hclosed := (section34_inner_tube_isCompact hprep hpack e).isClosed
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hin, hout, -⟩ := hpack
  obtain ⟨a, ha, hsideA⟩ := hin e
  obtain ⟨b, hb, hsideB⟩ := hout e
  exact ⟨a, ha, b, hb,
    fun y hy hya => closure_minimal (component_subset_of_outside_component hsideA hy hya) hclosed,
    fun y hy hyb => closure_minimal (component_subset_of_outside_component hsideB hy hyb) hclosed⟩

omit [FiniteDimensional ℝ Ea] in
theorem section34_trace_free_component_side
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (e : Section34EdgeIndex 𝒦 𝒦') (y : M₂) :
    connectedComponentIn (G (ends e).2 '' Bb e \ G (ends e).1 '' CpBd (ends e).1) y ⊆
        interior (G (ends e).1 '' Cp (ends e).1) ∨
      connectedComponentIn (G (ends e).2 '' Bb e \ G (ends e).1 '' CpBd (ends e).1) y ⊆
        (G (ends e).1 '' Cp (ends e).1)ᶜ := by
  obtain ⟨-, -, -, -, hCp, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hG, -⟩ := hpack
  have hclosed := ((hCp (ends e).1).image (hG (ends e).1)).isCompact.isClosed
  have hfront := ((hCp (ends e).1).image_boundary_interior (hG (ends e).1)).1
  apply isPreconnected_connectedComponentIn.subset_or_subset
    isOpen_interior hclosed.isOpen_compl (disjoint_compl_right.mono_left interior_subset)
  intro z hz
  have hzD := connectedComponentIn_subset _ _ hz
  by_cases hzint : z ∈ interior (G (ends e).1 '' Cp (ends e).1)
  · exact Or.inl hzint
  · refine Or.inr fun hzC => ?_
    apply hzD.2
    rw [hfront]
    exact ⟨subset_closure hzC, hzint⟩

omit [FiniteDimensional ℝ Ea] in
theorem section34_trace_free_components_trapped
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (e : Section34EdgeIndex 𝒦 𝒦') :
    ∃ a ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1,
      ∃ b ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1,
      ∀ y ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' CpBd (ends e).1,
        y ∉ connectedComponentIn (G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) a →
        y ∉ connectedComponentIn (G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) b →
        closure (connectedComponentIn
          (G (ends e).2 '' Bb e \ G (ends e).1 '' CpBd (ends e).1) y) ⊆ Tp e := by
  obtain ⟨a, ha, b, hb, hinside, houtside⟩ := section34_piercing_components_trapped hprep hpack e
  refine ⟨a, ha, b, hb, fun y hy hya hyb => ?_⟩
  have hycomp := mem_connectedComponentIn hy
  rcases section34_trace_free_component_side hprep hpack e y with hin | hout
  · have hsub : connectedComponentIn
        (G (ends e).2 '' Bb e \ G (ends e).1 '' CpBd (ends e).1) y ⊆
          G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1 :=
      fun z hz => ⟨(connectedComponentIn_subset _ _ hz).1, interior_subset (hin hz)⟩
    exact (closure_mono (isPreconnected_connectedComponentIn.subset_connectedComponentIn
      hycomp hsub)).trans (hinside y (hsub hycomp) hya)
  · have hsub : connectedComponentIn
        (G (ends e).2 '' Bb e \ G (ends e).1 '' CpBd (ends e).1) y ⊆
          G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1 :=
      fun z hz => ⟨(connectedComponentIn_subset _ _ hz).1, hout hz⟩
    exact (closure_mono (isPreconnected_connectedComponentIn.subset_connectedComponentIn
      hycomp hsub)).trans (houtside y (hsub hycomp) hyb)

end DifferentialGeometry.Topology.PiecewiseLinear
