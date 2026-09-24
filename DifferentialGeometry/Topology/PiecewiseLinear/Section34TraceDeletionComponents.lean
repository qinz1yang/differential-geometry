import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingSideConnectivity

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_inside_component_after_trace_deletion {M : Type*} [TopologicalSpace M]
    {A A' B T : Set M} (hA' : IsClosed A') (hB : IsClosed B)
    (htrace : frontier A' ∩ B ⊆ frontier A) (hfront : frontier A ∩ B ⊆ T)
    (hclosure : ∀ z ∈ B ∩ interior A,
      closure (connectedComponentIn (B ∩ interior A) z) = connectedComponentIn (B ∩ A) z)
    (hoff : ∀ z ∈ B, z ∉ T → (z ∈ A' ↔ z ∈ A))
    (hcomponent : ∃ a ∈ B ∩ A, ∀ z ∈ B ∩ A, z ∉ T →
      z ∈ connectedComponentIn (B ∩ A) a) (hne : (B ∩ A').Nonempty) :
    ∃ a ∈ B ∩ A', ∀ z ∈ B ∩ A', z ∉ T → z ∈ connectedComponentIn (B ∩ A') a := by
  by_cases hex : ∃ z ∈ B ∩ A', z ∉ T
  · obtain ⟨z, hz, hzT⟩ := hex
    obtain ⟨a, -, hc⟩ := hcomponent
    have hzA := (hoff z hz.1 hzT).mp hz.2
    have hzint : z ∈ interior A := by
      by_contra hnot
      exact hzT (hfront ⟨⟨subset_closure hzA, hnot⟩, hz.1⟩)
    have hzC := mem_connectedComponentIn (show z ∈ B ∩ interior A from ⟨hz.1, hzint⟩)
    have hCsub : connectedComponentIn (B ∩ interior A) z ⊆ A' := by
      apply IsPreconnected.subset_of_disjoint_frontier isPreconnected_connectedComponentIn
        ⟨z, hzC, hz.2⟩
      apply disjoint_left.mpr
      intro x hx hxF
      have hxS := connectedComponentIn_subset (B ∩ interior A) z hx
      exact (htrace ⟨hxF, hxS.1⟩).2 hxS.2
    have hclsub : closure (connectedComponentIn (B ∩ interior A) z) ⊆ B ∩ A' :=
      closure_minimal (fun x hx => ⟨(connectedComponentIn_subset _ _ hx).1, hCsub hx⟩)
        (hB.inter hA')
    have hnew := isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
      (subset_closure hzC) hclsub
    refine ⟨z, hz, fun w hw hwT => hnew ?_⟩
    rw [hclosure z ⟨hz.1, hzint⟩, ← connectedComponentIn_eq (hc z ⟨hz.1, hzA⟩ hzT)]
    exact hc w ⟨hw.1, (hoff w hw.1 hwT).mp hw.2⟩ hwT
  · obtain ⟨a, ha⟩ := hne
    exact ⟨a, ha, fun z hz hzT => (hex ⟨z, hz, hzT⟩).elim⟩

theorem exists_outside_component_after_trace_deletion {M : Type*} [TopologicalSpace M]
    {A A' B T : Set M} (hA : IsClosed A)
    (htrace : frontier A' ∩ B ⊆ frontier A)
    (hoff : ∀ z ∈ B, z ∉ T → (z ∈ A' ↔ z ∈ A))
    (hcomponent : ∃ a ∈ B \ A, ∀ z ∈ B \ A, z ∉ T →
      z ∈ connectedComponentIn (B \ A) a) (hne : (B \ A').Nonempty) :
    ∃ a ∈ B \ A', ∀ z ∈ B \ A', z ∉ T → z ∈ connectedComponentIn (B \ A') a := by
  by_cases hex : ∃ z ∈ B \ A', z ∉ T
  · obtain ⟨z, hz, hzT⟩ := hex
    obtain ⟨a, -, hc⟩ := hcomponent
    have hzA : z ∉ A := fun hzA => hz.2 ((hoff z hz.1 hzT).mpr hzA)
    have hzC := mem_connectedComponentIn (show z ∈ B \ A from ⟨hz.1, hzA⟩)
    have hCsub : connectedComponentIn (B \ A) z ⊆ A'ᶜ := by
      apply IsPreconnected.subset_of_disjoint_frontier isPreconnected_connectedComponentIn
        ⟨z, hzC, hz.2⟩
      rw [frontier_compl]
      apply disjoint_left.mpr
      intro x hx hxF
      have hxS := connectedComponentIn_subset (B \ A) z hx
      exact hxS.2 (hA.frontier_subset (htrace ⟨hxF, hxS.1⟩))
    have hnew := isPreconnected_connectedComponentIn.subset_connectedComponentIn hzC
      (show connectedComponentIn (B \ A) z ⊆ B \ A' from
        fun x hx => ⟨(connectedComponentIn_subset _ _ hx).1, hCsub hx⟩)
    refine ⟨z, hz, fun w hw hwT => hnew ?_⟩
    rw [← connectedComponentIn_eq (hc z ⟨hz.1, hzA⟩ hzT)]
    exact hc w ⟨hw.1, fun hwA => hw.2 ((hoff w hw.1 hwT).mpr hwA)⟩ hwT
  · obtain ⟨a, ha⟩ := hne
    exact ⟨a, ha, fun z hz hzT => (hex ⟨z, hz, hzT⟩).elim⟩

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

theorem section34_piercing_components_after_first_trace_deletion
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {A' : Set M₂} (hA' : IsClosed A')
    (htrace : frontier A' ∩ G (ends e).2 '' Bb e ⊆ G (ends e).1 '' CpBd (ends e).1)
    (hoff : ∀ z ∈ G (ends e).2 '' Bb e, z ∉ Tp e →
      (z ∈ A' ↔ z ∈ G (ends e).1 '' Cp (ends e).1))
    (hin : (G (ends e).2 '' Bb e ∩ A').Nonempty)
    (hout : (G (ends e).2 '' Bb e \ A').Nonempty) :
    (∃ a ∈ G (ends e).2 '' Bb e ∩ A', ∀ z ∈ G (ends e).2 '' Bb e ∩ A', z ∉ Tp e →
      z ∈ connectedComponentIn (G (ends e).2 '' Bb e ∩ A') a) ∧
    ∃ b ∈ G (ends e).2 '' Bb e \ A', ∀ z ∈ G (ends e).2 '' Bb e \ A', z ∉ Tp e →
      z ∈ connectedComponentIn (G (ends e).2 '' Bb e \ A') b := by
  have hB := (section34_second_annulus_isCompact hprep hpack e).isClosed
  have hclosure (z : M₂) (hz : z ∈ G (ends e).2 '' Bb e ∩
      interior (G (ends e).1 '' Cp (ends e).1)) :=
    section34_inside_component_closure_eq hprep hpack e z hz
  have hcomponent (z : M₂) (hz : z ∈ G (ends e).2 '' Bb e ∩
      interior (G (ends e).1 '' Cp (ends e).1)) :=
    section34_trace_free_component_eq_inside hprep hpack e z hz
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, -, hBb, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, hmeet, -, -, -, hG, -, -, -, hinside, houtside, -⟩ := hpack
  have hA := (hCp (ends e).1).image (hG (ends e).1)
  have hfront : frontier (G (ends e).1 '' Cp (ends e).1) ∩ G (ends e).2 '' Bb e ⊆ Tp e := by
    rw [← hA.boundary_eq_frontier]
    exact fun _ hx => interior_subset (hmeet e ⟨hx.1, image_mono (hBb e).1 hx.2⟩).2
  rw [hA.boundary_eq_frontier] at htrace
  refine ⟨exists_inside_component_after_trace_deletion hA' hB htrace hfront ?_ hoff
      (hinside e) hin,
    exists_outside_component_after_trace_deletion hA.isCompact.isClosed htrace hoff
      (houtside e) hout⟩
  intro z hz
  rw [← hcomponent z hz]
  exact hclosure z hz

end DifferentialGeometry.Topology.PiecewiseLinear
