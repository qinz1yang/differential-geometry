import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame
import DifferentialGeometry.Topology.PiecewiseLinear.CompactEmbeddingApproximation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem Moise341.exists_chart_local_cell_approximations (h341 : Moise341)
    {M₁ M₂ ι : Type*} [TopologicalSpace M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [MetricSpace M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] [HasGroupoid M₂ (plGroupoid 3)]
    {U : Set M₁} {h : M₁ → M₂} (hh : Topology.IsEmbedding (U.domRestrict h))
    (C B : ι → Set M₁) (hC : ∀ i, IsPLCellOn 3 (C i) (B i))
    (hCU : ∀ i, C i ⊆ U)
    (hchart : ∀ i, ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, h '' C i ⊆ c.source)
    (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i) :
    ∃ G : ι → M₁ → M₂, (∀ i, IsPLHomeomorphInto 3 (G i) (C i)) ∧
      ∀ i, ∀ x ∈ C i, dist (G i x) (h x) < δ i := by
  classical
  have hcontU : ContinuousOn h U :=
    continuousOn_iff_continuous_domRestrict.mpr hh.continuous
  have hinjU : InjOn h U := by
    intro x hx y hy hxy
    have hxy' : U.domRestrict h ⟨x, hx⟩ = U.domRestrict h ⟨y, hy⟩ := hxy
    exact congrArg Subtype.val (hh.injective hxy')
  have key : ∀ w : ι, ∃ F : M₁ → M₂,
      IsPLHomeomorphInto 3 F (C w) ∧ ∀ x ∈ C w, dist (F x) (h x) < δ w := by
    intro w
    obtain ⟨P, r, u, hr, hu, hCeq, -⟩ := hC w
    obtain ⟨c, hc, hcsrc⟩ := hchart w
    have hPball : IsPLBall 3 P := ⟨r, hr⟩
    have hmem : ∀ x ∈ P, u x ∈ C w := by
      intro x hx
      rw [hCeq]
      exact ⟨x, hx, rfl⟩
    have hback : ∀ y ∈ C w, ∃ x ∈ P, u x = y := by
      intro y hy
      rw [hCeq] at hy
      exact hy
    have huP : MapsTo u P U := fun x hx => hCU w (hmem x hx)
    have hcont : ContinuousOn (h ∘ u) P := hcontU.comp hu.continuousOn huP
    have hinj : InjOn (h ∘ u) P := hinjU.comp hu.injOn huP
    have hmap : MapsTo (h ∘ u) P c.source := fun x hx => hcsrc ⟨u x, hmem x hx, rfl⟩
    obtain ⟨f, hf, -, hfd⟩ :=
      h341.exists_isPLHomeomorphInto_dist_lt_of_mapsTo_chart hPball hcont hinj c hc hmap
        (τ := fun _ => δ w) continuousOn_const fun _ _ => hδ w
    refine ⟨f ∘ Function.invFunOn u P, ?_, ?_⟩
    · rw [hCeq]
      exact (exists_isPLHomeomorphInto_of_isPLHomeomorphOn hu hf
        hPball.isPolyhedron.isPLHomeomorphOn_id).1
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := hback x hx
      have hzz : Function.invFunOn u P (u z) = z := hu.injOn.leftInvOn_invFunOn hz
      have hd := hfd z hz
      simp only [Function.comp_apply, hzz] at hd ⊢
      exact hd
  choose G hG hGd using key
  exact ⟨G, hG, hGd⟩

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
theorem Moise341.exists_section34VertexApproximation (h341 : Moise341)
    [HasGroupoid M₂ (plGroupoid 3)] (hh : Topology.IsEmbedding (U.domRestrict h))
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε) :
    ∃ G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂,
      (∀ w, IsPLHomeomorphInto 3 (G w) (Cc w)) ∧
        ∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < ε w := by
  obtain ⟨hε, hcc, hsub, hchart, -⟩ := hprep
  exact h341.exists_chart_local_cell_approximations hh Cc CcBd hcc
    (fun w => (hsub w).2.2) hchart ε hε

end DifferentialGeometry.Topology.PiecewiseLinear
