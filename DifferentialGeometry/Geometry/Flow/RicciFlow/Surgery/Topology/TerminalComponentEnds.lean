import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.Terminal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarSublevel
import DifferentialGeometry.Geometry.Neck.SmoothSavedEnd

noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Topology (SmoothTwoSidedCollar symmetricOpenInterval)
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OneStepIncoming
universe u v

theorem exists_smooth_saved_end_decomposition_on_noncompact_component :
    ∃ η : ℝ, 0 < η ∧ ∀ (D : OneStepIncoming.{u}) (δ ε A C Λ : ℝ),
      δ ≤ η → 26000 * δ ≤ ε → 0 ≤ A → 1 ≤ C →
      ∀ y : D.slab.terminalRegularOpen, metricScalarAt D.terminal.metric y ≤ A →
        ¬ IsCompact (connectedComponent y) →
      let U := connectedComponentOpen (I := I3) y
      let g := D.terminal.metric.restrictOpen U
      ∀ (ι : Type v) [Finite ι] (point : ι → U) (neck : ∀ i, SpatialNeck g δ (point i))
        (level : ι → ℝ) (W : Set U),
        IsCompact W → closure (interior W) = W →
        {x : U | metricScalarAt g x ≤ C * A} ⊆ interior W →
        {x : U | metricScalarAt g x ≤ ((D.parameters.protectedRadius D.endTime)^2)⁻¹}
          ⊆ interior W →
        (∀ x ∈ W, metricScalarAt g x ≤ Λ * A) →
        (∀ i, |level i| ≤ 4) →
        Pairwise (fun i j => Disjoint (range (fun z : Sphere 2 => (neck i).map (z, level i)))
          (range (fun z : Sphere 2 => (neck j).map (z, level j)))) →
        frontier W = ⋃ i, range (fun z : Sphere 2 => (neck i).map (z, level i)) →
        (∀ V : Set U, W ⊆ V → ∀ x : U, x ∉ interior V →
          C * A < metricScalarAt g x ∧
          ∀ (p : U) (nk : SpatialNeck g δ p) (z : Sphere 2) (level : ℝ),
            |level| ≤ 4 → nk.map (z, level) = x →
            Nonempty (SpatialNeck g δ x) ∨
            ∃ K : CompactDomain U, Nonempty (CapCore K.carrier) ∧
              nk.map '' (univ ×ˢ Icc (-4 : ℝ) 4) ⊆ interior K.carrier ∧
              (∀ w ∈ K.carrier, A < metricScalarAt g w ∧
                metricScalarAt g x / C < metricScalarAt g w ∧
                metricScalarAt g w < C * metricScalarAt g x)) →
        ∃ (K : Set U) (m : ℕ) (origin : Fin m → ι) (Θ : Fin m → Cylinder → U)
          (charts : ChartedSpace (EuclideanHalfSpace 3) K)
          (collar : ∀ i, SmoothTwoSidedCollar I2 I3 (fun z => Θ i (z, 0))),
          W ⊆ K ∧ IsCompact K ∧ IsConnected K ∧ closure (interior K) = K ∧ 0 < m ∧
          Function.Injective origin ∧ frontier K ⊆ frontier W ∧
          (∀ i z, Θ i (z, 0) = (neck (origin i)).map (z, level (origin i))) ∧
          {x : U | metricScalarAt g x ≤ A} ⊆ interior K ∧
          {x : U | metricScalarAt g x ≤ ((D.parameters.protectedRadius D.endTime)^2)⁻¹}
            ⊆ interior K ∧
          (∀ i, ContMDiffOn IC I3 ∞ (Θ i) (univ ×ˢ Ici (0 : ℝ)) ∧
            InjOn (Θ i) (univ ×ˢ Ici (0 : ℝ)) ∧
            IsProperMap (fun z : Sphere 2 × ℝ≥0 => Θ i (z.1, z.2.val)) ∧
            (let V : TopologicalSpace.Opens Cylinder :=
              ⟨univ ×ˢ Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
             IsSmoothEmbedding IC I3 ∞ (fun z : V => Θ i z)) ∧
            Θ i '' (univ ×ˢ Ici (0 : ℝ)) ∩ K = range (fun z => Θ i (z, 0)) ∧
            (∀ B : ℝ, ∃ T : ℝ≥0, ∀ (z : Sphere 2) (t : ℝ≥0),
              T ≤ t → B < metricScalarAt g (Θ i (z, t.val))) ∧
            (∀ z t, 0 ≤ t → A < metricScalarAt g (Θ i (z, t))) ∧
            (∀ z, metricScalarAt g (Θ i (z, 0)) ≤ Λ * A) ∧
            ∀ x, x ∈ Θ i '' (univ ×ˢ Ici (0 : ℝ)) →
              ∃ (α : ℝ) (k : ℕ) (N : NormalizedNeck g α k),
                N.center = x ∧ α ≤ ε ∧ ⌊ε⁻¹⌋₊ + 1 ≤ k) ∧
          Pairwise (fun i j => Disjoint (Θ i '' (univ ×ˢ Ici (0 : ℝ)))
            (Θ j '' (univ ×ˢ Ici (0 : ℝ)))) ∧
          frontier K = ⋃ i, range (fun z => Θ i (z, 0)) ∧
          K ∪ (⋃ i, Θ i '' (univ ×ˢ Ici (0 : ℝ))) = univ ∧
          (let _ := charts
           IsManifold (𝓡∂ 3) ∞ K ∧
             IsSmoothEmbedding (𝓡∂ 3) I3 ∞ (Subtype.val : K → U) ∧
             (∀ x : K, (𝓡∂ 3).IsBoundaryPoint x ↔ x.val ∈ frontier K) ∧
             (∀ x : K, (𝓡∂ 3).IsInteriorPoint x ↔ x.val ∈ interior K) ∧
             Subtype.val '' ((𝓡∂ 3).boundary K) = frontier K ∧
             Subtype.val '' ((𝓡∂ 3).interior K) = interior K) ∧
          ∀ i, (collar i).radius < 1 ∧
            (∀ z : Sphere 2 × symmetricOpenInterval (collar i).radius,
              (collar i).toFun z ∈ K ↔ z.2.val ≤ 0) ∧
            (∀ z : Sphere 2 × symmetricOpenInterval (collar i).radius,
              z.2.val < 0 → (collar i).toFun z ∈ interior K) ∧
            ∀ z : Sphere 2 × symmetricOpenInterval (collar i).radius,
              0 ≤ z.2.val → (collar i).toFun z = Θ i (z.1, z.2.val) := by
  obtain ⟨η, hη, hproduce⟩ :=
    exists_spatial_neck_smooth_saved_end_decomposition_covering_scalar_sublevel_tolerance.{u, v}
  refine ⟨η, hη, ?_⟩
  intro D δ ε A C Λ hδη hδε hA hC y hy hnoncompact U g ι _ point neck level W
    hW hreg hlow hprotected hupper hlevel hpair hfront hexterior
  let _ : ConnectedSpace U := connectedComponentOpen_connectedSpace (I := I3) y
  let _ : NoncompactSpace U :=
    ⟨fun hcompact => hnoncompact (isCompact_iff_isCompact_univ.mpr hcompact)⟩
  have hclosed : IsClosed (U : Set D.slab.terminalRegularOpen) := isClosed_connectedComponent
  have hscalar (B : ℝ) : IsCompact {x : U | metricScalarAt g x ≤ B} := by
    dsimp only [g]
    simp only [DifferentialGeometry.CheegerGromovCompactness.metricScalarAt_restrictOpen]
    change IsCompact ((Subtype.val : U → D.slab.terminalRegularOpen) ⁻¹'
      {x : D.slab.terminalRegularOpen | metricScalarAt D.terminal.metric x ≤ B})
    exact hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage (D.terminal.isCompact_scalar_sublevel B)
  have hAle : A ≤ C * A := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hA
  have hlowA : {x : U | metricScalarAt g x ≤ A} ⊆ interior W :=
    fun x hx => hlow (hx.trans hAle)
  have hlowne : {x : U | metricScalarAt g x ≤ A}.Nonempty := by
    refine ⟨⟨y, mem_connectedComponent⟩, ?_⟩
    change metricScalarAt (D.terminal.metric.restrictOpen U) ⟨y, mem_connectedComponent⟩ ≤ A
    simpa only [DifferentialGeometry.CheegerGromovCompactness.metricScalarAt_restrictOpen] using hy
  have hmodels (p : U) (nk : SpatialNeck g δ p) (s : ℝ) (hs : |s| ≤ 4)
      (hout : nk.map (nk.center, s) ∉ interior W) :
      Nonempty (SpatialNeck g δ (nk.map (nk.center, s))) ∨
      ∃ V : CompactDomain U, Nonempty (CapCore V.carrier) ∧
        range (fun z : Sphere 2 => nk.map (z, s)) ⊆ interior V.carrier ∧
        ∀ a ∈ V.carrier, A < metricScalarAt g a := by
    rcases (hexterior W subset_rfl _ hout).2 p nk nk.center s hs rfl with hn | hc
    · exact Or.inl hn
    · obtain ⟨V, hcap, hinside, hbounds⟩ := hc
      refine Or.inr ⟨V, hcap, ?_, fun a ha => (hbounds a ha).1⟩
      rintro x ⟨z, rfl⟩
      exact hinside ⟨(z, s), ⟨mem_univ _, abs_le.mp hs⟩, rfl⟩
  obtain ⟨K, m, origin, Θ, charts, collar, hWK, hK, hKconn, hKreg, hm, horigin,
    hfrontW, hzero, hends, hdisjoint, hfrontK, hcover, hcharts, hcollar⟩ :=
    hproduce δ hδη U g W hW hreg ι point neck level hlevel hpair hfront A hlowA hlowne
      hmodels hscalar
  refine ⟨K, m, origin, Θ, charts, collar, hWK, hK, hKconn, hKreg, hm, horigin,
    hfrontW, hzero, hlowA.trans (interior_mono hWK),
    hprotected.trans (interior_mono hWK), ?_, hdisjoint, hfrontK, hcover, hcharts, ?_⟩
  · intro i
    obtain ⟨hsm, hinj, hproper, hembed, hinter, hdiverge, _⟩ := hends i
    refine ⟨hsm, hinj, hproper, hembed, hinter, hdiverge, ?_, ?_, ?_⟩
    · intro z t ht
      apply lt_of_not_ge
      intro hs
      have hi : Θ i (z, t) ∈ interior K := interior_mono hWK (hlowA hs)
      have hb : Θ i (z, t) ∈ range (fun z => Θ i (z, 0)) := by
        rw [← hinter]
        exact ⟨⟨(z, t), ⟨mem_univ _, ht⟩, rfl⟩, interior_subset hi⟩
      have hf : Θ i (z, t) ∈ frontier K := by
        rw [hfrontK]
        exact mem_iUnion.mpr ⟨i, hb⟩
      exact hf.2 hi
    · intro z
      apply hupper
      apply hW.isClosed.frontier_subset
      apply hfrontW
      rw [hfrontK]
      exact mem_iUnion.mpr ⟨i, mem_range_self z⟩
    · exact (hcollar i).2.2.2.2.2 ε hδε
  · intro i
    obtain ⟨hr, hside, hnegative, hpositive, _, _⟩ := hcollar i
    exact ⟨hr, hside, hnegative, hpositive⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OneStepIncoming
