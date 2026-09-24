import DifferentialGeometry.Geometry.Neck.SpatialCapEnd
import DifferentialGeometry.Topology.Manifold.CylinderCollar.CoreAtlas

noncomputable section
open Set Manifold
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v

private theorem exists_smooth_saved_end_charts
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I3 M) (eps : ℝ) (K : Set M) (m : ℕ)
    (Θ : Fin m → Cylinder → M) (hKreg : closure (interior K) = K)
    (hends : (∀ i, ContMDiffOn IC I3 ∞ (Θ i) (univ ×ˢ Ici (0 : ℝ)) ∧
              InjOn (Θ i) (univ ×ˢ Ici (0 : ℝ)) ∧
              IsProperMap (fun z : Sphere 2 × ℝ≥0 => Θ i (z.1, z.2.val)) ∧
              (let U : TopologicalSpace.Opens Cylinder :=
                ⟨univ ×ˢ Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
               IsSmoothEmbedding IC I3 ∞ (fun z : U => Θ i z)) ∧
              Θ i '' (univ ×ˢ Ici (0 : ℝ)) ∩ K = range (fun z => Θ i (z, 0)) ∧
              (∀ B : ℝ, ∃ T : ℝ≥0, ∀ (z : Sphere 2) (t : ℝ≥0),
                T ≤ t → B < Geometry.Curvature.metricScalarAt g (Θ i (z, t.val))) ∧
              ∃ (p : M) (nk : SpatialNeck g eps p)
                (P : PartialDiffeomorph IC I3 Cylinder M ∞),
                p ∈ range (fun z => Θ i (z, 0)) ∧
                univ ×ˢ Icc (0 : ℝ) 1 ⊆ P.source ∧
                (∀ z t, t ∈ Icc (0 : ℝ) 1 → Θ i (z, t) = P (z, t)) ∧
                P '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆ nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹)))
    (hdisjoint : Pairwise (fun i j => Disjoint (Θ i '' (univ ×ˢ Ici (0 : ℝ)))
      (Θ j '' (univ ×ˢ Ici (0 : ℝ)))))
    (hfrontK : frontier K = ⋃ i, range (fun z => Θ i (z, 0))) :
    ∃ (charts : ChartedSpace (EuclideanHalfSpace 3) K)
      (collar : ∀ i, DifferentialGeometry.Topology.SmoothTwoSidedCollar I2 I3
        (fun z => Θ i (z, 0))),
      (∀ i, ContMDiffOn IC I3 ∞ (Θ i) (univ ×ˢ Ici (0 : ℝ)) ∧
              InjOn (Θ i) (univ ×ˢ Ici (0 : ℝ)) ∧
              IsProperMap (fun z : Sphere 2 × ℝ≥0 => Θ i (z.1, z.2.val)) ∧
              (let U : TopologicalSpace.Opens Cylinder :=
                ⟨univ ×ˢ Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
               IsSmoothEmbedding IC I3 ∞ (fun z : U => Θ i z)) ∧
              Θ i '' (univ ×ˢ Ici (0 : ℝ)) ∩ K = range (fun z => Θ i (z, 0)) ∧
              (∀ B : ℝ, ∃ T : ℝ≥0, ∀ (z : Sphere 2) (t : ℝ≥0),
                T ≤ t → B < Geometry.Curvature.metricScalarAt g (Θ i (z, t.val))) ∧
              ∃ (p : M) (nk : SpatialNeck g eps p)
                (P : PartialDiffeomorph IC I3 Cylinder M ∞),
                p ∈ range (fun z => Θ i (z, 0)) ∧
                univ ×ˢ Icc (0 : ℝ) 1 ⊆ P.source ∧
                (∀ z t, t ∈ Icc (0 : ℝ) 1 → Θ i (z, t) = P (z, t)) ∧
                P '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆ nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ∧
                (∀ z t, t ∈ Icc (-(collar i).radius) (collar i).radius → (z, t) ∈ P.source) ∧
                ∀ z : Sphere 2 ×
                    DifferentialGeometry.Topology.symmetricOpenInterval (collar i).radius,
                  (collar i).toFun z = P (z.1, z.2.val)) ∧
      (let _ := charts; IsManifold (𝓡∂ 3) ∞ K ∧
               IsSmoothEmbedding (𝓡∂ 3) I3 ∞ (Subtype.val : K → M) ∧
               (∀ x : K, (𝓡∂ 3).IsBoundaryPoint x ↔ x.val ∈ frontier K) ∧
               (∀ x : K, (𝓡∂ 3).IsInteriorPoint x ↔ x.val ∈ interior K) ∧
               Subtype.val '' ((𝓡∂ 3).boundary K) = frontier K ∧
               Subtype.val '' ((𝓡∂ 3).interior K) = interior K) ∧
            ∀ i, (collar i).radius < 1 ∧
              (∀ z : Sphere 2 ×
                  DifferentialGeometry.Topology.symmetricOpenInterval (collar i).radius,
                (collar i).toFun z ∈ K ↔ z.2.val ≤ 0) ∧
              (∀ z : Sphere 2 ×
                  DifferentialGeometry.Topology.symmetricOpenInterval (collar i).radius,
                z.2.val < 0 → (collar i).toFun z ∈ interior K) ∧
              ∀ z : Sphere 2 ×
                  DifferentialGeometry.Topology.symmetricOpenInterval (collar i).radius,
                0 ≤ z.2.val → (collar i).toFun z = Θ i (z.1, z.2.val) := by
  have hfirst (i : Fin m) := (hends i).2.2.2.2.2.2
  choose center neck₀ P hcenter hsource hfirst hcontrolled using hfirst
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))
  obtain ⟨charts, collar, hcharts, hcollar⟩ :=
    DifferentialGeometry.Topology.exists_isManifold_of_finite_half_cylinders (n := 2)
      Θ P hsource hfirst hdisjoint hKreg hfrontK (fun i => (hends i).2.2.2.2.1)
  refine ⟨charts, collar, ?_, hcharts, ?_⟩
  · intro i
    obtain ⟨hsm, hinj, hproper, hembed, hinter, hdiverge, _⟩ := hends i
    exact ⟨hsm, hinj, hproper, hembed, hinter, hdiverge, center i, neck₀ i, P i,
      hcenter i, hsource i, hfirst i, hcontrolled i, (hcollar i).2.1, (hcollar i).2.2.1⟩
  intro i
  obtain ⟨hr, _, _, hside, hnegative, hpositive⟩ := hcollar i
  exact ⟨hr, hside, hnegative, hpositive⟩


theorem exists_spatial_neck_smooth_saved_end_decomposition_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M] [PreconnectedSpace M] [NoncompactSpace M]
          (g : SmoothRiemannianMetric I3 M) (W : Set M),
          IsCompact W → W.Nonempty → closure (interior W) = W →
          ∀ (ι : Type v) [Finite ι] (point : ι → M) (neck : ∀ i, SpatialNeck g eps (point i))
          (level : ι → ℝ), (∀ i, |level i| ≤ 4) →
          Pairwise (fun i j => Disjoint (range (fun q => (neck i).map (q, level i)))
            (range (fun q => (neck j).map (q, level j)))) →
          frontier W = ⋃ i, range (fun q => (neck i).map (q, level i)) →
          (∀ x : M, x ∉ interior W → Nonempty (SpatialNeck g eps x)) →
          (∀ B : ℝ, IsCompact {x : M | Geometry.Curvature.metricScalarAt g x ≤ B}) →
          ∃ (K : Set M) (m : ℕ) (origin : Fin m → ι) (Θ : Fin m → Cylinder → M)
            (charts : ChartedSpace (EuclideanHalfSpace 3) K)
            (collar : ∀ i, DifferentialGeometry.Topology.SmoothTwoSidedCollar I2 I3
              (fun z => Θ i (z, 0))),
            W ⊆ K ∧ IsCompact K ∧ IsConnected K ∧ closure (interior K) = K ∧ 0 < m ∧
            Function.Injective origin ∧ frontier K ⊆ frontier W ∧
            (∀ i z, Θ i (z, 0) = (neck (origin i)).map (z, level (origin i))) ∧
            (∀ i, ContMDiffOn IC I3 ∞ (Θ i) (univ ×ˢ Ici (0 : ℝ)) ∧
              InjOn (Θ i) (univ ×ˢ Ici (0 : ℝ)) ∧
              IsProperMap (fun z : Sphere 2 × ℝ≥0 => Θ i (z.1, z.2.val)) ∧
              (let U : TopologicalSpace.Opens Cylinder :=
                ⟨univ ×ˢ Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
               IsSmoothEmbedding IC I3 ∞ (fun z : U => Θ i z)) ∧
              Θ i '' (univ ×ˢ Ici (0 : ℝ)) ∩ K = range (fun z => Θ i (z, 0)) ∧
              (∀ B : ℝ, ∃ T : ℝ≥0, ∀ (z : Sphere 2) (t : ℝ≥0),
                T ≤ t → B < Geometry.Curvature.metricScalarAt g (Θ i (z, t.val))) ∧
              ∃ (p : M) (nk : SpatialNeck g eps p)
                (P : PartialDiffeomorph IC I3 Cylinder M ∞),
                p ∈ range (fun z => Θ i (z, 0)) ∧
                univ ×ˢ Icc (0 : ℝ) 1 ⊆ P.source ∧
                (∀ z t, t ∈ Icc (0 : ℝ) 1 → Θ i (z, t) = P (z, t)) ∧
                P '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆ nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ∧
                (∀ z t, t ∈ Icc (-(collar i).radius) (collar i).radius → (z, t) ∈ P.source) ∧
                ∀ z : Sphere 2 ×
                    DifferentialGeometry.Topology.symmetricOpenInterval (collar i).radius,
                  (collar i).toFun z = P (z.1, z.2.val)) ∧
            Pairwise (fun i j => Disjoint (Θ i '' (univ ×ˢ Ici (0 : ℝ)))
              (Θ j '' (univ ×ˢ Ici (0 : ℝ)))) ∧
            frontier K = ⋃ i, range (fun z => Θ i (z, 0)) ∧
            K ∪ (⋃ i, Θ i '' (univ ×ˢ Ici (0 : ℝ))) = univ ∧
            (let _ := charts
             IsManifold (𝓡∂ 3) ∞ K ∧
               IsSmoothEmbedding (𝓡∂ 3) I3 ∞ (Subtype.val : K → M) ∧
               (∀ x : K, (𝓡∂ 3).IsBoundaryPoint x ↔ x.val ∈ frontier K) ∧
               (∀ x : K, (𝓡∂ 3).IsInteriorPoint x ↔ x.val ∈ interior K) ∧
               Subtype.val '' ((𝓡∂ 3).boundary K) = frontier K ∧
               Subtype.val '' ((𝓡∂ 3).interior K) = interior K) ∧
            ∀ i, (collar i).radius < 1 ∧
              (∀ z : Sphere 2 ×
                  DifferentialGeometry.Topology.symmetricOpenInterval (collar i).radius,
                (collar i).toFun z ∈ K ↔ z.2.val ≤ 0) ∧
              (∀ z : Sphere 2 ×
                  DifferentialGeometry.Topology.symmetricOpenInterval (collar i).radius,
                z.2.val < 0 → (collar i).toFun z ∈ interior K) ∧
              ∀ z : Sphere 2 ×
                  DifferentialGeometry.Topology.symmetricOpenInterval (collar i).radius,
                0 ≤ z.2.val → (collar i).toFun z = Θ i (z.1, z.2.val) := by
  obtain ⟨eta, heta, hproduce⟩ := exists_spatial_neck_saved_end_decomposition_tolerance.{u, v}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ _ _ g W hW hne hreg ι _ point neck level hlevel hpair
    hfront hneck hscalar
  obtain ⟨K, m, origin, Θ, hWK, hK, hKconn, hKreg, hm, horigin, hfrontW, hzero,
    hends, hdisjoint, hfrontK, hcover⟩ :=
    hproduce eps heps M g W hW hne hreg ι point neck level hlevel hpair hfront hneck hscalar
  obtain ⟨charts, collar, hends', hcharts, hcollar⟩ :=
    exists_smooth_saved_end_charts g eps K m Θ hKreg hends hdisjoint hfrontK
  exact ⟨K, m, origin, Θ, charts, collar, hWK, hK, hKconn, hKreg, hm, horigin,
    hfrontW, hzero, hends', hdisjoint, hfrontK, hcover, hcharts, hcollar⟩

open DifferentialGeometry.Geometry.Curvature in
theorem exists_spatial_neck_smooth_saved_end_decomposition_of_neck_or_cap_core_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M] [PreconnectedSpace M] [NoncompactSpace M]
          (g : SmoothRiemannianMetric I3 M) (W : Set M),
          IsCompact W → W.Nonempty → closure (interior W) = W →
          ∀ (ι : Type v) [Finite ι] (point : ι → M) (neck : ∀ i, SpatialNeck g eps (point i))
          (level : ι → ℝ), (∀ i, |level i| ≤ 4) →
          Pairwise (fun i j => Disjoint (range (fun q => (neck i).map (q, level i)))
            (range (fun q => (neck j).map (q, level j)))) →
          frontier W = ⋃ i, range (fun q => (neck i).map (q, level i)) →
          ∀ A : ℝ,
          (∀ x ∈ interior W, ∃ a ∈ connectedComponentIn (interior W) x,
            metricScalarAt g a ≤ A) →
          (∀ (p : M) (nk : SpatialNeck g eps p) (level : ℝ), |level| ≤ 4 →
            nk.map (nk.center, level) ∉ interior W →
            Nonempty (SpatialNeck g eps (nk.map (nk.center, level))) ∨
            ∃ U : CompactDomain M, Nonempty (CapCore U.carrier) ∧
              range (fun z : Sphere 2 => nk.map (z, level)) ⊆ interior U.carrier ∧
              ∀ a ∈ U.carrier, A < metricScalarAt g a) →
          (∀ B : ℝ, IsCompact {x : M | metricScalarAt g x ≤ B}) →
          ∃ (K : Set M) (m : ℕ) (origin : Fin m → ι) (Θ : Fin m → Cylinder → M)
            (charts : ChartedSpace (EuclideanHalfSpace 3) K)
            (collar : ∀ i, DifferentialGeometry.Topology.SmoothTwoSidedCollar I2 I3
              (fun z => Θ i (z, 0))),
            W ⊆ K ∧ IsCompact K ∧ IsConnected K ∧ closure (interior K) = K ∧ 0 < m ∧
            Function.Injective origin ∧ frontier K ⊆ frontier W ∧
            (∀ i z, Θ i (z, 0) = (neck (origin i)).map (z, level (origin i))) ∧
            (∀ i, ContMDiffOn IC I3 ∞ (Θ i) (univ ×ˢ Ici (0 : ℝ)) ∧
              InjOn (Θ i) (univ ×ˢ Ici (0 : ℝ)) ∧
              IsProperMap (fun z : Sphere 2 × ℝ≥0 => Θ i (z.1, z.2.val)) ∧
              (let U : TopologicalSpace.Opens Cylinder :=
                ⟨univ ×ˢ Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
               IsSmoothEmbedding IC I3 ∞ (fun z : U => Θ i z)) ∧
              Θ i '' (univ ×ˢ Ici (0 : ℝ)) ∩ K = range (fun z => Θ i (z, 0)) ∧
              (∀ B : ℝ, ∃ T : ℝ≥0, ∀ (z : Sphere 2) (t : ℝ≥0),
                T ≤ t → B < Geometry.Curvature.metricScalarAt g (Θ i (z, t.val))) ∧
              ∃ (p : M) (nk : SpatialNeck g eps p)
                (P : PartialDiffeomorph IC I3 Cylinder M ∞),
                p ∈ range (fun z => Θ i (z, 0)) ∧
                univ ×ˢ Icc (0 : ℝ) 1 ⊆ P.source ∧
                (∀ z t, t ∈ Icc (0 : ℝ) 1 → Θ i (z, t) = P (z, t)) ∧
                P '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆ nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ∧
                (∀ z t, t ∈ Icc (-(collar i).radius) (collar i).radius → (z, t) ∈ P.source) ∧
                ∀ z : Sphere 2 ×
                    DifferentialGeometry.Topology.symmetricOpenInterval (collar i).radius,
                  (collar i).toFun z = P (z.1, z.2.val)) ∧
            Pairwise (fun i j => Disjoint (Θ i '' (univ ×ˢ Ici (0 : ℝ)))
              (Θ j '' (univ ×ˢ Ici (0 : ℝ)))) ∧
            frontier K = ⋃ i, range (fun z => Θ i (z, 0)) ∧
            K ∪ (⋃ i, Θ i '' (univ ×ˢ Ici (0 : ℝ))) = univ ∧
            (let _ := charts
             IsManifold (𝓡∂ 3) ∞ K ∧
               IsSmoothEmbedding (𝓡∂ 3) I3 ∞ (Subtype.val : K → M) ∧
               (∀ x : K, (𝓡∂ 3).IsBoundaryPoint x ↔ x.val ∈ frontier K) ∧
               (∀ x : K, (𝓡∂ 3).IsInteriorPoint x ↔ x.val ∈ interior K) ∧
               Subtype.val '' ((𝓡∂ 3).boundary K) = frontier K ∧
               Subtype.val '' ((𝓡∂ 3).interior K) = interior K) ∧
            ∀ i, (collar i).radius < 1 ∧
              (∀ z : Sphere 2 ×
                  DifferentialGeometry.Topology.symmetricOpenInterval (collar i).radius,
                (collar i).toFun z ∈ K ↔ z.2.val ≤ 0) ∧
              (∀ z : Sphere 2 ×
                  DifferentialGeometry.Topology.symmetricOpenInterval (collar i).radius,
                z.2.val < 0 → (collar i).toFun z ∈ interior K) ∧
              ∀ z : Sphere 2 ×
                  DifferentialGeometry.Topology.symmetricOpenInterval (collar i).radius,
                0 ≤ z.2.val → (collar i).toFun z = Θ i (z.1, z.2.val) := by
  obtain ⟨eta, heta, hproduce⟩ :=
    exists_spatial_neck_saved_end_decomposition_of_neck_or_cap_core_tolerance.{u, v}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ _ _ g W hW hne hreg ι _ point neck level hlevel hpair
    hfront A hanchor hmodels hscalar
  obtain ⟨K, m, origin, Θ, hWK, hK, hKconn, hKreg, hm, horigin, hfrontW, hzero,
    hends, hdisjoint, hfrontK, hcover⟩ :=
    hproduce eps heps M g W hW hne hreg ι point neck level hlevel hpair
      hfront A hanchor hmodels hscalar
  obtain ⟨charts, collar, hends', hcharts, hcollar⟩ :=
    exists_smooth_saved_end_charts g eps K m Θ hKreg hends hdisjoint hfrontK
  exact ⟨K, m, origin, Θ, charts, collar, hWK, hK, hKconn, hKreg, hm, horigin,
    hfrontW, hzero, hends', hdisjoint, hfrontK, hcover, hcharts, hcollar⟩


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
