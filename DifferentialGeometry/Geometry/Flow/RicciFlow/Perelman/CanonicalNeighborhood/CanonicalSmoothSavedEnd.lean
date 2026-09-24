import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalProperEnd
import DifferentialGeometry.Topology.Manifold.CylinderCollar.CoreAtlas

noncomputable section
open Set Manifold
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v

theorem exists_spatial_neck_smooth_saved_end_decomposition_of_canonical_witnesses_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M] [PreconnectedSpace M] [NoncompactSpace M]
          [SigmaCompactSpace M] (D : Geometry.Curvature.RealTimeInterval)
          (S : SolutionOn (I := I3) (M := M) D) (C1 C2 t : ℝ) (W : Set M),
          IsCompact W → closure (interior W) = W → IsPreconnected (interior W) →
          ∀ (ι : Type v) [Finite ι] (point : ι → M) (neck : ∀ i, SpatialNeck (S.base.metric t) eps (point i))
          (level : ι → ℝ), (∀ i, |level i| ≤ 4) →
          Pairwise (fun i j => Disjoint (range (fun q => (neck i).map (q, level i)))
            (range (fun q => (neck j).map (q, level j)))) →
          frontier W = ⋃ i, range (fun q => (neck i).map (q, level i)) →
          ∀ anchor ∈ W,
          (∀ x : M, x ∉ interior W → Nonempty (CanonicalWitness S eps C1 C2 x t)) →
          (∀ x : M, x ∉ interior W → C2 * S.scalar t anchor < S.scalar t x) →
          (∀ B : ℝ, IsCompact {x : M | S.scalar t x ≤ B}) →
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
              (∀ B : ℝ, ∃ T : ℝ≥0, ∀ (z : Sphere 2) (s : ℝ≥0),
                T ≤ s → B < S.scalar t (Θ i (z, s.val))) ∧
              ∃ (p : M) (nk : SpatialNeck (S.base.metric t) eps p)
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
  obtain ⟨eta, heta, hproduce⟩ := exists_spatial_neck_saved_end_decomposition_of_canonical_witnesses_tolerance.{u, v}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ _ _ _ D S C1 C2 t W hW hreg hconn ι _ point neck level hlevel hpair
    hfront anchor ha hcanonical hgap hscalar
  obtain ⟨K, m, origin, Θ, hWK, hK, hKconn, hKreg, hm, horigin, hfrontW, hzero,
    hends, hdisjoint, hfrontK, hcover⟩ :=
    hproduce eps heps M D S C1 C2 t W hW hreg hconn ι point neck level hlevel hpair
      hfront anchor ha hcanonical hgap hscalar
  have hfirst (i : Fin m) := (hends i).2.2.2.2.2.2
  choose center neck₀ P hcenter hsource hfirst hcontrolled using hfirst
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))
  obtain ⟨charts, collar, hcharts, hcollar⟩ :=
    DifferentialGeometry.Topology.exists_isManifold_of_finite_half_cylinders (n := 2)
      Θ P hsource hfirst hdisjoint hKreg hfrontK (fun i => (hends i).2.2.2.2.1)
  refine ⟨K, m, origin, Θ, charts, collar, hWK, hK, hKconn, hKreg, hm, horigin,
    hfrontW, hzero, ?_, hdisjoint, hfrontK, hcover, hcharts, ?_⟩
  · intro i
    obtain ⟨hsm, hinj, hproper, hembed, hinter, hdiverge, _⟩ := hends i
    exact ⟨hsm, hinj, hproper, hembed, hinter, hdiverge, center i, neck₀ i, P i,
      hcenter i, hsource i, hfirst i, hcontrolled i, (hcollar i).2.1, (hcollar i).2.2.1⟩
  intro i
  obtain ⟨hr, _, _, hside, hnegative, hpositive⟩ := hcollar i
  exact ⟨hr, hside, hnegative, hpositive⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
