import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SphericalRegion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalSphericalRegion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalSphericalRegionConnectedSigned
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingFromOpen
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph
import DifferentialGeometry.Topology.Manifold.ProductChartCollar
import DifferentialGeometry.Topology.Manifold.SignedGraphCollar
import DifferentialGeometry.Topology.Manifold.SmoothTwoSidedCollarAmbient
import DifferentialGeometry.Topology.Handle.Manifold
import DifferentialGeometry.Topology.Embedding.Frontier

noncomputable section
open Set Manifold
open DifferentialGeometry.Topology (SmoothTwoSidedCollar symmetricOpenInterval)
open DifferentialGeometry.Topology.Handle (chartedSpaceOfHomeomorph isManifoldOfHomeomorph
  contMDiff_homeomorph_of_chartedSpaceOfHomeomorph
  contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph)
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

private theorem exists_ambient_spherical_region {P : OrientedThreeStage.{u}}
    (U : TopologicalSpace.Opens P.Carrier) (C : Set U)
    [ChartedSpace (EuclideanHalfSpace 3) C] [IsManifold (𝓡∂ 3) ∞ C]
    (hcompact : IsCompact C) (hconnected : IsConnected C)
    (hinduced : IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ (Subtype.val : C → U))
    (hinterior : IsConnected ((Subtype.val : C → U) '' (𝓡∂ 3).interior C))
    {ι : Type u} [Finite ι] (sphere : ι → C(Sphere 2, C))
    (hsmooth : ∀ i, IsSmoothEmbedding (𝓡 2) ThreeModel ∞
      (fun y : Sphere 2 => (sphere i y).val))
    (hdisjoint : Pairwise fun i j => Disjoint (range (sphere i)) (range (sphere j)))
    (hboundary : (𝓡∂ 3).boundary C = ⋃ i, range (sphere i)) :
    ∃ (S : SmoothSphericalRegion P) (label : ι ≃ S.Boundary),
      S.region = Subtype.val '' C ∧
      ∀ i y, (S.sphere (label i) y).val = (sphere i y).val.val := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let R : Set P.Carrier := Subtype.val '' C
  let e : C ≃ₜ R := _root_.Topology.IsEmbedding.subtypeVal.homeomorphImage C
  let _ : ChartedSpace (EuclideanHalfSpace 3) R := chartedSpaceOfHomeomorph e.symm
  let _ : IsManifold (𝓡∂ 3) ∞ R := isManifoldOfHomeomorph (𝓡∂ 3) e.symm
  let D : R ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ C :=
    { toEquiv := e.symm.toEquiv
      contMDiff_toFun := contMDiff_homeomorph_of_chartedSpaceOfHomeomorph e.symm (𝓡∂ 3) ∞
      contMDiff_invFun := contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph e.symm (𝓡∂ 3) ∞ }
  have hval (x : C) : (D.symm x).val = x.val.val := rfl
  have hval' (x : R) : (D x).val.val = x.val := by
    have h := hval (D x)
    have hh : x.val = (D x).val.val := by simpa only [D.symm_apply_apply] using h
    exact hh.symm
  let label : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let spheres : Fin (Fintype.card ι) → C(Sphere 2, R) := fun j =>
    ⟨fun z => D.symm (sphere (label.symm j) z),
      D.symm.contMDiff.continuous.comp (sphere (label.symm j)).continuous⟩
  have hind : IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ (Subtype.val : R → P.Carrier) := by
    have h := DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_precomp
      (Subtype.val ∘ (Subtype.val : C → U))
      (DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_fromOpen
        (𝓡∂ 3) ThreeModel U (Subtype.val : C → U) hinduced) D
    simpa only [Function.comp_def, hval'] using h
  refine ⟨{ region := R
            compact := hcompact.image continuous_subtype_val
            connected := hconnected.image Subtype.val continuous_subtype_val.continuousOn
            induced := hind
            interior_connected := ?_
            Boundary := Fin (Fintype.card ι)
            finiteBoundary := inferInstance
            sphere := spheres
            sphere_smooth := ?_
            sphere_disjoint := ?_
            boundary_eq := ?_ }, label, rfl, ?_⟩
  · have hset : (Subtype.val : R → P.Carrier) '' (𝓡∂ 3).interior R =
        Subtype.val '' ((Subtype.val : C → U) '' (𝓡∂ 3).interior C) := by
      rw [← D.symm.image_interior (by simp), image_image, image_image]
      rfl
    rw [hset]
    exact hinterior.image Subtype.val continuous_subtype_val.continuousOn
  · intro j
    exact DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_fromOpen
      (𝓡 2) ThreeModel U (fun y => (sphere (label.symm j) y).val) (hsmooth _)
  · intro i j hij
    apply disjoint_left.mpr
    rintro z ⟨p, hp⟩ ⟨q, hq⟩
    have heq : sphere (label.symm i) p = sphere (label.symm j) q :=
      D.symm.injective (hp.trans hq.symm)
    exact disjoint_left.mp (hdisjoint (fun h => hij (label.symm.injective h)))
      (mem_range_self p) ⟨q, heq.symm⟩
  · rw [← D.symm.image_boundary (by simp), hboundary, image_iUnion]
    ext z
    simp only [mem_iUnion, mem_image, mem_range]
    constructor
    · rintro ⟨i, x, ⟨y, rfl⟩, hz⟩
      have hzy : spheres (label i) y = z := by
        simpa only [spheres, ContinuousMap.coe_mk, label.symm_apply_apply] using hz
      exact ⟨label i, y, hzy⟩
    · rintro ⟨j, y, hy⟩
      exact ⟨label.symm j, sphere (label.symm j) y, ⟨y, rfl⟩, hy⟩
  · intro i y
    change (D.symm (sphere (label.symm (label i)) y)).val = _
    rw [label.symm_apply_apply, hval]


namespace OrientedThreeStage.IncomingSlab

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.exists_smoothSphericalRegion_terminal_component_with_signed_collar
    (L : G.TerminalLimitMetric) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ η →
      ∃ C2 q : ℝ, 1 ≤ C2 ∧ 0 < q ∧
        ∀ (A : ℝ) (y : G.terminalRegularOpen), 0 < A → q < 4 * C2 * A →
          metricScalarAt L.metric y ≤ A → ¬ IsCompact (connectedComponent y) →
          ∃ (ι : Type u) (v : ι → G.terminalRegularOpen)
            (neck : ∀ i, SpatialNeck L.metric δ (v i)) (level : ι → ℝ)
            (b : Finset ι) (C : Set G.terminalRegularOpen)
            (S : SmoothSphericalRegion P) (label : {i // i ∈ b} ≃ S.Boundary),
            b.Nonempty ∧ IsConnected (interior C) ∧
            y ∈ interior C ∧ y.val ∈ interior S.region ∧
            C ⊆ connectedComponent y ∧ S.region = Subtype.val '' C ∧
            (∀ x ∈ C, metricScalarAt L.metric x ≤ 8 * C2^2 * A) ∧
            frontier C = ⋃ i ∈ b, range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
            (∀ x ∈ frontier C, 2 * A < metricScalarAt L.metric x) ∧
            (∀ i z, (S.sphere (label i) z).val = ((neck i.val).map (z, level i.val)).val) ∧
            ∀ i ∈ b, |level i| ≤ 3 ∧
              IsSmoothEmbedding I2 I3 ∞ (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
              (∀ z ∈ (univ ×ˢ Icc (-101 : ℝ) 101 : Set Cylinder),
                2 * A < metricScalarAt L.metric ((neck i).map z) ∧
                  metricScalarAt L.metric ((neck i).map z) ≤ 8 * C2^2 * A) ∧
              (neck i).cylindricalChart.metricCloseOn L.metric δ
                {z : (neck i).cylindricalChart.domain | z.val.2 ∈ Icc (-101 : ℝ) 101} ∧
              (∀ z t, t ∈ Icc (-101 : ℝ) 101 → (z, t) ∈ (neck i).cylindricalChart.domain) ∧
              ∃ r σ : ℝ, 0 < r ∧ r ≤ 1 ∧ (σ = 1 ∨ σ = -1) ∧
                (∀ z, ∀ t ∈ Ioo (-r) r, (z, level i + σ * t) ∈ (neck i).map.source) ∧
                (∀ z, ∀ t ∈ Ioo (-r) r,
                  (neck i).map (z, level i + σ * t) ∈ C ↔ t ≤ 0) ∧
                (∀ z, ∀ t ∈ Ioo (-r) r,
                  (neck i).map (z, level i + σ * t) ∈ interior C ↔ t < 0) ∧
                ∃ c : SmoothTwoSidedCollar I2 ThreeModel
                    (fun z : Sphere 2 => ((neck i).map (z, level i)).val),
                  c.radius < r ∧
                  ∀ q : Sphere 2 × symmetricOpenInterval c.radius,
                    c.toFun q = ((neck i).map (q.1, level i + σ * (q.2 : ℝ))).val ∧
                    (c.toFun q ∈ S.region ↔ (q.2 : ℝ) ≤ 0) ∧
                    (c.toFun q ∈ interior S.region ↔ (q.2 : ℝ) < 0) := by
  obtain ⟨η, hη, hregion⟩ := L.exists_connected_spherical_region_with_signed_collar
  refine ⟨η, hη, ?_⟩
  intro δ hδ hδη
  obtain ⟨C2, q, hC2, hq, hregion⟩ := hregion δ hδ hδη
  refine ⟨C2, q, hC2, hq, ?_⟩
  intro A y hA hqA hyA hnoncompact
  obtain ⟨ι, v, neck, level, b, C, hb, hcompact, hconnected, hinteriorconnected,
    _, hy, hcomponent, hscalar, hdisjoint, hfrontier, hfrontierscalar, hatlas, hnecks⟩ :=
    hregion A y hA hqA hyA hnoncompact
  obtain ⟨charts, hmanifold, hinduced, hboundary, hinterior⟩ := hatlas
  let _ : ChartedSpace (EuclideanHalfSpace 3) C := charts
  let _ : IsManifold (𝓡∂ 3) ∞ C := hmanifold
  classical
  let _ : Fintype {i // i ∈ b} := Fintype.ofFinite _
  have hmem (i : {i // i ∈ b}) (z : Sphere 2) : (neck i.val).map (z, level i.val) ∈ C :=
    hcompact.isClosed.frontier_subset
      (hfrontier.symm ▸ mem_iUnion₂.mpr ⟨i.val, i.property, mem_range_self z⟩)
  let sphere : {i // i ∈ b} → C(Sphere 2, C) := fun i =>
    ⟨fun z => ⟨(neck i.val).map (z, level i.val), hmem i z⟩,
      ((hnecks i.val i.property).2.1.contMDiff.continuous).subtype_mk _⟩
  have hsphere : ∀ i, IsSmoothEmbedding (𝓡 2) ThreeModel ∞
      (fun z : Sphere 2 => (sphere i z).val) := fun i => (hnecks i.val i.property).2.1
  have hspheredisjoint : Pairwise fun i j => Disjoint (range (sphere i)) (range (sphere j)) := by
    intro i j hij
    apply disjoint_left.mpr
    rintro z ⟨p, hp⟩ ⟨q, hq⟩
    exact disjoint_left.mp
      (hdisjoint i.property j.property (fun h => hij (Subtype.ext h)))
      ⟨p, congrArg Subtype.val hp⟩ ⟨q, congrArg Subtype.val hq⟩
  have hsphereboundary : (𝓡∂ 3).boundary C = ⋃ i, range (sphere i) := by
    ext z
    constructor
    · intro hz
      have hzfront : z.val ∈ frontier C := hboundary ▸ mem_image_of_mem Subtype.val hz
      obtain ⟨i, hi, p, hp⟩ := mem_iUnion₂.mp (hfrontier ▸ hzfront)
      exact mem_iUnion.mpr ⟨⟨i, hi⟩, p, Subtype.ext hp⟩
    · intro hz
      obtain ⟨i, p, hp⟩ := mem_iUnion.mp hz
      have hzfront : z.val ∈ frontier C := hfrontier.symm ▸
        mem_iUnion₂.mpr ⟨i.val, i.property, p, congrArg Subtype.val hp⟩
      rw [← hboundary] at hzfront
      obtain ⟨w, hw, hwz⟩ := hzfront
      exact Subtype.ext hwz ▸ hw
  obtain ⟨S, label, hSregion, hSsphere⟩ := exists_ambient_spherical_region
    G.terminalRegularOpen C hcompact hconnected hinduced
      (by rw [hinterior]; exact hinteriorconnected) sphere hsphere hspheredisjoint hsphereboundary
  have hyambient : y.val ∈ interior S.region := by
    rw [hSregion]
    have hopen : IsOpen (Subtype.val '' interior C : Set P.Carrier) :=
      G.terminalRegularOpen.isOpenEmbedding'.isOpenMap _ isOpen_interior
    exact interior_maximal (image_mono interior_subset) hopen (mem_image_of_mem Subtype.val hy)
  refine ⟨ι, v, neck, level, b, C, S, label, hb, hinteriorconnected, hy, hyambient,
    hcomponent, hSregion, hscalar, hfrontier, hfrontierscalar, hSsphere, ?_⟩
  intro i hi
  obtain ⟨hl, hsmooth, hscalar, hclose, hdomain, r, σ, hr, hr1, hσ,
    hsource, hside, hinside⟩ := hnecks i hi
  have hslice (z : Sphere 2) : (z, level i) ∈ (neck i).map.source := by
    simpa only [mul_zero, add_zero] using hsource z 0 ⟨neg_lt_zero.mpr hr, hr⟩
  obtain ⟨c₀, hcr, _, hcoord⟩ :=
    DifferentialGeometry.Topology.exists_smoothTwoSidedCollar_of_signed_partialDiffeomorph_graph
      (neck i).map (fun _ => level i) contMDiff_const hslice σ hσ hr
  let c := c₀.mapAmbient (Subtype.val : G.terminalRegularOpen → P.Carrier)
    (DifferentialGeometry.isLocalDiffeomorph_subtype_val G.terminalRegularOpen)
    Subtype.val_injective
  refine ⟨hl, hsmooth, hscalar, hclose, hdomain, r, σ, hr, hr1, hσ,
    hsource, hside, hinside, c, hcr, ?_⟩
  intro q
  have ht : (q.2 : ℝ) ∈ Ioo (-r) r := by
    have hq : -c₀.radius < (q.2 : ℝ) ∧ (q.2 : ℝ) < c₀.radius := q.2.property
    constructor <;> linarith
  have hmap : c.toFun q = ((neck i).map (q.1, level i + σ * (q.2 : ℝ))).val :=
    congrArg Subtype.val (hcoord q)
  refine ⟨hmap, ?_, ?_⟩
  · rw [hmap, hSregion, Subtype.val_injective.mem_set_image]
    exact hside q.1 q.2 ht
  · rw [hmap, hSregion, DifferentialGeometry.Topology.Embedding.interior_image_of_isOpenEmbedding
      G.terminalRegularOpen.isOpenEmbedding', Subtype.val_injective.mem_set_image]
    exact hinside q.1 q.2 ht

end OrientedThreeStage.IncomingSlab

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
