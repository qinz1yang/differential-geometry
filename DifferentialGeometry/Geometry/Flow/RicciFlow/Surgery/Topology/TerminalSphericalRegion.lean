import DifferentialGeometry.Geometry.Neck.SpatialComponentCollar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalBarrierComponents
import DifferentialGeometry.Geometry.Neck.DisjointBarrierRegion
import DifferentialGeometry.Geometry.Neck.BoundaryAtlas
import DifferentialGeometry.Topology.Connected.RegularClosedComponents
import DifferentialGeometry.Topology.Manifold.ConnectedInterior
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalConnectedCore
import DifferentialGeometry.Topology.Connected.CoverBySides

set_option autoImplicit false
noncomputable section
open Set Manifold
open DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem exists_uniform_disjoint_spherical_region_of_canonical_neighborhoods :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, δ ≤ η →
      ∀ C1 C2 q : ℝ,
      ∀ (P : OrientedThreeStage.{u}) (a s : ℝ) (G : P.IncomingSlab a s)
        (L : G.TerminalLimitMetric),
        (∀ x t, t ∈ Ioo a s → q < G.flow.scalar t x →
          ∃ W : CanonicalWitness G.flow (δ / 4) C1 C2 x t,
            W.capTubeHasNeckChart (δ / 4)) →
        ∀ (A : ℝ) (y : G.terminalRegularOpen), 0 < A → q < 4 * C2 * A →
          metricScalarAt L.metric y ≤ A → ¬ IsCompact (connectedComponent y) →
          ∃ (ι : Type u) (v : ι → G.terminalRegularOpen)
            (neck : ∀ i, SpatialNeck L.metric δ (v i)) (level : ι → ℝ)
            (b : Finset ι) (K : Set G.terminalRegularOpen),
            b.Nonempty ∧ IsCompact K ∧ closure (interior K) = K ∧
            {x : G.terminalRegularOpen | x ∈ connectedComponent y ∧ metricScalarAt L.metric x ≤ A}
              ⊆ interior K ∧ K ⊆ connectedComponent y ∧
            (∀ x ∈ K, metricScalarAt L.metric x ≤ 8 * C2^2 * A) ∧
            (b : Set ι).PairwiseDisjoint
              (fun i => range (fun z : Sphere 2 => (neck i).map (z, level i))) ∧
            frontier K = ⋃ i ∈ b, range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
            (∀ x ∈ frontier K, 2 * A < metricScalarAt L.metric x) ∧
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
                  (neck i).map (z, level i + σ * t) ∈ K ↔ t ≤ 0) ∧
                ∀ z, ∀ t ∈ Ioo (-r) r,
                  (neck i).map (z, level i + σ * t) ∈ interior K ↔ t < 0 := by
  obtain ⟨eta, heta, hregion⟩ :=
    exists_compact_region_of_finite_spatial_neck_barriers_tolerance.{u, u}
  refine ⟨min eta (1 / 40000), lt_min heta (by norm_num), ?_⟩
  intro δ hδeta C1 C2 q P a s G L hcanonical A y hA hqA hyA hnoncompact
  obtain ⟨x, _, hx⟩ := L.exists_scalar_gt_on_connectedComponent_of_not_isCompact y hnoncompact q
  have hhigh := (L.tendsto_metricScalarAt x).eventually (Ioi_mem_nhds hx)
  have htime : ∀ᶠ t in nhdsWithin s (Iio s), t ∈ Ioo a s := Ioo_mem_nhdsLT G.lt
  obtain ⟨t, ht, hqt⟩ := (htime.and hhigh).exists
  obtain ⟨W, _⟩ := hcanonical x.val t ht hqt
  have hC2 : 1 ≤ C2 := W.one_le_comparison_constant
  have hδsmall : δ < 1 / 20000 := by linarith [hδeta.trans (min_le_right _ _)]
  obtain ⟨S, D, hSne, hcover, hD, v, neck, level, sign, collar, hfront, hunion, hgeometry,
    hcollar, hallcompact, hlow, hold⟩ := L.exists_finite_recorded_spherical_barriers_with_compact_component_closures_of_canonical
      hδsmall hcanonical A y hA hqA hyA hnoncompact
  let J := {p // p ∈ S} × Fin 2
  let F : J → Set G.terminalRegularOpen := fun i =>
    range (fun z : Sphere 2 => (neck i.1).map (z, level i))
  let Low := {x : G.terminalRegularOpen | x ∈ connectedComponent y ∧ metricScalarAt L.metric x ≤ A}
  classical
  let _ := Fintype.ofFinite J
  have hLowcompact : IsCompact Low :=
    (L.isCompact_scalar_sublevel A).of_isClosed_subset
      (isClosed_connectedComponent.inter
        (isClosed_le (metricScalar_smooth L.metric).continuous continuous_const))
      (fun x hx => hx.2)
  have hLowold (x : G.terminalRegularOpen) (hx : x ∈ Low) :
      IsCompact (closure (connectedComponentIn
        (⋃ i ∈ (Finset.univ : Finset J), F i)ᶜ x)) := by
    simpa only [Finset.mem_univ, iUnion_true] using (hold x hx.1 hx.2).1
  obtain ⟨t, b, C, ht, hbt, htdis, hC, hCprops, hKcompact, hLowK, hKreg,
    hKsub, hKfront, hKcollar⟩ :=
    hregion δ (hδeta.trans (min_le_left _ _)) G.terminalRegularOpen L.metric
      J (fun i => v i.1) (fun i => neck i.1) level Finset.univ
      (fun i _ => (hcollar i).1) A Low hLowcompact (fun _ hx => hx.2)
      (fun i _ => (hgeometry i.1).1) hLowold
  let K := ⋃ V ∈ C, closure V
  have hKcomp : K ⊆ connectedComponent y := by
    intro z hz
    obtain ⟨V, hVC, hzV⟩ := mem_iUnion₂.mp hz
    obtain ⟨x, hx, rfl⟩ := (hC V).mp hVC
    have hsubset : connectedComponentIn (⋃ i ∈ t, F i)ᶜ x ⊆ connectedComponent y := by
      have hxout : x ∉ ⋃ i ∈ t, F i := by
        intro hxbar
        obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxbar
        exact disjoint_left.mp hlow hx.2 (mem_iUnion.mpr ⟨i, hxi⟩)
      have hc := isPreconnected_connectedComponentIn.subset_connectedComponent
        (mem_connectedComponentIn (show x ∈ (⋃ i ∈ t, F i)ᶜ from hxout))
      rw [← connectedComponent_eq hx.1] at hc
      exact hc
    exact closure_minimal hsubset isClosed_connectedComponent hzV
  have hKband : ∀ z ∈ K, metricScalarAt L.metric z ≤ 8 * C2^2 * A := by
    intro z hz
    rcases hKsub hz with hzold | hzchart
    · obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.mp hzold
      have hzx' : z ∈ closure (connectedComponentIn (⋃ i : J, F i)ᶜ x) := by
        simpa only [Finset.mem_univ, iUnion_true] using hzx
      have hb := (hold x hx.1 hx.2).2 hzx'
      have hupper : 4 * C2 * A ≤ 8 * C2^2 * A :=
        mul_le_mul_of_nonneg_right (by nlinarith : 4 * C2 ≤ 8 * C2 ^ 2) hA.le
      exact hb.2.le.trans hupper
    · obtain ⟨i, _, w, hw, rfl⟩ := mem_iUnion₂.mp hzchart
      exact ((hgeometry i.1).2.1 w
        ⟨hw.1, by constructor <;> linarith [hw.2.1, hw.2.2]⟩).2
  have hfrontband : ∀ z ∈ frontier K, 2 * A < metricScalarAt L.metric z := by
    intro z hz
    obtain ⟨i, hi, w, rfl⟩ := mem_iUnion₂.mp (hKfront ▸ hz)
    exact ((hgeometry i.1).2.1 (w, level i)
      ⟨mem_univ _, by constructor <;>
        linarith [(abs_le.mp (hcollar i).1).1, (abs_le.mp (hcollar i).1).2]⟩).1
  have hbne : b.Nonempty := by
    by_contra hn
    have hbempty : b = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hfrontempty : frontier K = ∅ := by
      rw [hKfront, hbempty]
      simp
    have hsub : connectedComponent y ⊆ interior K :=
      isPreconnected_subset_interior_of_meets_of_disjoint_frontier isPreconnected_connectedComponent
        ⟨y, mem_connectedComponent, interior_subset (hLowK ⟨mem_connectedComponent, hyA⟩)⟩
        (by rw [hfrontempty]; exact disjoint_empty _)
    exact hnoncompact (hKcompact.of_isClosed_subset isClosed_connectedComponent
      (hsub.trans interior_subset))
  refine ⟨J, (fun i => v i.1), (fun i => neck i.1), level, b, K, hbne, hKcompact,
    hKreg, hLowK, hKcomp,
    hKband, ?_, hKfront, hfrontband, ?_⟩
  · intro i hi j hj hij
    exact htdis (hbt hi) (hbt hj) hij
  · intro i hi
    obtain ⟨r, σ, hr, hσ, hsrc, hside, hinside⟩ := hKcollar i hi
    let r' := min r 1
    have hr' : 0 < r' := lt_min hr zero_lt_one
    have hscaled (z : ℝ) (hz : z ∈ Ioo (-r') r') : σ * z ∈ Ioo (-r) r := by
      rcases hσ with rfl | rfl <;> constructor <;> nlinarith [hz.1, hz.2, min_le_left r 1]
    refine ⟨(hcollar i).1, (hcollar i).2.2.1, (hgeometry i.1).2.1,
      (hgeometry i.1).2.2.1, (hgeometry i.1).2.2.2, r', σ, hr', min_le_right _ _, hσ,
      (fun z t ht => hsrc z (σ * t) (hscaled t ht)), ?_, ?_⟩
    · intro z t ht
      have hh := hside z (σ * t) (hscaled t ht)
      rcases hσ with rfl | rfl <;> simpa [K] using hh
    · intro z t ht
      have hh := hinside z (σ * t) (hscaled t ht)
      rcases hσ with rfl | rfl <;> simpa [K] using hh

theorem exists_uniform_disjoint_spherical_region :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ η →
      ∃ C2 : ℝ, 1 ≤ C2 ∧ ∀ (P : OrientedThreeStage.{u}) (a s : ℝ)
        (G : P.IncomingSlab a s), ∃ q : ℝ, 0 < q ∧
        ∀ (L : G.TerminalLimitMetric) (A : ℝ) (y : G.terminalRegularOpen), 0 < A → q < 4 * C2 * A →
          metricScalarAt L.metric y ≤ A → ¬ IsCompact (connectedComponent y) →
          ∃ (ι : Type u) (v : ι → G.terminalRegularOpen)
            (neck : ∀ i, SpatialNeck L.metric δ (v i)) (level : ι → ℝ)
            (b : Finset ι) (K : Set G.terminalRegularOpen),
            b.Nonempty ∧ IsCompact K ∧ closure (interior K) = K ∧
            {x : G.terminalRegularOpen | x ∈ connectedComponent y ∧ metricScalarAt L.metric x ≤ A}
              ⊆ interior K ∧ K ⊆ connectedComponent y ∧
            (∀ x ∈ K, metricScalarAt L.metric x ≤ 8 * C2^2 * A) ∧
            (b : Set ι).PairwiseDisjoint
              (fun i => range (fun z : Sphere 2 => (neck i).map (z, level i))) ∧
            frontier K = ⋃ i ∈ b, range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
            (∀ x ∈ frontier K, 2 * A < metricScalarAt L.metric x) ∧
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
                  (neck i).map (z, level i + σ * t) ∈ K ↔ t ≤ 0) ∧
                ∀ z, ∀ t ∈ Ioo (-r) r,
                  (neck i).map (z, level i + σ * t) ∈ interior K ↔ t < 0 := by
  obtain ⟨eta, heta, hregion⟩ :=
    exists_uniform_disjoint_spherical_region_of_canonical_neighborhoods.{u}
  refine ⟨min eta (1 / 40000), lt_min heta (by norm_num), ?_⟩
  intro δ hδ hδη
  have heps : 0 < δ / 4 := by positivity
  have hsmall : δ / 4 < 1 / 11 := by linarith [hδη.trans (min_le_right _ _)]
  obtain ⟨C2, hC2, hmain⟩ := exists_uniform_canonical_constants_with_cap_neck_charts.{u} heps hsmall
  refine ⟨C2, hC2, ?_⟩
  intro P a s G
  obtain ⟨q, hq, hcanonical⟩ := hmain P a s G
  refine ⟨q, hq, ?_⟩
  intro L A y hA hqA hyA hnoncompact
  exact hregion δ (hδη.trans (min_le_left _ _)) C2 C2 q P a s G L
    (fun x t ht hx => hcanonical x t ⟨ht.1.le, ht.2⟩ hx.le) A y hA hqA hyA hnoncompact

theorem TerminalLimitMetric.exists_disjoint_spherical_region
    (L : G.TerminalLimitMetric) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ η →
      ∃ C2 q : ℝ, 1 ≤ C2 ∧ 0 < q ∧
        ∀ (A : ℝ) (y : G.terminalRegularOpen), 0 < A → q < 4 * C2 * A →
          metricScalarAt L.metric y ≤ A → ¬ IsCompact (connectedComponent y) →
          ∃ (ι : Type u) (v : ι → G.terminalRegularOpen)
            (neck : ∀ i, SpatialNeck L.metric δ (v i)) (level : ι → ℝ)
            (b : Finset ι) (K : Set G.terminalRegularOpen),
            b.Nonempty ∧ IsCompact K ∧ closure (interior K) = K ∧
            {x : G.terminalRegularOpen | x ∈ connectedComponent y ∧ metricScalarAt L.metric x ≤ A}
              ⊆ interior K ∧ K ⊆ connectedComponent y ∧
            (∀ x ∈ K, metricScalarAt L.metric x ≤ 8 * C2^2 * A) ∧
            (b : Set ι).PairwiseDisjoint
              (fun i => range (fun z : Sphere 2 => (neck i).map (z, level i))) ∧
            frontier K = ⋃ i ∈ b, range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
            (∀ x ∈ frontier K, 2 * A < metricScalarAt L.metric x) ∧
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
                  (neck i).map (z, level i + σ * t) ∈ K ↔ t ≤ 0) ∧
                ∀ z, ∀ t ∈ Ioo (-r) r,
                  (neck i).map (z, level i + σ * t) ∈ interior K ↔ t < 0 := by
  obtain ⟨eta, heta, hregion⟩ := exists_uniform_disjoint_spherical_region.{u}
  refine ⟨eta, heta, ?_⟩
  intro δ hδ hδη
  obtain ⟨C2, hC2, hregion⟩ := hregion δ hδ hδη
  obtain ⟨q, hq, hregion⟩ := hregion P a s G
  exact ⟨C2, q, hC2, hq, hregion L⟩

theorem TerminalLimitMetric.exists_disjoint_spherical_region_with_boundary_atlas
    (L : G.TerminalLimitMetric) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ η →
      ∃ C2 q : ℝ, 1 ≤ C2 ∧ 0 < q ∧
        ∀ (A : ℝ) (y : G.terminalRegularOpen), 0 < A → q < 4 * C2 * A →
          metricScalarAt L.metric y ≤ A → ¬ IsCompact (connectedComponent y) →
          ∃ (ι : Type u) (v : ι → G.terminalRegularOpen)
            (neck : ∀ i, SpatialNeck L.metric δ (v i)) (level : ι → ℝ)
            (b : Finset ι) (K : Set G.terminalRegularOpen),
            b.Nonempty ∧ IsCompact K ∧ closure (interior K) = K ∧
            {x : G.terminalRegularOpen | x ∈ connectedComponent y ∧ metricScalarAt L.metric x ≤ A}
              ⊆ interior K ∧ K ⊆ connectedComponent y ∧
            (∀ x ∈ K, metricScalarAt L.metric x ≤ 8 * C2^2 * A) ∧
            (b : Set ι).PairwiseDisjoint
              (fun i => range (fun z : Sphere 2 => (neck i).map (z, level i))) ∧
            frontier K = ⋃ i ∈ b, range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
            (∀ x ∈ frontier K, 2 * A < metricScalarAt L.metric x) ∧
            (∃ charts : ChartedSpace (EuclideanHalfSpace 3) K,
              let _ := charts
              IsManifold (𝓡∂ 3) ∞ K ∧
                IsSmoothEmbedding (𝓡∂ 3) I3 ∞ (Subtype.val : K → G.terminalRegularOpen) ∧
                Subtype.val '' ((𝓡∂ 3).boundary K) = frontier K ∧
                Subtype.val '' ((𝓡∂ 3).interior K) = interior K) ∧
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
                  (neck i).map (z, level i + σ * t) ∈ K ↔ t ≤ 0) ∧
                ∀ z, ∀ t ∈ Ioo (-r) r,
                  (neck i).map (z, level i + σ * t) ∈ interior K ↔ t < 0 := by
  obtain ⟨η, hη, hregion⟩ := L.exists_disjoint_spherical_region
  refine ⟨η, hη, ?_⟩
  intro δ hδ hδη
  obtain ⟨C2, q, hC2, hq, hregion⟩ := hregion δ hδ hδη
  refine ⟨C2, q, hC2, hq, ?_⟩
  intro A y hA hqA hyA hnoncompact
  obtain ⟨ι, v, neck, level, b, K, hb, hK, hregular, hlow, hcomponent, hscalar,
    hdisjoint, hfrontier, hfrontier_scalar, hnecks⟩ := hregion A y hA hqA hyA hnoncompact
  refine ⟨ι, v, neck, level, b, K, hb, hK, hregular, hlow, hcomponent, hscalar,
    hdisjoint, hfrontier, hfrontier_scalar, ?_, hnecks⟩
  have hlevel (i : {i // i ∈ b}) : |level i.val| < δ⁻¹ := by
    have hlen : (3 : ℝ) < δ⁻¹ :=
      (lt_inv_comm₀ (by norm_num) (neck i.val).eps_pos).mpr
        (by linarith [(neck i.val).eps_small])
    exact ((hnecks i.val i.property).1).trans_lt hlen
  apply exists_isManifold_of_finite_spatial_neck_levels L.metric
    (fun i : {i // i ∈ b} => v i.val) (fun i => neck i.val)
    (fun i => level i.val) hlevel (fun _ => Diffeomorph.refl I2 (Sphere 2) ∞)
  · intro i j hij
    simpa only [Diffeomorph.coe_refl, id_eq] using
      hdisjoint i.property j.property (fun heq => hij (Subtype.ext heq))
  · exact hregular
  · intro x hx
    obtain ⟨i, hi, q, hq⟩ := mem_iUnion₂.mp (hfrontier ▸ hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, q, hq⟩


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

noncomputable section

open Set Manifold
open DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.exists_connected_spherical_region
    (L : G.TerminalLimitMetric) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ η →
      ∃ C2 q : ℝ, 1 ≤ C2 ∧ 0 < q ∧
        ∀ (A : ℝ) (y : G.terminalRegularOpen), 0 < A → q < 4 * C2 * A →
          metricScalarAt L.metric y ≤ A → ¬ IsCompact (connectedComponent y) →
          ∃ (ι : Type u) (v : ι → G.terminalRegularOpen)
            (neck : ∀ i, SpatialNeck L.metric δ (v i)) (level : ι → ℝ)
            (b : Finset ι) (C : Set G.terminalRegularOpen),
            b.Nonempty ∧ IsCompact C ∧ IsConnected C ∧ IsConnected (interior C) ∧
            closure (interior C) = C ∧
            y ∈ interior C ∧ C ⊆ connectedComponent y ∧
            (∀ x ∈ C, metricScalarAt L.metric x ≤ 8 * C2^2 * A) ∧
            (b : Set ι).PairwiseDisjoint
              (fun i => range (fun z : Sphere 2 => (neck i).map (z, level i))) ∧
            frontier C = ⋃ i ∈ b, range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
            (∀ x ∈ frontier C, 2 * A < metricScalarAt L.metric x) ∧
            (∃ charts : ChartedSpace (EuclideanHalfSpace 3) C,
              let _ := charts
              IsManifold (𝓡∂ 3) ∞ C ∧
                IsSmoothEmbedding (𝓡∂ 3) I3 ∞ (Subtype.val : C → G.terminalRegularOpen) ∧
                Subtype.val '' ((𝓡∂ 3).boundary C) = frontier C ∧
                Subtype.val '' ((𝓡∂ 3).interior C) = interior C) ∧
            ∀ i ∈ b, |level i| ≤ 3 ∧
              IsSmoothEmbedding I2 I3 ∞ (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
              (∀ z ∈ (univ ×ˢ Icc (-101 : ℝ) 101 : Set Cylinder),
                2 * A < metricScalarAt L.metric ((neck i).map z) ∧
                  metricScalarAt L.metric ((neck i).map z) ≤ 8 * C2^2 * A) ∧
              (neck i).cylindricalChart.metricCloseOn L.metric δ
                {z : (neck i).cylindricalChart.domain | z.val.2 ∈ Icc (-101 : ℝ) 101} ∧
              (∀ z t, t ∈ Icc (-101 : ℝ) 101 → (z, t) ∈ (neck i).cylindricalChart.domain) := by
  obtain ⟨η, hη, hregion⟩ := L.exists_disjoint_spherical_region_with_boundary_atlas
  refine ⟨η, hη, ?_⟩
  intro δ hδ hδη
  obtain ⟨C2, q, hC2, hq, hregion⟩ := hregion δ hδ hδη
  refine ⟨C2, q, hC2, hq, ?_⟩
  intro A y hA hqA hyA hnoncompact
  obtain ⟨ι, v, neck, level, b, K, hb, hK, hregular, hlow, hcomponent, hscalar,
    hdisjoint, hfrontier, hfrontier_scalar, hatlas, hnecks⟩ :=
    hregion A y hA hqA hyA hnoncompact
  obtain ⟨charts, hmanifold, _, _, _⟩ := hatlas
  let _ : ChartedSpace (EuclideanHalfSpace 3) K := charts
  let _ : IsManifold (𝓡∂ 3) ∞ K := hmanifold
  let _ : LocallyConnectedSpace K :=
    ChartedSpace.locallyConnectedSpace (EuclideanHalfSpace 3) K
  let _ : LocallyConnectedSpace G.terminalRegularOpen :=
    ChartedSpace.locallyConnectedSpace ThreeSpace G.terminalRegularOpen
  let C := connectedComponentIn K y
  let F : ι → Set G.terminalRegularOpen := fun i =>
    range (fun z : Sphere 2 => (neck i).map (z, level i))
  classical
  let b' := b.filter fun i => (F i ∩ C).Nonempty
  have hsub : C ⊆ K := connectedComponentIn_subset K y
  have hyK : y ∈ interior K := hlow ⟨mem_connectedComponent, hyA⟩
  have hyC : y ∈ C := mem_connectedComponentIn (interior_subset hyK)
  have hcompact : IsCompact C := isCompact_connectedComponentIn hK y
  have hreg : closure (interior C) = C := closure_interior_connectedComponentIn hregular y
  have hfrontsub : frontier C ⊆ frontier K := frontier_connectedComponentIn_subset K y
  have hyint : y ∈ interior C :=
    (mem_interior_iff_notMem_frontier hyC).mpr fun hyfront => (hfrontsub hyfront).2 hyK
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))
  have hF (i : {i // i ∈ b}) : IsPreconnected (F i.val) :=
    isPreconnected_range ((hnecks i.val i.property).2.1.contMDiff.continuous)
  have hfrontall : frontier K = ⋃ i : {i // i ∈ b}, F i.val := by
    simpa only [iUnion_subtype] using hfrontier
  have hfront : frontier C = ⋃ i ∈ b', F i := by
    rw [frontier_connectedComponentIn_eq_iUnion hK.isClosed
      (fun i : {i // i ∈ b} => F i.val) hF hfrontall y]
    ext z
    simp only [b', Finset.mem_filter, mem_iUnion, Subtype.exists, exists_prop]
    tauto
  have hb' : b'.Nonempty := by
    by_contra hn
    have hfrontempty : frontier C = ∅ := by
      rw [hfront, Finset.not_nonempty_iff_eq_empty.mp hn]
      simp
    have hall : connectedComponent y ⊆ interior C :=
      isPreconnected_subset_interior_of_meets_of_disjoint_frontier isPreconnected_connectedComponent
        ⟨y, mem_connectedComponent, hyC⟩
        (by rw [hfrontempty]; exact disjoint_empty _)
    exact hnoncompact (hcompact.of_isClosed_subset isClosed_connectedComponent
      (hall.trans interior_subset))
  have hb'sub : b' ⊆ b := Finset.filter_subset _ _
  have hselected : (b' : Set ι).PairwiseDisjoint F := by
    intro i hi j hj hij
    exact hdisjoint (hb'sub hi) (hb'sub hj) hij
  have hconn : IsConnected C :=
    isConnected_connectedComponentIn_iff.mpr (interior_subset hyK)
  have hatlasC : ∃ charts : ChartedSpace (EuclideanHalfSpace 3) C,
      let _ := charts
      IsManifold (𝓡∂ 3) ∞ C ∧
        IsSmoothEmbedding (𝓡∂ 3) I3 ∞ (Subtype.val : C → G.terminalRegularOpen) ∧
        Subtype.val '' ((𝓡∂ 3).boundary C) = frontier C ∧
        Subtype.val '' ((𝓡∂ 3).interior C) = interior C := by
    have hlevel (i : {i // i ∈ b'}) : |level i.val| < δ⁻¹ := by
      have hlen : (3 : ℝ) < δ⁻¹ :=
        (lt_inv_comm₀ (by norm_num) (neck i.val).eps_pos).mpr
          (by linarith [(neck i.val).eps_small])
      exact ((hnecks i.val (hb'sub i.property)).1).trans_lt hlen
    apply exists_isManifold_of_finite_spatial_neck_levels L.metric
      (fun i : {i // i ∈ b'} => v i.val) (fun i => neck i.val)
      (fun i => level i.val) hlevel (fun _ => Diffeomorph.refl I2 (Sphere 2) ∞)
    · intro i j hij
      simpa only [Diffeomorph.coe_refl, id_eq] using
        hselected i.property j.property (fun heq => hij (Subtype.ext heq))
    · exact hreg
    · intro x hx
      obtain ⟨i, hi, z, hz⟩ := mem_iUnion₂.mp (hfront ▸ hx)
      exact mem_iUnion.mpr ⟨⟨i, hi⟩, z, hz⟩
  have hconnint : IsConnected (interior C) := by
    obtain ⟨chartsC, hmanifoldC, _, _, hinteriorC⟩ := hatlasC
    let _ : ChartedSpace (EuclideanHalfSpace 3) C := chartsC
    let _ : IsManifold (𝓡∂ 3) ∞ C := hmanifoldC
    let _ : ConnectedSpace C := isConnected_iff_connectedSpace.mp hconn
    refine ⟨⟨y, hyint⟩, ?_⟩
    rw [← hinteriorC]
    exact (DifferentialGeometry.Topology.Manifold.isPreconnected_manifold_interior
      (I := 𝓡∂ 3) (M := C)).image Subtype.val continuous_subtype_val.continuousOn
  refine ⟨ι, v, neck, level, b', C, hb', hcompact, hconn, hconnint, hreg, hyint,
    hsub.trans hcomponent, (fun x hx => hscalar x (hsub hx)), hselected, hfront,
    (fun x hx => hfrontier_scalar x (hfrontsub hx)), hatlasC, ?_⟩
  intro i hi
  obtain ⟨hlevel, hsmooth, hscalar, hclose, hsource, _⟩ := hnecks i (hb'sub hi)
  exact ⟨hlevel, hsmooth, hscalar, hclose, hsource⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab


namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem exists_uniform_disjoint_spherical_region_with_low_anchors_of_le :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ η →
      ∃ C2 : ℝ, 1 ≤ C2 ∧ ∀ (P : OrientedThreeStage.{u}) (a s : ℝ)
        (G : P.IncomingSlab a s), ∃ q : ℝ, 0 < q ∧
        ∀ (L : G.TerminalLimitMetric) (A B : ℝ) (y : G.terminalRegularOpen),
          0 < A → A ≤ B → q < 4 * C2 * B →
          metricScalarAt L.metric y ≤ A → ¬ IsCompact (connectedComponent y) →
          ∃ (ι : Type u) (v : ι → G.terminalRegularOpen)
            (neck : ∀ i, SpatialNeck L.metric δ (v i)) (level : ι → ℝ)
            (b : Finset ι) (K : Set G.terminalRegularOpen),
            b.Nonempty ∧ IsCompact K ∧ closure (interior K) = K ∧
            {x : G.terminalRegularOpen | x ∈ connectedComponent y ∧ metricScalarAt L.metric x ≤ A}
              ⊆ interior K ∧ K ⊆ connectedComponent y ∧
            (∀ x ∈ K, metricScalarAt L.metric x ≤ 8 * C2^2 * B) ∧
            (b : Set ι).PairwiseDisjoint
              (fun i => range (fun z : Sphere 2 => (neck i).map (z, level i))) ∧
            frontier K = ⋃ i ∈ b, range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
            (∀ x ∈ frontier K, 2 * B < metricScalarAt L.metric x) ∧
            (∀ x ∈ interior K, ∃ a ∈ connectedComponentIn (interior K) x,
              metricScalarAt L.metric a ≤ A) ∧
            ∀ i ∈ b, |level i| ≤ 3 ∧
              IsSmoothEmbedding I2 I3 ∞ (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
              (∀ z ∈ (univ ×ˢ Icc (-101 : ℝ) 101 : Set Cylinder),
                2 * B < metricScalarAt L.metric ((neck i).map z) ∧
                  metricScalarAt L.metric ((neck i).map z) ≤ 8 * C2^2 * B) ∧
              (neck i).cylindricalChart.metricCloseOn L.metric δ
                {z : (neck i).cylindricalChart.domain | z.val.2 ∈ Icc (-101 : ℝ) 101} ∧
              (∀ z t, t ∈ Icc (-101 : ℝ) 101 → (z, t) ∈ (neck i).cylindricalChart.domain) ∧
              ∃ r σ : ℝ, 0 < r ∧ r ≤ 1 ∧ (σ = 1 ∨ σ = -1) ∧
                (∀ z, ∀ t ∈ Ioo (-r) r, (z, level i + σ * t) ∈ (neck i).map.source) ∧
                (∀ z, ∀ t ∈ Ioo (-r) r,
                  (neck i).map (z, level i + σ * t) ∈ K ↔ t ≤ 0) ∧
                ∀ z, ∀ t ∈ Ioo (-r) r,
                  (neck i).map (z, level i + σ * t) ∈ interior K ↔ t < 0 := by
  obtain ⟨eta, heta, hregion⟩ := exists_uniform_disjoint_spherical_region.{u}
  refine ⟨eta, heta, ?_⟩
  intro δ hδ hδη
  obtain ⟨C2, hC2, hregion⟩ := hregion δ hδ hδη
  refine ⟨C2, hC2, ?_⟩
  intro P a s G
  obtain ⟨q, hq, hregion⟩ := hregion P a s G
  refine ⟨q, hq, ?_⟩
  intro L A B y hA hAB hqB hyA hnoncompact
  obtain ⟨ι, v, neck, level, b, W, _, hW, hregular, hlow, hcomponent, hscalar,
    hdisjoint, hfront, hfrontscalar, hnecks⟩ :=
      hregion L B y (hA.trans_le hAB) hqB (hyA.trans hAB) hnoncompact
  let Low := {z : G.terminalRegularOpen | z ∈ connectedComponent y ∧ metricScalarAt L.metric z ≤ A}
  let R := ⋃ z ∈ Low, connectedComponentIn W z
  let F (i : ι) := range (fun z : Sphere 2 => (neck i).map (z, level i))
  classical
  let b' := b.filter fun i => (F i ∩ R).Nonempty
  have hlevel (i : {i // i ∈ b}) : |level i.val| < δ⁻¹ := by
    have hthree : (3 : ℝ) < δ⁻¹ :=
      (lt_inv_comm₀ (by norm_num) (neck i.val).eps_pos).mpr
        (by linarith [(neck i.val).eps_small])
    exact ((hnecks i.val i.property).1).trans_lt hthree
  have hdisjoint' : Pairwise (fun i j : {i // i ∈ b} => Disjoint (F i.val) (F j.val)) := by
    intro i j hij
    exact hdisjoint i.property j.property (fun h => hij (Subtype.ext h))
  have hfront' : frontier W = ⋃ i : {i // i ∈ b}, F i.val := by
    simpa only [iUnion_subtype] using hfront
  obtain ⟨hRcompact, hRW, hLR, hRregular, hRfront, hanchor, _, hcollars⟩ :=
    spatial_neck_component_union_meeting L.metric (fun i : {i // i ∈ b} => v i.val)
      (fun i => neck i.val) (fun i => level i.val) hlevel hdisjoint' hW hregular hfront'
      (show Low ⊆ interior W from fun z hz => hlow ⟨hz.1, hz.2.trans hAB⟩)
  have hfrontR : frontier R = ⋃ i ∈ b', F i := by
    change frontier R = ⋃ i : {i // i ∈ b},
      ⋃ (_ : (F i.val ∩ R).Nonempty), F i.val at hRfront
    rw [hRfront]
    ext z
    simp only [mem_iUnion, b', Finset.mem_filter, Subtype.exists, exists_prop]
    tauto
  have hlowR : Low ⊆ interior R := hLR
  have hb' : b'.Nonempty := by
    by_contra hn
    have hempty : frontier R = ∅ := by
      rw [hfrontR, Finset.not_nonempty_iff_eq_empty.mp hn]
      simp
    have hall : connectedComponent y ⊆ interior R :=
      isPreconnected_subset_interior_of_meets_of_disjoint_frontier isPreconnected_connectedComponent
        ⟨y, mem_connectedComponent, interior_subset (hlowR ⟨mem_connectedComponent, hyA⟩)⟩
        (by rw [hempty]; exact disjoint_empty _)
    exact hnoncompact (hRcompact.of_isClosed_subset isClosed_connectedComponent
      (hall.trans interior_subset))
  refine ⟨ι, v, neck, level, b', R, hb', hRcompact, hRregular, hlowR,
    hRW.trans hcomponent, fun z hz => hscalar z (hRW hz), ?_, hfrontR, ?_, ?_, ?_⟩
  · intro i hi j hj hij
    exact hdisjoint ((Finset.mem_filter.mp hi).1) ((Finset.mem_filter.mp hj).1) hij
  · intro z hz
    have hzW : z ∈ frontier W := by
      obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (hfrontR ▸ hz)
      exact hfront.symm ▸ mem_iUnion₂.mpr ⟨i, (Finset.mem_filter.mp hi).1, hzi⟩
    exact hfrontscalar z hzW
  · intro z hz
    obtain ⟨a, ha, haLow⟩ := hanchor z hz
    exact ⟨a, ha, haLow.2⟩
  · intro i hi
    have hib : i ∈ b := (Finset.mem_filter.mp hi).1
    obtain ⟨hl, hembed, hband, hclose, hdomain, r, σ, hr, hr1, hσ,
      hsrc, hside, hinside⟩ := hnecks i hib
    have hia : (F i ∩ R).Nonempty := (Finset.mem_filter.mp hi).2
    obtain ⟨hside', hinside'⟩ := hcollars ⟨i, hib⟩ hia r σ hsrc hside hinside
    exact ⟨hl, hembed, hband, hclose, hdomain, r, σ, hr, hr1, hσ, hsrc, hside', hinside'⟩


theorem TerminalLimitMetric.exists_disjoint_spherical_region_with_low_anchors_of_le
    (L : G.TerminalLimitMetric) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ η →
      ∃ C2 q : ℝ, 1 ≤ C2 ∧ 0 < q ∧
        ∀ (A B : ℝ) (y : G.terminalRegularOpen), 0 < A → A ≤ B → q < 4 * C2 * B →
          metricScalarAt L.metric y ≤ A → ¬ IsCompact (connectedComponent y) →
          ∃ (ι : Type u) (v : ι → G.terminalRegularOpen)
            (neck : ∀ i, SpatialNeck L.metric δ (v i)) (level : ι → ℝ)
            (b : Finset ι) (K : Set G.terminalRegularOpen),
            b.Nonempty ∧ IsCompact K ∧ closure (interior K) = K ∧
            {x : G.terminalRegularOpen | x ∈ connectedComponent y ∧ metricScalarAt L.metric x ≤ A}
              ⊆ interior K ∧ K ⊆ connectedComponent y ∧
            (∀ x ∈ K, metricScalarAt L.metric x ≤ 8 * C2^2 * B) ∧
            (b : Set ι).PairwiseDisjoint
              (fun i => range (fun z : Sphere 2 => (neck i).map (z, level i))) ∧
            frontier K = ⋃ i ∈ b, range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
            (∀ x ∈ frontier K, 2 * B < metricScalarAt L.metric x) ∧
            (∀ x ∈ interior K, ∃ a ∈ connectedComponentIn (interior K) x,
              metricScalarAt L.metric a ≤ A) ∧
            ∀ i ∈ b, |level i| ≤ 3 ∧
              IsSmoothEmbedding I2 I3 ∞ (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
              (∀ z ∈ (univ ×ˢ Icc (-101 : ℝ) 101 : Set Cylinder),
                2 * B < metricScalarAt L.metric ((neck i).map z) ∧
                  metricScalarAt L.metric ((neck i).map z) ≤ 8 * C2^2 * B) ∧
              (neck i).cylindricalChart.metricCloseOn L.metric δ
                {z : (neck i).cylindricalChart.domain | z.val.2 ∈ Icc (-101 : ℝ) 101} ∧
              (∀ z t, t ∈ Icc (-101 : ℝ) 101 → (z, t) ∈ (neck i).cylindricalChart.domain) ∧
              ∃ r σ : ℝ, 0 < r ∧ r ≤ 1 ∧ (σ = 1 ∨ σ = -1) ∧
                (∀ z, ∀ t ∈ Ioo (-r) r, (z, level i + σ * t) ∈ (neck i).map.source) ∧
                (∀ z, ∀ t ∈ Ioo (-r) r,
                  (neck i).map (z, level i + σ * t) ∈ K ↔ t ≤ 0) ∧
                ∀ z, ∀ t ∈ Ioo (-r) r,
                  (neck i).map (z, level i + σ * t) ∈ interior K ↔ t < 0 := by
  obtain ⟨eta, heta, hregion⟩ := exists_uniform_disjoint_spherical_region_with_low_anchors_of_le.{u}
  refine ⟨eta, heta, ?_⟩
  intro δ hδ hδη
  obtain ⟨C2, hC2, hregion⟩ := hregion δ hδ hδη
  obtain ⟨q, hq, hregion⟩ := hregion P a s G
  exact ⟨C2, q, hC2, hq, hregion L⟩

theorem TerminalLimitMetric.exists_disjoint_spherical_region_with_low_anchors
    (L : G.TerminalLimitMetric) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ η →
      ∃ C2 q : ℝ, 1 ≤ C2 ∧ 0 < q ∧
        ∀ (A : ℝ) (y : G.terminalRegularOpen), 0 < A → q < 4 * C2 * A →
          metricScalarAt L.metric y ≤ A → ¬ IsCompact (connectedComponent y) →
          ∃ (ι : Type u) (v : ι → G.terminalRegularOpen)
            (neck : ∀ i, SpatialNeck L.metric δ (v i)) (level : ι → ℝ)
            (b : Finset ι) (K : Set G.terminalRegularOpen),
            b.Nonempty ∧ IsCompact K ∧ closure (interior K) = K ∧
            {x : G.terminalRegularOpen | x ∈ connectedComponent y ∧ metricScalarAt L.metric x ≤ A}
              ⊆ interior K ∧ K ⊆ connectedComponent y ∧
            (∀ x ∈ K, metricScalarAt L.metric x ≤ 8 * C2^2 * A) ∧
            (b : Set ι).PairwiseDisjoint
              (fun i => range (fun z : Sphere 2 => (neck i).map (z, level i))) ∧
            frontier K = ⋃ i ∈ b, range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
            (∀ x ∈ frontier K, 2 * A < metricScalarAt L.metric x) ∧
            (∀ x ∈ interior K, ∃ a ∈ connectedComponentIn (interior K) x,
              metricScalarAt L.metric a ≤ A) ∧
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
                  (neck i).map (z, level i + σ * t) ∈ K ↔ t ≤ 0) ∧
                ∀ z, ∀ t ∈ Ioo (-r) r,
                  (neck i).map (z, level i + σ * t) ∈ interior K ↔ t < 0 := by
  obtain ⟨eta, heta, hregion⟩ := L.exists_disjoint_spherical_region_with_low_anchors_of_le
  refine ⟨eta, heta, ?_⟩
  intro δ hδ hδη
  obtain ⟨C2, q, hC2, hq, hregion⟩ := hregion δ hδ hδη
  exact ⟨C2, q, hC2, hq, fun A y hA hqA hyA hnoncompact =>
    hregion A A y hA le_rfl hqA hyA hnoncompact⟩



theorem exists_uniform_disjoint_spherical_region_with_scalar_gap :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ η →
      ∃ C2 : ℝ, 1 ≤ C2 ∧ ∀ C : ℝ, 1 ≤ C → ∀ (P : OrientedThreeStage.{u}) (a s : ℝ)
        (G : P.IncomingSlab a s), ∃ q : ℝ, 0 < q ∧
        ∀ (L : G.TerminalLimitMetric) (A : ℝ) (y : G.terminalRegularOpen),
          0 < A → q < 4 * C2 * (C * A) →
          metricScalarAt L.metric y ≤ A → ¬ IsCompact (connectedComponent y) →
          ∃ (ι : Type u) (v : ι → G.terminalRegularOpen)
            (neck : ∀ i, SpatialNeck L.metric δ (v i)) (level : ι → ℝ)
            (b : Finset ι) (K : Set G.terminalRegularOpen),
            b.Nonempty ∧ IsCompact K ∧ closure (interior K) = K ∧
            {x : G.terminalRegularOpen | x ∈ connectedComponent y ∧ metricScalarAt L.metric x ≤ A}
              ⊆ interior K ∧ K ⊆ connectedComponent y ∧
            (∀ x ∈ K, metricScalarAt L.metric x ≤ 8 * C2^2 * (C * A)) ∧
            (b : Set ι).PairwiseDisjoint
              (fun i => range (fun z : Sphere 2 => (neck i).map (z, level i))) ∧
            frontier K = ⋃ i ∈ b, range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
            (∀ x ∈ frontier K, 2 * (C * A) < metricScalarAt L.metric x) ∧
            (∀ x ∈ interior K, ∃ a ∈ connectedComponentIn (interior K) x,
              metricScalarAt L.metric a ≤ A ∧
              ∀ z ∈ frontier K, C * metricScalarAt L.metric a < metricScalarAt L.metric z) ∧
            ∀ i ∈ b, |level i| ≤ 3 ∧
              IsSmoothEmbedding I2 I3 ∞ (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
              (∀ z ∈ (univ ×ˢ Icc (-101 : ℝ) 101 : Set Cylinder),
                2 * (C * A) < metricScalarAt L.metric ((neck i).map z) ∧
                  metricScalarAt L.metric ((neck i).map z) ≤ 8 * C2^2 * (C * A)) ∧
              (neck i).cylindricalChart.metricCloseOn L.metric δ
                {z : (neck i).cylindricalChart.domain | z.val.2 ∈ Icc (-101 : ℝ) 101} ∧
              (∀ z t, t ∈ Icc (-101 : ℝ) 101 → (z, t) ∈ (neck i).cylindricalChart.domain) ∧
              ∃ r σ : ℝ, 0 < r ∧ r ≤ 1 ∧ (σ = 1 ∨ σ = -1) ∧
                (∀ z, ∀ t ∈ Ioo (-r) r, (z, level i + σ * t) ∈ (neck i).map.source) ∧
                (∀ z, ∀ t ∈ Ioo (-r) r,
                  (neck i).map (z, level i + σ * t) ∈ K ↔ t ≤ 0) ∧
                ∀ z, ∀ t ∈ Ioo (-r) r,
                  (neck i).map (z, level i + σ * t) ∈ interior K ↔ t < 0 := by
  obtain ⟨eta, heta, hmain⟩ := exists_uniform_disjoint_spherical_region_with_low_anchors_of_le.{u}
  refine ⟨eta, heta, ?_⟩
  intro δ hδ hδη
  obtain ⟨C2, hC2, hmain⟩ := hmain δ hδ hδη
  refine ⟨C2, hC2, ?_⟩
  intro C hC P a s G
  obtain ⟨q, hq, hregion⟩ := hmain P a s G
  refine ⟨q, hq, ?_⟩
  intro L A y hA hqA hyA hnoncompact
  have hCA : 0 < C * A := mul_pos (zero_lt_one.trans_le hC) hA
  have hA_CA : A ≤ C * A := le_mul_of_one_le_left hA.le hC
  obtain ⟨ι, v, neck, level, b, K, hb, hK, hregular, hlow, hcomp, hscalar,
    hdisj, hfront, hfrontscalar, hanchor, hnecks⟩ :=
    hregion L A (C * A) y hA hA_CA hqA hyA hnoncompact
  refine ⟨ι, v, neck, level, b, K, hb, hK, hregular, hlow, hcomp, hscalar,
    hdisj, hfront, hfrontscalar, ?_, hnecks⟩
  intro x hx
  obtain ⟨z, hzx, hzA⟩ := hanchor x hx
  refine ⟨z, hzx, hzA, ?_⟩
  intro w hw
  have hmul := mul_le_mul_of_nonneg_left hzA (zero_le_one.trans hC)
  exact hmul.trans_lt (lt_trans (by linarith : C * A < 2 * (C * A)) (hfrontscalar w hw))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
