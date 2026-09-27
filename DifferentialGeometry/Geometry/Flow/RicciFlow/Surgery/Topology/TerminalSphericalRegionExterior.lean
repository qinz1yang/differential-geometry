import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCapCore
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalSphericalRegion
import DifferentialGeometry.Geometry.Neck.SpatialRestriction
noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

theorem exists_uniform_disjoint_spherical_region_with_exterior_alternatives_of_canonical_neighborhoods :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, δ ≤ η →
      ∀ C1 C2 q : ℝ, 0 < q →
      ∀ (P : OrientedThreeStage.{u}) (a s : ℝ) (G : P.IncomingSlab a s)
        (L : G.TerminalLimitMetric),
        (∀ x t, t ∈ Ioo a s → q < G.flow.scalar t x →
          ∃ W : CanonicalWitness G.flow (δ / 4) C1 C2 x t,
            W.capTubeHasNeckChart (δ / 4)) →
        ∀ (A B : ℝ) (y : G.terminalRegularOpen),
          q < B → (2 * C2) * A ≤ B → metricScalarAt L.metric y ≤ B →
          ¬ IsCompact (connectedComponent y) →
          ∃ (ι : Type u) (v : ι → G.terminalRegularOpen)
            (neck : ∀ i, SpatialNeck L.metric δ (v i)) (level : ι → ℝ)
            (b : Finset ι) (W : Set G.terminalRegularOpen),
            b.Nonempty ∧ IsCompact W ∧ closure (interior W) = W ∧
            {x : G.terminalRegularOpen | x ∈ connectedComponent y ∧ metricScalarAt L.metric x ≤ B}
              ⊆ interior W ∧ W ⊆ connectedComponent y ∧
            (∀ x ∈ W, metricScalarAt L.metric x ≤ 8 * C2^2 * B) ∧
            (b : Set ι).PairwiseDisjoint
              (fun i => range (fun z : Sphere 2 => (neck i).map (z, level i))) ∧
            frontier W = ⋃ i ∈ b, range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
            (∀ x ∈ frontier W, 2 * B < metricScalarAt L.metric x) ∧
            (∀ i ∈ b, |level i| ≤ 3 ∧
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
                  (neck i).map (z, level i + σ * t) ∈ W ↔ t ≤ 0) ∧
                ∀ z, ∀ t ∈ Ioo (-r) r,
                  (neck i).map (z, level i + σ * t) ∈ interior W ↔ t < 0) ∧
            ∀ V : Set G.terminalRegularOpen, W ⊆ V →
              ∀ x ∈ connectedComponent y, x ∉ interior V →
                B < metricScalarAt L.metric x ∧
                ∀ (p : G.terminalRegularOpen) (nk : SpatialNeck L.metric δ p)
                  (z : Sphere 2) (level : ℝ), |level| ≤ 4 → nk.map (z, level) = x →
                  Nonempty (SpatialNeck L.metric δ x) ∨
                  ∃ K : CompactDomain G.terminalRegularOpen,
                    Nonempty (CapCore K.carrier) ∧
                    nk.map '' (univ ×ˢ Icc (-4 : ℝ) 4) ⊆ interior K.carrier ∧
                    (∀ w ∈ K.carrier, A < metricScalarAt L.metric w ∧
                      metricScalarAt L.metric x / (2 * C2) < metricScalarAt L.metric w ∧
                        metricScalarAt L.metric w < (2 * C2) * metricScalarAt L.metric x) := by
  obtain ⟨η, hη, hregion⟩ := exists_uniform_disjoint_spherical_region_of_canonical_neighborhoods.{u}
  refine ⟨min η (1 / 8646), lt_min hη (by norm_num), ?_⟩
  intro δ hδη C1 C2 q hq P a s G L hcanonical A B y hqB hAB hyB hnoncompact
  obtain ⟨x, _, hx⟩ := L.exists_scalar_gt_on_connectedComponent_of_not_isCompact y hnoncompact q
  have hhigh := (L.tendsto_metricScalarAt x).eventually (Ioi_mem_nhds hx)
  have htime : ∀ᶠ t in nhdsWithin s (Iio s), t ∈ Ioo a s := Ioo_mem_nhdsLT G.lt
  obtain ⟨t, ht, hqt⟩ := (htime.and hhigh).exists
  obtain ⟨W, _⟩ := hcanonical x.val t ht hqt
  have hC2 : 1 ≤ C2 := W.one_le_comparison_constant
  have hδsmall : δ ≤ 1 / 8646 := hδη.trans (min_le_right _ _)
  let C := 2 * C2
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hB : 0 < B := hq.trans hqB
  have hqscale : q < 4 * C2 * B := by nlinarith
  obtain ⟨ι, v, neck, level, b, W, hb, hW, hreg, hlow, hcomponent,
    hscalar, hdisjoint, hfront, hfrontscalar, hnecks⟩ :=
    hregion δ (hδη.trans (min_le_left _ _)) C1 C2 q P a s G L hcanonical
      B y hB hqscale hyB hnoncompact
  refine ⟨ι, v, neck, level, b, W, hb, hW, hreg, hlow, hcomponent,
    hscalar, hdisjoint, hfront, hfrontscalar, hnecks, ?_⟩
  intro V hWV x hxcomp hxout
  have hxhigh : B < metricScalarAt L.metric x := by
    by_contra hn
    exact hxout (interior_mono hWV (hlow ⟨hxcomp, le_of_not_gt hn⟩))
  refine ⟨hxhigh, ?_⟩
  intro p nk z level hlevel hx
  have hxnoncompact : ¬ IsCompact (connectedComponent x) := by
    rw [← connectedComponent_eq hxcomp]
    exact hnoncompact
  rcases L.spatial_neck_or_cap_core_of_canonical_neighborhoods_of_not_isCompact
      hδsmall hq p x (fun t ht hx => hcanonical x.val t ht hx)
      (hqB.trans hxhigh) hxnoncompact nk z level hlevel hx with hn | hc
  · exact Or.inl hn
  · obtain ⟨K, hmodel, hinside, hband⟩ := hc
    refine Or.inr ⟨K, hmodel, hinside, ?_⟩
    intro w hw
    have hCpos : 0 < C := zero_lt_one.trans_le hC
    have hAx : A < metricScalarAt L.metric x / C :=
      (lt_div_iff₀ hCpos).mpr (by nlinarith)
    exact ⟨hAx.trans (hband w hw).1, hband w hw⟩

theorem exists_uniform_disjoint_spherical_region_with_exterior_alternatives :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ η →
      ∃ C C2 : ℝ, 1 ≤ C ∧ 1 ≤ C2 ∧ ∀ (P : OrientedThreeStage.{u}) (a s : ℝ)
        (G : P.IncomingSlab a s), ∃ q : ℝ, 0 < q ∧
        ∀ (L : G.TerminalLimitMetric) (A B : ℝ) (y : G.terminalRegularOpen),
          q < B → C * A ≤ B → metricScalarAt L.metric y ≤ B →
          ¬ IsCompact (connectedComponent y) →
          ∃ (ι : Type u) (v : ι → G.terminalRegularOpen)
            (neck : ∀ i, SpatialNeck L.metric δ (v i)) (level : ι → ℝ)
            (b : Finset ι) (W : Set G.terminalRegularOpen),
            b.Nonempty ∧ IsCompact W ∧ closure (interior W) = W ∧
            {x : G.terminalRegularOpen | x ∈ connectedComponent y ∧ metricScalarAt L.metric x ≤ B}
              ⊆ interior W ∧ W ⊆ connectedComponent y ∧
            (∀ x ∈ W, metricScalarAt L.metric x ≤ 8 * C2^2 * B) ∧
            (b : Set ι).PairwiseDisjoint
              (fun i => range (fun z : Sphere 2 => (neck i).map (z, level i))) ∧
            frontier W = ⋃ i ∈ b, range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
            (∀ x ∈ frontier W, 2 * B < metricScalarAt L.metric x) ∧
            (∀ i ∈ b, |level i| ≤ 3 ∧
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
                  (neck i).map (z, level i + σ * t) ∈ W ↔ t ≤ 0) ∧
                ∀ z, ∀ t ∈ Ioo (-r) r,
                  (neck i).map (z, level i + σ * t) ∈ interior W ↔ t < 0) ∧
            ∀ V : Set G.terminalRegularOpen, W ⊆ V →
              ∀ x ∈ connectedComponent y, x ∉ interior V →
                B < metricScalarAt L.metric x ∧
                ∀ (p : G.terminalRegularOpen) (nk : SpatialNeck L.metric δ p)
                  (z : Sphere 2) (level : ℝ), |level| ≤ 4 → nk.map (z, level) = x →
                  Nonempty (SpatialNeck L.metric δ x) ∨
                  ∃ K : CompactDomain G.terminalRegularOpen,
                    Nonempty (CapCore K.carrier) ∧
                    nk.map '' (univ ×ˢ Icc (-4 : ℝ) 4) ⊆ interior K.carrier ∧
                    (∀ w ∈ K.carrier, A < metricScalarAt L.metric w ∧
                      metricScalarAt L.metric x / C < metricScalarAt L.metric w ∧
                        metricScalarAt L.metric w < C * metricScalarAt L.metric x) := by
  obtain ⟨eta, heta, hmain⟩ :=
    exists_uniform_disjoint_spherical_region_with_exterior_alternatives_of_canonical_neighborhoods.{u}
  refine ⟨min eta (1 / 8646), lt_min heta (by norm_num), ?_⟩
  intro δ hδ hδη
  have heps : 0 < δ / 4 := by positivity
  have hsmall : δ / 4 < 1 / 11 := by linarith [hδη.trans (min_le_right _ _)]
  obtain ⟨C2, hC2, hcanonical⟩ := exists_uniform_canonical_constants_with_cap_neck_charts.{u} heps hsmall
  refine ⟨2 * C2, C2, by linarith, hC2, ?_⟩
  intro P a s G
  obtain ⟨q, hq, hcanonical⟩ := hcanonical P a s G
  refine ⟨q, hq, ?_⟩
  intro L
  exact hmain δ (hδη.trans (min_le_left _ _)) C2 C2 q hq P a s G L
    (fun x t ht hx => hcanonical x t ⟨ht.1.le, ht.2⟩ hx.le)

theorem exists_uniform_disjoint_spherical_region_on_component_with_exterior_alternatives_of_canonical_neighborhoods :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, δ ≤ η →
      ∀ C1 C2 q : ℝ, 0 < q →
      ∀ (P : OrientedThreeStage.{u}) (a s : ℝ) (G : P.IncomingSlab a s)
        (L : G.TerminalLimitMetric),
        (∀ x t, t ∈ Ioo a s → q < G.flow.scalar t x →
          ∃ W : CanonicalWitness G.flow (δ / 4) C1 C2 x t,
            W.capTubeHasNeckChart (δ / 4)) →
        ∀ (A B : ℝ) (y : G.terminalRegularOpen),
          q < B → (2 * C2) * A ≤ B → metricScalarAt L.metric y ≤ B →
          ¬ IsCompact (connectedComponent y) →
          let U := connectedComponentOpen (I := I3) y
          ∃ (ι : Type u) (_ : Finite ι) (_ : Nonempty ι)
            (v : ι → U) (neck : ∀ i, SpatialNeck (L.metric.restrictOpen U) δ (v i))
            (level : ι → ℝ) (W : Set U),
            IsCompact W ∧ closure (interior W) = W ∧
            {x : U | metricScalarAt (L.metric.restrictOpen U) x ≤ B} ⊆ interior W ∧
            (∀ x ∈ W, metricScalarAt (L.metric.restrictOpen U) x ≤ 8 * C2^2 * B) ∧
            Pairwise (fun i j => Disjoint
              (range (fun z : Sphere 2 => (neck i).map (z, level i)))
              (range (fun z : Sphere 2 => (neck j).map (z, level j)))) ∧
            frontier W = ⋃ i, range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
            (∀ i, |level i| ≤ 3) ∧
            (∀ i, ∃ r σ : ℝ, 0 < r ∧ r ≤ 1 ∧ (σ = 1 ∨ σ = -1) ∧
              (∀ z, ∀ t ∈ Ioo (-r) r, (z, level i + σ * t) ∈ (neck i).map.source) ∧
              (∀ z, ∀ t ∈ Ioo (-r) r,
                (neck i).map (z, level i + σ * t) ∈ W ↔ t ≤ 0) ∧
              ∀ z, ∀ t ∈ Ioo (-r) r,
                (neck i).map (z, level i + σ * t) ∈ interior W ↔ t < 0) ∧
            (∀ x ∈ frontier W, 2 * B < metricScalarAt (L.metric.restrictOpen U) x) ∧
            ∀ V : Set U, W ⊆ V → ∀ x : U, x ∉ interior V →
              B < metricScalarAt (L.metric.restrictOpen U) x ∧
              ∀ (p : U) (nk : SpatialNeck (L.metric.restrictOpen U) δ p)
                (z : Sphere 2) (level : ℝ), |level| ≤ 4 → nk.map (z, level) = x →
                Nonempty (SpatialNeck (L.metric.restrictOpen U) δ x) ∨
                ∃ K : CompactDomain U,
                  Nonempty (CapCore K.carrier) ∧
                  nk.map '' (univ ×ˢ Icc (-4 : ℝ) 4) ⊆ interior K.carrier ∧
                  (∀ w ∈ K.carrier, A < metricScalarAt (L.metric.restrictOpen U) w ∧
                    metricScalarAt (L.metric.restrictOpen U) x / (2 * C2) <
                      metricScalarAt (L.metric.restrictOpen U) w ∧
                    metricScalarAt (L.metric.restrictOpen U) w <
                      (2 * C2) * metricScalarAt (L.metric.restrictOpen U) x) := by
  obtain ⟨η, hη, hmain⟩ :=
    exists_uniform_disjoint_spherical_region_with_exterior_alternatives_of_canonical_neighborhoods.{u}
  refine ⟨η, hη, ?_⟩
  intro δ hδη C1 C2 q hq P a s G L hcanonical A B y hqB hAB hyB hnoncompact U
  obtain ⟨ι, v, neck, level, b, W₀, hb, hW₀, hreg₀, hlow₀, hcomponent,
    hscalar₀, hdisjoint₀, hfront₀, hfrontscalar₀, hgeometry, hmodels⟩ :=
    hmain δ hδη C1 C2 q hq P a s G L hcanonical A B y hqB hAB hyB hnoncompact
  have hlevel (i : ι) (hi : i ∈ b) : |level i| < δ⁻¹ := by
    have hlen : (3 : ℝ) < δ⁻¹ :=
      (lt_inv_comm₀ (by norm_num) (neck i).eps_pos).mpr
        (by linarith [(neck i).eps_small])
    exact ((hgeometry i hi).1).trans_lt hlen
  obtain ⟨v', neck', hpoint, hcenter, hmap, hcompact, hregular, hinterior,
    hfront, hdisjoint⟩ := exists_spatial_neck_frontier_on_connectedComponent b v neck level
      hlevel y hW₀ hreg₀ hcomponent hfront₀ hdisjoint₀
  let W : Set U := Subtype.val ⁻¹' W₀
  let _ : Nonempty {i // i ∈ b} := by
    obtain ⟨i, hi⟩ := hb
    exact ⟨⟨i, hi⟩⟩
  refine ⟨{i // i ∈ b}, inferInstance, inferInstance, v', neck',
    (fun i => level i.val), W, hcompact, hregular, ?_, ?_, hdisjoint, hfront,
    (fun i => (hgeometry i.val i.property).1), ?_, ?_, ?_⟩
  · intro x hx
    rw [hinterior]
    apply hlow₀
    refine ⟨x.property, ?_⟩
    change metricScalarAt (L.metric.restrictOpen U) x ≤ B at hx
    simpa only [DifferentialGeometry.CheegerGromovCompactness.metricScalarAt_restrictOpen] using hx
  · intro x hx
    simpa only [DifferentialGeometry.CheegerGromovCompactness.metricScalarAt_restrictOpen] using
      hscalar₀ x.val hx
  · intro i
    obtain ⟨hlev, _, _, _, _, r, σ, hr, hr1, hσ, _, hside, hint⟩ :=
      hgeometry i.val i.property
    have hlen : (4 : ℝ) < δ⁻¹ :=
      (lt_inv_comm₀ (by norm_num) (neck i.val).eps_pos).mpr
        (by linarith [(neck i.val).eps_small])
    have hwindow (z : Sphere 2) (t : ℝ) (ht : t ∈ Ioo (-r) r) :
        (z, level i.val + σ * t) ∈ univ ×ˢ Ioo (-δ⁻¹) δ⁻¹ := by
      refine ⟨mem_univ _, ?_⟩
      rcases hσ with hσ | hσ
      · rw [hσ, one_mul]
        constructor <;> linarith [(abs_le.mp hlev).1, (abs_le.mp hlev).2, ht.1, ht.2]
      · rw [hσ, neg_one_mul]
        constructor <;> linarith [(abs_le.mp hlev).1, (abs_le.mp hlev).2, ht.1, ht.2]
    refine ⟨r, σ, hr, hr1, hσ, ?_, ?_, ?_⟩
    · intro z t ht
      exact (neck' i).domain (hwindow z t ht)
    · intro z t ht
      change ((neck' i).map (z, level i.val + σ * t) : G.terminalRegularOpen) ∈ W₀ ↔ t ≤ 0
      rw [hmap i _ (hwindow z t ht)]
      exact hside z t ht
    · intro z t ht
      rw [hinterior]
      change ((neck' i).map (z, level i.val + σ * t) : G.terminalRegularOpen) ∈ interior W₀ ↔ t < 0
      rw [hmap i _ (hwindow z t ht)]
      exact hint z t ht
  · intro x hx
    have hx₀ : x.val ∈ frontier W₀ := by
      have heq := U.isOpenEmbedding'.isOpenMap.preimage_frontier_eq_frontier_preimage
        continuous_subtype_val W₀
      exact heq.superset hx
    simpa only [DifferentialGeometry.CheegerGromovCompactness.metricScalarAt_restrictOpen] using
      hfrontscalar₀ x.val hx₀
  · intro V hWV x hxout
    let V₀ : Set G.terminalRegularOpen := Subtype.val '' V
    have hW₀V₀ : W₀ ⊆ V₀ := by
      intro w hw
      exact ⟨⟨w, hcomponent hw⟩, hWV hw, rfl⟩
    have hxout₀ : x.val ∉ interior V₀ := by
      intro hxint
      apply hxout
      have heq := U.isOpenEmbedding'.isOpenMap.preimage_interior_eq_interior_preimage
        continuous_subtype_val V₀
      have hxpre : x ∈ interior ((Subtype.val : U → G.terminalRegularOpen) ⁻¹' V₀) :=
        heq ▸ hxint
      simpa only [V₀, preimage_image_eq _ Subtype.val_injective] using hxpre
    obtain ⟨hxhigh, hmodel⟩ := hmodels V₀ hW₀V₀ x.val x.property hxout₀
    refine ⟨?_, ?_⟩
    · simpa only [DifferentialGeometry.CheegerGromovCompactness.metricScalarAt_restrictOpen] using hxhigh
    · intro p nk z height hheight hx
      obtain ⟨nk₀, _, hnkmap, _, _, _⟩ := nk.exists_of_restrictOpen
      have hx₀ : nk₀.map (z, height) = x.val := by rw [hnkmap, hx]
      rcases hmodel p.val nk₀ z height hheight hx₀ with hn | hc
      · obtain ⟨newNeck⟩ := hn
        have hcomp : connectedComponent x.val = connectedComponent y :=
          (connectedComponent_eq x.property).symm
        have hcapture : newNeck.map '' (univ ×ˢ Ioo (-δ⁻¹) δ⁻¹) ⊆ U := by
          change _ ⊆ connectedComponent y
          rw [← hcomp]
          exact newNeck.controlled_range_subset_connectedComponent
        exact Or.inl ⟨newNeck.restrictOpen hcapture⟩
      · obtain ⟨K₀, ⟨model⟩, hinside, hscalar⟩ := hc
        have hxK : x.val ∈ K₀.carrier := interior_subset (hinside
          ⟨(z, height), ⟨mem_univ _, abs_le.mp hheight⟩, hx₀⟩)
        have hKU : K₀.carrier ⊆ U := by
          change K₀.carrier ⊆ connectedComponent y
          rw [← (connectedComponent_eq x.property).symm]
          exact K₀.connected.subset_connectedComponent hxK
        let K := K₀.restrictOpen U hKU
        refine Or.inr ⟨K, model.nonempty_preimage_open U hKU, ?_, ?_⟩
        · rw [CompactDomain.interior_restrictOpen_carrier]
          rintro w ⟨v, hv, rfl⟩
          exact hinside ⟨v, hv, hnkmap v⟩
        · intro w hw
          simpa only [DifferentialGeometry.CheegerGromovCompactness.metricScalarAt_restrictOpen] using
            hscalar w.val hw

theorem exists_uniform_disjoint_spherical_region_on_component_with_exterior_alternatives :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ η →
      ∃ C C2 : ℝ, 1 ≤ C ∧ 1 ≤ C2 ∧ ∀ (P : OrientedThreeStage.{u}) (a s : ℝ)
        (G : P.IncomingSlab a s), ∃ q : ℝ, 0 < q ∧
        ∀ (L : G.TerminalLimitMetric) (A B : ℝ) (y : G.terminalRegularOpen),
          q < B → C * A ≤ B → metricScalarAt L.metric y ≤ B →
          ¬ IsCompact (connectedComponent y) →
          let U := connectedComponentOpen (I := I3) y
          ∃ (ι : Type u) (_ : Finite ι) (_ : Nonempty ι)
            (v : ι → U) (neck : ∀ i, SpatialNeck (L.metric.restrictOpen U) δ (v i))
            (level : ι → ℝ) (W : Set U),
            IsCompact W ∧ closure (interior W) = W ∧
            {x : U | metricScalarAt (L.metric.restrictOpen U) x ≤ B} ⊆ interior W ∧
            (∀ x ∈ W, metricScalarAt (L.metric.restrictOpen U) x ≤ 8 * C2^2 * B) ∧
            Pairwise (fun i j => Disjoint
              (range (fun z : Sphere 2 => (neck i).map (z, level i)))
              (range (fun z : Sphere 2 => (neck j).map (z, level j)))) ∧
            frontier W = ⋃ i, range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
            (∀ i, |level i| ≤ 3) ∧
            (∀ i, ∃ r σ : ℝ, 0 < r ∧ r ≤ 1 ∧ (σ = 1 ∨ σ = -1) ∧
              (∀ z, ∀ t ∈ Ioo (-r) r, (z, level i + σ * t) ∈ (neck i).map.source) ∧
              (∀ z, ∀ t ∈ Ioo (-r) r,
                (neck i).map (z, level i + σ * t) ∈ W ↔ t ≤ 0) ∧
              ∀ z, ∀ t ∈ Ioo (-r) r,
                (neck i).map (z, level i + σ * t) ∈ interior W ↔ t < 0) ∧
            (∀ x ∈ frontier W, 2 * B < metricScalarAt (L.metric.restrictOpen U) x) ∧
            ∀ V : Set U, W ⊆ V → ∀ x : U, x ∉ interior V →
              B < metricScalarAt (L.metric.restrictOpen U) x ∧
              ∀ (p : U) (nk : SpatialNeck (L.metric.restrictOpen U) δ p)
                (z : Sphere 2) (level : ℝ), |level| ≤ 4 → nk.map (z, level) = x →
                Nonempty (SpatialNeck (L.metric.restrictOpen U) δ x) ∨
                ∃ K : CompactDomain U,
                  Nonempty (CapCore K.carrier) ∧
                  nk.map '' (univ ×ˢ Icc (-4 : ℝ) 4) ⊆ interior K.carrier ∧
                  (∀ w ∈ K.carrier, A < metricScalarAt (L.metric.restrictOpen U) w ∧
                    metricScalarAt (L.metric.restrictOpen U) x / C <
                      metricScalarAt (L.metric.restrictOpen U) w ∧
                    metricScalarAt (L.metric.restrictOpen U) w <
                      C * metricScalarAt (L.metric.restrictOpen U) x) := by
  obtain ⟨eta, heta, hmain⟩ :=
    exists_uniform_disjoint_spherical_region_on_component_with_exterior_alternatives_of_canonical_neighborhoods.{u}
  refine ⟨min eta (1 / 8646), lt_min heta (by norm_num), ?_⟩
  intro δ hδ hδη
  have heps : 0 < δ / 4 := by positivity
  have hsmall : δ / 4 < 1 / 11 := by linarith [hδη.trans (min_le_right _ _)]
  obtain ⟨C2, hC2, hcanonical⟩ := exists_uniform_canonical_constants_with_cap_neck_charts.{u} heps hsmall
  refine ⟨2 * C2, C2, by linarith, hC2, ?_⟩
  intro P a s G
  obtain ⟨q, hq, hcanonical⟩ := hcanonical P a s G
  refine ⟨q, hq, ?_⟩
  intro L
  exact hmain δ (hδη.trans (min_le_left _ _)) C2 C2 q hq P a s G L
    (fun x t ht hx => hcanonical x t ⟨ht.1.le, ht.2⟩ hx.le)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
