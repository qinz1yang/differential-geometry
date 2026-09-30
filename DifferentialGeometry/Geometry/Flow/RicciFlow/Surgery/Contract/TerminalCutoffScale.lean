import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.Terminal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalSphericalBarrierCover
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalSphericalRegionExterior
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoffRemainingFields

noncomputable section
open Set Manifold
open DifferentialGeometry.Topology (SmoothTwoSidedCollar)
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

namespace OneStepIncoming

def withNeckRadius (D : OneStepIncoming.{u}) (ρ : ℝ → ℝ)
    (hρ : ∀ t, 0 ≤ t → 0 < ρ t) : OneStepIncoming.{u} :=
  { D with parameters := D.parameters.withNeckRadius ρ hρ }

@[simp] theorem withNeckRadius_slab (D : OneStepIncoming.{u}) (ρ : ℝ → ℝ)
    (hρ : ∀ t, 0 ≤ t → 0 < ρ t) : (D.withNeckRadius ρ hρ).slab = D.slab := rfl

@[simp] theorem withNeckRadius_terminal (D : OneStepIncoming.{u}) (ρ : ℝ → ℝ)
    (hρ : ∀ t, 0 ≤ t → 0 < ρ t) : (D.withNeckRadius ρ hρ).terminal = D.terminal := rfl

@[simp] theorem withNeckRadius_delta (D : OneStepIncoming.{u}) (ρ : ℝ → ℝ)
    (hρ : ∀ t, 0 ≤ t → 0 < ρ t) :
    (D.withNeckRadius ρ hρ).parameters.delta = D.parameters.delta := rfl

@[simp] theorem withNeckRadius_neckRadius (D : OneStepIncoming.{u}) (ρ : ℝ → ℝ)
    (hρ : ∀ t, 0 ≤ t → 0 < ρ t) :
    (D.withNeckRadius ρ hρ).parameters.neckRadius = ρ := rfl

theorem hasRecenterConstants_withNeckRadius (D : OneStepIncoming.{u}) (ρ : ℝ → ℝ)
    (hρ : ∀ t, 0 ≤ t → 0 < ρ t) (h : HasRecenterConstants.{u} D.parameters) :
    HasRecenterConstants.{u} (D.withNeckRadius ρ hρ).parameters :=
  h.withNeckRadius hρ


theorem exists_neckRadius_finite_spherical_barrier_cover
    {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 20000) :
    ∃ C2 : ℝ, 1 ≤ C2 ∧ ∀ D : OneStepIncoming.{u},
      ∃ (ρ : ℝ → ℝ) (hρ : ∀ t, 0 ≤ t → 0 < ρ t),
        (∀ t, 0 ≤ t → ρ t ≤ D.parameters.neckRadius t) ∧
        (Antitone D.parameters.neckRadius → Antitone ρ) ∧
        (AntitoneOn D.parameters.neckRadius (Ici 0) → AntitoneOn ρ (Ici 0)) ∧
        let D' := D.withNeckRadius ρ hρ
        let A := ((D'.parameters.delta D'.endTime *
          D'.parameters.neckRadius D'.endTime) ^ 2)⁻¹
        ∀ y : D'.slab.terminalRegularOpen, metricScalarAt D'.terminal.metric y ≤ A →
          ¬ IsCompact (connectedComponent y) →
        ∃ (s : Finset {z : D'.slab.terminalRegularOpen //
            z ∈ connectedComponent y ∧ metricScalarAt D'.terminal.metric z = 4 * C2 * A})
          (K : {z : D'.slab.terminalRegularOpen //
            z ∈ connectedComponent y ∧ metricScalarAt D'.terminal.metric z = 4 * C2 * A} →
              CompactDomain D'.slab.terminalRegularOpen),
          s.Nonempty ∧
          {z : D'.slab.terminalRegularOpen | z ∈ connectedComponent y ∧ metricScalarAt D'.terminal.metric z = 4 * C2 * A} ⊆
            ⋃ p ∈ s, interior (K p).carrier ∧
          (∀ p ∈ s, p.val ∈ interior (K p).carrier ∧ (K p).carrier ⊆ connectedComponent y ∧
            (∀ z ∈ (K p).carrier, 2 * A < metricScalarAt D'.terminal.metric z ∧
              metricScalarAt D'.terminal.metric z ≤ 8 * C2 ^ 2 * A) ∧
            ∃ (v : D'.slab.terminalRegularOpen) (nk : SpatialNeck D'.terminal.metric η v),
          (∀ z ∈ (univ ×ˢ Icc (-101 : ℝ) 101 : Set Cylinder),
            2 * A < metricScalarAt D'.terminal.metric (nk.map z) ∧ metricScalarAt D'.terminal.metric (nk.map z) ≤ 8 * C2 ^ 2 * A) ∧
          nk.cylindricalChart.metricCloseOn D'.terminal.metric η
            {z : nk.cylindricalChart.domain | z.val.2 ∈ Icc (-101 : ℝ) 101} ∧
          (∀ q z, z ∈ Icc (-101 : ℝ) 101 → (q, z) ∈ nk.cylindricalChart.domain) ∧
          (((K p).carrier = nk.map '' (univ ×ˢ Icc (-3 : ℝ) 3) ∧
            frontier (K p).carrier = range (fun q : Sphere 2 => nk.map (q, -3)) ∪
              range (fun q : Sphere 2 => nk.map (q, 3)) ∧
            Disjoint (range (fun q : Sphere 2 => nk.map (q, -3)))
              (range (fun q : Sphere 2 => nk.map (q, 3))) ∧
            (∀ b ∈ ({-3, 3} : Set ℝ), IsSmoothEmbedding I2 I3 ∞ (fun q : Sphere 2 => nk.map (q, b))) ∧
            ∃ (cneg : SmoothTwoSidedCollar I2 I3 (fun q : Sphere 2 => nk.map (q, -3)))
              (cpos : SmoothTwoSidedCollar I2 I3 (fun q : Sphere 2 => nk.map (q, 3))),
              cneg.radius < 1 ∧ cpos.radius < 1 ∧
              (∀ q, cneg.toFun q = nk.map (q.1, -3 - (q.2 : ℝ)) ∧
                (cneg.toFun q ∈ (K p).carrier ↔ (q.2 : ℝ) ≤ 0)) ∧
              (∀ q, cpos.toFun q = nk.map (q.1, 3 + (q.2 : ℝ)) ∧
                (cpos.toFun q ∈ (K p).carrier ↔ (q.2 : ℝ) ≤ 0))) ∨
          (frontier (K p).carrier = range (fun q : Sphere 2 => nk.map (q, 1 / 2)) ∧
            IsSmoothEmbedding I2 I3 ∞ (fun q : Sphere 2 => nk.map (q, 1 / 2)) ∧
            ∃ c : SmoothTwoSidedCollar I2 I3 (fun q : Sphere 2 => nk.map (q, 1 / 2)),
              c.radius < 1 / 4 ∧ ∀ q,
                c.toFun q = nk.map (q.1, 1 / 2 + (q.2 : ℝ)) ∧
                  (c.toFun q ∈ (K p).carrier ↔ (q.2 : ℝ) ≤ 0)))) ∧
          IsCompact (⋃ p ∈ s, frontier (K p).carrier) ∧
          Disjoint {z : D'.slab.terminalRegularOpen | metricScalarAt D'.terminal.metric z ≤ A}
            (⋃ p ∈ s, frontier (K p).carrier) := by
  obtain ⟨C2, hC2, hbarrier⟩ :=
    OrientedThreeStage.IncomingSlab.exists_uniform_finite_spherical_barrier_cover.{u} hη hηsmall
  refine ⟨C2, hC2, ?_⟩
  intro D
  obtain ⟨q, _, hcover⟩ := hbarrier D.stage D.startTime D.endTime D.slab
  have htime : 0 ≤ D.endTime := D.startTime_nonneg.trans D.startTime_lt_endTime.le
  have hC : 0 < 4 * C2 := by linarith
  obtain ⟨ρ, hρ, hρle, hmono, hmonoOn, hscale⟩ :=
    D.parameters.exists_neckRadius_le_cutoff_scale_gt htime hC q
  refine ⟨ρ, hρ, hρle, hmono, hmonoOn, ?_⟩
  let D' := D.withNeckRadius ρ hρ
  let A := ((D'.parameters.delta D'.endTime *
    D'.parameters.neckRadius D'.endTime) ^ 2)⁻¹
  have hA : 0 < A := inv_pos.mpr (sq_pos_of_pos
    (mul_pos (D.parameters.delta_pos D.endTime htime) (hρ D.endTime htime)))
  dsimp only
  intro y hy hnoncompact
  exact hcover D.terminal A y hA hscale hy hnoncompact

theorem exists_neckRadius_spherical_region_with_exterior_alternatives_of_canonical_neighborhoods :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ η →
      ∀ C1 C2 q : ℝ, 1 ≤ C2 → 0 < q →
      ∀ D : OneStepIncoming.{u},
        (∀ x t, t ∈ Ioo D.startTime D.endTime → q < D.slab.flow.scalar t x →
          ∃ W : CanonicalWitness D.slab.flow (δ / 4) C1 C2 x t,
            W.capTubeHasNeckChart (δ / 4)) →
        ∀ q' : ℝ, q ≤ q' →
        ∃ (ρ : ℝ → ℝ) (hρ : ∀ t, 0 ≤ t → 0 < ρ t),
          (∀ t, 0 ≤ t → ρ t ≤ D.parameters.neckRadius t) ∧
          (Antitone D.parameters.neckRadius → Antitone ρ) ∧
          (AntitoneOn D.parameters.neckRadius (Ici 0) → AntitoneOn ρ (Ici 0)) ∧
          (HasRecenterConstants.{u} D.parameters →
            HasRecenterConstants.{u} (D.withNeckRadius ρ hρ).parameters) ∧
          D.parameters.delta D.endTime * ρ D.endTime ≤ D.parameters.protectedRadius D.endTime ∧
          q' < (2 * C2) * ((D.parameters.delta D.endTime * ρ D.endTime)^2)⁻¹ ∧
          ((D.parameters.delta D.endTime * ρ D.endTime)^2)⁻¹ ≤
            max (max ((D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime)^2)⁻¹
              ((D.parameters.protectedRadius D.endTime)^2)⁻¹) (4 * (max q' 0 + 1) / (2 * C2)) ∧
          let D' := D.withNeckRadius ρ hρ
          let A := ((D'.parameters.delta D'.endTime * D'.parameters.neckRadius D'.endTime) ^ 2)⁻¹
          ∀ y : D'.slab.terminalRegularOpen, metricScalarAt D'.terminal.metric y ≤ A →
            ¬ IsCompact (connectedComponent y) →
            let U := connectedComponentOpen (I := I3) y
            ∃ (ι : Type u) (_ : Finite ι) (_ : Nonempty ι)
              (v : ι → U) (neck : ∀ i, SpatialNeck (D'.terminal.metric.restrictOpen U) δ (v i))
              (level : ι → ℝ) (W : Set U),
              IsCompact W ∧ closure (interior W) = W ∧
              {x : U | metricScalarAt (D'.terminal.metric.restrictOpen U) x ≤ (2 * C2) * A} ⊆ interior W ∧
              {x : U | metricScalarAt (D'.terminal.metric.restrictOpen U) x ≤
                ((D.parameters.protectedRadius D.endTime) ^ 2)⁻¹} ⊆ interior W ∧
              (∀ x ∈ W, metricScalarAt (D'.terminal.metric.restrictOpen U) x ≤ (8 * C2 ^ 2 * (2 * C2)) * A) ∧
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
              (∀ x ∈ frontier W, 2 * ((2 * C2) * A) < metricScalarAt (D'.terminal.metric.restrictOpen U) x) ∧
              ∀ V : Set U, W ⊆ V → ∀ x : U, x ∉ interior V →
                (2 * C2) * A < metricScalarAt (D'.terminal.metric.restrictOpen U) x ∧
                ∀ (p : U) (nk : SpatialNeck (D'.terminal.metric.restrictOpen U) δ p)
                  (z : Sphere 2) (level : ℝ), |level| ≤ 4 → nk.map (z, level) = x →
                  Nonempty (SpatialNeck (D'.terminal.metric.restrictOpen U) δ x) ∨
                  ∃ K : CompactDomain U,
                    Nonempty (CapCore K.carrier) ∧
                    nk.map '' (univ ×ˢ Icc (-4 : ℝ) 4) ⊆ interior K.carrier ∧
                    (∀ w ∈ K.carrier, A < metricScalarAt (D'.terminal.metric.restrictOpen U) w ∧
                      metricScalarAt (D'.terminal.metric.restrictOpen U) x / (2 * C2) <
                        metricScalarAt (D'.terminal.metric.restrictOpen U) w ∧
                      metricScalarAt (D'.terminal.metric.restrictOpen U) w <
                        (2 * C2) * metricScalarAt (D'.terminal.metric.restrictOpen U) x) := by
  obtain ⟨η, hη, hmain⟩ :=
    OrientedThreeStage.IncomingSlab.exists_uniform_disjoint_spherical_region_on_component_with_exterior_alternatives_of_canonical_neighborhoods.{u}
  refine ⟨η, hη, ?_⟩
  intro δ hδ hδη C1 C2 q hC2 hq D hcanonical q' hqq'
  let C := 2 * C2
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hs : 0 ≤ D.endTime := D.startTime_nonneg.trans D.startTime_lt_endTime.le
  have hd : 0 < D.parameters.delta D.endTime := D.parameters.delta_pos _ hs
  obtain ⟨ρ, hρ, hρle, hmono, hmonoOn, hprotect, hscale, hscaleBound⟩ :=
    D.parameters.exists_neckRadius_le_protected_cutoff_scale_gt_with_bound hs hCpos q'
  refine ⟨ρ, hρ, hρle, hmono, hmonoOn,
    (fun h => h.withNeckRadius hρ), hprotect, hscale, hscaleBound, ?_⟩
  let D' := D.withNeckRadius ρ hρ
  let A := ((D'.parameters.delta D'.endTime * D'.parameters.neckRadius D'.endTime) ^ 2)⁻¹
  have hprod : 0 < D.parameters.delta D.endTime * ρ D.endTime := mul_pos hd (hρ _ hs)
  have hA : 0 < A := inv_pos.mpr (sq_pos_of_pos hprod)
  have hAle : A ≤ C * A := by nlinarith
  have hprotected : ((D.parameters.protectedRadius D.endTime) ^ 2)⁻¹ ≤ A := by
    apply inv_anti₀ (sq_pos_of_pos hprod)
    nlinarith
  dsimp only
  intro y hy hnoncompact
  obtain ⟨ι, hi, hne, v, neck, level, W, hW, hreg, hlow, hupper,
    hdisjoint, hfront, hlevel, hcollar, hfrontscalar, hexterior⟩ :=
    hmain δ hδη C1 C2 q hq D.stage D.startTime D.endTime D.slab D.terminal
      hcanonical A (C * A) y (hqq'.trans_lt hscale) le_rfl (hy.trans hAle) hnoncompact
  refine ⟨ι, hi, hne, v, neck, level, W, hW, hreg, hlow,
    (fun x hx => hlow (hx.trans (hprotected.trans hAle))), ?_,
    hdisjoint, hfront, hlevel, hcollar, hfrontscalar, hexterior⟩
  intro x hx
  exact (hupper x hx).trans_eq (by change 8 * C2^2 * (C * A) = 8 * C2^2 * C * A; ring)

theorem exists_neckRadius_disjoint_spherical_region_with_exterior_alternatives_and_scale_bound :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ η →
      ∃ C Λ : ℝ, 1 ≤ C ∧ 1 ≤ Λ ∧ ∀ D : OneStepIncoming.{u},
        ∃ q : ℝ, 0 < q ∧ ∀ q' : ℝ, q ≤ q' →
        ∃ (ρ : ℝ → ℝ) (hρ : ∀ t, 0 ≤ t → 0 < ρ t),
          (∀ t, 0 ≤ t → ρ t ≤ D.parameters.neckRadius t) ∧
          (Antitone D.parameters.neckRadius → Antitone ρ) ∧
          (AntitoneOn D.parameters.neckRadius (Ici 0) → AntitoneOn ρ (Ici 0)) ∧
          (HasRecenterConstants.{u} D.parameters →
            HasRecenterConstants.{u} (D.withNeckRadius ρ hρ).parameters) ∧
          D.parameters.delta D.endTime * ρ D.endTime ≤ D.parameters.protectedRadius D.endTime ∧
          q' < C * ((D.parameters.delta D.endTime * ρ D.endTime)^2)⁻¹ ∧
          ((D.parameters.delta D.endTime * ρ D.endTime)^2)⁻¹ ≤
            max (max ((D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime)^2)⁻¹
              ((D.parameters.protectedRadius D.endTime)^2)⁻¹) (4 * (max q' 0 + 1) / C) ∧
          let D' := D.withNeckRadius ρ hρ
          let A := ((D'.parameters.delta D'.endTime * D'.parameters.neckRadius D'.endTime) ^ 2)⁻¹
          ∀ y : D'.slab.terminalRegularOpen, metricScalarAt D'.terminal.metric y ≤ A →
            ¬ IsCompact (connectedComponent y) →
            let U := connectedComponentOpen (I := I3) y
            ∃ (ι : Type u) (_ : Finite ι) (_ : Nonempty ι)
              (v : ι → U) (neck : ∀ i, SpatialNeck (D'.terminal.metric.restrictOpen U) δ (v i))
              (level : ι → ℝ) (W : Set U),
              IsCompact W ∧ closure (interior W) = W ∧
              {x : U | metricScalarAt (D'.terminal.metric.restrictOpen U) x ≤ C * A} ⊆ interior W ∧
              {x : U | metricScalarAt (D'.terminal.metric.restrictOpen U) x ≤
                ((D.parameters.protectedRadius D.endTime) ^ 2)⁻¹} ⊆ interior W ∧
              (∀ x ∈ W, metricScalarAt (D'.terminal.metric.restrictOpen U) x ≤ Λ * A) ∧
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
              (∀ x ∈ frontier W, 2 * (C * A) < metricScalarAt (D'.terminal.metric.restrictOpen U) x) ∧
              ∀ V : Set U, W ⊆ V → ∀ x : U, x ∉ interior V →
                C * A < metricScalarAt (D'.terminal.metric.restrictOpen U) x ∧
                ∀ (p : U) (nk : SpatialNeck (D'.terminal.metric.restrictOpen U) δ p)
                  (z : Sphere 2) (level : ℝ), |level| ≤ 4 → nk.map (z, level) = x →
                  Nonempty (SpatialNeck (D'.terminal.metric.restrictOpen U) δ x) ∨
                  ∃ K : CompactDomain U,
                    Nonempty (CapCore K.carrier) ∧
                    nk.map '' (univ ×ˢ Icc (-4 : ℝ) 4) ⊆ interior K.carrier ∧
                    (∀ w ∈ K.carrier, A < metricScalarAt (D'.terminal.metric.restrictOpen U) w ∧
                      metricScalarAt (D'.terminal.metric.restrictOpen U) x / C <
                        metricScalarAt (D'.terminal.metric.restrictOpen U) w ∧
                      metricScalarAt (D'.terminal.metric.restrictOpen U) w <
                        C * metricScalarAt (D'.terminal.metric.restrictOpen U) x) := by
  obtain ⟨eta, heta, hmain⟩ :=
    exists_neckRadius_spherical_region_with_exterior_alternatives_of_canonical_neighborhoods.{u}
  refine ⟨min eta (1 / 8646), lt_min heta (by norm_num), ?_⟩
  intro δ hδ hδη
  have heps : 0 < δ / 4 := by positivity
  have hsmall : δ / 4 < 1 / 11 := by linarith [hδη.trans (min_le_right _ _)]
  obtain ⟨C2, hC2, hcanonical⟩ :=
    OrientedThreeStage.IncomingSlab.exists_uniform_canonical_constants_with_cap_neck_charts.{u} heps hsmall
  have hΛ : 1 ≤ 8 * C2 ^ 2 * (2 * C2) := by
    have hsq : 1 ≤ C2 ^ 2 := by nlinarith
    nlinarith
  refine ⟨2 * C2, 8 * C2 ^ 2 * (2 * C2), by linarith, hΛ, ?_⟩
  intro D
  obtain ⟨q, hq, hcanonical⟩ := hcanonical D.stage D.startTime D.endTime D.slab
  refine ⟨q, hq, ?_⟩
  exact hmain δ hδ (hδη.trans (min_le_left _ _)) C2 C2 q hC2 hq D
    (fun x t ht hx => hcanonical x t ⟨ht.1.le, ht.2⟩ hx.le)

theorem exists_neckRadius_disjoint_spherical_region_with_exterior_alternatives :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ η →
      ∃ C Λ : ℝ, 1 ≤ C ∧ 1 ≤ Λ ∧ ∀ D : OneStepIncoming.{u},
        ∃ (ρ : ℝ → ℝ) (hρ : ∀ t, 0 ≤ t → 0 < ρ t),
          (∀ t, 0 ≤ t → ρ t ≤ D.parameters.neckRadius t) ∧
          (Antitone D.parameters.neckRadius → Antitone ρ) ∧
          (AntitoneOn D.parameters.neckRadius (Ici 0) → AntitoneOn ρ (Ici 0)) ∧
          (HasRecenterConstants.{u} D.parameters →
            HasRecenterConstants.{u} (D.withNeckRadius ρ hρ).parameters) ∧
          D.parameters.delta D.endTime * ρ D.endTime ≤ D.parameters.protectedRadius D.endTime ∧
          let D' := D.withNeckRadius ρ hρ
          let A := ((D'.parameters.delta D'.endTime * D'.parameters.neckRadius D'.endTime) ^ 2)⁻¹
          ∀ y : D'.slab.terminalRegularOpen, metricScalarAt D'.terminal.metric y ≤ A →
            ¬ IsCompact (connectedComponent y) →
            let U := connectedComponentOpen (I := I3) y
            ∃ (ι : Type u) (_ : Finite ι) (_ : Nonempty ι)
              (v : ι → U) (neck : ∀ i, SpatialNeck (D'.terminal.metric.restrictOpen U) δ (v i))
              (level : ι → ℝ) (W : Set U),
              IsCompact W ∧ closure (interior W) = W ∧
              {x : U | metricScalarAt (D'.terminal.metric.restrictOpen U) x ≤ C * A} ⊆ interior W ∧
              {x : U | metricScalarAt (D'.terminal.metric.restrictOpen U) x ≤
                ((D.parameters.protectedRadius D.endTime) ^ 2)⁻¹} ⊆ interior W ∧
              (∀ x ∈ W, metricScalarAt (D'.terminal.metric.restrictOpen U) x ≤ Λ * A) ∧
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
              (∀ x ∈ frontier W, 2 * (C * A) < metricScalarAt (D'.terminal.metric.restrictOpen U) x) ∧
              ∀ V : Set U, W ⊆ V → ∀ x : U, x ∉ interior V →
                C * A < metricScalarAt (D'.terminal.metric.restrictOpen U) x ∧
                ∀ (p : U) (nk : SpatialNeck (D'.terminal.metric.restrictOpen U) δ p)
                  (z : Sphere 2) (level : ℝ), |level| ≤ 4 → nk.map (z, level) = x →
                  Nonempty (SpatialNeck (D'.terminal.metric.restrictOpen U) δ x) ∨
                  ∃ K : CompactDomain U,
                    Nonempty (CapCore K.carrier) ∧
                    nk.map '' (univ ×ˢ Icc (-4 : ℝ) 4) ⊆ interior K.carrier ∧
                    (∀ w ∈ K.carrier, A < metricScalarAt (D'.terminal.metric.restrictOpen U) w ∧
                      metricScalarAt (D'.terminal.metric.restrictOpen U) x / C <
                        metricScalarAt (D'.terminal.metric.restrictOpen U) w ∧
                      metricScalarAt (D'.terminal.metric.restrictOpen U) w <
                        C * metricScalarAt (D'.terminal.metric.restrictOpen U) x) := by
  obtain ⟨η, hη, hproduce⟩ :=
    exists_neckRadius_disjoint_spherical_region_with_exterior_alternatives_and_scale_bound.{u}
  refine ⟨η, hη, ?_⟩
  intro δ hδ hδη
  obtain ⟨C, Λ, hC, hΛ, hproduce⟩ := hproduce δ hδ hδη
  refine ⟨C, Λ, hC, hΛ, ?_⟩
  intro D
  obtain ⟨q, _, hproduce⟩ := hproduce D
  obtain ⟨ρ, hρ, hle, hmono, hmonoOn, hrecenter, hprotect, _, _, hregion⟩ := hproduce q le_rfl
  exact ⟨ρ, hρ, hle, hmono, hmonoOn, hrecenter, hprotect, hregion⟩


end OneStepIncoming
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
