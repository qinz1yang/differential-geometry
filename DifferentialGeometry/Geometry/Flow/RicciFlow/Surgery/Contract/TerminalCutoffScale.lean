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
  obtain ⟨η, hη, hmain⟩ :=
    OrientedThreeStage.IncomingSlab.exists_uniform_disjoint_spherical_region_on_component_with_exterior_alternatives.{u}
  refine ⟨η, hη, ?_⟩
  intro δ hδ hδη
  obtain ⟨C, C2, hC, hC2, hmain⟩ := hmain δ hδ hδη
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hΛ : 1 ≤ 8 * C2^2 * C := by
    have hsq : 1 ≤ C2^2 := by nlinarith
    have hp := mul_le_mul hsq hC (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg C2)
    nlinarith
  refine ⟨C, 8 * C2^2 * C, hC, hΛ, ?_⟩
  intro D
  have hs : 0 ≤ D.endTime := D.startTime_nonneg.trans D.startTime_lt_endTime.le
  have hd : 0 < D.parameters.delta D.endTime := D.parameters.delta_pos _ hs
  have hp : 0 < D.parameters.protectedRadius D.endTime := D.parameters.protectedRadius_pos _ hs
  let r := D.parameters.protectedRadius D.endTime / D.parameters.delta D.endTime
  have hr : 0 < r := div_pos hp hd
  let ρ₀ := fun t => min (D.parameters.neckRadius t) r
  have hρ₀ : ∀ t, 0 ≤ t → 0 < ρ₀ t := fun t ht => lt_min (D.parameters.neckRadius_pos t ht) hr
  obtain ⟨q, _, hregion⟩ := hmain D.stage D.startTime D.endTime D.slab
  obtain ⟨ρ, hρ, hρle, hmono, hmonoOn, hscale⟩ :=
    (D.parameters.withNeckRadius ρ₀ hρ₀).exists_neckRadius_le_cutoff_scale_gt hs hCpos q
  have hprotect : D.parameters.delta D.endTime * ρ D.endTime ≤ D.parameters.protectedRadius D.endTime := by
    have hle : ρ D.endTime ≤ r := (hρle _ hs).trans (min_le_right _ _)
    have hmul := (le_div_iff₀ hd).mp hle
    nlinarith
  refine ⟨ρ, hρ, (fun t ht => (hρle t ht).trans (min_le_left _ _)),
    (fun h => hmono (h.min antitone_const)),
    (fun h => hmonoOn (h.min antitoneOn_const)),
    (fun h => h.withNeckRadius hρ), hprotect, ?_⟩
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
    hregion D.terminal A (C * A) y hscale le_rfl (hy.trans hAle) hnoncompact
  refine ⟨ι, hi, hne, v, neck, level, W, hW, hreg, hlow,
    (fun x hx => hlow (hx.trans (hprotected.trans hAle))), ?_,
    hdisjoint, hfront, hlevel, hcollar, hfrontscalar, hexterior⟩
  intro x hx
  exact (hupper x hx).trans_eq (by change 8 * C2^2 * (C * A) = 8 * C2^2 * C * A; ring)


end OneStepIncoming
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
