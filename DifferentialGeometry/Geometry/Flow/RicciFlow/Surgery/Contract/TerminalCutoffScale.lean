import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.Terminal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalSphericalBarrierCover
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

end OneStepIncoming
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
