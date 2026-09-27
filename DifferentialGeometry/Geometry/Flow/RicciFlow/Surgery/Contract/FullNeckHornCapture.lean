import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornNeckCoordinates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoffRemainingFields

set_option autoImplicit false
noncomputable section

open Set Function TopologicalSpace Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private theorem neckBuffer_le_centralOpen {δ δ₀ : ℝ} (hfit : δ⁻¹ + 1 < δ₀⁻¹) :
    neckBuffer δ ≤ neckCentralOpen δ₀ := by
  intro q hq
  exact ⟨mem_univ _, by linarith [hq.1], by linarith [hq.2]⟩

namespace TerminalCorePresentation

universe u

variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)

private local instance : SigmaCompactSpace D.slab.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel D.slab.terminalRegularOpen.isOpen)

theorem exists_scale_threshold_full_neck_in_horn
    (c : ConnectedComponents D.slab.terminalRegularOpen) (hc : c ∈ P.component)
    (e : P.hornIndex c) (r : ℝ) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ {δ₀ : ℝ} {k : ℕ}
      (N : NormalizedNeck D.terminal.metric δ₀ k),
      2 ≤ k → δ₀ ≤ 1 / 8646 → N.center ∈ hornHalfRange P c e → Q < N.scale →
      ∀ {δ : ℝ} (hδ : δ₀ ≤ δ) (hδ1 : δ < 1), δ⁻¹ + 1 < δ₀⁻¹ →
      ∃ Θ : neckBuffer δ → positiveHornDomain,
        IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ Θ ∧
        (∀ q : neckBuffer δ, P.horn c e (Θ q).val = (N.monoDelta hδ hδ1).chart q) ∧
        (∀ q : neckBuffer δ, r < (Θ q).val.2) ∧
        ∃ K : Set D.slab.terminalRegularOpen, IsCompact K ∧
          range (N.monoDelta hδ hδ1).chart ⊆ K ∧
          K ⊆ P.horn c e '' (univ ×ˢ Ioi r) := by
  obtain ⟨Q, hQ, hcoords⟩ := P.exists_scale_threshold_neck_coordinates_beyond_depth c hc e r
  refine ⟨Q, hQ, ?_⟩
  intro δ₀ k N hk hδ₀ hcenter hscale δ hδ hδ1 hfit
  obtain ⟨Θ, hΘ, hΘeq, hΘdepth⟩ := hcoords N hk hδ₀ hcenter hscale
  let j := Opens.inclusion (neckBuffer_le_centralOpen hfit)
  let Θ' := Θ ∘ j
  have hj : IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ j :=
    isSmoothEmbedding_opens_inclusion (neckBuffer_le_centralOpen hfit)
  have hΘ' : IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ Θ' :=
    IsSmoothEmbedding.comp hΘ hj (by simp)
  have hΘ'eq (q : neckBuffer δ) : P.horn c e (Θ' q).val = (N.monoDelta hδ hδ1).chart q :=
    hΘeq (j q)
  let B : Set NeckCylinder := univ ×ˢ Icc (-(δ⁻¹ + 1)) (δ⁻¹ + 1)
  have hBc : IsCompact B := isCompact_univ.prod isCompact_Icc
  have hBsub : B ⊆ neckCentralOpen δ₀ := by
    rintro q ⟨_, hq⟩
    exact ⟨mem_univ _, by linarith [hq.1], by linarith [hq.2]⟩
  let K₀ : Set (neckCentralOpen δ₀) := Subtype.val ⁻¹' B
  have hK₀ : IsCompact K₀ := _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hBc
    (fun q hq => ⟨⟨q, hBsub hq⟩, rfl⟩)
  let f : neckCentralOpen δ₀ → D.slab.terminalRegularOpen :=
    fun q => N.chart (Opens.inclusion (neckCentralOpen_le_buffer δ₀) q)
  let K := f '' K₀
  have hK : IsCompact K := hK₀.image
    (N.chart.continuous.comp (continuous_inclusion (neckCentralOpen_le_buffer δ₀)))
  refine ⟨Θ', hΘ', hΘ'eq, fun q => hΘdepth (j q), K, hK, ?_, ?_⟩
  · rintro x ⟨q, rfl⟩
    exact ⟨j q, ⟨mem_univ _, by change -(δ⁻¹ + 1) ≤ q.val.2; linarith [q.property.1], q.property.2.le⟩, rfl⟩
  · rintro x ⟨q, hq, rfl⟩
    exact ⟨(Θ q).val, ⟨mem_univ _, hΘdepth q⟩, hΘeq q⟩

end TerminalCorePresentation

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
