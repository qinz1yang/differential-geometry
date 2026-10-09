import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.SignedCylinder
import DifferentialGeometry.Topology.Manifold.HalfLine.Immersion
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Embedding
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingCompositionBoundary

noncomputable section

open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CuspTruncation.FiniteCuspTruncation

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open CuspCrossSections (endStabilizer)

private local instance {m : ℕ} (Δ : Subgroup (PO (m + 1) 1)) :
    MulAction Δ (HUpper (m + 1)) :=
  EquivariantMap.subAction (Nat.le_add_left 1 m) Δ

private local instance {m : ℕ} (Δ : Subgroup (PO (m + 1) 1)) :
    ContinuousConstSMul Δ (HUpper (m + 1)) :=
  ⟨fun γ ↦ (HyperbolicAction.contMDiff_po_smul m ∞ (γ : PO (m + 1) 1)).continuous⟩

private local instance {m : ℕ} (Δ : Subgroup (PO (m + 1) 1)) :
    ContMDiffConstSMul 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ Δ (HUpper (m + 1)) :=
  ⟨fun γ ↦ HyperbolicAction.contMDiff_po_smul m ∞ (γ : PO (m + 1) 1)⟩

variable {Γ : Subgroup (PO (2 + 1) 1)} [DiscreteTopology Γ]
  [IsCancelSMul Γ (HUpper (2 + 1))] {r : ℝ}
  (D : FiniteCuspTruncation (Nat.le_add_left 1 2) Γ r) (ξ : D.centers)

local notation "hΓ" => (isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ))
local notation "P" => endStabilizer (Nat.le_add_left 1 2) Γ (Set.singleton ξ.val)
local notation "QΓ" => MulAction.orbitRel.Quotient Γ (HUpper (2 + 1))
local notation "πΓ" => Quotient.mk (MulAction.orbitRel Γ (HUpper (2 + 1)))
local notation "πP" => Quotient.mk (MulAction.orbitRel P (HUpper (2 + 1)))
local notation "S" => (πP '' Busemann.horosphere ξ.val (D.level ξ))
local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 + 1)))
local notation "K" => 𝓘(ℝ, Fin 2 → ℝ)
local notation "T" => ModelWithCorners.prod (𝓡 1) (𝓡 1)
local notation "J" => ModelWithCorners.prod T 𝓘(ℝ, ℝ)
local notation "J∂" => ModelWithCorners.prod T (𝓡∂ 1)

private local instance : ProperlyDiscontinuousSMul Γ (HUpper (2 + 1)) :=
  OrbifoldCompactness.properlyDiscontinuous_subAction (Nat.le_add_left 1 2) Γ hΓ

private local instance : IsCancelSMul P (HUpper (2 + 1)) :=
  EquivariantMap.isCancelSMul_subAction (Nat.le_add_left 1 2) (show P ≤ Γ from inf_le_left)

private local instance : ChartedSpace (Fin 2 → ℝ) S := D.horosphereQuotientChartedSpace hΓ ξ

theorem isSmoothEmbedding_horoballCylinderMap_at_depth
    {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N]
    {L : ModelWithCorners ℝ E H} [L.Boundaryless] [IsManifold L ∞ N]
    (e : QΓ ≃ₜ N) (he : IsLocalDiffeomorph I L ∞ (e ∘ πΓ))
    (F : Diffeomorph T K (Circle × Circle) S ∞) (R : ℝ) (hR : 0 < R) :
    IsSmoothEmbedding J∂ L ∞ (fun p : (Circle × Circle) × EuclideanHalfSpace 1 ↦
      e (D.horoballCylinderMap hΓ ξ
        (F p.1, ⟨R + p.2.val 0 / 2,
          add_nonneg hR.le (div_nonneg p.2.property (by norm_num))⟩))) := by
  let f : (Circle × Circle) × EuclideanHalfSpace 1 → N := fun p ↦
    e (D.horoballCylinderMap hΓ ξ
      (F p.1, ⟨R + p.2.val 0 / 2,
        add_nonneg hR.le (div_nonneg p.2.property (by norm_num))⟩))
  let g : (Circle × Circle) × EuclideanHalfSpace 1 → (Circle × Circle) × ℝ :=
    fun p ↦ (p.1, p.2.val 0 / 2)
  obtain ⟨Φ, hΦs, _, _, hΦf, _⟩ :=
    D.exists_partialDiffeomorph_horoballCylinderMap_at_depth ξ e he F R hR
  have hgΦ (p : (Circle × Circle) × EuclideanHalfSpace 1) : g p ∈ Φ.source := by
    rw [hΦs]
    exact add_pos_of_pos_of_nonneg hR (div_nonneg p.2.property (by norm_num))
  have hfg : Φ ∘ g = f := by
    funext p
    apply hΦf (g p)
    have hp := hgΦ p
    rw [hΦs] at hp
    exact hp
  have hg : IsImmersionOfComplement (PUnit.{1} × PUnit.{1}) J∂ J ∞ g := by
    have ht := Topology.Manifold.isImmersionOfComplement_scaledHalfSpaceOneCoordinate
      (σ := (1 : ℝ) / 2) (by norm_num)
    have hid : IsImmersionOfComplement PUnit.{1} T T ∞
        (id : Circle × Circle → Circle × Circle) := IsImmersionOfComplement.id
    have hp := IsImmersionOfComplement.prodMap hid ht
    apply hp.congr
    funext p
    apply Prod.ext
    · rfl
    · change (1 / 2 : ℝ) * p.2.val 0 = p.2.val 0 / 2
      ring
  have himm : IsImmersionOfComplement ((PUnit.{1} × PUnit.{1}) × PUnit.{1}) J∂ L ∞
      (Φ ∘ g) := by
    intro p
    have hΦ := PDE.RicciFlow.Perelman.KappaSolutions.localDiffeomorphAt_isImmersionAtOfComplement
      (Φ.isLocalDiffeomorphAt J L ∞ (hgΦ p))
    have hi : ModelWithCorners.IsInteriorPoint J (g p) :=
      BoundarylessManifold.isInteriorPoint
    exact (hg p).comp_of_isInteriorPoint_map hΦ (by simp) hi
  refine ⟨himm.isImmersion.congr hfg, ?_⟩
  let A : ℝ ≃ₜ ℝ :=
    { toFun := fun t ↦ R + t / 2
      invFun := fun t ↦ 2 * (t - R)
      left_inv := fun t ↦ by ring
      right_inv := fun t ↦ by ring
      continuous_toFun := continuous_const.add (continuous_id.div_const 2)
      continuous_invFun := continuous_const.mul (continuous_id.sub continuous_const) }
  let depth : EuclideanHalfSpace 1 → Ici (0 : ℝ) := fun t ↦
    ⟨R + t.val 0 / 2, add_nonneg hR.le (div_nonneg t.property (by norm_num))⟩
  have hdepth : _root_.Topology.IsEmbedding depth := by
    apply _root_.Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
    exact A.isEmbedding.comp (_root_.Topology.IsEmbedding.subtypeVal.comp
      Topology.Manifold.halfSpaceOneHomeomorph.isEmbedding)
  exact e.isEmbedding.comp ((D.horoballCylinderMap_isClosedEmbedding hΓ ξ).isEmbedding.comp
    (F.toHomeomorph.isEmbedding.prodMap hdepth))

end DifferentialGeometry.CuspTruncation.FiniteCuspTruncation
