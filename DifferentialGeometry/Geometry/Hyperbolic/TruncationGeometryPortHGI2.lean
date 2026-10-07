import DifferentialGeometry.Geometry.Hyperbolic.TruncationInterior
import DifferentialGeometry.Geometry.Hyperbolic.ModelAtlas
import DifferentialGeometry.Geometry.Hyperbolic.ModelAtlasProofHGI2

noncomputable section

open Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation

open ProjectiveOrthogonalGroup (PO)
open DifferentialGeometry.Hyperbolic (HUpper)

variable {H : FiniteVolumeHyperbolicModel} (Tr : HyperbolicTruncation H)

private local instance : BoundarylessManifold Tr.core.model Tr.core.interior :=
  DifferentialGeometry.Manifold.boundarylessManifold_intrinsicInterior Tr.core.model ∞ (by simp)

private local instance : SigmaCompactSpace Tr.core.interior :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen Tr.core.model Tr.core.interior.isOpen)

private local instance (Δ : Subgroup (PO 3 1)) : MulAction Δ (HUpper 3) :=
  EquivariantMap.subAction (Nat.le_add_left 1 2) Δ

private local instance (Δ : Subgroup (PO 3 1)) : ContinuousConstSMul Δ (HUpper 3) :=
  ⟨fun γ => (HyperbolicAction.contMDiff_po_smul 2 ∞ (γ : PO 3 1)).continuous⟩

variable {Γ : Subgroup (PO 3 1)} [DiscreteTopology Γ] [IsCancelSMul Γ (HUpper 3)]
  {r : ℝ} (D : CuspTruncation.FiniteCuspTruncation (Nat.le_add_left 1 2) Γ r)

local notation "QΓ" => MulAction.orbitRel.Quotient Γ (HUpper 3)
local notation "πΓ" => Quotient.mk (MulAction.orbitRel Γ (HUpper 3))

theorem exists_hyperbolic_structure_interior_of_truncated_image
    (e : QΓ ≃ₜ H.Carrier) (he : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e ∘ πΓ))
    (hcore : range Tr.inclusion = (e ∘ πΓ) '' CuspTruncation.truncatedSet
      (Nat.le_add_left 1 2) Γ D.centers D.level) :
    let _ := DifferentialGeometry.Manifold.interiorChartedSpace Tr.core.model ∞ (M := Tr.core.interior)
    let _ := DifferentialGeometry.Manifold.interiorIsManifold Tr.core.model ∞ (M := Tr.core.interior)
    ∃ (ψ : Tr.core.interior ≃ₘ⟮𝓡 3, 𝓡 3⟯ H.Carrier)
      (G : GC.Geometry.GeometricStructure (𝓡 3) Tr.core.interior),
      G.model = .hyperbolic ∧
      G.metric = scaleMetric (1 / 4 : ℝ) (by norm_num) (Diffeomorph.pullbackMetric H.metric ψ) ∧
      (∀ x, (∀ ξ : D.centers, Tr.inclusion x.val ∉ (e ∘ πΓ) '' interior
        (OrbifoldThinRegions.thinRegion (Nat.le_add_left 1 2) Γ r {ξ.val})) →
          ψ x = Tr.inclusion x.val) ∧
      ∀ y, (∀ ξ : D.centers, y ∉ (e ∘ πΓ) '' interior
        (OrbifoldThinRegions.thinRegion (Nat.le_add_left 1 2) Γ r {ξ.val})) →
          Tr.inclusion ((ψ.symm y).val) = y := by
  let _ := DifferentialGeometry.Manifold.interiorChartedSpace Tr.core.model ∞ (M := Tr.core.interior)
  let _ := DifferentialGeometry.Manifold.interiorIsManifold Tr.core.model ∞ (M := Tr.core.interior)
  obtain ⟨ψ, hc, hk, hv, _, hf, hi⟩ :=
    Tr.exists_complete_metric_interior_of_truncated_image D e he hcore
  let G := hyperbolicGeometricStructure_HGI2 (Diffeomorph.pullbackMetric H.metric ψ)
    hk hc (hv.trans_lt H.finite_volume)
  exact ⟨ψ, G, rfl, rfl, hf, hi⟩

end DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation
