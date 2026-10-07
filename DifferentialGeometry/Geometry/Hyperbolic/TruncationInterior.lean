import DifferentialGeometry.Geometry.Hyperbolic.CoreInterior
import DifferentialGeometry.Geometry.Hyperbolic.Truncation
import DifferentialGeometry.Topology.Manifold.Embedding.Interior

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

theorem exists_diffeomorph_interior_of_truncated_image
    (e : QΓ ≃ₜ H.Carrier) (he : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e ∘ πΓ))
    (hcore : range Tr.inclusion = (e ∘ πΓ) '' CuspTruncation.truncatedSet
      (Nat.le_add_left 1 2) Γ D.centers D.level) :
    ∃ ψ : Tr.core.interior ≃ₘ⟮Tr.core.model, 𝓡 3⟯ H.Carrier,
      (∀ x, (∀ ξ : D.centers, Tr.inclusion x.val ∉ (e ∘ πΓ) '' interior
        (OrbifoldThinRegions.thinRegion (Nat.le_add_left 1 2) Γ r {ξ.val})) →
          ψ x = Tr.inclusion x.val) ∧
      ∀ y, (∀ ξ : D.centers, y ∉ (e ∘ πΓ) '' interior
        (OrbifoldThinRegions.thinRegion (Nat.le_add_left 1 2) Γ r {ξ.val})) →
          Tr.inclusion ((ψ.symm y).val) = y := by
  let A : Tr.core.interior ≃ₘ⟮Tr.core.model, 𝓡 3⟯
      (⟨interior (range Tr.inclusion), isOpen_interior⟩ : TopologicalSpace.Opens H.Carrier) :=
    Tr.embedding.interiorDiffeomorph rfl
  have hA (x : Tr.core.interior) : (A x).val = Tr.inclusion x.val :=
    Tr.embedding.interiorDiffeomorph_apply_val rfl x
  have hAi (y : (⟨interior (range Tr.inclusion), isOpen_interior⟩ :
      TopologicalSpace.Opens H.Carrier)) : Tr.inclusion ((A.symm y).val) = y.val :=
    Tr.embedding.interiorDiffeomorph_symm_apply rfl y
  have hU : (⟨interior (range Tr.inclusion), isOpen_interior⟩ : TopologicalSpace.Opens H.Carrier) =
      ⟨interior ((e ∘ πΓ) '' CuspTruncation.truncatedSet
        (Nat.le_add_left 1 2) Γ D.centers D.level), isOpen_interior⟩ := by
    apply SetLike.coe_injective
    exact congrArg interior hcore
  have h := D.exists_diffeomorph_interior_truncated_image e he
  dsimp only at h
  rw [← hU] at h
  obtain ⟨ψ, hψ, hψi⟩ := h
  refine ⟨A.trans ψ, ?_, ?_⟩
  · intro x hx
    change ψ (A x) = Tr.inclusion x.val
    rw [hψ (A x) (by
      intro ξ
      rw [hA]
      exact hx ξ), hA]
  · intro y hy
    change Tr.inclusion ((A.symm (ψ.symm y)).val) = y
    rw [hAi, hψi y hy]

theorem exists_complete_metric_interior_of_truncated_image
    (e : QΓ ≃ₜ H.Carrier) (he : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e ∘ πΓ))
    (hcore : range Tr.inclusion = (e ∘ πΓ) '' CuspTruncation.truncatedSet
      (Nat.le_add_left 1 2) Γ D.centers D.level) :
    let _ := DifferentialGeometry.Manifold.interiorChartedSpace Tr.core.model ∞ (M := Tr.core.interior)
    let _ := DifferentialGeometry.Manifold.interiorIsManifold Tr.core.model ∞ (M := Tr.core.interior)
    ∃ ψ : Tr.core.interior ≃ₘ⟮𝓡 3, 𝓡 3⟯ H.Carrier,
      let g := Diffeomorph.pullbackMetric H.metric ψ
      RiemannianMetricComplete g ∧
      hasConstantSectionalCurvature g (-(1 / 4 : ℝ)) ∧
      Integral.Measure.riemannianVolumeMeasure (𝓡 3) Tr.core.interior g univ =
        Integral.Measure.riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric univ ∧
      (∀ x y : Tr.core.interior,
        riemannianEDistOf g x y = riemannianEDistOf H.metric (ψ x) (ψ y)) ∧
      (∀ x, (∀ ξ : D.centers, Tr.inclusion x.val ∉ (e ∘ πΓ) '' interior
        (OrbifoldThinRegions.thinRegion (Nat.le_add_left 1 2) Γ r {ξ.val})) →
          ψ x = Tr.inclusion x.val) ∧
      ∀ y, (∀ ξ : D.centers, y ∉ (e ∘ πΓ) '' interior
        (OrbifoldThinRegions.thinRegion (Nat.le_add_left 1 2) Γ r {ξ.val})) →
          Tr.inclusion ((ψ.symm y).val) = y := by
  obtain ⟨f, hf, hfi⟩ := Tr.exists_diffeomorph_interior_of_truncated_image D e he hcore
  let A := DifferentialGeometry.Manifold.interiorAtlasDiffeomorph Tr.core.model ∞ (M := Tr.core.interior)
  let _ := DifferentialGeometry.Manifold.interiorChartedSpace Tr.core.model ∞ (M := Tr.core.interior)
  let _ := DifferentialGeometry.Manifold.interiorIsManifold Tr.core.model ∞ (M := Tr.core.interior)
  let ψ := A.symm.trans f
  refine ⟨ψ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Diffeomorph.pullbackMetricCross_eq_pullbackMetric] using
      Metric.riemannianMetricComplete_pullbackMetricCross H.complete ψ
  · intro x v w hvw
    rw [Riemannian.sectionalCurvature_pullback]
    apply H.curvature
    let L := ψ.mfderivToContinuousLinearEquiv (by simp) x
    have hL : LinearIndependent ℝ (L.toLinearMap ∘ ![v, w]) :=
      hvw.map' L.toLinearMap (LinearMap.ker_eq_bot.mpr L.injective)
    convert hL using 1
    ext i
    fin_cases i <;> rfl
  · let : MeasurableSpace H.Carrier := borel H.Carrier
    let : BorelSpace H.Carrier := ⟨rfl⟩
    let : MeasurableSpace Tr.core.interior := borel Tr.core.interior
    let : BorelSpace Tr.core.interior := ⟨rfl⟩
    rw [Integral.Measure.riemannianVolumeMeasure_pullback]
    exact MeasureTheory.Measure.map_apply_of_aemeasurable ψ.symm.continuous.measurable.aemeasurable
      MeasurableSet.univ |>.trans (by rw [preimage_univ])
  · intro x y
    simpa only [Diffeomorph.pullbackMetricCross_eq_pullbackMetric] using
      Metric.edistOf_pullbackMetricCross H.metric ψ x y
  · exact hf
  · exact hfi

end DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation
