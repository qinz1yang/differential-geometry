import DifferentialGeometry.Geometry.Hyperbolic.FiniteVolumeModel
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.CoreOpening
import DifferentialGeometry.Geometry.Metric.CompletenessPullback
import DifferentialGeometry.Analysis.Integration.Measure.Pullback

noncomputable section

open Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Hyperbolic.FiniteVolumeHyperbolicModel

open ProjectiveOrthogonalGroup (PO)
open DifferentialGeometry.Hyperbolic (HUpper)

private local instance (Δ : Subgroup (PO 3 1)) : MulAction Δ (HUpper 3) :=
  EquivariantMap.subAction (Nat.le_add_left 1 2) Δ

private local instance (Δ : Subgroup (PO 3 1)) : ContinuousConstSMul Δ (HUpper 3) :=
  ⟨fun γ => (HyperbolicAction.contMDiff_po_smul 2 ∞ (γ : PO 3 1)).continuous⟩

variable (H : FiniteVolumeHyperbolicModel) {Γ : Subgroup (PO 3 1)} [DiscreteTopology Γ]
  [IsCancelSMul Γ (HUpper 3)] {r : ℝ}
  (D : CuspTruncation.FiniteCuspTruncation (Nat.le_add_left 1 2) Γ r)

local notation "QΓ" => MulAction.orbitRel.Quotient Γ (HUpper 3)
local notation "πΓ" => Quotient.mk (MulAction.orbitRel Γ (HUpper 3))

private local instance (U : TopologicalSpace.Opens H.Carrier) : SigmaCompactSpace U := by
  let : SecondCountableTopology H.Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin 3)) H.Carrier
  let : LocallyCompactSpace H.Carrier :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) H.Carrier
  let : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  infer_instance

theorem exists_complete_metric_interior_truncated_image
    (e : QΓ ≃ₜ H.Carrier) (he : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e ∘ πΓ)) :
    let U : TopologicalSpace.Opens H.Carrier :=
      ⟨interior ((e ∘ πΓ) '' CuspTruncation.truncatedSet
        (Nat.le_add_left 1 2) Γ D.centers D.level), isOpen_interior⟩
    ∃ ψ : U ≃ₘ⟮𝓡 3, 𝓡 3⟯ H.Carrier,
      let g := Diffeomorph.pullbackMetric H.metric ψ
      RiemannianMetricComplete g ∧
      hasConstantSectionalCurvature g (-(1 / 4 : ℝ)) ∧
      Integral.Measure.riemannianVolumeMeasure (𝓡 3) U g univ =
        Integral.Measure.riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric univ ∧
      (∀ x y : U, riemannianEDistOf g x y = riemannianEDistOf H.metric (ψ x) (ψ y)) ∧
      (∀ x : U, (∀ ξ : D.centers, x.val ∉ (e ∘ πΓ) '' interior
        (OrbifoldThinRegions.thinRegion (Nat.le_add_left 1 2) Γ r {ξ.val})) → ψ x = x.val) ∧
      ∀ y, (∀ ξ : D.centers, y ∉ (e ∘ πΓ) '' interior
        (OrbifoldThinRegions.thinRegion (Nat.le_add_left 1 2) Γ r {ξ.val})) → (ψ.symm y).val = y := by
  let U : TopologicalSpace.Opens H.Carrier :=
    ⟨interior ((e ∘ πΓ) '' CuspTruncation.truncatedSet
      (Nat.le_add_left 1 2) Γ D.centers D.level), isOpen_interior⟩
  obtain ⟨ψ, hψ, hψi⟩ := D.exists_diffeomorph_interior_truncated_image e he
  refine ⟨ψ, ?_, ?_, ?_, ?_, hψ, hψi⟩
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
    let : MeasurableSpace U := borel U
    let : BorelSpace U := ⟨rfl⟩
    rw [Integral.Measure.riemannianVolumeMeasure_pullback]
    exact MeasureTheory.Measure.map_apply_of_aemeasurable ψ.symm.continuous.measurable.aemeasurable
      MeasurableSet.univ |>.trans (by rw [preimage_univ])
  · intro x y
    simpa only [Diffeomorph.pullbackMetricCross_eq_pullbackMetric] using
      Metric.edistOf_pullbackMetricCross H.metric ψ x y

end DifferentialGeometry.Geometry.Hyperbolic.FiniteVolumeHyperbolicModel
