import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Curvature.Flatness

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

noncomputable section

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {D : RealTimeInterval}

theorem complete_forward_flatness
    (F : PointedFlowData.{u, uE, uH} (I := I) D)
    {a b : Real} (hab : a < b)
    (hcarrier : Set.Icc a b ⊆ D.carrier)
    (hregular : Set.Ico a b ⊆ D.regular)
    (hcomplete : ∀ t ∈ Set.Icc a b, MetricComplete (I := I) (F.atTime (I := I) t))
    (hcurv : ∃ K : Real, ∀ t ∈ Set.Icc a b, ∀ x : F.M,
      F.rmNormSq (I := I) t x ≤ K)
    (hflat : ∀ x : F.M, F.rmNormSq (I := I) a x = 0) :
    ∀ t ∈ Set.Icc a b, ∀ x : F.M, F.rmNormSq (I := I) t x = 0 := by
  let : TopologicalSpace F.M := F.topology
  let : ChartedSpace H F.M := F.charted
  let : IsManifold I ∞ F.M := F.smooth
  let : SigmaCompactSpace F.M := F.sigmaCompact
  let : T2Space F.M := F.t2
  obtain ⟨K, hK⟩ := hcurv
  have hbound : ∃ K' : Real, 0 ≤ K' ∧ ∀ t ∈ Set.Icc a b, ∀ x : F.M,
      DifferentialGeometry.Tensor0SBundle.normSq0S (I := I)
        (F.S.base.metric t) x 4 (F.S.base.rm04 t x) ≤ K' :=
    ⟨max K 0, le_max_right _ _,
      fun t ht x => (hK t ht x).trans (le_max_left _ _)⟩
  have hflat' : ∀ x : F.M,
      DifferentialGeometry.Tensor0SBundle.normSq0S (I := I)
        (F.S.base.metric a) x 4 (F.S.base.rm04 a x) = 0 := hflat
  have hcomplete' : DifferentialGeometry.RiemannianMetricComplete (I := I)
      (F.S.base.metric a) :=
    ⟨MetricComplete.complete (I := I) (F.atTime (I := I) a)
      (hcomplete a ⟨le_rfl, hab.le⟩)⟩
  exact DifferentialGeometry.PDE.RicciFlow.curvature_normSq_eq_zero_on_Icc_of_eq_zero_at_left
    (I := I) F.S F.isSolution hab hcarrier hregular hcomplete' hbound hflat'

end

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
