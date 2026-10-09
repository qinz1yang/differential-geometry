import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedWitnessTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CylinderReferenceModel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RecenterAux
import DifferentialGeometry.Geometry.Metric.Pullback.Cross
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps δ t : ℝ} {x : M}

theorem StrongNeck.exists_neckBuffer_pullback_bound (nk : StrongNeck S eps x t)
    (hfit : δ⁻¹ + 1 ≤ eps⁻¹) :
    ∃ (V : TopologicalSpace.Opens M) (Φ : neckBuffer δ ≃ₘ⟮IC, I3⟯ V),
      (∀ z : neckBuffer δ, (Φ z : M) = nk.map z.val) ∧
      ∀ a ≤ ⌈eps⁻¹⌉₊, ∀ z : neckBuffer δ,
        metricDerivNorm a
          (scaleMetric (S.scalar t x) nk.Q_pos
            (Diffeomorph.pullbackMetricCross ((S.base.metric t).restrictOpen V) Φ))
          (roundCylinderMetric.restrictOpen (neckBuffer δ))
          (roundCylinderMetric.restrictOpen (neckBuffer δ)) z ≤ eps := by
  have hdomain : (neckBuffer δ : Set Cylinder) ⊆
      Set.univ ×ˢ Set.Ioo (-eps⁻¹) eps⁻¹ := by
    intro z hz
    have hz' : -δ⁻¹ - 1 < z.2 ∧ z.2 < δ⁻¹ + 1 := hz
    exact ⟨Set.mem_univ _, by linarith [hz'.1], hz'.2.trans_le hfit⟩
  have hsource : (neckBuffer δ : Set Cylinder) ⊆ nk.map.source :=
    hdomain.trans nk.domain
  let V : TopologicalSpace.Opens M :=
    ⟨nk.map '' (neckBuffer δ : Set Cylinder), image_opens_isOpen nk.map hsource⟩
  let Φ : neckBuffer δ ≃ₘ⟮IC, I3⟯ V := PartialDiffeomorph.toOpensDiffeo nk.map hsource
  let G := scaleMetric (S.scalar t x) nk.Q_pos
    (Diffeomorph.pullbackMetricCross ((S.base.metric t).restrictOpen V) Φ)
  have hG (z : neckBuffer δ) (v w : TangentSpace IC z) :
      G.inner z v w = (rescaledMetric S t (S.scalar t x) nk.Q_pos 0).inner
        (nk.map z.val) (mfderiv IC I3 nk.map z.val v) (mfderiv IC I3 nk.map z.val w) := by
    simp only [G, rescaledMetric, parabolicTime_zero, scaleMetric_inner,
      Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.restrictOpen_inner]
    rw [show (Φ z : M) = nk.map z.val from rfl]
    change S.scalar t x * (S.base.metric t).inner (nk.map z.val)
      (mfderiv IC I3 (PartialDiffeomorph.toOpensDiffeo nk.map hsource) z v)
      (mfderiv IC I3 (PartialDiffeomorph.toOpensDiffeo nk.map hsource) z w) = _
    rw [PartialDiffeomorph.mfderiv_toOpensDiffeo, PartialDiffeomorph.mfderiv_toOpensDiffeo]
  have href : nk.cylinder.metric 0 = roundCylinderMetric :=
    nk.cylinder.metric_zero_eq_roundCylinder.trans roundCylinderMetric_eq_geometry.symm
  refine ⟨V, Φ, fun _ => rfl, ?_⟩
  intro a ha z
  have hnorm := nk.comparison.metricDerivNorm_of_local_metric
    (neckBuffer δ) hdomain 0 G hG a z
  rw [href] at hnorm
  rw [hnorm]
  have hclose := nk.comparison.close a 0 (by simpa using ha) 0 (by norm_num)
    z.val (hdomain z.property)
  simpa only [href] using hclose

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
