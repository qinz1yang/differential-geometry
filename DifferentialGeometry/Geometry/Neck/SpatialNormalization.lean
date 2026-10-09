import DifferentialGeometry.Geometry.Neck.Spatial
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorphImmersion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedWitnessTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CylinderReferenceModel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RecenterAux
import DifferentialGeometry.Geometry.Metric.Pullback.Cross
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

set_option autoImplicit false

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I3 M} {eps δ : ℝ} {x : M}

theorem SpatialNeck.exists_neckBuffer_pullback_bound (nk : SpatialNeck g eps x)
    (hfit : δ⁻¹ + 1 ≤ eps⁻¹) :
    ∃ (V : TopologicalSpace.Opens M) (Φ : neckBuffer δ ≃ₘ⟮IC, I3⟯ V),
      (∀ z : neckBuffer δ, (Φ z : M) = nk.map z.val) ∧
      ∀ a ≤ ⌈eps⁻¹⌉₊, ∀ z : neckBuffer δ,
        metricDerivNorm a
          (DifferentialGeometry.scaleMetric (metricScalarAt g x) nk.Q_pos
            (Diffeomorph.pullbackMetricCross (g.restrictOpen V) Φ))
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
  let G := DifferentialGeometry.scaleMetric (metricScalarAt g x) nk.Q_pos
    (Diffeomorph.pullbackMetricCross (g.restrictOpen V) Φ)
  have hG (z : neckBuffer δ) (v w : TangentSpace IC z) :
      G.inner z v w = (DifferentialGeometry.scaleMetric (metricScalarAt g x) nk.Q_pos g).inner
        (nk.map z.val) (mfderiv IC I3 nk.map z.val v) (mfderiv IC I3 nk.map z.val w) := by
    simp only [G, scaleMetric_inner,
      Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.restrictOpen_inner]
    rw [show (Φ z : M) = nk.map z.val from rfl]
    change metricScalarAt g x * g.inner (nk.map z.val)
      (mfderiv IC I3 (PartialDiffeomorph.toOpensDiffeo nk.map hsource) z v)
      (mfderiv IC I3 (PartialDiffeomorph.toOpensDiffeo nk.map hsource) z w) = _
    rw [PartialDiffeomorph.mfderiv_toOpensDiffeo, PartialDiffeomorph.mfderiv_toOpensDiffeo]
  have href : nk.cylinder.metric 0 = roundCylinderMetric :=
    nk.cylinder.metric_zero_eq_roundCylinder.trans roundCylinderMetric_eq_geometry.symm
  refine ⟨V, Φ, fun _ => rfl, ?_⟩
  intro a ha z
  have hnorm := nk.comparison.metricDerivNorm_of_local_metric
    (neckBuffer δ) hdomain 0 G hG a z
  rw [← href]
  rw [hnorm]
  have hclose := nk.comparison.close a 0 (by simpa using ha) 0 (by norm_num)
    z.val (hdomain z.property)
  simpa only [href] using hclose


theorem SpatialNeck.exists_normalizedNeck (nk : SpatialNeck g eps x)
    (hδ1 : δ < 1) (hepsδ : eps < δ) (k : ℕ) (hk : k ≤ ⌈eps⁻¹⌉₊)
    (hfit : δ⁻¹ + 1 ≤ eps⁻¹) :
    ∃ N : NormalizedNeck g δ k,
      N.center = x ∧ N.sphereMark = nk.center ∧ ∀ z, N.chart z = nk.map z.val := by
  obtain ⟨V, Φ, hmap, hbound⟩ := nk.exists_neckBuffer_pullback_bound hfit
  have hδ : 0 < δ := nk.eps_pos.trans hepsδ
  let G := DifferentialGeometry.scaleMetric (metricScalarAt g x) nk.Q_pos
    (Diffeomorph.pullbackMetricCross (g.restrictOpen V) Φ)
  let chart : C(neckBuffer δ, M) :=
    ⟨fun z => (Φ z).1, continuous_subtype_val.comp Φ.continuous⟩
  have hchart : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ chart := by
    apply DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_injective_mfderiv
      (contMDiff_subtype_val.comp Φ.contMDiff)
      (Subtype.val_injective.comp Φ.injective)
    · intro z
      change Function.Injective (mfderiv NeckCylinderModel ThreeModel
        (fun q => (Φ q).1) z)
      rw [DifferentialGeometry.mfderiv_subtypeVal_comp]
      exact (Φ.isLocalDiffeomorph.mfderivToContinuousLinearEquiv (by simp) z).injective
    · simp [ThreeSpace]
  let N : NormalizedNeck g δ k :=
    { delta_pos := hδ
      delta_lt_one := hδ1
      sphereMark := nk.center
      center := x
      chart := chart
      chart_smooth := hchart
      marked := (hmap _).trans nk.center_eq
      scale := metricScalarAt g x
      scale_pos := nk.Q_pos
      scale_scalar := rfl
      normalizedMetric := G
      normalized_inner := by
        intro z A B
        rw [scaleMetric_inner, Diffeomorph.pullbackMetricCross_inner,
          SmoothRiemannianMetric.restrictOpen_inner]
        change metricScalarAt g x * g.inner (Φ z).1
          (mfderiv NeckCylinderModel ThreeModel Φ z A)
          (mfderiv NeckCylinderModel ThreeModel Φ z B) = _
        change _ = metricScalarAt g x * g.inner (Φ z).1
          (mfderiv NeckCylinderModel ThreeModel (fun q => (Φ q).1) z A)
          (mfderiv NeckCylinderModel ThreeModel (fun q => (Φ q).1) z B)
        rw [DifferentialGeometry.mfderiv_subtypeVal_comp]
        rfl
      closeness := lt_of_le_of_lt
        (metricDerivNormSupOn_le_of_forall (neckClosedTest δ) k G _ _ eps nk.eps_pos.le
          (fun a ha z _ => hbound a (ha.trans hk) z)) hepsδ }
  exact ⟨N, rfl, rfl, hmap⟩

omit [T2Space M] in
private theorem doubled_precision_buffer (nk : SpatialNeck g eps x) :
    (2 * eps)⁻¹ + 1 ≤ eps⁻¹ := by
  have heps : eps ≤ 1 / 2 := nk.eps_small.le.trans (by norm_num)
  have hprod : eps * ((2 * eps)⁻¹ + 1) = 1 / 2 + eps := by
    field_simp [nk.eps_pos.ne']
  apply (mul_le_mul_iff_left₀ nk.eps_pos).mp
  rw [mul_comm ((2 * eps)⁻¹ + 1), hprod, inv_mul_cancel₀ nk.eps_pos.ne']
  linarith

omit [T2Space M] in
private theorem doubled_precision_order (nk : SpatialNeck g eps x) {ε : ℝ}
    (hreserve : 2 * eps ≤ ε) : ⌊ε⁻¹⌋₊ + 1 ≤ ⌈eps⁻¹⌉₊ := by
  have hepspos := nk.eps_pos
  have hε : 0 < ε := lt_of_lt_of_le (by positivity) hreserve
  have hfit := doubled_precision_buffer nk
  have hεinv : ε⁻¹ ≤ (2 * eps)⁻¹ := inv_anti₀ (by positivity) hreserve
  have hfloor : (⌊ε⁻¹⌋₊ : ℝ) ≤ ε⁻¹ := Nat.floor_le (inv_nonneg.mpr hε.le)
  have hceil : eps⁻¹ ≤ (⌈eps⁻¹⌉₊ : ℝ) := Nat.le_ceil _
  have hresult : ((⌊ε⁻¹⌋₊ + 1 : ℕ) : ℝ) ≤ (⌈eps⁻¹⌉₊ : ℝ) := by
    push_cast
    linarith
  exact_mod_cast hresult


theorem SpatialNeck.exists_normalizedNeck_of_two_mul_le (nk : SpatialNeck g eps x)
    {ε : ℝ} (hreserve : 2 * eps ≤ ε) :
    ∃ N : NormalizedNeck g (2 * eps) (⌊ε⁻¹⌋₊ + 1),
      N.center = x ∧ N.sphereMark = nk.center ∧ ∀ z, N.chart z = nk.map z.val := by
  have hδ1 : 2 * eps < 1 := by linarith [nk.eps_small]
  exact nk.exists_normalizedNeck hδ1 (by linarith [nk.eps_pos]) (⌊ε⁻¹⌋₊ + 1)
    (doubled_precision_order nk hreserve) (doubled_precision_buffer nk)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
