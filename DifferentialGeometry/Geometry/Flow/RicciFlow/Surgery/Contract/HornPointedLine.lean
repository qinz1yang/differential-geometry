import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornMinimizingSegment
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckSpatialBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBall
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.SeparatingSegments

set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.SphereSeparation
open DifferentialGeometry.CheegerGromovCompactness

universe u

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
  {g : SmoothRiemannianMetric ThreeModel M} {delta eps : ℝ} {k : ℕ}

omit [T2Space M] [SigmaCompactSpace M] in
private theorem NormalizedNeck.central_sphere_scaled_distance_le
    (N : NormalizedNeck g delta k) (hprecision : delta ≤ eps)
    (heps : eps < 1 / 11) (hk : ⌈eps⁻¹⌉₊ ≤ k) (y : Sphere 2) :
    riemannianEDistOf (scaleMetric N.scale N.scale_pos g) N.center
      (N.chart ⟨(y, 0), by have h := inv_pos.mpr N.delta_pos; constructor <;> linarith⟩) ≤
        ENNReal.ofReal 7 := by
  obtain ⟨nk, _, hmap⟩ := N.exists_spatialNeck hprecision heps hk
  have hcentral : nk.map (y, 0) ∈ nk.map '' (univ ×ˢ ({0} : Set ℝ)) :=
    ⟨(y, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  have hbound := nk.central_sphere_subset_closedBall hcentral
  change riemannianEDistOf g N.center (nk.map (y, 0)) ≤
    ENNReal.ofReal (7 / Real.sqrt (metricScalarAt g N.center)) at hbound
  rw [← N.scale_scalar] at hbound
  have h := mul_le_mul' (le_refl (ENNReal.ofReal (Real.sqrt N.scale))) hbound
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg N.scale),
    mul_div_cancel₀ (7 : ℝ) (Real.sqrt_pos.mpr N.scale_pos).ne'] at h
  have hchart : nk.map (y, 0) = N.chart ⟨(y, 0), by
      have hp := inv_pos.mpr N.delta_pos; constructor <;> linarith⟩ :=
    hmap ⟨(y, 0), by have hp := inv_pos.mpr N.delta_pos; constructor <;> linarith⟩
  rw [hchart] at h
  simpa only [edistOf_scale] using h


theorem exists_metric_line_of_pointed_horn_neck_limit
    (D : ℕ → OneStepIncoming.{u}) {epsilon Lambda : ℝ}
    (P : ∀ i, TerminalCorePresentation (D i) epsilon Lambda)
    (c : ∀ i, ConnectedComponents (D i).slab.terminalRegularOpen)
    (e : ∀ i, (P i).hornIndex (c i))
    (delta : ℕ → ℝ) (order : ℕ → ℕ)
    (N : ∀ i, NormalizedNeck (D i).terminal.metric (delta i) (order i))
    (hprecision : ∀ i, delta i ≤ epsilon) (hepsilon : epsilon < 1 / 11)
    (horder : ∀ i, ⌈epsilon⁻¹⌉₊ ≤ order i)
    (Theta : ∀ i, neckCentralOpen (delta i) → positiveHornDomain)
    (hTheta : ∀ i z, (P i).horn (c i) (e i) (Theta i z).val =
      (N i).chart (TopologicalSpace.Opens.inclusion (neckCentralOpen_le_buffer (delta i)) z))
    (side : ∀ i, ComplementPair (range (fun y : Sphere 2 =>
      Theta i ⟨(y, 0), mem_univ _, neg_lt_zero.mpr (inv_pos.mpr (N i).delta_pos),
        inv_pos.mpr (N i).delta_pos⟩)))
    (hleft : ∀ i, range (fun y : Sphere 2 =>
      Theta i ⟨(y, 0), mem_univ _, neg_lt_zero.mpr (inv_pos.mpr (N i).delta_pos),
        inv_pos.mpr (N i).delta_pos⟩) ⊆ closure (side i).left)
    (hright : ∀ i, range (fun y : Sphere 2 =>
      Theta i ⟨(y, 0), mem_univ _, neg_lt_zero.mpr (inv_pos.mpr (N i).delta_pos),
        inv_pos.mpr (N i).delta_pos⟩) ⊆ closure (side i).right)
    (Tlo Thi : ℕ → ℝ) (hTlo : ∀ i, 0 < Tlo i)
    (hlow : ∀ i (z : positiveHornDomain), z.val.2 < Tlo i → z ∈ (side i).left)
    (hhigh : ∀ i (z : positiveHornDomain), Thi i < z.val.2 → z ∈ (side i).right)
    (hballs : ∀ R : ℝ, 0 < R → ∀ᶠ i in atTop,
      IsCompact (riemannianClosedBallOf (scaleMetric (N i).scale (N i).scale_pos (D i).terminal.metric)
        (N i).center R) ∧
      riemannianClosedBallOf (scaleMetric (N i).scale (N i).scale_pos (D i).terminal.metric)
        (N i).center R ⊆ (P i).horn (c i) (e i) '' (univ ×ˢ Ioi (0 : ℝ)))
    (hbase : ∀ R : ℝ, 0 < R → ∀ᶠ i in atTop, ∀ y : Sphere 2,
      ENNReal.ofReal R < riemannianEDistOf
        (scaleMetric (N i).scale (N i).scale_pos (D i).terminal.metric)
        (N i).center ((P i).horn (c i) (e i) (y, 0))) :
    letI : ∀ i, SigmaCompactSpace (D i).slab.terminalRegularOpen := fun i =>
      isSigmaCompact_iff_sigmaCompactSpace.mp
        (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel (D i).slab.terminalRegularOpen.isOpen)
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel := {obj := fun i =>
      {M := (D i).slab.terminalRegularOpen, basepoint := (N i).center,
       metric := scaleMetric (N i).scale (N i).scale_pos (D i).terminal.metric}}
    ∀ (L : PointedRiemannianManifold.{u, 0, 0} ThreeModel) (f : ℕ → ℕ), StrictMono f →
      ∀ Phi : PointedRiemannianConvergenceMaps X L f,
      ∀ C : MetricConvergenceData Phi,
      (∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric) →
      MetricComplete L →
      (letI := L.topology; ConnectedSpace L.M) →
      ∃ line : ℝ → L.M, ∀ s t : ℝ,
        riemannianEDistOf L.metric (line s) (line t) = ENNReal.ofReal |s - t| := by
  intro X L f hf Phi C href hcomplete hconnected
  let _ := L.topology
  let _ := L.charted
  let _ := L.smooth
  let sphere (i : ℕ) : Set (D i).slab.terminalRegularOpen :=
    (P i).positiveHornMap (c i) (e i) '' range (fun y : Sphere 2 =>
      Theta i ⟨(y, 0), mem_univ _, neg_lt_zero.mpr (inv_pos.mpr (N i).delta_pos),
        inv_pos.mpr (N i).delta_pos⟩)
  have hbound (i : ℕ) : sphere i ⊆ riemannianClosedBallOf
      (scaleMetric (N i).scale (N i).scale_pos (D i).terminal.metric) (N i).center 7 := by
    rintro z ⟨w, ⟨y, rfl⟩, rfl⟩
    have heq := hTheta i ⟨(y, 0), mem_univ _, neg_lt_zero.mpr (inv_pos.mpr (N i).delta_pos),
      inv_pos.mpr (N i).delta_pos⟩
    change riemannianEDistOf _ _ ((P i).horn (c i) (e i) _) ≤ _
    rw [heq]
    exact (N i).central_sphere_scaled_distance_le (hprecision i) hepsilon (horder i) y
  apply exists_pointed_metric_line_of_eventual_minimizing_segments_intersecting_bounded_sets
    C href hcomplete hconnected (fun k => sphere (f k)) (by norm_num : (0 : ℝ) ≤ 7)
    (fun k => hbound (f k))
  intro R hR
  have hRpos : 0 < R := by linarith
  filter_upwards [hf.tendsto_atTop.eventually (hballs (3 * R + 1) (by linarith)),
    hf.tendsto_atTop.eventually (hballs (3 * R) (by positivity)),
    hf.tendsto_atTop.eventually (hbase R hRpos)] with k hcompact hcapture hfar
  let i := f k
  let center : positiveHornDomain :=
    Theta i ⟨((N i).sphereMark, 0), mem_univ _, neg_lt_zero.mpr (inv_pos.mpr (N i).delta_pos),
      inv_pos.mpr (N i).delta_pos⟩
  have hcenter : (P i).horn (c i) (e i) center.val = (N i).center := by
    exact (hTheta i _).trans (N i).marked
  have hmem : center ∈ range (fun y : Sphere 2 =>
      Theta i ⟨(y, 0), mem_univ _, neg_lt_zero.mpr (inv_pos.mpr (N i).delta_pos),
        inv_pos.mpr (N i).delta_pos⟩) := mem_range_self (N i).sphereMark
  obtain ⟨a, b, _, _, hdistA, hdistB, gamma, hstart, hend, _, _, hmin, hcut⟩ :=
    (P i).exists_minimizing_segment_across_scaled_horn_sides (c i) (e i) (side i)
      (hleft i) (hright i) center.val.1 center.property.2 hmem
      (N i).scale (N i).scale_pos hRpos (hTlo i)
      (hcenter.symm ▸ hcompact.1) (hcenter.symm ▸ hcapture.2)
      (hcenter.symm ▸ hfar center.val.1) (hlow i) (hhigh i)
  refine ⟨gamma, _, ENNReal.toReal_nonneg, hmin, hcut, ?_, ?_⟩
  · change (riemannianEDistOf _ (N i).center (gamma 0)).toReal = R
    rw [hstart, ← hcenter, hdistA, ENNReal.toReal_ofReal hRpos.le]
  · change (riemannianEDistOf _ (N i).center (gamma _)).toReal = R
    rw [hend, ← hcenter, hdistB, ENNReal.toReal_ofReal hRpos.le]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
