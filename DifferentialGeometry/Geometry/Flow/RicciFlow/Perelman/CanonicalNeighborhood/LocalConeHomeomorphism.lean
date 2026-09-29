import DifferentialGeometry.Topology.Homeomorph.EmbeddedNeighborhood
import DifferentialGeometry.Geometry.Metric.ConeDistance
import DifferentialGeometry.Geometry.Metric.Distance.Basic
import Mathlib.Topology.Algebra.GroupWithZero
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.OriginalSourceConeEmbedding
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonComposition

section

noncomputable section
open Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

variable {E H M Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MetricSpace Y]

theorem exists_local_distance_cone_of_scaled_embedding
    (g : SmoothRiemannianMetric I M) {D : Set (ℝ × Y)} (hD : IsOpen D)
    (hpos : ∀ x ∈ D, 0 < x.1) (F : D → M) (hF : Topology.IsEmbedding F)
    (o : D) (honto : range F ∈ 𝓝 (F o)) {lambda : ℝ} (hlambda : 0 < lambda)
    (hdist : ∀ x z : D, (riemannianEDistOf g (F x) (F z)).toReal =
      lambda * Metric.coneDistance (x : ℝ × Y) (z : ℝ × Y)) :
    ∃ e : OpenPartialHomeomorph M (ℝ × Y), F o ∈ e.source ∧
      e (F o) = (lambda * (o : ℝ × Y).1, (o : ℝ × Y).2) ∧
      (∀ x ∈ e.source, 0 < (e x).1) ∧
      (∀ x ∈ e.source, ∀ z ∈ e.source,
        (riemannianEDistOf g x z).toReal = Metric.coneDistance (e x) (e z)) ∧
      ∀ x ∈ e.source, ∃ y : D, F y = x ∧
        e x = (lambda * (y : ℝ × Y).1, (y : ℝ × Y).2) := by
  obtain ⟨e, ho, heo, hetarget, heforward⟩ :=
    hF.exists_openPartialHomeomorph_of_range_mem_nhds hD honto
  let scale : (ℝ × Y) ≃ₜ (ℝ × Y) :=
    (Homeomorph.mulLeft₀ lambda hlambda.ne').prodCongr (Homeomorph.refl Y)
  let e' := e.transHomeomorph scale
  have heEval (x : M) : e' x = (lambda * (e x).1, (e x).2) := rfl
  have heSource : e'.source = e.source := rfl
  refine ⟨e', ho, ?_, ?_, ?_, ?_⟩
  · rw [heEval, heo]
  · intro x hx
    rw [heEval]
    exact mul_pos hlambda (hpos (e x) (hetarget (e.map_source hx)))
  · intro x hx z hz
    obtain ⟨y, rfl, hey⟩ := heforward x hx
    obtain ⟨w, rfl, hew⟩ := heforward z hz
    rw [hdist, heEval, heEval, hey, hew, Metric.coneDistance_radial_mul, abs_of_pos hlambda]
  · intro x hx
    obtain ⟨y, hy, hey⟩ := heforward x hx
    exact ⟨y, hy, (heEval x).trans (congrArg (fun z : ℝ × Y => (lambda * z.1, z.2)) hey)⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  RealizedFiniteHorn.metricSpace RealizedFiniteHorn.charted RealizedFiniteHorn.smooth
  RealizedFiniteHorn.sigmaCompact EndAngles.metric

theorem RealizedFiniteHorn.exists_marked_original_source_local_distance_cone
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (H : RealizedFiniteHorn X.toFlowSequence)
    (angles : EndAngles H.horn) [CompactSpace (UniformSpace.Completion angles.quotient)]
    (ray : EndRay H.horn.endpoint) (d : ℕ → ℝ) (N : ℕ)
    (C : AnnularConvergence H.horn angles ray d)
    (hd : ∀ i, d i ∈ Ioc 0 ray.length)
    (j psi nseq : ℕ → ℕ) (hpsi : StrictMono psi) (hnseq : StrictMono nseq)
    (hQ : ∀ n, 0 < metricScalarAt H.metric (ray.point (d (N + n))))
    {a b lambda R : ℝ} (ha : 0 < a) (hlambda : 0 < lambda)
    (ha1 : a < 1) (h1b : 1 < b) (hR : 0 < R)
    (hscale : Tendsto (fun k => Real.sqrt
      (metricScalarAt H.metric (ray.point (d (N + nseq k))) * d (N + nseq k) ^ 2))
      atTop (𝓝 lambda))
    (hcompact : ∀ n, IsCompact (riemannianClosedBallOf
      (scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n) H.metric)
      (ray.point (d (N + n))) R))
    (hdiagonal : ∀ i n : ℕ, n ≤ i →
      let scaled := scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n) H.metric
      let ball := riemannianClosedBallOf scaled (ray.point (d (N + n))) R
      ball ⊆ (H.maps (j i)).source ∧
      Nonempty (MetricComparisonOn (fun _ => scaled)
        (fun _ => scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n)
          ((X.term (H.subseq (j i))).S.base.metric 0)) (H.maps (j i)) ball {0} i
            (1 / ((i : ℝ) + 2))))
    {Q : Type v} [TopologicalSpace Q] [ChartedSpace ThreeSpace Q] [IsManifold I3 ∞ Q]
    [T2Space Q] [SigmaCompactSpace Q]
    (g : SmoothRiemannianMetric I3 Q) (V U : TopologicalSpace.Opens Q)
    (hVU : V ≤ U) (q : Q) (hq : q ∈ V)
    (f : ∀ k, PartialDiffeomorph I3 I3 Q (X.term (H.subseq (j (psi (nseq k))))).M ∞)
    (G : ℕ → SmoothRiemannianMetric I3 U)
    (hG : MetricCInfConvergenceOnCompacts G (g.restrictOpen U) (g.restrictOpen U))
    (hsource : ∀ᶠ k in atTop, (U : Set Q) ⊆ (f k).source)
    (hmetric : ∀ᶠ k in atTop, ∀ (x : U) (v w : TangentSpace I3 x),
      (G k).inner x v w =
        (scaleMetric (metricScalarAt H.metric (ray.point (d (N + nseq k)))) (hQ (nseq k))
          ((X.term (H.subseq (j (psi (nseq k))))).S.base.metric 0)).inner (f k x)
            (mfderiv I3 I3 (f k) x v) (mfderiv I3 I3 (f k) x w))
    (hbase : ∀ k, f k q = H.maps (j (psi (nseq k))) (ray.point (d (N + nseq k))))
 :
    ∃ e : OpenPartialHomeomorph V (ℝ × UniformSpace.Completion angles.quotient),
      (⟨q, hq⟩ : V) ∈ e.source ∧
      e ⟨q, hq⟩ = (lambda, (angles.classOf ray : UniformSpace.Completion angles.quotient)) ∧
      (∀ x ∈ e.source, 0 < (e x).1) ∧
      ∀ x ∈ e.source, ∀ z ∈ e.source,
        (riemannianEDistOf (g.restrictOpen V) x z).toReal = Metric.coneDistance (e x) (e z) := by
  obtain ⟨D, hD, hoD, hradial, Psi, hemb, hrange, hmarked, hdist, _⟩ :=
    H.exists_marked_original_source_local_cone_embedding X angles ray d N C hd j psi nseq
      hpsi hnseq hQ ha hlambda ha1 h1b hR hscale hcompact hdiagonal
      g V U hVU q hq f G hG hsource hmetric hbase
  let o : D := ⟨(1, (angles.classOf ray : UniformSpace.Completion angles.quotient)), hoD⟩
  have hmark : Psi o = (⟨q, hq⟩ : V) := Subtype.ext (hmarked o rfl)
  have hrange' : range Psi ∈ 𝓝 (Psi o) := by
    have hh : (Subtype.val : V → Q) ⁻¹' range (fun x => (Psi x : Q)) ∈ 𝓝 (Psi o) :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds (by
        rw [hmarked o rfl]
        exact hrange)
    apply Filter.mem_of_superset hh
    rintro p ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  obtain ⟨e, he, heo, hpos, hmetric, _⟩ := exists_local_distance_cone_of_scaled_embedding
    (g.restrictOpen V) hD (fun x hx => ha.trans (hradial x hx).1) Psi hemb o hrange' hlambda hdist
  rw [hmark] at he heo
  refine ⟨e, he, ?_, hpos, hmetric⟩
  simpa only [o, mul_one] using heo

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
