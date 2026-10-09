import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.MinimizingLensAngle
import DifferentialGeometry.Geometry.Geodesic.MinimizingArm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TransverseCrossingPath
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckArmNoReturn

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
universe u
attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle
variable {X : PointedRiemannianSeq.{u, 0, 0} I3}
  {P : PointedRiemannianManifold.{u, 0, 0} I3} {f : ℕ → ℕ}
  {F : PointedRiemannianConvergenceMaps X P f}

theorem eventually_exists_minimizingArms_comparisonAngle_lt
    [ConnectedSpace P.M]
    (C : MetricConvergenceData F)
    (href : ∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric)
    (hcomplete : MetricComplete P) (hsec : HasNonnegativeSectionalCurvature P.metric)
    (hsource : ∀ᶠ i in atTop, MetricComplete (X.obj (f i)))
    (hconnected : ∀ i, ConnectedSpace (X.obj (f i)).M)
    (y p z : P.M) {r θ : ℝ} (hr : 0 < r)
    (hrp : r < metricDistance P.metric y p) (hrz : r < metricDistance P.metric y z)
    (hθ : θ < comparisonAngle (metricDistance P.metric y p)
      (metricDistance P.metric y z) (metricDistance P.metric p z)) :
    ∀ᶠ i in atTop, ∃ a b : MinimizingArm (X.obj (f i)).metric (F.map i y),
      a.length = metricDistance (X.obj (f i)).metric (F.map i y) (F.map i p) ∧
      b.length = metricDistance (X.obj (f i)).metric (F.map i y) (F.map i z) ∧
      a.point a.length = F.map i p ∧ b.point b.length = F.map i z ∧
      r < a.length ∧ r < b.length ∧
      θ < comparisonAngle r r (metricDistance (X.obj (f i)).metric (a.point r) (b.point r)) := by
  classical
  let E := fun i => ∃ a b : MinimizingArm (X.obj (f i)).metric (F.map i y),
      a.length = metricDistance (X.obj (f i)).metric (F.map i y) (F.map i p) ∧
      b.length = metricDistance (X.obj (f i)).metric (F.map i y) (F.map i z) ∧
      a.point a.length = F.map i p ∧ b.point b.length = F.map i z ∧
      r < a.length ∧ r < b.length
  have hE : ∀ᶠ i in atTop, E i := by
    filter_upwards [hsource,
      (tendsto_pointed_map_distance C href hcomplete y p).eventually (lt_mem_nhds hrp),
      (tendsto_pointed_map_distance C href hcomplete y z).eventually (lt_mem_nhds hrz)]
      with i hi hip hiz
    let : ConnectedSpace (X.obj (f i)).M := hconnected i
    have hcomplete' : RiemannianMetricComplete (X.obj (f i)).metric :=
      ⟨MetricComplete.complete (X.obj (f i)) hi⟩
    have hyp : F.map i y ≠ F.map i p := by
      intro heq
      have hh : metricDistance (X.obj (f i)).metric (F.map i y) (F.map i p) = 0 := by
        simp only [heq, metricDistance, riemannianEDistOf_self, ENNReal.toReal_zero]
      change r < metricDistance (X.obj (f i)).metric (F.map i y) (F.map i p) at hip
      linarith
    have hyz : F.map i y ≠ F.map i z := by
      intro heq
      have hh : metricDistance (X.obj (f i)).metric (F.map i y) (F.map i z) = 0 := by
        simp only [heq, metricDistance, riemannianEDistOf_self, ENNReal.toReal_zero]
      change r < metricDistance (X.obj (f i)).metric (F.map i y) (F.map i z) at hiz
      linarith
    obtain ⟨a, ha, hae⟩ := exists_minimizingArm_of_complete (X.obj (f i)).metric hcomplete'
      (F.map i y) (F.map i p) hyp
    obtain ⟨b, hb, hbe⟩ := exists_minimizingArm_of_complete (X.obj (f i)).metric hcomplete'
      (F.map i y) (F.map i z) hyz
    exact ⟨a, b, ha, hb, hae, hbe, ha.symm ▸ hip, hb.symm ▸ hiz⟩
  let u := fun i => if h : E i then (Classical.choose h).point r else F.map i y
  let v := fun i => if h : E i then (Classical.choose (Classical.choose_spec h)).point r
    else F.map i y
  have hu : ∀ᶠ i in atTop,
      riemannianEDistOf (X.obj (f i)).metric (F.map i y) (u i) = ENNReal.ofReal r ∧
      metricDistance (X.obj (f i)).metric (u i) (F.map i p) =
        metricDistance (X.obj (f i)).metric (F.map i y) (F.map i p) - r := by
    filter_upwards [hE] with i hi
    let a := Classical.choose hi
    have hs := Classical.choose_spec (Classical.choose_spec hi)
    have hri : r ∈ Icc (0 : ℝ) a.length := ⟨hr.le, hs.2.2.2.2.1.le⟩
    have hu' : u i = a.point r := dite_eq_left hi
    rw [hu']
    constructor
    · exact a.edistOf_start hri
    · have hh := a.minimizing r hri a.length ⟨a.length_pos.le, le_rfl⟩
      rw [hs.2.2.1, abs_of_neg (sub_neg.mpr hs.2.2.2.2.1), hs.1] at hh
      exact hh.trans (by ring)
  have hv : ∀ᶠ i in atTop,
      riemannianEDistOf (X.obj (f i)).metric (F.map i y) (v i) = ENNReal.ofReal r ∧
      metricDistance (X.obj (f i)).metric (v i) (F.map i z) =
        metricDistance (X.obj (f i)).metric (F.map i y) (F.map i z) - r := by
    filter_upwards [hE] with i hi
    let b := Classical.choose (Classical.choose_spec hi)
    have hs := Classical.choose_spec (Classical.choose_spec hi)
    have hri : r ∈ Icc (0 : ℝ) b.length := ⟨hr.le, hs.2.2.2.2.2.le⟩
    have hv' : v i = b.point r := dite_eq_left hi
    rw [hv']
    constructor
    · exact b.edistOf_start hri
    · have hh := b.minimizing r hri b.length ⟨b.length_pos.le, le_rfl⟩
      rw [hs.2.2.2.1, abs_of_neg (sub_neg.mpr hs.2.2.2.2.2), hs.2.1] at hh
      exact hh.trans (by ring)
  have hangle := eventually_lt_comparisonAngle_of_pointed_distance_lenses C href hcomplete
    hsec y p z u v hr hrp hrz hu hv hθ
  filter_upwards [hE, hangle] with i hi hanglei
  refine ⟨Classical.choose hi, Classical.choose (Classical.choose_spec hi), ?_⟩
  have hs := Classical.choose_spec (Classical.choose_spec hi)
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2,
    by simpa only [u, v, dite_eq_left hi] using hanglei⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
