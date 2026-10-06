import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspExteriorProducers
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.MeridianTopBasic

/-!
# CP1-Q3: `PrescribedCuspMeridianTop_CPQ` and the bridge to `PrescribedCuspMeridian`

Review CP1-Q, Q3 / D-CP1Q-3.  Same fields as `PrescribedCuspMeridian` except `spans` is replaced by
`fills`: for every `t ≥ exterior.start` the prescribed transported loop bounds a *continuous* disk
inside `exterior.region t` (exact trace, range in the region).  The bridge
`toPrescribedCuspMeridian_CPQ` takes the same-start strong-disk upgrade contract (a regular exterior spanning disk for each
such `t`) as an explicit hypothesis; non-emptiness of the area comparison class is thus a real
producer-2 step (no `sInf ∅` convention is used).
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint Set
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

open GC.LongTime

structure PrescribedCuspMeridianTop_CPQ {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} (cores : PersistentHyperbolicCores F K) where
  exterior : PersistentCuspExterior cores
  model : Fin cores.count
  port : Fin (exterior.truncation model).count
  loop : freeLoop Torus
  embedded : Topology.IsEmbedding loop
  smooth : ContMDiff 𝓘(ℝ, ℝ) torusModel ∞ (loopLift loop)
  geodesic : DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesic
    ((exterior.truncation model).cusp port).torusMetric (loopLift loop)
  primitive : ∃ e : FundamentalGroup Torus (loop 0) ≃*
      Multiplicative ℤ × Multiplicative ℤ, e (loopDegreeClass loop 1) = (Multiplicative.ofAdd 1, 1)
  short : ∃ L : ℝ, 0 < L ∧ L < 1 ∧ ∀ s : ℝ,
    let v := mfderiv 𝓘(ℝ, ℝ) torusModel (loopLift loop) s 1;
    ((exterior.truncation model).cusp port).torusMetric.inner (loopLift loop s) v v ≤ L ^ 2
  transported : (t : ℝ) → exterior.start ≤ t → freeLoop (postStage F.observation t).Carrier
  prescribed : ∀ t (ht : exterior.start ≤ t) x,
    transported t ht x = cores.map model t (exterior.after_cores.trans ht)
      ((exterior.truncation model).cuspMap port (loop x, halfZero))
  fills : ∀ t (ht : exterior.start ≤ t), ∃ u : C(closedDisk, (postStage F.observation t).Carrier),
    diskTrace u = transported t ht ∧ Set.range u ⊆ exterior.region t

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- The original structure gives the Top one (the strong spanning disk has exact trace and lies
in the region). -/
def prescribedCuspMeridian_toTop_CPQ (M : PrescribedCuspMeridian cores) :
    PrescribedCuspMeridianTop_CPQ cores where
  exterior := M.exterior
  model := M.model
  port := M.port
  loop := M.loop
  embedded := M.embedded
  smooth := M.smooth
  geodesic := M.geodesic
  primitive := M.primitive
  short := M.short
  transported := M.transported
  prescribed := M.prescribed
  fills := fun t ht => by
    obtain ⟨u, hu⟩ := M.spans t ht
    exact ⟨u, hu.1, hu.2.2.2.1⟩

/-- Bridge.  `hP2` is the same-start strong-disk upgrade contract for the prescribed curve: whenever the
transported curve has a continuous filling in `exterior.region t`, there is a regular exterior
spanning disk (`isExteriorSpanningDisk`).  The filling hypothesis is supplied by `M.fills`, so
non-emptiness comes from the topology, not from an infimum convention. -/
def PrescribedCuspMeridianTop_CPQ.toPrescribedCuspMeridian (M : PrescribedCuspMeridianTop_CPQ cores)
    (hP2 : ∀ (t : ℝ) (ht : M.exterior.start ≤ t),
      (∃ u : C(closedDisk, (postStage F.observation t).Carrier),
        diskTrace u = M.transported t ht ∧ Set.range u ⊆ M.exterior.region t) →
      ∃ u : C(closedDisk, (postStage F.observation t).Carrier),
        isExteriorSpanningDisk (M.exterior.region t) (M.transported t ht) u) :
    PrescribedCuspMeridian cores where
  exterior := M.exterior
  model := M.model
  port := M.port
  loop := M.loop
  embedded := M.embedded
  smooth := M.smooth
  geodesic := M.geodesic
  primitive := M.primitive
  short := M.short
  transported := M.transported
  prescribed := M.prescribed
  spans := fun t ht => hP2 t ht (M.fills t ht)

theorem nonempty_top_iff_CPQ (hP2 : ∀ (M : PrescribedCuspMeridianTop_CPQ cores) (t : ℝ)
    (ht : M.exterior.start ≤ t),
      (∃ u : C(closedDisk, (postStage F.observation t).Carrier),
        diskTrace u = M.transported t ht ∧ Set.range u ⊆ M.exterior.region t) →
      ∃ u : C(closedDisk, (postStage F.observation t).Carrier),
        isExteriorSpanningDisk (M.exterior.region t) (M.transported t ht) u) :
    Nonempty (PrescribedCuspMeridianTop_CPQ cores) ↔ Nonempty (PrescribedCuspMeridian cores) :=
  ⟨fun ⟨M⟩ => ⟨M.toPrescribedCuspMeridian (hP2 M)⟩, fun ⟨M⟩ => ⟨prescribedCuspMeridian_toTop_CPQ M⟩⟩

end GC.LongTime.CuspP1
