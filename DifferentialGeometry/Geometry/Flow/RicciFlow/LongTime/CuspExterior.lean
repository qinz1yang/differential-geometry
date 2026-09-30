import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.PersistentHyperbolicCores
import DifferentialGeometry.Geometry.Hyperbolic.Truncation
import DifferentialGeometry.Geometry.Geodesic.Equation.Basic
import DifferentialGeometry.Topology.LoopSpace.CircleDegree

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint Set
open scoped Manifold ContDiff
namespace GC.LongTime
universe u

structure PersistentCuspExterior {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} (cores : PersistentHyperbolicCores F K) where
  truncation : (i : Fin cores.count) → HyperbolicTruncation (cores.model i)
  start : ℝ
  after_cores : cores.start ≤ start
  in_ball : ∀ i t, start ≤ t → range (truncation i).inclusion ⊆
    riemannianBallOf (cores.model i).metric
      (cores.model i).basepoint (cores.accuracy t)⁻¹

def PersistentCuspExterior.region {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} {cores : PersistentHyperbolicCores F K}
    (E : PersistentCuspExterior cores) (t : ℝ) : Set (postStage F.observation t).Carrier :=
  if ht : E.start ≤ t then
    (⋃ i, cores.map i t (E.after_cores.trans ht) ''
      ((E.truncation i).inclusion '' ((E.truncation i).core.interior : Set (E.truncation i).core.Carrier)))ᶜ
  else univ

structure PrescribedCuspMeridian {P : OrientedThreeStage.{u}} {g : P.Metric}
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
  spans : ∀ t (ht : exterior.start ≤ t), ∃ u : C(closedDisk, (postStage F.observation t).Carrier),
    isExteriorSpanningDisk (exterior.region t) (transported t ht) u

def PrescribedCuspMeridian.loopAfter {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} {cores : PersistentHyperbolicCores F K}
    (M : PrescribedCuspMeridian cores) (T : ℝ) (hT : M.exterior.start ≤ T)
    (t : ℝ) (ht : T ≤ t) : freeLoop (postStage F.observation t).Carrier :=
  M.transported t (hT.trans ht)

end GC.LongTime
