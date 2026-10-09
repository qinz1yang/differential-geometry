import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.MeridianTopAssemblyV6

/-!
# CP1-RS: restart bridge (D-AB-2)

`hP2After` (an explicit hypothesis shape, discharged by the Top-input eventual strong-disk supplier
of producer 2) gives, for each Top object `M₀`, a threshold `T₀ ≥ M₀.exterior.start` after which a
strong spanning disk exists.  The exterior is restarted at `T₀` (truncation unchanged) and the
original `PrescribedCuspMeridian` is rebuilt.  Region equality is only claimed for `t ≥ T₀`.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert GC.Topology
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

open GC.LongTime

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- Restart the exterior at `T₀ ≥ start`: same truncation. -/
def _root_.GC.LongTime.PersistentCuspExterior.restart_CPRS (E : PersistentCuspExterior cores)
    (T₀ : ℝ) (h₀ : E.start ≤ T₀) : PersistentCuspExterior cores where
  truncation := E.truncation
  start := T₀
  after_cores := E.after_cores.trans h₀
  in_ball := fun i t ht => E.in_ball i t (h₀.trans ht)

theorem _root_.GC.LongTime.PersistentCuspExterior.region_restart_CPRS
    (E : PersistentCuspExterior cores) (T₀ : ℝ) (h₀ : E.start ≤ T₀) (t : ℝ) (ht : T₀ ≤ t) :
    (E.restart_CPRS T₀ h₀).region t = E.region t := by
  unfold PersistentCuspExterior.region
  have ht' : (E.restart_CPRS T₀ h₀).start ≤ t := ht
  rw [dif_pos ht', dif_pos (h₀.trans ht)]
  rfl

/-- Restart a Top object at `T₀`, given strong disks for all `t ≥ T₀`. -/
def PrescribedCuspMeridianTop_CPQ.restartStrong_CPRS (M₀ : PrescribedCuspMeridianTop_CPQ cores)
    (T₀ : ℝ) (h₀ : M₀.exterior.start ≤ T₀)
    (disks : ∀ t : ℝ, ∀ ht : T₀ ≤ t, ∃ u : C(closedDisk, (postStage F.observation t).Carrier),
      isExteriorSpanningDisk (M₀.exterior.region t) (M₀.transported t (h₀.trans ht)) u) :
    PrescribedCuspMeridian cores where
  exterior := M₀.exterior.restart_CPRS T₀ h₀
  model := M₀.model
  port := M₀.port
  loop := M₀.loop
  embedded := M₀.embedded
  smooth := M₀.smooth
  geodesic := M₀.geodesic
  primitive := M₀.primitive
  short := M₀.short
  transported := fun t ht => M₀.transported t (h₀.trans ht)
  prescribed := fun t ht x => M₀.prescribed t (h₀.trans ht) x
  spans := fun t ht => by
    obtain ⟨u, hu⟩ := disks t ht
    refine ⟨u, ?_⟩
    rw [PersistentCuspExterior.region_restart_CPRS M₀.exterior T₀ h₀ t ht]
    exact hu

theorem exists_primitive_meridian_of_compressible_seam_via_restart_CPRS
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (j : ℕ) (hj : L.first ≤ j) (C : ConnectedComponents (slices j).stage.Carrier)
    (s : Fin (L.decomposition j C).boundary.count) (x : Torus)
    (hcomp : ¬ Function.Injective (FundamentalGroup.map
      ((L.decomposition j C).reconstructionAtlas.torusInPrime (L.decomposition j C).reconstruction s) x))
    (hP2After : ∀ M : PrescribedCuspMeridianTop_CPQ L.cores, ∃ T₀ : ℝ, ∃ h₀ : M.exterior.start ≤ T₀,
      ∀ t : ℝ, ∀ ht : T₀ ≤ t, ∃ u : C(closedDisk, (postStage F.observation t).Carrier),
        isExteriorSpanningDisk (M.exterior.region t) (M.transported t (h₀.trans ht)) u) :
    Nonempty (PrescribedCuspMeridian L.cores) := by
  obtain ⟨M⟩ := exists_primitive_meridian_top_CPA3 K hK δ hadm hdec L j hj C s x hcomp
  obtain ⟨T₀, h₀, disks⟩ := hP2After M
  exact ⟨M.restartStrong_CPRS T₀ h₀ disks⟩

end GC.LongTime.CuspP1
