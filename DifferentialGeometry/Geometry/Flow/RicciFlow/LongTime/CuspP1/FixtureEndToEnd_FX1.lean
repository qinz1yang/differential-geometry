import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.RouteWFinalWA2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.RestartBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.MeridianTopAssemblyV6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspExteriorProducers
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.LateDecomposition

/-!
# FX1: end-to-end type-assembly fixture (D-AB-6 (1))

Type/data-flow checks only.  The skeleton hypotheses and `hP2After` are carried as explicit
hypotheses, so none of this is non-vacuity evidence.
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

/-- (1) No data is re-chosen by `restartStrong_CPRS`. -/
theorem restartStrong_data_FX1 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} {cores : PersistentHyperbolicCores F K}
    (M₀ : PrescribedCuspMeridianTop_CPQ cores) (T₀ : ℝ) (h₀ : M₀.exterior.start ≤ T₀)
    (disks : ∀ t : ℝ, ∀ ht : T₀ ≤ t, ∃ u : C(closedDisk, (postStage F.observation t).Carrier),
      isExteriorSpanningDisk (M₀.exterior.region t) (M₀.transported t (h₀.trans ht)) u) :
    let M := M₀.restartStrong_CPRS T₀ h₀ disks
    M.model = M₀.model ∧ HEq M.port M₀.port ∧ M.loop = M₀.loop ∧
    M.exterior.truncation = M₀.exterior.truncation ∧ M.exterior.start = T₀ ∧
    (∀ t : ℝ, ∀ ht : T₀ ≤ t, M.exterior.region t = M₀.exterior.region t) ∧
    (∀ t : ℝ, ∀ (ht : M.exterior.start ≤ t),
      M.transported t ht = M₀.transported t (h₀.trans ht)) ∧
    M.exterior.start ≤ T₀ ∧ (∃ h : M.exterior.start ≤ T₀, M.transported T₀ h =
      M₀.transported T₀ h₀) := by
  intro M
  refine ⟨rfl, HEq.rfl, rfl, rfl, rfl, ?_, fun t ht => rfl, le_rfl, ⟨le_rfl, rfl⟩⟩
  intro t ht
  exact PersistentCuspExterior.region_restart_CPRS M₀.exterior T₀ h₀ t ht

/-- (1) End-to-end through the skeleton hypotheses. -/
theorem end_to_end_FX1
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
    ∃ (M₀ : PrescribedCuspMeridianTop_CPQ L.cores) (T₀ : ℝ) (h₀ : M₀.exterior.start ≤ T₀)
      (disks : ∀ t : ℝ, ∀ ht : T₀ ≤ t, ∃ u : C(closedDisk, (postStage F.observation t).Carrier),
        isExteriorSpanningDisk (M₀.exterior.region t) (M₀.transported t (h₀.trans ht)) u),
      let M := M₀.restartStrong_CPRS T₀ h₀ disks
      M.model = M₀.model ∧ HEq M.port M₀.port ∧ M.loop = M₀.loop ∧
      M.exterior.truncation = M₀.exterior.truncation ∧ M.exterior.start = T₀ := by
  obtain ⟨M₀⟩ := exists_primitive_meridian_top_CPA3 K hK δ hadm hdec L j hj C s x hcomp
  obtain ⟨T₀, h₀, disks⟩ := hP2After M₀
  exact ⟨M₀, T₀, h₀, disks, rfl, HEq.rfl, rfl, rfl, rfl⟩

/-- (2) The order of `L.cores` is exactly what P2-P4 need (`K + 4`, by `rfl`). -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices) :
    PersistentHyperbolicCores F (K + 4) := L.cores

/- The obsolete anonymous example calling the deleted P2/P3/P4 admissions was retired. -/

/-- (3) Region equality is usable for `t ≥ T₀`. -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
    {cores : PersistentHyperbolicCores F K} (E : PersistentCuspExterior cores)
    (T₀ : ℝ) (h₀ : E.start ≤ T₀) (t : ℝ) (ht : T₀ ≤ t) :
    (E.restart_CPRS T₀ h₀).region t = E.region t :=
  PersistentCuspExterior.region_restart_CPRS E T₀ h₀ t ht

/-- (3) For `t < T₀` the restarted region is `univ` (dif_neg branch), so the equality with the
old region is not claimed; the old region at `E.start ≤ t < T₀` is a complement of core images. -/
theorem region_restart_lt_FX1 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} {cores : PersistentHyperbolicCores F K}
    (E : PersistentCuspExterior cores) (T₀ : ℝ) (h₀ : E.start ≤ T₀) (t : ℝ) (ht : t < T₀) :
    (E.restart_CPRS T₀ h₀).region t = univ := by
  unfold PersistentCuspExterior.region
  have : ¬ (E.restart_CPRS T₀ h₀).start ≤ t := not_le.mpr ht
  rw [dif_neg this]

/-- (3) For `t < E.start` both regions are `univ`; for `E.start ≤ t < T₀` the old region is the
complement set of the core images, restart gives `univ`. -/
theorem region_old_eq_compl_FX1 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} {cores : PersistentHyperbolicCores F K}
    (E : PersistentCuspExterior cores) (t : ℝ) (ht : E.start ≤ t) :
    E.region t = (⋃ i, cores.map i t (E.after_cores.trans ht) ''
      ((E.truncation i).inclusion '' ((E.truncation i).core.interior :
        Set (E.truncation i).core.Carrier)))ᶜ := by
  unfold PersistentCuspExterior.region
  rw [dif_pos ht]

/-- (4) The restart-fixture conclusion follows from the proved Route W obstruction
without a separate eventual-disk existence hypothesis. -/
theorem hasExteriorAreaObstructionAfter_of_producers_restart_FX1
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (j : ℕ) (hj : L.first ≤ j) (C : ConnectedComponents (slices j).stage.Carrier) :
    hasAttainedExteriorAreaObstructionAfter F (L.decomposition j C) :=
  hasAttainedExteriorAreaObstructionAfter_of_routeW_final_WA K hK δ hadm hdec L j hj C

end GC.LongTime.CuspP1
