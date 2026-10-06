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

/-- (2) Feed the restarted meridian to P2, P3, P4 (type check only). -/
example
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (M : PrescribedCuspMeridian L.cores) : True := by
  have _p2 := exists_attained_leastExteriorDiskArea K hK δ hadm hdec M
  have _p3 := local_disk_comparisons_of_cusp_exterior K hK δ hadm hdec M
  obtain ⟨H⟩ := hadm
  have _p4 := exists_local_upper_barrier_of_exteriorDiskArea K hK δ H hdec M
  trivial

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

/-- (4) Producer 1 replaced by `via_restart_CPRS` + `hP2After`; producers 2-4 and the assembly
of `hasExteriorAreaObstructionAfter_of_producers` unchanged. -/
theorem hasExteriorAreaObstructionAfter_of_producers_restart_FX1
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (hP2After : ∀ M : PrescribedCuspMeridianTop_CPQ L.cores, ∃ T₀ : ℝ, ∃ h₀ : M.exterior.start ≤ T₀,
      ∀ t : ℝ, ∀ ht : T₀ ≤ t, ∃ u : C(closedDisk, (postStage F.observation t).Carrier),
        isExteriorSpanningDisk (M.exterior.region t) (M.transported t (h₀.trans ht)) u)
    (j : ℕ) (hj : L.first ≤ j) (C : ConnectedComponents (slices j).stage.Carrier) :
    hasAttainedExteriorAreaObstructionAfter F (L.decomposition j C) := by
  intro s x hcomp
  obtain ⟨M⟩ := exists_primitive_meridian_of_compressible_seam_via_restart_CPRS K hK δ hadm hdec
    L j hj C s x hcomp hP2After
  obtain ⟨H⟩ := hadm
  obtain ⟨Tm, hm, hmin⟩ := exists_attained_leastExteriorDiskArea K hK δ ⟨H⟩ hdec M
  obtain ⟨Tc, hc, hcomparison⟩ := local_disk_comparisons_of_cusp_exterior K hK δ ⟨H⟩ hdec M
  obtain ⟨Tb, hb, hbarrier⟩ := exists_local_upper_barrier_of_exteriorDiskArea K hK δ H hdec M
  let T := max Tm (max Tc Tb)
  have hTm : Tm ≤ T := le_max_left _ _
  have hTc : Tc ≤ T := le_trans (le_max_left _ _) (le_max_right _ _)
  have hTb : Tb ≤ T := le_trans (le_max_right _ _) (le_max_right _ _)
  have hstart : M.exterior.start ≤ T := hm.trans hTm
  let γ := M.loopAfter T hstart
  have hmin' : hasExteriorDiskMinimizersAfter F.observation M.exterior.region T γ := (hmin T hTm).1
  refine ⟨T, H.scalarShift, M.exterior.region, γ,
    (L.cores.start_pos.le.trans M.exterior.after_cores).trans hstart, H.scalarShift_pos, hmin', ?_, ?_⟩
  · exact continuousOn_exteriorDiskArea_of_local_comparisons _ _ _ _ hmin'
      (hcomparison T hTc hmin')
  · exact hbarrier T hTb hmin'

end GC.LongTime.CuspP1
