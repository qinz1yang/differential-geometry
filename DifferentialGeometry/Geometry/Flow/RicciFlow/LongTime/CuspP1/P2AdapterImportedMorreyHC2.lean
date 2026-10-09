import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.P2AdapterImportedTop_HC2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.P2AdapterCompetitorHCOpen

/-!
# S-MIRRORS G4 (`_HC2`): `exists_eventual_confined_morrey_disk_HC2`, free of placeholder proofs

`PrescribedCuspMeridianTop_CPQ.exists_eventual_confined_morrey_disk_P2A_HC2`
(`P2AdapterImportedTop_HC2.lean`) with its two explicit parameters discharged:
* `hloop := fun t ht => M.transported_isSmoothEmbeddedLoop_P2A t ht` (P2A-13, `P2AdapterOwnLoop`);
* `hcomp := M.competitors_nonempty_HC` (S-HCOMP G2, from `fills` and the compact-range
  rel-boundary smooth approximation of G1).

The conclusion is verbatim that of `exists_eventual_confined_morrey_disk_HC2`
(`P2AdapterImportedMorreyHC.lean`).  This module is the copy of that file whose chain uses the real
IMS03 theorems (`P2AdapterReal{1,2,3}_HC2`) instead of the placeholder mirrors of
`P2AdapterImportedLemmas`, so the axioms are `propext`, `Classical.choice`, `Quot.sound` only.
-/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.LongTime
open DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff Topology

namespace GC.LongTime.CuspP1

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- Top version of IMS03 `PrescribedCuspMeridian.exists_eventual_confined_morrey_disk`
(`CuspProfileDisk.lean:21` @ 981d9a8cd) with no extra hypotheses: the smooth embedded loop and the
competitor non-emptiness are produced from `fills`. -/
theorem PrescribedCuspMeridianTop_CPQ.exists_eventual_confined_morrey_disk_HC2
    (M : PrescribedCuspMeridianTop_CPQ cores) (tmin : ℝ) :
    ∃ a : ℝ, ∃ ha : 0 < a, ∃ T₀ : ℝ, ∃ h₀ : M.exterior.start ≤ T₀,
      tmin ≤ T₀ ∧ 1 ≤ T₀ ∧ ∀ (T : ℝ) (h : T₀ ≤ T) (t : ℝ) (ht : T ≤ t),
        ∃ ρ : (postStage F.observation t).Carrier → ℝ,
        ∃ hρ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ρ,
          M.exterior.region t = {x | ρ x ≤ 0} ∧
          IsCompact (closure {x | ρ x < a}) ∧
          (∀ x, 0 ≤ ρ x → ρ x < a →
            mfderiv (𝓡 3) 𝓘(ℝ) ρ x ≠ 0 ∧
            ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 →
              0 < hessFun (postMetric F.observation t) ρ x v v) ∧
          let U : Opens (postStage F.observation t).Carrier :=
            ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
          let δ : (postStage F.observation t).Carrier → ℝ := fun x => cutoff_P2A a (ρ x)
          let hδ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ δ :=
            (cutoff_smooth_P2A a).contMDiff.comp hρ
          let hU : ∀ x : (postStage F.observation t).Carrier, x ∈ U ↔ 0 < δ x :=
            fun x => (cutoff_pos_iff_P2A ha (ρ x)).symm
          let G := canonicalPositiveDomainMetric_P2A (postMetric F.observation t) hδ U hU
          let ι : C(U, (postStage F.observation t).Carrier) :=
            ⟨Subtype.val, continuous_subtype_val⟩
          ∃ (γU : freeLoop U) (q : C(closedDisk, U)),
            ι.comp γU = M.transported t ((h₀.trans h).trans ht) ∧
            IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γU ∧
            IsMorreyDisk G γU q ∧
            range (ι.comp q) ⊆ M.exterior.region t ∧
            (∀ z : closedDisk, ‖(z : ℂ)‖ < 1 →
              (ι.comp q) z ∈ interior (M.exterior.region t)) ∧
            (∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ρ ((ι.comp q) z) < 0) ∧
            (∀ θ : loopCircle, ρ ((ι.comp q) (diskBoundary θ)) = 0) ∧
            DiskWeakJordanTrace (M.transported t ((h₀.trans h).trans ht)) (ι.comp q) ∧
            ∀ z : closedDisk, ∀ᶠ y : U in 𝓝 (q z),
              G.inner y = ((postMetric F.observation t).restrictOpen U).inner y ∧
                barrier_P2A a (ρ (y : (postStage F.observation t).Carrier)) =
                  ρ (y : (postStage F.observation t).Carrier) := by
  exact M.exists_eventual_confined_morrey_disk_P2A_HC2 tmin
    (fun t ht => M.transported_isSmoothEmbeddedLoop_P2A t ht) M.competitors_nonempty_HC

/-- Type-alignment check: the exact type of `hcomp` is that of `competitors_nonempty_HC`, so the
`_P2A_HC2` theorem applies verbatim with `hloop` and `hcomp` supplied by P2A-13 and S-HCOMP. -/
example (M : PrescribedCuspMeridianTop_CPQ cores) (tmin : ℝ) :=
  M.exists_eventual_confined_morrey_disk_P2A_HC2 tmin
    (fun t ht => M.transported_isSmoothEmbeddedLoop_P2A t ht) M.competitors_nonempty_HC

/-- Consumer of G4: eventually there is a continuous closed disk inside the exterior region. -/
theorem PrescribedCuspMeridianTop_CPQ.exists_eventual_disk_in_region_HC2
    (M : PrescribedCuspMeridianTop_CPQ cores) (tmin : ℝ) :
    ∃ T₀ : ℝ, ∃ _ : M.exterior.start ≤ T₀, tmin ≤ T₀ ∧ ∀ (t : ℝ) (_ : T₀ ≤ t),
      ∃ u : C(closedDisk, (postStage F.observation t).Carrier),
        range u ⊆ M.exterior.region t := by
  obtain ⟨_, _, T₀, h₀, h1, _, h⟩ := M.exists_eventual_confined_morrey_disk_HC2 tmin
  refine ⟨T₀, h₀, h1, fun t ht => ?_⟩
  obtain ⟨_, _, _, _, _, γU, q, _, _, _, hrange, _⟩ := h T₀ le_rfl t ht
  exact ⟨_, hrange⟩

end GC.LongTime.CuspP1
