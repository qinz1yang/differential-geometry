import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.P2AdapterImportedTop
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.P2AdapterCompetitorHCOpen

/-!
# S-HCOMP G3: `exists_eventual_confined_morrey_disk` without `hcomp` (and without `hloop`)

`PrescribedCuspMeridianTop_CPQ.exists_eventual_confined_morrey_disk_P2A`
(`P2AdapterImportedTop.lean:266`) with its two explicit parameters discharged:
* `hloop := fun t ht => M.transported_isSmoothEmbeddedLoop_P2A t ht` (P2A-13, `P2AdapterOwnLoop`);
* `hcomp := M.competitors_nonempty_HC` (S-HCOMP G2, from `fills` and the compact-range
  rel-boundary smooth approximation of G1).

The conclusion is verbatim that of the `_P2A` theorem.  Axioms: `propext`, `Classical.choice`,
`Quot.sound`, plus `sorryAx` only through the explicit section-A mirrors of
`P2AdapterImportedLemmas` (the user-authorized sorries of lane P2A-24, listed in
`docs/geometrization/chapter15/p2-adapter-sorries.md`); nothing in this file is a `sorry`.
Like `P2AdapterImported{Defs,Lemmas,Top}` this module is NOT registered in the root aggregate and
may not be imported by any module outside the `P2AdapterImported*` family.
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

/-- **G3.**  Top version of IMS03 `PrescribedCuspMeridian.exists_eventual_confined_morrey_disk`
(`CuspProfileDisk.lean:21` @ 981d9a8cd) with no extra hypotheses: the smooth embedded loop and the
competitor non-emptiness are produced from `fills`. -/
theorem PrescribedCuspMeridianTop_CPQ.exists_eventual_confined_morrey_disk_HC
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
  exact M.exists_eventual_confined_morrey_disk_P2A tmin
    (fun t ht => M.transported_isSmoothEmbeddedLoop_P2A t ht) M.competitors_nonempty_HC

/-- Consumer check: the exact type of `hcomp` is that of `competitors_nonempty_HC`, so the
`_P2A` theorem applies verbatim with `hloop` and `hcomp` supplied by P2A-13 and G2. -/
example (M : PrescribedCuspMeridianTop_CPQ cores) (tmin : ℝ) :=
  M.exists_eventual_confined_morrey_disk_P2A tmin
    (fun t ht => M.transported_isSmoothEmbeddedLoop_P2A t ht) M.competitors_nonempty_HC

end GC.LongTime.CuspP1
