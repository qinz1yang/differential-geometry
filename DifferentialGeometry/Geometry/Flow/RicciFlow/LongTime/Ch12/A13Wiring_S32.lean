import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.AllBranchesAssembly_CX9
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EnhancedProfileAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.W2Assembly_CX2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LTF03Wiring_S32

set_option autoImplicit false

/-!
# CH12-S32 (G2): A13 from the named supplies

Pure wiring, no new mathematics.  `late_derivative_tests_of_flow_of_supplies_S32` is A13
(`late_derivative_tests_of_flow_allBranches_CX9`, same binders and conclusion) with its two
external inputs replaced by the supplies of the other lanes, for **a given profile `Hp`**:

* `hW1` (normalised form) is obtained from the physical form of `hW1_of_enhanced_O2`
  (`P1`–`P4`, the macro whole-ball statement `macroWholeBall_of_G2_CX2 Hp hdec hG2`, and `hMicro`)
  by `exists_normalized_bound_of_physical_W1`;
* `hLTF03` (for every profile and every negative-branch witness) is `hLTF03_of_P6_G2_S32`; the
  profile argument of `SeedHyperbolicOnFixedBallsSeq_S13` is an unused binder, so the statement
  for `Hp` is the statement for every profile.

Quantifier form: the supplies `P1`–`P4`, `P6`, `hG2`, `hMicro` all mention the nominal radii of the
records of `Hp`, i.e. they are properties of one profile; stating them for every profile would
demand them for profiles that never occur.  A given `Hp` is also what the supplying lanes state,
and it is equivalent to an existential over the profile (the shape of `hadm`).
-/

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.LongTime
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch12
universe u

/-- **A13 from the supplies.**  Binders `F … L` exactly as in
`late_derivative_tests_of_flow_allBranches_CX9`; then a profile `Hp`, the profile hypotheses
`P1`–`P4` (with `Ctime`) and `P6`, the KL84.2 backward-seed statement `hG2` (binder of
`W2Assembly_CX2.lean`, l.24–49) and the micro-regime glue `hMicro` (binder of
`hW1_of_enhanced_O2`). -/
theorem late_derivative_tests_of_flow_of_supplies_S32 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ)
    (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (slices : ℕ → RegularSlice F.observation)
    (htimes : ∀ j : ℕ, (j : ℝ) < (slices j).time)
    (hnonempty : ∀ j : ℕ, Nonempty (slices j).stage.Carrier)
    (L : GC.LongTime.LateCutFamily F K slices)
    (Hp : AnalyticSurgeryProfile F δ)
    (hP1 : P1_O2 Hp) (Ctime : ℝ≥0) (hP2 : P2_O2 Hp Ctime) (hP3 : P3_O2 Hp) (hP4 : P4_O2 Hp)
    (hP6 : P6_S23 Hp)
    (hG2 : ∀ w : ℝ, 0 < w → ∃ a c c₁ Λ₀ b₀ T₀ : ℝ,
      0 < a ∧ 2 * a ^ 2 < c ∧ 0 < c₁ ∧ 1 ≤ Λ₀ ∧ 0 < b₀ ∧ 0 < T₀ ∧
      ∀ s : RegularSlice F.observation, T₀ ≤ s.time →
      ∀ (p : (s.history.stageAt (sliceTop_S8 s)).Carrier) (r : ℝ), 0 < r →
        r ≤ b₀ * Real.sqrt s.time →
        (∀ q ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) p r,
          SectionalBoundedBelowAt (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time)
            q (-(r ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume
          (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) p r →
        (∀ n (i : Fin (F.tower.history n).eventCount),
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time →
          ∀ h, Λ₀ * (Hp.records n i).nominalRadius h ≤ r) →
        ∃ y ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) p r,
          ∀ v : Icc (0 : ℝ) s.history.horizon, s.time - c * r ^ 2 ≤ v.val →
          ∃ yv : (s.history.stageAt v).Carrier,
            (v.val = s.time → HEq yv y) ∧
            hasSmallParabolicCurvature s.history v yv (a * r) ∧
            ENNReal.ofReal (c₁ * (a * r) ^ 3) ≤
              ballVolume (s.history.stageMetric (s.history.activeStage v) v) yv (a * r) ∧
            ∃ A : BackwardPointTrace s.history (s.history.activeStage v)
                (s.history.activeStage (sliceTop_S8 s))
                (s.history.activeStage_mono (show v ≤ sliceTop_S8 s from v.property.2)) y,
              A.point (s.history.activeStage v) le_rfl
                (s.history.activeStage_mono (show v ≤ sliceTop_S8 s from v.property.2)) = yv)
    (hMicro : P2_O2 Hp Ctime → (∀ κ : ℝ, 0 < κ → ∀ (Cgrad : ℝ≥0) (phi : ℝ → ℝ),
        Perelman.AdmissiblePinchingFunction phi → W4Output_O2 Hp κ Ctime Cgrad phi) →
      (∀ N : ℕ, capWindowJets_O2 Hp N) → MicroWholeBall_O2 Hp) :
    L.hasEventualDerivativeBounds := by
  obtain ⟨b, T, A, hb, hphys⟩ :=
    hW1_of_enhanced_O2 F K δ Hp hdec hP1 Ctime hP2 hP3 hP4
      (macroWholeBall_of_G2_CX2 Hp hdec hG2) hMicro
  exact late_derivative_tests_of_flow_allBranches_CX9 F K hK δ hadm hdec slices htimes hnonempty L
    (fun _ hn S a v Lr => hLTF03_of_P6_G2_S32 Hp hdec hn hP6 hG2 S a v Lr)
    (exists_normalized_bound_of_physical_W1 F K b T A hb hphys)

end GC.LongTime.Ch12
