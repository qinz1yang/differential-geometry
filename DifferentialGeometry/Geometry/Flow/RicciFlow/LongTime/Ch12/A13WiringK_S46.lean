import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.A13Wiring_S32
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EnhancedProfileAssemblyK_S46

set_option autoImplicit false

/-!
# CH12-S46 (G2): A13 from the named supplies, with the K-indexed micro glue

Pure wiring.  `late_derivative_tests_of_flow_of_supplies_K_S46` is
`late_derivative_tests_of_flow_of_supplies_S32` (`A13Wiring_S32.lean:47`) with the last binder
`hMicro : ... → MicroWholeBall_O2 Hp` replaced by
`hMicroK : ... → MicroWholeBallK_S44 Hp K` (the order cap `K` of the theorem itself; the late time and
constants of the micro glue may depend on `K`).  All other binders and the conclusion
`L.hasEventualDerivativeBounds` are unchanged; the proof is the S32 proof with
`hW1_of_enhanced_K_S46` in place of `hW1_of_enhanced_O2`.  A13 is stated for the fixed `K` of the
theorem, so the K-indexed glue suffices.
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

/-- **A13 from the supplies, K-indexed micro glue.**  Binders `F … hG2` exactly as in
`late_derivative_tests_of_flow_of_supplies_S32`; the last binder `hMicroK` is the micro-regime glue
for the order cap `K`. -/
theorem late_derivative_tests_of_flow_of_supplies_K_S46 {P : OrientedThreeStage.{u}} {g : P.Metric}
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
    (hMicroK : P2_O2 Hp Ctime → (∀ κ : ℝ, 0 < κ → ∀ (Cgrad : ℝ≥0) (phi : ℝ → ℝ),
        Perelman.AdmissiblePinchingFunction phi → W4Output_O2 Hp κ Ctime Cgrad phi) →
      (∀ N : ℕ, capWindowJets_O2 Hp N) → MicroWholeBallK_S44 Hp K) :
    L.hasEventualDerivativeBounds := by
  obtain ⟨b, T, A, hb, hphys⟩ :=
    hW1_of_enhanced_K_S46 F K δ Hp hdec hP1 Ctime hP2 hP3 hP4
      (macroWholeBall_of_G2_CX2 Hp hdec hG2) hMicroK
  exact late_derivative_tests_of_flow_allBranches_CX9 F K hK δ hadm hdec slices htimes hnonempty L
    (fun _ hn S a v Lr => hLTF03_of_P6_G2_S32 Hp hdec hn hP6 hG2 S a v Lr)
    (exists_normalized_bound_of_physical_W1 F K b T A hb hphys)

end GC.LongTime.Ch12
