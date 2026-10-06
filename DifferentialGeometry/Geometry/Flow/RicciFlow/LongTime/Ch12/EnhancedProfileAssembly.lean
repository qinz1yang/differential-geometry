import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EnhancedProfileScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EnhancedProfileCapJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.DerivativeAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.DerivativeAssemblyW1
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.InteriorScaleMain

/-!
# CH12-O2, group 4: WBD03 physical form and the conditional A13 under P1–P4

`hW1_of_enhanced_O2` produces the physical whole-ball bound in **exactly** the shape of `hphysical`
(`LongTime/UniformNormalizedDerivativeBounds.lean:21`, consumed by S5's
`exists_normalized_bound_of_physical_W1`), for every `K`.

Proof structure: split each test ball by the recent-surgery scale.

* macroscopic (`Λ · h ≤ ρ` for every recent cutoff radius `h`): the W2 + W3 output, an explicit
  input `MacroWholeBall_O2` (KL83.1/84.2 seed + KL84.1 buffered region + first exit + Shi;
  not proved here);
* microscopic (`ρ < Λ · h` for some recent `h`): the micro-regime glue `MicroWholeBall_O2`,
  an explicit input that is **given the proved W4 and W5 outputs** (`W4_scalar_bound_O2`,
  `late_cap_window_jets_O2`) as arguments.

`late_derivative_tests_of_flow_of_enhanced_O2` is A13 (`LateCutGeometry.lean:158`) under
P1–P4 and the remaining explicit inputs hT1, hT3 (other lanes), G2 (`CollarNegativePlane K`).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian Set
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- W2 + W3 output (explicit input shape; KL83.1/84.2 seed + WBD01 buffered estimate): whole-ball
bounds of all orders at test balls above `Λ` times every recent cutoff radius. -/
def MacroWholeBall_O2 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) : Prop :=
  ∀ w : ℝ, 0 < w → ∃ (Λ b T : ℝ) (A : ℕ → ℝ), 1 ≤ Λ ∧ 0 < b ∧
    ∀ s : RegularSlice F.observation, T ≤ s.time →
    ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ b * Real.sqrt s.time →
      (∀ n (i : Fin (F.tower.history n).eventCount),
        (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time →
        ∀ h, Λ * (Hp.records n i).nominalRadius h ≤ ρ) →
      (∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt s.metric z 0) →
      (∀ q ∈ riemannianBallOf s.metric p ρ,
        SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹)) →
      ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
      ∀ k : ℕ, ∀ q ∈ riemannianBallOf s.metric p ρ,
        curvatureDerivativeNorm s.metric k q ≤ A k * (ρ ^ (k + 2))⁻¹

/-- Micro-regime whole-ball bound (explicit input shape): for every `Λ`, at test balls below `Λ`
times some recent cutoff radius.  (D-WBD §5: KL70.2 at canonical scale 1/2 + local Shi on
unscathed backward neighborhoods + the cap-window jets near new caps.) -/
def MicroWholeBall_O2 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) : Prop :=
  ∀ w : ℝ, 0 < w → ∀ Λ : ℝ, 1 ≤ Λ → ∃ (b T : ℝ) (A : ℕ → ℝ), 0 < b ∧
    ∀ s : RegularSlice F.observation, T ≤ s.time →
    ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ b * Real.sqrt s.time →
      (∃ n, ∃ i : Fin (F.tower.history n).eventCount, ∃ h,
        (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time ∧
        ρ < Λ * (Hp.records n i).nominalRadius h) →
      (∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt s.metric z 0) →
      (∀ q ∈ riemannianBallOf s.metric p ρ,
        SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹)) →
      ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
      ∀ k : ℕ, ∀ q ∈ riemannianBallOf s.metric p ρ,
        curvatureDerivativeNorm s.metric k q ≤ A k * (ρ ^ (k + 2))⁻¹

/-- **WBD03, physical form, under P1–P4.**  The conclusion's second component is `hphysical`
verbatim (`UniformNormalizedDerivativeBounds.lean:21`), for every `K`. -/
theorem hW1_of_enhanced_O2 (F : GC.Interface.RawSurgery P g) (K : ℕ) (δ : ℝ → ℝ)
    (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hP1 : P1_O2 Hp) (Ctime : ℝ≥0) (hP2 : P2_O2 Hp Ctime) (hP3 : P3_O2 Hp) (hP4 : P4_O2 Hp)
    (hW3 : MacroWholeBall_O2 Hp)
    (hMicro : P2_O2 Hp Ctime → (∀ κ : ℝ, 0 < κ → ∀ (Cgrad : ℝ≥0) (phi : ℝ → ℝ),
        Perelman.AdmissiblePinchingFunction phi → W4Output_O2 Hp κ Ctime Cgrad phi) →
      (∀ N : ℕ, capWindowJets_O2 Hp N) → MicroWholeBall_O2 Hp) :
    ∃ (b T : ℝ → ℝ) (A : ℝ → ℕ → ℝ), (∀ w : ℝ, 0 < w → 0 < b w) ∧
      ∀ w : ℝ, 0 < w → ∀ s : RegularSlice F.observation,
        T w ≤ s.time → ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ →
        ρ ≤ b w * Real.sqrt s.time →
        (∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt s.metric z 0) →
        (∀ q ∈ riemannianBallOf s.metric p ρ,
          SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹)) →
        ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
        ∀ k : ℕ, k ≤ K → ∀ q ∈ riemannianBallOf s.metric p ρ,
          curvatureDerivativeNorm s.metric k q ≤ A w k * (ρ ^ (k + 2))⁻¹ := by
  classical
  have hW4 : ∀ κ : ℝ, 0 < κ → ∀ (Cgrad : ℝ≥0) (phi : ℝ → ℝ),
      Perelman.AdmissiblePinchingFunction phi → W4Output_O2 Hp κ Ctime Cgrad phi :=
    fun κ hκ Cgrad _ hphi => W4_scalar_bound_O2 Hp hP4 κ hκ Ctime Cgrad hphi
  have hW5 : ∀ N : ℕ, capWindowJets_O2 Hp N := fun N => late_cap_window_jets_O2 Hp hdec hP1 hP3 N
  have hmicro := hMicro hP2 hW4 hW5
  have key : ∀ w : ℝ, 0 < w → ∃ (b T : ℝ) (A : ℕ → ℝ), 0 < b ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ b * Real.sqrt s.time →
        (∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt s.metric z 0) →
        (∀ q ∈ riemannianBallOf s.metric p ρ,
          SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹)) →
        ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
        ∀ k : ℕ, k ≤ K → ∀ q ∈ riemannianBallOf s.metric p ρ,
          curvatureDerivativeNorm s.metric k q ≤ A k * (ρ ^ (k + 2))⁻¹ := by
    intro w hw
    obtain ⟨Λ, b₁, T₁, A₁, hΛ, hb₁, h₁⟩ := hW3 w hw
    obtain ⟨b₂, T₂, A₂, hb₂, h₂⟩ := hmicro w hw Λ hΛ
    refine ⟨min b₁ b₂, max T₁ T₂, fun k => max (A₁ k) (A₂ k), lt_min hb₁ hb₂, ?_⟩
    intro s hs p ρ hρ hρb hneg hsec hvol k _ q hq
    have hpos : (0 : ℝ) ≤ (ρ ^ (k + 2))⁻¹ := inv_nonneg.mpr (pow_nonneg hρ.le _)
    have hsq := Real.sqrt_nonneg s.time
    by_cases hmac : ∀ n (i : Fin (F.tower.history n).eventCount),
        (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time →
        ∀ h, Λ * (Hp.records n i).nominalRadius h ≤ ρ
    · exact (h₁ s ((le_max_left _ _).trans hs) p ρ hρ
        (hρb.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hsq)) hmac hneg hsec hvol
        k q hq).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos)
    · push Not at hmac
      obtain ⟨n, i, hi, h, hlt⟩ := hmac
      exact (h₂ s ((le_max_right _ _).trans hs) p ρ hρ
        (hρb.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hsq)) ⟨n, i, h, hi, hlt⟩
        hneg hsec hvol k q hq).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hpos)
  choose! b T A hb hbound using key
  exact ⟨b, T, A, hb, hbound⟩

/-- **A13 under P1–P4** (conditional): A13's hypotheses verbatim, plus the profile `Hp` and P1–P4,
plus the remaining explicit inputs (W2/W3 macro output, micro glue, hT1, hT3, G2). -/
theorem late_derivative_tests_of_flow_of_enhanced_O2 (F : GC.Interface.RawSurgery P g) (K : ℕ)
    (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ)
    (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (slices : ℕ → RegularSlice F.observation)
    (htimes : ∀ j : ℕ, (j : ℝ) < (slices j).time)
    (hnonempty : ∀ j : ℕ, Nonempty (slices j).stage.Carrier)
    (L : LateCutFamily F K slices)
    (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hP1 : P1_O2 Hp) (Ctime : ℝ≥0) (hP2 : P2_O2 Hp Ctime) (hP3 : P3_O2 Hp) (hP4 : P4_O2 Hp)
    (hW3 : MacroWholeBall_O2 Hp)
    (hMicro : P2_O2 Hp Ctime → (∀ κ : ℝ, 0 < κ → ∀ (Cgrad : ℝ≥0) (phi : ℝ → ℝ),
        Perelman.AdmissiblePinchingFunction phi → W4Output_O2 Hp κ Ctime Cgrad phi) →
      (∀ N : ℕ, capWindowJets_O2 Hp N) → MicroWholeBall_O2 Hp)
    -- T1 (TCF03), as in `late_derivative_tests_of_flow_assembly_W1`
    (hT1 : ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ, ∀ j, N ≤ j → ∀ C i, L.thin j C i →
      ∀ p : ((L.decomposition j C).component i).Carrier,
        distanceToBoundary ((L.decomposition j C).component i) (L.metric j C i) p ≤
          ENNReal.ofReal 10 →
      ∀ r : ℝ, 0 < r → ENNReal.ofReal r < curvatureRadius (L.metric j C i) p →
      ∀ k : ℕ, k ≤ K → ∀ q ∈ riemannianBallOf (L.metric j C i) p r,
        curvatureDerivativeNorm (L.metric j C i) k q ≤ A * (r ^ (k + 2))⁻¹)
    -- T3 (TCF04), as in `late_derivative_tests_of_flow_assembly_W1`
    (hT3 : ∀ w : ℝ, 0 < w → w < euclideanThreeUnitBallVolume → ∀ b : ℝ, 0 < b →
      ∃ N : ℕ, ∀ j, N ≤ j → ∀ c i, L.thin j c i →
        ∀ p : ((L.decomposition j c).component i).Carrier,
          ENNReal.ofReal 10 <
            distanceToBoundary ((L.decomposition j c).component i) (L.metric j c i) p →
          ∀ r : ℝ, 0 < r → ENNReal.ofReal r < curvatureRadius (L.metric j c i) p →
            ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (L.metric j c i) p r → r < b)
    -- G2 of T2 (S2)
    (hG2 : CollarNegativePlane.{u} K) :
    L.hasEventualDerivativeBounds := by
  obtain ⟨b, T, A, hb, hphys⟩ :=
    hW1_of_enhanced_O2 F K δ Hp hdec hP1 Ctime hP2 hP3 hP4 hW3 hMicro
  exact late_derivative_tests_of_flow_assembly_W1 F K hK δ hadm hdec slices htimes hnonempty L
    hT1 (LateCutFamily.hT2_shape_T2 L hG2) hT3
    (exists_normalized_bound_of_physical_W1 F K b T A hb hphys)

end GC.LongTime.Ch12
