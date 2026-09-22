import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HarnackLocalGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.TerminalFromJets

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance harnackTerminalJetsTopology : TopologicalSpace F.M := F.topology
local instance harnackTerminalJetsCharted : ChartedSpace H F.M := F.charted
local instance harnackTerminalJetsSmooth : IsManifold I ∞ F.M := F.smooth
local instance harnackTerminalJetsC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance harnackTerminalJetsSigmaCompact : SigmaCompactSpace F.M := F.sigmaCompact
local instance harnackTerminalJetsT2 : T2Space F.M := F.t2
local instance harnackTerminalJetsTangentT2 : T2Space (TangentBundle I F.M) := F.t2TangentBundle

variable {kappa : ℝ}

theorem terminalCurvatureNormalizedFlowSeq_curvDerivNorm_bound_on_past_slice
    (hK : KLim kappa F) (hdim : Module.finrank ℝ E = 2)
    (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)) (i : ℕ) (r : ℝ)
    (hlocal : ∀ z : F.M,
      (riemannianEDistOf (I := I) (F.S.base.metric 0) z (x i)).toReal < r →
        F.S.scalar 0 z ≤ 4 * F.S.scalar 0 (x i))
    {A : ℝ} (hA : 0 ≤ A)
    (hmargin : A + 1 / 2 < r * Real.sqrt (F.S.scalar 0 (x i)))
    {s : ℝ} (hs : s ≤ 0) (m : ℕ) (y : F.M)
    (hy : riemannianEDistOf (I := I)
      (((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.base.metric 0)
      (x i) y ≤ ENNReal.ofReal A) :
    curvDerivNorm (I := I) m
      (((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.base.metric s) y ≤
        4 * shiLocalUniformBound 2 m 4 1 := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let G := (terminalCurvatureNormalizedFlowSeq F hK x hQ).term i
  have ha : s - 1 ≤ 0 := by linarith
  have hspan : s - (s - 1) = 1 := by ring
  have houter : (1 : ℝ) / Real.sqrt 4 = 1 / 2 := by norm_num
  have hball : IsCompact {z : F.M |
      riemannianEDistOf (I := I) (G.S.base.metric (s - 1)) y z ≤
        ENNReal.ofReal ((1 : ℝ) / Real.sqrt 4)} := by
    rw [houter]
    exact terminalCurvatureNormalizedFlowSeq_closedBall_isCompact
      F hK x hQ i ha y (1 / 2)
  have hcurv : ∀ q ∈ Set.Icc (s - 1) s, ∀ z : F.M,
      riemannianEDistOf (I := I) (G.S.base.metric (s - 1)) y z ≤
        ENNReal.ofReal ((1 : ℝ) / Real.sqrt 4) →
          curvDerivNormSq (I := I) 0 (G.S.base.metric q) z ≤ (4 : ℝ) ^ 2 := by
    intro q hq z hz
    rw [houter] at hz
    have hb := terminalCurvatureNormalizedFlowSeq_buffered_rmNormSq_bound
      F hK hdim x hQ i r hlocal (a := s - 1) (s := q) ha (hq.2.trans hs)
      hA (by norm_num) hmargin y z hy hz
    change G.rmNormSq (I := I) q z ≤ 16 at hb
    change G.rmNormSq (I := I) q z ≤ (4 : ℝ) ^ 2
    have hfour : (4 : ℝ) ^ 2 = 16 := by norm_num
    rw [hfour]
    exact hb
  have hcarrier : Set.Icc (s - 1) s ⊆ ancientTimeInterval.carrier := by
    intro q hq
    exact hq.2.trans hs
  have hregular : Set.Ico (s - 1) s ⊆ ancientTimeInterval.regular := by
    intro q hq
    exact hq.2.trans_le hs
  have hcenter : riemannianEDistOf (I := I) (G.S.base.metric (s - 1)) y y ≤
      ENNReal.ofReal ((1 : ℝ) / (2 * Real.sqrt 4)) := by
    let g : SmoothRiemannianMetric I F.M := G.S.base.metric (s - 1)
    change riemannianEDistOf (I := I) g y y ≤ _
    exact (riemannianEDistOf_self (I := I) g y).le.trans bot_le
  have hb := shi_local_curvDerivNorm_terminal_of_solution_jets G.S G.isSolution
    (by omega) (a := s - 1) (b := s) (K := 4) (R := 1)
    (by linarith) (by norm_num) (by norm_num) hcarrier hregular y hball hcurv
    m s ⟨by linarith, le_rfl⟩ y hcenter
  change curvDerivNorm (I := I) m (G.S.base.metric s) y ≤
    4 * shiLocalUniformBound 2 m 4 1
  simpa only [hdim, hspan, mul_one, one_mul, Real.sqrt_one, one_pow,
    div_one, mul_comm] using hb

theorem terminalCurvatureNormalizedFlowSeq_curvDerivNorm_bound
    (hK : KLim kappa F) (hdim : Module.finrank ℝ E = 2)
    (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)) (i : ℕ) (r : ℝ)
    (hlocal : ∀ z : F.M,
      (riemannianEDistOf (I := I) (F.S.base.metric 0) z (x i)).toReal < r →
        F.S.scalar 0 z ≤ 4 * F.S.scalar 0 (x i))
    {A : ℝ} (hA : 0 ≤ A)
    (hmargin : A + 1 / 2 < r * Real.sqrt (F.S.scalar 0 (x i)))
    (m : ℕ) (y : F.M)
    (hy : riemannianEDistOf (I := I)
      (((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.base.metric 0)
      (x i) y ≤ ENNReal.ofReal A) :
    curvDerivNorm (I := I) m
      (((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.base.metric 0) y ≤
        4 * shiLocalUniformBound 2 m 4 1 :=
  terminalCurvatureNormalizedFlowSeq_curvDerivNorm_bound_on_past_slice
    F hK hdim x hQ i r hlocal hA hmargin le_rfl m y hy

theorem eventually_terminalCurvatureNormalizedFlowSeq_curvDerivNorm_bound
    (hK : KLim kappa F) (hdim : Module.finrank ℝ E = 2)
    (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)) (r : ℕ → ℝ)
    (hlocal : ∀ i : ℕ, ∀ z : F.M,
      (riemannianEDistOf (I := I) (F.S.base.metric 0) z (x i)).toReal < r i →
        F.S.scalar 0 z ≤ 4 * F.S.scalar 0 (x i))
    (hexpand : Tendsto (fun i => r i * Real.sqrt (F.S.scalar 0 (x i))) atTop atTop)
    {A : ℝ} (hA : 0 ≤ A) :
    ∀ᶠ i in atTop, ∀ s ≤ (0 : ℝ), ∀ m : ℕ, ∀ y : F.M,
      riemannianEDistOf (I := I)
        (((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.base.metric 0)
        (x i) y ≤ ENNReal.ofReal A →
      curvDerivNorm (I := I) m
        (((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.base.metric s) y ≤
          4 * shiLocalUniformBound 2 m 4 1 := by
  filter_upwards [hexpand.eventually_gt_atTop (A + 1 / 2)] with i hi
  intro s hs m y hy
  exact terminalCurvatureNormalizedFlowSeq_curvDerivNorm_bound_on_past_slice
    F hK hdim x hQ i (r i) (hlocal i) hA hi hs m y hy

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
