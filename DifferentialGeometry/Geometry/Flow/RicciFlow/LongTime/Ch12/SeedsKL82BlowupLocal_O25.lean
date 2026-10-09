import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84BlowupCore_O9
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRicciShift

/-!
# CH12-O25, G1: the blow-up core of KL82.1 with locally uniform pinching (D-R3-3 adapter)

Source: corrected w-dependent local variant of KL 82.1 / Perelman II.6.5 (Kleiner–Lott,
*Notes on Perelman's papers*, §82, and the blow-up argument of Cor. 45.1 / 45.13); this file
only provides the blow-up contradiction, not KL82.1 itself.  The reference PDFs named in
AGENTS.md are not on this machine; locators follow the CX11 report and the DELIVERIES records.

`blowup_core_local_O25` is `blowup_core_O9` with its pinching input replaced, as required by
the external review CH12-R3 (D-R3-3): the constants of KL82.1 may not depend on a pinching
function chosen after them, so instead of a global admissible `Φ` on every history we assume the
*locally uniform* pinching `sec ≥ -ε n · R n` at every traced point of the backward parabolic
blow-up regions, with `ε n → 0`.  In KL82.1, `ε n = (R n · r0 n²)⁻¹` comes from
`sec ≥ -r0⁻²` on `B(X(v), r0)`.  In the rescaled metric the curvature operator is then
`≥ -ε n`, which is the rescaled constant pinching function `Φ ≡ 1` at scale `(ε n)⁻¹ → ∞`;
the limit is therefore `Rm ≥ 0` and the O9 argument applies verbatim.
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian (SectionalBoundedBelowAt)
open DifferentialGeometry.Geometry.Curvature.DimensionThree
  (sectionalBoundedBelowAt_iff_curvatureOperatorLowerBoundAt)
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood (ancientTimeInterval
  IsAncientKappaSolution PointedFlowScalarAtBase)
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
  (isAncientKappaSolution_flowOfMetric_of_curvatureOperator_nonnegative)
open scoped Manifold ContDiff Topology NNReal ENNReal

open private ObservedHistory.isScaledSurvivor ObservedHistory.riemannianBallOf_scaleMetric_eq
  ObservedHistory.mem_Icc_of_mem_window
  ObservedHistory.exists_isScaledSurvivor_of_isTracedRegion
  ObservedHistory.exists_curvDerivNorm_bound_of_window
  ObservedHistory.isCompact_riemannianClosedBallOf_restrictOpen
  ObservedHistory.comp_inclusion_eq_of_backward_maps
  ObservedHistory.scaleMetric_restrictOpenOfSubset
  from DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimit

namespace GC.LongTime.Ch12

universe u

private local instance : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp⟩

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle


/-- **KL82.1 blow-up core, Φ-free** (`blowup_core_O9` with locally uniform pinching). -/
theorem blowup_core_local_O25
    (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
    (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hscal : ∀ n, metricScalarAt ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n) = R n)
    {K : ℝ}
    (htraced : ∀ A T : ℝ, 0 < A → 0 < T → ∀ᶠ n in atTop,
      (H n).isTracedRegion (t n) (y n) (A / Real.sqrt (R n)) (T / R n) (K * R n))
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    (hsec : ∀ A T : ℝ, 0 < A → 0 < T → ∀ᶠ n in atTop,
      ∀ (a : Icc (0 : ℝ) (H n).horizon) (hat : a ≤ t n), (a : ℝ) = t n - T / R n →
      ∀ q ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
          (A / Real.sqrt (R n)),
      ∀ X : BackwardPointTrace (H n) ((H n).activeStage a) ((H n).activeStage (t n))
          ((H n).activeStage_mono hat) q,
      ∀ (v : Icc (0 : ℝ) (H n).horizon) (hav : a ≤ v) (hvt : v ≤ t n),
        SectionalBoundedBelowAt ((H n).stageMetric ((H n).activeStage v) v)
          (X.point ((H n).activeStage v) ((H n).activeStage_mono hav)
            ((H n).activeStage_mono hvt)) (-(ε n * R n)))
    {v : ℝ} (hv : 0 < v)
    (hvol : ∀ D : ℝ, 0 < D → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianClosedBallOf
          (scaleMetric (R n) (hR n) ((H n).stageMetric ((H n).activeStage (t n)) (t n))) (y n) D,
      ∀ s : ℝ, 0 < s → s ≤ D →
        ENNReal.ofReal (v * s ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((H n).stageAt (t n)).Carrier
            (scaleMetric (R n) (hR n) ((H n).stageMetric ((H n).activeStage (t n)) (t n)))
            (riemannianBallOf
              (scaleMetric (R n) (hR n) ((H n).stageMetric ((H n).activeStage (t n)) (t n)))
              x s)) :
    False := by
  classical
  let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
    { obj := fun n =>
        { M := ((H n).stageAt (t n)).Carrier
          basepoint := y n
          metric := scaleMetric (R n) (hR n)
            ((H n).stageMetric ((H n).activeStage (t n)) (t n)) } }
  have hθ (k : ℕ) : 0 < 2 * ((k + 2 : ℕ) : ℝ) := by positivity
  have hKev : ∀ k : ℕ, ∀ᶠ n in atTop,
      (H n).isTracedRegion (t n) (y n) (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n))
        (2 * ((k + 2 : ℕ) : ℝ) / R n) (K * R n) :=
    fun k => htraced ((k + 3 : ℕ) : ℝ) (2 * ((k + 2 : ℕ) : ℝ)) (by positivity) (hθ k)
  have hex : ∀ k n, ∃ (Wk : Opens (X.obj n).M) (g : ℝ → SmoothRiemannianMetric ThreeModel Wk),
      (H n).isTracedRegion (t n) (y n) (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n))
          (2 * ((k + 2 : ℕ) : ℝ) / R n) (K * R n) →
        ObservedHistory.isScaledSurvivor (H n) (t n) (y n) (R n) (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n))
          (2 * ((k + 2 : ℕ) : ℝ)) K (hR n) Wk g := by
    intro k n
    by_cases htr : (H n).isTracedRegion (t n) (y n) (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n))
        (2 * ((k + 2 : ℕ) : ℝ) / R n) (K * R n)
    · obtain ⟨Wk, g, hg⟩ :=
        ObservedHistory.exists_isScaledSurvivor_of_isTracedRegion (H n) (t n) (y n) (hR n) (hθ k) htr
      exact ⟨Wk, g, fun _ => hg⟩
    · exact ⟨⊤, fun _ => (X.obj n).metric.restrictOpen ⊤, fun hh => absurd hh htr⟩
  choose W h hWh using hex
  have hsurv (k : ℕ) : ∀ᶠ n in atTop,
      ObservedHistory.isScaledSurvivor (H n) (t n) (y n) (R n) (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n))
        (2 * ((k + 2 : ℕ) : ℝ)) K (hR n) (W k n) (h k n) :=
    (hKev k).mono fun n hn => hWh k n hn
  have hWset (k n : ℕ) (hn : ObservedHistory.isScaledSurvivor (H n) (t n) (y n) (R n)
      (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) (2 * ((k + 2 : ℕ) : ℝ)) K (hR n) (W k n)
      (h k n)) :
      (W k n : Set (X.obj n).M) =
        riemannianBallOf (X.obj n).metric (X.obj n).basepoint ((k + 3 : ℕ) : ℝ) := by
    rw [hn.1]
    exact (ObservedHistory.riemannianBallOf_scaleMetric_eq _ (hR n) _ _).symm
  have hcompact : ∀ r : ℝ, 0 < r → ∀ᶠ n in atTop,
      IsCompact (riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint r) :=
    fun r _ => Eventually.of_forall fun n =>
      (Geometry.Metric.isClosed_riemannianClosedBallOf (X.obj n).metric _ r).isCompact
  have hsubW (k n : ℕ) (hn : ObservedHistory.isScaledSurvivor (H n) (t n) (y n) (R n)
      (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) (2 * ((k + 2 : ℕ) : ℝ)) K (hR n) (W k n)
      (h k n)) :
      riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 2 : ℕ) : ℝ) ⊆
        W k n := by
    intro z hz
    rw [hWset k n hn]
    exact lt_of_le_of_lt hz ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
      (by push_cast; linarith))
  have hball : ∀ k : ℕ, ∀ᶠ n in atTop,
      riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) ⊆
        W k n := by
    intro k
    filter_upwards [hsurv k] with n hn
    exact (riemannianClosedBallOf_mono _ _ (by push_cast; linarith)).trans (hsubW k n hn)
  have hsol : ∀ k : ℕ, ∀ᶠ n in atTop, IsSolutionOn ({ base.metric := h k n } :
      SolutionOn (I := ThreeModel) (M := W k n)
        (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0
          (neg_nonpos.mpr (Nat.cast_nonneg _)))) := by
    intro k
    filter_upwards [hsurv k] with n hn
    exact hn.2.1 ((k + 2 : ℕ) : ℝ) (Nat.cast_nonneg _)
      (by have := (Nat.cast_nonneg (k + 2) : (0 : ℝ) ≤ _); linarith)
  have hzero : ∀ k : ℕ, ∀ᶠ n in atTop, h k n 0 = (X.obj n).metric.restrictOpen (W k n) := by
    intro k
    filter_upwards [hsurv k] with n hn
    exact hn.2.2.1
  have hjets : ∀ k m : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop,
      ∀ s ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, ∀ x : W k n,
        (x : (X.obj n).M) ∈
          riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) →
        curvDerivNorm m (h k n s) x ≤ B := by
    intro k m
    obtain ⟨B, hB0, hB⟩ := ObservedHistory.exists_curvDerivNorm_bound_of_window (hθ k) (K := K)
    refine ⟨B m, hB0 m, ?_⟩
    filter_upwards [hsurv k] with n hn s hs x hx
    let _ : SigmaCompactSpace (W k n) := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel (W k n).isOpen)
    have hcpt : IsCompact (riemannianClosedBallOf (h k n 0) x 1) := by
      rw [hn.2.2.1]
      apply ObservedHistory.isCompact_riemannianClosedBallOf_restrictOpen
      refine (riemannianClosedBallOf_subset_of_add_radius_le _ (Nat.cast_nonneg _) zero_le_one
        ?_ hx).trans (hsubW k n hn)
      push_cast
      linarith
    refine hB (h k n) (hn.2.1 _ (hθ k).le le_rfl) hn.2.2.2.1 x hcpt m s ⟨?_, hs.2⟩
    have := hs.1
    push_cast at this ⊢
    linarith
  have hcompat : ∀ k l : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-((min k l + 1 : ℕ) : ℝ)) 0,
      (h k n s).restrictOpenOfSubset (inf_le_left : W k n ⊓ W l n ≤ W k n) =
        (h l n s).restrictOpenOfSubset (inf_le_right : W k n ⊓ W l n ≤ W l n) := by
    intro k l
    filter_upwards [hsurv k, hsurv l] with n hk hl s hs
    obtain ⟨a₁, hat₁, ha₁, f₁, hf₁, hc₁, hl₁, hp₁⟩ := hk.2.2.2.2.2
    obtain ⟨a₂, hat₂, ha₂, f₂, hf₂, hc₂, hl₂, hp₂⟩ := hl.2.2.2.2.2
    have hkl := min_le_left (k : ℝ) (l : ℝ)
    have hlk := min_le_right (k : ℝ) (l : ℝ)
    have hs1 := hs.1
    push_cast at hs1
    have hsk : s ∈ Icc (-(2 * ((k + 2 : ℕ) : ℝ))) 0 := ⟨by push_cast; linarith, hs.2⟩
    have hsl : s ∈ Icc (-(2 * ((l + 2 : ℕ) : ℝ))) 0 := ⟨by push_cast; linarith, hs.2⟩
    have hv₁ := ObservedHistory.mem_Icc_of_mem_window (hR n) ha₁ hsk
    have hv₂ := ObservedHistory.mem_Icc_of_mem_window (hR n) ha₂ hsl
    let w : Icc (0 : ℝ) (H n).horizon :=
      ⟨(t n : ℝ) + s / R n, a₁.2.1.trans hv₁.1, hv₁.2.trans (t n).2.2⟩
    have hja₁ : (H n).activeStage a₁ ≤ (H n).activeStage w :=
      (H n).activeStage_mono (show a₁ ≤ w from hv₁.1)
    have hja₂ : (H n).activeStage a₂ ≤ (H n).activeStage w :=
      (H n).activeStage_mono (show a₂ ≤ w from hv₂.1)
    have hjt : (H n).activeStage w ≤ (H n).activeStage (t n) :=
      (H n).activeStage_mono (show w ≤ t n from hv₁.2)
    have hdom := (H n).activeStage_mem w
    rw [hp₁ s hsk ⟨_, hja₁, hjt⟩ hdom, hp₂ s hsl ⟨_, hja₂, hjt⟩ hdom,
      ObservedHistory.scaleMetric_restrictOpenOfSubset,
      ObservedHistory.scaleMetric_restrictOpenOfSubset]
    congr 1
    exact localPullMetric_restrictOpenOfSubset_eq_of_comp_eq _ _ _ _ _ _ _
      (ObservedHistory.comp_inclusion_eq_of_backward_maps (H n) hat₁ hat₂ f₁ hc₁ hl₁ f₂ hc₂
        hl₂ _ hja₁ hja₂ hjt)
  -- the time-zero local noncollapsing input of the limit theorem, from the volume test
  have hvolX : ∀ r R' : ℝ, 0 < r → r < R' → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ' : ℝ, 0 < a ∧ 0 < κ' ∧ r + a ≤ R' ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ x ∈ riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint r,
        ENNReal.ofReal (κ' * a ^ Module.finrank ℝ ThreeSpace) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel (X.obj n).M (X.obj n).metric
            (riemannianBallOf (X.obj n).metric x a) := by
    intro r R' hr hrR' C hC
    set a := min (min (R' - r) 1) (1 / (C + 1)) with ha
    have ha0 : 0 < a := lt_min (lt_min (by linarith) one_pos) (by positivity)
    have ha1 : a ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
    have har : a ≤ R' - r := (min_le_left _ _).trans (min_le_left _ _)
    have haC : a * (C + 1) ≤ 1 := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    have hac : a * C ≤ 1 := by nlinarith
    have hac0 : 0 ≤ a * C := by positivity
    have h1 : (a * C) ^ 2 ≤ 1 := by nlinarith
    have h2 : a ^ 2 ≤ 1 := by nlinarith
    refine ⟨a, v, ha0, hv, by linarith, ?_, ?_⟩
    · calc a ^ 4 * C ^ 2 = a ^ 2 * (a * C) ^ 2 := by ring
        _ ≤ 1 * 1 := mul_le_mul h2 h1 (sq_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    · have hD : 0 < r + 1 := by linarith
      filter_upwards [hvol (r + 1) hD] with n hn x hx
      have hx' := riemannianClosedBallOf_mono _ _ (show r ≤ r + 1 by linarith) hx
      have := hn x hx' a ha0 (by linarith)
      simpa [ThreeSpace] using this
  obtain ⟨f, hf, P, F, ⟨C0, hC0⟩, hPc, hconn, -, V, N, hV, hVF, φ, hφ, hφF, G, hG0, hG, ψ, hψ,
      hconv⟩ :=
    exists_ancient_pointed_flow_limit_of_local_solutions X hcompact hvolX W h hball hsol hzero
      hjets hcompat
  -- curvature operator `≥ 0` and completeness of the limit (Hamilton–Ivey pinching, `R n → ∞`)
  have hPhi1 : Perelman.AdmissiblePinchingFunction (fun _ : ℝ => (1 : ℝ)) :=
    Perelman.admissiblePinchingFunction_const one_pos
  have hQ' : Tendsto (fun n => (ε n)⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨hεlim, Eventually.of_forall hε⟩)
  have hpinchW : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ q ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
      ∀ x : W k n, curvatureOperatorLowerBoundAt (h k n q) x
        (metricAlgebraicCurvatureTensorAt (h k n q) x)
        (Perelman.rescalePinchingFunction (ε n)⁻¹ (fun _ : ℝ => (1 : ℝ))
          (metricScalarAt (h k n q) x)) := by
    intro k
    filter_upwards [hsurv k, hsec ((k + 3 : ℕ) : ℝ) (2 * ((k + 2 : ℕ) : ℝ)) (by positivity)
      (hθ k)] with n hn hsn q hq x
    obtain ⟨a, hat, ha, fs, hfs, hcr, htop, hp⟩ := hn.2.2.2.2.2
    have hxball : (x : ((H n).stageAt (t n)).Carrier) ∈ riemannianBallOf
        ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
        (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) := by
      have hx : (x : ((H n).stageAt (t n)).Carrier) ∈ (W k n : Set (X.obj n).M) := x.2
      rw [hn.1] at hx
      exact hx
    let Xtr : BackwardPointTrace (H n) ((H n).activeStage a) ((H n).activeStage (t n))
        ((H n).activeStage_mono hat) x.val :=
      { point := fun j h1 h2 => fs ⟨j, h1, h2⟩ x
        endpoint_eq := htop x
        crossing := fun i hf hl => hcr i hf hl x }
    have hqθ : q ∈ Icc (-(2 * ((k + 2 : ℕ) : ℝ))) 0 :=
      ⟨by have := hq.1; push_cast at this ⊢; linarith, hq.2⟩
    have hv := ObservedHistory.mem_Icc_of_mem_window (hR n) ha hqθ
    let w : Icc (0 : ℝ) (H n).horizon :=
      ⟨(t n : ℝ) + q / R n, a.2.1.trans hv.1, hv.2.trans (t n).2.2⟩
    let j : (H n).StageInterval ((H n).activeStage a) ((H n).activeStage (t n)) :=
      ⟨(H n).activeStage w, (H n).activeStage_mono (show a ≤ w from hv.1),
        (H n).activeStage_mono (show w ≤ t n from hv.2)⟩
    have hq' := hp q hqθ j ((H n).activeStage_mem w)
    have hs := hsn a hat ha x.val hxball Xtr w hv.1 hv.2
    have hop := (sectionalBoundedBelowAt_iff_curvatureOperatorLowerBoundAt
      finrank_euclideanSpace_fin).mp hs
    have hpull := (curvatureOperatorLowerBoundAt_localPullMetric_iff _ (fs j) (hfs j) x _).mpr hop
    rw [hq', curvatureOperatorLowerBoundAt_scaleMetric_iff]
    convert hpull using 1
    simp only [Perelman.rescalePinchingFunction, inv_inv, mul_one]
    ring
  obtain ⟨hcone, hcomplete⟩ := ancient_pointed_flow_limit_curvatureOperator_nonnegative_and_complete
    hf hPc hconn hV hG0 hG hψ hconv hQ' hPhi1 hpinchW
  -- scalar curvature `1` at the base point
  have hbaseP : metricScalarAt P.metric P.basepoint = 1 := by
    refine metricScalarAt_basepoint_eq_of_local_flow_limit hf F hV hφF hG0 hψ hconv ?_ ?_
    · intro k
      filter_upwards [hsurv k] with n hn z
      rw [hn.2.2.1, metricScalarAt_restrictOpen]
    · intro n
      change metricScalarAt (scaleMetric (R n) (hR n)
        ((H n).stageMetric ((H n).activeStage (t n)) (t n))) (y n) = 1
      rw [Geometry.Curvature.metricScalarAt_scaleMetric, hscal n, inv_mul_cancel₀ (hR n).ne']
  -- uniformly bounded curvature of the limit
  set Bs : ℝ := (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * |K| with hBs
  have hscalW : ∀ k, ∀ᶠ n in atTop, ∀ s ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, ∀ z : W k n,
      metricScalarAt (h k n s) z ≤ Bs := by
    intro k
    filter_upwards [hsurv k] with n hn s hs z
    have hs' : s ∈ Icc (-(2 * ((k + 2 : ℕ) : ℝ))) 0 :=
      ⟨by have := hs.1; push_cast at this ⊢; linarith, hs.2⟩
    have hc := hn.2.2.2.1 s hs' z
    have hsq : Real.sqrt (Tensor0SBundle.normSq0S (h k n s) z 4 (metricRm04At (h k n s) z)) ≤
        |K| := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hc
    exact (le_abs_self _).trans ((scalar_abs_le_rm (h k n s) z).trans
      (mul_le_mul_of_nonneg_left hsq (by positivity)))
  have hbound := metricScalarAt_le_of_local_flow_limit_O9 hf hV hψ hconv hscalW hconn
  -- time-zero volume growth of the limit, from the volume test
  have hsource : ∀ s : ℝ, 0 < s → ∀ᶠ k : ℕ in atTop,
      ENNReal.ofReal v * ENNReal.ofReal (s ^ Module.finrank ℝ ThreeSpace) ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel (X.obj (f k)).M
          (X.obj (f k)).metric
          (riemannianBallOf (X.obj (f k)).metric (X.obj (f k)).basepoint s) := by
    intro s hs
    filter_upwards [hf.tendsto_atTop.eventually (hvol s hs)] with k hk
    have hbase : (X.obj (f k)).basepoint ∈
        riemannianClosedBallOf (X.obj (f k)).metric (X.obj (f k)).basepoint s := by
      rw [riemannianClosedBallOf, mem_ofPred_eq, riemannianEDistOf_self]
      exact bot_le
    have := hk _ hbase s hs le_rfl
    rw [← ENNReal.ofReal_mul hv.le]
    simpa [ThreeSpace] using this
  have hlimvol := pointed_ball_volume_lower_of_eventually C0 hC0 hPc (ENNReal.ofReal v) hsource
  have hv0 : ENNReal.ofReal v ≠ 0 := (ENNReal.ofReal_pos.mpr hv).ne'
  have hG0vol : ∀ r : ℝ, 0 < r →
      ENNReal.ofReal v * ENNReal.ofReal (r ^ Module.finrank ℝ ThreeSpace) ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel P.M (G 0)
          (riemannianBallOf (G 0) P.basepoint r) := by
    rw [hG0]
    exact hlimvol
  have hBs0 : 0 ≤ Bs := by positivity
  have hall := ballVolume_lower_all_times_of_ancient_O9 (by simp [ThreeSpace]) G hG hcomplete
    hcone hBs0 hbound P.basepoint (ENNReal.ofReal v) hG0vol
  -- the limit is an ancient κ-solution
  have hkappa : ∀ ρ : ℝ, 0 < ρ → Perelman.ParabolicallyKappaNoncollapsedBelowScale
      ({ base.metric := G } : SolutionOn (I := ThreeModel) (M := P.M) ancientTimeInterval)
        v ρ := by
    intro ρ hρ
    refine ⟨hρ, fun time B _ _ => ⟨hv, ?_⟩⟩
    have h := hall (time : ℝ) time.2 B.center B.radius B.radius_pos
    have hpow : ENNReal.ofReal (B.radius ^ Module.finrank ℝ ThreeSpace) =
        ENNReal.ofReal B.radius ^ Module.finrank ℝ ThreeSpace :=
      ENNReal.ofReal_pow B.radius_pos.le _
    rw [hpow] at h
    exact h
  obtain ⟨hanc, -⟩ := isAncientKappaSolution_flowOfMetric_of_curvatureOperator_nonnegative
    P hG hG0 hconn hcomplete hcone hbound hv hkappa hbaseP
  -- noncompactness and positive asymptotic volume ratio
  have hnoncompact : NoncompactSpace P.M :=
    noncompact_of_positive_ball_volume_lower P.metric P.basepoint (ENNReal.ofReal v) hv0
      hlimvol
  have havr := asymptoticVolumeRatio_lower_of_ball_volume_lower P.metric P.basepoint
    (ENNReal.ofReal v) hlimvol
  have hzero := ancientKappaThree_avr_eq_zero
    (flowOfMetric ancientTimeInterval P G hG) hanc (by simp [ThreeSpace]) hnoncompact 0
    (by simp) P.basepoint
  change asymptoticVolumeRatio (G 0) P.basepoint = 0 at hzero
  rw [hG0] at hzero
  rw [hzero] at havr
  have hpos : 0 < ENNReal.ofReal v / euclideanUnitBallVolume (Module.finrank ℝ ThreeSpace) :=
    ENNReal.div_pos hv0 (euclideanUnitBallVolume_ne_top _)
  exact (not_le.mpr hpos) havr

end GC.LongTime.Ch12
