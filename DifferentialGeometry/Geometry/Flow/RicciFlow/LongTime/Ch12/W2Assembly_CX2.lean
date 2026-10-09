import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SliceG3b_CX2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedPath_CX2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroGlueVolumeTest

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.VolumeComparison DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
  (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)

/- The frozen O4 G2 consumer statement, expanded inline below: its final
clause is an actual backward trace with the specified earlier centre. -/
variable (hG2 : ∀ w : ℝ, 0 < w → ∃ a c c₁ Λ₀ b₀ T₀ : ℝ,
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

include hdec hG2

/-- Exact hW2, using the frozen backward-seed supplier and the proved G3a/G3b.
No traced-region or surgery-avoidance hypothesis remains. -/
theorem W2_of_G2_CX2 :
    ∀ w : ℝ, 0 < w → ∃ T Λ b τ C : ℝ, 0 < T ∧ 1 ≤ Λ ∧ 0 < b ∧ 0 < τ ∧ 0 < C ∧
      τ * b ^ 2 < 1 / 2 ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (p : (s.history.stageAt (sliceTop_S8 s)).Carrier) (r : ℝ), 0 < r →
        r ≤ b * Real.sqrt s.time →
        (∀ q ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) p r,
          SectionalBoundedBelowAt (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time)
            q (-(r ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume
          (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) p r →
        (∀ n (i : Fin (F.tower.history n).eventCount),
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time →
          ∀ h, Λ * (Hp.records n i).nominalRadius h ≤ r) →
        s.history.isTracedRegion (sliceTop_S8 s) p (2 * r) (τ * r ^ 2) (C / r ^ 2) := by
  intro w hw
  obtain ⟨a, c, c₁, Λ₀, b₀, Tseed, ha, hac, hc₁, _, hb₀, hTseed, hseed⟩ := hG2 w hw
  have hc : 0 < c := (by positivity : 0 ≤ 2 * a ^ 2).trans_lt hac
  obtain ⟨Tcurv, ρ, K, hTcurv, hρ, hK, henlarge⟩ := enlarged_rm_bound_along_seed_trace_CX2 Hp ha hc₁
  obtain ⟨b, τ, hb, hτ, hbb₀, hbρ, hτc, hwindow, hexp⟩ := exists_window_constants_CX2 hc hb₀ hρ hK
  obtain ⟨Λ, hΛ, hΛ₀, hKΛ⟩ := exists_cutoff_multiplier_CX2 (9 * K) Λ₀
  obtain ⟨Tδ, _, hδ⟩ := eventually_recent_cutoff_accuracy_CX2 Hp hdec
  let T := max Tseed (max (2 * Tcurv) Tδ)
  have hT : 0 < T := hTseed.trans_le (le_max_left _ _)
  refine ⟨T, Λ, b, τ, K, hT, hΛ, hb, hτ, hK, hwindow, ?_⟩
  intro s hs p r hr hrb hsec hvol hrec
  have hsSeed : Tseed ≤ s.time := (le_max_left Tseed _).trans hs
  have hsCurv : 2 * Tcurv ≤ s.time := (le_max_left (2 * Tcurv) Tδ).trans ((le_max_right Tseed _).trans hs)
  have hsδ : Tδ ≤ s.time := (le_max_right (2 * Tcurv) Tδ).trans ((le_max_right Tseed _).trans hs)
  have hrb₀ : r ≤ b₀ * Real.sqrt s.time := hrb.trans
    (mul_le_mul_of_nonneg_right hbb₀ (Real.sqrt_nonneg _))
  obtain ⟨y, hy, hseedTime⟩ := hseed s hsSeed p r hr hrb₀ hsec hvol
    (recent_nominal_mono_CX2 Hp hΛ₀ hrec)
  have hlowLe : s.time - τ * r ^ 2 ≤ s.time := sub_le_self _ (by positivity)
  have hlow := window_time_and_radius_CX2 hb hτ hbρ hwindow s.positive hr hrb ⟨le_rfl, hlowLe⟩
  let l : Icc (0 : ℝ) s.history.horizon := ⟨s.time - τ * r ^ 2, hlow.2.1.le, hlowLe⟩
  have hlt : l ≤ sliceTop_S8 s := hlowLe
  have hsize : ∀ v : Icc (0 : ℝ) s.history.horizon, l ≤ v → Tcurv ≤ v.val ∧ r ≤ ρ * Real.sqrt v := by
    intro v hlv
    have hv := window_time_and_radius_CX2 hb hτ hbρ hwindow s.positive hr hrb
      (show v.val ∈ Icc (s.time - τ * r ^ 2) s.time from ⟨hlv, v.property.2⟩)
    exact ⟨by linarith [hv.1], hv.2.2⟩
  obtain ⟨Y, hY⟩ := henlarge s l hlt y r hr hsize (by
    intro v hlv
    have hv : s.time - c * r ^ 2 ≤ v.val := by
      have hm := mul_le_mul_of_nonneg_right hτc (sq_nonneg r)
      have hl : s.time - τ * r ^ 2 ≤ v.val := hlv
      linarith
    obtain ⟨yv, _, hseedv, hvolv, A, hA⟩ := hseedTime v hv
    exact ⟨yv, hseedv, hvolv, A, hA⟩)
  exact slice_seed_tracedRegion_CX2 Hp s hτ hr hK hΛ hKΛ hexp (a := l) rfl hlt hlow.1.le
    hy Y (fun v hlv _ => hY v hlv) (hδ s.time hsδ) hrec

/-- G1 in the exact O4/O6 shape. Once its frozen G2 consumer is supplied,
G1 is an upstream input rather than an additional analytic gap in G3b. -/
theorem W2_of_G1_G2_CX2
    (_hG1 : ∀ w : ℝ, 0 < w → ∀ ε : ℝ, 0 < ε → ∃ θ : ℝ, 0 < θ ∧
      ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace ThreeSpace X]
        [IsManifold ThreeModel ∞ X] [T2Space X] [CompactSpace X]
        (gX : SmoothRiemannianMetric ThreeModel X) (p : X) (r : ℝ), 0 < r →
        (∀ q ∈ riemannianBallOf gX p r, SectionalBoundedBelowAt gX q (-(r ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume gX p r →
        ∃ y : X, riemannianBallOf gX y (θ * r) ⊆ riemannianBallOf gX p r ∧
          ∀ z ∈ riemannianBallOf gX y (θ * r), ∀ b : ℝ, 0 < b → b ≤ θ * r →
            ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * b ^ 3) ≤ ballVolume gX z b) :
    ∀ w : ℝ, 0 < w → ∃ T Λ b τ C : ℝ, 0 < T ∧ 1 ≤ Λ ∧ 0 < b ∧ 0 < τ ∧ 0 < C ∧
      τ * b ^ 2 < 1 / 2 ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (p : (s.history.stageAt (sliceTop_S8 s)).Carrier) (r : ℝ), 0 < r →
        r ≤ b * Real.sqrt s.time →
        (∀ q ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) p r,
          SectionalBoundedBelowAt (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time)
            q (-(r ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume
          (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) p r →
        (∀ n (i : Fin (F.tower.history n).eventCount),
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time →
          ∀ h, Λ * (Hp.records n i).nominalRadius h ≤ r) →
        s.history.isTracedRegion (sliceTop_S8 s) p (2 * r) (τ * r ^ 2) (C / r ^ 2) :=
  W2_of_G2_CX2 Hp hdec hG2

/-- Direct application to the existing W2-to-whole-ball consumer. -/
theorem macroWholeBall_of_G2_CX2 : MacroWholeBall_O2 Hp :=
  macroWholeBall_O2_of_W2_S8 Hp (W2_of_G2_CX2 Hp hdec hG2)

/-- The requested G1/G2 interface feeds the unchanged whole-ball consumer. -/
theorem macroWholeBall_of_G1_G2_CX2
    (hG1 : ∀ w : ℝ, 0 < w → ∀ ε : ℝ, 0 < ε → ∃ θ : ℝ, 0 < θ ∧
      ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace ThreeSpace X]
        [IsManifold ThreeModel ∞ X] [T2Space X] [CompactSpace X]
        (gX : SmoothRiemannianMetric ThreeModel X) (p : X) (r : ℝ), 0 < r →
        (∀ q ∈ riemannianBallOf gX p r, SectionalBoundedBelowAt gX q (-(r ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume gX p r →
        ∃ y : X, riemannianBallOf gX y (θ * r) ⊆ riemannianBallOf gX p r ∧
          ∀ z ∈ riemannianBallOf gX y (θ * r), ∀ b : ℝ, 0 < b → b ≤ θ * r →
            ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * b ^ 3) ≤ ballVolume gX z b) :
    MacroWholeBall_O2 Hp :=
  macroWholeBall_O2_of_W2_S8 Hp (W2_of_G1_G2_CX2 Hp hdec hG2 hG1)

end GC.LongTime.Ch12
