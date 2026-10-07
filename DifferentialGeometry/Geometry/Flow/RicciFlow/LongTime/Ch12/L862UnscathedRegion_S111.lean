import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82DistBoot_S68
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82ClaimWindow_O30
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82ClaimTerminal_O36

/-!
# CH12-S111 G1: from an unscathed parent ball and the KL84.1(c) bound to a traced region

`traced_region_S111` is the region bookkeeping of the assembly `step866_of_unscathed_S111`
(`[FROZEN] CH12-S111`): on a general observed history `H`, a backward trace `X` of `x0` from `a`
to `top` such that (i) every point of `B_v(X(v), r0)` traces back to `a` (with some finite bound)
and (ii) `|Rm| ≤ B/r0²` on `B_v(X(v), 20 r0)` for `v` in the window `[top − c r0², top]`, yields
`isTracedRegion w (X(w)) κr δ Kb` for every `w` with `w − δ` in the window.  The traces of the
points of `B_w(X(w), κr)` are the restrictions of those of (i); their positions are kept inside
`B_v(X(v), r0)` by the distance bootstrap `dist_trace_boot_S68` (the Ricci bound it needs is the
Riemann bound (ii) via `ricci_le_of_rm_S111`), and the event clause of `isRmBoundedBy` follows
from the stage clause (`isRmBoundedBy_of_stage_O36`).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.VolumeComparison DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- Dimension three: `|Rm| ≤ K` bounds the Ricci form by `3K` (copy of the private
`abs_ricciTensor_le_of_rmNormSq_le` of `WindowedScalarComparison`). -/
theorem ricci_le_of_rm_S111 {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric ThreeModel M) (z : M) {K : ℝ} (hK : 0 ≤ K)
    (hrm : normSq0S g z 4 (metricRm04At g z) ≤ K ^ 2) (w : TangentSpace ThreeModel z) :
    ricciTensor g z w w ≤ 3 * K * g.inner z w w := by
  have hKr (a b c : TangentSpace ThreeModel z) :
      Real.sqrt (g.inner z (riemannOp (cov := LeviCivita g) z a b c)
        (riemannOp (cov := LeviCivita g) z a b c)) ≤
        K * Real.sqrt (g.inner z a a) * Real.sqrt (g.inner z b b) * Real.sqrt (g.inner z c c) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ K ^ 2 * g.inner z a a * g.inner z b b * g.inner z c c :=
        riemannOp_normSq_le_of_rmNormSq_le g z hrm a b c
      _ = _ := by
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (metric_inner_self_nonneg g z a),
          Real.sq_sqrt (metric_inner_self_nonneg g z b),
          Real.sq_sqrt (metric_inner_self_nonneg g z c)]
  have hh := abs_ricciTensor_le_of_riemannOp_le g hKr w w
  simp only [show Module.finrank ℝ ThreeSpace = 3 from by simp [ThreeSpace], Nat.cast_ofNat]
    at hh
  calc ricciTensor g z w w ≤ |ricciTensor g z w w| := le_abs_self _
    _ ≤ 3 * K * Real.sqrt (g.inner z w w) * Real.sqrt (g.inner z w w) := hh
    _ = 3 * K * g.inner z w w := by
      rw [mul_assoc, Real.mul_self_sqrt (metric_inner_self_nonneg g z w)]

/-- The numerical margins of the distance bootstrap: with `C = (3B + 48) δ / r0²` and
`δ ≤ r0² / (64 (B + 16))`, both `16 √(C/3) √δ` and `√(3δ/C)` are at most `r0 / 4`. -/
theorem margins_S111 {r0 B δ C : ℝ} (hr0 : 0 < r0) (hB : 0 < B) (hδ : 0 < δ)
    (hδs : δ ≤ r0 ^ 2 / (64 * (B + 16))) (hC : C = (3 * B + 48) * δ / r0 ^ 2) :
    16 * Real.sqrt (C / 3) * Real.sqrt δ ≤ r0 / 4 ∧ Real.sqrt (3 * δ / C) ≤ r0 / 4 := by
  have hBp : 0 < B + 16 := by linarith
  have h64 : 64 * (B + 16) * δ ≤ r0 ^ 2 := by
    rw [le_div_iff₀ (by positivity)] at hδs
    linarith
  constructor
  · rw [mul_assoc, ← Real.sqrt_mul (by rw [hC]; positivity)]
    have hq : Real.sqrt (C / 3 * δ) ≤ r0 / 64 := by
      rw [Real.sqrt_le_left (by positivity)]
      have e : C / 3 * δ = (B + 16) * δ ^ 2 / r0 ^ 2 := by rw [hC]; field_simp; ring
      rw [e, div_le_iff₀ (by positivity)]
      have h1 : (64 * (B + 16) * δ) ^ 2 ≤ (r0 ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) h64 2
      have h2 : (B + 16) * δ ^ 2 ≤ (B + 16) ^ 2 * δ ^ 2 :=
        mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg δ)
      have e2 : (r0 / 64) ^ 2 * r0 ^ 2 = (r0 ^ 2) ^ 2 / 4096 := by ring
      have e3 : (64 * (B + 16) * δ) ^ 2 = 4096 * ((B + 16) ^ 2 * δ ^ 2) := by ring
      rw [e2]
      linarith
    linarith
  · rw [Real.sqrt_le_left (by positivity)]
    have e : 3 * δ / C = r0 ^ 2 / (B + 16) := by rw [hC]; field_simp; ring
    rw [e, div_le_iff₀ hBp]
    nlinarith [mul_nonneg (sq_nonneg r0) hB.le]

/-- **Region bookkeeping** (see the module doc).  `hSF`: every point of `B_v(X(v), r0)` traces back
to `a`; `hrm`: `|Rm| ≤ B/r0²` on `B_v(X(v), 20 r0)` for `v ≥ top − c r0²` (the output of
`enlarged_rm_kl82_O42` at `A = 1`); `δ` is the depth, `κr` the radius, `Kb ≥ B/r0²`. -/
theorem traced_region_S111 (H : ObservedHistory.{u}) {a top : Icc (0 : ℝ) H.horizon}
    (hat : a ≤ top) {x0 : (H.stageAt top).Carrier}
    (X : BackwardPointTrace H (H.activeStage a) (H.activeStage top) (H.activeStage_mono hat) x0)
    {r0 B K' c δ κr Kb : ℝ} (hr0 : 0 < r0) (hB : 0 < B) (hδ : 0 < δ) (hκr : 0 < κr)
    (hκr4 : κr ≤ r0 / 4) (hδs : δ ≤ r0 ^ 2 / (64 * (B + 16))) (hKb : B / r0 ^ 2 ≤ Kb)
    (hac : (a : ℝ) ≤ (top : ℝ) - c * r0 ^ 2)
    (hSF : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) r0,
        ∃ A' : BackwardPointTrace H (H.activeStage a) (H.activeStage v)
            (H.activeStage_mono hav) q, A'.isRmBoundedBy (hat := hav) K')
    (hrm : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
      (top : ℝ) - c * r0 ^ 2 ≤ v →
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (20 * (1 * r0)),
        Real.sqrt (normSq0S (H.stageMetric (H.activeStage v) v) q 4
          (metricRm04At (H.stageMetric (H.activeStage v) v) q)) ≤ B / r0 ^ 2)
    (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ top)
    (hw : (top : ℝ) - c * r0 ^ 2 + δ ≤ w) :
    H.isTracedRegion w
      (X.point (H.activeStage w) (H.activeStage_mono haw) (H.activeStage_mono hwt)) κr δ Kb := by
  have hwa_ge : (a : ℝ) ≤ (w : ℝ) - δ := by linarith
  let a'' : Icc (0 : ℝ) H.horizon :=
    ⟨(w : ℝ) - δ, a.2.1.trans hwa_ge, (sub_le_self _ hδ.le).trans w.2.2⟩
  have haa : a ≤ a'' := hwa_ge
  have haw'' : a'' ≤ w := show (w : ℝ) - δ ≤ w from sub_le_self _ hδ.le
  have hwa : (w : ℝ) - (a'' : ℝ) = δ := by
    change (w : ℝ) - ((w : ℝ) - δ) = δ
    ring
  refine ⟨hκr, hδ, a'', haw'', rfl, fun q hq => ?_⟩
  -- constants
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = (3 * B + 48) * δ / r0 ^ 2 := ⟨_, rfl⟩
  have hC : 0 < C := by rw [hCdef]; positivity
  obtain ⟨hE, hM⟩ := margins_S111 hr0 hB hδ hδs hCdef
  have hqr0 : q ∈ riemannianBallOf (H.stageMetric (H.activeStage w) w)
      (X.point (H.activeStage w) (H.activeStage_mono haw) (H.activeStage_mono hwt)) r0 :=
    lt_of_lt_of_le hq (ENNReal.ofReal_le_ofReal (by linarith))
  have hd : (riemannianEDistOf (H.stageMetric (H.activeStage w) w)
      (X.point (H.activeStage w) (H.activeStage_mono haw) (H.activeStage_mono hwt)) q).toReal <
      κr := ENNReal.toReal_lt_of_lt_ofReal hq
  have hd0 := ENNReal.toReal_nonneg (a := riemannianEDistOf (H.stageMetric (H.activeStage w) w)
      (X.point (H.activeStage w) (H.activeStage_mono haw) (H.activeStage_mono hwt)) q)
  obtain ⟨A', -⟩ := hSF w haw hwt q hqr0
  let Xw := (X.restrictLast (H.activeStage_mono haw) (H.activeStage_mono hwt)).restrictFirst
    (H.activeStage_mono haa) (H.activeStage_mono haw'')
  let A'' := traceRestrict_O30 A' (H.activeStage_mono haa) (H.activeStage_mono haw'')
  have hSFb : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a'' ≤ v) (hvw : v ≤ w),
      ∀ z ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (Xw.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvw)) r0,
        Nonempty (BackwardPointTrace H (H.activeStage a'') (H.activeStage v)
          (H.activeStage_mono hav) z) := by
    intro v hav hvw z hz
    obtain ⟨A₁, -⟩ := hSF v (haa.trans hav) (hvw.trans hwt) z hz
    exact ⟨traceRestrict_O30 A₁ (H.activeStage_mono haa) (H.activeStage_mono hav)⟩
  have hRic : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a'' ≤ v) (hvw : v ≤ w), (a'' : ℝ) < v →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
          (Xw.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvw)) z <
          ENNReal.ofReal r0 →
      ∀ w' : TangentSpace ThreeModel z,
        ricciTensor (H.stageMetric (H.activeStage v) v) z w' w' ≤
          C / ((v : ℝ) - a'') * (H.stageMetric (H.activeStage v) v).inner z w' w' := by
    intro v hav hvw hva z hz w'
    have hv_ge : (top : ℝ) - c * r0 ^ 2 ≤ v := by
      have : (a'' : ℝ) ≤ v := hav
      have h2 : (a'' : ℝ) = (w : ℝ) - δ := rfl
      linarith
    have hz20 : z ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
        (X.point (H.activeStage v) (H.activeStage_mono (haa.trans hav))
          (H.activeStage_mono (hvw.trans hwt))) (20 * (1 * r0)) :=
      lt_of_lt_of_le hz (ENNReal.ofReal_le_ofReal (by linarith))
    have hb := hrm v (haa.trans hav) (hvw.trans hwt) hv_ge z hz20
    obtain ⟨hB0, hB2⟩ := Real.sqrt_le_iff.mp hb
    have hR := ricci_le_of_rm_S111 (H.stageMetric (H.activeStage v) v) z hB0 hB2 w'
    have hg := metric_inner_self_nonneg (H.stageMetric (H.activeStage v) v) z w'
    have hsub : 0 < (v : ℝ) - a'' := by linarith
    have hvw' : (v : ℝ) ≤ w := hvw
    have hle : (v : ℝ) - a'' ≤ δ := by linarith
    have hcoef : 3 * (B / r0 ^ 2) ≤ C / ((v : ℝ) - a'') := by
      rw [le_div_iff₀ hsub]
      have e : C = 3 * (B / r0 ^ 2) * δ + 48 * δ / r0 ^ 2 := by rw [hCdef]; ring
      have h1 : 3 * (B / r0 ^ 2) * ((v : ℝ) - a'') ≤ 3 * (B / r0 ^ 2) * δ :=
        mul_le_mul_of_nonneg_left hle (by positivity)
      have h2 : 0 ≤ 48 * δ / r0 ^ 2 := by positivity
      linarith
    exact hR.trans (mul_le_mul_of_nonneg_right hcoef hg)
  have hroom : (riemannianEDistOf (H.stageMetric (H.activeStage w) w)
      (X.point (H.activeStage w) (H.activeStage_mono haw) (H.activeStage_mono hwt)) q).toReal +
      16 * Real.sqrt (C / 3) * Real.sqrt ((w : ℝ) - a'') < r0 / 2 := by
    rw [hwa]; linarith
  have hR0 : (riemannianEDistOf (H.stageMetric (H.activeStage w) w)
      (X.point (H.activeStage w) (H.activeStage_mono haw) (H.activeStage_mono hwt)) q).toReal +
      16 * Real.sqrt (C / 3) * Real.sqrt ((w : ℝ) - a'') +
        Real.sqrt (3 * ((w : ℝ) - a'') / C) < r0 := by
    rw [hwa]; linarith
  have hboot := dist_trace_boot_S68 H haw'' Xw A'' hC hr0 hqr0 hroom hR0 hSFb hRic
  refine ⟨A'', isRmBoundedBy_of_stage_O36 H A'' ?_⟩
  intro v hav hvw
  have hv_ge : (top : ℝ) - c * r0 ^ 2 ≤ v := by
    have : (a'' : ℝ) ≤ v := hav
    have h2 : (a'' : ℝ) = (w : ℝ) - δ := rfl
    linarith
  have hdist := hboot v hav hvw
  have hs0 := Real.sqrt_nonneg ((v : ℝ) - a'')
  have hsC : 0 ≤ 16 * Real.sqrt (C / 3) := by positivity
  have hmem : A''.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvw) ∈
      riemannianBallOf (H.stageMetric (H.activeStage v) v)
        (X.point (H.activeStage v) (H.activeStage_mono (haa.trans hav))
          (H.activeStage_mono (hvw.trans hwt))) (20 * (1 * r0)) := by
    have h1 : (riemannianEDistOf (H.stageMetric (H.activeStage w) w)
        (X.point (H.activeStage w) (H.activeStage_mono haw) (H.activeStage_mono hwt)) q).toReal +
        16 * Real.sqrt (C / 3) * (Real.sqrt ((w : ℝ) - a'') - Real.sqrt ((v : ℝ) - a'')) < 20 * (1 * r0) := by
      rw [hwa] at hroom ⊢
      nlinarith [mul_nonneg hsC hs0]
    exact lt_of_le_of_lt hdist ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr h1)
  have hb := hrm v (haa.trans hav) (hvw.trans hwt) hv_ge _ hmem
  exact (Real.sqrt_le_iff.mp (hb.trans hKb)).2

/-- Arithmetic of the KL window `[u − c (σ r)², u]`: for `r ≤ b √u`, `b ≤ min (1/2) (ρ/2)`,
`c ≤ τ₀ ≤ 1`, `2 T₁ ≤ T ≤ u`, every `v` in the window has `T₁ ≤ v` and `σ r ≤ ρ √v`. -/
theorem window_S111 {u v c τ₀ σ r b ρ T T₁ : ℝ} (hu0 : 0 ≤ u) (hr : 0 < r) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hcτ : c ≤ τ₀) (hτ₀1 : τ₀ ≤ 1) (hb : 0 < b) (hbb : b ≤ 1 / 2)
    (hbc : b ≤ ρ / 2) (hρ : 0 < ρ) (hrb : r ≤ b * Real.sqrt u) (hT₁ : 0 < T₁)
    (hT : 2 * T₁ ≤ T) (hTu : T ≤ u) (hv0 : 0 ≤ v) (hv : u - c * (σ * r) ^ 2 ≤ v) :
    T₁ ≤ v ∧ σ * r ≤ ρ * Real.sqrt v := by
  have hr0 : 0 < σ * r := mul_pos hσ hr
  have hσr : σ * r ≤ r := mul_le_of_le_one_left hr.le hσ1
  have hr2 : r ^ 2 ≤ b ^ 2 * u :=
    calc r ^ 2 ≤ (b * Real.sqrt u) ^ 2 := pow_le_pow_left₀ hr.le hrb 2
      _ = b ^ 2 * u := by rw [mul_pow, Real.sq_sqrt hu0]
  have hb2 : b ^ 2 ≤ 1 / 4 := by nlinarith
  have hr0sq : (σ * r) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hr0.le hσr 2
  have hcX : c * (σ * r) ^ 2 ≤ (σ * r) ^ 2 := by nlinarith [sq_nonneg (σ * r)]
  have h4 : c * (σ * r) ^ 2 ≤ u / 4 := by nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hb2)]
  have hv34 : 3 * u / 4 ≤ v := by linarith
  refine ⟨by linarith, ?_⟩
  have hsq : (σ * r) ^ 2 ≤ (ρ * Real.sqrt v) ^ 2 := by
    rw [mul_pow ρ, Real.sq_sqrt hv0]
    have hbρ : b ^ 2 ≤ (ρ / 2) ^ 2 := pow_le_pow_left₀ hb.le hbc 2
    nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hbρ), sq_nonneg ρ]
  exact (pow_le_pow_iff_left₀ hr0.le (by positivity) two_ne_zero).mp hsq

end GC.LongTime.Ch12
