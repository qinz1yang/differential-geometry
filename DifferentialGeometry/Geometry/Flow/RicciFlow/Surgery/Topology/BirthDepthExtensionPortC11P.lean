import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BirthWindowAnchorBound

/-!
# O-CH11-FIX3 port of astra `BirthDepthExtension`（`PortC11P`）

来源：donor `DifferentialGeometry/Geometry/Flow/RicciFlow/Surgery/Topology/BirthDepthExtension.lean`
（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。修补（elaboration only；no statement / definition /
proof idea altered）：
* `open private RetainedCoreHistory.exists_birth_persistence_inputs_eventually … from …` 的模块名
  `BirthTimeZeroBound` → `BirthTimeZeroBoundPortC11P`；
* 三个 opened private 名字在调用处写全名 `RetainedCoreHistory.…`，并对
  `exists_birth_persistence_inputs_eventually` 补 `(ρb := ρb)`（同 `BirthAnchorDistancePortC11P`）；
  `filter_upwards [RetainedCoreHistory.eventually_one_div_nat_add_one_le …]` 因此折成两行；
* `linarith` hint `Nat.cast_nonneg n` → `Nat.cast_nonneg (α := ℝ) n`（`IsOrderedRing ?m` stuck）；
* `e1` 的 `field_simp` 已关闭目标，删去其后多余的 `ring`（"No goals to be solved"）。

原路径 `BirthDepthExtension` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open private RetainedCoreHistory.exists_birth_persistence_inputs_eventually
  RetainedCoreHistory.eventually_nat_add_one_ge
  RetainedCoreHistory.eventually_one_div_nat_add_one_le from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BirthTimeZeroBoundPortC11P

universe u

namespace RetainedCoreHistory

variable {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric} {Ctime : ℝ≥0} {phi : ℝ → ℝ}
  {D θcap q R : ℕ → ℝ} {p₀ p : ℕ → CutoffParameters} {δb ρb : ℕ → ℝ}
  {H : ℕ → RetainedCoreHistory.{u}}
  {records : ∀ n i, GeometricCutoffRecord (H n).toHistory i (p n)}
  {t : ∀ n, Icc (0 : ℝ) (H n).toHistory.horizon}
  {y : ∀ n, ((H n).toHistory.stageAt (t n)).Carrier}
  (hphi : Perelman.AdmissiblePinchingFunction phi)
  (hinit : ∀ n, Nonempty (InitialIdentification P₀ g₀ (H n).toHistory))
  (hrec : ∀ n, (H n).IsCanonicalCutoffRecordFamily (p₀ n) (δb n) (ρb n) (records n))
  (hq : ∀ n : ℕ, (n : ℝ) + 1 ≤ q n ∧ q n < R n)
  (hbirth : ∀ n, (H n).time ((H n).toHistory.activeStage (t n)) = (t n : ℝ))
  (hne : ∀ n, (H n).toHistory.activeStage (t n) ≠ 0)
  (hpar : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
    D n ≤ (p₀ n).modelRadius ∧ n + 2 ≤ (p₀ n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
  (hscale : ∀ (n : ℕ) i b, ((n : ℝ) + 1) * q n ≤ ((records n i).static b).neck.scale)
  (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
  (hpinch : ∀ n, (H n).EventSlabsPinched phi)
  (hlast : ∀ n, (H n).toHistory.activeStage (t n) = Fin.last (H n).eventCount →
    ∃ h : (H n).time (Fin.last (H n).eventCount) < (H n).horizon,
      Perelman.PhiAlmostNonnegative ((H n).finalSlab h).flow
        (Icc ((H n).time (Fin.last (H n).eventCount)) (H n).horizon) phi)
  (hder : ∀ n, (H n).EventSlabsDerivative Ctime (q n) ((H n).toHistory.activeStage (t n)))
  (hnot : ∀ n, ¬ (H n).CapWindowPoint (records n) ((H n).toHistory.activeStage (t n))
    (y n) (t n) (D n) (θcap n))

include hphi hinit hrec hq hbirth hpar hscale hθcap hpinch hlast hder hnot in
private theorem exists_eventually_isTracedRegion_at_birth_of_scalar_le_along_traces
    {A T Q : ℝ} (hA : 0 < A) (hT : 0 < T) (hQ : 1 ≤ Q) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ᶠ n in atTop,
      ∀ uu : Icc (0 : ℝ) (H n).toHistory.horizon, (uu : ℝ) = (t n : ℝ) - T / R n →
      (∀ x ∈ riemannianBallOf
          ((H n).toHistory.stageMetric ((H n).toHistory.activeStage (t n)) (t n)) (y n)
          (A / Real.sqrt (R n)),
        ∀ (w : Icc (0 : ℝ) (H n).toHistory.horizon) (_ : uu ≤ w) (hwt : w ≤ t n)
          (B : BackwardPointTrace (H n).toHistory ((H n).toHistory.activeStage w)
            ((H n).toHistory.activeStage (t n)) ((H n).toHistory.activeStage_mono hwt) x)
          (v : Icc (0 : ℝ) (H n).toHistory.horizon) (hwv : w ≤ v) (hvt : v ≤ t n),
          metricScalarAt ((H n).toHistory.stageMetric ((H n).toHistory.activeStage v) v)
            (B.point ((H n).toHistory.activeStage v) ((H n).toHistory.activeStage_mono hwv)
              ((H n).toHistory.activeStage_mono hvt)) ≤ 2 * (Q * R n)) →
      (H n).toHistory.isTracedRegion (t n) (y n) (A / Real.sqrt (R n)) (T / R n)
        (K₀ * R n) := by
  obtain ⟨c, hc, hB⟩ := exists_isTracedRegion_or_capWindowPoint_at_scale.{u}
  have hφ0 := hphi.pos 0
  have hφ1 := hphi.pos 1
  have hTQ : 0 < 8 * T * Q := by positivity
  let θ₁ : ℝ := max (1 / 4) (1 - c / (8 * T * Q))
  have hθ₁ : θ₁ < 1 := max_lt (by norm_num) (by have := div_pos hc hTQ; linarith)
  have hΘ0 : 0 < (θ₁ + 1) / 2 := by
    have := le_max_left (1 / 4 : ℝ) (1 - c / (8 * T * Q))
    dsimp [θ₁]
    linarith
  obtain ⟨Cbirth, hCb, hB⟩ := hB ((θ₁ + 1) / 2) hΘ0 (by linarith) Ctime
  let Dcap : ℝ := 2 * StandardCap.transitionEnd + Real.sqrt (8 * Q) *
    Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0)) * Q * T) * A + 1
  have hDs : StandardCap.transitionEnd < Dcap := by
    have := StandardCap.transitionEnd_pos
    have : 0 ≤ Real.sqrt (8 * Q) *
        Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0)) * Q * T) * A := by positivity
    dsimp [Dcap]
    linarith
  obtain ⟨Rrad, -, m₀, -, ζ₀, δ₀, hζ₀, -, hδ₀, hB⟩ := hB Dcap hDs
  obtain ⟨a₀, -, hHI, hev⟩ := RetainedCoreHistory.exists_birth_persistence_inputs_eventually
    (ρb := ρb) hinit (fun n => (hq n).1) hpar hscale
  have hθev : ∀ᶠ n : ℕ in atTop, θ₁ ≤ θcap n := by
    filter_upwards [RetainedCoreHistory.eventually_one_div_nat_add_one_le
      (show 0 < 1 - θ₁ by linarith)] with n hn
    have hn' : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    linarith [hθcap n]
  refine ⟨8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * Q, by positivity, ?_⟩
  filter_upwards [hev Rrad ζ₀ δ₀ Cbirth m₀ hζ₀ hδ₀ hCb,
    RetainedCoreHistory.eventually_nat_add_one_ge Dcap, hθev] with n hn hDn hθn
  obtain ⟨hδn, hRn, hmn, hζn, hbirthscale⟩ := hn
  intro uu huu hscal
  have hR0 : 0 < R n := (lt_of_lt_of_le (by positivity) (hq n).1).trans (hq n).2
  have hut : uu ≤ t n := by
    change (uu : ℝ) ≤ (t n : ℝ)
    rw [huu]
    exact sub_le_self _ (div_pos hT hR0).le
  have hd := (H n).derivativeBound_inputs_at_birth (hbirth n) Ctime (q n)
  have hR1 : 1 ≤ R n := by linarith [(hq n).1, (hq n).2, Nat.cast_nonneg (α := ℝ) n]
  have hQR : 1 ≤ Q * R n := hR1.trans (le_mul_of_one_le_left hR0.le hQ)
  rcases hB (H n) (p₀ n) (δb n) (ρb n) (records n) (hrec n) hδn hRn hmn hζn
      (q n) a₀ (lt_of_lt_of_le (by positivity) (hq n).1)
      (fun x => (hHI n x).1) (fun x => (hHI n x).2)
      (fun i b => (hbirthscale i b).1) (fun i b => (hbirthscale i b).2)
      phi hphi (hpinch n) uu (t n) hut (hlast n) (hder n) hd.1 hd.2
      (y n) (R n) A T Q Dcap θ₁ hR0 hA hT
      hQR huu
      (le_max_left _ _) (le_max_right _ _) (by linarith) le_rfl hscal
      (by dsimp [Dcap]; linarith) with htr | hcw
  · simpa only [mul_assoc] using htr
  · exact False.elim ((hnot n) (hcw.mono (hDn.trans (hpar n).2.1) hθn))

include hphi hinit hrec hq hbirth hne hpar hscale hθcap hpinch hlast hder hnot in
/-- A uniform scalar anchor on every smaller traced depth extends the same
birth family by a positive amount independent of the spatial radius. -/
theorem depthExtendable_add_of_windowAnchorBound_at_birth
    {σ : ℕ → ℕ} (hσ : StrictMono σ) {Tstar M : ℝ} (hT : 0 < Tstar) (hM : 0 ≤ M)
    (hext : ∀ T : ℝ, 0 < T → T < Tstar →
      ObservedHistory.DepthExtendable (fun n => (H n).toHistory) t y R σ T)
    (hanc : ∀ T' : ℝ, 0 < T' → T' < Tstar → ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      ∀ x ∈ riemannianBallOf ((H (σ i)).toHistory.stageMetric
          ((H (σ i)).toHistory.activeStage (t (σ i))) (t (σ i))) (y (σ i))
          (A / Real.sqrt (R (σ i))),
      ∀ (w : Icc (0 : ℝ) (H (σ i)).toHistory.horizon),
        (w : ℝ) = (t (σ i) : ℝ) - T' / R (σ i) →
      ∀ (hwt : w ≤ t (σ i))
        (Bt : BackwardPointTrace (H (σ i)).toHistory
          ((H (σ i)).toHistory.activeStage w) ((H (σ i)).toHistory.activeStage (t (σ i)))
          ((H (σ i)).toHistory.activeStage_mono hwt) x),
        metricScalarAt ((H (σ i)).toHistory.stageMetric ((H (σ i)).toHistory.activeStage w) w)
          (Bt.point ((H (σ i)).toHistory.activeStage w) le_rfl
            ((H (σ i)).toHistory.activeStage_mono hwt)) ≤ M * R (σ i)) :
    ObservedHistory.DepthExtendable (fun n => (H n).toHistory) t y R σ
      (Tstar + 1 / (32 * ((Ctime : ℝ) + 1) * (M + 1))) := by
  intro A hA
  have hRpos : ∀ n, 0 < R n := fun n =>
    (lt_of_lt_of_le (by positivity) (hq n).1).trans (hq n).2
  have hC0 : (0 : ℝ) ≤ Ctime := Ctime.coe_nonneg
  set Tg : ℝ := Tstar + 1 / (32 * ((Ctime : ℝ) + 1) * (M + 1)) with hTg
  set Δ : ℝ := 1 / (8 * ((Ctime : ℝ) + 1) * (M + 1)) with hΔ
  have hΔ0 : 0 < Δ := by positivity
  set T' : ℝ := max (Tstar - Δ / 2) (Tstar / 2) with hT'
  have hT'0 : 0 < T' := lt_max_of_lt_right (half_pos hT)
  have hT'lt : T' < Tstar := max_lt (by linarith) (by linarith)
  have hTgΔ : Tg = Tstar + Δ / 4 := by
    rw [hTg, hΔ]
    field_simp
    ring
  have hgap : Tg - T' ≤ 3 * Δ / 4 := by
    have := le_max_left (Tstar - Δ / 2) (Tstar / 2)
    linarith
  have hTg0 : 0 < Tg := by positivity
  have hCΔ : 4 * (Ctime : ℝ) * (M + 1) * Δ ≤ 1 / 2 := by
    rw [hΔ]
    rw [show 4 * (Ctime : ℝ) * (M + 1) * (1 / (8 * ((Ctime : ℝ) + 1) * (M + 1))) =
      (Ctime : ℝ) / (2 * ((Ctime : ℝ) + 1)) by field_simp; ring]
    rw [div_le_iff₀ (by positivity)]
    linarith
  obtain ⟨K₁, hK₁, hev1⟩ := hext T' hT'0 hT'lt A hA
  have hev2 := hanc T' hT'0 hT'lt A hA
  obtain ⟨K₀, hK₀, hev3⟩ :=
    exists_eventually_isTracedRegion_at_birth_of_scalar_le_along_traces
      hphi hinit hrec hq hbirth hpar hscale hθcap hpinch hlast hder hnot
      (A := A) (T := Tg) (Q := 9 * K₁ + 4 * (M + 1)) hA hTg0 (by linarith)
  have hRt := tendsto_scale_mul_birth_time_atTop_of_initialIdentification
    (records := records) hinit hq hbirth hne
  refine ⟨K₀, hK₀, ?_⟩
  filter_upwards [hev1, hev2, hσ.tendsto_atTop.eventually hev3,
    hσ.tendsto_atTop.eventually (hRt.eventually_gt_atTop Tg)] with i h1 h2 h3 h4
  generalize σ i = n at h1 h2 h3 h4 ⊢
  have hR := hRpos n
  have hut0 : 0 ≤ (t n : ℝ) - Tg / R n := by
    rw [sub_nonneg, div_le_iff₀ hR]
    linarith
  let uu : Icc (0 : ℝ) (H n).toHistory.horizon :=
    ⟨(t n : ℝ) - Tg / R n, hut0,
      (sub_le_self _ (div_pos hTg0 hR).le).trans (t n).2.2⟩
  refine h3 uu rfl ?_
  intro x hx w huw hwt B v hwv hvt
  obtain ⟨-, -, a, hat', ha, htr⟩ := h1
  by_cases hva : a ≤ v
  · obtain ⟨A₁, hA₁⟩ := htr x hx
    have hpt := BackwardPointTrace.point_unique
      (B.restrictFirst ((H n).toHistory.activeStage_mono hwv)
        ((H n).toHistory.activeStage_mono hvt))
      (A₁.restrictFirst ((H n).toHistory.activeStage_mono hva)
        ((H n).toHistory.activeStage_mono hvt))
      ((H n).toHistory.activeStage v) le_rfl ((H n).toHistory.activeStage_mono hvt)
    have hnorm := hA₁.1 v hva hvt
    have hsc := scalar_abs_le_rm ((H n).toHistory.stageMetric ((H n).toHistory.activeStage v) v)
      (A₁.point ((H n).toHistory.activeStage v) ((H n).toHistory.activeStage_mono hva)
        ((H n).toHistory.activeStage_mono hvt))
    have hfin : (Module.finrank ℝ (TangentSpace ThreeModel
        (A₁.point ((H n).toHistory.activeStage v) ((H n).toHistory.activeStage_mono hva)
          ((H n).toHistory.activeStage_mono hvt))) : ℝ) = 3 := by
      change ((Module.finrank ℝ ThreeSpace : ℕ) : ℝ) = 3
      simp [ThreeSpace]
    have hsq : Real.sqrt (normSq0S ((H n).toHistory.stageMetric ((H n).toHistory.activeStage v) v)
        (A₁.point ((H n).toHistory.activeStage v) ((H n).toHistory.activeStage_mono hva)
          ((H n).toHistory.activeStage_mono hvt)) 4
        (metricRm04At ((H n).toHistory.stageMetric ((H n).toHistory.activeStage v) v)
          (A₁.point ((H n).toHistory.activeStage v) ((H n).toHistory.activeStage_mono hva)
            ((H n).toHistory.activeStage_mono hvt)))) ≤
        K₁ * R n :=
      (Real.sqrt_le_sqrt hnorm).trans (Real.sqrt_sq (by positivity)).le
    rw [hfin] at hsc
    refine (le_of_eq (congrArg _ hpt)).trans ((le_abs_self _).trans (hsc.trans ?_))
    nlinarith
  · have hva' : v < a := lt_of_not_ge hva
    have hwa : w ≤ a := hwv.trans hva'.le
    have hanchor := h2 x hx a ha hat'
      (B.restrictFirst ((H n).toHistory.activeStage_mono hwa)
        ((H n).toHistory.activeStage_mono hat'))
    have hd := (H n).derivativeBound_inputs_at_birth (hbirth n) Ctime (q n)
    have haw : (a : ℝ) - w ≤ (Tg - T') / R n := by
      have hw : (t n : ℝ) - Tg / R n ≤ (w : ℝ) := huw
      have ha' : (a : ℝ) = (t n : ℝ) - T' / R n := ha
      calc (a : ℝ) - w ≤ ((t n : ℝ) - T' / R n) - ((t n : ℝ) - Tg / R n) := by
            rw [ha']; linarith
        _ = (Tg - T') / R n := by ring
    have htime : (Ctime : ℝ) * (2 * (M + 1) * R n) * ((a : ℝ) - w) ≤ 1 / 2 := by
      have e1 : (Ctime : ℝ) * (2 * (M + 1) * R n) * ((Tg - T') / R n) =
          2 * (Ctime : ℝ) * (M + 1) * (Tg - T') := by
        field_simp
      have e2 : (Ctime : ℝ) * (2 * (M + 1) * R n) * ((a : ℝ) - w) ≤
          (Ctime : ℝ) * (2 * (M + 1) * R n) * ((Tg - T') / R n) :=
        mul_le_mul_of_nonneg_left haw (by positivity)
      have e3 : 2 * (Ctime : ℝ) * (M + 1) * (Tg - T') ≤
          4 * (Ctime : ℝ) * (M + 1) * Δ := by
        calc
          2 * (Ctime : ℝ) * (M + 1) * (Tg - T') ≤
              2 * (Ctime : ℝ) * (M + 1) * (2 * Δ) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          _ = 4 * (Ctime : ℝ) * (M + 1) * Δ := by ring
      linarith
    have hstep := (H n).scalar_le_two_mul_of_backwardPointTrace_of_scalar_le_at
      (Ctime := Ctime) (qcan := q n) (M := 2 * (M + 1) * R n)
      hwa hat' B (hder n) hd.1 hd.2 (by positivity)
      (by nlinarith [(hq n).2, mul_nonneg hM hR.le])
      (hanchor.trans (by nlinarith [mul_nonneg hM hR.le])) htime v hwv hva'.le
    exact hstep.trans (by nlinarith)


include hphi hinit hrec hq hbirth hne hpar hscale hθcap hpinch hlast hnot in
/-- The actual positive-depth and window producers, followed by the birth
depth gain, exclude finite maximal depth on the same selected subsequence. -/
theorem exists_subseq_depthExtendable_all_at_birth_of_initialIdentification
    {ε C1 C2 κ ρ : ℝ} {Cgrad : ℝ≥0}
    (hεcone : ε ≤ coneAccuracy) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hslabs : ∀ n,
      (H n).EventSlabsSpatiallyCanonical ε C1 C2 (q n) ((H n).toHistory.activeStage (t n)) ∧
      (H n).EventSlabsDerivative Ctime (q n) ((H n).toHistory.activeStage (t n)) ∧
      (H n).EventSlabsGradient Cgrad (q n) ((H n).toHistory.activeStage (t n)))
    (hnc : ∀ n, (H n).NoncollapsedBefore κ ρ (t n))
    (hRscalar : ∀ n, R n = metricScalarAt
      ((H n).toHistory.stageMetric ((H n).toHistory.activeStage (t n)) (t n)) (y n))
    (hε : 0 < ε) (hεX : ε ≤ crossingNeckAccuracy.{u})
    (hεW : ε ≤ crossingWindowNeckAccuracy.{u}) (σ₀ : ℕ → ℕ) (hσ₀ : StrictMono σ₀) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ T : ℝ, 0 < T →
      ObservedHistory.DepthExtendable (fun n => (H n).toHistory) t y R (σ₀ ∘ ψ) T := by
  obtain ⟨ψ, hψ, hcase⟩ := exists_subseq_all_depth_or_maximal_window_at_birth
    hεcone hκ hρ hphi hinit hrec hq hbirth hne hpar hscale hpinch hlast hslabs hnc
    hε hεX hεW hRscalar hθcap hnot σ₀ hσ₀
  refine ⟨ψ, hψ, ?_⟩
  rcases hcase with hall | ⟨Tstar, hT, M, hM, hext, hmax, hanc⟩
  · exact hall
  · have hgain := depthExtendable_add_of_windowAnchorBound_at_birth
      hphi hinit hrec hq hbirth hne hpar hscale hθcap hpinch hlast
      (fun n => (hslabs n).2.1) hnot (hσ₀.comp hψ) hT hM hext hanc
    have hlt : Tstar < Tstar + 1 / (32 * ((Ctime : ℝ) + 1) * (M + 1)) :=
      lt_add_of_pos_right _ (by positivity)
    exact False.elim (hmax id strictMono_id _ hlt
      (by simpa only [Function.comp_id] using hgain))

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
