import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceSliver
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceAfterEvent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialWindowScalarBound

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

variable {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric}
  {B ε C1 C2 τmin θ κ C1s C2s Cs : ℝ} {Ctime Cgrad : ℝ≥0} {phi : ℝ → ℝ}
  {D θcap qcan qs η t₀ t s : ℕ → ℝ} {p₀ p : ℕ → CutoffParameters} {δb ρb : ℕ → ℝ}
  {H : ℕ → RetainedCoreHistory.{u}}
  {records : ∀ n i, GeometricCutoffRecord (H n).toHistory i (p n)}
  {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
    ((H n).time (Fin.last (H n).eventCount)) (s n)}
  {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
  (hε : 0 < ε) (hεcone : ε ≤ coneAccuracy)
  (hκ : 0 < κ) (hphi : Perelman.AdmissiblePinchingFunction phi) (hθ : 0 < θ)
  (hCs : 1 ≤ Cs) (hCt : 0 < Ctime)
  (hH : ∀ n, (H n).InCutoffClass (P₀ := P₀) g₀ B (p₀ n) (δb n) (ρb n))
  (hG : ∀ n, (H n).IsContinuationSlab B (Fin.last (H n).eventCount) (G n))
  (hrec : ∀ n, (H n).IsCanonicalCutoffRecordFamily (p₀ n) (δb n) (ρb n) (records n))
  (hq : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n ∧ qcan n ≤ qs n ∧ qs n ≤ Cs * qcan n)
  (hpar : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
    D n ≤ (p₀ n).modelRadius ∧ n + 2 ≤ (p₀ n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
  (hscale : ∀ (n : ℕ) i b, ((n : ℝ) + 1) * qcan n ≤ ((records n i).static b).neck.scale)
  (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
  (hpinch : ∀ n, (H n).EventSlabsPinched phi ∧
    Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi)
  (hslabs : ∀ n,
    (H n).EventSlabsCanonical ε C1 C2 (qcan n) τmin (Fin.last (H n).eventCount) ∧
    (H n).EventSlabsDerivative Ctime (qcan n) (Fin.last (H n).eventCount) ∧
    (H n).EventSlabsGradient Cgrad (qcan n) (Fin.last (H n).eventCount) ∧
    (H n).EventSlabsSpatiallyCanonical ε C1s C2s (qs n) (Fin.last (H n).eventCount) ∧
    (H n).NoncollapsedBefore κ ε ((H n).time (Fin.last (H n).eventCount)))
  (hbefore : ∀ n, t₀ n ∈ Ico ((H n).time (Fin.last (H n).eventCount)) (s n) ∧
    (G n).CanonicalBefore ε C1 C2 (qcan n) τmin (t₀ n) ∧
    (G n).DerivativeBoundBefore Ctime (qcan n) (t₀ n) ∧
    (G n).GradientBoundBefore Cgrad (qcan n) (t₀ n) ∧
    (G n).SpatiallyCanonicalBefore ε C1s C2s (qs n) (t₀ n) ∧
    (H n).TerminalNoncollapsedBefore (hH n).2.1 (G n) (hG n).2 κ ε (t₀ n))
  (hsliver : ∀ n, 0 < η n ∧ t₀ n + η n < s n ∧
    (G n).DerivativeBoundBefore (2 * Ctime) (2 * qcan n) (t₀ n + η n) ∧
    (∀ t' ∈ Icc (t₀ n) (t₀ n + η n), ∀ x, (G n).flow.scalar t' x * η n ≤ 1 / ((n : ℝ) + 1) ∧
      |(G n).flow.scalar t' x - (G n).flow.scalar (t₀ n) x| ≤ qcan n / 4 ∧
      ∀ v : TangentSpace ThreeModel x,
        ((G n).flow.base.metric t').inner x v v ≤
          Real.exp 1 * ((G n).flow.base.metric (t₀ n)).inner x v v ∧
        ((G n).flow.base.metric (t₀ n)).inner x v v ≤
          Real.exp 1 * ((G n).flow.base.metric t').inner x v v) ∧
    ∀ i b, ((records n i).static b).neck.scale * η n ≤ 1 / ((n : ℝ) + 2))
  (hbad : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n ∧ t₀ n ≤ t n ∧
    t n < t₀ n + η n ∧ qcan n < (G n).flow.scalar (t n) (y n) ∧
    (G n).flow.scalar (t n) (y n) * (t n - (H n).time (Fin.last (H n).eventCount)) < θ ∧
    ¬ (H n).CapWindowPoint (records n) (Fin.last (H n).eventCount) (y n) (t n) (D n) (θcap n))

include hq hbad in
theorem tendsto_scalar_at_bad_point_atTop :
    Tendsto (fun n => (G n).flow.scalar (t n) (y n)) atTop atTop := by
  refine tendsto_atTop_mono (fun n => ((hq n).1.trans_lt (hbad n).2.2.2.1).le) ?_
  exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop

include hH hG hq hsliver hbad in
theorem tendsto_scalar_mul_time_atTop :
    Tendsto (fun n => (G n).flow.scalar (t n) (y n) * t₀ n) atTop atTop := by
  refine tendsto_scalar_mul_earlier_time_atTop_of_inCutoffClass (B := fun _ => B) hH G
    (fun n => (hG n).2) y (fun n => ⟨(hbad n).1.le, (hbad n).2.2.1.trans (hsliver n).2.1⟩)
    (tendsto_scalar_at_bad_point_atTop hq hbad) (C := 1) (fun n => ?_)
  have h1 := ((hsliver n).2.2.2.1 (t n) ⟨(hbad n).2.1, (hbad n).2.2.1.le⟩ (y n)).1
  have hη := (hsliver n).1
  have hR : 0 ≤ (G n).flow.scalar (t n) (y n) :=
    (lt_of_lt_of_le (by positivity) (hq n).1).le.trans (hbad n).2.2.2.1.le
  have hgap : t n - t₀ n ≤ η n := by linarith [(hbad n).2.2.1]
  have hn : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  calc (G n).flow.scalar (t n) (y n) * (t n - t₀ n) ≤ (G n).flow.scalar (t n) (y n) * η n :=
        mul_le_mul_of_nonneg_left hgap hR
    _ ≤ 1 := h1.trans hn

private theorem derivativeBoundBefore_of_le_threshold {P : OrientedThreeStage.{u}} {a s' : ℝ}
    {F : P.IncomingSlab a s'} {C : ℝ≥0} {q q' T : ℝ} (hqq : q ≤ q')
    (h : F.DerivativeBoundBefore C q T) : F.DerivativeBoundBefore C q' T :=
  fun x v hv hx => h x v hv (hqq.trans_lt hx)

private theorem gradientBoundBefore_of_le_threshold {P : OrientedThreeStage.{u}} {a s' : ℝ}
    {F : P.IncomingSlab a s'} {C : ℝ≥0} {q q' T : ℝ} (hqq : q ≤ q')
    (h : F.GradientBoundBefore C q T) : F.GradientBoundBefore C q' T :=
  fun x v hv hx => h x v hv (hqq.trans_lt hx)

include hε hεcone hκ hphi hCs hH hG hrec hq hpar hθcap hpinch hslabs hbefore hsliver hbad in
theorem eventually_scalar_le_on_normalized_ball_at_base :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 1 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
          (A / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        (G n).flow.scalar (t n) z ≤ Q * (G n).flow.scalar (t n) (y n) := by
  intro A hA
  obtain ⟨Q₁, Λ₁, D₁, R₁, ζ₁, hQ₁, hΛ₁, -, -, hζ₁, h₁⟩ :=
    exists_scalar_bound_at_distance_of_not_capWindowPoint_terminal_of_sliver.{u} hεcone κ C1s
      C2s hκ Ctime Cgrad hphi A hA Cs (1 / 2) (by norm_num)
  obtain ⟨Q₂, Λ₂, D₂, R₂, ζ₂, hQ₂, hΛ₂, -, -, hζ₂, h₂⟩ :=
    exists_scalar_bound_at_distance_of_not_capWindowPoint_after_event.{u} hεcone κ C1s C2s hκ
      Ctime Cgrad hphi A hA Cs (1 / 2) (by norm_num)
  refine ⟨max Q₁ Q₂, hQ₁.trans (le_max_left _ _), ?_⟩
  have hR := tendsto_scalar_at_bad_point_atTop hq hbad
  have hRt₀ := tendsto_scalar_mul_time_atTop hH hG hq hsliver hbad
  have hRsq : Tendsto (fun n => ε * Real.sqrt ((G n).flow.scalar (t n) (y n))) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp hR).const_mul_atTop hε
  have hbig : ∀ c : ℝ, ∀ᶠ n : ℕ in atTop, c ≤ (n : ℝ) + 1 := by
    intro c
    obtain ⟨N, hN⟩ := exists_nat_ge c
    filter_upwards [eventually_ge_atTop N] with n hn
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hsmall : ∀ c : ℝ, 0 < c → ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ c := by
    intro c hc
    filter_upwards [hbig (1 / c)] with n hn
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hc] at hn
    linarith
  filter_upwards [hR.eventually_ge_atTop (max Λ₁ Λ₂), hRt₀.eventually_ge_atTop (max Λ₁ Λ₂),
    hRsq.eventually_ge_atTop (max Λ₁ Λ₂), hbig (max R₁ R₂), hbig (max D₁ D₂),
    hsmall (min ζ₁ ζ₂) (lt_min hζ₁ hζ₂), eventually_ge_atTop 2]
    with n hRn hRtn hρn hRr hDn hζn hn2
  obtain ⟨hacc, hD1, hDrad, hord, -⟩ := hpar n
  obtain ⟨hq1, hq2, hq3⟩ := hq n
  obtain ⟨hat, ht₀t, htη, hqR, -, hnot⟩ := hbad n
  obtain ⟨hη, hηs, -, hsl, hscη⟩ := hsliver n
  have hΛ : 1 ≤ max Λ₁ Λ₂ := hΛ₁.trans (le_max_left _ _)
  have hR0 : 0 < (G n).flow.scalar (t n) (y n) := by linarith
  have hqpos : 0 < qs n := lt_of_lt_of_le (by positivity) (hq1.trans hq2)
  have hqsR : qs n ≤ Cs * (G n).flow.scalar (t n) (y n) :=
    hq3.trans (mul_le_mul_of_nonneg_left hqR.le (by linarith))
  have hts : t n < s n := htη.trans hηs
  have htI : t n ∈ Icc (t₀ n) (t₀ n + η n) := ⟨ht₀t, htη.le⟩
  have hclose : ∀ x, |(G n).flow.scalar (t n) x - (G n).flow.scalar (t₀ n) x| ≤
      (G n).flow.scalar (t n) (y n) / 4 := fun x =>
    (hsl (t n) htI x).2.1.trans (by linarith)
  have hmet : ∀ x (v : TangentSpace ThreeModel x),
      ((G n).flow.base.metric (t₀ n)).inner x v v ≤
        Real.exp 1 * ((G n).flow.base.metric (t n)).inner x v v := fun x v =>
    ((hsl (t n) htI x).2.2 v).2
  have hnotcw : ∀ Dc : ℝ, Dc ≤ D n →
      ¬ (H n).CapWindowPoint (records n) (Fin.last (H n).eventCount) (y n) (t₀ n) Dc (1 / 2) := by
    intro Dc hDc hcw
    have hS : ∀ i b, ((records n i).static b).neck.scale ≤ 1 / ((n : ℝ) + 2) / η n := fun i b =>
      (le_div_iff₀ hη).mpr (hscη i b)
    have hslack : 1 / ((n : ℝ) + 2) / η n * (t n - t₀ n) ≤
        (1 / 2 + 1 / ((n : ℝ) + 2)) - 1 / 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hη]
      have : (0 : ℝ) ≤ 1 / ((n : ℝ) + 2) := by positivity
      nlinarith
    have hθn : 1 / 2 + 1 / ((n : ℝ) + 2) ≤ θcap n := by
      have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      have h4 : 2 / ((n : ℝ) + 2) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]
        linarith
      have := hθcap n
      have e : 1 / ((n : ℝ) + 2) + 1 / ((n : ℝ) + 2) = 2 / ((n : ℝ) + 2) := by ring
      linarith
    exact hnot ((hcw.of_le_time ht₀t hS hslack).mono hDc hθn)
  have hslab' := (hslabs n).2.1
  rcases (hbefore n).1.1.lt_or_eq with hlt | heq
  · intro z hz
    refine (h₁ (H n) (hH n).2.1 (G n) (hG n).2 (p₀ n) (δb n) (ρb n) (records n) (hrec n)
      ((le_max_left _ _).trans (hRr.trans (hD1.trans hDrad))) (by omega)
      (hacc.trans (hζn.trans (min_le_left _ _))) hlt ht₀t hts (y n) (qs n) ε hqpos hqsR
      ((le_max_left _ _).trans hRn) ((le_max_left _ _).trans hRtn) hclose hmet
      (hbefore n).2.2.2.2.1
      (fun j hj => derivativeBoundBefore_of_le_threshold hq2 (hslab' j hj))
      (derivativeBoundBefore_of_le_threshold hq2 (hbefore n).2.2.1)
      (gradientBoundBefore_of_le_threshold hq2 (hbefore n).2.2.2.1) (hpinch n).1 (hpinch n).2
      (hbefore n).2.2.2.2.2 ((le_max_left _ _).trans hρn)
      (hnotcw D₁ ((le_max_left _ _).trans (hDn.trans hD1))) z hz).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hR0.le
  · have hne : Fin.last (H n).eventCount ≠ 0 := by
      intro h0
      have htime : (H n).time (Fin.last (H n).eventCount) = 0 := by
        rw [h0]
        exact (H n).time_zero
      rw [show t₀ n = 0 from heq.symm.trans htime, mul_zero] at hRtn
      linarith
    obtain ⟨j, hj⟩ := Fin.exists_succ_eq.mpr hne
    have key : ∀ (k : Fin ((H n).eventCount + 1)) (_ : j.succ = k)
        (Gk : ((H n).stage k).IncomingSlab ((H n).time k) (s n))
        (_ : Gk.flow.base.metric ((H n).time k) = (H n).initialMetric k)
        (yk : ((H n).stage k).Carrier), (H n).time k < t n →
        qs n ≤ Cs * Gk.flow.scalar (t n) yk → Λ₂ ≤ Gk.flow.scalar (t n) yk →
        Λ₂ ≤ Gk.flow.scalar (t n) yk * (H n).time k →
        (∀ x, |Gk.flow.scalar (t n) x - Gk.flow.scalar ((H n).time k) x| ≤
          Gk.flow.scalar (t n) yk / 4) →
        (∀ x (v : TangentSpace ThreeModel x), (Gk.flow.base.metric ((H n).time k)).inner x v v ≤
          Real.exp 1 * (Gk.flow.base.metric (t n)).inner x v v) →
        (H n).EventSlabsSpatiallyCanonical ε C1s C2s (qs n) k →
        (H n).EventSlabsDerivative Ctime (qs n) k → (H n).EventSlabsGradient Cgrad (qs n) k →
        (H n).NoncollapsedBefore κ ε ((H n).time k) →
        Λ₂ ≤ ε * Real.sqrt (Gk.flow.scalar (t n) yk) →
        ¬ (H n).CapWindowPoint (records n) k yk ((H n).time k) D₂ (1 / 2) →
        ∀ z ∈ riemannianBallOf (Gk.flow.base.metric (t n)) yk
          (A / Real.sqrt (Gk.flow.scalar (t n) yk)),
          Gk.flow.scalar (t n) z ≤ Q₂ * Gk.flow.scalar (t n) yk := by
      intro k hk
      subst hk
      intro Gk hGk yk hkt hqk hΛk hΛkt hck hmk hspk hdk hgk hnck hρk hnotk
      exact h₂ (H n) (p₀ n) (δb n) (ρb n) (records n) (hrec n)
        ((le_max_right _ _).trans (hRr.trans (hD1.trans hDrad))) (by omega)
        (hacc.trans (hζn.trans (min_le_right _ _))) j Gk hGk hkt hts yk (qs n) ε hqpos hqk hΛk
        hΛkt hck hmk hspk hdk hgk (hpinch n).1 hnck hρk hnotk
    intro z hz
    refine (key (Fin.last (H n).eventCount) hj (G n) (hG n).2 (y n) hat hqsR
      ((le_max_right _ _).trans hRn)
      (((le_max_right _ _).trans hRtn).trans_eq
        (congrArg ((G n).flow.scalar (t n) (y n) * ·) heq.symm))
      (fun x => by
        rw [congrArg (fun r => (G n).flow.scalar r x) heq]
        exact hclose x)
      (fun x v => by
        rw [congrArg (fun r => ((G n).flow.base.metric r).inner x v v) heq]
        exact hmet x v) (hslabs n).2.2.2.1
      (fun i hi => derivativeBoundBefore_of_le_threshold hq2 (hslab' i hi))
      (fun i hi => gradientBoundBefore_of_le_threshold hq2 ((hslabs n).2.2.1 i hi))
      (hslabs n).2.2.2.2 ((le_max_right _ _).trans hρn)
      (heq ▸ hnotcw D₂ ((le_max_right _ _).trans (hDn.trans hD1))) z hz).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hR0.le

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
