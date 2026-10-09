import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.PulledCoreType
import DifferentialGeometry.Geometry.Collapse.SublevelCore.OpenBallModelTypeAtScale
import DifferentialGeometry.Geometry.Collapse.SublevelCore.FiniteUniformCollarApplications
import DifferentialGeometry.Geometry.Collapse.SublevelCore.FiniteCollarTransfer

/-!
# LC61 at a fixed scale for a finite model (LFR49, noncompact branch kernel)

Frozen blueprint master207A, LFR49 (A:29096): "At this FIXED `R`, restrict LFR48's maps to a
neighborhood of the closed radius-`10R` model ball. LC50's minimizing-direction argument uses only
`C¹` metric convergence … It applies to this `C^{K-5}` metric … The noncompact model has the actual
smooth total-normal-bundle map just constructed, so the unit-open-disk/full-bundle map in LC61
finishes its smooth open-ball type."

`exists_scale_eventually_open_ball_model_type_finite` (statement T4 of lane LFR49) is the
finite-order twin of `exists_scale_eventually_open_ball_model_type` (LC5X, smooth model). The model
is a complete finite-order (`C^{r+1}`, `1 ≤ r`) Riemannian manifold `(N, G)`, the comparison maps are
SMOOTH in LFR48's shape, and the model data are a field `V` (`|V| ≤ 2`, point margin `-1/4` against
the FINITE minimizing directions to `n` beyond `A₂`) and a core coordinate `u` whose open cores are
the whole model. Proof at one fixed `R`:
* LC57 (1)–(2) (`exists_scale_eventually_cone_radial_witnesses`): the source radial functions;
* B4 (`eventually_pushforward_inner_le_of_finite_limit`, LC50′ inside) on the compact model annulus
  `R/20 ≤ d_n ≤ 3R`: `|dj V| ≤ 4` and pairing `≤ -1/8` with the source minimizing directions;
* scaling (`radialScaled_field_pairing_le` on the SOURCES): the margins at `R⁻² g_i`;
* T3 (`eventually_open_ball_core_type_of_pulled_core`) with the rescaled instances;
* the open cores of `u` (`hcore`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Manifold
open GC.MetricGeometry

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- A rescaled proper metric space is proper (same topology, closed balls of rescaled radius). -/
theorem properSpace_rescale_of_properSpace {X : Type*} (m : MetricSpace X) (c : ℝ) (hc : 0 < c)
    (h : @ProperSpace X m.toPseudoMetricSpace) :
    @ProperSpace X (m.rescale c hc).toPseudoMetricSpace := by
  refine @ProperSpace.mk X (m.rescale c hc).toPseudoMetricSpace (fun x r => ?_)
  have h1 := MetricSpace.rescale_closedBall m c hc x (r / c)
  rw [mul_div_cancel₀ r hc.ne'] at h1
  rw [h1]
  exact @isCompact_closedBall X m.toPseudoMetricSpace h x (r / c)

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : ℕ → Type} [mM : ∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)] [∀ i, SigmaCompactSpace (M i)]
  [rbM : ∀ i, RiemannianBundle (fun x : M i => TangentSpace I x)]
  [rmM : ∀ i, IsRiemannianManifold I (M i)] [hMc : ∀ i, CompleteSpace (M i)]
  [crM : ∀ i, IsContinuousRiemannianBundle E (fun x : M i => TangentSpace I x)]

/-- **LC61 scale-R wrapper for a finite model (LFR49 noncompact branch, kernel).**
A finite-order (`C^{r+1}`, `1 ≤ r`) complete model `(N, G)` with smooth comparison maps in LFR48's
shape (exhaustion, `C¹` chart convergence of the pullback coefficients, distortion, coverage), a
supplied cone, the separate source curvature bounds, a field `V` with `|V| ≤ 2` and the point
margin `-1/4` against the FINITE minimizing directions to `n` beyond `A₂`, and an LC54-type core
coordinate `u` whose open cores are the whole model: there is `R₀ > 0` such that for every
`R ≥ R₀` one tail has every open ball `B(j_i n, ρ R)`, `ρ ∈ [1/5, 2]`, diffeomorphic to `N`. -/
theorem exists_scale_eventually_open_ball_model_type_finite {mdim : ℕ}
    (hdim : Module.finrank ℝ E = mdim + 1)
    {N : Type} [mN : MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [pN : ProperSpace N]
    [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]
    {r : ℕ∞} (hr : 1 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (n : N) {C : Type} [MetricSpace C] {o : C} (Hc : RadialConeData o)
    (hcone : ∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
      Nonempty (@KleinerLottApprox N C (mN.rescale R⁻¹ (inv_pos.mpr hR)) _ n o τ))
    (gSeq : ∀ i, SmoothRiemannianMetric I (M i)) (hSeqNorm : ∀ i, IsMetricNorm (gSeq i))
    (j : ∀ i, PartialDiffeomorph I I N (M i) ∞)
    (hexh : ∀ K : Set N, IsCompact K → ∀ᶠ i in atTop, K ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set E), IsCompact L → L ⊆ (extChartAt I x).target →
      MapCPConvergenceOn L 1
        (fun i => pullbackMetricCoefficients (gSeq i) ((j i : N → M i) ∘ (extChartAt I x).symm))
        (chartCoeff G x))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball n R, ∀ y ∈ ball n R,
      |dist (j i x) (j i y) - dist x y| < ε)
    (hcover : ∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
      ball (j i n) a ⊆ (j i : N → M i) '' ball n b)
    (hGH : PointedGHConverges (fun i => j i n) n)
    (Hb : ℕ → ℝ) (hHb : Tendsto Hb atTop atTop)
    (hsecM : ∀ i, ∀ y ∈ Metric.ball (j i n) (Hb i),
      SectionalBoundedBelowAt (gSeq i) y (-((Hb i)⁻¹ ^ 2)))
    (V : (x : N) → TangentSpace I x) {A₂ : ℝ}
    (hVB : ∀ x, G.inner x (V x) (V x) ≤ 4)
    (hVdir : ∀ x, A₂ ≤ dist n x → ∀ v ∈ G.finiteMinimizingDirectionsTo {n} x,
      G.inner x (V x) v ≤ -(1 / 4))
    {u : N → ℝ} (hu : Continuous u) (hucpt : ∀ T, IsCompact {x | u x ≤ T}) {T₀ : ℝ}
    {Wu : Set N} (hWu : IsOpen Wu) (hWuT : {x | T₀ ≤ u x} ⊆ Wu)
    (huW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ u Wu)
    (hVW : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun x => (⟨x, V x⟩ : TangentBundle I N)) Wu)
    (huV : ∀ x, T₀ ≤ u x → 0 < mvfderiv (I := I) u x (V x))
    (hcore : ∀ T : ℝ, T₀ < T → ∃ Ψ : PartialDiffeomorph I I N N ∞,
      Ψ.source = interior {x | u x ≤ T} ∧ Ψ.target = univ) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ᶠ i in atTop, ∀ ρ ∈ Icc (1 / 5 : ℝ) 2,
      ∃ Ψ : PartialDiffeomorph I I (M i) N ∞,
        Ψ.source = Metric.ball (j i n) (ρ * R) ∧ Ψ.target = univ := by
  -- the core `{u ≤ T₀}` is bounded
  obtain ⟨B₀, hB₀⟩ := (hucpt T₀).isBounded.subset_ball n
  have hmetricM : ∀ i a b, riemannianEDistOf (gSeq i) a b = ENNReal.ofReal (dist a b) :=
    fun i => riemannianEDistOf_eq_ofReal_dist (gSeq i) (hSeqNorm i)
  -- LC57 (1)–(2): the source radial functions at every large scale
  obtain ⟨R₂, -, hG1⟩ := exists_scale_eventually_cone_radial_witnesses (M := M) gSeq hmetricM
    hGH Hc hcone Hb hHb hsecM (δ := 1 / 2) (ε := ((1 / 64 : ℝ≥0) : ℝ)) (e := 1 / 80)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨max R₂ (max (20 * |A₂| + 1) (20 * |B₀| + 1)),
    lt_of_lt_of_le (by positivity) ((le_max_left _ _).trans (le_max_right _ _)),
    fun R hRR => ?_⟩
  have hR2 : R₂ ≤ R := (le_max_left _ _).trans hRR
  have hRA : 20 * |A₂| + 1 ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hRR)
  have hRB : 20 * |B₀| + 1 ≤ R := (le_max_right _ _).trans ((le_max_right _ _).trans hRR)
  have hR : 0 < R := by linarith [abs_nonneg A₂]
  have hRi : 0 < R⁻¹ := inv_pos.mpr hR
  have hA₂R : A₂ ≤ R / 20 := by linarith [le_abs_self A₂]
  have hB₀R : B₀ < R / 20 := by linarith [le_abs_self B₀]
  -- `η_i`: LC57 (1)–(2) at scale `R`, in the core theorems' form
  let Q : ∀ i, (M i → ℝ) → Prop := fun i F =>
    letI := (mM i).rescale R⁻¹ (inv_pos.mpr hR)
    let gR : SmoothRiemannianMetric I (M i) :=
      scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) (gSeq i)
    (1 / 80 : ℝ) < 1 / 40 ∧ (∀ x, |F x - dist (j i n) x| < 1 / 80) ∧
      LipschitzWith (1 / 64 : ℝ≥0) (fun x => F x - dist (j i n) x) ∧
      ∃ W : Set (M i), IsOpen W ∧ (∀ x, 1 / 10 ≤ dist (j i n) x → dist (j i n) x ≤ 10 → x ∈ W) ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F W ∧
        ∀ x, 1 / 10 ≤ dist (j i n) x → dist (j i n) x ≤ 10 →
          (1 - ((1 / 64 : ℝ≥0) : ℝ)) ^ 2 ≤ gR.inner x (gradientFun (I := I) gR F x)
            (gradientFun (I := I) gR F x)
  have hQ : ∀ᶠ i in atTop, ∃ F, Q i F := by
    filter_upwards [hG1 R hR hR2] with i hi
    obtain ⟨-, F, -, hFO, hFclose, -, hFdiff, -, -, hFgrad, -⟩ := hi
    exact ⟨F, core_clauses_of_radial_clauses_at_scale (gSeq i) hR (j i n) (by norm_num)
      (by norm_num) ⟨hFO, hFclose, hFdiff, fun q hq => (hFgrad q hq).1⟩⟩
  let η : ∀ i, M i → ℝ := fun i =>
    @dite _ (∃ F, Q i F) (Classical.propDecidable _) (fun h => h.choose) (fun _ _ => 0)
  have hηQ : ∀ᶠ i in atTop, Q i (η i) := by
    filter_upwards [hQ] with i hi
    have hηi : η i = hi.choose := dite_eq_left hi
    rw [hηi]
    exact hi.choose_spec
  -- B4 on the compact model annulus `R/20 ≤ d_n ≤ 3R`
  set CR : Set N := {x | R / 20 ≤ dist n x ∧ dist n x ≤ 3 * R} with hCRdef
  have hCRc : IsCompact CR := by
    refine (isCompact_closedBall n (3 * R)).of_isClosed_subset ?_ fun x hx => ?_
    · exact (isClosed_le continuous_const (continuous_const.dist continuous_id)).inter
        (isClosed_le (continuous_const.dist continuous_id) continuous_const)
    · rw [mem_closedBall, dist_comm]
      exact hx.2
  have hCRW : CR ⊆ Wu := by
    intro x hx
    apply hWuT
    by_contra hlt
    have hlt' : u x < T₀ := not_le.mp hlt
    have hxb := hB₀ (show u x ≤ T₀ from hlt'.le)
    rw [mem_ball, dist_comm] at hxb
    linarith [hx.1]
  let jK : ∀ i, PartialDiffeomorph I I N (M i) (2 : ℕ) := fun i =>
    DifferentialGeometry.PartialDiffeomorph.ofLE (j i) (WithTop.coe_le_coe.mpr le_top)
  have hB4 := eventually_pushforward_inner_le_of_finite_limit hr G hGnorm gSeq hmetricM
    (K := 2) le_rfl n jK hexh hconv hdist hcover hCRc n V (hVW.continuousOn.mono hCRW)
    (a := 1 / 4) (B := 2) two_pos
    (fun x hx v hv => hVdir x (hA₂R.trans hx.1) v hv)
    (fun x _ => by have := hVB x; norm_num; linarith) (α := 1 / 8) (by norm_num)
  -- T3 at the rescaled instances
  refine (fun hstep => ?_) (eventually_open_ball_core_type_of_pulled_core
    (mM := fun i => (mM i).rescale R⁻¹ hRi)
    (rbM := fun i => radialScaledBundle (gSeq i) R⁻¹ hRi)
    (rmM := fun i => radialScaledManifold (m := mM i) (gSeq i) (hmetricM i) R⁻¹ hRi)
    (cM := fun i => ((mM i).rescale_completeSpace_iff R⁻¹ hRi).mpr (hMc i))
    (crM := fun i => radialScaledContinuous (gSeq i) R⁻¹ hRi)
    (mN := mN.rescale R⁻¹ hRi) (pN := properSpace_rescale_of_properSpace mN R⁻¹ hRi pN)
    hdim (fun i => scaleMetric (R⁻¹ ^ 2) (pow_pos hRi 2) (gSeq i))
    (fun i => isMetricNorm_of_riemannianBundle _) n j ?hsrc ?hdist ?hcov V
    (α := 1 / 8 * R⁻¹) (B := 4 * R⁻¹) (ε := (1 / 64 : ℝ≥0)) ?hε ?hεB ?hpair hu hucpt
    (T₀ := T₀) ?hT₀ hWu hWuT huW hVW huV η (fun _ => 1 / 80) ?hη)
  case hsrc =>
    filter_upwards [hexh _ (isCompact_closedBall n (4 * R))] with i hi x hx
    apply hi
    have hx' : R⁻¹ * dist x n ≤ 4 := hx
    rw [mem_closedBall]
    have := mul_le_mul_of_nonneg_left hx' hR.le
    rwa [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul, mul_comm] at this
  case hdist =>
    filter_upwards [hdist (4 * R) (R / 40) (by positivity)] with i hi x hx y hy
    have hx' : R⁻¹ * dist x n < 4 := hx
    have hy' : R⁻¹ * dist y n < 4 := hy
    have hx4 : x ∈ ball n (4 * R) := by
      rw [mem_ball]
      have := mul_lt_mul_of_pos_left hx' hR
      rwa [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul, mul_comm] at this
    have hy4 : y ∈ ball n (4 * R) := by
      rw [mem_ball]
      have := mul_lt_mul_of_pos_left hy' hR
      rwa [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul, mul_comm] at this
    have h := hi x hx4 y hy4
    change |R⁻¹ * dist (j i x) (j i y) - R⁻¹ * dist x y| < 1 / 40
    rw [← mul_sub, abs_mul, abs_of_pos hRi]
    calc R⁻¹ * |dist (j i x) (j i y) - dist x y| < R⁻¹ * (R / 40) :=
          mul_lt_mul_of_pos_left h hRi
      _ = 1 / 40 := by field_simp
  case hcov =>
    filter_upwards [hcover (3 * R) (4 * R) (by positivity) (by linarith)] with i hi
    have h1 := MetricSpace.rescale_ball (mM i) R⁻¹ hRi (j i n) (3 * R)
    have h2 := MetricSpace.rescale_ball mN R⁻¹ hRi n (4 * R)
    rw [show R⁻¹ * (3 * R) = 3 by field_simp] at h1
    rw [show R⁻¹ * (4 * R) = 4 by field_simp] at h2
    rw [h1, h2]
    exact hi
  case hε => norm_num
  case hεB =>
    have : ((1 / 64 : ℝ≥0) : ℝ) = 1 / 64 := by norm_num
    rw [this]
    nlinarith
  case hpair =>
    filter_upwards [hB4] with i hi x hxs h1 h2
    have h1' : 1 / 20 ≤ R⁻¹ * dist n x := h1
    have h2' : R⁻¹ * dist n x ≤ 3 := h2
    have hxC : x ∈ CR := by
      constructor
      · have := mul_le_mul_of_nonneg_left h1' hR.le
        rw [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul] at this
        linarith
      · have := mul_le_mul_of_nonneg_left h2' hR.le
        rw [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul] at this
        linarith
    obtain ⟨hZB, hZdir⟩ := hi x hxC
    set Z := mfderiv I I (j i : N → M i) x (V x) with hZdef
    refine ⟨?_, ?_⟩
    · change √(R⁻¹ ^ 2 * (gSeq i).inner (j i x) Z Z) ≤ 4 * R⁻¹
      rw [Real.sqrt_le_left (by positivity)]
      have hZB0 : (gSeq i).inner (j i x) Z Z ≤ (2 * 2) ^ 2 := hZB
      have hZB' : (gSeq i).inner (j i x) Z Z ≤ 16 := by norm_num at hZB0; exact hZB0
      have h16 : R⁻¹ ^ 2 * (gSeq i).inner (j i x) Z Z ≤ R⁻¹ ^ 2 * 16 :=
        mul_le_mul_of_nonneg_left hZB' (by positivity)
      nlinarith
    · have hV' : ∀ w ∈ inwardMinimizingDirections (I := I) (gSeq i) (hSeqNorm i) (j i n) (j i x),
          (gSeq i).inner (j i x) (R⁻¹ • Z) w ≤ -(1 / 8 * R⁻¹) := by
        intro w hw
        have h : (gSeq i).inner (j i x) Z w ≤ -(1 / 8) :=
          inner_le_of_mem_inwardMinimizingDirections_of_finite (gSeq i) (hSeqNorm i) hZdir hw
        rw [map_smul, smul_apply, smul_eq_mul]
        have := mul_le_mul_of_nonneg_left h hRi.le
        linarith
      have h := radialScaled_field_pairing_le (gSeq i) (hSeqNorm i) hR (j i n) (j i x)
        (R⁻¹ • Z) hV'
      rwa [smul_smul, mul_inv_cancel₀ hR.ne', one_smul] at h
  case hT₀ =>
    intro x hx
    have hb := hB₀ hx
    rw [mem_ball] at hb
    change R⁻¹ * dist x n < 1 / 20
    calc R⁻¹ * dist x n < R⁻¹ * (R / 20) := mul_lt_mul_of_pos_left (by linarith) hRi
      _ = 1 / 20 := by field_simp
  case hη =>
    filter_upwards [hηQ] with i hi
    exact hi
  -- the open cores of `u`
  obtain ⟨T₁, hT₁, hfin⟩ := hstep
  obtain ⟨Ψb, hΨbs, hΨbt⟩ := hcore ((T₀ + T₁) / 2) (by linarith)
  filter_upwards [hfin] with i hi ρ hρ
  obtain ⟨Ψ, hΨs, hΨt⟩ := hi ρ hρ ((T₀ + T₁) / 2) ⟨by linarith, by linarith⟩
  have hball' : @Metric.ball (M i) ((mM i).rescale R⁻¹ hRi).toPseudoMetricSpace (j i n) ρ =
      Metric.ball (j i n) (ρ * R) := by
    have h := MetricSpace.rescale_ball (mM i) R⁻¹ hRi (j i n) (ρ * R)
    rwa [show R⁻¹ * (ρ * R) = ρ by field_simp] at h
  refine ⟨Ψ.trans Ψb, ?_, ?_⟩
  · rw [PartialDiffeomorph.trans_source, hΨs, hΨbs]
    refine (inter_eq_left.mpr fun y hy => ?_).trans hball'
    have hy' : y ∈ Ψ.source := by rw [hΨs]; exact hy
    have h := Ψ.toPartialEquiv.map_source hy'
    rw [hΨt] at h
    exact h
  · apply eq_univ_of_forall
    intro w
    have hw : w ∈ Ψb.target := by rw [hΨbt]; exact mem_univ w
    refine ⟨hw, ?_⟩
    have h := Ψb.toPartialEquiv.map_target hw
    change Ψb.symm w ∈ Ψ.target
    rw [hΨt]
    rw [hΨbs] at h
    exact h

end DifferentialGeometry.Geometry.Collapse
