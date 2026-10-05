import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.PulledCoreClosed
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LFR49InputsApplications

/-!
# LC38, closed form, at a fixed scale for a finite model (LFR49 noncompact branch)

The closed twins of `exists_scale_eventually_open_ball_model_type_finite` (T4) and
`exists_scale_eventually_open_ball_bundle_type_finite` (T4 + T5): with the same comparison maps,
field, margins and core coordinate, there is `R₀` such that for every scale `R ≥ R₀` there is a
level window `(T₀, T₁)` and one tail on which EVERY radial function `η` of the rescaled source
`(M_i, R⁻¹ d)` with `|η - R⁻¹ d(j_i n, ·)| < 1/40`, `(1/64)`-Lipschitz error and smooth near the
annulus `{1/10 ≤ R⁻¹ d ≤ 10}` has its ACTUAL sublevels `{η ≤ ρ}`, `ρ ∈ [1/5, 2]`, carried by an
ambient partial diffeomorphism onto the model cores `{u ≤ ρ'}`, `ρ' ∈ (T₀, T₁)`.

* `exists_scale_eventually_closed_core_type_finite` (T4 closed): general core coordinate `u`;
* `exists_scale_eventually_closed_disc_core_type_finite` (T4 + T5 closed): `u = ‖(D⁻¹ ·).2‖` for a
  smooth bundle diffeomorphism `D : TotalSpace F V ≃ N`, so the model cores are the disc cores
  `D_T` of LC45 and every `T > ℓ + 1` close enough to `ℓ + 1` occurs.

The proof is T4's (B4 margins on the model annulus `R/20 ≤ d_n ≤ 3R`, rescaled instances) with
`eventually_closed_core_of_pulled_core` in place of T3; no source radial function is constructed.
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

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : ℕ → Type} [mM : ∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)] [∀ i, SigmaCompactSpace (M i)]
  [rbM : ∀ i, RiemannianBundle (fun x : M i => TangentSpace I x)]
  [rmM : ∀ i, IsRiemannianManifold I (M i)] [hMc : ∀ i, CompleteSpace (M i)]
  [crM : ∀ i, IsContinuousRiemannianBundle E (fun x : M i => TangentSpace I x)]

/-- **LC38 closed, scale `R`, finite model (T4 closed).** In T4's setting (without its open-core
hypothesis): there is `R₀ > 0` such that for every `R ≥ R₀` there are `T₁ > T₀` and a tail on which
every radial function `η` of `(M_i, R⁻¹ d)` with `|η - d(j_i n, ·)| < e_η < 1/40`,
`(1/64)`-Lipschitz error and smooth near `{1/10 ≤ d(j_i n, ·) ≤ 10}` (all in `R⁻¹ d`), every
`ρ ∈ [1/5, 2]` and every `ρ' ∈ (T₀, T₁)` have an ambient partial diffeomorphism `M_i ⇀ N` whose
source contains `{η ≤ ρ}` and maps it onto `{u ≤ ρ'}`. -/
theorem exists_scale_eventually_closed_core_type_finite
    {N : Type} [mN : MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [pN : ProperSpace N]
    [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]
    {r : ℕ∞} (hr : 1 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (n : N) (gSeq : ∀ i, SmoothRiemannianMetric I (M i)) (hSeqNorm : ∀ i, IsMetricNorm (gSeq i))
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
    (V : (x : N) → TangentSpace I x) {A₂ : ℝ}
    (hVB : ∀ x, G.inner x (V x) (V x) ≤ 4)
    (hVdir : ∀ x, A₂ ≤ dist n x → ∀ v ∈ G.finiteMinimizingDirectionsTo {n} x,
      G.inner x (V x) v ≤ -(1 / 4))
    {u : N → ℝ} (hu : Continuous u) (hucpt : ∀ T, IsCompact {x | u x ≤ T}) {T₀ : ℝ}
    {Wu : Set N} (hWu : IsOpen Wu) (hWuT : {x | T₀ ≤ u x} ⊆ Wu)
    (huW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ u Wu)
    (hVW : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun x => (⟨x, V x⟩ : TangentBundle I N)) Wu)
    (huV : ∀ x, T₀ ≤ u x → 0 < mvfderiv (I := I) u x (V x)) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R → ∃ T₁ : ℝ, T₀ < T₁ ∧
      ∀ᶠ i in atTop, ∀ (η : M i → ℝ) (eη : ℝ), eη < 1 / 40 →
        (letI := (mM i).rescale R⁻¹ (inv_pos.mpr hR)
        (∀ x, |η x - dist (j i n) x| < eη) ∧
          LipschitzWith (1 / 64 : ℝ≥0) (fun x => η x - dist (j i n) x) ∧
          ∃ Wi : Set (M i), IsOpen Wi ∧
            (∀ x, 1 / 10 ≤ dist (j i n) x → dist (j i n) x ≤ 10 → x ∈ Wi) ∧
            ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η Wi) →
        ∀ ρ ∈ Icc (1 / 5 : ℝ) 2, ∀ ρ' ∈ Ioo T₀ T₁,
          ∃ Ψ : PartialDiffeomorph I I (M i) N ∞,
            {y | η y ≤ ρ} ⊆ Ψ.source ∧ Ψ '' {y | η y ≤ ρ} = {x | u x ≤ ρ'} := by
  -- the core `{u ≤ T₀}` is bounded
  obtain ⟨B₀, hB₀⟩ := (hucpt T₀).isBounded.subset_ball n
  have hmetricM : ∀ i a b, riemannianEDistOf (gSeq i) a b = ENNReal.ofReal (dist a b) :=
    fun i => riemannianEDistOf_eq_ofReal_dist (gSeq i) (hSeqNorm i)
  refine ⟨max (20 * |A₂| + 1) (20 * |B₀| + 1), lt_of_lt_of_le (by positivity) (le_max_left _ _),
    fun R hR hRR => ?_⟩
  have hRA : 20 * |A₂| + 1 ≤ R := (le_max_left _ _).trans hRR
  have hRB : 20 * |B₀| + 1 ≤ R := (le_max_right _ _).trans hRR
  have hRi : 0 < R⁻¹ := inv_pos.mpr hR
  have hA₂R : A₂ ≤ R / 20 := by linarith [le_abs_self A₂]
  have hB₀R : B₀ < R / 20 := by linarith [le_abs_self B₀]
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
  -- the closed T3 at the rescaled instances
  refine (fun hstep => ?_) (eventually_closed_core_of_pulled_core
    (mM := fun i => (mM i).rescale R⁻¹ hRi)
    (rbM := fun i => radialScaledBundle (gSeq i) R⁻¹ hRi)
    (rmM := fun i => radialScaledManifold (m := mM i) (gSeq i) (hmetricM i) R⁻¹ hRi)
    (cM := fun i => ((mM i).rescale_completeSpace_iff R⁻¹ hRi).mpr (hMc i))
    (crM := fun i => radialScaledContinuous (gSeq i) R⁻¹ hRi)
    (mN := mN.rescale R⁻¹ hRi) (pN := properSpace_rescale_of_properSpace mN R⁻¹ hRi pN)
    (fun i => scaleMetric (R⁻¹ ^ 2) (pow_pos hRi 2) (gSeq i))
    (fun i => isMetricNorm_of_riemannianBundle _) n j ?hsrc ?hdist ?hcov V
    (α := 1 / 8 * R⁻¹) (B := 4 * R⁻¹) (ε := (1 / 64 : ℝ≥0)) ?hεB ?hpair hu hucpt
    (T₀ := T₀) ?hT₀ hWu hWuT huW hVW huV)
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
  obtain ⟨T₁, hT₁, hfin⟩ := hstep
  refine ⟨T₁, hT₁, ?_⟩
  filter_upwards [hfin] with i hi η eη heη hηc ρ hρ ρ' hρ'
  exact hi η eη heη hηc.1 hηc.2.1 hηc.2.2 ρ hρ ρ' hρ'

/-- **LC38 closed, scale `R`, finite model in carrier coordinates (T4 + T5 closed).** For a finite
model with a smooth bundle diffeomorphism `D : TotalSpace F V ≃ N` and a field `W` as in
`exists_scale_eventually_open_ball_bundle_type_finite`: there is `R₀ > 0` such that for every
`R ≥ R₀` there is `T₁ > ℓ + 1` and a tail on which every radial function `η` of `(M_i, R⁻¹ d)`
with the bounds of T4 closed has, for every `ρ ∈ [1/5, 2]` and `ρ' ∈ (ℓ + 1, T₁)`, an ambient
partial diffeomorphism `M_i ⇀ N` carrying `{η ≤ ρ}` onto the disc core `{‖(D⁻¹ x).2‖ ≤ ρ'}`. -/
theorem exists_scale_eventually_closed_disc_core_type_finite
    {N : Type} [mN : MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [pN : ProperSpace N]
    [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]
    {r : ℕ∞} (hr : 1 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (n : N) (gSeq : ∀ i, SmoothRiemannianMetric I (M i)) (hSeqNorm : ∀ i, IsMetricNorm (gSeq i))
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
    {EB F : Type} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {HB : Type} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
    {B : Type} [TopologicalSpace B] [ChartedSpace HB B] [CompactSpace B]
    {Vb : B → Type} [TopologicalSpace (TotalSpace F Vb)]
    [∀ b, NormedAddCommGroup (Vb b)] [∀ b, InnerProductSpace ℝ (Vb b)]
    [FiberBundle F Vb] [VectorBundle ℝ F Vb] [IsContMDiffRiemannianBundle IB ∞ F Vb]
    (D : Diffeomorph (IB.prod 𝓘(ℝ, F)) I (TotalSpace F Vb) N ∞)
    (W : (x : N) → TangentSpace I x)
    (hW : ContMDiff I I.tangent ∞ (fun x => (⟨x, W x⟩ : TangentBundle I N)))
    {A₂ ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hWB : ∀ x, G.inner x (W x) (W x) ≤ 4)
    (hWdir : ∀ x, A₂ ≤ dist n x → ∀ v ∈ G.finiteMinimizingDirectionsTo {n} x,
      G.inner x (W x) v ≤ -(1 / 4))
    (hdu : ∀ y, ℓ < ‖(D.symm y).2‖ →
      mvfderiv (I := I) (fun y' => ‖(D.symm y').2‖) y (W y) = 1) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R → ∃ T₁ : ℝ, ℓ + 1 < T₁ ∧
      ∀ᶠ i in atTop, ∀ (η : M i → ℝ) (eη : ℝ), eη < 1 / 40 →
        (letI := (mM i).rescale R⁻¹ (inv_pos.mpr hR)
        (∀ x, |η x - dist (j i n) x| < eη) ∧
          LipschitzWith (1 / 64 : ℝ≥0) (fun x => η x - dist (j i n) x) ∧
          ∃ Wi : Set (M i), IsOpen Wi ∧
            (∀ x, 1 / 10 ≤ dist (j i n) x → dist (j i n) x ≤ 10 → x ∈ Wi) ∧
            ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η Wi) →
        ∀ ρ ∈ Icc (1 / 5 : ℝ) 2, ∀ ρ' ∈ Ioo (ℓ + 1) T₁,
          ∃ Ψ : PartialDiffeomorph I I (M i) N ∞,
            {y | η y ≤ ρ} ⊆ Ψ.source ∧ Ψ '' {y | η y ≤ ρ} = {x | ‖(D.symm x).2‖ ≤ ρ'} := by
  obtain ⟨hu, hucpt, -, huW, -⟩ := bundle_disc_core_data D
  set u : N → ℝ := fun y => ‖(D.symm y).2‖ with hudef
  have hWu : IsOpen {y : N | 0 < u y} := isOpen_lt continuous_const hu
  exact exists_scale_eventually_closed_core_type_finite hr G hGnorm n gSeq hSeqNorm j hexh hconv
    hdist hcover W hWB hWdir hu hucpt (T₀ := ℓ + 1) hWu (fun y hy => by
      have hy' : ℓ + 1 ≤ u y := hy
      change 0 < u y
      linarith) huW hW.contMDiffOn
    (fun y hy => by
      have hy' : ℓ + 1 ≤ u y := hy
      rw [hdu y (by linarith)]
      exact one_pos)

end DifferentialGeometry.Geometry.Collapse
