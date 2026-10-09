import DifferentialGeometry.Geometry.Collapse.EdgeSharedProfiles
import DifferentialGeometry.Geometry.Collapse.EdgeFullCollarFamily

/-!
# LFR33: every normalization of the shared smoothing satisfies LFR27

Blueprint 207A, LFR33 (`cor:collapse-finite-edge-family-shared-smoothing`, A:27771–27830), last
paragraph of the proof: "In the normalization at `p_i`, put `F_i = F/ρ_i` and `ρ̂_i = ρ/ρ_i` ...
Hence each normalization satisfies LFR27, including the full quotient derivative and smooth
constant core."

Codex X91's `exists_shared_edge_smoothing_with_profiles` gives the per-centre clauses of ONE shared
smoothing `F` in PHYSICAL units (scale `Δρ(p)`, physical metric `g`). Here they are transported to the
normalization `(M, ρ(p)⁻¹ d, ρ(p)⁻² g)` of each centre (the instances `m.rescale ρ(p)⁻¹`,
`radialScaledBundle`, `radialScaledContinuous`, `radialScaledManifold` of F7-EDGE's
`exists_edge_full_collar_family`), with `F_p = F/ρ(p)` and `ρ̂ = ρ/ρ(p)`: the conclusion clauses of
LFR27 (`exists_edge_scaled_smoothing`) hold verbatim at scale `Δ`, for the SAME `η = F_p/ρ̂ = F/ρ` and
the SAME `H = Δψ(η/Δ)` (`exists_shared_edge_smoothing_normalized`). New transport:
`radialScaled_quotient_clause` (the quotient clause `‖ρ(p)∇η - ∇F‖_g ≤ c` is the normalized
`‖∇_{g_p}η - ∇_{g_p}F_p‖_{g_p} ≤ c`), `radialScaled_profile_collar_subset` (LFR27's collar `C`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Topology
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- LFR27's smoothing collar `C` at physical scale `ΔR` is the collar `C` at scale `Δ` of the
normalized distance. -/
theorem radialScaled_profile_collar_subset {X : Type*} [m : MetricSpace X] {A O : Set X} {p : X}
    {Δ R : ℝ} (hR : 0 < R)
    (hCO : closedBall p (20 * (Δ * R)) ∩ {x | 3 / 4 * (Δ * R) ≤ infDist x A ∧
      infDist x A ≤ 21 / 2 * (Δ * R)} ⊆ O) :
    letI := m.rescale R⁻¹ (inv_pos.mpr hR)
    closedBall p (20 * Δ) ∩ {y | 3 / 4 * Δ ≤ infDist y A ∧ infDist y A ≤ 21 / 2 * Δ} ⊆ O := by
  intro y hy
  obtain ⟨hy1, hy2, hy3⟩ := hy
  have hd : R⁻¹ * dist y p ≤ 20 * Δ := hy1
  rw [infDist_rescale] at hy2 hy3
  apply hCO
  refine ⟨?_, ?_, ?_⟩
  · change dist y p ≤ 20 * (Δ * R)
    rw [← div_eq_inv_mul, div_le_iff₀ hR] at hd
    linarith
  · rw [← div_eq_inv_mul, le_div_iff₀ hR] at hy2
    linarith
  · rw [← div_eq_inv_mul, div_le_iff₀ hR] at hy3
    linarith

/-- The quotient clause transported to the normalization at scale `R`: in the metric
`R⁻² g`, `∇((F/R)/(ρ/R)) - ∇(F/R) = R (R∇(F/ρ) - ∇F)`, of the same length as `R∇(F/ρ) - ∇F` in `g`. -/
theorem radialScaled_quotient_clause {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) {R : ℝ} (hR : 0 < R)
    {F ρ : M → ℝ} {x : M} {c : ℝ} (hF : MDifferentiableAt I 𝓘(ℝ, ℝ) F x)
    (hquot : Real.sqrt (g.inner x (R • gradFun g (fun y => F y / ρ y) x - gradFun g F x)
      (R • gradFun g (fun y => F y / ρ y) x - gradFun g F x)) ≤ c) :
    let gR : SmoothRiemannianMetric I M := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
    Real.sqrt (gR.inner x (gradFun gR (fun y => F y / R / (ρ y / R)) x -
        gradFun gR (fun y => F y / R) x)
      (gradFun gR (fun y => F y / R / (ρ y / R)) x - gradFun gR (fun y => F y / R) x)) ≤ c := by
  intro gR
  have hRi : 0 < R⁻¹ := inv_pos.mpr hR
  have hη : (fun y => F y / R / (ρ y / R)) = fun y => F y / ρ y := by
    funext y
    exact div_div_div_cancel_right₀ hR.ne' (F y) (ρ y)
  have he : (fun z => F z / R) = R⁻¹ • F := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  have hgr := gradientFun_const_smul g R⁻¹ hF
  rw [← he] at hgr
  change gradFun g (fun z => F z / R) x = R⁻¹ • gradFun g F x at hgr
  have hsc : ∀ f : M → ℝ, gradFun gR f x = R ^ 2 • gradFun g f x := by
    intro f
    change gradientFun (scaleMetric (R⁻¹ ^ 2) (pow_pos hRi 2) g) f x = _
    rw [gradientFun_scale]
    change (R⁻¹ ^ 2)⁻¹ • gradFun g f x = _
    congr 1
    field_simp
  have hsplit : gradFun gR (fun y => F y / R / (ρ y / R)) x - gradFun gR (fun y => F y / R) x =
      R • (R • gradFun g (fun y => F y / ρ y) x - gradFun g F x) := by
    rw [hη, hsc, hsc, hgr, smul_smul, smul_sub, smul_smul,
      show R ^ 2 * R⁻¹ = R by field_simp, show R ^ 2 = R * R by ring]
  have hval : ∀ w : TangentSpace I x, gR.inner x (R • w) (R • w) = g.inner x w w := by
    intro w
    change (scaleMetric (R⁻¹ ^ 2) (pow_pos hRi 2) g).inner x _ _ = _
    rw [scaleMetric_inner, map_smul, map_smul, smul_apply, smul_eq_mul,
      smul_eq_mul]
    field_simp
  rw [hsplit, hval]
  exact hquot

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [hM : CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **LFR33: every normalization of the shared smoothing satisfies LFR27.** Under the hypotheses of
X91's `exists_shared_edge_smoothing_with_profiles` there is ONE nonnegative `(1+ε)`-Lipschitz `F`,
smooth on an open `O`, such that at every centre `p`, in the normalization
`(M, ρ(p)⁻¹ d, ρ(p)⁻² g)` with `F_p = F/ρ(p)` and `ρ̂ = ρ/ρ(p)` (`ρ̂(p) = 1`, `Λ`-Lipschitz), all
conclusion clauses of LFR27 hold at scale `Δ`: `C ⊆ O`, `|F_p - d_A| < μΔ`, `Lip(F_p - d_A) ≤ ε`,
the nearest-direction gradient clause on `C`, the quotient clause on `C`, and the constant-core
clauses of `H = Δψ(η/Δ)` for `η = F_p/ρ̂` (`= F/ρ`, the same at every centre). -/
theorem exists_shared_edge_smoothing_normalized (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g)
    {A : Set M} (hA : IsClosed A) {P : Finset M} (hP : P.Nonempty)
    {Q : M → M → WithLp 2 (ℝ × ℝ)} {ρ : M → ℝ} (hρpos : ∀ x, 0 < ρ x) {Δ τ κ ε μ : ℝ}
    (hΔ : 0 < Δ) (hτ : 0 < τ) (hτsmall : τ < 1 / 10000)
    (hQp : ∀ p ∈ P, Q p p = 0)
    (hdist : ∀ p ∈ P, ∀ x ∈ ball p (200 * (Δ * ρ p)), ∀ y ∈ ball p (200 * (Δ * ρ p)),
      |dist (Q p x) (Q p y) - dist x y| ≤ τ * (Δ * ρ p))
    (hheight : ∀ p ∈ P, ∀ x ∈ ball p (200 * (Δ * ρ p)), 0 ≤ (Q p x).snd)
    (hcover : ∀ p ∈ P, ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * (Δ * ρ p) →
      z.snd ∈ Icc 0 (100 * (Δ * ρ p)) →
        ∃ x ∈ ball p (200 * (Δ * ρ p)), dist (Q p x) z ≤ τ * (Δ * ρ p))
    (hpA : ∀ p ∈ P, p ∈ A)
    (hborder : ∀ p ∈ P, ∀ a ∈ A ∩ ball p (190 * (Δ * ρ p)), (Q p a).snd ≤ τ * (Δ * ρ p))
    (hbordercover : ∀ p ∈ P, ∀ t : ℝ, |t| ≤ 100 * (Δ * ρ p) →
      ∃ a ∈ A ∩ ball p (190 * (Δ * ρ p)),
        dist (Q p a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * (Δ * ρ p))
    (hκ : 0 ≤ κ) (hκΔ : ∀ p ∈ P, κ * (Δ * ρ p) ≤ 1 / 100)
    (hsec : ∀ p ∈ P, ∀ z ∈ ball p (1000 * (Δ * ρ p)), SectionalBoundedBelowAt g z (-κ ^ 2))
    (hε : 0 < ε) (hε1 : ε < 1 / 100) (hμ : 0 < μ) (hμ1 : μ < 1 / 100)
    (hθ : 30 * Real.sqrt τ < ε ^ 2 / 20)
    {Λ : ℝ≥0} (hρ : LipschitzWith Λ ρ)
    (hρs : ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ) (hlam : 100 * Δ * Λ ≤ 1 / 100) :
    ∃ F : M → ℝ, ∃ O : Set M, IsOpen O ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O ∧ (∀ x, 0 ≤ F x) ∧
      LipschitzWith (Real.toNNReal (1 + ε)) F ∧
      ∀ p ∈ P,
        (have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
        letI := m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
        letI := radialScaledBundle g (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
        letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
          radialScaledContinuous g (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
        letI : IsRiemannianManifold I M :=
          radialScaledManifold (m := m) g hmetric (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
        letI : CompleteSpace M :=
          (m.rescale_completeSpace_iff (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).mpr hM
        let gR : SmoothRiemannianMetric I M :=
          scaleMetric ((ρ p)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρpos p)) 2) g
        have hnR : IsMetricNorm (I := I) (M := M) gR := isMetricNorm_of_riemannianBundle gR
        let C : Set M := closedBall p (20 * Δ) ∩
          {x | 3 / 4 * Δ ≤ infDist x A ∧ infDist x A ≤ 21 / 2 * Δ}
        C ⊆ O ∧ ρ p / ρ p = 1 ∧ LipschitzWith Λ (fun y => ρ y / ρ p) ∧
        LipschitzWith (Real.toNNReal (1 + ε)) (fun y => F y / ρ p) ∧
        (∀ x, |F x / ρ p - infDist x A| < μ * Δ) ∧
        (∀ x y, |(F x / ρ p - infDist x A) - (F y / ρ p - infDist y A)| ≤ ε * dist x y) ∧
        (∀ x ∈ C, ∀ v ∈ minimizingDirectionsTo gR hnR A x,
          Real.sqrt (gR.inner x (gradFun gR (fun y => F y / ρ p) x + v)
            (gradFun gR (fun y => F y / ρ p) x + v)) < ε) ∧
        (∀ x ∈ C, Real.sqrt (gR.inner x
          (gradFun gR (fun y => F y / ρ p / (ρ y / ρ p)) x - gradFun gR (fun y => F y / ρ p) x)
          (gradFun gR (fun y => F y / ρ p / (ρ y / ρ p)) x - gradFun gR (fun y => F y / ρ p) x))
            ≤ 100 * Δ * Λ) ∧
        (∀ x ∈ ball p (20 * Δ), infDist x A < 41 / 4 * Δ →
          ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => Δ * DifferentialGeometry.Analysis.edgeSublevelProfile
            (F y / ρ p / (ρ y / ρ p) / Δ)) x) ∧
        (∀ s, 2 * Δ ≤ s → ∀ x,
          (Δ * DifferentialGeometry.Analysis.edgeSublevelProfile (F x / ρ p / (ρ x / ρ p) / Δ) ≤ s ↔
            F x / ρ p / (ρ x / ρ p) ≤ s)) ∧
        (∀ s, 2 * Δ < s → ∀ x,
          (Δ * DifferentialGeometry.Analysis.edgeSublevelProfile (F x / ρ p / (ρ x / ρ p) / Δ) = s ↔
            F x / ρ p / (ρ x / ρ p) = s)) ∧
        ∀ x ∈ ball p (100 * Δ), 2 * Δ < F x / ρ p / (ρ x / ρ p) →
          (fun y => Δ * DifferentialGeometry.Analysis.edgeSublevelProfile
            (F y / ρ p / (ρ y / ρ p) / Δ)) =ᶠ[𝓝 x] fun y => F y / ρ p / (ρ y / ρ p)) := by
  obtain ⟨F, O, hO, hFO, hF0, hFL, hdiff, hcentres⟩ :=
    exists_shared_edge_smoothing_with_profiles g hEnorm hA hP hρpos hΔ hτ hτsmall hQp hdist
      hheight hcover hpA hborder hbordercover hκ hκΔ hsec hε hε1 hμ hμ1 hθ hρ hρs hlam
  refine ⟨F, O, hO, hFO, hF0, hFL, fun p hp => ?_⟩
  obtain ⟨hval, hCO, hgrad, hquot, hcore, hsub, hlev, hev⟩ := hcentres p hp
  have hr : 0 < ρ p := hρpos p
  have hri : 0 < (ρ p)⁻¹ := inv_pos.mpr hr
  have hη : ∀ y, F y / ρ p / (ρ y / ρ p) = F y / ρ y := fun y =>
    div_div_div_cancel_right₀ hr.ne' (F y) (ρ y)
  have hηf : (fun y => F y / ρ p / (ρ y / ρ p)) = fun y => F y / ρ y := funext hη
  have hCOR := radialScaled_profile_collar_subset hr hCO
  have hFLR := radialScaled_div_lipschitzWith hFL hr
  have hρR := lipschitzWith_normalized_scale hρ hr
  have hCC := radialScaled_profile_collar_subset (A := A) (p := p) (Δ := Δ)
    (O := closedBall p (20 * (Δ * ρ p)) ∩ {x | 3 / 4 * (Δ * ρ p) ≤ infDist x A ∧
      infDist x A ≤ 21 / 2 * (Δ * ρ p)}) hr subset_rfl
  have hFd : ∀ y ∈ closedBall p (20 * (Δ * ρ p)) ∩ {x | 3 / 4 * (Δ * ρ p) ≤ infDist x A ∧
      infDist x A ≤ 21 / 2 * (Δ * ρ p)}, MDifferentiableAt I 𝓘(ℝ, ℝ) F y :=
    fun y hy => (hFO.contMDiffAt (hO.mem_nhds (hCO hy))).mdifferentiableAt (by simp)
  have hgradR (y : M) (hy : y ∈ closedBall p (20 * (Δ * ρ p)) ∩ {x | 3 / 4 * (Δ * ρ p) ≤
      infDist x A ∧ infDist x A ≤ 21 / 2 * (Δ * ρ p)}) :=
    radialScaled_low_collar_gradient g hEnorm hr (hFd y hy) (hgrad y hy)
  intro hmetric
  let mR : MetricSpace M := m.rescale (ρ p)⁻¹ hri
  let _ : CompleteSpace M := (m.rescale_completeSpace_iff (ρ p)⁻¹ hri).mpr hM
  let _ := radialScaledBundle g (ρ p)⁻¹ hri
  let _ := radialScaledContinuous g (ρ p)⁻¹ hri
  let _ := radialScaledManifold (m := m) g hmetric (ρ p)⁻¹ hri
  intro gR hnR C
  -- the normalized distances
  have hdR : ∀ x y : M, dist x y = (ρ p)⁻¹ * @dist M m.toDist x y := fun _ _ => rfl
  have hinfR : ∀ x : M, infDist x A = (ρ p)⁻¹ * @infDist M m.toPseudoMetricSpace x A :=
    fun x => infDist_rescale m (ρ p)⁻¹ hri x A
  have hball : ∀ x r, x ∈ ball p r → @dist M m.toDist x p < r * ρ p := by
    intro x r hx
    have h : (ρ p)⁻¹ * @dist M m.toDist x p < r := hx
    rw [← div_eq_inv_mul, div_lt_iff₀ hr] at h
    exact h
  refine ⟨hCOR, div_self hr.ne', hρR, hFLR, ?_, ?_, fun x hx => hgradR x (hCC hx), ?_, ?_, ?_, ?_,
    ?_⟩
  · -- the value clause
    intro x
    rw [hinfR, div_eq_inv_mul, ← mul_sub, abs_mul, abs_of_pos hri, ← div_eq_inv_mul,
      div_lt_iff₀ hr]
    have h := hval x
    linarith
  · -- the Lipschitz-difference clause
    intro x y
    rw [hinfR, hinfR, hdR, div_eq_inv_mul, div_eq_inv_mul, ← mul_sub, ← mul_sub, ← mul_sub,
      abs_mul, abs_of_pos hri]
    have h := hdiff x y
    calc (ρ p)⁻¹ * |(F x - @infDist M m.toPseudoMetricSpace x A) -
          (F y - @infDist M m.toPseudoMetricSpace y A)| ≤
        (ρ p)⁻¹ * (ε * @dist M m.toDist x y) := mul_le_mul_of_nonneg_left h hri.le
      _ = ε * ((ρ p)⁻¹ * @dist M m.toDist x y) := by ring
  · -- the quotient clause
    intro x hx
    have hxC := hCC hx
    obtain ⟨-, hq⟩ := hquot x hxC
    exact radialScaled_quotient_clause g hr (hFd x hxC) hq
  · -- the smooth constant core
    intro x hx hxA
    simp only [hη]
    apply hcore x
    · change @dist M m.toDist x p < 20 * (Δ * ρ p)
      have := hball x (20 * Δ) hx
      linarith
    · rw [hinfR, ← div_eq_inv_mul, div_lt_iff₀ hr] at hxA
      linarith
  · intro s hs x
    rw [hη]
    exact hsub s hs x
  · intro s hs x
    rw [hη]
    exact hlev s hs x
  · intro x hx hx2
    have hfun : (fun y => Δ * DifferentialGeometry.Analysis.edgeSublevelProfile
        (F y / ρ p / (ρ y / ρ p) / Δ)) =
        fun y => Δ * DifferentialGeometry.Analysis.edgeSublevelProfile (F y / ρ y / Δ) := by
      funext y
      rw [hη]
    rw [hfun, hηf]
    rw [hη] at hx2
    apply hev x ?_ hx2
    change @dist M m.toDist x p < 100 * (Δ * ρ p)
    have := hball x (100 * Δ) hx
    linarith

end DifferentialGeometry.Geometry.Collapse
