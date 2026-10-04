import DifferentialGeometry.Geometry.Collapse.EdgeSharedSmoothing
import DifferentialGeometry.Geometry.Collapse.EdgeBandGradient
set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem exists_shared_edge_smoothing_with_profiles (g : SmoothRiemannianMetric I M)
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
      (∀ x y, |(F x - infDist x A) - (F y - infDist y A)| ≤ ε * dist x y) ∧
      ∀ p ∈ P, (∀ x, |F x - infDist x A| < μ * (Δ * ρ p)) ∧
        (closedBall p (20 * (Δ * ρ p)) ∩ {x | 3 / 4 * (Δ * ρ p) ≤ infDist x A ∧
          infDist x A ≤ 21 / 2 * (Δ * ρ p)}) ⊆ O ∧
        (∀ x ∈ closedBall p (20 * (Δ * ρ p)) ∩ {x | 3 / 4 * (Δ * ρ p) ≤ infDist x A ∧
          infDist x A ≤ 21 / 2 * (Δ * ρ p)}, ∀ v ∈ minimizingDirectionsTo g hEnorm A x,
            Real.sqrt (g.inner x (gradFun g F x + v) (gradFun g F x + v)) < ε) ∧
        (∀ x ∈ closedBall p (20 * (Δ * ρ p)) ∩ {x | 3 / 4 * (Δ * ρ p) ≤ infDist x A ∧
          infDist x A ≤ 21 / 2 * (Δ * ρ p)},
          (∀ w : TangentSpace I x, mvfderiv I (fun y => F y / ρ y) x w =
            (ρ x)⁻¹ * mvfderiv I F x w - F x * (ρ x ^ 2)⁻¹ * mvfderiv I ρ x w) ∧
          Real.sqrt (g.inner x (ρ p • gradFun g (fun y => F y / ρ y) x - gradFun g F x)
            (ρ p • gradFun g (fun y => F y / ρ y) x - gradFun g F x)) ≤ 100 * Δ * Λ) ∧
        (∀ x ∈ ball p (20 * (Δ * ρ p)), infDist x A < 41 / 4 * (Δ * ρ p) →
          ContMDiffAt I 𝓘(ℝ, ℝ) ∞
            (fun y => Δ * DifferentialGeometry.Analysis.edgeSublevelProfile
              (F y / ρ y / Δ)) x) ∧
        (∀ s, 2 * Δ ≤ s → ∀ x,
          (Δ * DifferentialGeometry.Analysis.edgeSublevelProfile (F x / ρ x / Δ) ≤ s ↔
            F x / ρ x ≤ s)) ∧
        (∀ s, 2 * Δ < s → ∀ x,
          (Δ * DifferentialGeometry.Analysis.edgeSublevelProfile (F x / ρ x / Δ) = s ↔
            F x / ρ x = s)) ∧
        (∀ x ∈ ball p (100 * (Δ * ρ p)), 2 * Δ < F x / ρ x →
          (fun y => Δ * DifferentialGeometry.Analysis.edgeSublevelProfile
            (F y / ρ y / Δ)) =ᶠ[𝓝 x] fun y => F y / ρ y) := by
  obtain ⟨F, O, hO, hFO, hF0, hFL, hdiff, hcentres⟩ :=
    exists_shared_edge_smoothing g hEnorm hA hP hρpos hΔ hτ hτsmall hQp hdist hheight
      hcover hpA hborder hbordercover hκ hκΔ hsec hε (by linarith) hμ hμ1 hθ
  refine ⟨F, O, hO, hFO, hF0, hFL, hdiff, fun p hp => ?_⟩
  obtain ⟨hval, hCO, hgrad⟩ := hcentres p hp
  let r : ℝ := ρ p
  have hr : 0 < r := hρpos p
  let L : ℝ≥0 := ⟨(Λ : ℝ) / r, by positivity⟩
  have hρhat : LipschitzWith L (fun y => ρ y / r) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hr]
    calc |ρ y - ρ z| / r ≤ ((Λ : ℝ) * dist y z) / r :=
        div_le_div_of_nonneg_right (by simpa only [Real.dist_eq] using hρ.dist_le_mul y z) hr.le
      _ = (L : ℝ) * dist y z := by change _ = ((Λ : ℝ) / r) * dist y z; ring
  have hscale : 0 < Δ * r := mul_pos hΔ hr
  have hsmall : 100 * (Δ * r) * L ≤ 1 / 100 := by
    change 100 * (Δ * r) * ((Λ : ℝ) / r) ≤ 1 / 100
    convert hlam using 1
    field_simp
  have hsmooth : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => ρ y / r) (ball p (100 * (Δ * r))) :=
    (hρs.div_const r).contMDiffOn
  have hprof := edgeProfile_core_clauses (I := I) (F := F) (ρ := fun y => ρ y / r)
    (c := 3 / 4) hscale hO hFO
    (fun x hx hc hd => hCO
      ⟨(show dist x p ≤ 20 * (Δ * ρ p) from hx.le), hc, by linarith⟩)
    hval hFL.continuous hρhat
    (div_self hr.ne') hsmooth hsmall (by linarith)
  have hratio (y : M) : F y / (ρ y / r) = r * (F y / ρ y) := by
    rw [div_div_eq_mul_div]; ring
  have hprofile (y : M) :
      (Δ * r) * DifferentialGeometry.Analysis.edgeSublevelProfile
        (F y / (ρ y / r) / (Δ * r)) =
      r * (Δ * DifferentialGeometry.Analysis.edgeSublevelProfile (F y / ρ y / Δ)) := by
    rw [hratio, mul_comm Δ r, mul_div_mul_left _ _ hr.ne']
    ring
  obtain ⟨hsm, hle, heq, hnear⟩ := hprof
  refine ⟨hval, hCO, hgrad, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hFx : MDifferentiableAt I 𝓘(ℝ, ℝ) F x :=
      (hFO.contMDiffAt (hO.mem_nhds (hCO hx))).mdifferentiableAt (by simp)
    have hρx : MDifferentiableAt I 𝓘(ℝ, ℝ) ρ x :=
      (hρs.contMDiffAt (x := x)).mdifferentiableAt (by simp)
    refine ⟨fun w => mvfderiv_div_apply hFx hρx (hρpos x).ne' w, ?_⟩
    have hηx := hFx.div hρx (hρpos x).ne'
    have hhat : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => ρ y / r) x :=
      ((hρs.div_const r).contMDiffAt (x := x)).mdifferentiableAt (by simp)
    have herr := edgeQuotient_gradient_error g hEnorm hscale hε.le hε1 hμ1 hFL
      (hval x).le hFx hρhat (div_self hr.ne') hhat hsmall hx.1 hx.2.2
    have heq : (fun y => F y / (ρ y / r)) = r • (fun y => F y / ρ y) := by
      funext y
      exact hratio y
    have hgr := gradientFun_const_smul g r hηx
    change gradientFun g (r • (fun y => F y / ρ y)) x =
      r • gradientFun g (fun y => F y / ρ y) x at hgr
    rw [← heq] at hgr
    change gradFun g (fun y => F y / (ρ y / r)) x =
      r • gradFun g (fun y => F y / ρ y) x at hgr
    rw [hgr, norm_tangent_eq_sqrt_gInner hEnorm] at herr
    have he : 100 * (Δ * r) * (L : ℝ) = 100 * Δ * Λ := by
      change 100 * (Δ * r) * ((Λ : ℝ) / r) = _
      field_simp
    rwa [he] at herr
  · intro x hx hd
    have h := hsm x hx hd
    simp_rw [hprofile] at h
    have hh := (contMDiffAt_const (c := r⁻¹)).mul h
    change ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y => r⁻¹ * (r * (Δ * DifferentialGeometry.Analysis.edgeSublevelProfile
        (F y / ρ y / Δ)))) x at hh
    simpa only [← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul] using hh
  · intro s hs x
    have h := hle (r * s) (by nlinarith) x
    rw [hprofile, hratio, mul_le_mul_iff_right₀ hr, mul_le_mul_iff_right₀ hr] at h
    exact h
  · intro s hs x
    have h := heq (r * s) (by nlinarith) x
    rw [hprofile, hratio, mul_right_inj' hr.ne', mul_right_inj' hr.ne'] at h
    exact h
  · intro x hx hη
    have h := hnear x hx (by rw [hratio]; nlinarith)
    filter_upwards [h] with y hy
    rw [hprofile, hratio] at hy
    exact (mul_left_cancel₀ hr.ne' hy)

end DifferentialGeometry.Geometry.Collapse
