import DifferentialGeometry.Geometry.Collapse.EdgeScaledSmoothing

/-!
# LFR38, finite family: ONE smoothing down to the full collar at every centre

Blueprint 207A, LFR38 (A:28304–28315): "For the finite family, replace each `U_i, C_i` in LFR33 by
the physical rescalings of `U⁺, C⁺`. Apply LFR02 ONCE to the compact union, with value tolerance
smaller than `μΔ min_i ρ(p_i)` and the common Lipschitz-difference tolerance. The same rescaling
calculation gives LFR34 at every center ... These stronger smoothness conclusions also include
LFR27's entire displayed output." In physical units, for finitely many centres `p ∈ P`, each with a
coarse-border chart for the SAME closed set `A` at its own scale `Δρ(p)` and the NORMALIZED
curvature bound `sec ≥ -(κ/ρ(p))²` on `B(p, 1000Δρ(p))` with `κΔ ≤ 1/100`:

* `exists_shared_low_collar_smoothing`: one nonnegative `(1+ε)`-Lipschitz `F` with
  `|F - d_A| < μΔρ(p)`, smooth near every `C⁺_p = B̄(p, 20Δρ(p)) ∩ {Δρ(p)/25 ≤ d_A ≤ 10.5Δρ(p)}`,
  with `‖∇F + v‖ < ε` for every nearest direction there (LFR34 at every centre, threshold
  `140√τ < ε²/20`), and LFR27's profile clauses for `H = Δψ(F/(ρΔ))` at every centre.
-/

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

/-- **LFR38, finite family, smoothing.** See the module docstring. -/
theorem exists_shared_low_collar_smoothing (g : SmoothRiemannianMetric I M)
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
    (hκ : 0 ≤ κ) (hκΔ : κ * Δ ≤ 1 / 100)
    (hsec : ∀ p ∈ P, ∀ z ∈ ball p (1000 * (Δ * ρ p)),
      SectionalBoundedBelowAt g z (-(κ / ρ p) ^ 2))
    (hε : 0 < ε) (hε1 : ε < 1 / 100) (hμ : 0 < μ) (hμ1 : μ < 1 / 1000)
    (hθ : 140 * Real.sqrt τ < ε ^ 2 / 20)
    {Λ : ℝ≥0} (hρ : LipschitzWith Λ ρ)
    (hρs : ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ) (hlam : 100 * Δ * Λ ≤ 1 / 100) :
    ∃ F : M → ℝ, ∃ O : Set M, IsOpen O ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O ∧ (∀ x, 0 ≤ F x) ∧
      LipschitzWith (Real.toNNReal (1 + ε)) F ∧
      (∀ x y, |(F x - infDist x A) - (F y - infDist y A)| ≤ ε * dist x y) ∧
      ∀ p ∈ P, (∀ x, |F x - infDist x A| < μ * (Δ * ρ p)) ∧
        (closedBall p (20 * (Δ * ρ p)) ∩ {x | Δ * ρ p / 25 ≤ infDist x A ∧
          infDist x A ≤ 21 / 2 * (Δ * ρ p)}) ⊆ O ∧
        (∀ x ∈ closedBall p (20 * (Δ * ρ p)) ∩ {x | Δ * ρ p / 25 ≤ infDist x A ∧
          infDist x A ≤ 21 / 2 * (Δ * ρ p)}, ∀ v ∈ minimizingDirectionsTo g hEnorm A x,
            Real.sqrt (g.inner x (gradFun g F x + v) (gradFun g F x + v)) < ε) ∧
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
  let Up : M → Set M := fun p => ball p (30 * (Δ * ρ p)) ∩
    {x | Δ * ρ p / 50 < infDist x A ∧ infDist x A < 12 * (Δ * ρ p)}
  let Cp : M → Set M := fun p => closedBall p (20 * (Δ * ρ p)) ∩
    {x | Δ * ρ p / 25 ≤ infDist x A ∧ infDist x A ≤ 21 / 2 * (Δ * ρ p)}
  let U : Set M := ⋃ p ∈ P, Up p
  let C : Set M := ⋃ p ∈ P, Cp p
  have hscale (p : M) : 0 < Δ * ρ p := mul_pos hΔ (hρpos p)
  have hU : IsOpen U := isOpen_biUnion fun p _ => isOpen_ball.inter
    ((isOpen_lt continuous_const (continuous_infDist_pt A)).inter
      (isOpen_lt (continuous_infDist_pt A) continuous_const))
  have hC : IsCompact C := P.isCompact_biUnion fun p _ =>
    (soul_isCompact_closedBall (I := I) g hEnorm p _).inter_right
      ((isClosed_le continuous_const (continuous_infDist_pt A)).inter
        (isClosed_le (continuous_infDist_pt A) continuous_const))
  have hCpU (p : M) (hp : p ∈ P) : Cp p ⊆ U := fun x hx =>
    mem_biUnion hp ⟨(show dist x p < 30 * (Δ * ρ p) by
      have : dist x p ≤ 20 * (Δ * ρ p) := hx.1
      linarith [hscale p]), by linarith [hx.2.1, hscale p], by linarith [hx.2.2, hscale p]⟩
  have hCU : C ⊆ U := iUnion₂_subset fun p hp => hCpU p hp
  have hUd : ∀ x ∈ U, ∃ p ∈ P, x ∈ Up p := fun x hx => by
    simpa only [U, mem_iUnion, exists_prop] using hx
  have hUA : U ⊆ Aᶜ := fun x hx hxA => by
    obtain ⟨p, -, hxp⟩ := hUd x hx
    have := hxp.2.1
    rw [infDist_zero_of_mem hxA] at this
    linarith [hscale p]
  have hsq : 2 * Real.sqrt (4600 * τ) < 140 * Real.sqrt τ := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4600)]
    have h4600 : Real.sqrt 4600 < 70 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    have hτs : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
    nlinarith
  have hdiam : ∀ q ∈ U, ∀ v ∈ minimizingDirectionsTo g hEnorm A q,
      ∀ v' ∈ minimizingDirectionsTo g hEnorm A q,
        Real.sqrt (g.inner q (v - v') (v - v')) ≤ 2 * Real.sqrt (4600 * τ) := fun q hq => by
    obtain ⟨p, hp, hqp⟩ := hUd q hq
    have hκp : 0 ≤ κ / ρ p := div_nonneg hκ (hρpos p).le
    have hκpΔ : κ / ρ p * (Δ * ρ p) ≤ 1 / 100 := by
      have he : κ / ρ p * (Δ * ρ p) = κ * Δ := by field_simp [(hρpos p).ne']
      rw [he]
      exact hκΔ
    exact (coarseBorder_nearest_directions_low g hEnorm (hscale p) hτ hτsmall (hQp p hp)
      (hdist p hp) (hheight p hp) (hcover p hp) (hpA p hp) (hborder p hp) (hbordercover p hp)
      hκp hκpΔ (hsec p hp) hqp.1 (by linarith [hqp.2.1]) hqp.2.2.le).2.1
  set m := P.inf' hP ρ with hm_def
  have hm : 0 < m := (Finset.lt_inf'_iff hP).mpr fun p _ => hρpos p
  have hmle (p : M) (hp : p ∈ P) : m ≤ ρ p := Finset.inf'_le ρ hp
  obtain ⟨F, O, hO, hCO, hFO, hclose, hout, hdiff, hlip, hgrad⟩ :=
    exists_distance_smoothing_with_gradient g hEnorm hε (by linarith) hA
      ⟨_, hpA _ hP.choose_spec⟩ hU hUA hdiam (hsq.trans hθ) hC hCU (mul_pos hμ (mul_pos hΔ hm))
  have hval (p : M) (hp : p ∈ P) (x : M) : |F x - infDist x A| < μ * (Δ * ρ p) :=
    (hclose x).trans_le (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hmle p hp) hΔ.le) hμ.le)
  refine ⟨F, O, hO, hFO, fun x => ?_, hlip, hdiff, fun p hp => ?_⟩
  · by_cases hxU : x ∈ U
    · obtain ⟨p, hp, hxp⟩ := hUd x hxU
      have h1 := (abs_lt.mp (hval p hp x)).1
      have h2 := hxp.2.1
      nlinarith [hscale p]
    · rw [hout x hxU]
      exact infDist_nonneg
  have hCO' : Cp p ⊆ O := fun x hx => hCO (mem_biUnion hp hx)
  -- LFR27's profile clauses at the centre, in its normalization of the scale
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
  have hsmall : 100 * (Δ * r) * L ≤ 1 / 100 := by
    change 100 * (Δ * r) * ((Λ : ℝ) / r) ≤ 1 / 100
    convert hlam using 1
    field_simp
  have hsmooth : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => ρ y / r) (ball p (100 * (Δ * r))) :=
    (hρs.div_const r).contMDiffOn
  have hprof := edgeProfile_core_clauses (I := I) (F := F) (ρ := fun y => ρ y / r)
    (c := 1 / 25) (mul_pos hΔ hr) hO hFO
    (fun x hx hc hd => hCO'
      ⟨(show dist x p ≤ 20 * (Δ * ρ p) from hx.le), by linarith, by linarith⟩)
    (hval p hp) hlip.continuous hρhat (div_self hr.ne') hsmooth hsmall (by linarith)
  have hratio (y : M) : F y / (ρ y / r) = r * (F y / ρ y) := by
    rw [div_div_eq_mul_div]; ring
  have hprofile (y : M) :
      (Δ * r) * DifferentialGeometry.Analysis.edgeSublevelProfile
        (F y / (ρ y / r) / (Δ * r)) =
      r * (Δ * DifferentialGeometry.Analysis.edgeSublevelProfile (F y / ρ y / Δ)) := by
    rw [hratio, mul_comm Δ r, mul_div_mul_left _ _ hr.ne']
    ring
  obtain ⟨hsm, hle, heq, hnear⟩ := hprof
  refine ⟨hval p hp, hCO', fun x hx v hv => hgrad x (mem_biUnion hp hx) v hv, ?_, ?_, ?_, ?_⟩
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
