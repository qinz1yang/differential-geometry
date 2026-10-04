import DifferentialGeometry.Geometry.Collapse.EdgeScaledSmoothing

/-!
# LFR33 (smoothing half): a finite verified edge family shares one distance function

Blueprint 207A, LFR33 (`cor:collapse-finite-edge-family-shared-smoothing`, A:27771–27855). For finitely many
centers `p ∈ P`, each with a coarse-border chart for the SAME closed set `A` at its own physical scale
`Δ ρ(p)` (LFR25.1 with `Δ` replaced by `Δ ρ(p)`, as LFR32 supplies for `A = closure E'`) and the LFR25
curvature hypothesis at that scale, ONE application of LC28 (in the physical metric, on the union of the
smoothing regions, with value error below all the finitely many tolerances) gives a single nonnegative
Lipschitz `F` which, at every center, has the LFR27 value, Lipschitz-difference, smoothness and
nearest-direction gradient clauses on that center's collar. Separate smoothings and their compatibility are
not needed. The proper disk bundles of LFR28 at each center are NOT claimed (LFR28 is blocked).
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

/-- **LFR33**, smoothing half, in physical units. -/
theorem exists_shared_edge_smoothing (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {A : Set M} (hA : IsClosed A) {P : Finset M} (hP : P.Nonempty)
    {Q : M → M → WithLp 2 (ℝ × ℝ)} {ρ : M → ℝ} (hρpos : ∀ x, 0 < ρ x) {Δ τ κ ε μ : ℝ}
    (hΔ : 0 < Δ) (hτ : 0 < τ) (hτsmall : τ < 1 / 10000)
    (hQp : ∀ p ∈ P, Q p p = 0)
    (hdist : ∀ p ∈ P, ∀ x ∈ ball p (200 * (Δ * ρ p)), ∀ y ∈ ball p (200 * (Δ * ρ p)),
      |dist (Q p x) (Q p y) - dist x y| ≤ τ * (Δ * ρ p))
    (hheight : ∀ p ∈ P, ∀ x ∈ ball p (200 * (Δ * ρ p)), 0 ≤ (Q p x).snd)
    (hcover : ∀ p ∈ P, ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * (Δ * ρ p) →
      z.snd ∈ Icc 0 (100 * (Δ * ρ p)) → ∃ x ∈ ball p (200 * (Δ * ρ p)), dist (Q p x) z ≤ τ * (Δ * ρ p))
    (hpA : ∀ p ∈ P, p ∈ A)
    (hborder : ∀ p ∈ P, ∀ a ∈ A ∩ ball p (190 * (Δ * ρ p)), (Q p a).snd ≤ τ * (Δ * ρ p))
    (hbordercover : ∀ p ∈ P, ∀ t : ℝ, |t| ≤ 100 * (Δ * ρ p) →
      ∃ a ∈ A ∩ ball p (190 * (Δ * ρ p)),
        dist (Q p a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * (Δ * ρ p))
    (hκ : 0 ≤ κ) (hκΔ : ∀ p ∈ P, κ * (Δ * ρ p) ≤ 1 / 100)
    (hsec : ∀ p ∈ P, ∀ z ∈ ball p (1000 * (Δ * ρ p)), SectionalBoundedBelowAt g z (-κ ^ 2))
    (hε : 0 < ε) (hε1 : ε < 1) (hμ : 0 < μ) (hμ1 : μ < 1 / 100)
    (hθ : 30 * Real.sqrt τ < ε ^ 2 / 20) :
    ∃ F : M → ℝ, ∃ O : Set M, IsOpen O ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O ∧ (∀ x, 0 ≤ F x) ∧
      LipschitzWith (Real.toNNReal (1 + ε)) F ∧
      (∀ x y, |(F x - infDist x A) - (F y - infDist y A)| ≤ ε * dist x y) ∧
      ∀ p ∈ P, (∀ x, |F x - infDist x A| < μ * (Δ * ρ p)) ∧
        (closedBall p (20 * (Δ * ρ p)) ∩ {x | 3 / 4 * (Δ * ρ p) ≤ infDist x A ∧
          infDist x A ≤ 21 / 2 * (Δ * ρ p)}) ⊆ O ∧
        ∀ x ∈ closedBall p (20 * (Δ * ρ p)) ∩ {x | 3 / 4 * (Δ * ρ p) ≤ infDist x A ∧
          infDist x A ≤ 21 / 2 * (Δ * ρ p)}, ∀ v ∈ minimizingDirectionsTo g hEnorm A x,
            Real.sqrt (g.inner x (gradFun g F x + v) (gradFun g F x + v)) < ε := by
  let Up : M → Set M := fun p => ball p (30 * (Δ * ρ p)) ∩
    {x | Δ * ρ p / 2 < infDist x A ∧ infDist x A < 12 * (Δ * ρ p)}
  let Cp : M → Set M := fun p => closedBall p (20 * (Δ * ρ p)) ∩
    {x | 3 / 4 * (Δ * ρ p) ≤ infDist x A ∧ infDist x A ≤ 21 / 2 * (Δ * ρ p)}
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
  have hsq : 2 * Real.sqrt (200 * τ) < 30 * Real.sqrt τ := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 200)]
    have h200 : Real.sqrt 200 < 15 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    have hτs : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
    nlinarith
  have hdiam : ∀ q ∈ U, ∀ v ∈ minimizingDirectionsTo g hEnorm A q,
      ∀ v' ∈ minimizingDirectionsTo g hEnorm A q,
        Real.sqrt (g.inner q (v - v') (v - v')) ≤ 2 * Real.sqrt (200 * τ) := fun q hq => by
    obtain ⟨p, hp, hqp⟩ := hUd q hq
    exact (coarseBorder_nearest_directions g hEnorm (hscale p) hτ hτsmall (hQp p hp) (hdist p hp)
      (hheight p hp) (hcover p hp) (hpA p hp) (hborder p hp) (hbordercover p hp) hκ (hκΔ p hp)
      (hsec p hp) hqp.1 hqp.2.1.le hqp.2.2.le).2.1
  set m := P.inf' hP ρ with hm_def
  have hm : 0 < m := (Finset.lt_inf'_iff hP).mpr fun p _ => hρpos p
  have hmle (p : M) (hp : p ∈ P) : m ≤ ρ p := Finset.inf'_le ρ hp
  obtain ⟨F, O, hO, hCO, hFO, hclose, hout, hdiff, hlip, hgrad⟩ :=
    exists_distance_smoothing_with_gradient g hEnorm hε hε1 hA ⟨_, hpA _ hP.choose_spec⟩ hU hUA
      hdiam (hsq.trans hθ) hC hCU (mul_pos hμ (mul_pos hΔ hm))
  have hval (p : M) (hp : p ∈ P) (x : M) : |F x - infDist x A| < μ * (Δ * ρ p) :=
    (hclose x).trans_le (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hmle p hp) hΔ.le) hμ.le)
  refine ⟨F, O, hO, hFO, fun x => ?_, hlip, hdiff, fun p hp => ⟨hval p hp,
    fun x hx => hCO (mem_biUnion hp hx), fun x hx v hv => hgrad x (mem_biUnion hp hx) v hv⟩⟩
  by_cases hxU : x ∈ U
  · obtain ⟨p, hp, hxp⟩ := hUd x hxU
    have h1 := (abs_lt.mp (hval p hp x)).1
    have h2 := hxp.2.1
    nlinarith [hscale p]
  · rw [hout x hxU]
    exact infDist_nonneg

end DifferentialGeometry.Geometry.Collapse
