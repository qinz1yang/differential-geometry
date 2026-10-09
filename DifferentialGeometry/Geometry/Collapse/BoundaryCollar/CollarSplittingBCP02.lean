import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarSplitting
import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarHeightBCP01Applications

/-!
# Row BCP02: the actual cusp splitting with the smoothed height as its coordinate

Blueprint 207B, BCP02 (`B:8212–8321`). Let `η` be the BCP01 height of a collar
(`CuspEmbedding.bcp01`, errors `< ε` in `g`-norms on `2 ≤ z ≤ 98`). At a point `p₀ = e q₀` with
`5 ≤ η(p₀) ≤ 95` and a scale `r` (the value `ρ(p₀)` of the BSA05 scale), the coordinate is
`Φ(x) = (η(x) − η(p₀))/r` (BCP02.a), with the residual factor the flat torus
`r⁻² e^{−z₀} g_T` (not a point).

* `ofReal_abs_sub_le_mul_pathELength` (any manifold, boundary allowed): along a `C¹` curve,
  `|f(γ 1) − f(γ 0)| ≤ L · length`, if `|df(v)| ≤ L |v|_g` at the curve points.
* `CuspEmbedding.abs_sub_le_mul_of_mvfderiv_le`: the same for two points near `e q₀` (curves of
  almost minimal length stay in the slab `|z − z₀| < 16ρ₁` by first exit).
* `hasEuclideanSplitting_of_coordinate_bounds` (metric kernel): a coordinate `Φ` with a torus
  label `τ`, bi-Lipschitz in the `√(ΔΦ² + (c d_T)²)` form and covering, gives the splitting.
* `CuspEmbedding.bcp02` (row BCP02, one member of the boundary sequence; the uniform tail is the
  explicit smallness `δ, ε ≤ β²/1000`, `r ≤ β³/(2000(1 + L))`): there is ONE smooth `η` (the
  BCP01 height) such that at every such `p₀` and scale `r`
  - (BCP02.a) `(W, r⁻¹ d_g, p₀)` has a rank-one splitting at scale `β`, through the map
    `x ↦ (Φ(x), t(x))` into `ℝ ×₂ (T², r⁻¹ e^{−z₀/2} d_{g_T})`;
  - (BCP02.b, with the radius-`L` buffer) that map is `(1 ± β²/20)`-bi-Lipschitz on the
    `r⁻¹ d_g`-ball of radius `β⁻¹ + β + L`;
  - (adapted coordinate of quality `γ`, KL4.21) `Φ` is smooth, `(1 + γ/2)`-Lipschitz on the unit
    ball; the chord test `|(Φ ∘ c)'(x₀) − (Φ(c(x₀ + ℓ)) − Φ(c x₀))/ℓ| < γ` holds along EVERY
    geodesic segment `c` of `g` in the collar band with `|c'|_g ≤ r` (unit speed for `r⁻²g`) and
    `ℓ ≤ 1 + γ⁻¹` (BCP02.c); image clause: points of the unit ball with `Φ` within `γ` of `±1`,
    and `|Φ| < 1 + γ` on the unit ball.

Deviation: the chord clause is stated for every geodesic segment of `g` in the band (the tree has
no "minimizing curves are geodesics" on a carrier with boundary); the blueprint needs it for the
minimizing segments, which are among them.
-/

set_option autoImplicit false

noncomputable section

open Set Function Bundle Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint GC.MetricGeometry
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Connection
  DifferentialGeometry.Geometry.Riemannian.Geodesic
open scoped Manifold ENNReal ContDiff

namespace DifferentialGeometry.Geometry.Collapse

universe u

section Curve

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **Mean value along a curve.** If `f` is differentiable at the points of a `C¹` curve `γ` on
`[0, 1]` and `|df(v)| ≤ L |v|_h` there (`L > 0`), then `|f(γ 1) − f(γ 0)| ≤ L · length_h γ`. -/
theorem ofReal_abs_sub_le_mul_pathELength (h : SmoothRiemannianMetric I M) {f : M → ℝ}
    {γ : ℝ → M} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1))
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, MDifferentiableAt I 𝓘(ℝ, ℝ) f (γ t)) {L : ℝ} (hL : 0 < L)
    (hbound : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ v : TangentSpace I (γ t),
      |mvfderiv I f (γ t) v| ≤ L * Real.sqrt (h.inner (γ t) v v)) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨h.toRiemannianMetric⟩
    ENNReal.ofReal |f (γ 1) - f (γ 0)| ≤ ENNReal.ofReal L * pathELength I γ 0 1 := by
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨h.toRiemannianMetric⟩
  have henorm : ∀ (z : M) (v : TangentSpace I z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (h.inner z v v)) := by
    intro z v
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    congr 2
  have hL0 : ENNReal.ofReal L ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hL
  rcases eq_or_ne (pathELength I γ 0 1) ⊤ with hLtop | hLtop
  · rw [hLtop, ENNReal.mul_top hL0]
    exact le_top
  have hLform : pathELength I γ 0 1 = ∫⁻ t in Ioo (0 : ℝ) 1, ‖mfderiv 𝓘(ℝ, ℝ) I γ t 1‖ₑ :=
    pathELength_eq_lintegral_mfderiv_Ioo
  have hucont : ContinuousOn (fun t : ℝ => f (γ t)) (Icc 0 1) := fun t ht =>
    ((hf t ht).continuousAt).comp_continuousWithinAt (hγ.continuousOn t ht)
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun s : ℝ => f (γ s))
      (mvfderiv I f (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)) t := by
    intro t ht
    have hmem : Icc (0 : ℝ) 1 ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    have hγd : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
      ((hγ.mdifferentiableOn one_ne_zero) t (Ioo_subset_Icc_self ht)).mdifferentiableAt hmem
    have hfd : MDifferentiableAt I 𝓘(ℝ, ℝ) f (γ t) := hf t (Ioo_subset_Icc_self ht)
    have hcomp : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => f (γ s)) t := hfd.comp t hγd
    have hdiff : DifferentiableAt ℝ (fun s : ℝ => f (γ s)) t :=
      mdifferentiableAt_iff_differentiableAt.mp hcomp
    have hval : deriv (fun s : ℝ => f (γ s)) t = mvfderiv I f (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) := by
      have h := mfderiv_comp t hfd hγd
      rw [mfderiv_eq_fderiv] at h
      have hv := congrArg (fun D => NormedSpace.fromTangentSpace (𝕜 := ℝ) (f (γ t))
        (D ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm (1 : ℝ)))) h
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply, fderiv_apply_one_eq_deriv] using! hv
    have := hdiff.hasDerivAt
    rwa [hval] at this
  have hderivval : ∀ t ∈ Ioo (0 : ℝ) 1, deriv (fun s : ℝ => f (γ s)) t =
      mvfderiv I f (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) := fun t ht => (hderiv t ht).deriv
  have hbdd : ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal |deriv (fun s : ℝ => f (γ s)) t| ≤
      ENNReal.ofReal L * pathELength I γ 0 1 := by
    rw [hLform, ← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine MeasureTheory.setLIntegral_mono_ae' measurableSet_Ioo ?_
    filter_upwards with t ht
    rw [hderivval t ht, henorm, ← ENNReal.ofReal_mul hL.le]
    exact ENNReal.ofReal_le_ofReal (hbound t ht _)
  have hfin : ENNReal.ofReal L * pathELength I γ 0 1 < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hLtop.lt_top
  have hint : MeasureTheory.IntegrableOn (deriv fun s : ℝ => f (γ s)) (Ioo (0 : ℝ) 1) := by
    refine ⟨(measurable_deriv (fun s : ℝ => f (γ s))).aestronglyMeasurable.restrict, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
    calc ∫⁻ t in Ioo (0 : ℝ) 1, ‖deriv (fun s : ℝ => f (γ s)) t‖ₑ
        = ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal |deriv (fun s : ℝ => f (γ s)) t| := by
          refine MeasureTheory.lintegral_congr fun t => ?_
          rw [Real.enorm_eq_ofReal_abs]
      _ ≤ _ := hbdd
      _ < ⊤ := hfin
  have hIint : IntervalIntegrable (deriv fun s : ℝ => f (γ s)) MeasureTheory.volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
    exact hint
  have hderivWithin : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt (fun s : ℝ => f (γ s))
      (deriv (fun s : ℝ => f (γ s)) t) (Ioi t) t := by
    intro t ht
    have h1 := (hderiv t ht).hasDerivWithinAt (s := Ioi t)
    rwa [← hderivval t ht] at h1
  have hftc : ∫ t in (0 : ℝ)..1, deriv (fun s : ℝ => f (γ s)) t = f (γ 1) - f (γ 0) :=
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le zero_le_one hucont
      hderivWithin hIint
  have habs : |f (γ 1) - f (γ 0)| ≤ ∫ t in (0 : ℝ)..1, |deriv (fun s : ℝ => f (γ s)) t| := by
    rw [← hftc]
    exact intervalIntegral.abs_integral_le_integral_abs zero_le_one
  have hconv : ENNReal.ofReal (∫ t in (0 : ℝ)..1, |deriv (fun s : ℝ => f (γ s)) t|) =
      ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal |deriv (fun s : ℝ => f (γ s)) t| := by
    rw [intervalIntegral.integral_of_le zero_le_one, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint.abs
      (Filter.Eventually.of_forall fun t => abs_nonneg _)
  calc ENNReal.ofReal |f (γ 1) - f (γ 0)|
      ≤ ENNReal.ofReal (∫ t in (0 : ℝ)..1, |deriv (fun s : ℝ => f (γ s)) t|) :=
        ENNReal.ofReal_le_ofReal habs
    _ = _ := hconv
    _ ≤ _ := hbdd

end Curve

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
  {X : Set W.Carrier}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **Mean value near a collar point.** If `|df(v)| ≤ L |v|_g` (`L > 0`) and `f` is
differentiable at every collar point of height within `16ρ₁` of `z₀`, then two points within
`2√(1 − δ) ρ₁` of `e q₀` satisfy `|f x − f x'| ≤ L d_g(x, x')`. -/
theorem CuspEmbedding.abs_sub_le_mul_of_mvfderiv_le [ConnectedSpace W.Carrier]
    (e : CuspEmbedding W g K δ X) {q₀ : CuspHalfSpace} {ρ₁ : ℝ}
    (hup : q₀.2.val 0 + 16 * ρ₁ < cuspDepth) (hδ : δ < 3 / 4) {f : W.Carrier → ℝ} {L : ℝ}
    (hL : 0 < L)
    (hf : ∀ p ∈ cuspDomain, |p.2.val 0 - q₀.2.val 0| < 16 * ρ₁ →
      MDifferentiableAt W.model 𝓘(ℝ, ℝ) f (e.toFun p) ∧
        ∀ v : TangentSpace W.model (e.toFun p),
          |mvfderiv W.model f (e.toFun p) v| ≤ L * Real.sqrt (g.inner (e.toFun p) v v))
    {x x' : W.Carrier}
    (hx : riemannianEDistOf g (e.toFun q₀) x <
      ENNReal.ofReal (Real.sqrt (1 - δ) * (4 * ρ₁ / 2)))
    (hx' : riemannianEDistOf g (e.toFun q₀) x' <
      ENNReal.ofReal (Real.sqrt (1 - δ) * (4 * ρ₁ / 2))) :
    |f x - f x'| ≤ L * (riemannianEDistOf g x x').toReal := by
  let : RiemannianBundle (fun x : W.Carrier => TangentSpace W.model x) := ⟨g.toRiemannianMetric⟩
  have hρ : 0 < ρ₁ := by
    by_contra hneg
    push Not at hneg
    have h0 : Real.sqrt (1 - δ) * (4 * ρ₁ / 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) (by linarith)
    rw [ENNReal.ofReal_of_nonpos h0] at hx
    exact absurd hx (not_lt.mpr bot_le)
  have hs : 0 < Real.sqrt (1 - δ) := Real.sqrt_pos.mpr (by linarith)
  have hup4 : q₀.2.val 0 + 4 * ρ₁ < cuspDepth := by linarith
  obtain ⟨q, hq, rfl, hqz⟩ := e.exists_preimage_of_riemannianEDistOf_lt hup4 hx
  set d : ℝ := (riemannianEDistOf g (e.toFun q) x').toReal with hd
  have hdne : riemannianEDistOf g (e.toFun q) x' ≠ ⊤ := riemannianEDistOf_ne_top g _ _
  have hdlt : d < Real.sqrt (1 - δ) * (16 * ρ₁ / 2) := by
    have htri : riemannianEDistOf g (e.toFun q) x' ≤
        riemannianEDistOf g (e.toFun q₀) (e.toFun q) + riemannianEDistOf g (e.toFun q₀) x' := by
      rw [riemannianEDistOf_comm g (e.toFun q₀) (e.toFun q)]
      exact riemannianEDistOf_triangle g _ _ _
    have hsum := ENNReal.add_lt_add hx hx'
    have h2 : riemannianEDistOf g (e.toFun q) x' <
        ENNReal.ofReal (Real.sqrt (1 - δ) * (4 * ρ₁ / 2) + Real.sqrt (1 - δ) * (4 * ρ₁ / 2)) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity)]
      exact htri.trans_lt hsum
    have h3 := (ENNReal.toReal_lt_toReal hdne ENNReal.ofReal_ne_top).mpr h2
    rw [ENNReal.toReal_ofReal (by positivity)] at h3
    rw [hd]
    nlinarith
  rw [abs_sub_comm]
  refine le_of_forall_pos_lt_add fun τ hτ => ?_
  set τ' : ℝ := min (τ / (2 * L)) (Real.sqrt (1 - δ) * (16 * ρ₁ / 2) - d) with hτ'
  have hτ'0 : 0 < τ' := lt_min (by positivity) (by linarith)
  have hlt : Manifold.riemannianEDist W.model (e.toFun q) x' < ENNReal.ofReal (d + τ') := by
    change riemannianEDistOf g (e.toFun q) x' < _
    rw [← ENNReal.ofReal_toReal hdne]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by rw [← hd]; linarith)
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hlt
  have hτ'2 : τ' ≤ Real.sqrt (1 - δ) * (16 * ρ₁ / 2) - d := min_le_right _ _
  have hlen' : pathELength W.model γ 0 1 <
      ENNReal.ofReal (Real.sqrt (1 - δ) * (16 * ρ₁ / 2)) :=
    hlen.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
  have hq8 : |q.2.val 0 - q₀.2.val 0| ≤ 16 * ρ₁ / 2 := by linarith
  obtain ⟨c, -, hcd, hce⟩ := e.exists_slab_lift_of_pathELength_lt hγ hup hq8 hγ0 hlen'
  have hcurve := ofReal_abs_sub_le_mul_pathELength g hγ (f := f)
    (fun t ht => by rw [← hce t ht]; exact (hf (c t) (hcd t ht).1 (hcd t ht).2).1) hL
    (fun t ht v => by
      have htI : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
      have h := (hf (c t) (hcd t htI).1 (hcd t htI).2).2
      rw [hce t htI] at h
      exact h v)
  rw [hγ0, hγ1] at hcurve
  have hfin := hcurve.trans (mul_le_mul' le_rfl hlen.le)
  rw [← ENNReal.ofReal_mul hL.le] at hfin
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hfin
  have hτ2 : L * τ' ≤ τ / 2 := by
    have h1 : τ' ≤ τ / (2 * L) := min_le_left _ _
    calc L * τ' ≤ L * (τ / (2 * L)) := mul_le_mul_of_nonneg_left h1 hL.le
      _ = τ / 2 := by field_simp
  nlinarith

/-- `|√((u + w)² + T²) − √(u² + T²)| ≤ |w|`. -/
theorem abs_sqrt_add_sq_sub_le (u w T : ℝ) :
    |Real.sqrt ((u + w) ^ 2 + T ^ 2) - Real.sqrt (u ^ 2 + T ^ 2)| ≤ |w| := by
  have key : ∀ a b : ℝ, Real.sqrt ((a + b) ^ 2 + T ^ 2) ≤ Real.sqrt (a ^ 2 + T ^ 2) + |b| := by
    intro a b
    have ha : |a| ≤ Real.sqrt (a ^ 2 + T ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg T])
    rw [Real.sqrt_le_left (by positivity)]
    have hS := Real.sq_sqrt (show 0 ≤ a ^ 2 + T ^ 2 by positivity)
    have hab : a * b ≤ |a| * |b| := by
      rw [← abs_mul]
      exact le_abs_self _
    nlinarith [abs_nonneg a, abs_nonneg b, sq_abs b, Real.sqrt_nonneg (a ^ 2 + T ^ 2)]
  rw [abs_le]
  constructor
  · have h := key (u + w) (-w)
    rw [add_neg_cancel_right, abs_neg] at h
    linarith
  · linarith [key u w]

/-- **Coordinate form of the splitting kernel.** A coordinate `Φ` with `Φ p₀ = 0` and a label
`τ` into a set `T` carrying a function `d_T`, such that `x ↦ (Φ x, τ x)` is `(1 ± a)`-bi-Lipschitz
on the ball of radius `β⁻¹ + β` and `β/4`-covering, measured with `√(ΔΦ² + (c d_T)²)`, gives a
rank-one splitting at `p₀`, for any metric model `φT : T → Y` of `c d_T`. -/
theorem hasEuclideanSplitting_of_coordinate_bounds {Xs : Type u} [MetricSpace Xs] {p₀ : Xs}
    {β a c : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (ha : 0 ≤ a) (ha1 : a < 1)
    (herr : 2 * a * (β⁻¹ + β) < β / 4) {T : Type} (Φ : Xs → ℝ) (τ : Xs → T)
    (dT : T → T → ℝ) (hbase : Φ p₀ = 0)
    (hdist : ∀ x x', dist x p₀ ≤ β⁻¹ + β → dist x' p₀ ≤ β⁻¹ + β →
      (1 - a) * dist x x' ≤ Real.sqrt ((Φ x - Φ x') ^ 2 + (c * dT (τ x) (τ x')) ^ 2) ∧
        Real.sqrt ((Φ x - Φ x') ^ 2 + (c * dT (τ x) (τ x')) ^ 2) ≤ (1 + a) * dist x x')
    (hcov : ∀ (s : ℝ) (t : T),
      Real.sqrt (s ^ 2 + (c * dT t (τ p₀)) ^ 2) ≤ β⁻¹ + β - β / 4 →
        ∃ x, dist x p₀ ≤ β⁻¹ + β ∧ Real.sqrt ((s - Φ x) ^ 2 + (c * dT t (τ x)) ^ 2) < β / 4)
    {Y : Type} [MetricSpace Y] (φT : T → Y) (hφT : Surjective φT)
    (hdY : ∀ t t', dist (φT t) (φT t') = c * dT t t') :
    HasEuclideanSplitting.{u, 0} p₀ 1 β := by
  have hd : ∀ (u u' : ℝ) (t t' : T),
      dist (WithLp.toLp 2 (u, φT t) : WithLp 2 (ℝ × Y)) (WithLp.toLp 2 (u', φT t')) =
        Real.sqrt ((u - u') ^ 2 + (c * dT t t') ^ 2) := by
    intro u u' t t'
    have h := WithLp.prod_dist_sq_eq_add_sq (WithLp.toLp 2 (u, φT t) : WithLp 2 (ℝ × Y))
      (WithLp.toLp 2 (u', φT t'))
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, Real.dist_eq, sq_abs, hdY] at h
    rw [← h, Real.sqrt_sq dist_nonneg]
  refine hasEuclideanSplitting_one_of_bilipschitz_product hβ hβ1 ha ha1 herr
    (fun x => WithLp.toLp 2 (Φ x, φT (τ x))) (by rw [hbase]) (fun x x' hx hx' => ?_)
    (fun y hy => ?_)
  · rw [hd]
    exact hdist x x' hx hx'
  · obtain ⟨t, ht⟩ := hφT y.snd
    have hy' : y = WithLp.toLp 2 (y.fst, φT t) := by
      rw [ht]
      rfl
    rw [hy', hd, sub_zero] at hy
    obtain ⟨x, hx, hxy⟩ := hcov y.fst t hy
    refine ⟨x, hx, ?_⟩
    rw [hy', hd]
    exact hxy

/-- `e^x (1 − x) ≤ 1`. -/
private theorem collarBCP_exp_mul_le (x : ℝ) : Real.exp x * (1 - x) ≤ 1 := by
  have h := Real.add_one_le_exp (-x)
  have h1 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have h2 : 0 < Real.exp x := Real.exp_pos x
  nlinarith

/-- **The distortion budget** of the frozen chart at `b = β²`: for `0 ≤ δ ≤ b/1000` and
`0 < ρ ≤ b/1000`, `e^{4ρ} ≤ (1 + b/40) √(1 − δ)`, `(1 − b/40)² (1 + δ) e^{4ρ} ≤ 1`, and
`(1 + δ) e^{ρ'} (R − β/4)² ≤ R²` for `R = β⁻¹ + β`, `ρ' ≤ ρ`. -/
theorem collarBCP_budget {β δ ρ ρ' : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ β ^ 2 / 1000) (hρ0 : 0 < ρ) (hρ : ρ ≤ β ^ 2 / 1000) (hρ' : ρ' ≤ ρ) :
    Real.exp (4 * ρ) ≤ (1 + β ^ 2 / 40) * Real.sqrt (1 - δ) ∧
      (1 - β ^ 2 / 40) ^ 2 * ((1 + δ) * Real.exp (4 * ρ)) ≤ 1 ∧
      (1 + δ) * Real.exp ρ' * (β⁻¹ + β - β / 4) ^ 2 ≤ (β⁻¹ + β) ^ 2 := by
  set b : ℝ := β ^ 2 with hb
  have hb0 : 0 < b := by positivity
  have hb1 : b < 1 := by nlinarith
  have hsqrt : 1 - δ ≤ Real.sqrt (1 - δ) := by
    have h0 : 0 ≤ 1 - δ := by nlinarith
    calc 1 - δ = Real.sqrt ((1 - δ) ^ 2) := (Real.sqrt_sq h0).symm
      _ ≤ Real.sqrt (1 - δ) := Real.sqrt_le_sqrt (by nlinarith)
  have hE4 := collarBCP_exp_mul_le (4 * ρ)
  have hE1 := collarBCP_exp_mul_le ρ'
  have hE4p : 0 < Real.exp (4 * ρ) := Real.exp_pos _
  have hE1p : 0 < Real.exp ρ' := Real.exp_pos _
  refine ⟨?_, ?_, ?_⟩
  · have hprod : 1 ≤ (1 + b / 40) * (1 - δ) * (1 - 4 * ρ) := by
      have h1 : 1 - δ - 4 * ρ ≤ (1 - δ) * (1 - 4 * ρ) := by nlinarith
      have h2 : 1 - b / 200 ≤ 1 - δ - 4 * ρ := by linarith
      nlinarith
    have hpos : 0 < 1 - 4 * ρ := by linarith
    have h1 : Real.exp (4 * ρ) ≤ (1 + b / 40) * (1 - δ) := by
      have : Real.exp (4 * ρ) * (1 - 4 * ρ) ≤ (1 + b / 40) * (1 - δ) * (1 - 4 * ρ) := by
        linarith
      exact le_of_mul_le_mul_right this hpos
    calc Real.exp (4 * ρ) ≤ (1 + b / 40) * (1 - δ) := h1
      _ ≤ (1 + b / 40) * Real.sqrt (1 - δ) := by gcongr
  · have hsq : (1 - b / 40) ^ 2 ≤ 1 - b / 40 := by nlinarith
    have h2 : (1 - b / 40) * (1 + δ) ≤ 1 - 4 * ρ := by nlinarith
    have h3 : (1 - b / 40) ^ 2 * (1 + δ) ≤ 1 - 4 * ρ := by nlinarith
    nlinarith
  · set R : ℝ := β⁻¹ + β with hR
    have hRβ : R * β = 1 + b := by
      rw [hR, hb, add_mul, inv_mul_cancel₀ hβ.ne']
      ring
    have hR0 : 0 < R := by positivity
    have hRb : R - β / 4 ≤ R * (1 - b / 8) := by nlinarith
    have hR4 : 0 ≤ R - β / 4 := by nlinarith
    have hsq : (R - β / 4) ^ 2 ≤ R ^ 2 * (1 - b / 8) := by
      have h1 : (R - β / 4) ^ 2 ≤ (R * (1 - b / 8)) ^ 2 := pow_le_pow_left₀ hR4 hRb 2
      have h2 : (1 - b / 8) ^ 2 ≤ 1 - b / 8 := by nlinarith
      nlinarith [sq_nonneg R]
    have h3 : (1 + δ) * (1 - b / 8) ≤ 1 - ρ' := by nlinarith
    have h4 : (1 + δ) * Real.exp ρ' * (1 - b / 8) ≤ 1 := by nlinarith
    calc (1 + δ) * Real.exp ρ' * (R - β / 4) ^ 2 ≤ (1 + δ) * Real.exp ρ' * (R ^ 2 * (1 - b / 8)) :=
          by gcongr
      _ = R ^ 2 * ((1 + δ) * Real.exp ρ' * (1 - b / 8)) := by ring
      _ ≤ R ^ 2 * 1 := by gcongr
      _ = R ^ 2 := mul_one _

/-- **BCP02.b with the smoothed coordinate.** If `Δ = η − ζ` has `|dΔ| ≤ ε' |·|_g` on the slab
`|z − z₀| < 16 r R₁`, then on the `r⁻¹ d_g`-ball of radius `R₁` the map
`x ↦ ((η x − η p₀)/r, t(x))` is `(1 ± β²/20)`-bi-Lipschitz into `ℝ ×₂ (T², r⁻¹ e^{−z₀/2} d_T)`
(`δ ≤ β²/1000`, `r R₁ ≤ β²/1000`, `ε' ≤ β²/40`). -/
theorem CuspEmbedding.bcp02_distortion [ConnectedSpace W.Carrier] (e : CuspEmbedding W g K δ X)
    {η : W.Carrier → ℝ} {q₀ : CuspHalfSpace} {β r R₁ ε' : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hδ : δ ≤ β ^ 2 / 1000) (hr : 0 < r) (hR₁ : 0 < R₁) (hρ : r * R₁ ≤ β ^ 2 / 1000)
    (hz4 : 4 < q₀.2.val 0) (hz96 : q₀.2.val 0 < 96) (hε' : 0 < ε') (hε'b : ε' ≤ β ^ 2 / 40)
    (hΔ : ∀ p ∈ cuspDomain, |p.2.val 0 - q₀.2.val 0| < 16 * (r * R₁) →
      MDifferentiableAt W.model 𝓘(ℝ, ℝ)
          (fun y => η y - (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p) ∧
        ∀ v : TangentSpace W.model (e.toFun p),
          |mvfderiv W.model (fun y => η y - (invFunOn e.toFun cuspDomain y).2.val 0)
              (e.toFun p) v| ≤ ε' * Real.sqrt (g.inner (e.toFun p) v v))
    {x x' : W.Carrier} (hx : r⁻¹ * (riemannianEDistOf g x (e.toFun q₀)).toReal ≤ R₁)
    (hx' : r⁻¹ * (riemannianEDistOf g x' (e.toFun q₀)).toReal ≤ R₁) :
    (1 - β ^ 2 / 20) * (r⁻¹ * (riemannianEDistOf g x x').toReal) ≤
        Real.sqrt (((η x - η (e.toFun q₀)) / r - (η x' - η (e.toFun q₀)) / r) ^ 2 +
          (r⁻¹ * Real.exp (-(q₀.2.val 0) / 2) * (riemannianEDistOf e.cusp.torusMetric
            (invFunOn e.toFun cuspDomain x).1 (invFunOn e.toFun cuspDomain x').1).toReal) ^ 2) ∧
      Real.sqrt (((η x - η (e.toFun q₀)) / r - (η x' - η (e.toFun q₀)) / r) ^ 2 +
          (r⁻¹ * Real.exp (-(q₀.2.val 0) / 2) * (riemannianEDistOf e.cusp.torusMetric
            (invFunOn e.toFun cuspDomain x).1 (invFunOn e.toFun cuspDomain x').1).toReal) ^ 2) ≤
        (1 + β ^ 2 / 20) * (r⁻¹ * (riemannianEDistOf g x x').toReal) := by
  set z₀ : ℝ := q₀.2.val 0 with hz₀
  set ρ₁ : ℝ := r * R₁ with hρ₁
  have hδ0 : 0 ≤ δ := e.delta_nonneg
  have hρ0 : 0 < ρ₁ := mul_pos hr hR₁
  have hb1 : β ^ 2 < 1 := by nlinarith
  have hδ34 : δ < 3 / 4 := by nlinarith
  have hs0 : 1 / 2 < Real.sqrt (1 - δ) := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have hball : ∀ y : W.Carrier, r⁻¹ * (riemannianEDistOf g y (e.toFun q₀)).toReal ≤ R₁ →
      riemannianEDistOf g (e.toFun q₀) y <
        ENNReal.ofReal (Real.sqrt (1 - δ) * (4 * ρ₁ / 2)) := by
    intro y hy
    have hle : (riemannianEDistOf g y (e.toFun q₀)).toReal ≤ ρ₁ := by
      rw [hρ₁]
      have := (inv_mul_le_iff₀ hr).mp hy
      linarith
    rw [riemannianEDistOf_comm, ← ENNReal.ofReal_toReal (riemannianEDistOf_ne_top g _ _)]
    refine (ENNReal.ofReal_lt_ofReal_iff (by nlinarith)).mpr ?_
    nlinarith
  have hup16 : z₀ + 16 * ρ₁ < cuspDepth := by
    have : z₀ + 16 * ρ₁ < 100 := by nlinarith
    simpa [cuspDepth] using this
  obtain ⟨hL, hU, -⟩ := collarBCP_budget (ρ' := ρ₁) hβ hβ1 hδ0 hδ hρ0 hρ le_rfl
  obtain ⟨q, hq, q', hq', rfl, rfl, -, -, hlo, hhi⟩ :=
    e.frozen_bilipschitz_toReal (ρ₁ := ρ₁) (by nlinarith) (by
      have : z₀ + 8 * ρ₁ < 100 := by nlinarith
      simpa [cuspDepth] using this) (hball _ hx) (hball _ hx')
  have hΔlip := e.abs_sub_le_mul_of_mvfderiv_le hup16 hδ34 hε' hΔ (hball _ hx) (hball _ hx')
  have hinv : ∀ p ∈ cuspDomain, invFunOn e.toFun cuspDomain (e.toFun p) = p :=
    fun p hp => e.injOn_cuspDomain.leftInvOn_invFunOn hp
  rw [hinv q hq, hinv q' hq']
  rw [hinv q hq, hinv q' hq'] at hΔlip
  set D : ℝ := (riemannianEDistOf g (e.toFun q) (e.toFun q')).toReal with hD
  set Q : ℝ := Real.sqrt ((q'.2.val 0 - q.2.val 0) ^ 2 + Real.exp (-z₀) *
    (riemannianEDistOf e.cusp.torusMetric q.1 q'.1).toReal ^ 2) with hQ
  set dT : ℝ := (riemannianEDistOf e.cusp.torusMetric q.1 q'.1).toReal with hdT
  set Δq : ℝ := η (e.toFun q) - q.2.val 0 with hΔq
  set Δq' : ℝ := η (e.toFun q') - q'.2.val 0 with hΔq'
  have hD0 : 0 ≤ D := ENNReal.toReal_nonneg
  have hQ0 : 0 ≤ Q := Real.sqrt_nonneg _
  -- the frozen bounds `(1 - β²/40) D ≤ Q ≤ (1 + β²/40) D`
  have he8 : Real.exp (-(8 * ρ₁) / 2) = (Real.exp (4 * ρ₁))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  have he8' : Real.exp (8 * ρ₁ / 2) = Real.exp (4 * ρ₁) := by
    congr 1
    ring
  rw [he8] at hlo
  rw [he8'] at hhi
  have hE : 0 < Real.exp (4 * ρ₁) := Real.exp_pos _
  have hsq : 0 < Real.sqrt (1 - δ) := by linarith
  have hQD : Q ≤ (1 + β ^ 2 / 40) * D := by
    have h1 : Real.sqrt (1 - δ) * Q ≤ Real.exp (4 * ρ₁) * D := by
      have := hlo
      rw [← mul_assoc, mul_comm (Real.sqrt (1 - δ)), mul_assoc] at this
      have h2 := (inv_mul_le_iff₀ hE).mp this
      linarith
    have h3 : Real.sqrt (1 - δ) * Q ≤ Real.sqrt (1 - δ) * ((1 + β ^ 2 / 40) * D) := by
      calc Real.sqrt (1 - δ) * Q ≤ Real.exp (4 * ρ₁) * D := h1
        _ ≤ (1 + β ^ 2 / 40) * Real.sqrt (1 - δ) * D := mul_le_mul_of_nonneg_right hL hD0
        _ = Real.sqrt (1 - δ) * ((1 + β ^ 2 / 40) * D) := by ring
    exact le_of_mul_le_mul_left h3 hsq
  have hDQ : (1 - β ^ 2 / 40) * D ≤ Q := by
    have h1a : 0 ≤ 1 - β ^ 2 / 40 := by linarith
    have hS : (1 - β ^ 2 / 40) * Real.sqrt ((1 + δ) * Real.exp (4 * ρ₁)) ≤ 1 := by
      have hsq' : Real.sqrt ((1 - β ^ 2 / 40) ^ 2 * ((1 + δ) * Real.exp (4 * ρ₁))) ≤ 1 := by
        have h1 := Real.sqrt_le_sqrt hU
        rwa [Real.sqrt_one] at h1
      rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h1a] at hsq'
    have hhi' : D ≤ Real.sqrt ((1 + δ) * Real.exp (4 * ρ₁)) * Q := by
      rw [hD, hQ, ← Real.sqrt_mul (by positivity)]
      exact hhi
    calc (1 - β ^ 2 / 40) * D ≤ (1 - β ^ 2 / 40) * (Real.sqrt ((1 + δ) * Real.exp (4 * ρ₁)) * Q) :=
          mul_le_mul_of_nonneg_left hhi' h1a
      _ = ((1 - β ^ 2 / 40) * Real.sqrt ((1 + δ) * Real.exp (4 * ρ₁))) * Q := by ring
      _ ≤ 1 * Q := mul_le_mul_of_nonneg_right hS hQ0
      _ = Q := one_mul Q
  -- the coordinate difference splits into the frozen part and the `Δ` part
  have hexp : Real.exp (-z₀ / 2) ^ 2 = Real.exp (-z₀) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hfrozen : Real.sqrt (((q.2.val 0 - q'.2.val 0) / r) ^ 2 +
      (r⁻¹ * Real.exp (-z₀ / 2) * dT) ^ 2) = r⁻¹ * Q := by
    have hrad : ((q.2.val 0 - q'.2.val 0) / r) ^ 2 + (r⁻¹ * Real.exp (-z₀ / 2) * dT) ^ 2 =
        r⁻¹ ^ 2 * ((q'.2.val 0 - q.2.val 0) ^ 2 + Real.exp (-z₀) * dT ^ 2) := by
      rw [mul_pow, mul_pow, hexp]
      field_simp
      ring
    rw [hrad, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hsplit : (η (e.toFun q) - η (e.toFun q₀)) / r - (η (e.toFun q') - η (e.toFun q₀)) / r =
      (q.2.val 0 - q'.2.val 0) / r + (Δq - Δq') / r := by
    rw [hΔq, hΔq']
    ring
  rw [hsplit]
  have hdiff := abs_sqrt_add_sq_sub_le ((q.2.val 0 - q'.2.val 0) / r) ((Δq - Δq') / r)
    (r⁻¹ * Real.exp (-z₀ / 2) * dT)
  rw [hfrozen] at hdiff
  have hw : |(Δq - Δq') / r| ≤ ε' * (r⁻¹ * D) := by
    rw [abs_div, abs_of_pos hr, div_le_iff₀ hr]
    have h := hΔlip
    simp only [hΔq, hΔq'] at h ⊢
    calc |η (e.toFun q) - q.2.val 0 - (η (e.toFun q') - q'.2.val 0)| ≤ ε' * D := h
      _ = ε' * (r⁻¹ * D) * r := by field_simp
  have hrinv : 0 < r⁻¹ := inv_pos.mpr hr
  have habs := abs_le.mp hdiff
  constructor
  · have h1 : (1 - β ^ 2 / 40) * (r⁻¹ * D) ≤ r⁻¹ * Q := by
      calc (1 - β ^ 2 / 40) * (r⁻¹ * D) = r⁻¹ * ((1 - β ^ 2 / 40) * D) := by ring
        _ ≤ r⁻¹ * Q := mul_le_mul_of_nonneg_left hDQ hrinv.le
    have hrD : 0 ≤ r⁻¹ * D := mul_nonneg hrinv.le hD0
    have h2 := mul_le_mul_of_nonneg_right hε'b hrD
    linarith [habs.1]
  · have h1 : r⁻¹ * Q ≤ (1 + β ^ 2 / 40) * (r⁻¹ * D) := by
      calc r⁻¹ * Q ≤ r⁻¹ * ((1 + β ^ 2 / 40) * D) := mul_le_mul_of_nonneg_left hQD hrinv.le
        _ = (1 + β ^ 2 / 40) * (r⁻¹ * D) := by ring
    have hrD : 0 ≤ r⁻¹ * D := mul_nonneg hrinv.le hD0
    have h2 := mul_le_mul_of_nonneg_right hε'b hrD
    linarith [habs.2]

/-- **BCP02.c (scaled chord test)** for any smooth `η` with the BCP01.b Hessian bound on the
band: along a geodesic segment `c` of `g` in the band with `|c'|_g ≤ r` and length parameter
`ℓ ≤ 1 + γ⁻¹`, `Φ = (η − a)/r` satisfies `|(Φ ∘ c)'(x₀) − (Φ(c(x₀+ℓ)) − Φ(c x₀))/ℓ| < γ`
(`r ≤ γ³/2000`). -/
theorem CuspEmbedding.bcp02_chord (e : CuspEmbedding W g K δ X) {η : W.Carrier → ℝ}
    (hη : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η)
    (hH : ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
      ∀ u w : TangentSpace W.model (e.toFun p),
        |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g) η
            (e.toFun p) u w| ≤
          3 / 2 * Real.sqrt (g.inner (e.toFun p) u u) * Real.sqrt (g.inner (e.toFun p) w w))
    {γ r a : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hr : 0 < r) (hrγ : r ≤ γ ^ 3 / 2000)
    (c : ℝ → W.Carrier) (x₀ ℓ : ℝ) (hℓ : 0 < ℓ) (hℓγ : ℓ ≤ 1 + γ⁻¹)
    (hc : ∀ t ∈ Icc x₀ (x₀ + ℓ), ContMDiffAt 𝓘(ℝ, ℝ) W.model 2 c t)
    (hgeo : ∀ t ∈ Icc x₀ (x₀ + ℓ), HasGeodesicEquationAt g c t)
    (hband : ∀ t ∈ Icc x₀ (x₀ + ℓ), ∃ p ∈ cuspDomain, 2 ≤ p.2.val 0 ∧ p.2.val 0 ≤ 98 ∧
      e.toFun p = c t)
    (hspeed : ∀ t ∈ Icc x₀ (x₀ + ℓ), g.inner (c t)
      (mfderiv 𝓘(ℝ, ℝ) W.model c t ((NormedSpace.fromTangentSpace t).symm 1))
      (mfderiv 𝓘(ℝ, ℝ) W.model c t ((NormedSpace.fromTangentSpace t).symm 1)) ≤ r ^ 2) :
    |deriv (fun t => (η (c t) - a) / r) x₀ -
      ((η (c (x₀ + ℓ)) - a) / r - (η (c x₀) - a) / r) / ℓ| < γ := by
  have hf : ∀ t ∈ Icc x₀ (x₀ + ℓ), ContDiffAt ℝ 2 (η ∘ c) t := fun t ht =>
    contMDiffAt_iff_contDiffAt.mp (((hη _).of_le (by simp)).comp t (hc t ht))
  have hM : ∀ t ∈ Icc x₀ (x₀ + ℓ), ‖iteratedFDeriv ℝ 2 (η ∘ c) t‖ ≤ 3 / 2 * r ^ 2 := by
    intro t ht
    obtain ⟨p, hp, h2, h98, hpt⟩ := hband t ht
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact e.abs_iteratedDeriv_two_comp_geodesic_le hη (hc t ht) (hgeo t ht) hp (by linarith) hpt
      (hH p hp h2 h98) (hspeed t ht)
  have h := DifferentialGeometry.Analysis.abs_deriv_sub_chord_le hℓ hf hM
  have hderiv : deriv (fun t => (η (c t) - a) / r) x₀ = deriv (η ∘ c) x₀ / r := by
    rw [deriv_div_const, deriv_sub_const]
    rfl
  have hchord : ((η (c (x₀ + ℓ)) - a) / r - (η (c x₀) - a) / r) / ℓ =
      ((η ∘ c) (x₀ + ℓ) - (η ∘ c) x₀) / ℓ / r := by
    simp only [Function.comp]
    field_simp
    ring
  rw [hderiv, hchord, ← sub_div, abs_div, abs_of_pos hr, div_lt_iff₀ hr]
  have hrinv : r * γ⁻¹ ≤ γ ^ 2 / 2000 := by
    have hinvγ : γ * γ⁻¹ = 1 := mul_inv_cancel₀ hγ0.ne'
    calc r * γ⁻¹ ≤ γ ^ 3 / 2000 * γ⁻¹ := mul_le_mul_of_nonneg_right hrγ (by positivity)
      _ = γ ^ 2 / 2000 * (γ * γ⁻¹) := by ring
      _ = γ ^ 2 / 2000 := by rw [hinvγ, mul_one]
  have hγ2 : γ ^ 2 < γ := by nlinarith
  have hγ3 : γ ^ 3 < γ := by nlinarith
  have hsum : 3 / 4 * (r + r * γ⁻¹) < γ := by linarith
  calc |deriv (η ∘ c) x₀ - ((η ∘ c) (x₀ + ℓ) - (η ∘ c) x₀) / ℓ| ≤ 3 / 2 * r ^ 2 / 2 * ℓ := h
    _ ≤ 3 / 2 * r ^ 2 / 2 * (1 + γ⁻¹) := by gcongr
    _ = r * (3 / 4 * (r + r * γ⁻¹)) := by ring
    _ < r * γ := mul_lt_mul_of_pos_left hsum hr
    _ = γ * r := by ring

/-- **BCP02, image clause.** If `Δ = η − ζ` is `ε'`-Lipschitz on the `r⁻¹ d_g`-ball of radius
`R₁ ≥ 1` around `e q₀`, the vertical points `e(t₀, z₀ ± r(1 − γ/2))` lie in the unit ball and
`Φ = (η − η(e q₀))/r` takes values within `γ` of `±1` there (`r ≤ γ/2000`, `δ ≤ γ/1000`,
`ε' < γ/2`). -/
theorem CuspEmbedding.bcp02_image (e : CuspEmbedding W g K δ X)
    {η : W.Carrier → ℝ} {q₀ : CuspHalfSpace} (hq₀ : q₀ ∈ cuspDomain) {γ r ε' R₁ : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hr : 0 < r) (hrγ : r ≤ γ / 2000) (hδ0 : 0 ≤ δ)
    (hδγ : δ ≤ γ / 1000) (hz4 : 4 < q₀.2.val 0) (hz96 : q₀.2.val 0 < 96) (hε'0 : 0 ≤ ε')
    (hε'γ : ε' < γ / 2) (hR1 : 1 ≤ R₁)
    (hΔlip : ∀ x x' : W.Carrier, r⁻¹ * (riemannianEDistOf g x (e.toFun q₀)).toReal ≤ R₁ →
      r⁻¹ * (riemannianEDistOf g x' (e.toFun q₀)).toReal ≤ R₁ →
      |(η x - (invFunOn e.toFun cuspDomain x).2.val 0) -
          (η x' - (invFunOn e.toFun cuspDomain x').2.val 0)| ≤
        ε' * (riemannianEDistOf g x x').toReal) :
    ∃ xp xm : W.Carrier, r⁻¹ * (riemannianEDistOf g xp (e.toFun q₀)).toReal < 1 ∧
      r⁻¹ * (riemannianEDistOf g xm (e.toFun q₀)).toReal < 1 ∧
      |(η xp - η (e.toFun q₀)) / r - 1| < γ ∧ |(η xm - η (e.toFun q₀)) / r + 1| < γ := by
  set z₀ : ℝ := q₀.2.val 0 with hz₀
  set p₀ : W.Carrier := e.toFun q₀ with hp₀
  have hinv : ∀ p ∈ cuspDomain, invFunOn e.toFun cuspDomain (e.toFun p) = p :=
    fun p hp => e.injOn_cuspDomain.leftInvOn_invFunOn hp
  have hinv₀ : invFunOn e.toFun cuspDomain p₀ = q₀ := hinv q₀ hq₀
  have hp₀R : r⁻¹ * (riemannianEDistOf g p₀ p₀).toReal ≤ R₁ := by
    rw [riemannianEDistOf_self, ENNReal.toReal_zero, mul_zero]
    linarith
  have himg : ∀ s : ℝ, |s| = r * (1 - γ / 2) →
      r⁻¹ * (riemannianEDistOf g (e.toFun (q₀.1, halfSpaceOneLift (z₀ + s))) p₀).toReal < 1 ∧
        |(η (e.toFun (q₀.1, halfSpaceOneLift (z₀ + s))) - η p₀) / r - s / r| ≤ ε' := by
    intro s hs
    have hs0 : 0 ≤ |s| := abs_nonneg s
    have hsr : |s| < r := by
      rw [hs]
      nlinarith
    have hlo' : |s| < z₀ := by linarith
    have hup' : z₀ + |s| < 100 := by linarith
    set q : CuspHalfSpace := (q₀.1, halfSpaceOneLift (z₀ + s)) with hqdef
    have hqz : q.2.val 0 = z₀ + s := by
      change (halfSpaceOneLift (z₀ + s)).1 0 = _
      rw [halfSpaceOneLift_val_zero, max_eq_left]
      linarith [neg_abs_le s]
    have hq : q ∈ cuspDomain := by
      change q.2.val 0 < cuspDepth
      rw [hqz]
      have h := le_abs_self s
      change z₀ + s < 100
      linarith
    have hcov := e.riemannianEDistOf_lift_le (q₀ := q₀) q₀.1 hlo' hup'
    rw [riemannianEDistOf_self, ENNReal.toReal_zero, zero_pow (by norm_num), mul_zero,
      add_zero] at hcov
    have hle : (riemannianEDistOf g (e.toFun q) p₀).toReal ≤
        Real.sqrt ((1 + δ) * Real.exp |s| * s ^ 2) :=
      ENNReal.toReal_le_of_le_ofReal (Real.sqrt_nonneg _) hcov
    have hE := collarBCP_exp_mul_le |s|
    have hEp : 0 < Real.exp |s| := Real.exp_pos _
    have hfac : (1 + δ) * Real.exp |s| * (1 - γ / 2) ^ 2 < 1 := by
      have hsq : (1 - γ / 2) ^ 2 ≤ 1 - γ / 2 := by nlinarith
      have hA : 0 ≤ (1 - γ / 2) ^ 2 := sq_nonneg _
      have h1 : (1 + δ) * (1 - γ / 2) ^ 2 < 1 - |s| := by nlinarith
      have h2 : Real.exp |s| * ((1 + δ) * (1 - γ / 2) ^ 2) ≤ Real.exp |s| * (1 - |s|) :=
        mul_le_mul_of_nonneg_left h1.le hEp.le
      have h3 : (1 + δ) * Real.exp |s| * (1 - γ / 2) ^ 2 =
          Real.exp |s| * ((1 + δ) * (1 - γ / 2) ^ 2) := by ring
      have h4 : Real.exp |s| * ((1 + δ) * (1 - γ / 2) ^ 2) < Real.exp |s| * (1 - |s|) :=
        mul_lt_mul_of_pos_left h1 hEp
      linarith
    have hd : (riemannianEDistOf g (e.toFun q) p₀).toReal < r := by
      refine hle.trans_lt ?_
      rw [show r = Real.sqrt (r ^ 2) from (Real.sqrt_sq hr.le).symm]
      refine Real.sqrt_lt_sqrt (by positivity) ?_
      have hs2 : s ^ 2 = r ^ 2 * (1 - γ / 2) ^ 2 := by
        rw [← sq_abs, hs]
        ring
      rw [hs2]
      have hr2 : 0 < r ^ 2 := by positivity
      calc (1 + δ) * Real.exp |s| * (r ^ 2 * (1 - γ / 2) ^ 2)
          = r ^ 2 * ((1 + δ) * Real.exp |s| * (1 - γ / 2) ^ 2) := by ring
        _ < r ^ 2 * 1 := mul_lt_mul_of_pos_left hfac hr2
        _ = r ^ 2 := mul_one _
    have hdR : r⁻¹ * (riemannianEDistOf g (e.toFun q) p₀).toReal < 1 := by
      rw [inv_mul_lt_iff₀ hr, mul_one]
      exact hd
    refine ⟨hdR, ?_⟩
    have hlipq := hΔlip (e.toFun q) p₀ (hdR.le.trans hR1) hp₀R
    rw [hinv q hq, hinv₀, hqz] at hlipq
    have heq : (η (e.toFun q) - η p₀) / r - s / r =
        (η (e.toFun q) - (z₀ + s) - (η p₀ - z₀)) / r := by
      field_simp
      ring
    rw [heq, abs_div, abs_of_pos hr, div_le_iff₀ hr]
    calc |η (e.toFun q) - (z₀ + s) - (η p₀ - z₀)| ≤
          ε' * (riemannianEDistOf g (e.toFun q) p₀).toReal := hlipq
      _ ≤ ε' * r := mul_le_mul_of_nonneg_left hd.le hε'0
  have hγ2 : 0 ≤ 1 - γ / 2 := by linarith
  have hpos : |r * (1 - γ / 2)| = r * (1 - γ / 2) := abs_of_nonneg (by positivity)
  have hneg : |-(r * (1 - γ / 2))| = r * (1 - γ / 2) := by rw [abs_neg, hpos]
  obtain ⟨hp1, hp2⟩ := himg (r * (1 - γ / 2)) hpos
  obtain ⟨hm1, hm2⟩ := himg (-(r * (1 - γ / 2))) hneg
  refine ⟨_, _, hp1, hm1, ?_, ?_⟩
  · have h1 : r * (1 - γ / 2) / r = 1 - γ / 2 := by field_simp
    rw [h1] at hp2
    have := abs_le.mp hp2
    rw [abs_lt]
    constructor <;> linarith
  · have h1 : -(r * (1 - γ / 2)) / r = -(1 - γ / 2) := by field_simp
    rw [h1] at hm2
    have := abs_le.mp hm2
    rw [abs_lt]
    constructor <;> linarith

/-- **BCP02, coverage by exact frozen preimages.** If `Δ = η − ζ` is `ε'`-Lipschitz on the
`r⁻¹ d_g`-ball of radius `R₁ ≥ β⁻¹ + β`, every target point `(s, t)` within `β⁻¹ + β − β/4` of
`(0, t₀)` is `β/4`-close to the image of the point `e(t, z₀ + r s)` of the `(β⁻¹ + β)`-ball. -/
theorem CuspEmbedding.bcp02_coverage (e : CuspEmbedding W g K δ X)
    {η : W.Carrier → ℝ} {q₀ : CuspHalfSpace} (hq₀ : q₀ ∈ cuspDomain) {β r ε' ρ₁ R₁ : ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) (hr : 0 < r) (hδ0 : 0 ≤ δ) (hδβ : δ ≤ β ^ 2 / 1000)
    (hρ0 : 0 < ρ₁) (hρ : ρ₁ ≤ β ^ 2 / 1000) (hrR : r * (β⁻¹ + β) ≤ ρ₁)
    (hRle : β⁻¹ + β ≤ R₁) (hz4 : 4 < q₀.2.val 0) (hz96 : q₀.2.val 0 < 96) (hε'0 : 0 ≤ ε')
    (hε'b : ε' ≤ β ^ 2 / 500)
    (hΔlip : ∀ x x' : W.Carrier, r⁻¹ * (riemannianEDistOf g x (e.toFun q₀)).toReal ≤ R₁ →
      r⁻¹ * (riemannianEDistOf g x' (e.toFun q₀)).toReal ≤ R₁ →
      |(η x - (invFunOn e.toFun cuspDomain x).2.val 0) -
          (η x' - (invFunOn e.toFun cuspDomain x').2.val 0)| ≤
        ε' * (riemannianEDistOf g x x').toReal)
    (s : ℝ) (t : Torus)
    (hst : Real.sqrt (s ^ 2 + (r⁻¹ * Real.exp (-(q₀.2.val 0) / 2) *
      (riemannianEDistOf e.cusp.torusMetric t q₀.1).toReal) ^ 2) ≤ β⁻¹ + β - β / 4) :
    ∃ x : W.Carrier, r⁻¹ * (riemannianEDistOf g x (e.toFun q₀)).toReal ≤ β⁻¹ + β ∧
      Real.sqrt ((s - (η x - η (e.toFun q₀)) / r) ^ 2 + (r⁻¹ * Real.exp (-(q₀.2.val 0) / 2) *
        (riemannianEDistOf e.cusp.torusMetric t (invFunOn e.toFun cuspDomain x).1).toReal) ^ 2) <
        β / 4 := by
  set z₀ : ℝ := q₀.2.val 0 with hz₀
  set p₀ : W.Carrier := e.toFun q₀ with hp₀
  have hinv : ∀ p ∈ cuspDomain, invFunOn e.toFun cuspDomain (e.toFun p) = p :=
    fun p hp => e.injOn_cuspDomain.leftInvOn_invFunOn hp
  have hinv₀ : invFunOn e.toFun cuspDomain p₀ = q₀ := hinv q₀ hq₀
  have hR0 : 0 < β⁻¹ + β := by positivity
  have hp₀R : r⁻¹ * (riemannianEDistOf g p₀ p₀).toReal ≤ R₁ := by
    rw [riemannianEDistOf_self, ENNReal.toReal_zero, mul_zero]
    linarith
  have hinvβ : 1 < β⁻¹ := (one_lt_inv₀ hβ).mpr hβ1
  have hA0 : 0 ≤ s ^ 2 + (r⁻¹ * Real.exp (-z₀ / 2) *
      (riemannianEDistOf e.cusp.torusMetric t q₀.1).toReal) ^ 2 := by positivity
  have hsR : |s| ≤ β⁻¹ + β := by
    have h1 := Real.abs_le_sqrt (le_add_of_nonneg_right (sq_nonneg (r⁻¹ *
      Real.exp (-z₀ / 2) * (riemannianEDistOf e.cusp.torusMetric t q₀.1).toReal)) :
      s ^ 2 ≤ _)
    have h4 : 0 ≤ β / 4 := by positivity
    linarith
  have hrs : |r * s| ≤ r * (β⁻¹ + β) := by
    rw [abs_mul, abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left hsR hr.le
  have hrsρ : |r * s| ≤ ρ₁ := hrs.trans hrR
  have hρ1 : ρ₁ ≤ 1 / 1000 := by nlinarith
  have hlo' : |r * s| < z₀ := by linarith
  have hup' : z₀ + |r * s| < 100 := by linarith
  set q : CuspHalfSpace := (t, halfSpaceOneLift (z₀ + r * s)) with hqdef
  have hqz : q.2.val 0 = z₀ + r * s := by
    change (halfSpaceOneLift (z₀ + r * s)).1 0 = _
    rw [halfSpaceOneLift_val_zero, max_eq_left]
    linarith [neg_abs_le (r * s)]
  have hq : q ∈ cuspDomain := by
    change q.2.val 0 < cuspDepth
    rw [hqz]
    have h := le_abs_self (r * s)
    change z₀ + r * s < 100
    linarith
  have hdist : r⁻¹ * (riemannianEDistOf g (e.toFun q) p₀).toReal ≤ β⁻¹ + β := by
    have hcov := e.riemannianEDistOf_lift_le (q₀ := q₀) t hlo' hup'
    have hle : (riemannianEDistOf g (e.toFun q) p₀).toReal ≤
        Real.sqrt ((1 + δ) * Real.exp |r * s| * ((r * s) ^ 2 + Real.exp (-z₀) *
          (riemannianEDistOf e.cusp.torusMetric t q₀.1).toReal ^ 2)) :=
      ENNReal.toReal_le_of_le_ofReal (Real.sqrt_nonneg _) hcov
    have hexp : Real.exp (-z₀ / 2) ^ 2 = Real.exp (-z₀) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hbr : (r * s) ^ 2 + Real.exp (-z₀) *
        (riemannianEDistOf e.cusp.torusMetric t q₀.1).toReal ^ 2 =
        r ^ 2 * (s ^ 2 + (r⁻¹ * Real.exp (-z₀ / 2) *
          (riemannianEDistOf e.cusp.torusMetric t q₀.1).toReal) ^ 2) := by
      rw [mul_pow, mul_pow, mul_pow, hexp]
      field_simp
    rw [hbr] at hle
    have hA : s ^ 2 + (r⁻¹ * Real.exp (-z₀ / 2) *
        (riemannianEDistOf e.cusp.torusMetric t q₀.1).toReal) ^ 2 ≤
        (β⁻¹ + β - β / 4) ^ 2 := by
      have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hst 2
      rwa [Real.sq_sqrt hA0] at this
    obtain ⟨-, -, hC⟩ := collarBCP_budget (ρ' := |r * s|) hβ hβ1 hδ0 hδβ hρ0 hρ hrsρ
    have hroot : Real.sqrt ((1 + δ) * Real.exp |r * s| * (r ^ 2 * (s ^ 2 +
        (r⁻¹ * Real.exp (-z₀ / 2) *
          (riemannianEDistOf e.cusp.torusMetric t q₀.1).toReal) ^ 2))) ≤
        r * (β⁻¹ + β) := by
      rw [show r * (β⁻¹ + β) = Real.sqrt ((r * (β⁻¹ + β)) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      refine Real.sqrt_le_sqrt ?_
      have hE : 0 ≤ (1 + δ) * Real.exp |r * s| := by positivity
      calc (1 + δ) * Real.exp |r * s| * (r ^ 2 * (s ^ 2 + (r⁻¹ * Real.exp (-z₀ / 2) *
            (riemannianEDistOf e.cusp.torusMetric t q₀.1).toReal) ^ 2))
          = r ^ 2 * ((1 + δ) * Real.exp |r * s| * (s ^ 2 + (r⁻¹ * Real.exp (-z₀ / 2) *
            (riemannianEDistOf e.cusp.torusMetric t q₀.1).toReal) ^ 2)) := by ring
        _ ≤ r ^ 2 * ((1 + δ) * Real.exp |r * s| * (β⁻¹ + β - β / 4) ^ 2) := by gcongr
        _ ≤ r ^ 2 * (β⁻¹ + β) ^ 2 := by gcongr
        _ = (r * (β⁻¹ + β)) ^ 2 := by ring
    rw [inv_mul_le_iff₀ hr]
    exact hle.trans hroot
  refine ⟨e.toFun q, hdist, ?_⟩
  rw [hinv q hq, riemannianEDistOf_self, ENNReal.toReal_zero, mul_zero,
    zero_pow (by norm_num), add_zero, Real.sqrt_sq_eq_abs]
  have hlipq := hΔlip (e.toFun q) p₀ (hdist.trans hRle) hp₀R
  rw [hinv q hq, hinv₀, hqz] at hlipq
  have hdq : (riemannianEDistOf g (e.toFun q) p₀).toReal ≤ r * (β⁻¹ + β) := by
    rw [inv_mul_le_iff₀ hr] at hdist
    exact hdist
  have hkey : |r * s - (η (e.toFun q) - η p₀)| ≤ ε' * (r * (β⁻¹ + β)) := by
    have h1 : r * s - (η (e.toFun q) - η p₀) =
        -(η (e.toFun q) - (z₀ + r * s) - (η p₀ - z₀)) := by ring
    rw [h1, abs_neg]
    exact hlipq.trans (mul_le_mul_of_nonneg_left hdq hε'0)
  have heq : s - (η (e.toFun q) - η p₀) / r = (r * s - (η (e.toFun q) - η p₀)) / r := by
    field_simp
  rw [heq, abs_div, abs_of_pos hr, div_lt_iff₀ hr]
  have hβR : ε' * (β⁻¹ + β) < β / 4 := by
    have hinvβ' : β * β⁻¹ = 1 := mul_inv_cancel₀ hβ.ne'
    have h1 : ε' * (β⁻¹ + β) ≤ β ^ 2 / 500 * (β⁻¹ + β) :=
      mul_le_mul_of_nonneg_right hε'b hR0.le
    have h2 : β ^ 2 / 500 * (β⁻¹ + β) = β / 500 * (β * β⁻¹) + β ^ 3 / 500 := by ring
    rw [hinvβ', mul_one] at h2
    have h3 : β ^ 3 < β := by nlinarith
    linarith
  calc |r * s - (η (e.toFun q) - η p₀)| ≤ ε' * (r * (β⁻¹ + β)) := hkey
    _ = r * (ε' * (β⁻¹ + β)) := by ring
    _ < r * (β / 4) := mul_lt_mul_of_pos_left hβR hr
    _ = β / 4 * r := by ring

/-- The parameter bookkeeping of BCP02: for `0 < β < γ < 1`, `L ≥ 0`, `δ ≤ β²/1000`,
`0 < ε ≤ β²/1000`,
`0 < r ≤ β³/(2000(1 + L))`: `r (β⁻¹ + β + L) ≤ β²/1000`, `ε (1 − δ)⁻¹ ≤ β²/500`,
`r ≤ γ³/2000`, `r ≤ γ/2000`, `δ ≤ γ/1000`, `ε (1 − δ)⁻¹ < γ/2`. -/
theorem bcp02_parameters {β γ L r δ ε : ℝ} (hβ : 0 < β) (hβγ : β < γ) (hγ1 : γ < 1)
    (hL : 0 ≤ L) (hδβ : δ ≤ β ^ 2 / 1000) (hε : 0 < ε) (hεβ : ε ≤ β ^ 2 / 1000)
    (hr : 0 < r) (hrβ : r ≤ β ^ 3 / (2000 * (1 + L))) :
    r * (β⁻¹ + β + L) ≤ β ^ 2 / 1000 ∧ 0 < ε * (1 - δ)⁻¹ ∧ ε * (1 - δ)⁻¹ ≤ β ^ 2 / 500 ∧
      r ≤ γ ^ 3 / 2000 ∧ r ≤ γ / 2000 ∧ δ ≤ γ / 1000 ∧ ε * (1 - δ)⁻¹ < γ / 2 ∧
      δ < 3 / 4 ∧ 1 < β⁻¹ := by
  have hβ1 : β < 1 := hβγ.trans hγ1
  have hb2 : β ^ 2 < β := by nlinarith
  have hinvβ : 1 < β⁻¹ := (one_lt_inv₀ hβ).mpr hβ1
  have h1 : r * (1 + L) ≤ β ^ 3 / 2000 := by
    rw [le_div_iff₀ (by positivity)] at hrβ
    rw [le_div_iff₀ (by norm_num)]
    linarith only [hrβ]
  have h2 := collarSplit_scale_le hβ hβ1 h1
  have h3 : β⁻¹ + β + L ≤ (β⁻¹ + β) * (1 + L) := by nlinarith
  have hρ : r * (β⁻¹ + β + L) ≤ β ^ 2 / 1000 :=
    calc r * (β⁻¹ + β + L) ≤ r * ((β⁻¹ + β) * (1 + L)) := mul_le_mul_of_nonneg_left h3 hr.le
      _ = r * (1 + L) * (β⁻¹ + β) := by ring
      _ ≤ β ^ 2 / 1000 := h2
  have hδ1 : δ < 1 := by linarith only [hδβ, hb2, hβ1]
  have hε'0 : 0 < ε * (1 - δ)⁻¹ := mul_pos hε (inv_pos.mpr (by linarith only [hδ1]))
  have hinv2 : (1 - δ)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith only [hδ1]) (by norm_num)]
    linarith only [hδβ, hb2, hβ1]
  have hε'b : ε * (1 - δ)⁻¹ ≤ β ^ 2 / 500 :=
    calc ε * (1 - δ)⁻¹ ≤ (β ^ 2 / 1000) * 2 :=
          mul_le_mul hεβ hinv2 (inv_pos.mpr (by linarith only [hδ1])).le (by positivity)
      _ = β ^ 2 / 500 := by ring
  have hr3 : r ≤ β ^ 3 / 2000 := by
    have : r ≤ r * (1 + L) := by nlinarith
    linarith only [this, h1]
  have hβ3 : β ^ 3 ≤ γ ^ 3 := pow_le_pow_left₀ hβ.le hβγ.le 3
  have hβ3' : β ^ 3 < β := by nlinarith
  have hγa : r ≤ γ ^ 3 / 2000 := by linarith
  have hγb : r ≤ γ / 2000 := by linarith
  have hγc : δ ≤ γ / 1000 := by linarith
  have hγd : ε * (1 - δ)⁻¹ < γ / 2 := by linarith
  have hγe : δ < 3 / 4 := by linarith
  exact ⟨hρ, hε'0, hε'b, hγa, hγb, hγc, hγd, hγe, hinvβ⟩

/-- On the slab `|z − z₀| < 16ρ₁` (`4 < z₀ < 96`, `ρ₁ ≤ 1/1000`) the BCP01 bound on
`Δ = η − ζ` applies: `Δ` is differentiable and `|dΔ(v)| ≤ ε' |v|_g`. -/
theorem CuspEmbedding.bcp02_slab_derivative (e : CuspEmbedding W g K δ X) {η : W.Carrier → ℝ}
    (hη : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η) {ε' : ℝ}
    (hd : ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
      ∀ u : TangentSpace W.model (e.toFun p),
        |mvfderiv W.model (fun y => η y - (invFunOn e.toFun cuspDomain y).2.val 0)
            (e.toFun p) u| ≤ ε' * Real.sqrt (g.inner (e.toFun p) u u))
    {q₀ : CuspHalfSpace} {ρ₁ : ℝ} (hz4 : 4 < q₀.2.val 0) (hz96 : q₀.2.val 0 < 96)
    (hρ : ρ₁ ≤ 1 / 1000) :
    ∀ p ∈ cuspDomain, |p.2.val 0 - q₀.2.val 0| < 16 * ρ₁ →
      MDifferentiableAt W.model 𝓘(ℝ, ℝ)
          (fun y => η y - (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p) ∧
        ∀ v : TangentSpace W.model (e.toFun p),
          |mvfderiv W.model (fun y => η y - (invFunOn e.toFun cuspDomain y).2.val 0)
              (e.toFun p) v| ≤ ε' * Real.sqrt (g.inner (e.toFun p) v v) := by
  intro p hp hpz
  have hpz' := abs_lt.mp hpz
  have h2 : 2 ≤ p.2.val 0 := by linarith only [hpz'.1, hz4, hρ]
  have h98 : p.2.val 0 ≤ 98 := by linarith only [hpz'.2, hz96, hρ]
  refine ⟨?_, hd p hp h2 h98⟩
  exact ((hη (e.toFun p)).mdifferentiableAt (by simp)).sub
    ((e.contMDiffAt_height_of_pos hp (by linarith only [h2])).mdifferentiableAt (by simp))

/-- **Row BCP02** (one member of the boundary sequence). For `K ≥ 1`, `0 ≤ δ ≤ 1/1000` and
`0 < ε ≤ 1/1000` there is ONE smooth `η` (the BCP01 height, `|η − z| < ε` on the band) such that
for all `0 < β < γ < 1`, `L ≥ 0` with `δ, ε ≤ β²/1000`, every scale `0 < r ≤ β³/(2000(1 + L))`
and every band point `q₀` (`2 ≤ z₀ ≤ 98`) with `5 ≤ η(e q₀) ≤ 95`, writing
`Φ x = (η x − η(e q₀))/r`:
(BCP02.a) the rescaled carrier `(W, r⁻¹ d_g)` has a rank-one splitting at `e q₀` at scale `β`;
(BCP02.b, buffer `L`) `x ↦ (Φ x, t(x))` is `(1 ± β²/20)`-bi-Lipschitz into
`ℝ ×₂ (T², r⁻¹ e^{−z₀/2} d_{g_T})` on the ball of radius `β⁻¹ + β + L`;
(adapted, quality `γ`) `Φ` is `(1 + γ/2)`-Lipschitz on the unit ball; the chord test holds along
every geodesic segment of `g` in the band with `|c'|_g ≤ r` and `ℓ ≤ 1 + γ⁻¹`; there are points of
the unit ball with `Φ` within `γ` of `±1`; and `|Φ| < 1 + γ` on the unit ball. -/
theorem CuspEmbedding.bcp02 [ConnectedSpace W.Carrier] (e : CuspEmbedding W g K δ X)
    (hK : 1 ≤ K) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 1000) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 1000) :
    ∃ η : W.Carrier → ℝ, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η ∧
      (∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 → |η (e.toFun p) - p.2.val 0| < ε) ∧
      ∀ (β γ L r : ℝ) (q₀ : CuspHalfSpace) (hr : 0 < r), 0 < β → β < γ → γ < 1 → 0 ≤ L →
        δ ≤ β ^ 2 / 1000 → ε ≤ β ^ 2 / 1000 → r ≤ β ^ 3 / (2000 * (1 + L)) →
        2 ≤ q₀.2.val 0 → q₀.2.val 0 ≤ 98 → 5 ≤ η (e.toFun q₀) → η (e.toFun q₀) ≤ 95 →
        @HasEuclideanSplitting.{u, 0} W.Carrier
            ((inducedMetricSpace g).rescale r⁻¹ (inv_pos.mpr hr)) (e.toFun q₀) 1 β ∧
        (∀ x x' : W.Carrier,
          r⁻¹ * (riemannianEDistOf g x (e.toFun q₀)).toReal ≤ β⁻¹ + β + L →
          r⁻¹ * (riemannianEDistOf g x' (e.toFun q₀)).toReal ≤ β⁻¹ + β + L →
          (1 - β ^ 2 / 20) * (r⁻¹ * (riemannianEDistOf g x x').toReal) ≤
              Real.sqrt (((η x - η (e.toFun q₀)) / r - (η x' - η (e.toFun q₀)) / r) ^ 2 +
                (r⁻¹ * Real.exp (-(q₀.2.val 0) / 2) * (riemannianEDistOf e.cusp.torusMetric
                  (invFunOn e.toFun cuspDomain x).1
                  (invFunOn e.toFun cuspDomain x').1).toReal) ^ 2) ∧
            Real.sqrt (((η x - η (e.toFun q₀)) / r - (η x' - η (e.toFun q₀)) / r) ^ 2 +
                (r⁻¹ * Real.exp (-(q₀.2.val 0) / 2) * (riemannianEDistOf e.cusp.torusMetric
                  (invFunOn e.toFun cuspDomain x).1
                  (invFunOn e.toFun cuspDomain x').1).toReal) ^ 2) ≤
              (1 + β ^ 2 / 20) * (r⁻¹ * (riemannianEDistOf g x x').toReal)) ∧
        (∀ x x' : W.Carrier, r⁻¹ * (riemannianEDistOf g x (e.toFun q₀)).toReal < 1 →
          r⁻¹ * (riemannianEDistOf g x' (e.toFun q₀)).toReal < 1 →
          |(η x - η (e.toFun q₀)) / r - (η x' - η (e.toFun q₀)) / r| ≤
            (1 + γ / 2) * (r⁻¹ * (riemannianEDistOf g x x').toReal)) ∧
        (∀ (c : ℝ → W.Carrier) (x₀ ℓ : ℝ), 0 < ℓ → ℓ ≤ 1 + γ⁻¹ →
          (∀ t ∈ Icc x₀ (x₀ + ℓ), ContMDiffAt 𝓘(ℝ, ℝ) W.model 2 c t) →
          (∀ t ∈ Icc x₀ (x₀ + ℓ), HasGeodesicEquationAt g c t) →
          (∀ t ∈ Icc x₀ (x₀ + ℓ), ∃ p ∈ cuspDomain, 2 ≤ p.2.val 0 ∧ p.2.val 0 ≤ 98 ∧
            e.toFun p = c t) →
          (∀ t ∈ Icc x₀ (x₀ + ℓ), g.inner (c t)
            (mfderiv 𝓘(ℝ, ℝ) W.model c t ((NormedSpace.fromTangentSpace t).symm 1))
            (mfderiv 𝓘(ℝ, ℝ) W.model c t ((NormedSpace.fromTangentSpace t).symm 1)) ≤ r ^ 2) →
          |deriv (fun t => (η (c t) - η (e.toFun q₀)) / r) x₀ -
            ((η (c (x₀ + ℓ)) - η (e.toFun q₀)) / r - (η (c x₀) - η (e.toFun q₀)) / r) / ℓ| <
            γ) ∧
        (∃ xp xm : W.Carrier, r⁻¹ * (riemannianEDistOf g xp (e.toFun q₀)).toReal < 1 ∧
          r⁻¹ * (riemannianEDistOf g xm (e.toFun q₀)).toReal < 1 ∧
          |(η xp - η (e.toFun q₀)) / r - 1| < γ ∧ |(η xm - η (e.toFun q₀)) / r + 1| < γ) ∧
        ∀ x : W.Carrier, r⁻¹ * (riemannianEDistOf g x (e.toFun q₀)).toReal < 1 →
          |(η x - η (e.toFun q₀)) / r| < 1 + γ := by
  obtain ⟨η, -, -, -, hη, -, hb, -⟩ := e.bcp01 hK hδ0 hδ hε hε1
  refine ⟨η, hη, fun p hp h2 h98 => (hb p hp h2 h98).1, ?_⟩
  intro β γ L r q₀ hr hβ hβγ hγ1 hL hδβ hεβ hrβ hz2 hz98 hη5 hη95
  obtain ⟨hρ, hε'0, hε'b, hrγ3, hrγ, hδγ, hε'γ, hδ34, hinvβ⟩ :=
    bcp02_parameters hβ hβγ hγ1 hL hδβ hε hεβ hr hrβ
  have hβ1 : β < 1 := hβγ.trans hγ1
  have hγ0 : 0 < γ := hβ.trans hβγ
  have hq₀ : q₀ ∈ cuspDomain := cusp_mem_cuspDomain_of_le (by norm_num [cuspDepth]) hz98
  have hηz₀ := (hb q₀ hq₀ hz2 hz98).1
  set z₀ : ℝ := q₀.2.val 0 with hz₀
  set p₀ : W.Carrier := e.toFun q₀ with hp₀
  have hz4 : 4 < z₀ := by linarith only [(abs_lt.mp hηz₀).2, hη5, hεβ, hε1]
  have hz96 : z₀ < 96 := by linarith only [(abs_lt.mp hηz₀).1, hη95, hε1]
  set R₁ : ℝ := β⁻¹ + β + L with hR₁
  have hR₁0 : 0 < R₁ := by positivity
  set ρ₁ : ℝ := r * R₁ with hρ₁
  have hρ0 : 0 < ρ₁ := mul_pos hr hR₁0
  have hb1 : β ^ 2 < 1 := by nlinarith only [hβ, hβ1]
  have hρ1 : ρ₁ ≤ 1 / 1000 := le_trans hρ (by linarith only [hb1])
  set ε' : ℝ := ε * (1 - δ)⁻¹ with hε'
  have hε'40 : ε' ≤ β ^ 2 / 40 := le_trans hε'b (by linarith only [sq_nonneg β])
  have hΔ := e.bcp02_slab_derivative hη (fun p hp h2 h98 => (hb p hp h2 h98).2.1) hz4 hz96 hρ1
  have hinv : ∀ p ∈ cuspDomain, invFunOn e.toFun cuspDomain (e.toFun p) = p :=
    fun p hp => e.injOn_cuspDomain.leftInvOn_invFunOn hp
  have hs0 : 1 / 2 < Real.sqrt (1 - δ) := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith only [hδ34])
  have hball : ∀ y : W.Carrier, r⁻¹ * (riemannianEDistOf g y p₀).toReal ≤ R₁ →
      riemannianEDistOf g p₀ y < ENNReal.ofReal (Real.sqrt (1 - δ) * (4 * ρ₁ / 2)) := by
    intro y hy
    have hle : (riemannianEDistOf g y p₀).toReal ≤ ρ₁ := by
      rw [hρ₁]
      have := (inv_mul_le_iff₀ hr).mp hy
      linarith only [this]
    rw [riemannianEDistOf_comm, ← ENNReal.ofReal_toReal (riemannianEDistOf_ne_top g _ _)]
    refine (ENNReal.ofReal_lt_ofReal_iff (by nlinarith only [hs0, hρ0])).mpr ?_
    nlinarith only [hs0, hρ0, hle]
  have hup16 : z₀ + 16 * ρ₁ < cuspDepth := by
    have : z₀ + 16 * ρ₁ < 100 := by linarith only [hz96, hρ1]
    simpa [cuspDepth] using this
  have hΔlip : ∀ x x' : W.Carrier, r⁻¹ * (riemannianEDistOf g x p₀).toReal ≤ R₁ →
      r⁻¹ * (riemannianEDistOf g x' p₀).toReal ≤ R₁ →
      |(η x - (invFunOn e.toFun cuspDomain x).2.val 0) -
          (η x' - (invFunOn e.toFun cuspDomain x').2.val 0)| ≤
        ε' * (riemannianEDistOf g x x').toReal := fun x x' hx hx' =>
    e.abs_sub_le_mul_of_mvfderiv_le (f := fun y => η y - (invFunOn e.toFun cuspDomain y).2.val 0)
      hup16 hδ34 hε'0 hΔ (hball x hx) (hball x' hx')
  have hp₀R : r⁻¹ * (riemannianEDistOf g p₀ p₀).toReal ≤ R₁ := by
    rw [riemannianEDistOf_self, ENNReal.toReal_zero, mul_zero]
    exact hR₁0.le
  -- BCP02.b with the buffer
  have hbuf := fun x x' (hx : r⁻¹ * (riemannianEDistOf g x p₀).toReal ≤ R₁)
      (hx' : r⁻¹ * (riemannianEDistOf g x' p₀).toReal ≤ R₁) =>
    e.bcp02_distortion (η := η) hβ hβ1 hδβ hr hR₁0 hρ hz4 hz96 hε'0 hε'40 hΔ hx hx'
  -- the Lipschitz clause on the unit ball
  have hlip : ∀ x x' : W.Carrier, r⁻¹ * (riemannianEDistOf g x p₀).toReal < 1 →
      r⁻¹ * (riemannianEDistOf g x' p₀).toReal < 1 →
      |(η x - η p₀) / r - (η x' - η p₀) / r| ≤
        (1 + γ / 2) * (r⁻¹ * (riemannianEDistOf g x x').toReal) := by
    intro x x' hx hx'
    have hR1 : 1 ≤ R₁ := by linarith only [hinvβ, hβ, hL]
    obtain ⟨-, hup⟩ := hbuf x x' (hx.le.trans hR1) (hx'.le.trans hR1)
    have habs := Real.abs_le_sqrt (le_add_of_nonneg_right (sq_nonneg (r⁻¹ *
      Real.exp (-z₀ / 2) * (riemannianEDistOf e.cusp.torusMetric (invFunOn e.toFun cuspDomain x).1
        (invFunOn e.toFun cuspDomain x').1).toReal)) :
      ((η x - η p₀) / r - (η x' - η p₀) / r) ^ 2 ≤ _)
    have hd0 : 0 ≤ r⁻¹ * (riemannianEDistOf g x x').toReal :=
      mul_nonneg (inv_pos.mpr hr).le ENNReal.toReal_nonneg
    have hβγ' : β ^ 2 / 20 ≤ γ / 2 := by nlinarith only [hβ, hβ1, hβγ]
    calc _ ≤ _ := habs
      _ ≤ (1 + β ^ 2 / 20) * (r⁻¹ * (riemannianEDistOf g x x').toReal) := hup
      _ ≤ (1 + γ / 2) * (r⁻¹ * (riemannianEDistOf g x x').toReal) := by gcongr
  refine ⟨?_, hbuf, hlip, ?_, ?_, ?_⟩
  · -- BCP02.a: the splitting
    have hc : 0 < r⁻¹ * Real.exp (-z₀ / 2) := mul_pos (inv_pos.mpr hr) (Real.exp_pos _)
    have hinv₀ : invFunOn e.toFun cuspDomain p₀ = q₀ := hinv q₀ hq₀
    have hRle : β⁻¹ + β ≤ R₁ := by linarith only [hL]
    refine @hasEuclideanSplitting_of_coordinate_bounds W.Carrier
      ((inducedMetricSpace g).rescale r⁻¹ (inv_pos.mpr hr)) p₀ β (β ^ 2 / 20)
      (r⁻¹ * Real.exp (-z₀ / 2)) hβ hβ1 (by positivity) (by linarith only [hb1]) ?_ Torus
      (fun x => (η x - η p₀) / r) (fun x => (invFunOn e.toFun cuspDomain x).1)
      (fun t t' => (riemannianEDistOf e.cusp.torusMetric t t').toReal) (by simp) ?_ ?_ Torus
      ((inducedMetricSpace e.cusp.torusMetric).rescale _ hc) id surjective_id (fun _ _ => rfl)
    · have hinvβ' : β * β⁻¹ = 1 := mul_inv_cancel₀ hβ.ne'
      have h3 : β ^ 3 < β := by nlinarith only [hβ, hβ1, hb1]
      calc 2 * (β ^ 2 / 20) * (β⁻¹ + β) = β / 10 * (β * β⁻¹) + β ^ 3 / 10 := by ring
        _ = β / 10 + β ^ 3 / 10 := by rw [hinvβ', mul_one]
        _ < β / 4 := by linarith only [h3, hβ]
    · intro x x' hx hx'
      change r⁻¹ * (riemannianEDistOf g x p₀).toReal ≤ β⁻¹ + β at hx
      change r⁻¹ * (riemannianEDistOf g x' p₀).toReal ≤ β⁻¹ + β at hx'
      exact hbuf x x' (hx.trans hRle) (hx'.trans hRle)
    · intro s t hst
      change Real.sqrt (s ^ 2 + (r⁻¹ * Real.exp (-z₀ / 2) * (riemannianEDistOf e.cusp.torusMetric
        t (invFunOn e.toFun cuspDomain p₀).1).toReal) ^ 2) ≤ β⁻¹ + β - β / 4 at hst
      rw [hinv₀] at hst
      exact e.bcp02_coverage hq₀ hβ hβ1 hr hδ0 hδβ hρ0 hρ
        (mul_le_mul_of_nonneg_left hRle hr.le) hRle hz4 hz96 hε'0.le hε'b hΔlip s t hst
  · -- the chord test
    exact fun c x₀ ℓ hℓ hℓγ hc hgeo hband hspeed => e.bcp02_chord hη
      (fun p hp h2 h98 => (hb p hp h2 h98).2.2.2.2.2.1) hγ0 hγ1 hr hrγ3 c x₀ ℓ hℓ hℓγ hc hgeo
      hband hspeed
  · -- the image clause
    exact e.bcp02_image hq₀ hγ0 hγ1 hr hrγ hδ0 hδγ hz4 hz96 hε'0.le hε'γ
      (by linarith only [hinvβ, hβ, hL]) hΔlip
  · intro x hx
    have h := hlip x p₀ hx (by
      rw [riemannianEDistOf_self, ENNReal.toReal_zero, mul_zero]
      exact zero_lt_one)
    rw [sub_self, zero_div, sub_zero] at h
    have hd0 : 0 ≤ r⁻¹ * (riemannianEDistOf g x p₀).toReal :=
      mul_nonneg (inv_pos.mpr hr).le ENNReal.toReal_nonneg
    have : (1 + γ / 2) * (r⁻¹ * (riemannianEDistOf g x p₀).toReal) < 1 + γ := by
      nlinarith only [hd0, hx, hγ0]
    linarith only [h, this]

end DifferentialGeometry.Geometry.Collapse
