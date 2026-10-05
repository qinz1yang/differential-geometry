import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulTube
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.Completeness
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.SpeedBound
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.Homogeneity
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.FlowLemmas
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.Speed

/-!
# The gradient of the distance to a soul on its normal tube (lane CMS3-FLOW2, G2)

LFR46 (blueprint A:28926–28930, "in the calibrated tube `∇d_S` has norm one and pairs to `−1` with
the inward minimizing direction"), finite-order metric. Data: a normal tube `(ε, ψ)` of `S` in the
form of S3-TUBE (`exists_normalTube_finite`): `ψ x` is the unique normal vector of length `< ε` with
`exp (ψ x) = x`, calibrated `|ψ x| = d_S x`.

* `tubeGradField g S ψ x = d_S(x)⁻¹ · (geodesicFlow (ψ x) 1).snd`: the velocity at time `d_S x` of the
  unit normal geodesic through `x`. It is read off the geodesic flow, so no index is raised.
* `tubeGradField_radial`: unit normal rays `t ↦ exp (t • u)` (`0 < t < ε`) are calibrated and are
  integral curves of `tubeGradField`.
* `inner_tubeGradField_self`: `g(∇d_S, ∇d_S) = 1` on the punctured tube.
* `hasMFDerivAt_infDist_tubeGradField`: `d(d_S) = g(∇d_S, ·)` on the punctured tube (the
  derivative of `d_S` is `≤ |·|` because `d_S` is `1`-Lipschitz, and `= 1` on `∇d_S`; equality in
  the resulting Cauchy–Schwarz inequality).
* `inner_tubeGradField_le_neg_one`: `g(∇d_S, u) ≤ −1` for every unit minimizing direction `u` to `S`.
* `contMDiffOn_tubeGradField`: `∇d_S` is a `C^(r−1)` field on the punctured tube.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

/-! ### Real-variable lemmas -/

/-- A derivative at `0` is at most any right upper slope bound. -/
theorem le_of_hasDerivAt_of_eventually_le_add_mul {f : ℝ → ℝ} {a C : ℝ} (hf : HasDerivAt f a 0)
    (hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), f t ≤ f 0 + C * t) : a ≤ C := by
  refine le_of_tendsto hf.tendsto_slope_zero_right ?_
  filter_upwards [hle, self_mem_nhdsWithin] with t ht htpos
  have htpos' : (0 : ℝ) < t := htpos
  rw [zero_add, smul_eq_mul, inv_mul_le_iff₀ htpos']
  linarith

/-- **Equality case of Cauchy–Schwarz for a linear form.** If `L ≤ √B` (with `B` symmetric),
`B Z Z = 1` and `L Z = 1`, then `L = B Z`. -/
theorem eq_apply_of_le_sqrt_of_eq_one {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {B : F →L[ℝ] F →L[ℝ] ℝ} (hsym : ∀ u w, B u w = B w u) {L : F →L[ℝ] ℝ} {Z : F}
    (hZ : B Z Z = 1) (hLZ : L Z = 1) (hL : ∀ w, L w ≤ Real.sqrt (B w w)) (w : F) :
    L w = B Z w := by
  set q : ℝ → ℝ := fun t => 1 + 2 * B Z w * t + B w w * t ^ 2 with hqdef
  have hq : ∀ t : ℝ, B (Z + t • w) (Z + t • w) = q t := by
    intro t
    simp only [hqdef, map_add, map_smul, add_apply, smul_apply, smul_eq_mul, hZ, hsym w Z]
    ring
  set h : ℝ → ℝ := fun t => Real.sqrt (q t) - (1 + t * L w) with hhdef
  have hq0 : q 0 = 1 := by simp [hqdef]
  have hmin : IsLocalMin h 0 := by
    refine Filter.Eventually.of_forall fun t => ?_
    have ht := hL (Z + t • w)
    rw [map_add, map_smul, hLZ, hq, smul_eq_mul] at ht
    simp only [hhdef, hq0, Real.sqrt_one, zero_mul, add_zero, sub_self]
    linarith
  have hq' : HasDerivAt q (2 * B Z w) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => 2 * B Z w * t) (2 * B Z w) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (2 * B Z w)
    have h2 : HasDerivAt (fun t : ℝ => B w w * t ^ 2) 0 0 := by
      simpa using ((hasDerivAt_pow 2 (0 : ℝ)).const_mul (B w w))
    exact (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add h1).add h2).congr_deriv (by ring)
  have hsq : HasDerivAt (fun t => Real.sqrt (q t)) (2 * B Z w / (2 * Real.sqrt (q 0))) 0 :=
    hq'.sqrt (by rw [hq0]; norm_num)
  have hlin : HasDerivAt (fun t : ℝ => 1 + t * L w) (L w) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (L w)).const_add (1 : ℝ)
  have h0 := hmin.hasDerivAt_eq_zero (hsq.sub hlin)
  rw [hq0, Real.sqrt_one] at h0
  linarith

/-! ### The gradient field on the tube -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

omit [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M] in
/-- The metric does not see a propositional change of base point. -/
theorem inner_congr_base_tube {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) {x y : M} (h : x = y)
    (v w : E) : g.inner x v w = g.inner y v w := by
  subst h
  rfl

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M] in
/-- A point of `TM` is the pair of any base point equal to its projection and its vector. -/
theorem mk_snd_eq_of_proj_eq_tube (p : TangentBundle I M) {y : M} (h : p.proj = y) :
    (⟨y, p.snd⟩ : TangentBundle I M) = p := by
  obtain ⟨a, b⟩ := p
  subst h
  rfl

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M] in
/-- Chain rule for a real function along a curve with prescribed velocity. -/
theorem hasDerivAt_comp_curve_tube {γ : ℝ → M} {f : M → ℝ} {t : ℝ} {w : TangentSpace I (γ t)}
    {L : TangentSpace I (γ t) →L[ℝ] ℝ}
    (hγ : HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight w))
    (hf : HasMFDerivAt I 𝓘(ℝ, ℝ) f (γ t) L) :
    HasDerivAt (fun s => f (γ s)) (L w) t := by
  have h := hf.comp t hγ
  rw [hasMFDerivAt_iff_hasFDerivAt] at h
  have h2 : HasFDerivAt (fun s => f (γ s)) ((1 : ℝ →L[ℝ] ℝ).smulRight (L w)) t :=
    h.congr_fderiv (ContinuousLinearMap.ext_ring (by
      change L ((1 : ℝ →L[ℝ] ℝ).smulRight w 1) = (1 : ℝ →L[ℝ] ℝ).smulRight (L w) 1
      simp only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul]))
  simpa using h2.hasDerivAt

/-- **The gradient of `d_S` on the tube**: the velocity at time `d_S x` of the unit normal
geodesic ending at `x`. -/
def tubeGradField {n : ℕ∞ω} (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (S : Set M) (ψ : M → TangentBundle I M) (x : M) : TangentSpace I x :=
  (infDist x S)⁻¹ • ((g.geodesicFlow (ψ x) 1).snd : E)

omit [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M] in
/-- Normal vectors are stable under scaling. -/
theorem smul_mem_normalSetFinite_tube {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) {S : Set M} {s : M}
    {u : TangentSpace I s} (hu : (⟨s, u⟩ : TangentBundle I M) ∈ normalSetFinite g S) (t : ℝ) :
    (⟨s, t • u⟩ : TangentBundle I M) ∈ normalSetFinite g S := by
  refine ⟨hu.1, fun w hw => ?_⟩
  have h := hu.2 w hw
  change g.inner s (t • u) w = 0
  change g.inner s u w = 0 at h
  rw [map_smul, smul_apply, h, smul_zero]

/-- **Unit normal rays are calibrated integral curves of `∇d_S`.** For a unit normal `u` at
`s ∈ S` and `0 < t < ε`: `d_S (exp (t u)) = t`, `ψ (exp (t u)) = t u`, and the ray has velocity
`∇d_S` at time `t`. -/
theorem tubeGradField_radial
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} {ε : ℝ} {ψ : M → TangentBundle I M}
    (hψexp : ∀ v ∈ normalSetFinite g S, Real.sqrt (g.inner v.proj v.snd v.snd) < ε →
      ψ (g.expMap v) = v ∧ infDist (g.expMap v) S = Real.sqrt (g.inner v.proj v.snd v.snd))
    {s : M} {u : TangentSpace I s} (hu : (⟨s, u⟩ : TangentBundle I M) ∈ normalSetFinite g S)
    (hu1 : g.inner s u u = 1) {t : ℝ} (ht0 : 0 < t) (htε : t < ε) :
    infDist (g.expMap (⟨s, t • u⟩ : TangentBundle I M)) S = t ∧
      ψ (g.expMap (⟨s, t • u⟩ : TangentBundle I M)) = (⟨s, t • u⟩ : TangentBundle I M) ∧
      g.expMap (⟨s, t • u⟩ : TangentBundle I M) =
        (g.geodesicFlow (⟨s, u⟩ : TangentBundle I M) t).proj ∧
      HasMFDerivAt 𝓘(ℝ, ℝ) I (fun τ => g.expMap (⟨s, τ • u⟩ : TangentBundle I M)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (tubeGradField g S ψ (g.expMap (⟨s, t • u⟩ : TangentBundle I M)))) := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hdom : ∀ q, q ∈ g.geodesicFlowDomain := fun q => by
    rw [g.geodesicFlowDomain_eq_univ hr hnorm]; exact mem_univ q
  have hlen : Real.sqrt (g.inner s (t • u) (t • u)) = t := by
    rw [g.inner_smul_self_smul, hu1, mul_one, Real.sqrt_sq ht0.le]
  obtain ⟨hψt, hdt⟩ := hψexp (⟨s, t • u⟩ : TangentBundle I M)
    (smul_mem_normalSetFinite_tube g hu t) (by
      change Real.sqrt (g.inner s (t • u) (t • u)) < ε
      rw [hlen]; exact htε)
  change infDist _ S = Real.sqrt (g.inner s (t • u) (t • u)) at hdt
  rw [hlen] at hdt
  have hexp : ∀ τ : ℝ, g.expMap (⟨s, τ • u⟩ : TangentBundle I M) =
      (g.geodesicFlow (⟨s, u⟩ : TangentBundle I M) τ).proj := fun τ =>
    g.expMap_smul_eq_proj_geodesicFlow hr1 s u τ (hdom _)
  refine ⟨hdt, hψt, hexp t, ?_⟩
  have hfun : (fun τ => g.expMap (⟨s, τ • u⟩ : TangentBundle I M)) =
      fun τ => (g.geodesicFlow (⟨s, u⟩ : TangentBundle I M) τ).proj := funext hexp
  rw [hfun]
  have hder := g.hasMFDerivAt_geodesicFlow_proj hr1 (p := (⟨s, u⟩ : TangentBundle I M)) (t := t)
    (hdom _)
  refine hder.congr_mfderiv ?_
  congr 1
  symm
  -- the gradient at `exp (t u)` is the velocity of the ray
  have hsm := g.geodesicFlow_smul_eq hr1 (⟨s, u⟩ : TangentBundle I M) t 1 (hdom _)
  rw [mul_one] at hsm
  change (infDist (g.expMap (⟨s, t • u⟩ : TangentBundle I M)) S)⁻¹ •
      ((g.geodesicFlow (ψ (g.expMap (⟨s, t • u⟩ : TangentBundle I M))) 1).snd : E) =
    ((g.geodesicFlow (⟨s, u⟩ : TangentBundle I M) t).snd : E)
  rw [hψt, hdt]
  rw [hsm]
  change t⁻¹ • (t • ((g.geodesicFlow (⟨s, u⟩ : TangentBundle I M) t).snd : E)) = _
  rw [smul_smul, inv_mul_cancel₀ ht0.ne', one_smul]

omit [I.Boundaryless] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M] in
/-- The unit normal through a point of the punctured tube: `ψ x = d_S x • u`, `u` unit normal. -/
theorem exists_unit_normal_tube
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    {S : Set M} {ε : ℝ} {ψ : M → TangentBundle I M}
    (hψ : ∀ x, infDist x S < ε → ψ x ∈ normalSetFinite g S ∧ g.expMap (ψ x) = x ∧
      Real.sqrt (g.inner (ψ x).proj (ψ x).snd (ψ x).snd) = infDist x S)
    {x : M} (hx0 : 0 < infDist x S) (hxε : infDist x S < ε) :
    ∃ s : M, ∃ u : TangentSpace I s, (⟨s, u⟩ : TangentBundle I M) ∈ normalSetFinite g S ∧
      g.inner s u u = 1 ∧ g.expMap (⟨s, infDist x S • u⟩ : TangentBundle I M) = x ∧
      ψ x = (⟨s, infDist x S • u⟩ : TangentBundle I M) := by
  obtain ⟨hn, hexp, hlen⟩ := hψ x hxε
  set ρ := infDist x S with hρ
  set s := (ψ x).proj with hs
  set u : TangentSpace I s := ρ⁻¹ • (ψ x).snd with hu
  have hψu : (⟨s, ρ • u⟩ : TangentBundle I M) = ψ x := by
    rw [hu, smul_smul, mul_inv_cancel₀ hx0.ne', one_smul]
  have hnu : (⟨s, u⟩ : TangentBundle I M) ∈ normalSetFinite g S := by
    have h := smul_mem_normalSetFinite_tube g (S := S) (s := s) (u := (ψ x).snd) hn ρ⁻¹
    exact h
  have hq : g.inner s (ψ x).snd (ψ x).snd = ρ ^ 2 := by
    rw [← hlen, Real.sq_sqrt]
    by_cases h0 : (ψ x).snd = 0
    · rw [h0]; simp
    · exact (g.pos _ _ h0).le
  refine ⟨s, u, hnu, ?_, ?_, hψu.symm⟩
  · rw [hu, g.inner_smul_self_smul, hq, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hx0.ne')]
  · rw [hψu, hexp]

/-- **`g(∇d_S, ∇d_S) = 1`** on the punctured tube. -/
theorem inner_tubeGradField_self
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} {ε : ℝ} {ψ : M → TangentBundle I M}
    (hψ : ∀ x, infDist x S < ε → ψ x ∈ normalSetFinite g S ∧ g.expMap (ψ x) = x ∧
      Real.sqrt (g.inner (ψ x).proj (ψ x).snd (ψ x).snd) = infDist x S)
    {x : M} (hx0 : 0 < infDist x S) (hxε : infDist x S < ε) :
    g.inner x (tubeGradField g S ψ x) (tubeGradField g S ψ x) = 1 := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  obtain ⟨-, hexp, hlen⟩ := hψ x hxε
  have hdom : (ψ x, (1 : ℝ)) ∈ g.geodesicFlowDomain := by
    rw [g.geodesicFlowDomain_eq_univ hr hnorm]; exact mem_univ _
  have hspeed := g.inner_geodesicFlow_eq hr1 (ψ x) 1 hdom
  have hbase : (g.geodesicFlow (ψ x) 1).proj = x := hexp
  have hq : g.inner (ψ x).proj (ψ x).snd (ψ x).snd = infDist x S ^ 2 := by
    rw [← hlen, Real.sq_sqrt]
    by_cases h0 : (ψ x).snd = 0
    · rw [h0]; simp
    · exact (g.pos _ _ h0).le
  have hspeed' : g.inner x (g.geodesicFlow (ψ x) 1).snd (g.geodesicFlow (ψ x) 1).snd =
      infDist x S ^ 2 := ((inner_congr_base_tube g hbase.symm _ _).trans hspeed).trans hq
  unfold tubeGradField
  refine (g.inner_smul_self_smul x (infDist x S)⁻¹ (g.geodesicFlow (ψ x) 1).snd).trans ?_
  rw [hspeed', inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hx0.ne')]

/-- `d_S` has derivative at most `|w|` in every direction `w` (it is `1`-Lipschitz). -/
theorem hasMFDerivAt_infDist_apply_le
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (S : Set M) {x : M} {L : TangentSpace I x →L[ℝ] ℝ}
    (hL : HasMFDerivAt I 𝓘(ℝ, ℝ) (fun y => infDist y S) x L) (w : TangentSpace I x) :
    L w ≤ Real.sqrt (g.inner x w w) := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hdom : ∀ q, q ∈ g.geodesicFlowDomain := fun q => by
    rw [g.geodesicFlowDomain_eq_univ hr hnorm]; exact mem_univ q
  set p : TangentBundle I M := ⟨x, w⟩ with hp
  have hγ0 : (g.geodesicFlow p 0).proj = x := by rw [g.geodesicFlow_zero hr1]
  have hγ := g.hasMFDerivAt_geodesicFlow_proj hr1 (p := p) (t := 0) (hdom _)
  rw [g.geodesicFlow_zero hr1] at hγ
  have hL' : HasMFDerivAt I 𝓘(ℝ, ℝ) (fun y => infDist y S) (g.geodesicFlow p 0).proj L := by
    rw [hγ0]; exact hL
  have hd := hasDerivAt_comp_curve_tube hγ hL'
  refine le_of_hasDerivAt_of_eventually_le_add_mul hd ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (0 : ℝ) < t := ht
  change infDist (g.geodesicFlow p t).proj S ≤ infDist (g.geodesicFlow p 0).proj S +
    Real.sqrt (g.inner x w w) * t
  have hdist := g.dist_proj_geodesicFlow_le hr1 hnorm (p := p) (s := 0) (t := t)
    (fun τ _ => hdom _)
  rw [sub_zero] at hdist
  have htri := infDist_le_infDist_add_dist (x := (g.geodesicFlow p t).proj)
    (y := (g.geodesicFlow p 0).proj) (s := S)
  rw [dist_comm] at htri
  change dist _ _ ≤ Real.sqrt (g.inner x w w) * |t| at hdist
  rw [abs_of_pos ht'] at hdist
  linarith

/-- **`d(d_S) = g(∇d_S, ·)`** on the punctured tube. -/
theorem hasMFDerivAt_infDist_tubeGradField
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} {ε : ℝ} {ψ : M → TangentBundle I M}
    (hψ : ∀ x, infDist x S < ε → ψ x ∈ normalSetFinite g S ∧ g.expMap (ψ x) = x ∧
      Real.sqrt (g.inner (ψ x).proj (ψ x).snd (ψ x).snd) = infDist x S)
    (hψexp : ∀ v ∈ normalSetFinite g S, Real.sqrt (g.inner v.proj v.snd v.snd) < ε →
      ψ (g.expMap v) = v ∧ infDist (g.expMap v) S = Real.sqrt (g.inner v.proj v.snd v.snd))
    (hdS : ContMDiffOn I 𝓘(ℝ, ℝ) ((r - 1 : ℕ∞) : ℕ∞ω) (fun x => infDist x S)
      {x | 0 < infDist x S ∧ infDist x S < ε})
    {x : M} (hx0 : 0 < infDist x S) (hxε : infDist x S < ε) :
    HasMFDerivAt I 𝓘(ℝ, ℝ) (fun y => infDist y S) x (g.inner x (tubeGradField g S ψ x)) := by
  have hopen : IsOpen {x : M | 0 < infDist x S ∧ infDist x S < ε} :=
    (isOpen_lt continuous_const (continuous_infDist_pt S)).inter
      (isOpen_lt (continuous_infDist_pt S) continuous_const)
  have hdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => infDist y S) x :=
    ((hdS x ⟨hx0, hxε⟩).contMDiffAt (hopen.mem_nhds ⟨hx0, hxε⟩)).mdifferentiableAt
      (zero_lt_one.trans_le (one_le_coe_sub_one_tube hr)).ne'
  set L := mfderiv I 𝓘(ℝ, ℝ) (fun y => infDist y S) x with hLdef
  have hL : HasMFDerivAt I 𝓘(ℝ, ℝ) (fun y => infDist y S) x L := hdiff.hasMFDerivAt
  -- `L (∇d_S) = 1` along the normal ray through `x`
  obtain ⟨s, u, hnu, hu1, hxs, -⟩ := exists_unit_normal_tube g hψ hx0 hxε
  obtain ⟨-, -, -, hray⟩ := tubeGradField_radial g hr hnorm hψexp hnu hu1 hx0 hxε
  have hL2 : HasMFDerivAt I 𝓘(ℝ, ℝ) (fun y => infDist y S)
      (g.expMap (⟨s, infDist x S • u⟩ : TangentBundle I M)) L := by rw [hxs]; exact hL
  have hd := hasDerivAt_comp_curve_tube hray hL2
  have hid : HasDerivAt (fun τ => infDist (g.expMap
      (⟨s, τ • u⟩ : TangentBundle I M)) S) 1 (infDist x S) := by
    have hev : (fun τ => infDist (g.expMap (⟨s, τ • u⟩ : TangentBundle I M)) S)
        =ᶠ[𝓝 (infDist x S)] fun τ => τ := by
      filter_upwards [Ioo_mem_nhds hx0 hxε] with τ hτ
      exact (tubeGradField_radial g hr hnorm hψexp hnu hu1 hτ.1 hτ.2).1
    exact (hasDerivAt_id (infDist x S)).congr_of_eventuallyEq hev
  have hLZ : L (tubeGradField g S ψ x) = 1 := by
    have h := hd.unique hid
    rwa [hxs] at h
  have hZ := inner_tubeGradField_self g hr hnorm hψ hx0 hxε
  have heq : ∀ w : TangentSpace I x, L w = g.inner x (tubeGradField g S ψ x) w := fun w =>
    eq_apply_of_le_sqrt_of_eq_one (F := E) (B := g.inner x) (fun a b => g.symm x a b) hZ hLZ
      (fun v => hasMFDerivAt_infDist_apply_le g hr hnorm S hL v) w
  have hLeq : L = g.inner x (tubeGradField g S ψ x) := ContinuousLinearMap.ext heq
  rw [← hLeq]
  exact hL

/-- **`g(∇d_S, u) ≤ −1`** for every unit minimizing direction `u` to `S` at a point of the
punctured tube. -/
theorem inner_tubeGradField_le_neg_one
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} {ε : ℝ} {ψ : M → TangentBundle I M}
    (hψ : ∀ x, infDist x S < ε → ψ x ∈ normalSetFinite g S ∧ g.expMap (ψ x) = x ∧
      Real.sqrt (g.inner (ψ x).proj (ψ x).snd (ψ x).snd) = infDist x S)
    (hψexp : ∀ v ∈ normalSetFinite g S, Real.sqrt (g.inner v.proj v.snd v.snd) < ε →
      ψ (g.expMap v) = v ∧ infDist (g.expMap v) S = Real.sqrt (g.inner v.proj v.snd v.snd))
    (hdS : ContMDiffOn I 𝓘(ℝ, ℝ) ((r - 1 : ℕ∞) : ℕ∞ω) (fun x => infDist x S)
      {x | 0 < infDist x S ∧ infDist x S < ε})
    {q : M} (hq0 : 0 < infDist q S) (hqε : infDist q S < ε)
    {u : TangentSpace I q} (hu : u ∈ g.finiteMinimizingDirectionsTo S q) :
    g.inner q (tubeGradField g S ψ q) u ≤ -1 := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hdom : ∀ p, p ∈ g.geodesicFlowDomain := fun p => by
    rw [g.geodesicFlowDomain_eq_univ hr hnorm]; exact mem_univ p
  have hL := hasMFDerivAt_infDist_tubeGradField g hr hnorm hψ hψexp hdS hq0 hqε
  set p : TangentBundle I M := ⟨q, u⟩ with hp
  have hγ0 : (g.geodesicFlow p 0).proj = q := by rw [g.geodesicFlow_zero hr1]
  have hγ := g.hasMFDerivAt_geodesicFlow_proj hr1 (p := p) (t := 0) (hdom _)
  rw [g.geodesicFlow_zero hr1] at hγ
  have hL' : HasMFDerivAt I 𝓘(ℝ, ℝ) (fun y => infDist y S) (g.geodesicFlow p 0).proj
      (g.inner q (tubeGradField g S ψ q)) := by rw [hγ0]; exact hL
  have hd := hasDerivAt_comp_curve_tube hγ hL'
  refine le_of_hasDerivAt_of_eventually_le_add_mul hd ?_
  filter_upwards [Ioo_mem_nhdsGT hq0] with t ht
  rw [hγ0]
  have hend : (g.geodesicFlow p (infDist q S)).proj ∈ S := by
    have h := hu.2
    rw [g.expMap_smul_eq_proj_geodesicFlow hr1 q u (infDist q S) (hdom _)] at h
    exact h
  have hdist := g.dist_proj_geodesicFlow_le hr1 hnorm (p := p) (s := t) (t := infDist q S)
    (fun τ _ => hdom _)
  change dist _ _ ≤ Real.sqrt (g.inner q u u) * |infDist q S - t| at hdist
  rw [hu.1, Real.sqrt_one, one_mul, abs_of_pos (sub_pos.mpr ht.2)] at hdist
  have hle := infDist_le_dist_of_mem (x := (g.geodesicFlow p t).proj) hend
  linarith

/-- **`∇d_S` is a `C^(r−1)` field on the punctured tube.** -/
theorem contMDiffOn_tubeGradField
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} {ε : ℝ} {ψ : M → TangentBundle I M}
    (hψs : ContMDiffOn I I.tangent ((r - 1 : ℕ∞) : ℕ∞ω) ψ {x | infDist x S < ε})
    (hψ : ∀ x, infDist x S < ε → ψ x ∈ normalSetFinite g S ∧ g.expMap (ψ x) = x ∧
      Real.sqrt (g.inner (ψ x).proj (ψ x).snd (ψ x).snd) = infDist x S)
    (hdS : ContMDiffOn I 𝓘(ℝ, ℝ) ((r - 1 : ℕ∞) : ℕ∞ω) (fun x => infDist x S)
      {x | 0 < infDist x S ∧ infDist x S < ε}) :
    ContMDiffOn I I.tangent ((r - 1 : ℕ∞) : ℕ∞ω)
      (fun x => (⟨x, tubeGradField g S ψ x⟩ : TangentBundle I M))
      {x | 0 < infDist x S ∧ infDist x S < ε} := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hle : ((r - 1 : ℕ∞) : ℕ∞ω) ≤ (r : ℕ∞ω) := by exact_mod_cast tsub_le_self
  have hopen : IsOpen {x : M | 0 < infDist x S ∧ infDist x S < ε} :=
    (isOpen_lt continuous_const (continuous_infDist_pt S)).inter
      (isOpen_lt (continuous_infDist_pt S) continuous_const)
  have hopenT : IsOpen {x : M | infDist x S < ε} :=
    isOpen_lt (continuous_infDist_pt S) continuous_const
  intro x hx
  apply ContMDiffAt.contMDiffWithinAt
  have hψx : ContMDiffAt I I.tangent ((r - 1 : ℕ∞) : ℕ∞ω) ψ x :=
    (hψs x hx.2).contMDiffAt (hopenT.mem_nhds hx.2)
  have hflow : ContMDiff (I.tangent.prod 𝓘(ℝ, ℝ)) I.tangent (r : ℕ∞ω)
      (fun p : TangentBundle I M × ℝ => g.geodesicFlow p.1 p.2) := by
    have h := g.contMDiffOn_geodesicFlow hr1
    rw [g.geodesicFlowDomain_eq_univ hr hnorm, contMDiffOn_univ] at h
    exact h
  have hG : ContMDiffAt I I.tangent ((r - 1 : ℕ∞) : ℕ∞ω)
      (fun y => g.geodesicFlow (ψ y) 1) x :=
    (hflow.of_le hle).contMDiffAt.comp x (hψx.prodMk contMDiffAt_const)
  have hG' : ContMDiffAt I I.tangent ((r - 1 : ℕ∞) : ℕ∞ω)
      (fun y => (⟨y, ((g.geodesicFlow (ψ y) 1).snd : E)⟩ : TangentBundle I M)) x := by
    apply hG.congr_of_eventuallyEq
    filter_upwards [hopenT.mem_nhds hx.2] with y hy
    exact mk_snd_eq_of_proj_eq_tube _ (hψ y hy).2.1
  have hinv : ContMDiffAt I 𝓘(ℝ, ℝ) ((r - 1 : ℕ∞) : ℕ∞ω) (fun y => (infDist y S)⁻¹) x :=
    ((hdS x hx).contMDiffAt (hopen.mem_nhds hx)).inv₀ hx.1.ne'
  exact hinv.smul_section hG'

end DifferentialGeometry.Geometry.FiniteSoul
