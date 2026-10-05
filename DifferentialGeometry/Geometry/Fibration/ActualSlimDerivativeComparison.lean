import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsValueApplications
import DifferentialGeometry.Geometry.Fibration.RiemannianDerivativeTools
import DifferentialGeometry.Geometry.Collapse.SublevelCore.ScaledMinimizingDirections

/-!
# SGP03: binding the original derivative tests and model supports (actual LC87 packets)

Blueprint `master207B.tex`, SGP03 (`lem:fibration-slim-actual-affine-comparison`, B:4483–4600), on
the actual final family with LFR19's separate slim value tolerance `P : LocalChartPacketsRV … vs`.
Units: `L = 10⁶Δ`, `ℓ = 10⁵Δ`, `s_j = ρ(j)/ρ(i)`, `D_i = B(i, .95Lρ(i))`, `u_j = sgpRaw P.slim j`,
`η_j = (P.slim.centre j _).coord`.

* `abs_sub_le_of_form_saturation_SGP2`: FC15's Riesz step for a quadratic form (no inner product
  space on the tangent space): two covectors of size `≤ 1 + ε`, both `≥ 1 − ε` on one unit vector,
  differ by at most `(2ε + 12√ε)` times the form norm.
* `exists_rescaled_minimizing_SGP2`: ONE minimizing initial velocity from `x` to `y` serves every
  normalization `(R⁻¹d, R⁻²g)` (geodesics are scale invariant, `intrinsicGeodesic_radialScaled_eq`).
* `SlimCentre.test_phys_SGP2`: LFR19's long derivative test of a slim centre in physical units;
  `SlimCentre.abs_mvfderiv_le_SGP2`: the `(1 + σs)`-Lipschitz bound as a derivative bound.
* `sgp03_reference_lift_SGP2`: the lift `y` of `(u_i(x) + 10La, v_i(x))` (pointed distortion).
* `sgp03_derivative_SGP2`, `sgp03_model_support_SGP2`: the two pointwise clauses at one `x`.
* `sgp03_row` (SC): for `0 < θ < 1`, `0 < E < θ²/10⁶` there are thresholds `Lc, η₀` such that for
  EVERY actual RV family with `β 2 = β₂`, `β 1 ≤ η₀`, `Lc ≤ Lmax`, `10⁶ΔΛ < 10⁻⁵` and the (SB)
  budgets `0 < σs < θ²/10⁶`, `vs < θ/100`: every slim `i` and listed `j ∈ J_i` have ONE sign
  `a = ±1` with (RA), the derivative bound `|s_j dη_j(w) − a dη_i(w)| ≤ θ√(ρ(i)⁻² g(w, w))` on
  `D_i ∩ B(j, Lρ(j))`, the model-support enclosure `f(λ_j(η_i)/(s_jℓ)) ≠ 0 ⇒ x ∈ B(j, .91Lρ(j))` on
  `D_i`, and the values `|s_jη_j − λ_j(η_i)| < θ` on `D_i ∩ B(j, Lρ(j))`, `λ_j(t) = at + s_ju_j(i)`.

Not here: the zero coordinate (SGP03's last paragraph) — it needs SGP02's (R0) and LC67's global
difference-Lipschitz estimate on the actual zero packets (lane C14-ZERO's rows).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Kernel

/-- One functional of the saturation step: a covector of size `≤ (1 + ε)` that is `≥ 1 − ε` on a
unit vector `w` is `≤ 6√ε` on every `B`-orthogonal direction (`ε ≤ 1/2`). -/
theorem abs_apply_le_of_form_saturation_SGP2 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hsymm : ∀ v w, B v w = B w v) (hpos : ∀ v, 0 ≤ B v v)
    (f : V →L[ℝ] ℝ) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    (hf : ∀ z, |f z| ≤ (1 + ε) * Real.sqrt (B z z)) (w : V) (hw : B w w = 1)
    (hfw : 1 - ε ≤ f w) (u : V) (hu : B w u = 0) :
    |f u| ≤ 6 * Real.sqrt ε * Real.sqrt (B u u) := by
  set c := f u with hc
  set n2 := B u u with hn2
  have hn2pos : 0 ≤ n2 := hpos u
  -- the test vector `w + k c u`
  have key : ∀ k : ℝ, 0 < k → (1 - ε + k * c ^ 2) ^ 2 ≤ (1 + ε) ^ 2 * (1 + k ^ 2 * c ^ 2 * n2) := by
    intro k hk
    have hB : B (w + (k * c) • u) (w + (k * c) • u) = 1 + k ^ 2 * c ^ 2 * n2 := by
      simp only [map_add, map_smul, add_apply, smul_apply,
        smul_eq_mul]
      rw [hw, hu, hsymm u w, hu]
      ring
    have hfz : f (w + (k * c) • u) = f w + k * c ^ 2 := by
      rw [map_add, map_smul, smul_eq_mul, ← hc]
      ring
    have h1 := hf (w + (k * c) • u)
    rw [hB, hfz] at h1
    have h0 : 0 ≤ 1 - ε + k * c ^ 2 := by nlinarith [sq_nonneg c]
    have h2 : 1 - ε + k * c ^ 2 ≤ (1 + ε) * Real.sqrt (1 + k ^ 2 * c ^ 2 * n2) := by
      have := le_abs_self (f w + k * c ^ 2)
      linarith
    have hs := Real.sq_sqrt (show 0 ≤ 1 + k ^ 2 * c ^ 2 * n2 by positivity)
    calc (1 - ε + k * c ^ 2) ^ 2 ≤ ((1 + ε) * Real.sqrt (1 + k ^ 2 * c ^ 2 * n2)) ^ 2 :=
          pow_le_pow_left₀ h0 h2 2
      _ = (1 + ε) ^ 2 * (1 + k ^ 2 * c ^ 2 * n2) := by rw [mul_pow, hs]
  have hsq : c ^ 2 ≤ 36 * ε * n2 := by
    rcases hn2pos.eq_or_lt with h0 | hpos'
    · -- `B u u = 0`: then `k c² ≤ 2ε` for every `k > 0`, so `c = 0`
      rw [← h0]
      by_contra hne
      have hc2 : 0 < c ^ 2 := by simpa using not_le.mp hne
      have hk : 0 < (2 * ε + 1) / c ^ 2 := by positivity
      have h := key _ hk
      rw [← h0, mul_zero, add_zero, mul_one] at h
      have hkc : (2 * ε + 1) / c ^ 2 * c ^ 2 = 2 * ε + 1 := div_mul_cancel₀ _ hc2.ne'
      rw [hkc] at h
      nlinarith
    · set k := (1 - ε) / ((1 + ε) ^ 2 * n2) with hk
      have hden : 0 < (1 + ε) ^ 2 * n2 := by positivity
      have hkpos : 0 < k := div_pos (by linarith) hden
      have h := key k hkpos
      have hkn : (1 + ε) ^ 2 * k * n2 = 1 - ε := by
        rw [hk]; field_simp
      -- `(1 − ε) k c² ≤ 4ε`
      have h3 : (1 - ε) * k * c ^ 2 ≤ 4 * ε := by
        have e1 : (1 + ε) ^ 2 * (1 + k ^ 2 * c ^ 2 * n2) =
            (1 + ε) ^ 2 + ((1 + ε) ^ 2 * k * n2) * (k * c ^ 2) := by ring
        rw [e1, hkn] at h
        nlinarith [sq_nonneg (k * c ^ 2)]
      have h4 : (1 - ε) * k = (1 - ε) ^ 2 / ((1 + ε) ^ 2 * n2) := by
        rw [hk]; ring
      rw [h4, div_mul_eq_mul_div, div_le_iff₀ hden] at h3
      have h5 : (1 + ε) ^ 2 ≤ 9 * (1 - ε) ^ 2 := by nlinarith
      have h6 : 0 < (1 - ε) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h5 (show 0 ≤ 4 * ε * n2 by positivity)]
  have hr : Real.sqrt (c ^ 2) ≤ Real.sqrt (36 * ε * n2) := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq_eq_abs] at hr
  have he : Real.sqrt (36 * ε * n2) = 6 * Real.sqrt ε * Real.sqrt n2 := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num)]
    rw [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  linarith

/-- **The saturation step in a quadratic form** (FC15's Riesz calculation without an inner product
space): two covectors of size `≤ (1 + ε)` for the form `B`, both `≥ 1 − ε` on one `B`-unit vector,
differ by at most `(2ε + 12√ε)√(B z z)` at every `z` (`0 ≤ ε ≤ 1/2`). -/
theorem abs_sub_le_of_form_saturation_SGP2 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hsymm : ∀ v w, B v w = B w v) (hpos : ∀ v, 0 ≤ B v v)
    (f h : V →L[ℝ] ℝ) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    (hf : ∀ z, |f z| ≤ (1 + ε) * Real.sqrt (B z z))
    (hh : ∀ z, |h z| ≤ (1 + ε) * Real.sqrt (B z z)) (w : V) (hw : B w w = 1)
    (hfw : 1 - ε ≤ f w) (hhw : 1 - ε ≤ h w) (z : V) :
    |f z - h z| ≤ (2 * ε + 12 * Real.sqrt ε) * Real.sqrt (B z z) := by
  set t := B w z with ht
  set u := z - t • w with hu
  have hwu : B w u = 0 := by
    rw [hu, map_sub, map_smul, smul_eq_mul, hw, mul_one, ← ht, sub_self]
  have huu : B u u = B z z - t ^ 2 := by
    simp only [hu, map_sub, map_smul, sub_apply,
      smul_apply, smul_eq_mul]
    rw [hw, hsymm z w, ← ht]
    ring
  have hz : z = t • w + u := by rw [hu]; abel
  have hfu := abs_apply_le_of_form_saturation_SGP2 B hsymm hpos f hε hε1 hf w hw hfw u hwu
  have hhu := abs_apply_le_of_form_saturation_SGP2 B hsymm hpos h hε hε1 hh w hw hhw u hwu
  have hfw1 : f w ≤ 1 + ε := by
    have := hf w; rw [hw, Real.sqrt_one, mul_one] at this; linarith [le_abs_self (f w)]
  have hhw1 : h w ≤ 1 + ε := by
    have := hh w; rw [hw, Real.sqrt_one, mul_one] at this; linarith [le_abs_self (h w)]
  have hdiff : |f w - h w| ≤ 2 * ε := abs_le.mpr ⟨by linarith, by linarith⟩
  have hsplit : f z - h z = t * (f w - h w) + (f u - h u) := by
    conv_lhs => rw [hz]
    simp only [map_add, map_smul, smul_eq_mul]
    ring
  have hBz : 0 ≤ B z z := hpos z
  have ht2 : t ^ 2 ≤ B z z := by have := hpos u; linarith
  have hta : |t| ≤ Real.sqrt (B z z) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt ht2
  have hua : Real.sqrt (B u u) ≤ Real.sqrt (B z z) :=
    Real.sqrt_le_sqrt (by rw [huu]; nlinarith [sq_nonneg t])
  have hsε := Real.sqrt_nonneg ε
  rw [hsplit]
  calc |t * (f w - h w) + (f u - h u)| ≤ |t| * |f w - h w| + (|f u| + |h u|) := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul]
        exact add_le_add le_rfl (abs_sub _ _)
    _ ≤ Real.sqrt (B z z) * (2 * ε) +
          (6 * Real.sqrt ε * Real.sqrt (B z z) + 6 * Real.sqrt ε * Real.sqrt (B z z)) := by
        gcongr
        · exact hfu.trans (by gcongr)
        · exact hhu.trans (by gcongr)
    _ = (2 * ε + 12 * Real.sqrt ε) * Real.sqrt (B z z) := by ring

end Kernel

section Geodesic

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X]

/-- **One minimizing segment for every normalization.** Between two points of a closed manifold
with an aligned metric there is an initial velocity `v` (`g(v, v) = d(x, y)²`) whose intrinsic
geodesic reaches `y` at time `t` with velocity `c v` whenever `c t = 1`, for EVERY normalization
`(R⁻¹d, R⁻²g)` (constant scaling does not change the geodesics). -/
theorem exists_rescaled_minimizing_SGP2 (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) (x y : X) :
    ∃ v : TangentSpace 𝓘(ℝ, E3) x, g.inner x v v = dist x y ^ 2 ∧
      ∀ (R : ℝ) (hR : 0 < R),
        let hMc : CompleteSpace X := complete_of_compact
        letI := mX.rescale R⁻¹ (inv_pos.mpr hR)
        letI := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
        letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
          radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
        letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
          radialScaledManifold (m := mX) g hmetric R⁻¹ (inv_pos.mpr hR)
        letI : CompleteSpace X := (mX.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
        let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
          scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
        have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
        ∀ c t : ℝ, c * t = 1 → intrinsicGeodesic gR hnR x (c • v) t = y := by
  let hRB : RiemannianBundle (fun z : X => TangentSpace 𝓘(ℝ, E3) z) := ⟨g.toRiemannianMetric⟩
  have hRM : IsRiemannianManifold 𝓘(ℝ, E3) X := ⟨fun a b => by
    change edist a b = riemannianEDistOf g a b
    rw [edist_dist, hmetric]⟩
  have hcont : IsContinuousRiemannianBundle E3 (fun z : X => TangentSpace 𝓘(ℝ, E3) z) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have hEnorm : IsMetricNorm (I := 𝓘(ℝ, E3)) g := isMetricNorm_of_riemannianBundle g
  have hM : CompleteSpace X := complete_of_compact
  have hfin : riemannianEDist 𝓘(ℝ, E3) x y ≠ ⊤ := by
    rw [← IsRiemannianManifold.out (I := 𝓘(ℝ, E3)), edist_dist]
    exact ENNReal.ofReal_ne_top
  obtain ⟨v, hv, hlen⟩ :=
    hopf_rinow_expMapIntrinsic_surjective_minimizing_of_ne_top g hEnorm x y hfin
  have hdlen : (riemannianEDist 𝓘(ℝ, E3) x y).toReal = dist x y := by
    rw [← IsRiemannianManifold.out (I := 𝓘(ℝ, E3)), edist_dist, ENNReal.toReal_ofReal dist_nonneg]
  rw [hdlen] at hlen
  refine ⟨v, ?_, fun R hR => ?_⟩
  · rw [← hlen, Real.sq_sqrt (gInner_self_nonneg g x v)]
  · intro hMc gR hnR c t hct
    have h1 := intrinsicGeodesic_radialScaled_eq g hEnorm hR x (c • v)
    have h2 := intrinsicGeo_smul_apply g hEnorm x v c t
    have h3 : intrinsicGeodesic g hEnorm x v 1 = y := hv
    refine (congrFun h1 t).trans ?_
    rw [h2, hct]
    exact h3

end Geodesic

section Centre

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Δ σs : ℝ} {K : ℕ}

/-- `|A − U| < σ r` from the normalized form `|r⁻¹A − U/r| < σ`. -/
theorem abs_sub_lt_of_normalized_SGP2 {A U r σ : ℝ} (hr : 0 < r) (h : |r⁻¹ * A - U / r| < σ) :
    |A - U| < σ * r := by
  have he : r⁻¹ * A - U / r = (A - U) / r := by field_simp
  rw [he, abs_div, abs_of_pos hr, div_lt_iff₀ hr] at h
  exact h

/-- The slim coordinate is `(1 + σs)ρ(j)⁻¹`-Lipschitz for the physical distance. -/
theorem SlimCentre.abs_coord_sub_le_SGP2 {β₁ : ℝ} {j : X}
    (S : SlimCentre X g hmetric ρ hρ β₁ Δ σs K j) (hσs : 0 ≤ σs) (y z : X) :
    |S.coord y - S.coord z| ≤ (1 + σs) * (ρ j)⁻¹ * dist y z := by
  have hr := hρ j
  have hK : ((Real.toNNReal (1 + σs) : NNReal) : ℝ) = 1 + σs := Real.coe_toNNReal _ (by linarith)
  suffices h' : |S.coord y - S.coord z| ≤ (1 + σs) * ((ρ j)⁻¹ * dist y z) by
    calc |S.coord y - S.coord z| ≤ (1 + σs) * ((ρ j)⁻¹ * dist y z) := h'
      _ = (1 + σs) * (ρ j)⁻¹ * dist y z := by ring
  let P := S.packet
  let iZ := S.instZ
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr hr)
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr hr)
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr hr)
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr hr)
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr hr)).mpr hMc
  have h := P.lipschitz.dist_le_mul y z
  rw [hK, Real.dist_eq] at h
  exact h

/-- The derivative of the slim coordinate is bounded by `(1 + σs)√(ρ(j)⁻² g)` on
`B(j, 10⁶Δρ(j))`. -/
theorem SlimCentre.abs_mvfderiv_le_SGP2 {β₁ : ℝ} {j : X}
    (S : SlimCentre X g hmetric ρ hρ β₁ Δ σs K j) (hσs : 0 ≤ σs) {x : X}
    (hx : x ∈ ball j (10 ^ 6 * Δ * ρ j)) (z : TangentSpace 𝓘(ℝ, E3) x) :
    |mvfderiv 𝓘(ℝ, E3) S.coord x z| ≤ (1 + σs) * (ρ j)⁻¹ * Real.sqrt (g.inner x z z) := by
  have hdiff : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) S.coord x :=
    (S.contMDiffOn_coord.contMDiffAt (isOpen_ball.mem_nhds hx)).mdifferentiableAt (by simp)
  have hM : CompleteSpace X := complete_of_compact
  exact abs_mvfderiv_le_of_lipschitzOn_riem g hmetric isOpen_ball hx hdiff
    (fun y _ z _ => S.abs_coord_sub_le_SGP2 hσs y z) z

/-- **The original long derivative test of a slim centre, in physical form.** For `x ∈ B(j, Lρ(j))`,
`y ∈ B(j, (L/σs)ρ(j))` with `d(x, y) > Lρ(j)` and a minimizing initial velocity `v` from `x` to `y`
(for the normalization at `j`, as produced by `exists_rescaled_minimizing_SGP2`):
`|dη_j(v) − (u_j(y) − u_j(x))| < σs ρ(j)⁻¹ d(x, y)`. -/
theorem SlimCentre.test_phys_SGP2 {β₁ : ℝ} {j : X} (S : SlimCentre X g hmetric ρ hρ β₁ Δ σs K j)
    {x y : X} (hx : x ∈ ball j (10 ^ 6 * Δ * ρ j)) (hy : y ∈ ball j (10 ^ 6 * Δ / σs * ρ j))
    (hxy : 10 ^ 6 * Δ * ρ j < dist x y) {v : TangentSpace 𝓘(ℝ, E3) x}
    (hvv : g.inner x v v = dist x y ^ 2)
    (hgeo : let hMc : CompleteSpace X := complete_of_compact
      letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
        radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
        radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : CompleteSpace X :=
        (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
      let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
        scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) g
      have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
      ∀ c t : ℝ, c * t = 1 → intrinsicGeodesic gR hnR x (c • v) t = y) :
    |mvfderiv 𝓘(ℝ, E3) S.coord x v - ((sgpSplitMap S y).fst - (sgpSplitMap S x).fst)| <
      σs * ((ρ j)⁻¹ * dist x y) := by
  have hr := hρ j
  have hL : 0 < 10 ^ 6 * Δ * ρ j := pos_of_mem_ball hx
  have hx' : (ρ j)⁻¹ * dist x j < 10 ^ 6 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 hr hx
  have hy' : (ρ j)⁻¹ * dist y j < 10 ^ 6 * Δ / σs := inv_mul_dist_lt_of_mem_ball_LC87 hr hy
  have hxy' : 10 ^ 6 * Δ < (ρ j)⁻¹ * dist x y := by
    rw [lt_inv_mul_iff₀ hr]
    linarith
  have hd : 0 < dist x y := hL.trans hxy
  set d := dist x y with hddef
  set r := (ρ j)⁻¹ * d with hrdef
  have hrpos : 0 < r := by positivity
  have hct : ρ j / d * r = 1 := by rw [hrdef]; field_simp
  have hcr : ρ j / d = r⁻¹ := by rw [hrdef]; field_simp
  have hw1 : (ρ j)⁻¹ ^ 2 * g.inner x ((ρ j / d) • v) ((ρ j / d) • v) = 1 := by
    rw [gInner_smul_self, hvv]
    field_simp
  have hsm : mvfderiv 𝓘(ℝ, E3) S.coord x ((ρ j / d) • v) =
      r⁻¹ * mvfderiv 𝓘(ℝ, E3) S.coord x v := by
    rw [map_smul, smul_eq_mul, hcr]
  suffices hT' : |mvfderiv 𝓘(ℝ, E3) S.coord x ((ρ j / d) • v) -
      ((sgpSplitMap S y).fst - (sgpSplitMap S x).fst) / r| < σs by
    rw [hsm] at hT'
    exact abs_sub_lt_of_normalized_SGP2 hrpos hT'
  let P := S.packet
  let iZ := S.instZ
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr hr)
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr hr)
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr hr)
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr hr)
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr hr)).mpr hMc
  let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
    scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr hr) 2) g
  have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
  have hxR : x ∈ ball j (10 ^ 6 * Δ) := hx'
  have hyR : y ∈ ball j (10 ^ 6 * Δ / σs) := hy'
  have hxyR : 10 ^ 6 * Δ < dist x y := hxy'
  have hw : gR.inner x ((ρ j / d) • v) ((ρ j / d) • v) = 1 := by
    rw [scaleMetric_inner]
    exact hw1
  have hg : intrinsicGeodesic gR hnR x ((ρ j / d) • v) (dist x y) = y := hgeo _ _ hct
  exact P.test x hxR y hyR hxyR _ hw hg

end Centre


section Arithmetic

/-- The ratio estimate of SGP03: for `D < r < D + 4δ` and `0 ≤ c ≤ 2E`,
`(D + δ − c)/r ≥ 1 − (3δ + 2E)/D`. -/
theorem sgp03_ratio_SGP2 {D r δ E c : ℝ} (hD : 0 < D) (hr1 : D < r) (hr2 : r < D + 4 * δ)
    (hc0 : 0 ≤ c) (hc : c ≤ 2 * E) : 1 - (3 * δ + 2 * E) / D ≤ (D + δ - c) / r := by
  have hr : 0 < r := hD.trans hr1
  have hδ : 0 ≤ δ := by linarith
  have e1 : (D + δ - c) / r = 1 - (r - D - δ + c) / r := by field_simp; ring
  have h1 : (r - D - δ + c) / r ≤ (3 * δ + c) / r :=
    div_le_div_of_nonneg_right (by linarith) hr.le
  have h2 : (3 * δ + c) / r ≤ (3 * δ + c) / D :=
    div_le_div_of_nonneg_left (by linarith) hD hr1.le
  have h3 : (3 * δ + c) / D ≤ (3 * δ + 2 * E) / D :=
    div_le_div_of_nonneg_right (by linarith) hD.le
  rw [e1]
  linarith

/-- SGP03, reference chart: `a dη_i(w) ≥ 1 − ε` on the normalized unit vector `w = r⁻¹ v`. -/
theorem sgp03_lower_i_SGP2 {A U a r σ δ E D : ℝ} (ha : a = 1 ∨ a = -1) (hD : 0 < D)
    (hr1 : D < r) (hr2 : r < D + 4 * δ) (hE : 0 ≤ E) (hT : |A - U| < σ * r)
    (hV : D + δ < a * U) : 1 - (σ + (3 * δ + 2 * E) / D) ≤ a * (r⁻¹ * A) := by
  have hr : 0 < r := hD.trans hr1
  have haA : a * U - σ * r < a * A := by
    have he : a * A = a * U + a * (A - U) := by ring
    have hb : |a * (A - U)| < σ * r := by
      have hab : |a * (A - U)| = |A - U| := by
        rw [abs_mul]
        rcases ha with rfl | rfl <;> norm_num
      rw [hab]
      exact hT
    rw [he]
    linarith [neg_abs_le (a * (A - U))]
  have hq := sgp03_ratio_SGP2 (E := E) (c := 0) hD hr1 hr2 le_rfl (by linarith)
  have hdiv : (D + δ - 0) / r ≤ (a * A + σ * r) / r :=
    div_le_div_of_nonneg_right (by linarith) hr.le
  have he2 : (a * A + σ * r) / r = a * (r⁻¹ * A) + σ := by field_simp
  linarith

/-- SGP03, listed chart: `s_j dη_j(w) ≥ 1 − ε` on the same vector, through the raw alignment. -/
theorem sgp03_lower_j_SGP2 {A U W s r σ δ E D : ℝ} (hs : 0 < s) (hD : 0 < D) (hr1 : D < r)
    (hr2 : r < D + 4 * δ) (hT : |A - U| < σ * (r / s)) (hRA : |s * U - W| < 2 * E)
    (hV : D + δ < W) : 1 - (σ + (3 * δ + 2 * E) / D) ≤ s * (r⁻¹ * A) := by
  have hr : 0 < r := hD.trans hr1
  have hE : 0 ≤ E := by linarith [abs_nonneg (s * U - W)]
  have hsA : s * U - σ * r < s * A := by
    have h := (abs_lt.mp hT).1
    have h' : s * (-(σ * (r / s))) < s * (A - U) := mul_lt_mul_of_pos_left h hs
    have hrs : s * (σ * (r / s)) = σ * r := by field_simp
    nlinarith
  have hsU : D + δ - 2 * E < s * U := by linarith [(abs_lt.mp hRA).1]
  have hq := sgp03_ratio_SGP2 (c := 2 * E) hD hr1 hr2 (by linarith) le_rfl
  have hdiv : (D + δ - 2 * E) / r ≤ (s * A + σ * r) / r :=
    div_le_div_of_nonneg_right (by linarith) hr.le
  have he2 : (s * A + σ * r) / r = s * (r⁻¹ * A) + σ := by field_simp
  linarith

/-- SGP03's budget (SB): `ε = σ + (3δ + 2E)/(10L − 2δ)` is at most `1/2` and
`2ε + 12√ε ≤ θ`. -/
theorem sgp03_budget_SGP2 {σ δ E L θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hσ0 : 0 ≤ σ)
    (hσ : σ < θ ^ 2 / 10 ^ 6) (hδ0 : 0 ≤ δ) (hδ : δ < θ ^ 2 / 10 ^ 6) (hE0 : 0 ≤ E)
    (hE : E < θ ^ 2 / 10 ^ 6) (hL : 1000000 ≤ L) :
    0 ≤ σ + (3 * δ + 2 * E) / (10 * L - 2 * δ) ∧ σ ≤ σ + (3 * δ + 2 * E) / (10 * L - 2 * δ) ∧
      σ + (3 * δ + 2 * E) / (10 * L - 2 * δ) ≤ 1 / 2 ∧
      2 * (σ + (3 * δ + 2 * E) / (10 * L - 2 * δ)) +
        12 * Real.sqrt (σ + (3 * δ + 2 * E) / (10 * L - 2 * δ)) ≤ θ := by
  have hθ2 : θ ^ 2 < θ := by nlinarith
  have hden : 1 ≤ 10 * L - 2 * δ := by nlinarith
  have hq0 : 0 ≤ (3 * δ + 2 * E) / (10 * L - 2 * δ) := div_nonneg (by linarith) (by linarith)
  have hq : (3 * δ + 2 * E) / (10 * L - 2 * δ) ≤ 3 * δ + 2 * E := div_le_self (by linarith) hden
  set ε := σ + (3 * δ + 2 * E) / (10 * L - 2 * δ) with hε
  have hεθ : ε < θ ^ 2 / 2500 := by nlinarith
  have hsq : Real.sqrt ε < θ / 50 := by
    rw [Real.sqrt_lt' (by positivity)]
    nlinarith
  refine ⟨by linarith, by linarith, by nlinarith, by nlinarith⟩

/-- Ball comparison: `k L ρ ≤ k' L ρ` for `k ≤ k'`, `L, ρ ≥ 0`. -/
theorem mul_mul_le_mul_mul_SGP2 {k k' L ρ : ℝ} (hk : k ≤ k') (hL : 0 ≤ L) (hρ : 0 ≤ ρ) :
    k * L * ρ ≤ k' * L * ρ :=
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk hL) hρ

/-- The tested ball of a chart of scale ratio `≤ 1.01` is passed: `Lρ_j < ρ_i r` for
`r > 10L − 2δ`. -/
theorem sgp03_num_far_SGP2 {L ρi ρj r δ : ℝ} (hL : 1000000 ≤ L) (hδ1 : δ < 1) (hri : 0 < ρi)
    (hji : ρj ≤ 101 / 100 * ρi) (hr1 : 10 * L - 2 * δ < r) : L * ρj < ρi * r := by
  have h1 : L * ρj ≤ L * (101 / 100 * ρi) := mul_le_mul_of_nonneg_left hji (by linarith)
  have h2 : L * (101 / 100 * ρi) < ρi * r := by
    have : 101 / 100 * L < r := by linarith
    nlinarith
  linarith

/-- The outer tested radius: `k L ≤ L/σ` for `σ k ≤ 1`. -/
theorem sgp03_num_outer_SGP2 {L σ k : ℝ} (hL : 0 ≤ L) (hσ : 0 < σ) (hσk : σ * k ≤ 1) :
    k * L ≤ L / σ := by
  rw [le_div_iff₀ hσ]
  nlinarith

/-- The lift stays within `24Lρ_j` of `j`. -/
theorem sgp03_num_lift_SGP2 {L ρi ρj a b : ℝ} (hL : 0 < L) (hri : 0 < ρi)
    (hij : ρi < 100 / 99 * ρj) (ha : a < 21 * L * ρi) (hb : b < 2 * L * ρi) :
    a + b < 24 * L * ρj := by
  have h : 23 * L * ρi < 24 * L * ρj := by nlinarith
  linarith

end Arithmetic

section Reference

/-- Points of `A × Z` with the same second component are as far apart as their first ones. -/
theorem dist_toLp_same_snd_SGP2 {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    (u v : α) (y : β) :
    dist (WithLp.toLp 2 (u, y)) (WithLp.toLp 2 (v, y)) = dist u v := by
  rw [WithLp.prod_dist_eq_add (by norm_num)]
  have h2 : (2 : ENNReal).toReal = 2 := by norm_num
  have hf : (WithLp.toLp 2 (u, y)).fst = u := rfl
  have hf' : (WithLp.toLp 2 (v, y)).fst = v := rfl
  have hs : (WithLp.toLp 2 (u, y)).snd = y := rfl
  have hs' : (WithLp.toLp 2 (v, y)).snd = y := rfl
  rw [h2, hf, hf', hs, hs', dist_self, Real.zero_rpow (by norm_num), add_zero,
    ← Real.rpow_mul dist_nonneg]
  norm_num

/-- The `L²` product distance is at most the sum of the component distances. -/
theorem dist_le_fst_add_snd_SGP2 {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    (x y : WithLp 2 (α × β)) : dist x y ≤ dist x.fst y.fst + dist x.snd y.snd := by
  rw [WithLp.prod_dist_eq_add (by norm_num)]
  have h2 : (2 : ENNReal).toReal = 2 := by norm_num
  rw [h2]
  have ha := dist_nonneg (x := x.fst) (y := y.fst)
  have hb := dist_nonneg (x := x.snd) (y := y.snd)
  rw [← Real.sqrt_eq_rpow, Real.rpow_two, Real.rpow_two, Real.sqrt_le_left (by positivity)]
  nlinarith

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}

/-- **The reference lift of SGP03.** For `x ∈ D_i` and a sign `a`, a lift `y ∈ B(i, 21Lρ(i))` of
`(u_i(x) + 10La, v_i(x))` (error `< δ`) has `|ρ(i)⁻¹d(x, y) − 10L| < 2δ` and
`a(u_i(y) − u_i(x)) > 10L − δ`. -/
theorem sgp03_reference_lift_SGP2 (S : SlimFamily X g hmetric ρ hρ β Δ σs K) {δ : ℝ}
    (hΔ : 1 ≤ Δ) (hδ1 : δ < 1) (hβ : β 1 ≤ min (1 / (1000 * (1000000 * Δ))) (δ / 100)) {i : X}
    (hi : i ∈ S.centres) {x : X} (hx : x ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i)) {a : ℝ}
    (ha : a = 1 ∨ a = -1) :
    ∃ y ∈ ball i (21 * (1000000 * Δ) * ρ i),
      |(ρ i)⁻¹ * dist x y - 10 * (1000000 * Δ)| < 2 * δ ∧
      10 * (1000000 * Δ) - δ < a * (sgpRaw S i y - sgpRaw S i x) := by
  have hri := hρ i
  have hΔ0 : 0 < Δ := by linarith
  have hL0 : 0 < 1000000 * Δ * ρ i := by positivity
  obtain ⟨-, hdist, hlift⟩ := sgp02_reference_tests S hΔ hβ hi
  let iZ := (S.centre i hi).instZ
  set F := sgpSplitMap (S.centre i hi) with hF
  have hdist' : ∀ x ∈ ball i (100 * (1000000 * Δ) * ρ i),
      ∀ x' ∈ ball i (100 * (1000000 * Δ) * ρ i),
      |dist (F x) (F x') - (ρ i)⁻¹ * dist x x'| ≤ δ := hdist
  have hlift' : ∀ y, dist y (F i) < 20 * (1000000 * Δ) →
      ∃ x ∈ ball i (21 * (1000000 * Δ) * ρ i), dist y (F x) < δ := hlift
  have hx100 : x ∈ ball i (100 * (1000000 * Δ) * ρ i) := ball_subset_ball (by nlinarith) hx
  have hi100 : i ∈ ball i (100 * (1000000 * Δ) * ρ i) := mem_ball_self (by positivity)
  have hxi := hdist' x hx100 i hi100
  have hxi' : (ρ i)⁻¹ * dist x i < 95 / 100 * (1000000 * Δ) :=
    inv_mul_dist_lt_of_mem_ball_LC87 hri hx
  have ha2 : a * a = 1 := by rcases ha with rfl | rfl <;> norm_num
  have haabs : |a| = 1 := by rcases ha with rfl | rfl <;> norm_num
  let ystar : WithLp 2 (ℝ × (S.centre i hi).Z) :=
    WithLp.toLp 2 ((F x).fst + 10 * (1000000 * Δ) * a, (F x).snd)
  have hxs : dist (F x) ystar = 10 * (1000000 * Δ) := by
    have he : F x = WithLp.toLp 2 ((F x).fst, (F x).snd) := rfl
    calc dist (F x) ystar = dist (WithLp.toLp 2 ((F x).fst, (F x).snd)) ystar := by rw [← he]
      _ = dist (F x).fst ((F x).fst + 10 * (1000000 * Δ) * a) := dist_toLp_same_snd_SGP2 _ _ _
      _ = 10 * (1000000 * Δ) := by
        rw [Real.dist_eq, sub_add_cancel_left, abs_neg, abs_mul, haabs, mul_one,
          abs_of_pos (by positivity)]
  have hys : dist ystar (F i) < 20 * (1000000 * Δ) := by
    have h1 := dist_triangle ystar (F x) (F i)
    rw [dist_comm ystar (F x), hxs] at h1
    have h2 := (abs_le.mp hxi).2
    nlinarith
  obtain ⟨y, hy, hyd⟩ := hlift' ystar hys
  have hy100 : y ∈ ball i (100 * (1000000 * Δ) * ρ i) := ball_subset_ball (by nlinarith) hy
  have hxy := hdist' x hx100 y hy100
  have hFxy : |dist (F x) (F y) - 10 * (1000000 * Δ)| < δ := by
    have t1 := dist_triangle (F x) ystar (F y)
    have t2 := dist_triangle (F x) (F y) ystar
    have t3 := dist_comm (F y) ystar
    rw [hxs] at t1 t2
    rw [abs_lt]
    constructor <;> linarith
  have hfst : |(F y).fst - ((F x).fst + 10 * (1000000 * Δ) * a)| < δ := by
    have h := WithLp.dist_fst_le (F y) ystar
    rw [Real.dist_eq] at h
    have hyd' : dist (F y) ystar < δ := by rw [dist_comm]; exact hyd
    exact lt_of_le_of_lt h hyd'
  refine ⟨y, hy, ?_, ?_⟩
  · rw [abs_lt] at hFxy ⊢
    rw [abs_le] at hxy
    constructor <;> linarith [hxy.1, hxy.2, hFxy.1, hFxy.2]
  · simp only [sgpRaw_of_mem S hi]
    have he : a * ((F y).fst - (F x).fst) =
        a * ((F y).fst - ((F x).fst + 10 * (1000000 * Δ) * a)) +
          10 * (1000000 * Δ) * (a * a) := by ring
    have hb : |a * ((F y).fst - ((F x).fst + 10 * (1000000 * Δ) * a))| < δ := by
      rw [abs_mul, haabs, one_mul]
      exact hfst
    rw [he, ha2, mul_one]
    linarith [neg_abs_le (a * ((F y).fst - ((F x).fst + 10 * (1000000 * Δ) * a)))]

end Reference

section Clauses

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}

/-- **SGP03 (SC), derivatives, at one point.** Under (SB) and SGP02's alignment `a` of a listed
chart `j`, at `x ∈ D_i ∩ B(j, Lρ(j))`: `|s_j dη_j(w) − a dη_i(w)| ≤ θ√(ρ(i)⁻² g(w, w))` (the common
reference-axis test toward the lift `y`, the two original long tests along ONE minimizing segment,
and the saturation step). -/
theorem sgp03_derivative_SGP2 (S : SlimFamily X g hmetric ρ hρ β Δ σs K) {θ E δ : ℝ}
    (hΔ : 1 ≤ Δ) (hθ : 0 < θ) (hθ1 : θ < 1) (hE : 0 ≤ E) (hEθ : E < θ ^ 2 / 10 ^ 6)
    (hδ : 0 < δ) (hδθ : δ < θ ^ 2 / 10 ^ 6) (hσs : 0 < σs) (hσθ : σs < θ ^ 2 / 10 ^ 6)
    (hβ : β 1 ≤ min (1 / (1000 * (1000000 * Δ))) (δ / 100)) {i j : X} (hi : i ∈ S.centres)
    (hj : j ∈ S.centres) (hs1 : 99 / 100 < ρ j / ρ i) (hs2 : ρ j / ρ i < 101 / 100)
    (hdij : dist i j < 2 * (1000000 * Δ) * ρ i) {a : ℝ} (ha : a = 1 ∨ a = -1)
    (hRA : ∀ x ∈ ball i (30 * (1000000 * Δ) * ρ i),
      |ρ j / ρ i * sgpRaw S j x - a * sgpRaw S i x - ρ j / ρ i * sgpRaw S j i| < E)
    {x : X} (hxi : x ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i))
    (hxj : x ∈ ball j (1000000 * Δ * ρ j)) (w : TangentSpace 𝓘(ℝ, E3) x) :
    |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (S.centre j hj).coord x w -
        a * mvfderiv 𝓘(ℝ, E3) (S.centre i hi).coord x w| ≤
      θ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hri := hρ i
  have hrj := hρ j
  have hΔ0 : 0 < Δ := by linarith
  have hθ2 : θ ^ 2 < 1 := by nlinarith
  have hδ1 : δ < 1 := by nlinarith
  have h106 : (10 : ℝ) ^ 6 * Δ = 1000000 * Δ := by norm_num
  have hLpos : 0 < 1000000 * Δ := by positivity
  have hsj : 0 < ρ j / ρ i := div_pos hrj hri
  have hij : ρ i < 100 / 99 * ρ j := by
    rw [lt_div_iff₀ hri] at hs1
    linarith
  have hji : ρ j < 101 / 100 * ρ i := by
    rw [div_lt_iff₀ hri] at hs2
    linarith
  obtain ⟨y, hy21, hdxy, hay⟩ := sgp03_reference_lift_SGP2 S hΔ hδ1 hβ hi hxi ha
  obtain ⟨v, hvv, hgeo⟩ := exists_rescaled_minimizing_SGP2 g hmetric x y
  set d := dist x y with hd
  set r := (ρ i)⁻¹ * d with hr
  have hr1 : 10 * (1000000 * Δ) - 2 * δ < r := by linarith [(abs_lt.mp hdxy).1]
  have hr2 : r < 10 * (1000000 * Δ) - 2 * δ + 4 * δ := by linarith [(abs_lt.mp hdxy).2]
  have hD : 0 < 10 * (1000000 * Δ) - 2 * δ := by nlinarith
  have hrpos : 0 < r := hD.trans hr1
  have hdeq : d = ρ i * r := by rw [hr]; field_simp
  -- the two original long tests along ONE minimizing segment
  have hL6 : (1000000 : ℝ) ≤ 1000000 * Δ := by linarith
  have hxLi : x ∈ ball i (10 ^ 6 * Δ * ρ i) := by
    rw [h106]
    refine ball_subset_ball ?_ hxi
    have := mul_mul_le_mul_mul_SGP2 (k := 95 / 100) (k' := 1) (by norm_num) hLpos.le hri.le
    linarith
  have hσ24 : σs * 24 ≤ 1 := by nlinarith
  have hyLi : y ∈ ball i (10 ^ 6 * Δ / σs * ρ i) := by
    rw [h106]
    refine ball_subset_ball ?_ hy21
    exact mul_le_mul_of_nonneg_right
      (sgp03_num_outer_SGP2 hLpos.le hσs (by linarith)) hri.le
  have hxyi : 10 ^ 6 * Δ * ρ i < d := by
    rw [h106, hdeq]
    exact sgp03_num_far_SGP2 hL6 hδ1 hri (by linarith) hr1
  have Ti := (S.centre i hi).test_phys_SGP2 hxLi hyLi hxyi hvv (hgeo (ρ i) hri)
  have hxLj : x ∈ ball j (10 ^ 6 * Δ * ρ j) := by rw [h106]; exact hxj
  have hyLj : y ∈ ball j (10 ^ 6 * Δ / σs * ρ j) := by
    rw [h106, mem_ball]
    have hyi : dist y i < 21 * (1000000 * Δ) * ρ i := hy21
    have htri := dist_triangle y i j
    have h24 := mul_le_mul_of_nonneg_right (sgp03_num_outer_SGP2 hLpos.le hσs hσ24) hrj.le
    have hl := sgp03_num_lift_SGP2 hLpos hri hij hyi hdij
    linarith
  have hxyj : 10 ^ 6 * Δ * ρ j < d := by
    rw [h106, hdeq]
    exact sgp03_num_far_SGP2 hL6 hδ1 hri hji.le hr1
  have Tj := (S.centre j hj).test_phys_SGP2 hxLj hyLj hxyj hvv (hgeo (ρ j) hrj)
  have hrj' : (ρ j)⁻¹ * d = r / (ρ j / ρ i) := by rw [hr]; field_simp
  rw [hrj'] at Tj
  -- (RA) at `x` and `y`: the raw increments agree up to `2E`
  have hRx := hRA x (ball_subset_ball (by nlinarith) hxi)
  have hRy := hRA y (ball_subset_ball (by nlinarith) hy21)
  simp only [sgpRaw_of_mem S hj, sgpRaw_of_mem S hi] at hRx hRy hay
  set uix := (sgpSplitMap (S.centre i hi) x).fst
  set uiy := (sgpSplitMap (S.centre i hi) y).fst
  set ujx := (sgpSplitMap (S.centre j hj) x).fst
  set ujy := (sgpSplitMap (S.centre j hj) y).fst
  set c := (sgpSplitMap (S.centre j hj) i).fst
  have hinc : |ρ j / ρ i * (ujy - ujx) - a * (uiy - uix)| < 2 * E := by
    have he : ρ j / ρ i * (ujy - ujx) - a * (uiy - uix) =
        (ρ j / ρ i * ujy - a * uiy - ρ j / ρ i * c) -
          (ρ j / ρ i * ujx - a * uix - ρ j / ρ i * c) := by
      ring
    rw [he]
    calc _ ≤ |ρ j / ρ i * ujy - a * uiy - ρ j / ρ i * c| +
          |ρ j / ρ i * ujx - a * uix - ρ j / ρ i * c| := abs_sub _ _
      _ < E + E := add_lt_add hRy hRx
      _ = 2 * E := by ring
  -- the saturation step in the normalized form `ρ(i)⁻² g` at `x`
  obtain ⟨ε, hεdef, hε0, hσε, hε1, hεθ⟩ : ∃ ε : ℝ,
      ε = σs + (3 * δ + 2 * E) / (10 * (1000000 * Δ) - 2 * δ) ∧ 0 ≤ ε ∧ σs ≤ ε ∧ ε ≤ 1 / 2 ∧
        2 * ε + 12 * Real.sqrt ε ≤ θ :=
    ⟨_, rfl, sgp03_budget_SGP2 hθ hθ1 hσs.le hσθ hδ.le hδθ hE hEθ hL6⟩
  let B : E3 →L[ℝ] E3 →L[ℝ] ℝ := ((ρ i)⁻¹ ^ 2) • (g.inner x : E3 →L[ℝ] E3 →L[ℝ] ℝ)
  have hB : ∀ z z' : E3, B z z' = (ρ i)⁻¹ ^ 2 * g.inner x z z' := fun _ _ => rfl
  have hsqrt : ∀ z : E3, Real.sqrt (B z z) = (ρ i)⁻¹ * Real.sqrt (g.inner x z z) := by
    intro z
    rw [hB, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hsymm : ∀ z z' : E3, B z z' = B z' z := by
    intro z z'
    rw [hB, hB, g.symm x z z']
  have hpos : ∀ z : E3, 0 ≤ B z z := fun z => by
    rw [hB]
    exact mul_nonneg (by positivity) (gInner_self_nonneg g x z)
  let f : E3 →L[ℝ] ℝ := (ρ j / ρ i) • (mvfderiv 𝓘(ℝ, E3) (S.centre j hj).coord x : E3 →L[ℝ] ℝ)
  let h : E3 →L[ℝ] ℝ := a • (mvfderiv 𝓘(ℝ, E3) (S.centre i hi).coord x : E3 →L[ℝ] ℝ)
  have hfapp : ∀ z : E3, f z = ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (S.centre j hj).coord x z :=
    fun _ => rfl
  have happ : ∀ z : E3, h z = a * mvfderiv 𝓘(ℝ, E3) (S.centre i hi).coord x z := fun _ => rfl
  have haabs : |a| = 1 := by rcases ha with rfl | rfl <;> norm_num
  have hf : ∀ z, |f z| ≤ (1 + ε) * Real.sqrt (B z z) := by
    intro z
    have hb := (S.centre j hj).abs_mvfderiv_le_SGP2 hσs.le hxLj z
    have hg0 := Real.sqrt_nonneg (g.inner x z z)
    rw [hfapp, abs_mul, abs_of_pos hsj, hsqrt]
    have hk : ρ j / ρ i * ((1 + σs) * (ρ j)⁻¹ * Real.sqrt (g.inner x z z)) =
        (1 + σs) * ((ρ i)⁻¹ * Real.sqrt (g.inner x z z)) := by field_simp
    calc ρ j / ρ i * |mvfderiv 𝓘(ℝ, E3) (S.centre j hj).coord x z|
        ≤ ρ j / ρ i * ((1 + σs) * (ρ j)⁻¹ * Real.sqrt (g.inner x z z)) :=
          mul_le_mul_of_nonneg_left hb hsj.le
      _ = (1 + σs) * ((ρ i)⁻¹ * Real.sqrt (g.inner x z z)) := hk
      _ ≤ (1 + ε) * ((ρ i)⁻¹ * Real.sqrt (g.inner x z z)) := by gcongr
  have hh : ∀ z, |h z| ≤ (1 + ε) * Real.sqrt (B z z) := by
    intro z
    have hb := (S.centre i hi).abs_mvfderiv_le_SGP2 hσs.le hxLi z
    rw [happ, abs_mul, haabs, one_mul, hsqrt]
    calc |mvfderiv 𝓘(ℝ, E3) (S.centre i hi).coord x z|
        ≤ (1 + σs) * (ρ i)⁻¹ * Real.sqrt (g.inner x z z) := hb
      _ = (1 + σs) * ((ρ i)⁻¹ * Real.sqrt (g.inner x z z)) := by ring
      _ ≤ (1 + ε) * ((ρ i)⁻¹ * Real.sqrt (g.inner x z z)) := by gcongr
  have hcr : ρ i / d = r⁻¹ := by rw [hr]; field_simp
  have hw : B ((ρ i / d) • v) ((ρ i / d) • v) = 1 := by
    change (ρ i)⁻¹ ^ 2 * g.inner x ((ρ i / d) • v) ((ρ i / d) • v) = 1
    rw [gInner_smul_self, hvv, hdeq]
    field_simp
  have hfw : 1 - ε ≤ f ((ρ i / d) • v) := by
    change 1 - ε ≤ ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (S.centre j hj).coord x ((ρ i / d) • v)
    rw [map_smul, smul_eq_mul, hcr]
    have hV : 10 * (1000000 * Δ) - 2 * δ + δ < a * (uiy - uix) := by linarith
    rw [hεdef]
    exact sgp03_lower_j_SGP2 hsj hD hr1 hr2 Tj hinc hV
  have hhw : 1 - ε ≤ h ((ρ i / d) • v) := by
    change 1 - ε ≤ a * mvfderiv 𝓘(ℝ, E3) (S.centre i hi).coord x ((ρ i / d) • v)
    rw [map_smul, smul_eq_mul, hcr]
    have hV : 10 * (1000000 * Δ) - 2 * δ + δ < a * (uiy - uix) := by linarith
    rw [hεdef]
    exact sgp03_lower_i_SGP2 ha hD hr1 hr2 hE Ti hV
  have key := abs_sub_le_of_form_saturation_SGP2 B hsymm hpos f h hε0 hε1 hf hh _ hw hfw hhw w
  have key' : |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (S.centre j hj).coord x w -
      a * mvfderiv 𝓘(ℝ, E3) (S.centre i hi).coord x w| ≤
      (2 * ε + 12 * Real.sqrt ε) * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := key
  exact key'.trans (mul_le_mul_of_nonneg_right hεθ (Real.sqrt_nonneg _))

/-- **SGP03, model support, at one point.** If the model cutoff `f(λ_j(η_i(x))/(s_jℓ))` is nonzero
at `x ∈ D_i`, then `x ∈ B(j, .91Lρ(j))` (SGP02's raw alignment, the reference value tolerance and
the pointed distortion of the `j` splitting; no `j` coordinate is used). -/
theorem sgp03_model_support_SGP2 (S : SlimFamily X g hmetric ρ hρ β Δ σs K) {δ E vs : ℝ}
    (hΔ : 1 ≤ Δ) (hδ1 : δ < 1) (hβ : β 1 ≤ min (1 / (1000 * (1000000 * Δ))) (δ / 100))
    {i j : X} (hi : i ∈ S.centres) (hj : j ∈ S.centres) (hs1 : 99 / 100 < ρ j / ρ i)
    (hdij : dist i j < 2 * (1000000 * Δ) * ρ i) {a : ℝ} (ha : a = 1 ∨ a = -1)
    (hE1 : E < 1 / 100) (hvs1 : vs < 1 / 100)
    (hRA : ∀ x ∈ ball i (30 * (1000000 * Δ) * ρ i),
      |ρ j / ρ i * sgpRaw S j x - a * sgpRaw S i x - ρ j / ρ i * sgpRaw S j i| < E)
    (hval : ∀ x ∈ ball i (10 ^ 6 * Δ * ρ i), |(S.centre i hi).coord x - sgpRaw S i x| < vs)
    {x : X} (hxi : x ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i))
    (hf : slimCutoffProfile_LC87 ((a * (S.centre i hi).coord x + ρ j / ρ i * sgpRaw S j i) /
      (ρ j / ρ i * (100000 * Δ))) ≠ 0) :
    x ∈ ball j (91 / 100 * (1000000 * Δ) * ρ j) := by
  have hri := hρ i
  have hrj := hρ j
  have hΔ0 : 0 < Δ := by linarith
  have hsj : 0 < ρ j / ρ i := div_pos hrj hri
  have hij : ρ i < 100 / 99 * ρ j := by
    rw [lt_div_iff₀ hri] at hs1
    linarith
  have haabs : |a| = 1 := by rcases ha with rfl | rfl <;> norm_num
  -- the profile is supported in `(-8.9, 8.9)`
  set t := (a * (S.centre i hi).coord x + ρ j / ρ i * sgpRaw S j i) /
    (ρ j / ρ i * (100000 * Δ)) with ht
  have htl : -(89 / 10) < t := by
    by_contra hle
    exact hf (intervalPlateauProfile_zero_left (by norm_num) (by linarith [not_lt.mp hle]))
  have htr : t < 89 / 10 := by
    by_contra hle
    exact hf (intervalPlateauProfile_zero_right (by norm_num) (by linarith [not_lt.mp hle]))
  have hden : 0 < ρ j / ρ i * (100000 * Δ) := by positivity
  have hlam : |a * (S.centre i hi).coord x + ρ j / ρ i * sgpRaw S j i| <
      89 / 10 * (ρ j / ρ i * (100000 * Δ)) := by
    rw [abs_lt]
    rw [ht, lt_div_iff₀ hden] at htl
    rw [ht, div_lt_iff₀ hden] at htr
    constructor <;> linarith
  have hRx := hRA x (ball_subset_ball (by nlinarith) hxi)
  have hvx := hval x (ball_subset_ball (by nlinarith) hxi)
  -- `|u_j(x)| < 8.9ℓ + 1`
  have huj : |sgpRaw S j x| < 89 / 10 * (100000 * Δ) + 1 := by
    have he : ρ j / ρ i * sgpRaw S j x =
        (a * (S.centre i hi).coord x + ρ j / ρ i * sgpRaw S j i) +
          a * (sgpRaw S i x - (S.centre i hi).coord x) +
          (ρ j / ρ i * sgpRaw S j x - a * sgpRaw S i x - ρ j / ρ i * sgpRaw S j i) := by ring
    have hb : |ρ j / ρ i * sgpRaw S j x| < 89 / 10 * (ρ j / ρ i * (100000 * Δ)) + vs + E := by
      rw [he]
      have h1 := abs_add_le (a * (S.centre i hi).coord x + ρ j / ρ i * sgpRaw S j i +
        a * (sgpRaw S i x - (S.centre i hi).coord x))
        (ρ j / ρ i * sgpRaw S j x - a * sgpRaw S i x - ρ j / ρ i * sgpRaw S j i)
      have h2 := abs_add_le (a * (S.centre i hi).coord x + ρ j / ρ i * sgpRaw S j i)
        (a * (sgpRaw S i x - (S.centre i hi).coord x))
      have h3 : |a * (sgpRaw S i x - (S.centre i hi).coord x)| < vs := by
        rw [abs_mul, haabs, one_mul, abs_sub_comm]
        exact hvx
      linarith
    rw [abs_mul, abs_of_pos hsj] at hb
    have hvE : vs + E < ρ j / ρ i := by
      have := abs_nonneg ((S.centre i hi).coord x - sgpRaw S i x)
      linarith
    have hq : (89 / 10 * (ρ j / ρ i * (100000 * Δ)) + vs + E) / (ρ j / ρ i) <
        89 / 10 * (100000 * Δ) + 1 := by
      rw [div_lt_iff₀ hsj]
      nlinarith
    calc |sgpRaw S j x| = ρ j / ρ i * |sgpRaw S j x| / (ρ j / ρ i) := by field_simp
      _ < (89 / 10 * (ρ j / ρ i * (100000 * Δ)) + vs + E) / (ρ j / ρ i) :=
          div_lt_div_of_pos_right hb hsj
      _ < _ := hq
  -- the pointed distortion of the `j` splitting
  obtain ⟨-, hdist, -⟩ := sgp02_reference_tests S hΔ hβ hj
  let iZ := (S.centre j hj).instZ
  set F := sgpSplitMap (S.centre j hj) with hF
  have hdist' : ∀ x ∈ ball j (100 * (1000000 * Δ) * ρ j),
      ∀ x' ∈ ball j (100 * (1000000 * Δ) * ρ j),
      |dist (F x) (F x') - (ρ j)⁻¹ * dist x x'| ≤ δ := hdist
  have hx100 : x ∈ ball j (100 * (1000000 * Δ) * ρ j) := by
    rw [mem_ball]
    have hxi' : dist x i < 95 / 100 * (1000000 * Δ) * ρ i := hxi
    have htri := dist_triangle x i j
    nlinarith
  have hxj := hdist' x hx100 j (mem_ball_self (by positivity))
  have hFj : F j = WithLp.toLp 2 ((0 : ℝ), (S.centre j hj).z) := sgpSplitMap_center _
  have hFx : |(F x).fst| < 89 / 10 * (100000 * Δ) + 1 := by
    rw [← sgpRaw_of_mem S hj]
    exact huj
  have hd := dist_le_fst_add_snd_SGP2 (F x) (F j)
  rw [hFj] at hd
  have hd1 : dist (F x).fst (WithLp.toLp 2 ((0 : ℝ), (S.centre j hj).z)).fst = |(F x).fst| := by
    rw [Real.dist_eq]
    change |(F x).fst - 0| = _
    rw [sub_zero]
  have hd2 : dist (F x).snd (WithLp.toLp 2 ((0 : ℝ), (S.centre j hj).z)).snd ≤ 10 ^ 3 * Δ :=
    (S.centre j hj).factor_dist _ _
  rw [hd1] at hd
  rw [hFj] at hxj
  have hdj : (ρ j)⁻¹ * dist x j < 91 / 100 * (1000000 * Δ) := by
    have := (abs_le.mp hxj).1
    nlinarith
  rw [mem_ball]
  rw [inv_mul_lt_iff₀ hrj] at hdj
  linarith

end Clauses

section Row

/-- **SGP03 (SC) on the actual final family with LFR19's tolerance.** For `Δ ≥ 1`, the exclusion
quality `β₂`, `0 < θ < 1` and `0 < E < θ²/10⁶` there are a curvature radius `Lc` and a raw quality
`η₀` such that for EVERY actual `P : LocalChartPacketsRV … vs` with `β 2 = β₂`, `β 1 ≤ η₀`,
`Lc ≤ Lmax`, `10⁶ΔΛ < 10⁻⁵` and the (SB) budgets `0 < σs < θ²/10⁶`, `vs < θ/100`: every slim
centre `i` and listed `j ∈ J_i` have ONE sign `a = ±1` with SGP02's (RA), the derivative bound on
`D_i ∩ B(j, Lρ(j))` (norm of `ρ(i)⁻² g`), the model-support enclosure on `D_i`, and the value bound
`|s_jη_j − λ_j(η_i)| < θ` on `D_i ∩ B(j, Lρ(j))`. -/
theorem sgp03_row {Δ β₂ θ E : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1) (hθ : 0 < θ)
    (hθ1 : θ < 1) (hE : 0 < E) (hEθ : E < θ ^ 2 / 10 ^ 6) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ)
        (P : LocalChartPacketsRV X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr
          e T V vs),
        β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 →
        0 < σs → σs < θ ^ 2 / 10 ^ 6 → vs < θ / 100 →
        ∀ i (hi : i ∈ P.slim.centres), ∀ j (hj : j ∈ sgpSlimList P.slim i), ∃ a : ℝ,
          (a = 1 ∨ a = -1) ∧
          (∀ x ∈ ball i (30 * (1000000 * Δ) * ρ i),
            |ρ j / ρ i * sgpRaw P.slim j x - a * sgpRaw P.slim i x -
              ρ j / ρ i * sgpRaw P.slim j i| < E) ∧
          (∀ x ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i), x ∈ ball j (1000000 * Δ * ρ j) →
            ∀ w : TangentSpace 𝓘(ℝ, E3) x,
              |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (P.slim.centre j hj.1).coord x w -
                a * mvfderiv 𝓘(ℝ, E3) (P.slim.centre i hi).coord x w| ≤
                θ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) ∧
          (∀ x ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i),
            slimCutoffProfile_LC87 ((a * (P.slim.centre i hi).coord x +
              ρ j / ρ i * sgpRaw P.slim j i) / (ρ j / ρ i * (100000 * Δ))) ≠ 0 →
            x ∈ ball j (91 / 100 * (1000000 * Δ) * ρ j)) ∧
          ∀ x ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i), x ∈ ball j (1000000 * Δ * ρ j) →
            |ρ j / ρ i * (P.slim.centre j hj.1).coord x -
              (a * (P.slim.centre i hi).coord x + ρ j / ρ i * sgpRaw P.slim j i)| < θ := by
  obtain ⟨Lc, η₀, hLc, hη₀, hRArow⟩ := sgp02_row hΔ hβ₂ hβ₂1 hE
  have hθ2 : θ ^ 2 < 1 := by nlinarith
  have hΔ0 : 0 < Δ := by linarith
  have hδr0 : (0 : ℝ) < θ ^ 2 / (2 * 10 ^ 6) := by positivity
  have hδrθ : θ ^ 2 / (2 * 10 ^ 6) < θ ^ 2 / 10 ^ 6 := by
    apply div_lt_div_of_pos_left (by positivity) (by positivity) (by norm_num)
  have hδr1 : θ ^ 2 / (2 * 10 ^ 6) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  refine ⟨Lc, min η₀ (min (1 / (1000 * (1000000 * Δ))) (θ ^ 2 / (2 * 10 ^ 6) / 100)), hLc,
    lt_min hη₀ (lt_min (by positivity) (by positivity)), ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs P hβ2
    hβ1 hLmax hΛ hLΛ hσs hσθ hvθ i hi j hj
  have hβη : β 1 ≤ η₀ := hβ1.trans (min_le_left _ _)
  have hβref : β 1 ≤ min (1 / (1000 * (1000000 * Δ))) (θ ^ 2 / (2 * 10 ^ 6) / 100) :=
    hβ1.trans (min_le_right _ _)
  obtain ⟨a, ha, hRA⟩ := hRArow X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax
    P.toLocalChartFamilyQ hβ2 hβη hLmax hΛ hLΛ i hi j hj
  obtain ⟨-, hs1, hs2, hdij⟩ := sgpSlimList_bounds P.toLocalChartFamily hΔ0 hΛ hLΛ hj
  have hri := hρ i
  have hii : i ∈ ball i (10 ^ 6 * Δ * ρ i) := mem_ball_self (by positivity)
  have hvs0 : 0 ≤ vs := (abs_nonneg _).trans (P.slim_value_sgpRaw hi hii).le
  have hEθ' : E < θ / 100 := by nlinarith
  refine ⟨a, ha, hRA, fun x hxi hxj w => ?_, fun x hxi hf => ?_, fun x hxi hxj => ?_⟩
  · exact sgp03_derivative_SGP2 P.slim hΔ hθ hθ1 hE.le hEθ hδr0 hδrθ hσs hσθ hβref hi hj.1 hs1
      hs2 hdij ha hRA hxi hxj w
  · exact sgp03_model_support_SGP2 P.slim hΔ hδr1 hβref hi hj.1 hs1 hdij ha (by linarith)
      (by linarith) hRA (fun x hx => P.slim_value_sgpRaw hi hx) hxi hf
  · have hxL : x ∈ ball i (10 ^ 6 * Δ * ρ i) := by
      refine ball_subset_ball ?_ hxi
      have := mul_mul_le_mul_mul_SGP2 (k := 95 / 100) (k' := 1) (L := 1000000 * Δ) (by norm_num)
        (by positivity) hri.le
      norm_num at this ⊢
      linarith
    have hxj' : x ∈ ball j (10 ^ 6 * Δ * ρ j) := by norm_num; exact hxj
    have h := sgp03_value_arith_SGP2 (div_pos (hρ j) hri) ha (P.slim_value_sgpRaw hj.1 hxj')
      (P.slim_value_sgpRaw hi hxL) (hRA x (ball_subset_ball (by
        have := mul_mul_le_mul_mul_SGP2 (k := 95 / 100) (k' := 30) (L := 1000000 * Δ)
          (by norm_num) (by positivity) hri.le
        linarith) hxi))
    exact h.trans (slim_value_comparison hs2 hvs0 hvθ hEθ')

/-- SGP03 with the blueprint's (SB) budget for `σs` verbatim, `0 < σs < min(1/100, θ²/10⁶,
1/(100L))`, and `0 < vs` (the parts `1/100`, `1/(100L)` and `0 < vs` are not needed). -/
example {Δ β₂ θ E : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hE : 0 < E) (hEθ : E < θ ^ 2 / 10 ^ 6) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ)
        (P : LocalChartPacketsRV X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr
          e T V vs),
        β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 →
        0 < σs → σs < min (1 / 100) (min (θ ^ 2 / 10 ^ 6) (1 / (100 * (1000000 * Δ)))) →
        0 < vs → vs < θ / 100 →
        ∀ i (hi : i ∈ P.slim.centres), ∀ j (hj : j ∈ sgpSlimList P.slim i), ∃ a : ℝ,
          (a = 1 ∨ a = -1) ∧
          (∀ x ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i), x ∈ ball j (1000000 * Δ * ρ j) →
            ∀ w : TangentSpace 𝓘(ℝ, E3) x,
              |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (P.slim.centre j hj.1).coord x w -
                a * mvfderiv 𝓘(ℝ, E3) (P.slim.centre i hi).coord x w| ≤
                θ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) ∧
          ∀ x ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i), x ∈ ball j (1000000 * Δ * ρ j) →
            |ρ j / ρ i * (P.slim.centre j hj.1).coord x -
              (a * (P.slim.centre i hi).coord x + ρ j / ρ i * sgpRaw P.slim j i)| < θ := by
  obtain ⟨Lc, η₀, hLc, hη₀, h⟩ := sgp03_row hΔ hβ₂ hβ₂1 hθ hθ1 hE hEθ
  refine ⟨Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs P hβ2
    hβ1 hLmax hΛ hLΛ hσs hσθ _ hvθ i hi j hj
  obtain ⟨a, ha, -, hD, -, hV⟩ := h X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr
    e T V vs P hβ2 hβ1 hLmax hΛ hLΛ hσs
    (hσθ.trans_le ((min_le_right _ _).trans (min_le_left _ _))) hvθ i hi j hj
  exact ⟨a, ha, hD, hV⟩

end Row

end DifferentialGeometry.Geometry.Collapse
