import DifferentialGeometry.Geometry.Fibration.ActualSlimGraphModel
import DifferentialGeometry.Geometry.Fibration.ActualSlimZeroComparison
import DifferentialGeometry.Geometry.Fibration.ManifoldBlockDerivative
import DifferentialGeometry.Geometry.Fibration.ActualCloudPackets

/-!
# SGP04 (SG): the actual slim graph approximation on the merged final family

Blueprint `master207B.tex`, SGP04 (`thm:fibration-actual-slim-graph`, B:4602–4665), the estimate
(SG): for `0 < e < 1/100` and an actual slim reference `i`, the full model `Φ_i = sgpFullGraph`
(C14-SGP3 G3: own block `(a, 1)`, listed slim blocks, FC05's zero block) satisfies
`‖R_i⁻¹π₃𝓔⁰ − Φ_iη_i‖_{C¹} < e` on `{|η_i| ≤ 8ℓ}`, where `𝓔⁰ = cgpGlobalMap` and
`π₃𝓔⁰ = cgpProjMap … cgpQ3Tags`. Units: `L = 10⁶Δ`, `ℓ = 10⁵Δ`, `D_i = B(i, .95Lρ(i))`,
`s_j = ρ(j)/ρ(i)`, `s₀ = R₀/ρ(i)`; derivatives along `w` are measured by `ν = √(ρ(i)⁻²g(w, w))`.

* Kernels with an abstract target (the fderiv of a map into `WithLp 2 (ℝ² × ℝ)` cannot be rewritten
  directly — instance synthesis of `ContinuousSMul` times out):
  `fderiv_orthogonalBlocks_apply_SGP4`,
  `fderiv_isometry_comp_apply_SGP4`, `fderiv_affine_comp_apply_SGP4`, `mvfderiv_comp_real_SGP4`,
  and the per-block comparison `block_c1_sub_le_SGP4` (value `≤ 4Bθ`, derivative `≤ 4Bθν`).
* `slim_block_eq_SGP4`, `zero_block_eq_SGP4`: the actual slim / zero block in reference units IS the
  model block of the scaled coordinate `U_j = s_jη_j` / `U₀ = s₀η₀`.
* Step 7: `cgpProjMap_Q3_eq_blockMap_SGP4` (`π₃𝓔⁰` is a block map with the non-`Q₃` cutoffs zero),
  `contMDiff_cgpProjMap_Q3_SGP4` (smooth with only `e ≤ 1/8`), `mvfderiv_cgpProjMap_Q3_apply_SGP4`.
* `sgp04_tag_bounds_SGP4`: (SG) at every tag (own block: error zero; listed slim block in its chart
  ball: SGP03 + `block_c1_sub_le_SGP4`; outside it: both sides vanish by SGP03's model support;
  unlisted slim and non-meeting zero tags: both vanish; meeting zero tag: SGP03's zero part).
* `sgp04_approx_SGP4`: square summation (`|J_i| ≤ N_*`, one meeting zero support).
* `sgp04_row` (SG) on `LocalChartPacketsRVZ`: `θ = e/(10C_*)` early; thresholds of SGP03 (slim and
  zero); for every slim `i` signs/translations with `‖ρ(i)⁻¹π₃𝓔⁰(x) − Φ_i(η_i x)‖ < e` and
  `‖ρ(i)⁻¹dπ₃𝓔⁰(w) − DΦ_i(η_i x)(dη_i(w))‖ ≤ e√(ρ(i)⁻²g(w, w))` on `{|η_i| ≤ 8ℓ}`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Kernel

/-- The `t`-th component of the derivative of `orthogonalBlocks f` is the derivative of `f t`. -/
theorem fderiv_orthogonalBlocks_apply_SGP4 {ι : Type*} [Finite ι] {F : ι → Type*}
    [∀ t, NormedAddCommGroup (F t)] [∀ t, InnerProductSpace ℝ (F t)] (f : ∀ t, ℝ → F t)
    {a : ℝ} (hf : ∀ t, DifferentiableAt ℝ (f t) a) (h : ℝ) (t : ι) :
    fderiv ℝ (orthogonalBlocks f) a h t = fderiv ℝ (f t) a h := by
  have : Fintype ι := Fintype.ofFinite ι
  have hW : DifferentiableAt ℝ (orthogonalBlocks f) a := by
    have hfun : orthogonalBlocks f =
        (PiLp.continuousLinearEquiv 2 ℝ F).symm ∘ fun y i => f i y := rfl
    rw [hfun]
    exact (PiLp.continuousLinearEquiv 2 ℝ F).symm.differentiableAt.comp a
      (differentiableAt_pi.mpr hf)
  let P : PiLp 2 F →L[ℝ] F t :=
    (ContinuousLinearMap.proj t).comp (PiLp.continuousLinearEquiv 2 ℝ F).toContinuousLinearMap
  have hD : fderiv ℝ (f t) a = P.comp (fderiv ℝ (orthogonalBlocks f) a) :=
    (P.hasFDerivAt.comp a hW.hasFDerivAt).fderiv
  rw [hD]
  rfl

/-- The derivative of `a ↦ T (G a)` for a continuous linear `T` (any target). -/
theorem fderiv_clm_comp_apply_SGP4 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (T : E →L[ℝ] F) {G : ℝ → E} {a : ℝ}
    (hG : DifferentiableAt ℝ G a) (h : ℝ) :
    fderiv ℝ (fun y => T (G y)) a h = T (fderiv ℝ G a h) := by
  have hD := (T.hasFDerivAt.comp a hG.hasFDerivAt).fderiv
  change fderiv ℝ (T ∘ G) a h = _
  rw [hD]
  rfl

/-- The derivative of `a ↦ ι (G a)` for a linear isometry `ι` (any target). -/
theorem fderiv_isometry_comp_apply_SGP4 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (ι : E →ₗᵢ[ℝ] F) {G : ℝ → E} {a : ℝ}
    (hG : DifferentiableAt ℝ G a) (h : ℝ) :
    fderiv ℝ (fun y => ι (G y)) a h = ι (fderiv ℝ G a h) :=
  fderiv_clm_comp_apply_SGP4 ι.toContinuousLinearMap hG h

/-- The derivative of a constant map (any target). -/
theorem fderiv_const_apply_SGP4 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (v : F)
    (a h : ℝ) : fderiv ℝ (fun _ : ℝ => v) a h = 0 := by
  rw [fderiv_const_apply]
  rfl

/-- The derivative of `a ↦ W(σa + c)`. -/
theorem fderiv_affine_comp_apply_SGP4 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : ℝ → E} {σ c a : ℝ} (hW : DifferentiableAt ℝ W (σ * a + c)) (h : ℝ) :
    fderiv ℝ (fun y => W (σ * y + c)) a h = fderiv ℝ W (σ * a + c) (σ * h) := by
  have haff : HasFDerivAt (fun y : ℝ => σ * y + c) (σ • ContinuousLinearMap.id ℝ ℝ) a :=
    ((hasFDerivAt_id a).const_smul σ).add_const c
  have hD := (hW.hasFDerivAt.comp a haff).fderiv
  change fderiv ℝ (W ∘ fun y : ℝ => σ * y + c) a h = _
  rw [hD, ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul]

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*}
  [TopologicalSpace HM] {I : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M]
  [ChartedSpace HM M]

/-- The manifold chain rule for a real function followed by a map of `ℝ` (any target). -/
theorem mvfderiv_comp_real_SGP4 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : M → ℝ} {x : M} (hU : MDifferentiableAt I 𝓘(ℝ, ℝ) U x) {G : ℝ → F}
    (hG : DifferentiableAt ℝ G (U x)) (w : TangentSpace I x) :
    mvfderiv I (fun y => G (U y)) x w = fderiv ℝ G (U x) (mvfderiv I U x w) := by
  have h := hG.hasFDerivAt.hasMFDerivAt.comp x hU.hasMFDerivAt
  rw [mvfderiv_apply_LC, mvfderiv_apply_LC]
  change mfderiv I 𝓘(ℝ, F) (G ∘ U) x w = _
  rw [h.mfderiv]
  rfl

/-- `d(sU) = s dU`. -/
theorem mvfderiv_const_mul_SGP4 {U : M → ℝ} {x : M} (hU : MDifferentiableAt I 𝓘(ℝ, ℝ) U x)
    (s : ℝ) (w : TangentSpace I x) :
    mvfderiv I (fun y => s * U y) x w = s * mvfderiv I U x w := by
  rw [mvfderiv_comp_real_SGP4 hU (G := fun t => s * t) (differentiableAt_id.const_mul s)]
  have hD : HasFDerivAt (fun t : ℝ => s * t) (s • ContinuousLinearMap.id ℝ ℝ) (U x) :=
    (hasFDerivAt_id (U x)).const_smul s
  rw [hD.fderiv, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]

/-- **The per-block `C¹` comparison of (SG).** If near `x` the actual block is `r • ι(W(U))`
(`ι` a linear isometry, `W` a model block with first and second derivatives `≤ B`) and `U` is
`θ`-close in value and in derivative (along `w`, measured by `ν`) to the affine input
`σ η + c` with `|σ dη| ≤ 2ν`, then `r⁻¹ • block` differs from the model `ι(W(σ η + c))` by at most
`4Bθ` in value and `4Bθν` in derivative. -/
theorem block_c1_sub_le_SGP4 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ι : WithLp 2 (ℝ × ℝ) →ₗᵢ[ℝ] F) {W : ℝ → WithLp 2 (ℝ × ℝ)} (hW : ContDiff ℝ 2 W)
    {B θ : ℝ} (hB : 0 ≤ B) (hfirst : ∀ y, ‖fderiv ℝ W y‖ ≤ B)
    (hsecond : ∀ y, ‖fderiv ℝ (fderiv ℝ W) y‖ ≤ B) (hθ1 : θ ≤ 1)
    {Bk : M → F} {U : M → ℝ} {x : M} {r : ℝ} (hr : r ≠ 0)
    (heq : Bk =ᶠ[𝓝 x] fun y => r • ι (W (U y))) (hU : MDifferentiableAt I 𝓘(ℝ, ℝ) U x)
    {σ c a ν dη : ℝ} (w : TangentSpace I x) (hν : 0 ≤ ν)
    (hval : |U x - (σ * a + c)| ≤ θ) (hder : |mvfderiv I U x w - σ * dη| ≤ θ * ν)
    (hdv : |σ * dη| ≤ 2 * ν) :
    ‖r⁻¹ • Bk x - ι (W (σ * a + c))‖ ≤ 4 * B * θ ∧
      ‖r⁻¹ • mvfderiv I Bk x w - ι (fderiv ℝ W (σ * a + c) (σ * dη))‖ ≤ 4 * B * θ * ν := by
  have hθ0 : 0 ≤ θ := (abs_nonneg _).trans hval
  have hWd : Differentiable ℝ W := hW.differentiable (by norm_num)
  have hBx : Bk x = r • ι (W (U x)) := heq.eq_of_nhds
  have hDx : mvfderiv I Bk x w = r • ι (fderiv ℝ W (U x) (mvfderiv I U x w)) := by
    have hG : DifferentiableAt ℝ (fun u => r • ι (W u)) (U x) :=
      ((r • ι.toContinuousLinearMap).differentiableAt).comp (U x) (hWd (U x))
    have hm := (hG.hasFDerivAt.hasMFDerivAt.comp x hU.hasMFDerivAt).congr_of_eventuallyEq heq
    rw [mvfderiv_apply_LC, hm.mfderiv]
    change fderiv ℝ (fun u => r • ι (W u)) (U x) (mvfderiv I U x w) = _
    exact fderiv_clm_comp_apply_SGP4 (r • ι.toContinuousLinearMap) (hWd (U x))
      (mvfderiv I U x w)
  have hrr : ∀ v : F, r⁻¹ • r • v = v := fun v => by rw [smul_smul, inv_mul_cancel₀ hr, one_smul]
  constructor
  · rw [hBx, hrr, ← map_sub, LinearIsometry.norm_map]
    -- the value bound from the pointwise lemma, with zero derivatives
    exact (modelBlock_pointwise_c1_sub_le hW hB hfirst hsecond hθ1 hval
      (du := 0) (dv := 0) (by simpa using hθ0) (by norm_num)).1
  · rw [hDx, hrr, ← map_sub, LinearIsometry.norm_map]
    rcases hν.lt_or_eq with hνp | hν0
    · have hd : |mvfderiv I U x w / ν - σ * dη / ν| ≤ θ := by
        rw [← sub_div, abs_div, abs_of_pos hνp, div_le_iff₀ hνp]
        exact hder
      have hdv' : |σ * dη / ν| ≤ 2 := by
        rw [abs_div, abs_of_pos hνp, div_le_iff₀ hνp]
        exact hdv
      have hm := (modelBlock_pointwise_c1_sub_le hW hB hfirst hsecond hθ1 hval hd hdv').2
      have hsc : fderiv ℝ W (U x) (mvfderiv I U x w) - fderiv ℝ W (σ * a + c) (σ * dη) =
          ν • (fderiv ℝ W (U x) (mvfderiv I U x w / ν) -
            fderiv ℝ W (σ * a + c) (σ * dη / ν)) := by
        rw [smul_sub, ← map_smul, ← map_smul, smul_eq_mul, smul_eq_mul,
          mul_div_cancel₀ _ hνp.ne', mul_div_cancel₀ _ hνp.ne']
      rw [hsc, norm_smul, Real.norm_eq_abs, abs_of_pos hνp]
      nlinarith
    · subst hν0
      have h1 : σ * dη = 0 := by
        have := abs_nonneg (σ * dη)
        exact abs_eq_zero.mp (le_antisymm (by linarith) this)
      have h2 : mvfderiv I U x w = 0 := by
        rw [h1, sub_zero, mul_zero] at hder
        exact abs_eq_zero.mp (le_antisymm hder (abs_nonneg _))
      rw [h1, h2, map_zero, map_zero, sub_zero, norm_zero, mul_zero]

end Kernel

section Algebra

/-- The actual slim block in reference units is the slim model block of the scaled coordinate:
`((ρ_j m) η, ρ_j m) = ρ_i ι(W_{s}(s η))`, `s = ρ_j/ρ_i`, `m = f(η/ℓ)`. -/
theorem slim_block_eq_SGP4 {ρi ρj ℓ η m : ℝ} (hρi : 0 < ρi) (hρj : 0 < ρj)
    (hm : m = slimCutoffProfile_LC87 (η / ℓ)) :
    (WithLp.toLp 2 ((ρj * m) • planeAxis η, ρj * m) : WithLp 2 (ℝ² × ℝ)) =
      ρi • sgpBlockEmbed (sgpModelBlock ℓ (ρj / ρi) (ρj / ρi * η)) := by
  have hs : ρj / ρi * η / (ρj / ρi * ℓ) = η / ℓ :=
    mul_div_mul_left _ _ (div_ne_zero hρj.ne' hρi.ne')
  rw [sgpModelBlock_apply, hs, ← hm, sgpBlockEmbed_apply, ← WithLp.toLp_smul]
  congr 1
  refine Prod.ext ?_ ?_
  · change (ρj * m) • planeAxis η = ρi • planeAxis (m * (ρj / ρi * η))
    rw [← map_smul, ← map_smul, smul_eq_mul, smul_eq_mul]
    congr 1
    field_simp
  · change ρj * m = ρi • (ρj / ρi * m)
    rw [smul_eq_mul]
    field_simp

/-- The actual zero block in reference units is FC05's zero model block of the scaled radial
function: `((R Φ(t)) t, R Φ(t)) = ρ_i ι(F_{s₀}(s₀ t))`, `s₀ = R/ρ_i`. -/
theorem zero_block_eq_SGP4 {ρi R t : ℝ} (hρi : 0 < ρi) (hR : 0 < R) :
    (WithLp.toLp 2 ((R * Calculus.annularCutoff Calculus.cutoffProfile t) • planeAxis t,
      R * Calculus.annularCutoff Calculus.cutoffProfile t) : WithLp 2 (ℝ² × ℝ)) =
      ρi • sgpBlockEmbed (zeroModelBlock (R / ρi) (R / ρi * t)) := by
  have hs : (R / ρi)⁻¹ * (R / ρi * t) = t := by
    rw [← mul_assoc, inv_mul_cancel₀ (div_ne_zero hR.ne' hρi.ne'), one_mul]
  rw [zeroModelBlock_apply, hs, sgpBlockEmbed_apply, ← WithLp.toLp_smul]
  congr 1
  refine Prod.ext ?_ ?_
  · change (R * Calculus.annularCutoff Calculus.cutoffProfile t) • planeAxis t =
      ρi • planeAxis (Calculus.annularCutoff Calculus.cutoffProfile t * (R / ρi * t))
    rw [← map_smul, ← map_smul, smul_eq_mul, smul_eq_mul]
    congr 1
    field_simp
  · change R * Calculus.annularCutoff Calculus.cutoffProfile t =
      ρi • (R / ρi * Calculus.annularCutoff Calculus.cutoffProfile t)
    rw [smul_eq_mul]
    field_simp

/-- Where LC87's profile vanishes the slim model block and its derivative vanish. -/
theorem sgpModelBlock_eq_zero_SGP4 {ℓ s y : ℝ} (h : slimCutoffProfile_LC87 (y / (s * ℓ)) = 0) :
    sgpModelBlock ℓ s y = 0 := by
  rw [sgpModelBlock_apply, h, zero_mul, mul_zero]
  rfl

/-- The own model block `a ↦ (a e₀, 1)` as an embedded scalar block. -/
theorem own_block_eq_SGP4 (a : ℝ) :
    (WithLp.toLp 2 (planeAxis a, (1 : ℝ)) : WithLp 2 (ℝ² × ℝ)) =
      sgpBlockEmbed (WithLp.toLp 2 (a, (1 : ℝ))) := rfl

/-- The scalar own block `a ↦ (a, 1)` has derivative `h ↦ (h, 0)`. -/
theorem fderiv_ownScalar_apply_SGP4 (a h : ℝ) :
    fderiv ℝ (fun y : ℝ => (WithLp.toLp 2 (y, (1 : ℝ)) : WithLp 2 (ℝ × ℝ))) a h =
      WithLp.toLp 2 (h, 0) := by
  have hp : HasFDerivAt (fun y : ℝ => ((y, (1 : ℝ)) : ℝ × ℝ))
      ((ContinuousLinearMap.id ℝ ℝ).prod 0) a :=
    (hasFDerivAt_id a).prodMk (hasFDerivAt_const (1 : ℝ) a)
  have hc := ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm :
    (ℝ × ℝ) →L[ℝ] WithLp 2 (ℝ × ℝ)).hasFDerivAt.comp a hp
  rw [show (fun y : ℝ => (WithLp.toLp 2 (y, (1 : ℝ)) : WithLp 2 (ℝ × ℝ))) =
    (((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm : (ℝ × ℝ) →L[ℝ] WithLp 2 (ℝ × ℝ)) ∘
      fun y : ℝ => ((y, (1 : ℝ)) : ℝ × ℝ)) from rfl, hc.fderiv]
  rfl

end Algebra

section Q3Map

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

variable (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

/-- The cutoffs of `π₃𝓔⁰` written as a block map: the slim and zero cutoffs of `𝓔⁰` on the `Q₃`
tags, zero on the other tags. -/
def sgpQ3Cutoff : CGPTag L Z → X → ℝ
  | .inr (.inl j) => cgpCutoff L Z (.inr (.inl j))
  | .inr (.inr (.inr (.inl k))) => cgpCutoff L Z (.inr (.inr (.inr (.inl k))))
  | _ => fun _ => 0

/-- The open smooth domains of the `Q₃` blocks (empty for the other tags). -/
def sgpQ3Domain : CGPTag L Z → Set X
  | .inr (.inl j) => cgpDomain L Z (.inr (.inl j))
  | .inr (.inr (.inr (.inl k))) => cgpDomain L Z (.inr (.inr (.inr (.inl k))))
  | _ => ∅

theorem cgpProjMap_apply_of_not_mem_SGP4 {t : Finset (CGPTag L Z)} {a : CGPTag L Z} (ha : a ∉ t)
    (p : X) : cgpProjMap L Z t p a = 0 := by
  simp only [cgpProjMap, blockRestrict_apply, ha, ite_false]

/-- `π₃𝓔⁰` is the block map with the cutoffs `sgpQ3Cutoff` (the same radii and coordinates). -/
theorem cgpProjMap_Q3_eq_blockMap_SGP4 :
    cgpProjMap L Z (cgpQ3Tags L Z) = blockMap (cgpRadius L Z) (sgpQ3Cutoff L Z) (cgpCoord L Z) := by
  funext p
  refine PiLp.ext fun t => ?_
  have hz : ∀ t, cgpInQ3 L Z t = false → cgpProjMap L Z (cgpQ3Tags L Z) p t =
      blockMap (cgpRadius L Z) (sgpQ3Cutoff L Z) (cgpCoord L Z) p t := by
    intro t ht
    have hmem : t ∉ cgpQ3Tags L Z := by simp [cgpQ3Tags, ht]
    rw [cgpProjMap_apply_of_not_mem_SGP4 L Z hmem, blockMap_apply]
    rcases t with j | j | j | k | bb <;> simp_all [cgpInQ3, sgpQ3Cutoff] <;> rfl
  have hq : ∀ t, cgpInQ3 L Z t = true → cgpProjMap L Z (cgpQ3Tags L Z) p t =
      cgpGlobalMap L Z p t := by
    intro t ht
    exact cgpProjMap_apply_of_mem L Z (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩) p
  rcases t with j | j | j | k | bb
  · exact hz _ rfl
  · rw [hq _ rfl]
    rfl
  · exact hz _ rfl
  · rw [hq _ rfl]
    rfl
  · exact hz _ rfl

/-- **Step 7 of (SG): `π₃𝓔⁰` is smooth** with only the zero-shell tolerance `e ≤ 1/8` (no edge
margin: the edge, circle and special blocks are projected away). -/
theorem contMDiff_cgpProjMap_Q3_SGP4 (hΔ : 0 < Δ) (he : e ≤ 1 / 8) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag L Z => ℝ²)) ∞
      (cgpProjMap L Z (cgpQ3Tags L Z)) := by
  rw [cgpProjMap_Q3_eq_blockMap_SGP4]
  have hplane : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ²) ∞ planeAxis := planeAxis.contMDiff
  refine contMDiff_blockMap (U := sgpQ3Domain L Z) (fun i => ?_) (fun i => ?_) (fun i => ?_)
    (fun i => ?_) (fun i => ?_)
  · rcases i with j | j | j | i | bb
    · exact isOpen_empty
    · exact isOpen_ball
    · exact isOpen_empty
    · exact (Classical.choose_spec
        (Z.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radial_spec.2.1).1
    · exact isOpen_empty
  · rcases i with j | j | j | i | bb
    · exact contMDiffOn_empty
    · have hj := (Set.Finite.mem_toFinset _).mp j.2
      exact hplane.comp_contMDiffOn (L.slim.centre j.1 hj).contMDiffOn_coord
    · exact contMDiffOn_empty
    · have hO := Classical.choose_spec
        (Z.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radial_spec.2.1
      exact hplane.comp_contMDiffOn hO.2.2
    · exact contMDiffOn_empty
  · rcases i with j | j | j | i | bb
    · exact contMDiff_const
    · have hj := (Set.Finite.mem_toFinset _).mp j.2
      change ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (L.slim.cutoff j.1)
      unfold SlimFamily.cutoff
      rw [dite_eq_left hj]
      exact (L.slim.centre j.1 hj).contMDiff_cutoff
    · exact contMDiff_const
    · have hspec :=
        (Z.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radial_spec.2.2.2.2.2.2.2.2.2.2.2
      exact hspec.choose_spec.2.2.1
    · exact contMDiff_const
  · rcases i with j | j | j | i | bb
    · exact contMDiff_const
    · exact contMDiff_const
    · exact contMDiff_const
    · exact contMDiff_const
    · cases bb
      · exact L.contMDiff_scale
      · exact L.contMDiff_scale
  · rcases i with j | j | j | i | bb
    · simp [sgpQ3Cutoff, tsupport]
    · have hj := (Set.Finite.mem_toFinset _).mp j.2
      obtain ⟨h1, h2, h3, -⟩ := fc18_slim_row L hΔ hj
      exact h1.trans (h2.trans h3)
    · simp [sgpQ3Cutoff, tsupport]
    · have hO := Classical.choose_spec
        (Z.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radial_spec.2.1
      have hspec :=
        (Z.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radial_spec.2.2.2.2.2.2.2.2.2.2.2
      have hts := hspec.choose_spec.2.2.2.2.2.1
      refine hts.trans (fun x hx => hO.2.1 ⟨?_, ?_⟩)
      · linarith [hx.1]
      · linarith [hx.2]
    · simp [sgpQ3Cutoff, tsupport]

/-- The `t`-th component of the derivative of `π₃𝓔⁰`. -/
theorem mvfderiv_cgpProjMap_Q3_apply_SGP4 (hΔ : 0 < Δ) (he : e ≤ 1 / 8) (x : X)
    (w : TangentSpace 𝓘(ℝ, E3) x) (t : CGPTag L Z) :
    mvfderiv 𝓘(ℝ, E3) (cgpProjMap L Z (cgpQ3Tags L Z)) x w t =
      mvfderiv 𝓘(ℝ, E3)
        (fun y => blockMap (cgpRadius L Z) (sgpQ3Cutoff L Z) (cgpCoord L Z) y t) x w := by
  have hF := (contMDiff_cgpProjMap_Q3_SGP4 L Z hΔ he x).mdifferentiableAt (by simp)
  rw [cgpProjMap_Q3_eq_blockMap_SGP4] at hF ⊢
  exact mvfderiv_blockMap_apply_apply hF w t

end Q3Map

section Tags

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

variable (Q : LocalChartFamilyQ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

/-- A block of `π₃𝓔⁰` whose cutoff vanishes near `x` contributes neither value nor derivative. -/
theorem q3_tag_eq_zero_SGP4 (t : CGPTag Q.toLocalChartFamily Z) {x : X}
    (hx : x ∉ tsupport (sgpQ3Cutoff Q.toLocalChartFamily Z t)) (w : TangentSpace 𝓘(ℝ, E3) x) :
    blockMap (cgpRadius Q.toLocalChartFamily Z) (sgpQ3Cutoff Q.toLocalChartFamily Z)
        (cgpCoord Q.toLocalChartFamily Z) x t = 0 ∧
      mvfderiv 𝓘(ℝ, E3) (fun y => blockMap (cgpRadius Q.toLocalChartFamily Z)
        (sgpQ3Cutoff Q.toLocalChartFamily Z) (cgpCoord Q.toLocalChartFamily Z) y t) x w = 0 := by
  refine ⟨?_, mvfderiv_block_eq_zero_of_notMem_tsupport hx w⟩
  rw [blockMap_apply, image_eq_zero_of_notMem_tsupport hx, mul_zero, zero_smul]
  rfl

/-- **(SG) at a slim tag in its chart ball** (own or listed `j`): if the scaled coordinate
`U_j = s_jη_j` is `θ`-close in value and derivative to the affine input `σ a + c`, the block of
`ρ(i)⁻¹π₃𝓔⁰` differs from the model block `ι(W_{s_j}(σ a + c))` by at most `4Bθ` in value and
`4Bθν` in derivative (`B = sgpBlockBound`). -/
theorem sgp04_slim_tag_SGP4 (hΔ : 1 ≤ Δ) (i j : Q.slim.finite_centres.toFinset) {x : X}
    (hxj : x ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1)) (hs : 99 / 100 ≤ ρ j.1 / ρ i.1)
    {σ c a θ ν dη : ℝ} (hθ1 : θ ≤ 1) (w : TangentSpace 𝓘(ℝ, E3) x) (hν : 0 ≤ ν)
    (hval : |ρ j.1 / ρ i.1 * (Q.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x -
      (σ * a + c)| ≤ θ)
    (hder : |ρ j.1 / ρ i.1 * mvfderiv 𝓘(ℝ, E3)
      (Q.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x w - σ * dη| ≤ θ * ν)
    (hdv : |σ * dη| ≤ 2 * ν) :
    ‖(ρ i.1)⁻¹ • blockMap (cgpRadius Q.toLocalChartFamily Z) (sgpQ3Cutoff Q.toLocalChartFamily Z)
        (cgpCoord Q.toLocalChartFamily Z) x (.inr (.inl j)) -
      sgpBlockEmbed (sgpModelBlock (10 ^ 5 * Δ) (ρ j.1 / ρ i.1) (σ * a + c))‖ ≤
        4 * sgpBlockBound * θ ∧
    ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (fun y => blockMap (cgpRadius Q.toLocalChartFamily Z)
        (sgpQ3Cutoff Q.toLocalChartFamily Z) (cgpCoord Q.toLocalChartFamily Z) y (.inr (.inl j)))
        x w -
      sgpBlockEmbed (fderiv ℝ (sgpModelBlock (10 ^ 5 * Δ) (ρ j.1 / ρ i.1)) (σ * a + c)
        (σ * dη))‖ ≤ 4 * sgpBlockBound * θ * ν := by
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  have hri := hρ i.1
  have hrj := hρ j.1
  have hℓ : (1 : ℝ) ≤ 10 ^ 5 * Δ := by nlinarith
  have hP := le_max_left sgpProfileBound zeroProfileBound
  have hB : 50 * (sgpProfileBound + 1) ≤ sgpBlockBound := by unfold sgpBlockBound; linarith
  have hB0 : 0 ≤ sgpBlockBound := by linarith [one_le_sgpBlockBound]
  have hηd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (Q.slim.centre j.1 hj).coord x :=
    ((Q.slim.centre j.1 hj).contMDiffOn_coord.contMDiffAt
      (isOpen_ball.mem_nhds hxj)).mdifferentiableAt (by simp)
  have hU : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
      (fun y => ρ j.1 / ρ i.1 * (Q.slim.centre j.1 hj).coord y) x :=
    hηd.const_smul (ρ j.1 / ρ i.1)
  have heq : (fun y => blockMap (cgpRadius Q.toLocalChartFamily Z)
      (sgpQ3Cutoff Q.toLocalChartFamily Z) (cgpCoord Q.toLocalChartFamily Z) y (.inr (.inl j)))
        =ᶠ[𝓝 x]
      fun y => ρ i.1 • sgpBlockEmbed (sgpModelBlock (10 ^ 5 * Δ) (ρ j.1 / ρ i.1)
        (ρ j.1 / ρ i.1 * (Q.slim.centre j.1 hj).coord y)) := by
    filter_upwards [slim_cutoff_eventuallyEq_KA2 Q hj hxj] with y hy
    change WithLp.toLp 2 ((ρ j.1 * Q.slim.cutoff j.1 y) •
      planeAxis ((Q.slim.centre j.1 hj).coord y), ρ j.1 * Q.slim.cutoff j.1 y) = _
    exact slim_block_eq_SGP4 hri hrj hy
  have hder' : |mvfderiv 𝓘(ℝ, E3) (fun y => ρ j.1 / ρ i.1 * (Q.slim.centre j.1 hj).coord y) x w -
      σ * dη| ≤ θ * ν := by
    rw [mvfderiv_const_mul_SGP4 hηd]
    exact hder
  exact block_c1_sub_le_SGP4 sgpBlockEmbed ((contDiff_sgpModelBlock _ _).of_le (by simp)) hB0
    (fun y => ((sgpModelBlock_derivative_bounds hℓ hs y).1).trans hB)
    (fun y => ((sgpModelBlock_derivative_bounds hℓ hs y).2).trans hB) hθ1 hri.ne' heq hU w hν
    hval hder' hdv

/-- **(SG) at a meeting zero tag**: the zero block of `ρ(i)⁻¹π₃𝓔⁰` is FC05's model block of
`U₀ = s₀η₀` everywhere; with SGP03's zero comparison it differs from `ι(F_{s₀}(σ a + c))` by at
most `4Bθ` in value and `4Bθν` in derivative (`s₀ ≥ 1`). -/
theorem sgp04_zero_tag_SGP4 (i : Q.slim.finite_centres.toFinset) (k : Z.finite_centres.toFinset)
    {x : X} (hs0 : 1 ≤ (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i.1)
    (hrad : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
      (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x)
    {σ c a θ ν dη : ℝ} (hθ1 : θ ≤ 1) (w : TangentSpace 𝓘(ℝ, E3) x) (hν : 0 ≤ ν)
    (hval : |(Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i.1 *
      (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x - (σ * a + c)| ≤ θ)
    (hder : |(Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i.1 *
      mvfderiv 𝓘(ℝ, E3) (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x w -
        σ * dη| ≤ θ * ν)
    (hdv : |σ * dη| ≤ 2 * ν) :
    ‖(ρ i.1)⁻¹ • blockMap (cgpRadius Q.toLocalChartFamily Z) (sgpQ3Cutoff Q.toLocalChartFamily Z)
        (cgpCoord Q.toLocalChartFamily Z) x (.inr (.inr (.inr (.inl k)))) -
      sgpBlockEmbed (zeroModelBlock ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius /
        ρ i.1) (σ * a + c))‖ ≤ 4 * sgpBlockBound * θ ∧
    ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (fun y => blockMap (cgpRadius Q.toLocalChartFamily Z)
        (sgpQ3Cutoff Q.toLocalChartFamily Z) (cgpCoord Q.toLocalChartFamily Z) y
        (.inr (.inr (.inr (.inl k))))) x w -
      sgpBlockEmbed (fderiv ℝ (zeroModelBlock ((Z.zero k.1
        ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i.1)) (σ * a + c) (σ * dη))‖ ≤
        4 * sgpBlockBound * θ * ν := by
  set Zk := Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2) with hZk
  have hri := hρ i.1
  have hR := Zk.radius_pos
  have hP := le_max_right sgpProfileBound zeroProfileBound
  have hB : 50 * (zeroProfileBound + 1) ≤ sgpBlockBound := by unfold sgpBlockBound; linarith
  have hB0 : 0 ≤ sgpBlockBound := by linarith [one_le_sgpBlockBound]
  have hU : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun y => Zk.radius / ρ i.1 * Zk.radial y) x :=
    hrad.const_smul (Zk.radius / ρ i.1)
  have heq : (fun y => blockMap (cgpRadius Q.toLocalChartFamily Z)
      (sgpQ3Cutoff Q.toLocalChartFamily Z) (cgpCoord Q.toLocalChartFamily Z) y
        (.inr (.inr (.inr (.inl k))))) =ᶠ[𝓝 x]
      fun y => ρ i.1 • sgpBlockEmbed (zeroModelBlock (Zk.radius / ρ i.1)
        (Zk.radius / ρ i.1 * Zk.radial y)) := by
    refine Filter.Eventually.of_forall fun y => ?_
    change WithLp.toLp 2 ((Zk.radius * Calculus.annularCutoff Calculus.cutoffProfile
      (Zk.radial y)) • planeAxis (Zk.radial y), Zk.radius *
        Calculus.annularCutoff Calculus.cutoffProfile (Zk.radial y)) = _
    exact zero_block_eq_SGP4 hri hR
  have hder' : |mvfderiv 𝓘(ℝ, E3) (fun y => Zk.radius / ρ i.1 * Zk.radial y) x w - σ * dη| ≤
      θ * ν := by
    rw [mvfderiv_const_mul_SGP4 hrad]
    exact hder
  exact block_c1_sub_le_SGP4 sgpBlockEmbed ((contDiff_zeroModelBlock _).of_le (by simp)) hB0
    (fun y => ((zeroModelBlock_derivative_bounds hs0 y).1).trans hB)
    (fun y => ((zeroModelBlock_derivative_bounds hs0 y).2).trans hB) hθ1 hri.ne' heq hU w hν
    hval hder' hdv

end Tags

section TagBounds

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

open Classical in
/-- The weight of a tag in (SG)'s square summation: one on the reference and listed slim tags and
on the zero tags meeting `D_i`, zero elsewhere. -/
def sgpTagWeight (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)
    (i : L.slim.finite_centres.toFinset) : CGPTag L Z → ℝ
  | .inr (.inl j) => if j = i ∨ j.1 ∈ sgpSlimList L.slim i.1 then 1 else 0
  | .inr (.inr (.inr (.inl k))) =>
      if sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i.1 k.1 ((Set.Finite.mem_toFinset _).mp k.2) then 1
      else 0
  | _ => 0

theorem sgpTagWeight_nonneg
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)
    (i : L.slim.finite_centres.toFinset) (t : CGPTag L Z) : 0 ≤ sgpTagWeight L Z i t := by
  rcases t with j | j | j | k | bb <;> simp only [sgpTagWeight] <;> (try split_ifs) <;> norm_num

/-- **The square summation of (SG).** Per-tag bounds `‖A_t‖ ≤ κ·w_t` give `‖A‖ ≤ √((N + 2)κ²)`
(`|J_i| ≤ N`, at most one zero support meets `D_i`). -/
theorem norm_le_of_tagWeight_SGP4
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)
    (i : L.slim.finite_centres.toFinset) (A : BlockSpace (fun _ : CGPTag L Z => ℝ²)) {κ Nc : ℝ}
    (hA : ∀ t, ‖A t‖ ≤ κ * sgpTagWeight L Z i t)
    (huniq : ∀ k₁ (hk₁ : k₁ ∈ Z.centres) k₂ (hk₂ : k₂ ∈ Z.centres),
      sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i.1 k₁ hk₁ → sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i.1 k₂ hk₂ →
      k₁ = k₂)
    (hN : ((sgpSlimList L.slim i.1).ncard : ℝ) ≤ Nc) :
    ‖A‖ ≤ Real.sqrt ((Nc + 2) * κ ^ 2) := by
  classical
  rw [PiLp.norm_eq_of_L2]
  refine Real.sqrt_le_sqrt ?_
  have hsq : ∀ t, ‖A t‖ ^ 2 ≤ κ ^ 2 * sgpTagWeight L Z i t := by
    intro t
    have h0 := norm_nonneg (A t)
    have hw := sgpTagWeight_nonneg L Z i t
    have hw1 : sgpTagWeight L Z i t ≤ 1 := by
      rcases t with j | j | j | k | bb <;> simp only [sgpTagWeight] <;> (try split_ifs) <;> norm_num
    have hw2 : sgpTagWeight L Z i t ^ 2 = sgpTagWeight L Z i t := by
      rcases t with j | j | j | k | bb <;> simp only [sgpTagWeight] <;> (try split_ifs) <;> norm_num
    calc ‖A t‖ ^ 2 ≤ (κ * sgpTagWeight L Z i t) ^ 2 := pow_le_pow_left₀ h0 (hA t) 2
      _ = κ ^ 2 * sgpTagWeight L Z i t := by rw [mul_pow, hw2]
  refine sum_cgpTag_le_SGP3 L Z i (fun t => ‖A t‖ ^ 2) (by positivity) (fun j => ?_)
    (fun j => ?_) (fun j => ?_) ?_ (fun bb => ?_) hN
  · simpa [sgpTagWeight] using hsq (.inl j)
  · have h := hsq (.inr (.inl j))
    simp only [sgpTagWeight] at h
    split_ifs at h ⊢ <;> simpa using h
  · simpa [sgpTagWeight] using hsq (.inr (.inr (.inl j)))
  · refine sum_zeroTag_le_SGP3 Z i.1 _ (by positivity) (fun k => ?_)
      (fun k₁ k₂ h₁ h₂ => Subtype.ext (huniq _ _ _ _ h₁ h₂))
    have h := hsq (.inr (.inr (.inr (.inl k))))
    simp only [sgpTagWeight] at h
    split_ifs at h ⊢ <;> simpa using h
  · simpa [sgpTagWeight] using hsq (.inr (.inr (.inr (.inr bb))))

/-- (SG)'s budget: `√((N + 2)(4Bθν)²) ≤ (2/5) e ν` for `θ = e/(10C_*)`, `N ≤ N_*`. -/
theorem sgp04_budget_SGP4 {Nc eg ν : ℝ} (hN0 : 0 ≤ Nc) (hN : Nc ≤ egp02SlimCount)
    (heg : 0 < eg) (hν : 0 ≤ ν) :
    Real.sqrt ((Nc + 2) * (4 * sgpBlockBound * (eg / (10 * sgpGraphBound)) * ν) ^ 2) ≤
      2 / 5 * eg * ν := by
  have hC := sqrt_count_le_sgpGraphBound hN0 hN
  have hB := one_le_sgpBlockBound
  have hG : 0 < sgpGraphBound := by
    have h0 : 0 ≤ Real.sqrt ((Nc + 2) * sgpBlockBound ^ 2) := Real.sqrt_nonneg _
    have h1 : 0 < Real.sqrt ((Nc + 2) * sgpBlockBound ^ 2) :=
      Real.sqrt_pos.mpr (by positivity)
    linarith
  have hθ : 0 ≤ 4 * (eg / (10 * sgpGraphBound)) * ν := by positivity
  have he : (Nc + 2) * (4 * sgpBlockBound * (eg / (10 * sgpGraphBound)) * ν) ^ 2 =
      ((Nc + 2) * sgpBlockBound ^ 2) * (4 * (eg / (10 * sgpGraphBound)) * ν) ^ 2 := by ring
  rw [he, Real.sqrt_mul (by positivity), Real.sqrt_sq hθ]
  calc Real.sqrt ((Nc + 2) * sgpBlockBound ^ 2) * (4 * (eg / (10 * sgpGraphBound)) * ν)
      ≤ sgpGraphBound * (4 * (eg / (10 * sgpGraphBound)) * ν) :=
        mul_le_mul_of_nonneg_right hC hθ
    _ = 2 / 5 * eg * ν := by field_simp; ring

end TagBounds

section AllTags

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

variable (Q : LocalChartFamilyQ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

/-- Both sides of a tag vanish to first order: the (SG) errors are zero. -/
theorem tag_errors_zero_SGP4 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {r : ℝ}
    {v d m dm : F} {M1 M2 : ℝ} (hv : v = 0) (hd : d = 0) (hm : m = 0) (hdm : dm = 0)
    (h1 : 0 ≤ M1) (h2 : 0 ≤ M2) : ‖r⁻¹ • v - m‖ ≤ M1 ∧ ‖r⁻¹ • d - dm‖ ≤ M2 := by
  rw [hv, hd, hm, hdm, smul_zero, sub_zero, norm_zero]
  exact ⟨h1, h2⟩

/-- **(SG) at every tag of `𝓔⁰`** (kernel of SGP04's row): at `x ∈ D_i` with `|η_i(x)| ≤ 8ℓ`,
given SGP03's comparisons for the listed slim charts and the meeting zero support (as inputs),
the block of `ρ(i)⁻¹π₃𝓔⁰` at `t` differs from the block of the full model `Φ_i` at `η_i(x)` by at
most `4Bθ w_t` in value and `4Bθν w_t` in derivative (`w_t = sgpTagWeight`). -/
theorem sgp04_tag_bounds_SGP4 (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (i : Q.slim.finite_centres.toFinset) (sgn c zsgn zc : X → ℝ) (hsgn : ∀ j, |sgn j| ≤ 1)
    (hzsgn : ∀ k, |zsgn k| ≤ 1) {x : X}
    (hxD : x ∈ ball i.1 (95 / 100 * (1000000 * Δ) * ρ i.1))
    (hxL : x ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1))
    (hη : |(Q.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x| ≤ 8 * 10 ^ 5 * Δ)
    {θ ν : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (w : TangentSpace 𝓘(ℝ, E3) x) (hν : 0 ≤ ν)
    (hdη : |mvfderiv 𝓘(ℝ, E3) (Q.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x
      w| ≤ 2 * ν)
    (hslim : ∀ j (hj : j ∈ sgpSlimList Q.slim i.1), x ∈ ball j (10 ^ 6 * Δ * ρ j) →
      |ρ j / ρ i.1 * (Q.slim.centre j hj.1).coord x -
        (sgn j * (Q.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x + c j)| ≤ θ ∧
      |ρ j / ρ i.1 * mvfderiv 𝓘(ℝ, E3) (Q.slim.centre j hj.1).coord x w -
        sgn j * mvfderiv 𝓘(ℝ, E3)
          (Q.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x w| ≤ θ * ν)
    (hsupp : ∀ j ∈ sgpSlimList Q.slim i.1,
      slimCutoffProfile_LC87 ((sgn j * (Q.slim.centre i.1
        ((Set.Finite.mem_toFinset _).mp i.2)).coord x + c j) / (ρ j / ρ i.1 * (10 ^ 5 * Δ))) ≠ 0 →
      x ∈ ball j (10 ^ 6 * Δ * ρ j))
    (hzero : ∀ k (hk : k ∈ Z.centres), sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i.1 k hk →
      1 ≤ (Z.zero k hk).radius / ρ i.1 ∧
      MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (Z.zero k hk).radial x ∧
      |(Z.zero k hk).radius / ρ i.1 * (Z.zero k hk).radial x -
        (zsgn k * (Q.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x + zc k)| ≤ θ ∧
      |(Z.zero k hk).radius / ρ i.1 * mvfderiv 𝓘(ℝ, E3) (Z.zero k hk).radial x w -
        zsgn k * mvfderiv 𝓘(ℝ, E3)
          (Q.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x w| ≤ θ * ν)
    (t : CGPTag Q.toLocalChartFamily Z) :
    ‖(ρ i.1)⁻¹ • blockMap (cgpRadius Q.toLocalChartFamily Z) (sgpQ3Cutoff Q.toLocalChartFamily Z)
        (cgpCoord Q.toLocalChartFamily Z) x t -
      sgpFullTag Q.toLocalChartFamily Z i sgn c zsgn zc t
        ((Q.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x)‖ ≤
        4 * sgpBlockBound * θ * sgpTagWeight Q.toLocalChartFamily Z i t ∧
    ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (fun y => blockMap (cgpRadius Q.toLocalChartFamily Z)
        (sgpQ3Cutoff Q.toLocalChartFamily Z) (cgpCoord Q.toLocalChartFamily Z) y t) x w -
      fderiv ℝ (sgpFullTag Q.toLocalChartFamily Z i sgn c zsgn zc t)
        ((Q.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x)
        (mvfderiv 𝓘(ℝ, E3) (Q.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x w)‖ ≤
        4 * sgpBlockBound * θ * ν * sgpTagWeight Q.toLocalChartFamily Z i t := by
  classical
  have hΔ0 : 0 < Δ := by linarith
  have hri := hρ i.1
  have hB := one_le_sgpBlockBound
  have hκ : 0 ≤ 4 * sgpBlockBound * θ := by positivity
  have hκν : 0 ≤ 4 * sgpBlockBound * θ * ν := by positivity
  have hℓ : (0 : ℝ) < 10 ^ 5 * Δ := by positivity
  set Fq := blockMap (cgpRadius Q.toLocalChartFamily Z) (sgpQ3Cutoff Q.toLocalChartFamily Z)
    (cgpCoord Q.toLocalChartFamily Z) with hFq
  -- `|σ dη_i(w)| ≤ 2ν` for a sign of size at most one
  have hdv : ∀ σ : ℝ, |σ| ≤ 1 → |σ * mvfderiv 𝓘(ℝ, E3)
      (Q.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x w| ≤ 2 * ν := by
    intro σ hσ
    rw [abs_mul]
    calc |σ| * |mvfderiv 𝓘(ℝ, E3) (Q.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord
          x w| ≤ 1 * (2 * ν) := mul_le_mul hσ hdη (abs_nonneg _) zero_le_one
      _ = 2 * ν := one_mul _
  -- the tags whose cutoff vanishes near `x` and whose model block is zero
  have hnull : ∀ t, x ∉ tsupport (sgpQ3Cutoff Q.toLocalChartFamily Z t) →
      sgpFullTag Q.toLocalChartFamily Z i sgn c zsgn zc t = (fun _ => 0) →
      ‖(ρ i.1)⁻¹ • Fq x t - sgpFullTag Q.toLocalChartFamily Z i sgn c zsgn zc t
        ((Q.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x)‖ ≤
        4 * sgpBlockBound * θ * sgpTagWeight Q.toLocalChartFamily Z i t ∧
      ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (fun y => Fq y t) x w -
        fderiv ℝ (sgpFullTag Q.toLocalChartFamily Z i sgn c zsgn zc t)
          ((Q.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x)
          (mvfderiv 𝓘(ℝ, E3) (Q.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x
            w)‖ ≤ 4 * sgpBlockBound * θ * ν * sgpTagWeight Q.toLocalChartFamily Z i t := by
    intro t hx hm
    obtain ⟨h1, h2⟩ := q3_tag_eq_zero_SGP4 Q Z t hx w
    rw [hm]
    exact tag_errors_zero_SGP4 h1 h2 rfl (fderiv_const_apply_SGP4 _ _ _)
      (mul_nonneg hκ (sgpTagWeight_nonneg _ _ _ _))
      (mul_nonneg hκν (sgpTagWeight_nonneg _ _ _ _))
  have hempty : ∀ t, sgpQ3Cutoff Q.toLocalChartFamily Z t = (fun _ => 0) →
      x ∉ tsupport (sgpQ3Cutoff Q.toLocalChartFamily Z t) := by
    intro t hz
    rw [hz]
    simp [tsupport]
  rcases t with j | j | j | k | bb
  · exact hnull _ (hempty _ rfl) rfl
  · -- slim tags
    have hj := (Set.Finite.mem_toFinset _).mp j.2
    have hfull : sgpFullTag Q.toLocalChartFamily Z i sgn c zsgn zc (.inr (.inl j)) =
        sgpSlimModelBlock Q.toLocalChartFamily i sgn c j := rfl
    by_cases hji : j = i
    · -- the own tag: error zero
      subst hji
      rw [hfull]
      have hw : sgpTagWeight Q.toLocalChartFamily Z j (.inr (.inl j)) = 1 := by
        simp [sgpTagWeight]
      rw [hw, mul_one, mul_one]
      have hss : ρ j.1 / ρ j.1 = 1 := div_self hri.ne'
      have ha8 : |1 * (Q.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x + 0| ≤
          8 * (10 ^ 5 * Δ) := by rw [one_mul, add_zero]; linarith
      obtain ⟨h1, h2⟩ := sgp04_slim_tag_SGP4 Q Z hΔ j j hxL (by rw [hss]; norm_num)
        (σ := 1) (c := 0) (θ := 0)
        (a := (Q.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x)
        (dη := mvfderiv 𝓘(ℝ, E3) (Q.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord
          x w) zero_le_one w hν
        (by rw [hss]; simp) (by rw [hss]; simp) (hdv 1 (by norm_num))
      have hmodel : sgpSlimModelBlock Q.toLocalChartFamily j sgn c j =
          fun y => sgpBlockEmbed (WithLp.toLp 2 (y, (1 : ℝ))) := by
        funext y
        simp [sgpSlimModelBlock, sgpBlockEmbed_apply]
      rw [hss] at h1 h2
      have hW : sgpModelBlock (10 ^ 5 * Δ) 1
          (1 * (Q.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x + 0) =
          WithLp.toLp 2 ((Q.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x,
            (1 : ℝ)) := by
        rw [sgpModelBlock_apply, one_mul, add_zero, one_mul]
        have hp := sgpProfile_eq_one hℓ (by rw [one_mul, add_zero] at ha8; exact ha8)
        unfold sgpProfile at hp
        rw [hp, one_mul, mul_one]
      have hdW : fderiv ℝ (sgpModelBlock (10 ^ 5 * Δ) 1)
          (1 * (Q.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x + 0)
          (mvfderiv 𝓘(ℝ, E3) (Q.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord
            x w) = WithLp.toLp 2 (mvfderiv 𝓘(ℝ, E3)
              (Q.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x w, (0 : ℝ)) :=
        fderiv_sgpModelBlock_one_apply_SGP3 hℓ ha8 _
      rw [hW] at h1
      rw [one_mul (mvfderiv 𝓘(ℝ, E3) _ x w), hdW] at h2
      have hG : ∀ y : ℝ,
          DifferentiableAt ℝ (fun y : ℝ => (WithLp.toLp 2 (y, (1 : ℝ)) : WithLp 2 (ℝ × ℝ))) y :=
        fun y => ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm.differentiableAt).comp y
          (differentiableAt_id.prodMk (differentiableAt_const _))
      have hd := fderiv_isometry_comp_apply_SGP4 sgpBlockEmbed
        (hG ((Q.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x))
        (mvfderiv 𝓘(ℝ, E3) (Q.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x w)
      rw [fderiv_ownScalar_apply_SGP4] at hd
      rw [hmodel, hd]
      exact ⟨h1.trans (by nlinarith), h2.trans (by nlinarith)⟩
    rw [hfull]
    by_cases hjl : j.1 ∈ sgpSlimList Q.slim i.1
    · have hw : sgpTagWeight Q.toLocalChartFamily Z i (.inr (.inl j)) = 1 := by
        simp [sgpTagWeight, hjl]
      rw [hw, mul_one, mul_one]
      have hs := (sgpSlimList_bounds Q.toLocalChartFamily hΔ0 hΛ hLΛ hjl).2.1
      have hWd : Differentiable ℝ (sgpModelBlock (10 ^ 5 * Δ) (ρ j.1 / ρ i.1)) :=
        (contDiff_sgpModelBlock _ _).differentiable (by simp)
      have hmodel : sgpSlimModelBlock Q.toLocalChartFamily i sgn c j = fun y =>
          sgpBlockEmbed (sgpModelBlock (10 ^ 5 * Δ) (ρ j.1 / ρ i.1) (sgn j.1 * y + c j.1)) := by
        funext y
        simp [sgpSlimModelBlock, hji, hjl]
      have hd := fderiv_isometry_comp_apply_SGP4 sgpBlockEmbed
        (G := fun y => sgpModelBlock (10 ^ 5 * Δ) (ρ j.1 / ρ i.1) (sgn j.1 * y + c j.1))
        (a := (Q.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x)
        ((hWd _).comp _ (((differentiableAt_id.const_mul _).add_const _)))
        (mvfderiv 𝓘(ℝ, E3) (Q.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x w)
      rw [fderiv_affine_comp_apply_SGP4 (hWd _)] at hd
      rw [hmodel, hd]
      by_cases hxj : x ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1)
      · obtain ⟨hv, hder⟩ := hslim j.1 hjl hxj
        exact sgp04_slim_tag_SGP4 Q Z hΔ i j hxj hs.le hθ1 w hν hv hder (hdv _ (hsgn j.1))
      · -- outside the chart ball: both sides vanish to first order
        have hx : x ∉ tsupport (sgpQ3Cutoff Q.toLocalChartFamily Z (.inr (.inl j))) := by
          intro hx
          obtain ⟨h1, h2, h3, -⟩ := fc18_slim_row Q.toLocalChartFamily hΔ0 hj
          exact hxj (h3 (h2 (h1 hx)))
        have h0 : slimCutoffProfile_LC87 ((sgn j.1 * (Q.slim.centre i.1
            ((Set.Finite.mem_toFinset _).mp i.2)).coord x + c j.1) /
              (ρ j.1 / ρ i.1 * (10 ^ 5 * Δ))) = 0 := by
          by_contra hne
          exact hxj (hsupp j.1 hjl hne)
        obtain ⟨h1, h2⟩ := q3_tag_eq_zero_SGP4 Q Z _ hx w
        refine tag_errors_zero_SGP4 h1 h2 ?_ ?_ hκ hκν
        · beta_reduce
          rw [sgpModelBlock_eq_zero_SGP4 h0, map_zero]
        · rw [fderiv_sgpModelBlock_eq_zero_SGP3 h0, zero_apply, map_zero]
    · -- unlisted: the closed support misses `D_i`
      have hx : x ∉ tsupport (sgpQ3Cutoff Q.toLocalChartFamily Z (.inr (.inl j))) := by
        intro hx
        exact hjl ⟨hj, x, hx, hxD⟩
      refine hnull _ hx ?_
      funext y
      simp [sgpFullTag, sgpSlimModelBlock, hji, hjl]
  · exact hnull _ (hempty _ rfl) rfl
  · -- zero tags
    have hk := (Set.Finite.mem_toFinset _).mp k.2
    have hfull : sgpFullTag Q.toLocalChartFamily Z i sgn c zsgn zc (.inr (.inr (.inr (.inl k)))) =
        sgpZeroModelBlock Q.toLocalChartFamily Z i zsgn zc k := rfl
    rw [hfull]
    by_cases hm : sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i.1 k.1 hk
    · have hw : sgpTagWeight Q.toLocalChartFamily Z i (.inr (.inr (.inr (.inl k)))) = 1 := by
        simp [sgpTagWeight, hm]
      rw [hw, mul_one, mul_one]
      obtain ⟨hs0, hrad, hv, hder⟩ := hzero k.1 hk hm
      have hWd : Differentiable ℝ (zeroModelBlock ((Z.zero k.1 hk).radius / ρ i.1)) :=
        (contDiff_zeroModelBlock _).differentiable (by simp)
      have hmodel : sgpZeroModelBlock Q.toLocalChartFamily Z i zsgn zc k = fun y =>
          sgpBlockEmbed (zeroModelBlock ((Z.zero k.1 hk).radius / ρ i.1)
            (zsgn k.1 * y + zc k.1)) := by
        funext y
        simp [sgpZeroModelBlock, hm]
      have hd := fderiv_isometry_comp_apply_SGP4 sgpBlockEmbed
        (G := fun y => zeroModelBlock ((Z.zero k.1 hk).radius / ρ i.1) (zsgn k.1 * y + zc k.1))
        (a := (Q.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x)
        ((hWd _).comp _ (((differentiableAt_id.const_mul _).add_const _)))
        (mvfderiv 𝓘(ℝ, E3) (Q.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x w)
      rw [fderiv_affine_comp_apply_SGP4 (hWd _)] at hd
      rw [hmodel, hd]
      exact sgp04_zero_tag_SGP4 Q Z i k hs0 hrad hθ1 w hν hv hder (hdv _ (hzsgn k.1))
    · have hx :
          x ∉ tsupport (sgpQ3Cutoff Q.toLocalChartFamily Z (.inr (.inr (.inr (.inl k))))) := by
        intro hx
        exact hm ⟨x, hx, hxD⟩
      refine hnull _ hx ?_
      funext y
      simp [sgpFullTag, sgpZeroModelBlock, hm]
  · exact hnull _ (hempty _ rfl) rfl

/-- **(SG) assembled** (kernel of SGP04's row): under the per-tag inputs of
`sgp04_tag_bounds_SGP4` and SGP01's uniqueness of the zero support meeting `D_i`,
`‖ρ(i)⁻¹π₃𝓔⁰(x) − Φ_i(η_i x)‖ ≤ √((|J_i| + 2)(4Bθ)²)` and, along `w`,
`‖ρ(i)⁻¹dπ₃𝓔⁰(w) − DΦ_i(η_i x)(dη_i(w))‖ ≤ √((|J_i| + 2)(4Bθν)²)`. -/
theorem sgp04_approx_SGP4 (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (he : e ≤ 1 / 8) (i : Q.slim.finite_centres.toFinset) (sgn c zsgn zc : X → ℝ)
    (hsgn : ∀ j, |sgn j| ≤ 1) (hzsgn : ∀ k, |zsgn k| ≤ 1) {x : X}
    (hxD : x ∈ ball i.1 (95 / 100 * (1000000 * Δ) * ρ i.1))
    (hxL : x ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1))
    (hη : |(Q.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x| ≤ 8 * 10 ^ 5 * Δ)
    {θ ν : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (w : TangentSpace 𝓘(ℝ, E3) x) (hν : 0 ≤ ν)
    (hdη : |mvfderiv 𝓘(ℝ, E3) (Q.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x
      w| ≤ 2 * ν)
    (hslim : ∀ j (hj : j ∈ sgpSlimList Q.slim i.1), x ∈ ball j (10 ^ 6 * Δ * ρ j) →
      |ρ j / ρ i.1 * (Q.slim.centre j hj.1).coord x -
        (sgn j * (Q.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x + c j)| ≤ θ ∧
      |ρ j / ρ i.1 * mvfderiv 𝓘(ℝ, E3) (Q.slim.centre j hj.1).coord x w -
        sgn j * mvfderiv 𝓘(ℝ, E3)
          (Q.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x w| ≤ θ * ν)
    (hsupp : ∀ j ∈ sgpSlimList Q.slim i.1,
      slimCutoffProfile_LC87 ((sgn j * (Q.slim.centre i.1
        ((Set.Finite.mem_toFinset _).mp i.2)).coord x + c j) / (ρ j / ρ i.1 * (10 ^ 5 * Δ))) ≠ 0 →
      x ∈ ball j (10 ^ 6 * Δ * ρ j))
    (hzero : ∀ k (hk : k ∈ Z.centres), sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i.1 k hk →
      1 ≤ (Z.zero k hk).radius / ρ i.1 ∧
      MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (Z.zero k hk).radial x ∧
      |(Z.zero k hk).radius / ρ i.1 * (Z.zero k hk).radial x -
        (zsgn k * (Q.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x + zc k)| ≤ θ ∧
      |(Z.zero k hk).radius / ρ i.1 * mvfderiv 𝓘(ℝ, E3) (Z.zero k hk).radial x w -
        zsgn k * mvfderiv 𝓘(ℝ, E3)
          (Q.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x w| ≤ θ * ν)
    (huniq : ∀ k₁ (hk₁ : k₁ ∈ Z.centres) k₂ (hk₂ : k₂ ∈ Z.centres),
      sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i.1 k₁ hk₁ → sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i.1 k₂ hk₂ →
      k₁ = k₂) :
    ‖(ρ i.1)⁻¹ • cgpProjMap Q.toLocalChartFamily Z (cgpQ3Tags Q.toLocalChartFamily Z) x -
      sgpFullGraph Q.toLocalChartFamily Z i sgn c zsgn zc
        ((Q.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x)‖ ≤
      Real.sqrt ((((sgpSlimList Q.slim i.1).ncard : ℝ) + 2) * (4 * sgpBlockBound * θ) ^ 2) ∧
    ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
        (cgpProjMap Q.toLocalChartFamily Z (cgpQ3Tags Q.toLocalChartFamily Z)) x w -
      fderiv ℝ (sgpFullGraph Q.toLocalChartFamily Z i sgn c zsgn zc)
        ((Q.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x)
        (mvfderiv 𝓘(ℝ, E3) (Q.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x
          w)‖ ≤
      Real.sqrt ((((sgpSlimList Q.slim i.1).ncard : ℝ) + 2) * (4 * sgpBlockBound * θ * ν) ^ 2) := by
  have hΔ0 : 0 < Δ := by linarith
  have htag := sgp04_tag_bounds_SGP4 Q Z hΔ hΛ hLΛ i sgn c zsgn zc hsgn hzsgn hxD hxL hη hθ0 hθ1
    w hν hdη hslim hsupp hzero
  constructor
  · refine norm_le_of_tagWeight_SGP4 Q.toLocalChartFamily Z i _ (fun t => ?_) huniq le_rfl
    rw [PiLp.sub_apply, PiLp.smul_apply, cgpProjMap_Q3_eq_blockMap_SGP4, sgpFullGraph_apply]
    exact (htag t).1
  · refine norm_le_of_tagWeight_SGP4 Q.toLocalChartFamily Z i _ (fun t => ?_) huniq le_rfl
    have hcomp := mvfderiv_cgpProjMap_Q3_apply_SGP4 Q.toLocalChartFamily Z hΔ0 he x w t
    have hfd := fderiv_orthogonalBlocks_apply_SGP4
      (sgpFullTag Q.toLocalChartFamily Z i sgn c zsgn zc)
      (a := (Q.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x)
      (fun t => (contDiff_sgpFullTag Q.toLocalChartFamily Z i sgn c zsgn zc t).differentiable
        (by simp) _)
      (mvfderiv 𝓘(ℝ, E3) (Q.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x w) t
    rw [PiLp.sub_apply, PiLp.smul_apply, hcomp]
    change ‖(ρ i.1)⁻¹ • _ - fderiv ℝ (orthogonalBlocks (sgpFullTag Q.toLocalChartFamily Z i sgn c
      zsgn zc)) _ _ t‖ ≤ _
    rw [hfd]
    exact (htag t).2

end AllTags

section Row

/-- LC87's slim multiplicity constant is positive (a ratio of two positive model volumes). -/
theorem egp02SlimCount_pos_SGP4 : 0 < egp02SlimCount := by
  have hK : ¬ (0 < -((1 / 2000000 : ℝ) ^ 2)) := by
    have := sq_nonneg (1 / 2000000 : ℝ)
    linarith
  unfold egp02SlimCount
  exact div_pos (VolumeComparison.modelVolume_pos (by norm_num) (by norm_num)
      ⟨by norm_num, fun h => absurd h hK⟩)
    (VolumeComparison.modelVolume_pos (by norm_num) (by norm_num)
      ⟨by norm_num, fun h => absurd h hK⟩)

theorem four_le_sgpGraphBound_SGP4 : 4000 ≤ sgpGraphBound := by
  have hN := egp02SlimCount_pos_SGP4
  have hP := le_max_left sgpProfileBound zeroProfileBound
  have hP1 := sgpProfileBound_spec.1
  unfold sgpGraphBound
  have h1 : (2 : ℝ) ≤ egp02SlimCount + 2 := by linarith
  have h2 : (2 : ℝ) ≤ max sgpProfileBound zeroProfileBound + 1 := by linarith
  nlinarith

/-- `T ≥ 1600L` gives `s₀ ≥ T/20 ≥ 1`. -/
theorem one_le_div_twenty_SGP4 {Δ T : ℝ} (hΔ : 1 ≤ Δ) (hT : 1600 * (1000000 * Δ) ≤ T) :
    1 ≤ T / 20 := by
  rw [le_div_iff₀ (by norm_num)]
  linarith

/-- The model metrics of `LocalChartPacketsRVZ`, as a named local instance. -/
local instance instMetricNRVZ_SGP4 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsRVZ`, as a named local instance. -/
local instance instChartedNRVZ_SGP4 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsRVZ`, as a named local instance. -/
local instance instMetricCRVZ_SGP4 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **SGP04 (SG) on the actual merged family.** For `Δ ≥ 1`, the exclusion quality `β₂` and
`0 < e < 1/100` there is an early `θ = e/(10C_*)` and thresholds `Lc, η₀` such that for EVERY actual
`P : LocalChartPacketsRVZ … vs ζ Λz` with SGP03's hypotheses at `θ` (slim and zero parts) and every
actual slim reference `i` there are signs and translations (`sgn, c` for the listed slim charts,
`zsgn, zc` for the meeting zero support) such that the full model `Φ_i = sgpFullGraph` satisfies
(SG) on `{|η_i| ≤ 8ℓ}`: `‖ρ(i)⁻¹π₃𝓔⁰ − Φ_iη_i‖ < e` and
`‖ρ(i)⁻¹dπ₃𝓔⁰(w) − DΦ_i(η_i)(dη_i(w))‖ ≤ e√(ρ(i)⁻²g(w, w))`. -/
theorem sgp04_row {Δ β₂ eg : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1) (heg : 0 < eg)
    (heg1 : eg < 1 / 100) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 →
        e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T →
        0 < σs → σs < θ ^ 2 / 10 ^ 6 → vs < θ / 100 →
        0 < ζ → ζ < θ ^ 2 / 10 ^ 6 → ζ < 1 / (100 * (1000000 * Δ)) →
        εr < θ / (100 * (1000000 * Δ)) →
        ∀ i : P.toLocalChartFamily.slim.finite_centres.toFinset, ∃ sgn c zsgn zc : X → ℝ,
          (∀ j, |sgn j| ≤ 1) ∧ (∀ k, |zsgn k| ≤ 1) ∧
          ∀ x ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1),
            |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x| ≤
              8 * 10 ^ 5 * Δ →
            ‖(ρ i.1)⁻¹ • cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ3Tags P.toLocalChartFamily P.zero) x -
              sgpFullGraph P.toLocalChartFamily P.zero i sgn c zsgn zc
                ((P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x)‖ < eg ∧
            ∀ w : TangentSpace 𝓘(ℝ, E3) x,
              ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                  (cgpQ3Tags P.toLocalChartFamily P.zero)) x w -
                fderiv ℝ (sgpFullGraph P.toLocalChartFamily P.zero i sgn c zsgn zc)
                  ((P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x)
                  (mvfderiv 𝓘(ℝ, E3) (P.slim.centre i.1
                    ((Set.Finite.mem_toFinset _).mp i.2)).coord x w)‖ ≤
                eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner x w w) := by
  have hG := four_le_sgpGraphBound_SGP4
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = eg / (10 * sgpGraphBound) := ⟨_, rfl⟩
  have hθ : 0 < θ := by rw [hθdef]; positivity
  have hθ1 : θ < 1 := by
    rw [hθdef, div_lt_one (by positivity)]
    linarith
  have hE : (0 : ℝ) < θ ^ 2 / (2 * 10 ^ 6) := by positivity
  have hEθ : θ ^ 2 / (2 * 10 ^ 6) < θ ^ 2 / 10 ^ 6 :=
    div_lt_div_of_pos_left (by positivity) (by positivity) (by norm_num)
  have hθ2 : θ ^ 2 / 10 ^ 6 < 1 / 100 := by
    have : θ ^ 2 < 1 := by nlinarith
    rw [div_lt_iff₀ (by norm_num)]
    linarith
  have heg25 : 2 / 5 * eg < eg := by linarith
  obtain ⟨Lc₁, η₁, hLc₁, hη₁, hrow₁⟩ := sgp03_row hΔ hβ₂ hβ₂1 hθ hθ1 hE hEθ
  obtain ⟨Lc₂, η₂, hLc₂, hη₂, hrow₂⟩ := sgp03_zero_row hΔ hβ₂ hβ₂1 hθ hθ1 hE hEθ
  refine ⟨θ, hθ, hθ1, max Lc₁ Lc₂, min η₁ η₂, lt_max_of_lt_left hLc₁, lt_min hη₁ hη₂, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hβ2 hβ1 hLmax hΛ hLΛ he hT hΛzT hσs hσθ hvθ hζ hζθ hζL hεr i
  classical
  have hi := (Set.Finite.mem_toFinset _).mp i.2
  have hΔ0 : 0 < Δ := lt_of_lt_of_le one_pos hΔ
  have hri := hρ i.1
  have hσ1 : σs ≤ 1 / 100 := (hσθ.trans hθ2).le
  have hσ2 : 1 + σs ≤ 2 := by linarith
  have he8 : e ≤ 1 / 8 := he.le.trans (by norm_num)
  have hT20 : 1 ≤ T / 20 := one_le_div_twenty_SGP4 hΔ hT
  have hS := hrow₁ X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
    P.toLocalChartPacketsRV hβ2 (hβ1.trans (min_le_left _ _)) ((le_max_left _ _).trans hLmax)
    hΛ hLΛ hσs hσθ hvθ i.1 hi
  have hZ := hrow₂ X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hβ2 (hβ1.trans (min_le_right _ _)) ((le_max_right _ _).trans hLmax) hΛ hLΛ he hT hΛzT hσs
    hσθ hvθ hζ hζθ hζL hεr i.1 hi
  obtain ⟨-, hN, -, huniq, hzero01, hcore⟩ := sgp01_row P.toLocalChartPacketsR hΛ hΔ hLΛ he hT
    hσs.le hσ1 hi
  obtain ⟨hT0, hℓ0, hsmall⟩ := sgp01_zero_smallness_ZERO hΔ hLΛ hT
  -- the signs of the listed slim charts (SGP03) and of the meeting zero support (SGP03, zero)
  obtain ⟨sgn, hsgndef⟩ : ∃ sgn : X → ℝ, ∀ j, sgn j =
      if hj : j ∈ sgpSlimList P.slim i.1 then Classical.choose (hS j hj) else 0 :=
    ⟨_, fun j => rfl⟩
  obtain ⟨zsgn, hzsgndef⟩ : ∃ zsgn : X → ℝ, ∀ k, zsgn k =
      if hk : k ∈ P.zero.centres then
        (if hm : sgpZeroMeets P.zero (Δ := Δ) (ρ := ρ) i.1 k hk then Classical.choose (hZ k hk hm)
          else 0) else 0 :=
    ⟨_, fun k => rfl⟩
  obtain ⟨zc, hzcdef⟩ : ∃ zc : X → ℝ, ∀ k, zc k =
      if hk : k ∈ P.zero.centres then
        (P.zero.zero k hk).radius / ρ i.1 * (P.zero.zero k hk).radial i.1 else 0 :=
    ⟨_, fun k => rfl⟩
  have hsgn1 : ∀ j, |sgn j| ≤ 1 := by
    intro j
    rw [hsgndef]
    split_ifs with hj
    · rcases (Classical.choose_spec (hS j hj)).1 with h | h <;> rw [h] <;> norm_num
    · norm_num
  have hzsgn1 : ∀ k, |zsgn k| ≤ 1 := by
    intro k
    rw [hzsgndef]
    split_ifs with hk hm
    · rcases (Classical.choose_spec (hZ k hk hm)).1 with h | h <;> rw [h] <;> norm_num
    · norm_num
    · norm_num
  refine ⟨sgn, fun j => ρ j / ρ i.1 * sgpRaw P.slim j i.1, zsgn, zc, hsgn1, hzsgn1,
    fun x hxL hη => ?_⟩
  have h105 : (10 : ℝ) ^ 5 * Δ = 100000 * Δ := by norm_num
  have h106 : (10 : ℝ) ^ 6 * Δ = 1000000 * Δ := by norm_num
  have hL0 : 0 < 1000000 * Δ := by positivity
  have hxD : x ∈ ball i.1 (95 / 100 * (1000000 * Δ) * ρ i.1) := by
    have h := hcore x hxL (by rw [← h105]; linarith)
    refine ball_subset_ball ?_ h
    rw [h106]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hL0.le) hri.le
  have hsq : ∀ w : TangentSpace 𝓘(ℝ, E3) x, Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner x w w) =
      (ρ i.1)⁻¹ * Real.sqrt (g.inner x w w) := by
    intro w
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hdη : ∀ w : TangentSpace 𝓘(ℝ, E3) x,
      |mvfderiv 𝓘(ℝ, E3) (P.slim.centre i.1 hi).coord x w| ≤
        2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner x w w) := by
    intro w
    have hb := (P.slim.centre i.1 hi).abs_mvfderiv_le_SGP2 hσs.le hxL w
    rw [hsq]
    have hg0 := Real.sqrt_nonneg (g.inner x w w)
    have hk : 0 ≤ (ρ i.1)⁻¹ * Real.sqrt (g.inner x w w) := by positivity
    calc |mvfderiv 𝓘(ℝ, E3) (P.slim.centre i.1 hi).coord x w|
        ≤ (1 + σs) * (ρ i.1)⁻¹ * Real.sqrt (g.inner x w w) := hb
      _ = (1 + σs) * ((ρ i.1)⁻¹ * Real.sqrt (g.inner x w w)) := by ring
      _ ≤ 2 * ((ρ i.1)⁻¹ * Real.sqrt (g.inner x w w)) := mul_le_mul_of_nonneg_right hσ2 hk
  have hsupp : ∀ j ∈ sgpSlimList P.slim i.1,
      slimCutoffProfile_LC87 ((sgn j * (P.slim.centre i.1 hi).coord x +
        ρ j / ρ i.1 * sgpRaw P.slim j i.1) / (ρ j / ρ i.1 * (10 ^ 5 * Δ))) ≠ 0 →
      x ∈ ball j (10 ^ 6 * Δ * ρ j) := by
    intro j hj hf
    have hsj : sgn j = Classical.choose (hS j hj) := by rw [hsgndef, dite_eq_left hj]
    obtain ⟨-, -, -, hM, -⟩ := Classical.choose_spec (hS j hj)
    rw [hsj, h105] at hf
    have h := hM x hxD hf
    refine ball_subset_ball ?_ h
    rw [h106]
    have h1 : 91 / 100 * (1000000 * Δ) ≤ 1000000 * Δ := by
      have := hL0.le
      linarith
    exact mul_le_mul_of_nonneg_right h1 (hρ j).le
  have hslim : ∀ w : TangentSpace 𝓘(ℝ, E3) x, ∀ j (hj : j ∈ sgpSlimList P.slim i.1),
      x ∈ ball j (10 ^ 6 * Δ * ρ j) →
      |ρ j / ρ i.1 * (P.slim.centre j hj.1).coord x -
        (sgn j * (P.slim.centre i.1 hi).coord x + ρ j / ρ i.1 * sgpRaw P.slim j i.1)| ≤ θ ∧
      |ρ j / ρ i.1 * mvfderiv 𝓘(ℝ, E3) (P.slim.centre j hj.1).coord x w -
        sgn j * mvfderiv 𝓘(ℝ, E3) (P.slim.centre i.1 hi).coord x w| ≤
          θ * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner x w w) := by
    intro w j hj hxj
    have hsj : sgn j = Classical.choose (hS j hj) := by rw [hsgndef, dite_eq_left hj]
    obtain ⟨-, -, hD, -, hV⟩ := Classical.choose_spec (hS j hj)
    have hxj' : x ∈ ball j (1000000 * Δ * ρ j) := by rw [← h106]; exact hxj
    rw [hsj]
    exact ⟨(hV x hxD hxj').le, hD x hxD hxj' w⟩
  have hzero : ∀ w : TangentSpace 𝓘(ℝ, E3) x, ∀ k (hk : k ∈ P.zero.centres),
      sgpZeroMeets P.zero (Δ := Δ) (ρ := ρ) i.1 k hk →
      1 ≤ (P.zero.zero k hk).radius / ρ i.1 ∧
      MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (P.zero.zero k hk).radial x ∧
      |(P.zero.zero k hk).radius / ρ i.1 * (P.zero.zero k hk).radial x -
        (zsgn k * (P.slim.centre i.1 hi).coord x + zc k)| ≤ θ ∧
      |(P.zero.zero k hk).radius / ρ i.1 * mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x w -
        zsgn k * mvfderiv 𝓘(ℝ, E3) (P.slim.centre i.1 hi).coord x w| ≤
          θ * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner x w w) := by
    intro w k hk hm
    have hzk : zsgn k = Classical.choose (hZ k hk hm) := by
      rw [hzsgndef, dite_eq_left hk, dite_eq_left hm]
    have hzck : zc k = (P.zero.zero k hk).radius / ρ i.1 * (P.zero.zero k hk).radial i.1 := by
      rw [hzcdef, dite_eq_left hk]
    obtain ⟨-, -, hD, hV⟩ := Classical.choose_spec (hZ k hk hm)
    obtain ⟨hs0, -⟩ := hzero01 k hk hm
    obtain ⟨-, O, hOo, hOsub, hOc⟩ :=
      (zero_meeting_clauses_ZERO P.toLocalChartPacketsR hΛ he hT0 i.1 hℓ0 hsmall).2 k hk hm
    have hdiff : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (P.zero.zero k hk).radial x :=
      (hOc.contMDiffAt (hOo.mem_nhds (hOsub hxD))).mdifferentiableAt (by simp)
    rw [hzk, hzck]
    exact ⟨hT20.trans hs0, hdiff, (hV x hxD).le, hD x hxD w⟩
  have hN0 : (0 : ℝ) ≤ ((sgpSlimList P.slim i.1).ncard : ℝ) := Nat.cast_nonneg _
  refine ⟨?_, fun w => ?_⟩
  · obtain ⟨hv, -⟩ := sgp04_approx_SGP4 P.toLocalChartFamilyQ P.zero hΔ hΛ hLΛ he8 i
      sgn (fun j => ρ j / ρ i.1 * sgpRaw P.slim j i.1) zsgn zc hsgn1 hzsgn1 hxD hxL hη hθ.le
      hθ1.le 0 (Real.sqrt_nonneg _) (hdη 0) (hslim 0) hsupp (hzero 0) huniq
    have hb := sgp04_budget_SGP4 hN0 hN heg zero_le_one
    rw [mul_one, mul_one, ← hθdef] at hb
    exact lt_of_le_of_lt (hv.trans hb) heg25
  · obtain ⟨-, hd⟩ := sgp04_approx_SGP4 P.toLocalChartFamilyQ P.zero hΔ hΛ hLΛ he8 i
      sgn (fun j => ρ j / ρ i.1 * sgpRaw P.slim j i.1) zsgn zc hsgn1 hzsgn1 hxD hxL hη hθ.le
      hθ1.le w (Real.sqrt_nonneg _) (hdη w) (hslim w) hsupp (hzero w) huniq
    have hb := sgp04_budget_SGP4 hN0 hN heg (Real.sqrt_nonneg ((ρ i.1)⁻¹ ^ 2 * g.inner x w w))
    rw [← hθdef] at hb
    exact hd.trans (hb.trans (mul_le_mul_of_nonneg_right heg25.le (Real.sqrt_nonneg _)))

end Row

end DifferentialGeometry.Geometry.Collapse
