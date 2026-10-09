import DifferentialGeometry.Geometry.Fibration.GraphModelBlocks
import DifferentialGeometry.Geometry.Fibration.ActualSlimComparisonList
import DifferentialGeometry.Analysis.Calculus.OrthogonalBlockDerivatives
import DifferentialGeometry.Analysis.Calculus.SecondDerivativeComposition

/-!
# SGP04: the model slim graph `Φ_i` and its early derivative modulus

Blueprint `master207B.tex`, SGP04 (`thm:fibration-actual-slim-graph`, B:4602–4665). For an actual
slim reference `i` of CGP01's map `𝓔⁰ = cgpGlobalMap L Z`, the model graph `Φ_i : ℝ → Q₃` has the
own block `(a, 1)` (on the axis of `ℝ²`), for every listed slim chart `j ∈ J_i = sgpSlimList`,
`j ≠ i`, the block `(λ f(λ/(s_jℓ)), s_j f(λ/(s_jℓ)))`, `λ = sgn_j a + c_j`, `s_j = ρ(j)/ρ(i)`,
`ℓ = 10⁵Δ` (C14-KC3's shared `sgpModelBlock` with LC87's profile `f`), and zero elsewhere
(`sgpModelGraph`, frozen form). `sgpFullGraph` adds FC05's zero block
`F_{s₀}(λ₀(a))` (`zeroModelBlock`, `s₀ = R₀/ρ(i)`, `λ₀(a) = zsgn a + zc`) at the zero tags whose
support meets `D_i = B(i, .95Lρ(i))` — the model used by (SG).

* `sgpBlockEmbed`: `(u, m) ↦ (u e₀, m)`, a linear isometry onto the axis of a block.
* `contDiff_sgpModelGraph`, `sgpModelGraph_own`, `contDiff_sgpFullGraph`, `sgpFullGraph_own`.
* `sum_cgpTag_le_SGP3`: the counting step — a nonnegative function on the tags of `𝓔⁰` that is at
  most `c` on listed slim tags and on meeting zero tags and vanishes elsewhere sums to at most
  `(N + 1)c` (`|J_i| ≤ N`, at most one meeting zero support).
* `sgp04_model_bounds` / `sgp04_full_model_bounds`: `‖DΦ_i‖, ‖D²Φ_i‖, ‖iteratedFDeriv 2 Φ_i‖ ≤ C_*`,
  `C_* = sgpGraphBound = 1000(N_* + 2)(P_* + 1)` with `N_* = egp02SlimCount` (LC87's slim
  multiplicity) and `P_* = max(P_slim, P_zero)` (the profiles' early `C²` constants): early
  constants, chosen before `Δ, β₂` and noncollapse.
* Profile facts used by (SG): `fderiv_slimCutoffProfile_eq_zero_of_abs_le` (plateau),
  `fderiv_sgpModelBlock_eq_zero_SGP3` (where the profile vanishes),
  `fderiv_sgpModelBlock_one_apply_SGP3` (the own block on the plateau).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold
open scoped ContDiff Topology Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Embed

/-- `(u, m) ↦ (u e₀, m)`: a scalar model block placed on the axis of a block of `𝓔⁰`. -/
def sgpBlockEmbed : WithLp 2 (ℝ × ℝ) →ₗᵢ[ℝ] WithLp 2 (ℝ² × ℝ) where
  toFun m := WithLp.toLp 2 (planeAxis m.fst, m.snd)
  map_add' m n := by
    change WithLp.toLp 2 (planeAxis (m.fst + n.fst), m.snd + n.snd) = _
    rw [map_add]
    rfl
  map_smul' r m := by
    change WithLp.toLp 2 (planeAxis (r • m.fst), r • m.snd) = _
    rw [map_smul]
    rfl
  norm_map' m := by
    rw [WithLp.prod_norm_eq_of_L2, WithLp.prod_norm_eq_of_L2]
    change Real.sqrt (‖planeAxis m.fst‖ ^ 2 + ‖m.snd‖ ^ 2) = _
    simp only [norm_planeAxis, Real.norm_eq_abs]

theorem sgpBlockEmbed_apply (u v : ℝ) :
    sgpBlockEmbed (WithLp.toLp 2 (u, v)) = WithLp.toLp 2 (planeAxis u, v) := rfl

end Embed

section Profile

theorem slimCutoffProfile_mem_Icc_SGP3 (t : ℝ) : slimCutoffProfile_LC87 t ∈ Icc 0 1 :=
  intervalPlateauProfile_mem_Icc _ _ _ _ t

theorem differentiable_slimCutoffProfile_SGP3 : Differentiable ℝ slimCutoffProfile_LC87 :=
  (contDiff_intervalPlateauProfile (-89 / 10 : ℝ) (-8) 8 (89 / 10)).differentiable (by simp)

/-- LC87's slim profile has zero derivative on its plateau `|t| ≤ 8` (a global maximum). -/
theorem fderiv_slimCutoffProfile_eq_zero_of_abs_le {t : ℝ} (ht : |t| ≤ 8) :
    fderiv ℝ slimCutoffProfile_LC87 t = 0 := by
  apply IsLocalMax.fderiv_eq_zero
  have h1 : slimCutoffProfile_LC87 t = 1 :=
    intervalPlateauProfile_one (by norm_num) (by norm_num)
      ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  exact Filter.Eventually.of_forall fun y => by
    rw [h1]
    exact (slimCutoffProfile_mem_Icc_SGP3 y).2

/-- LC87's slim profile has zero derivative where it vanishes (a global minimum). -/
theorem fderiv_slimCutoffProfile_eq_zero_of_eq_zero {t : ℝ} (ht : slimCutoffProfile_LC87 t = 0) :
    fderiv ℝ slimCutoffProfile_LC87 t = 0 := by
  apply IsLocalMin.fderiv_eq_zero
  exact Filter.Eventually.of_forall fun y => by
    rw [ht]
    exact (slimCutoffProfile_mem_Icc_SGP3 y).1

theorem deriv_slimCutoffProfile_eq_zero_of_fderiv {t : ℝ}
    (h : fderiv ℝ slimCutoffProfile_LC87 t = 0) : deriv slimCutoffProfile_LC87 t = 0 := by
  change fderiv ℝ slimCutoffProfile_LC87 t 1 = 0
  rw [h]
  rfl

/-- The derivative of the slim model block. -/
theorem hasDerivAt_sgpModelBlock_SGP3 (ℓ s y : ℝ) :
    HasDerivAt (sgpModelBlock ℓ s)
      (WithLp.toLp 2 (deriv slimCutoffProfile_LC87 (y / (s * ℓ)) / (s * ℓ) * y +
          slimCutoffProfile_LC87 (y / (s * ℓ)),
        s * (deriv slimCutoffProfile_LC87 (y / (s * ℓ)) / (s * ℓ)))) y := by
  have hf := differentiable_slimCutoffProfile_SGP3
  have h1 : HasDerivAt (fun y => slimCutoffProfile_LC87 (y / (s * ℓ)))
      (deriv slimCutoffProfile_LC87 (y / (s * ℓ)) / (s * ℓ)) y := by
    have h := (hf (y / (s * ℓ))).hasDerivAt.comp y ((hasDerivAt_id y).div_const (s * ℓ))
    exact h.congr_deriv (by rw [mul_one_div])
  have h2 : HasDerivAt (fun y => slimCutoffProfile_LC87 (y / (s * ℓ)) * y)
      (deriv slimCutoffProfile_LC87 (y / (s * ℓ)) / (s * ℓ) * y +
        slimCutoffProfile_LC87 (y / (s * ℓ)) * 1) y := h1.mul (hasDerivAt_id y)
  have h3 : HasDerivAt (fun y => s * slimCutoffProfile_LC87 (y / (s * ℓ)))
      (s * (deriv slimCutoffProfile_LC87 (y / (s * ℓ)) / (s * ℓ))) y := h1.const_mul s
  have hp := h2.prodMk h3
  have hc := ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm :
    (ℝ × ℝ) →L[ℝ] WithLp 2 (ℝ × ℝ)).hasFDerivAt.comp_hasDerivAt y hp
  have hfun : sgpModelBlock ℓ s = (((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm :
      (ℝ × ℝ) →L[ℝ] WithLp 2 (ℝ × ℝ)) ∘ fun y => (slimCutoffProfile_LC87 (y / (s * ℓ)) * y,
        s * slimCutoffProfile_LC87 (y / (s * ℓ)))) := by
    funext x
    rw [sgpModelBlock_apply]
    rfl
  rw [hfun]
  convert hc using 1
  rw [mul_one]
  rfl

/-- Where LC87's profile vanishes, the slim model block has zero derivative. -/
theorem fderiv_sgpModelBlock_eq_zero_SGP3 {ℓ s y : ℝ}
    (h : slimCutoffProfile_LC87 (y / (s * ℓ)) = 0) : fderiv ℝ (sgpModelBlock ℓ s) y = 0 := by
  have hd := deriv_slimCutoffProfile_eq_zero_of_fderiv
    (fderiv_slimCutoffProfile_eq_zero_of_eq_zero h)
  rw [(hasDerivAt_sgpModelBlock_SGP3 ℓ s y).hasFDerivAt.fderiv, h, hd]
  ext1
  simp

/-- On the plateau `|a| ≤ 8ℓ` the model block of scale ratio one has derivative `h ↦ (h, 0)`. -/
theorem fderiv_sgpModelBlock_one_apply_SGP3 {ℓ a : ℝ} (hℓ : 0 < ℓ) (ha : |a| ≤ 8 * ℓ) (h : ℝ) :
    fderiv ℝ (sgpModelBlock ℓ 1) a h = WithLp.toLp 2 (h, 0) := by
  have hq : |a / (1 * ℓ)| ≤ 8 := by
    rw [one_mul, abs_div, abs_of_pos hℓ, div_le_iff₀ hℓ]
    exact ha
  have h1 : slimCutoffProfile_LC87 (a / (1 * ℓ)) = 1 :=
    intervalPlateauProfile_one (by norm_num) (by norm_num)
      ⟨by linarith [neg_abs_le (a / (1 * ℓ))], by linarith [le_abs_self (a / (1 * ℓ))]⟩
  have hd := deriv_slimCutoffProfile_eq_zero_of_fderiv
    (fderiv_slimCutoffProfile_eq_zero_of_abs_le hq)
  rw [(hasDerivAt_sgpModelBlock_SGP3 ℓ 1 a).hasFDerivAt.fderiv, h1, hd]
  rw [ContinuousLinearMap.toSpanSingleton_apply, ← WithLp.toLp_smul]
  congr 1
  simp

end Profile

section Model

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

variable (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

/-- The zero support of the zero ball at `k` meets SGP01's `D_i = B(i, .95Lρ(i))`. -/
def sgpZeroMeets (i k : X) (hk : k ∈ Z.centres) : Prop :=
  (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile ((Z.zero k hk).radial y)) ∩
    ball i (95 / 100 * (1000000 * Δ) * ρ i)).Nonempty

open Classical in
/-- The slim block of SGP04's model graph at the slim tag `j` (reference tag `i`): the own block
`(a, 1)`; for a listed `j ≠ i` the block `(λ f(λ/(s_jℓ)), s_j f(λ/(s_jℓ)))`, `λ = sgn_j a + c_j`;
zero for unlisted `j`. -/
def sgpSlimModelBlock (i : L.slim.finite_centres.toFinset) (sgn c : X → ℝ)
    (j : L.slim.finite_centres.toFinset) (a : ℝ) : WithLp 2 (ℝ² × ℝ) :=
  if j = i then WithLp.toLp 2 (planeAxis a, 1)
  else if j.1 ∈ sgpSlimList L.slim i.1 then
    sgpBlockEmbed (sgpModelBlock (10 ^ 5 * Δ) (ρ j.1 / ρ i.1) (sgn j.1 * a + c j.1))
  else 0

open Classical in
/-- The zero block of SGP04's full model graph at the zero tag `k`: FC05's
`F_{s₀}(zsgn a + zc)`, `s₀ = R₀/ρ(i)`, when the zero support meets `D_i`; zero otherwise. -/
def sgpZeroModelBlock (i : L.slim.finite_centres.toFinset) (zsgn zc : X → ℝ)
    (k : Z.finite_centres.toFinset) (a : ℝ) : WithLp 2 (ℝ² × ℝ) :=
  if sgpZeroMeets Z (Δ := Δ) i.1 k.1 ((Set.Finite.mem_toFinset _).mp k.2) then
    sgpBlockEmbed (zeroModelBlock ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius /
      ρ i.1) (zsgn k.1 * a + zc k.1))
  else 0

/-- The blocks of SGP04's (frozen) slim model graph: slim blocks, zero elsewhere. -/
def sgpModelTag (i : L.slim.finite_centres.toFinset) (sgn c : X → ℝ) :
    CGPTag L Z → ℝ → WithLp 2 (ℝ² × ℝ)
  | .inr (.inl j) => sgpSlimModelBlock L i sgn c j
  | _ => fun _ => 0

/-- **SGP04's model slim graph** `Φ_i : ℝ → Q₃` (frozen form): own block `(a, 1)`, the listed
slim blocks, zero elsewhere. -/
def sgpModelGraph (i : L.slim.finite_centres.toFinset) (sgn c : X → ℝ) :
    ℝ → BlockSpace (fun _ : CGPTag L Z => ℝ²) :=
  orthogonalBlocks (sgpModelTag L Z i sgn c)

/-- The blocks of SGP04's full model graph: the slim blocks and FC05's meeting zero block. -/
def sgpFullTag (i : L.slim.finite_centres.toFinset) (sgn c zsgn zc : X → ℝ) :
    CGPTag L Z → ℝ → WithLp 2 (ℝ² × ℝ)
  | .inr (.inl j) => sgpSlimModelBlock L i sgn c j
  | .inr (.inr (.inr (.inl k))) => sgpZeroModelBlock L Z i zsgn zc k
  | _ => fun _ => 0

/-- **SGP04's full model graph** `Φ_i : ℝ → Q₃` (the model of (SG)): `sgpModelGraph` plus the
zero block of the zero support meeting `D_i`. -/
def sgpFullGraph (i : L.slim.finite_centres.toFinset) (sgn c zsgn zc : X → ℝ) :
    ℝ → BlockSpace (fun _ : CGPTag L Z => ℝ²) :=
  orthogonalBlocks (sgpFullTag L Z i sgn c zsgn zc)

theorem sgpModelGraph_apply (i : L.slim.finite_centres.toFinset) (sgn c : X → ℝ) (a : ℝ)
    (t : CGPTag L Z) : sgpModelGraph L Z i sgn c a t = sgpModelTag L Z i sgn c t a := rfl

theorem sgpFullGraph_apply (i : L.slim.finite_centres.toFinset) (sgn c zsgn zc : X → ℝ)
    (a : ℝ) (t : CGPTag L Z) :
    sgpFullGraph L Z i sgn c zsgn zc a t = sgpFullTag L Z i sgn c zsgn zc t a := rfl

/-- The own block of `Φ_i` is `(a, 1)`. -/
theorem sgpModelGraph_own (i : L.slim.finite_centres.toFinset) (sgn c : X → ℝ) (a : ℝ) :
    sgpModelGraph L Z i sgn c a (.inr (.inl i)) = WithLp.toLp 2 (planeAxis a, 1) := by
  rw [sgpModelGraph_apply]
  change sgpSlimModelBlock L i sgn c i a = _
  simp [sgpSlimModelBlock]

theorem sgpFullGraph_own (i : L.slim.finite_centres.toFinset) (sgn c zsgn zc : X → ℝ)
    (a : ℝ) :
    sgpFullGraph L Z i sgn c zsgn zc a (.inr (.inl i)) = WithLp.toLp 2 (planeAxis a, 1) := by
  rw [sgpFullGraph_apply]
  change sgpSlimModelBlock L i sgn c i a = _
  simp [sgpSlimModelBlock]

theorem contDiff_sgpSlimModelBlock (i : L.slim.finite_centres.toFinset) (sgn c : X → ℝ)
    (j : L.slim.finite_centres.toFinset) : ContDiff ℝ ∞ (sgpSlimModelBlock L i sgn c j) := by
  classical
  unfold sgpSlimModelBlock
  split_ifs
  · have h : ContDiff ℝ ∞ fun a : ℝ => ((a, (1 : ℝ)) : ℝ × ℝ) :=
      contDiff_id.prodMk contDiff_const
    have h2 : ContDiff ℝ ∞ fun a : ℝ => ((planeAxis a, (1 : ℝ)) : ℝ² × ℝ) :=
      (planeAxis.contDiff).prodMk contDiff_const
    exact ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ² ℝ).symm :
      (ℝ² × ℝ) →L[ℝ] WithLp 2 (ℝ² × ℝ)).contDiff.comp h2
  · exact sgpBlockEmbed.toContinuousLinearMap.contDiff.comp
      ((contDiff_sgpModelBlock _ _).comp ((contDiff_const.mul contDiff_id).add contDiff_const))
  · exact contDiff_const

theorem contDiff_sgpZeroModelBlock (i : L.slim.finite_centres.toFinset) (zsgn zc : X → ℝ)
    (k : Z.finite_centres.toFinset) : ContDiff ℝ ∞ (sgpZeroModelBlock L Z i zsgn zc k) := by
  classical
  unfold sgpZeroModelBlock
  split_ifs
  · exact sgpBlockEmbed.toContinuousLinearMap.contDiff.comp
      ((contDiff_zeroModelBlock _).comp ((contDiff_const.mul contDiff_id).add contDiff_const))
  · exact contDiff_const

theorem contDiff_sgpModelTag (i : L.slim.finite_centres.toFinset) (sgn c : X → ℝ)
    (t : CGPTag L Z) : ContDiff ℝ ∞ (sgpModelTag L Z i sgn c t) := by
  rcases t with j | j | j | k | bb
  · exact contDiff_const
  · exact contDiff_sgpSlimModelBlock L i sgn c j
  · exact contDiff_const
  · exact contDiff_const
  · exact contDiff_const

theorem contDiff_sgpFullTag (i : L.slim.finite_centres.toFinset) (sgn c zsgn zc : X → ℝ)
    (t : CGPTag L Z) : ContDiff ℝ ∞ (sgpFullTag L Z i sgn c zsgn zc t) := by
  rcases t with j | j | j | k | bb
  · exact contDiff_const
  · exact contDiff_sgpSlimModelBlock L i sgn c j
  · exact contDiff_const
  · exact contDiff_sgpZeroModelBlock L Z i zsgn zc k
  · exact contDiff_const

/-- `Φ_i` is smooth. -/
theorem contDiff_sgpModelGraph (i : L.slim.finite_centres.toFinset) (sgn c : X → ℝ) :
    ContDiff ℝ ∞ (sgpModelGraph L Z i sgn c) :=
  contDiff_orthogonalBlocks (contDiff_sgpModelTag L Z i sgn c)

theorem contDiff_sgpFullGraph (i : L.slim.finite_centres.toFinset) (sgn c zsgn zc : X → ℝ) :
    ContDiff ℝ ∞ (sgpFullGraph L Z i sgn c zsgn zc) :=
  contDiff_orthogonalBlocks (contDiff_sgpFullTag L Z i sgn c zsgn zc)

end Model

section Bounds

/-- **Weighted orthogonal summation for iterated derivatives.** If the `t`-th block of
`orthogonalBlocks f` has `n`-th derivative at most `b t` at `a` (`n ≤ 2`), the assembled map has
`n`-th derivative at most `√(Σ b_t²)`. -/
theorem norm_iteratedFDeriv_orthogonalBlocks_le_SGP3 {ι : Type*} [Fintype ι] {F : ι → Type*}
    [∀ t, NormedAddCommGroup (F t)] [∀ t, InnerProductSpace ℝ (F t)] (f : ∀ t, ℝ → F t)
    (hf : ∀ t, ContDiff ℝ 2 (f t)) {n : ℕ} (hn : n ≤ 2) (a : ℝ) (bd : ι → ℝ)
    (hb : ∀ t, ‖iteratedFDeriv ℝ n (f t) a‖ ≤ bd t) :
    ‖iteratedFDeriv ℝ n (orthogonalBlocks f) a‖ ≤ Real.sqrt (∑ t, bd t ^ 2) := by
  have hW : ContDiff ℝ 2 (orthogonalBlocks f) := contDiff_orthogonalBlocks hf
  have hn' : (n : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hn
  have hcomp : ∀ t (m : Fin n → ℝ), (iteratedFDeriv ℝ n (orthogonalBlocks f) a m) t =
      iteratedFDeriv ℝ n (f t) a m := by
    intro t m
    have hft : f t = (PiLp.proj 2 (𝕜 := ℝ) F t) ∘ orthogonalBlocks f := rfl
    rw [hft, ContinuousLinearMap.iteratedFDeriv_comp_left _ hW.contDiffAt hn']
    rfl
  refine ContinuousMultilinearMap.opNorm_le_bound (Real.sqrt_nonneg _) (fun m => ?_)
  have hprod : 0 ≤ ∏ j, ‖m j‖ := Finset.prod_nonneg fun j _ => norm_nonneg (m j)
  have hsq : ‖iteratedFDeriv ℝ n (orthogonalBlocks f) a m‖ ^ 2 ≤
      (∑ t, bd t ^ 2) * (∏ j, ‖m j‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Finset.sum_mul]
    refine Finset.sum_le_sum fun t _ => ?_
    rw [hcomp]
    have h1 := (iteratedFDeriv ℝ n (f t) a).le_opNorm m
    have h2 : ‖iteratedFDeriv ℝ n (f t) a‖ * ∏ j, ‖m j‖ ≤ bd t * ∏ j, ‖m j‖ :=
      mul_le_mul_of_nonneg_right (hb t) hprod
    have h3 : 0 ≤ ‖iteratedFDeriv ℝ n (f t) a m‖ := norm_nonneg _
    calc ‖iteratedFDeriv ℝ n (f t) a m‖ ^ 2 ≤ (bd t * ∏ j, ‖m j‖) ^ 2 :=
          pow_le_pow_left₀ h3 (h1.trans h2) 2
      _ = bd t ^ 2 * (∏ j, ‖m j‖) ^ 2 := by ring
  have hs : 0 ≤ ∑ t, bd t ^ 2 := Finset.sum_nonneg fun t _ => sq_nonneg _
  have hr := Real.sq_sqrt hs
  have hp := mul_nonneg (Real.sqrt_nonneg (∑ t, bd t ^ 2)) hprod
  nlinarith [sq_nonneg (Real.sqrt (∑ t, bd t ^ 2) * ∏ j, ‖m j‖ -
    ‖iteratedFDeriv ℝ n (orthogonalBlocks f) a m‖), norm_nonneg (iteratedFDeriv ℝ n
      (orthogonalBlocks f) a m)]

/-- `‖iteratedFDeriv 2 f x‖ = ‖D²f(x)‖`. -/
theorem norm_iteratedFDeriv_two_eq_SGP3 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (x : E) :
    ‖iteratedFDeriv ℝ 2 f x‖ = ‖fderiv ℝ (fderiv ℝ f) x‖ := by
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]

/-- An affinely reparametrized embedded model block `a ↦ ι(W(σa + c))` (`|σ| ≤ 1`) keeps the first
and second derivative bound `B` of `W`. -/
theorem affine_block_derivative_bounds_SGP3 {W : ℝ → WithLp 2 (ℝ × ℝ)} (hW : ContDiff ℝ 2 W)
    {B : ℝ} (hB : 0 ≤ B) (h1 : ∀ y, ‖fderiv ℝ W y‖ ≤ B)
    (h2 : ∀ y, ‖fderiv ℝ (fderiv ℝ W) y‖ ≤ B) {σ c : ℝ} (hσ : |σ| ≤ 1) (a : ℝ) {n : ℕ}
    (hn1 : 1 ≤ n) (hn : n ≤ 2) :
    ‖iteratedFDeriv ℝ n (fun a => sgpBlockEmbed (W (σ * a + c))) a‖ ≤ B := by
  let W' : ℝ → WithLp 2 (ℝ × ℝ) := fun y => W (y + c)
  let Lσ : ℝ →L[ℝ] ℝ := σ • ContinuousLinearMap.id ℝ ℝ
  have hW' : ContDiff ℝ 2 W' := hW.comp (contDiff_id.add contDiff_const)
  have hd1 : ∀ y, fderiv ℝ W' y = fderiv ℝ W (y + c) := fun y => fderiv_comp_add_right c
  have hDW' : fderiv ℝ W' = fun y => fderiv ℝ W (y + c) := funext hd1
  have hd2 : ∀ y, fderiv ℝ (fderiv ℝ W') y = fderiv ℝ (fderiv ℝ W) (y + c) := by
    intro y
    rw [hDW']
    exact fderiv_comp_add_right (f := fderiv ℝ W) c
  have hL : ‖Lσ‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
    change ‖σ • y‖ ≤ 1 * ‖y‖
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hσ (norm_nonneg y)
  obtain ⟨hb1, hb2⟩ := linear_precomp_derivative_bounds Lσ hW' zero_le_one hB hB hL
    (fun y => (hd1 y).symm ▸ h1 (y + c)) (fun y => (hd2 y).symm ▸ h2 (y + c)) a
  have hfun : (fun a => W (σ * a + c)) = W' ∘ Lσ := by
    funext y
    change W (σ * y + c) = W (σ • y + c)
    rw [smul_eq_mul]
  have hh : ContDiff ℝ 2 (fun a => W (σ * a + c)) := by rw [hfun]; exact hW'.comp Lσ.contDiff
  have hiso : ‖iteratedFDeriv ℝ n (fun a => sgpBlockEmbed (W (σ * a + c))) a‖ =
      ‖iteratedFDeriv ℝ n (fun a => W (σ * a + c)) a‖ :=
    sgpBlockEmbed.norm_iteratedFDeriv_comp_left (f := fun a => W (σ * a + c)) hh.contDiffAt
      (by exact_mod_cast hn)
  rw [hiso, hfun]
  interval_cases n
  · rw [norm_iteratedFDeriv_one]
    simpa using hb1
  · rw [norm_iteratedFDeriv_two_eq_SGP3]
    simpa using hb2

/-- The own block `a ↦ (a e₀, 1)` has first derivative at most one and second derivative zero. -/
theorem own_block_derivative_bounds_SGP3 (a : ℝ) {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 2) :
    ‖iteratedFDeriv ℝ n (fun a : ℝ => (WithLp.toLp 2 (planeAxis a, (1 : ℝ)) :
      WithLp 2 (ℝ² × ℝ))) a‖ ≤ 1 := by
  obtain ⟨L₁, hL₁⟩ : ∃ L₁ : ℝ →L[ℝ] WithLp 2 (ℝ × ℝ), ∀ y, L₁ y = WithLp.toLp 2 (y, 0) :=
    ⟨((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm : (ℝ × ℝ) →L[ℝ] WithLp 2 (ℝ × ℝ)).comp
        (ContinuousLinearMap.inl ℝ ℝ ℝ), fun y => rfl⟩
  have hnorm : ‖L₁‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
    rw [hL₁, one_mul, WithLp.prod_norm_eq_of_L2]
    change Real.sqrt (‖y‖ ^ 2 + ‖(0 : ℝ)‖ ^ 2) ≤ ‖y‖
    rw [norm_zero, zero_pow two_ne_zero, add_zero, Real.sqrt_sq (norm_nonneg y)]
  have hfun1 : (fun a : ℝ => (WithLp.toLp 2 (a, (1 : ℝ)) : WithLp 2 (ℝ × ℝ))) =
      fun a => L₁ a + WithLp.toLp 2 (0, 1) := by
    funext y
    rw [hL₁, ← WithLp.toLp_add]
    simp
  have hfun : (fun a : ℝ => (WithLp.toLp 2 (planeAxis a, (1 : ℝ)) : WithLp 2 (ℝ² × ℝ))) =
      sgpBlockEmbed ∘ fun a => L₁ a + WithLp.toLp 2 ((0 : ℝ), (1 : ℝ)) := by
    rw [← hfun1]
    rfl
  have hc : ContDiff ℝ 2 fun a => L₁ a + WithLp.toLp 2 ((0 : ℝ), (1 : ℝ)) :=
    L₁.contDiff.add contDiff_const
  have hd : ∀ y, fderiv ℝ (fun a => L₁ a + WithLp.toLp 2 ((0 : ℝ), (1 : ℝ))) y = L₁ :=
    fun y => (L₁.hasFDerivAt.add_const (WithLp.toLp 2 ((0 : ℝ), (1 : ℝ)))).fderiv
  have hD : fderiv ℝ (fun a => L₁ a + WithLp.toLp 2 ((0 : ℝ), (1 : ℝ))) = fun _ => L₁ :=
    funext hd
  have hDD : fderiv ℝ (fderiv ℝ (fun a => L₁ a + WithLp.toLp 2 ((0 : ℝ), (1 : ℝ)))) a = 0 := by
    rw [hD]
    exact fderiv_const_apply L₁
  rw [hfun, sgpBlockEmbed.norm_iteratedFDeriv_comp_left hc.contDiffAt (by exact_mod_cast hn)]
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [norm_iteratedFDeriv_one, hd]
    exact hnorm
  · obtain rfl : n = 2 := by omega
    rw [norm_iteratedFDeriv_two_eq_SGP3, hDD, norm_zero]
    exact zero_le_one

theorem zero_block_iteratedFDeriv_SGP3 (a : ℝ) {n : ℕ} (hn1 : 1 ≤ n) :
    ‖iteratedFDeriv ℝ n (fun _ : ℝ => (0 : WithLp 2 (ℝ² × ℝ))) a‖ = 0 := by
  rw [iteratedFDeriv_const_of_ne (by omega)]
  simp

end Bounds

section Count

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

variable (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

open Classical in
/-- The slim tags that are the reference or listed: at most `|J_i| + 1`. -/
theorem card_slim_listed_le_SGP3 (i : L.slim.finite_centres.toFinset) :
    ((Finset.univ.filter fun j : L.slim.finite_centres.toFinset =>
      j = i ∨ j.1 ∈ sgpSlimList L.slim i.1).card : ℝ) ≤
      ((sgpSlimList L.slim i.1).ncard : ℝ) + 1 := by
  set S := Finset.univ.filter fun j : L.slim.finite_centres.toFinset =>
    j = i ∨ j.1 ∈ sgpSlimList L.slim i.1
  have hfin : (sgpSlimList L.slim i.1 ∪ {i.1}).Finite :=
    (L.slim.finite_centres.subset fun j hj => hj.1).union (Set.finite_singleton _)
  have hsub : ((S.map (Function.Embedding.subtype _) : Finset X) : Set X) ⊆
      sgpSlimList L.slim i.1 ∪ {i.1} := by
    intro x hx
    rw [Finset.coe_map, Set.mem_image] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    have hj' := (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2
    rcases hj' with h | h
    · right
      rw [h]
      rfl
    · left
      exact h
  have h1 : S.card = (S.map (Function.Embedding.subtype _)).card := (Finset.card_map _).symm
  have h2 : ((S.map (Function.Embedding.subtype _)).card : ℝ) ≤
      ((sgpSlimList L.slim i.1 ∪ {i.1}).ncard : ℝ) := by
    rw [← Set.ncard_coe_finset]
    exact_mod_cast Set.ncard_le_ncard hsub hfin
  have h3 : ((sgpSlimList L.slim i.1 ∪ {i.1}).ncard : ℝ) ≤
      ((sgpSlimList L.slim i.1).ncard : ℝ) + 1 := by
    have := Set.ncard_union_le (sgpSlimList L.slim i.1) {i.1}
    rw [Set.ncard_singleton] at this
    exact_mod_cast this
  rw [h1]
  exact h2.trans h3

open Classical in
/-- **The counting step of SGP04.** A function on the tags of `𝓔⁰` that is at most `c` on the
reference and listed slim tags and vanishes on the other slim tags, the circle, edge and special
tags, and whose zero tags sum to at most `c`, sums to at most `(N + 2)c` (`|J_i| ≤ N`). -/
theorem sum_cgpTag_le_SGP3 (i : L.slim.finite_centres.toFinset) (f : CGPTag L Z → ℝ)
    {c Nc : ℝ} (hc : 0 ≤ c) (hcirc : ∀ j, f (.inl j) ≤ 0)
    (hslim : ∀ j : L.slim.finite_centres.toFinset,
      f (.inr (.inl j)) ≤ if j = i ∨ j.1 ∈ sgpSlimList L.slim i.1 then c else 0)
    (hedge : ∀ j, f (.inr (.inr (.inl j))) ≤ 0)
    (hzero : ∑ k : Z.finite_centres.toFinset, f (.inr (.inr (.inr (.inl k)))) ≤ c)
    (hbool : ∀ bb, f (.inr (.inr (.inr (.inr bb)))) ≤ 0)
    (hN : ((sgpSlimList L.slim i.1).ncard : ℝ) ≤ Nc) :
    ∑ t, f t ≤ (Nc + 2) * c := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h1 : ∑ j, f (.inl j) ≤ 0 := Finset.sum_nonpos fun j _ => hcirc j
  have h3 : ∑ j, f (.inr (.inr (.inl j))) ≤ 0 := Finset.sum_nonpos fun j _ => hedge j
  have h5 : ∑ bb, f (.inr (.inr (.inr (.inr bb)))) ≤ 0 := Finset.sum_nonpos fun bb _ => hbool bb
  have h2 : ∑ j : L.slim.finite_centres.toFinset, f (.inr (.inl j)) ≤ (Nc + 1) * c := by
    calc ∑ j : L.slim.finite_centres.toFinset, f (.inr (.inl j))
        ≤ ∑ j : L.slim.finite_centres.toFinset,
            (if j = i ∨ j.1 ∈ sgpSlimList L.slim i.1 then c else 0) :=
          Finset.sum_le_sum fun j _ => hslim j
      _ = ((Finset.univ.filter fun j : L.slim.finite_centres.toFinset =>
            j = i ∨ j.1 ∈ sgpSlimList L.slim i.1).card : ℝ) * c := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Nc + 1) * c := by
          refine mul_le_mul_of_nonneg_right ?_ hc
          have := card_slim_listed_le_SGP3 L i
          linarith
  nlinarith

omit [CompactSpace X] in
open Classical in
/-- At most one zero tag meets `D_i`: a function bounded by `c` on meeting zero tags and vanishing
on the others sums to at most `c` over the zero tags. -/
theorem sum_zeroTag_le_SGP3 (i : X) (f : Z.finite_centres.toFinset → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hf : ∀ k : Z.finite_centres.toFinset,
      f k ≤ if sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i k.1 ((Set.Finite.mem_toFinset _).mp k.2) then c
        else 0)
    (huniq : ∀ k₁ k₂ : Z.finite_centres.toFinset,
      sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i k₁.1 ((Set.Finite.mem_toFinset _).mp k₁.2) →
      sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i k₂.1 ((Set.Finite.mem_toFinset _).mp k₂.2) →
      k₁ = k₂) :
    ∑ k, f k ≤ c := by
  by_cases hex : ∃ k₀ : Z.finite_centres.toFinset,
      sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i k₀.1 ((Set.Finite.mem_toFinset _).mp k₀.2)
  · obtain ⟨k₀, hk₀⟩ := hex
    calc ∑ k, f k ≤ ∑ k : Z.finite_centres.toFinset, (if sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i k.1
          ((Set.Finite.mem_toFinset _).mp k.2) then c else 0) := Finset.sum_le_sum fun k _ => hf k
      _ = c := by
          rw [Finset.sum_eq_single k₀
            (fun k _ hk => ite_eq_right (fun hm => hk (huniq k k₀ hm hk₀)))
            (fun h => absurd (Finset.mem_univ k₀) h), ite_eq_left hk₀]
  · calc ∑ k, f k ≤ ∑ _k : Z.finite_centres.toFinset, (0 : ℝ) :=
          Finset.sum_le_sum fun k _ => (hf k).trans_eq (ite_eq_right fun hm => hex ⟨k, hm⟩)
      _ ≤ c := by simp [hc]

end Count

section ModelBounds

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

variable (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

/-- `C_* = 1000(N_* + 2)(P_* + 1)`: `N_*` LC87's slim multiplicity constant, `P_*` the larger of
the slim and zero profiles' early `C²` constants (an early, numerical constant). -/
def sgpGraphBound : ℝ := 1000 * (egp02SlimCount + 2) * (max sgpProfileBound zeroProfileBound + 1)

/-- The per-block bound `50(P_* + 1)`. -/
def sgpBlockBound : ℝ := 50 * (max sgpProfileBound zeroProfileBound + 1)

theorem one_le_sgpBlockBound : 1 ≤ sgpBlockBound := by
  have := sgpProfileBound_spec.1
  have := le_max_left sgpProfileBound zeroProfileBound
  unfold sgpBlockBound
  linarith

/-- The slim block of `Φ_i` has `n`-th derivative (`n = 1, 2`) at most `50(P_* + 1)` when it is the
reference or listed, and zero otherwise. -/
theorem sgpSlimModelBlock_iteratedFDeriv_le (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (i : L.slim.finite_centres.toFinset) (sgn c : X → ℝ)
    (hsgn : ∀ j, |sgn j| ≤ 1) (j : L.slim.finite_centres.toFinset) (a : ℝ) {n : ℕ}
    (hn1 : 1 ≤ n) (hn : n ≤ 2) :
    ‖iteratedFDeriv ℝ n (sgpSlimModelBlock L i sgn c j) a‖ ≤
      (open Classical in if j = i ∨ j.1 ∈ sgpSlimList L.slim i.1 then sgpBlockBound else 0) := by
  classical
  have hB := one_le_sgpBlockBound
  by_cases hji : j = i
  · have hf : sgpSlimModelBlock L i sgn c j = fun a => WithLp.toLp 2 (planeAxis a, (1 : ℝ)) :=
      funext fun a => by simp [sgpSlimModelBlock, hji]
    rw [hf, ite_eq_left (Or.inl hji)]
    exact (own_block_derivative_bounds_SGP3 a hn1 hn).trans hB
  by_cases hjl : j.1 ∈ sgpSlimList L.slim i.1
  · have hf : sgpSlimModelBlock L i sgn c j = fun a => sgpBlockEmbed
        (sgpModelBlock (10 ^ 5 * Δ) (ρ j.1 / ρ i.1) (sgn j.1 * a + c j.1)) :=
      funext fun a => by simp [sgpSlimModelBlock, hji, hjl]
    rw [hf, ite_eq_left (Or.inr hjl)]
    have hs := (sgpSlimList_bounds L (by linarith) hΛ hLΛ hjl).2.1
    have hℓ : (1 : ℝ) ≤ 10 ^ 5 * Δ := by nlinarith
    have hP := le_max_left sgpProfileBound zeroProfileBound
    refine (affine_block_derivative_bounds_SGP3 ((contDiff_sgpModelBlock _ _).of_le (by simp))
      (by linarith [sgpProfileBound_spec.1])
      (fun y => (sgpModelBlock_derivative_bounds hℓ hs.le y).1)
      (fun y => (sgpModelBlock_derivative_bounds hℓ hs.le y).2) (hsgn j.1) a hn1 hn).trans ?_
    unfold sgpBlockBound
    linarith
  · have hf : sgpSlimModelBlock L i sgn c j = fun _ => 0 :=
      funext fun a => by simp [sgpSlimModelBlock, hji, hjl]
    rw [hf, zero_block_iteratedFDeriv_SGP3 a hn1]
    split_ifs <;> linarith

/-- The zero block of the full `Φ_i` has `n`-th derivative at most `50(P_* + 1)` when its support
meets `D_i` (`s₀ ≥ 1`), and zero otherwise. -/
theorem sgpZeroModelBlock_iteratedFDeriv_le (i : L.slim.finite_centres.toFinset)
    (zsgn zc : X → ℝ) (hzsgn : ∀ k, |zsgn k| ≤ 1) (k : Z.finite_centres.toFinset)
    (hs0 : sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i.1 k.1 ((Set.Finite.mem_toFinset _).mp k.2) →
      1 ≤ (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i.1)
    (a : ℝ) {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 2) :
    ‖iteratedFDeriv ℝ n (sgpZeroModelBlock L Z i zsgn zc k) a‖ ≤
      (open Classical in if sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i.1 k.1
        ((Set.Finite.mem_toFinset _).mp k.2) then sgpBlockBound else 0) := by
  classical
  by_cases hm : sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i.1 k.1 ((Set.Finite.mem_toFinset _).mp k.2)
  · have hf : sgpZeroModelBlock L Z i zsgn zc k = fun a => sgpBlockEmbed (zeroModelBlock
        ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i.1)
        (zsgn k.1 * a + zc k.1)) :=
      funext fun a => by simp [sgpZeroModelBlock, hm]
    rw [hf, ite_eq_left hm]
    have hs := hs0 hm
    have hP := le_max_right sgpProfileBound zeroProfileBound
    refine (affine_block_derivative_bounds_SGP3 ((contDiff_zeroModelBlock _).of_le (by simp))
      (by linarith [zeroProfileBound_spec.1])
      (fun y => (zeroModelBlock_derivative_bounds hs y).1)
      (fun y => (zeroModelBlock_derivative_bounds hs y).2) (hzsgn k.1) a hn1 hn).trans ?_
    unfold sgpBlockBound
    linarith
  · have hf : sgpZeroModelBlock L Z i zsgn zc k = fun _ => 0 :=
      funext fun a => by simp [sgpZeroModelBlock, hm]
    rw [hf, zero_block_iteratedFDeriv_SGP3 a hn1, ite_eq_right hm]

/-- The assembly: `√((N + 2) B²) ≤ C_*` for `B = 50(P_* + 1)`, `N ≤ N_*`. -/
theorem sqrt_count_le_sgpGraphBound {Nc : ℝ} (hN0 : 0 ≤ Nc) (hN : Nc ≤ egp02SlimCount) :
    Real.sqrt ((Nc + 2) * sgpBlockBound ^ 2) ≤ sgpGraphBound := by
  have hB := one_le_sgpBlockBound
  rw [Real.sqrt_mul (by linarith), Real.sqrt_sq (by linarith)]
  have h1 : Real.sqrt (Nc + 2) ≤ Nc + 2 := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have h2 : Real.sqrt (Nc + 2) * sgpBlockBound ≤ (egp02SlimCount + 2) * sgpBlockBound :=
    mul_le_mul_of_nonneg_right (h1.trans (by linarith)) (by linarith)
  have hM : 0 ≤ max sgpProfileBound zeroProfileBound + 1 := by
    linarith [le_max_left sgpProfileBound zeroProfileBound, sgpProfileBound_spec.1]
  have hQ : 0 ≤ (egp02SlimCount + 2) * (max sgpProfileBound zeroProfileBound + 1) :=
    mul_nonneg (by linarith) hM
  have e1 : (egp02SlimCount + 2) * sgpBlockBound =
      50 * ((egp02SlimCount + 2) * (max sgpProfileBound zeroProfileBound + 1)) := by
    unfold sgpBlockBound; ring
  have e2 : sgpGraphBound =
      1000 * ((egp02SlimCount + 2) * (max sgpProfileBound zeroProfileBound + 1)) := by
    unfold sgpGraphBound; ring
  rw [e2]
  linarith

/-- The iterated derivatives of the full model graph (kernel of the two `sgp04_*model_bounds`). -/
theorem sgpFullGraph_iteratedFDeriv_le (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (i : L.slim.finite_centres.toFinset)
    (sgn c zsgn zc : X → ℝ) (hsgn : ∀ j, |sgn j| ≤ 1) (hzsgn : ∀ k, |zsgn k| ≤ 1)
    (hs0 : ∀ k (hk : k ∈ Z.centres), sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i.1 k hk →
      1 ≤ (Z.zero k hk).radius / ρ i.1)
    (huniq : ∀ k₁ (hk₁ : k₁ ∈ Z.centres) k₂ (hk₂ : k₂ ∈ Z.centres),
      sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i.1 k₁ hk₁ → sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i.1 k₂ hk₂ →
      k₁ = k₂) (a : ℝ) {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 2) :
    ‖iteratedFDeriv ℝ n (sgpFullGraph L Z i sgn c zsgn zc) a‖ ≤ sgpGraphBound := by
  classical
  have hΔ0 : 0 < Δ := by linarith
  have hB := one_le_sgpBlockBound
  let bd : CGPTag L Z → ℝ
    | .inr (.inl j) => if j = i ∨ j.1 ∈ sgpSlimList L.slim i.1 then sgpBlockBound else 0
    | .inr (.inr (.inr (.inl k))) => if sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i.1 k.1
        ((Set.Finite.mem_toFinset _).mp k.2) then sgpBlockBound else 0
    | _ => 0
  have hbd : ∀ t, ‖iteratedFDeriv ℝ n (sgpFullTag L Z i sgn c zsgn zc t) a‖ ≤ bd t := by
    intro t
    rcases t with j | j | j | k | bb
    · exact (zero_block_iteratedFDeriv_SGP3 a hn1).le
    · exact sgpSlimModelBlock_iteratedFDeriv_le L hΔ hΛ hLΛ i sgn c hsgn j a hn1 hn
    · exact (zero_block_iteratedFDeriv_SGP3 a hn1).le
    · exact sgpZeroModelBlock_iteratedFDeriv_le L Z i zsgn zc hzsgn k (hs0 _ _) a hn1 hn
    · exact (zero_block_iteratedFDeriv_SGP3 a hn1).le
  have hmain := norm_iteratedFDeriv_orthogonalBlocks_le_SGP3 (sgpFullTag L Z i sgn c zsgn zc)
    (fun t => (contDiff_sgpFullTag L Z i sgn c zsgn zc t).of_le (by simp)) hn a bd hbd
  have hN := sgpSlimList_ncard_le_ZERO L hΔ0 hΛ hLΛ i.1
  have hN0 : (0 : ℝ) ≤ ((sgpSlimList L.slim i.1).ncard : ℝ) := Nat.cast_nonneg _
  have hsum : ∑ t, bd t ^ 2 ≤ (((sgpSlimList L.slim i.1).ncard : ℝ) + 2) * sgpBlockBound ^ 2 := by
    refine sum_cgpTag_le_SGP3 L Z i (fun t => bd t ^ 2) (by positivity) (fun j => by simp [bd])
      (fun j => ?_) (fun j => by simp [bd]) ?_ (fun bb => by simp [bd]) le_rfl
    · change (if j = i ∨ j.1 ∈ sgpSlimList L.slim i.1 then sgpBlockBound else 0) ^ 2 ≤ _
      split_ifs <;> simp
    · refine sum_zeroTag_le_SGP3 Z i.1 _ (by positivity) (fun k => ?_)
        (fun k₁ k₂ h₁ h₂ => Subtype.ext (huniq _ _ _ _ h₁ h₂))
      change (if sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i.1 k.1 ((Set.Finite.mem_toFinset _).mp k.2)
        then sgpBlockBound else 0) ^ 2 ≤ _
      split_ifs <;> simp
  exact hmain.trans ((Real.sqrt_le_sqrt hsum).trans (sqrt_count_le_sgpGraphBound hN0 hN))

/-- **SGP04, the model and its early modulus (full graph).** `‖DΦ_i‖, ‖D²Φ_i‖ ≤ C_*` and
`‖iteratedFDeriv 2 Φ_i‖ ≤ C_*` everywhere, `C_* = 1000(N_* + 2)(P_* + 1)` (early), for signs of
size at most one, zero scale ratios `s₀ ≥ 1` at the meeting zero supports and at most one such
support (SGP01). -/
theorem sgp04_full_model_bounds (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (i : L.slim.finite_centres.toFinset)
    (sgn c zsgn zc : X → ℝ) (hsgn : ∀ j, |sgn j| ≤ 1) (hzsgn : ∀ k, |zsgn k| ≤ 1)
    (hs0 : ∀ k (hk : k ∈ Z.centres), sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i.1 k hk →
      1 ≤ (Z.zero k hk).radius / ρ i.1)
    (huniq : ∀ k₁ (hk₁ : k₁ ∈ Z.centres) k₂ (hk₂ : k₂ ∈ Z.centres),
      sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i.1 k₁ hk₁ → sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i.1 k₂ hk₂ →
      k₁ = k₂) (a : ℝ) :
    ‖fderiv ℝ (sgpFullGraph L Z i sgn c zsgn zc) a‖ ≤ sgpGraphBound ∧
      ‖fderiv ℝ (fderiv ℝ (sgpFullGraph L Z i sgn c zsgn zc)) a‖ ≤ sgpGraphBound ∧
      ‖iteratedFDeriv ℝ 2 (sgpFullGraph L Z i sgn c zsgn zc) a‖ ≤ sgpGraphBound := by
  have h1 := sgpFullGraph_iteratedFDeriv_le L Z hΔ hΛ hLΛ i sgn c zsgn zc hsgn hzsgn hs0 huniq a
    le_rfl (by norm_num)
  have h2 := sgpFullGraph_iteratedFDeriv_le L Z hΔ hΛ hLΛ i sgn c zsgn zc hsgn hzsgn hs0 huniq a
    (by norm_num) le_rfl
  rw [norm_iteratedFDeriv_one] at h1
  refine ⟨h1, ?_, h2⟩
  rw [← norm_iteratedFDeriv_two_eq_SGP3]
  exact h2

/-- **SGP04, the model and its early modulus** (frozen slim graph `sgpModelGraph`):
`‖DΦ_i‖, ‖D²Φ_i‖, ‖iteratedFDeriv 2 Φ_i‖ ≤ C_*` everywhere, for signs of size at most one. -/
theorem sgp04_model_bounds (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (i : L.slim.finite_centres.toFinset) (sgn c : X → ℝ) (hsgn : ∀ j, |sgn j| ≤ 1) (a : ℝ) :
    ‖fderiv ℝ (sgpModelGraph L Z i sgn c) a‖ ≤ sgpGraphBound ∧
      ‖fderiv ℝ (fderiv ℝ (sgpModelGraph L Z i sgn c)) a‖ ≤ sgpGraphBound ∧
      ‖iteratedFDeriv ℝ 2 (sgpModelGraph L Z i sgn c) a‖ ≤ sgpGraphBound := by
  classical
  have hΔ0 : 0 < Δ := by linarith
  have hB := one_le_sgpBlockBound
  have hN := sgpSlimList_ncard_le_ZERO L hΔ0 hΛ hLΛ i.1
  have hN0 : (0 : ℝ) ≤ ((sgpSlimList L.slim i.1).ncard : ℝ) := Nat.cast_nonneg _
  let bd : CGPTag L Z → ℝ
    | .inr (.inl j) => if j = i ∨ j.1 ∈ sgpSlimList L.slim i.1 then sgpBlockBound else 0
    | _ => 0
  have hgen : ∀ {n : ℕ}, 1 ≤ n → n ≤ 2 →
      ‖iteratedFDeriv ℝ n (sgpModelGraph L Z i sgn c) a‖ ≤ sgpGraphBound := by
    intro n hn1 hn
    have hbd : ∀ t, ‖iteratedFDeriv ℝ n (sgpModelTag L Z i sgn c t) a‖ ≤ bd t := by
      intro t
      rcases t with j | j | j | k | bb
      · exact (zero_block_iteratedFDeriv_SGP3 a hn1).le
      · exact sgpSlimModelBlock_iteratedFDeriv_le L hΔ hΛ hLΛ i sgn c hsgn j a hn1 hn
      · exact (zero_block_iteratedFDeriv_SGP3 a hn1).le
      · exact (zero_block_iteratedFDeriv_SGP3 a hn1).le
      · exact (zero_block_iteratedFDeriv_SGP3 a hn1).le
    have hmain := norm_iteratedFDeriv_orthogonalBlocks_le_SGP3 (sgpModelTag L Z i sgn c)
      (fun t => (contDiff_sgpModelTag L Z i sgn c t).of_le (by simp)) hn a bd hbd
    have hsum : ∑ t, bd t ^ 2 ≤
        (((sgpSlimList L.slim i.1).ncard : ℝ) + 2) * sgpBlockBound ^ 2 := by
      refine sum_cgpTag_le_SGP3 L Z i (fun t => bd t ^ 2) (by positivity) (fun j => by simp [bd])
        (fun j => ?_) (fun j => by simp [bd]) ?_ (fun bb => by simp [bd]) le_rfl
      · change (if j = i ∨ j.1 ∈ sgpSlimList L.slim i.1 then sgpBlockBound else 0) ^ 2 ≤ _
        split_ifs <;> simp
      · simp only [bd]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
          Finset.sum_const_zero]
        positivity
    exact hmain.trans ((Real.sqrt_le_sqrt hsum).trans (sqrt_count_le_sgpGraphBound hN0 hN))
  have h1 := hgen le_rfl (by norm_num : 1 ≤ 2)
  have h2 := hgen (by norm_num : 1 ≤ 2) le_rfl
  rw [norm_iteratedFDeriv_one] at h1
  refine ⟨h1, ?_, h2⟩
  rw [← norm_iteratedFDeriv_two_eq_SGP3]
  exact h2

end ModelBounds

end DifferentialGeometry.Geometry.Collapse
