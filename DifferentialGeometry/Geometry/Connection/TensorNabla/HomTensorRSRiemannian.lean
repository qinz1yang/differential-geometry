import DifferentialGeometry.Geometry.Connection.TensorNabla.SecondOrderHomBundle
import DifferentialGeometry.Geometry.Connection.SingleSlotOperatorFiberNormBound
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.TensorRSContRiemannianBundle
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Topology.VectorBundle.Hom
import Mathlib.Topology.Order.Compact

/-!
# The `g`-fibre operator-norm Riemannian calculus on the second-order Hom-bundle `Hom(T^{r,a}, T^{r,c})`

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file equips the **second-order Hom-bundle**
`Hom(TensorRSSpace r a, TensorRSSpace r c) = fun x => HomTensorRSSpace r a c I x`
(built in `SecondOrderHomBundle.lean` as the `Bundle.ContinuousLinearMap` bundle of the smooth
`(r, a)`- and `(r, c)`-tensor bundles) with its intrinsic **`g`-fibre operator-norm** calculus,
making the operator bundle a first-class object of the Riemannian fibre-norm theory.

Each domain / codomain fibre `TensorRSSpace r a I x` / `TensorRSSpace r c I x` carries the `g`-fibre
inner product installed by `Tensor0SBundle.tensorRS_riemannianBundle`, under which it is a
finite-dimensional real inner-product space whose squared norm is the intrinsic
`riemannianFiberNormSq` (the proved bridge `riemannianFiberNormSq_eq_bundle_norm_sq'`).  A fibrewise
operator `A : TensorRSSpace r a I x →L TensorRSSpace r c I x` then has a well-defined intrinsic
`g`-fibre operator norm `‖A‖` (measured in those Riemannian fibre norms), and its action obeys the
sharp fibrewise contraction bound
```
rfns(A v) ≤ ‖A‖² · rfns(v)          for every fibre tensor v,
```
the intrinsic operator-norm analogue (no Hilbert–Schmidt dimension factor) of the codomain-only
post-composition bound.  This is the structural fact that makes the rank-`r` curvature operator-field
bounds clean: the curvature reading operator, being a smooth Hom-bundle section, has a continuous
`g`-fibre operator norm, and that norm is the proportionality coefficient of the fibre-energy bound.

## Main declarations

* `homTensorRS_riemannianFiberNormSq_clm_apply_le` — the **fibrewise** intrinsic operator bound
  `rfns(A v) ≤ ‖A‖² · rfns(v)` for any fibrewise operator `A` and the `g`-fibre operator norm `‖A‖`;
* `continuous_homTensorRS_opNorm` — the single genuinely-irreducible analytic core: for a smooth full
  Hom-bundle section `Ψ`, the `g`-fibre operator norm `x ↦ ‖Ψ x‖` is continuous (the exact full-Hom
  analogue of the curvature line's frame-energy continuity
  `exists_continuous_riemannOp_tensorCovS_frameEnergy_bound`), proved by specialising the generic
  `continuous_homBundle_opNorm_generic` to the tensor bundles via `tensorRS_isContinuousRiemannianBundle`;
* `exists_uniform_homTensorRS_opNorm_sq` — for a smooth full Hom-bundle section `Ψ`, the squared
  `g`-fibre operator norm `x ↦ ‖Ψ x‖²` admits a single uniform-over-`M` bound `C`, proved on top of
  `continuous_homTensorRS_opNorm` by "continuous on compact ⟹ bounded" (the exact full-Hom analogue of
  the curvature line's uniform constant `exists_uniform_riemannOp_tensorCovS_dualFrameEnergy_const`);
* `exists_continuous_homTensorRS_opNorm_sq` — its continuous-envelope version: a continuous nonnegative
  `N : M → ℝ` dominating `x ↦ ‖Ψ x‖²`, the constant envelope `fun _ => C` of the uniform bound (the
  exact full-Hom analogue of `exists_continuous_riemannOp_tensorCovS_frameEnergy_bound`);
* `exists_continuous_riemannianFiberNormSq_homTensorRS_section_clm_le` — **the payoff** (the reason
  this file exists): for a smooth full Hom-bundle section `Ψ` there is a continuous nonnegative
  `Cop : M → ℝ` with the per-point fibrewise `g`-contraction bound `rfns(Ψ x v) ≤ Cop x · rfns(v)`,
  the general envelope behind the rank-`r` curvature operator-field bounds;
* `exists_uniform_riemannianFiberNormSq_homTensorRS_section_clm_le` — its uniform version on a closed
  manifold (continuous on compact ⟹ bounded).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set IsManifold Tensor0SBundle ContinuousLinearMap Filter
open scoped Manifold Topology ContDiff BigOperators InnerProductSpace

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor.TensorRSRiemannianBundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

/-! ## Generic operator-norm continuity for a continuous Hom-bundle section

The intrinsic analytic core, proved for an *arbitrary* pair of continuous Riemannian vector bundles
`E₁`, `E₂` (model fibres `F₁`, `F₂`).  For a continuous section `Ψ` of the Hom bundle
`x ↦ E₁ x →L E₂ x`, the fibrewise operator norm `x ↦ ‖Ψ x‖` (measured in the per-fibre inner-product
norms) is continuous.  The proof reads `Ψ` through the local trivialisations at the base point: the
conjugated operator `Ψ̃ y = S_c(y) ∘ Ψ y ∘ S_a'(y)` into the *fixed* fibre `E₁ x₀ →L E₂ x₀`
(`S_c`, `S_a'` the trivialisation transports) is continuous and agrees with `Ψ x₀` at `x₀`, while the
trivialisation transports distort the norm by a factor arbitrarily close to `1`
(`eventually_norm_symmL_trivializationAt_self_comp_lt` and its companion), giving the two-sided
multiplicative pinch `‖Ψ̃ y‖ / r² ≤ ‖Ψ y‖ ≤ r² ‖Ψ̃ y‖` for every `r > 1` near `x₀`; the squeeze as
`r → 1` is `tendsto_order` applied to `x ↦ ‖Ψ̃ x‖ → ‖Ψ x₀‖`.  This is stated generically so the
`TensorRSModel`/Hom-fibre normed-instance diamond never enters the concrete application below. -/

section GenericHomOpNorm

/-- For `c < L` there is `r > 1` with `c · r² < L`: a one-sided neighbourhood of `1` witness used to
close the multiplicative squeeze as `r → 1⁺`. -/
private lemma exists_one_lt_mul_sq_lt {c L : ℝ} (h : c < L) :
    ∃ r : ℝ, 1 < r ∧ c * r ^ 2 < L := by
  have htend : Tendsto (fun r : ℝ => c * r ^ 2) (𝓝 1) (𝓝 c) := by
    have h1 : Tendsto (fun r : ℝ => c * r ^ 2) (𝓝 1) (𝓝 (c * (1 : ℝ) ^ 2)) :=
      tendsto_const_nhds.mul ((continuous_pow 2).tendsto 1)
    simpa using h1
  have hev : ∀ᶠ r in 𝓝 (1 : ℝ), c * r ^ 2 < L := htend.eventually (Iio_mem_nhds h)
  have hev2 : ∀ᶠ r in 𝓝[>] (1 : ℝ), c * r ^ 2 < L := hev.filter_mono nhdsWithin_le_nhds
  rcases (hev2.and self_mem_nhdsWithin).exists with ⟨r, hr2, hr1⟩
  exact ⟨r, hr1, hr2⟩

/-- **Operator-norm continuity of a continuous Hom-bundle section, generic form.**  For continuous
Riemannian vector bundles `E₁` (model `F₁`), `E₂` (model `F₂`) over a topological base `B` and a
continuous section `Ψ : Π x, E₁ x →L E₂ x` of the Hom bundle, the fibrewise operator norm
`x ↦ ‖Ψ x‖` (in the per-fibre inner-product norms) is continuous. -/
private lemma continuous_homBundle_opNorm_generic
    {B : Type*} [TopologicalSpace B]
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    {E₁ : B → Type*} [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, NormedAddCommGroup (E₁ x)]
      [∀ x, InnerProductSpace ℝ (E₁ x)]
      [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁] [IsContinuousRiemannianBundle F₁ E₁]
    {E₂ : B → Type*} [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, NormedAddCommGroup (E₂ x)]
      [∀ x, InnerProductSpace ℝ (E₂ x)]
      [FiberBundle F₂ E₂] [VectorBundle ℝ F₂ E₂] [IsContinuousRiemannianBundle F₂ E₂]
    (Ψ : Π x : B, E₁ x →L[ℝ] E₂ x)
    (hΨ : Continuous (fun x : B => TotalSpace.mk' (F₁ →L[ℝ] F₂)
      (E := fun z : B => E₁ z →L[ℝ] E₂ z) x (Ψ x))) :
    Continuous (fun x : B => ‖Ψ x‖) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have hx₀a : x₀ ∈ (trivializationAt F₁ E₁ x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  have hx₀c : x₀ ∈ (trivializationAt F₂ E₂ x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  have hΦcont : ContinuousAt (fun y : B => ContinuousLinearMap.inCoordinates
      F₁ E₁ F₂ E₂ x₀ y x₀ y (Ψ y)) x₀ := by
    have hcont := hΨ.continuousAt (x := x₀)
    rw [continuousAt_hom_bundle] at hcont
    exact hcont.2
  set Ψtil : B → (E₁ x₀ →L[ℝ] E₂ x₀) := fun y =>
    (((trivializationAt F₂ E₂ x₀).symmL ℝ x₀).comp
        ((trivializationAt F₂ E₂ x₀).continuousLinearMapAt ℝ y)).comp
      ((Ψ y).comp (((trivializationAt F₁ E₁ x₀).symmL ℝ y).comp
        ((trivializationAt F₁ E₁ x₀).continuousLinearMapAt ℝ x₀)))
    with hΨtil_def
  have hΨtilcont : ContinuousAt Ψtil x₀ := by
    rw [hΨtil_def]
    refine (ContinuousAt.clm_comp (g := fun _ : B => ((trivializationAt F₂ E₂ x₀).symmL ℝ x₀))
      (f := fun y : B => (((ContinuousLinearMap.inCoordinates F₁ E₁ F₂ E₂ x₀ y x₀ y (Ψ y))).comp
        ((trivializationAt F₁ E₁ x₀).continuousLinearMapAt ℝ x₀))) continuousAt_const
      (ContinuousAt.clm_comp
        (g := fun y : B => ContinuousLinearMap.inCoordinates F₁ E₁ F₂ E₂ x₀ y x₀ y (Ψ y))
        (f := fun _ : B => (trivializationAt F₁ E₁ x₀).continuousLinearMapAt ℝ x₀)
        hΦcont continuousAt_const)).congr ?_
    filter_upwards with y
    rw [ContinuousLinearMap.inCoordinates]
    simp only [ContinuousLinearMap.comp_assoc]
  have hnormtil : ContinuousAt (fun y => ‖Ψtil y‖) x₀ := hΨtilcont.norm
  have hΨtil_x0 : Ψtil x₀ = Ψ x₀ := by
    rw [hΨtil_def]
    ext v
    simp only [ContinuousLinearMap.comp_apply]
    rw [(trivializationAt F₁ E₁ x₀).symmL_continuousLinearMapAt hx₀a,
      (trivializationAt F₂ E₂ x₀).symmL_continuousLinearMapAt hx₀c]
  have hnormtil_lim : Tendsto (fun y => ‖Ψtil y‖) (𝓝 x₀) (𝓝 ‖Ψ x₀‖) := by
    have h0 : Tendsto (fun y => ‖Ψtil y‖) (𝓝 x₀) (𝓝 ‖Ψtil x₀‖) := hnormtil
    rwa [hΨtil_x0] at h0
  have hbasea : ∀ᶠ y in 𝓝 x₀, y ∈ (trivializationAt F₁ E₁ x₀).baseSet :=
    (trivializationAt F₁ E₁ x₀).open_baseSet.mem_nhds hx₀a
  have hbasec : ∀ᶠ y in 𝓝 x₀, y ∈ (trivializationAt F₂ E₂ x₀).baseSet :=
    (trivializationAt F₂ E₂ x₀).open_baseSet.mem_nhds hx₀c
  have hfwd : ∀ {r : ℝ}, 1 < r → ∀ᶠ y in 𝓝 x₀, ‖Ψtil y‖ ≤ r ^ 2 * ‖Ψ y‖ := by
    intro r hr
    have hSc := eventually_norm_symmL_trivializationAt_self_comp_lt F₂ E₂ x₀ hr
    have hSa' := eventually_norm_symmL_trivializationAt_comp_self_lt F₁ E₁ x₀ hr
    filter_upwards [hSc, hSa'] with y hyc hya
    rw [hΨtil_def]
    calc ‖(((trivializationAt F₂ E₂ x₀).symmL ℝ x₀).comp
              ((trivializationAt F₂ E₂ x₀).continuousLinearMapAt ℝ y)).comp
            ((Ψ y).comp (((trivializationAt F₁ E₁ x₀).symmL ℝ y).comp
              ((trivializationAt F₁ E₁ x₀).continuousLinearMapAt ℝ x₀)))‖
        ≤ ‖((trivializationAt F₂ E₂ x₀).symmL ℝ x₀).comp
              ((trivializationAt F₂ E₂ x₀).continuousLinearMapAt ℝ y)‖ *
            ‖(Ψ y).comp (((trivializationAt F₁ E₁ x₀).symmL ℝ y).comp
              ((trivializationAt F₁ E₁ x₀).continuousLinearMapAt ℝ x₀))‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖((trivializationAt F₂ E₂ x₀).symmL ℝ x₀).comp
              ((trivializationAt F₂ E₂ x₀).continuousLinearMapAt ℝ y)‖ *
            (‖Ψ y‖ * ‖((trivializationAt F₁ E₁ x₀).symmL ℝ y).comp
              ((trivializationAt F₁ E₁ x₀).continuousLinearMapAt ℝ x₀)‖) := by
          gcongr
          exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ r * (‖Ψ y‖ * r) := by gcongr
      _ = r ^ 2 * ‖Ψ y‖ := by ring
  have hrev : ∀ {r : ℝ}, 1 < r → ∀ᶠ y in 𝓝 x₀, ‖Ψ y‖ ≤ r ^ 2 * ‖Ψtil y‖ := by
    intro r hr
    have hSc' := eventually_norm_symmL_trivializationAt_comp_self_lt F₂ E₂ x₀ hr
    have hSa := eventually_norm_symmL_trivializationAt_self_comp_lt F₁ E₁ x₀ hr
    filter_upwards [hSc', hSa, hbasea, hbasec] with y hyc hya hya_mem hyc_mem
    have hid : Ψ y =
        (((trivializationAt F₂ E₂ x₀).symmL ℝ y).comp
            ((trivializationAt F₂ E₂ x₀).continuousLinearMapAt ℝ x₀)).comp
          ((Ψtil y).comp (((trivializationAt F₁ E₁ x₀).symmL ℝ x₀).comp
            ((trivializationAt F₁ E₁ x₀).continuousLinearMapAt ℝ y))) := by
      rw [hΨtil_def]
      ext v
      simp only [ContinuousLinearMap.comp_apply]
      rw [(trivializationAt F₁ E₁ x₀).continuousLinearMapAt_symmL hx₀a,
        (trivializationAt F₁ E₁ x₀).symmL_continuousLinearMapAt hya_mem,
        (trivializationAt F₂ E₂ x₀).continuousLinearMapAt_symmL hx₀c,
        (trivializationAt F₂ E₂ x₀).symmL_continuousLinearMapAt hyc_mem]
    rw [hid]
    calc ‖(((trivializationAt F₂ E₂ x₀).symmL ℝ y).comp
              ((trivializationAt F₂ E₂ x₀).continuousLinearMapAt ℝ x₀)).comp
            ((Ψtil y).comp (((trivializationAt F₁ E₁ x₀).symmL ℝ x₀).comp
              ((trivializationAt F₁ E₁ x₀).continuousLinearMapAt ℝ y)))‖
        ≤ ‖((trivializationAt F₂ E₂ x₀).symmL ℝ y).comp
              ((trivializationAt F₂ E₂ x₀).continuousLinearMapAt ℝ x₀)‖ *
            ‖(Ψtil y).comp (((trivializationAt F₁ E₁ x₀).symmL ℝ x₀).comp
              ((trivializationAt F₁ E₁ x₀).continuousLinearMapAt ℝ y))‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖((trivializationAt F₂ E₂ x₀).symmL ℝ y).comp
              ((trivializationAt F₂ E₂ x₀).continuousLinearMapAt ℝ x₀)‖ *
            (‖Ψtil y‖ * ‖((trivializationAt F₁ E₁ x₀).symmL ℝ x₀).comp
              ((trivializationAt F₁ E₁ x₀).continuousLinearMapAt ℝ y)‖) := by
          gcongr
          exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ r * (‖Ψtil y‖ * r) := by gcongr
      _ = r ^ 2 * ‖Ψtil y‖ := by ring
  change Tendsto (fun y => ‖Ψ y‖) (𝓝 x₀) (𝓝 ‖Ψ x₀‖)
  rw [tendsto_order]
  refine ⟨?_, ?_⟩
  · intro c hc
    obtain ⟨r, hr1, hrlt⟩ := exists_one_lt_mul_sq_lt hc
    have hev1 : ∀ᶠ y in 𝓝 x₀, c * r ^ 2 < ‖Ψtil y‖ :=
      hnormtil_lim.eventually (lt_mem_nhds hrlt)
    filter_upwards [hev1, hfwd hr1] with y hy1 hy2
    have hr2pos : (0 : ℝ) < r ^ 2 := by positivity
    have hchain : c * r ^ 2 < ‖Ψ y‖ * r ^ 2 := by
      calc c * r ^ 2 < ‖Ψtil y‖ := hy1
        _ ≤ r ^ 2 * ‖Ψ y‖ := hy2
        _ = ‖Ψ y‖ * r ^ 2 := by ring
    exact lt_of_mul_lt_mul_right hchain (le_of_lt hr2pos)
  · intro c hc
    obtain ⟨r, hr1, hrlt⟩ := exists_one_lt_mul_sq_lt hc
    have hlim2 : Tendsto (fun y => r ^ 2 * ‖Ψtil y‖) (𝓝 x₀) (𝓝 (r ^ 2 * ‖Ψ x₀‖)) :=
      hnormtil_lim.const_mul _
    have hlt2 : r ^ 2 * ‖Ψ x₀‖ < c := by rw [mul_comm]; exact hrlt
    have hev1 : ∀ᶠ y in 𝓝 x₀, r ^ 2 * ‖Ψtil y‖ < c :=
      hlim2.eventually (Iio_mem_nhds hlt2)
    filter_upwards [hev1, hrev hr1] with y hy1 hy2
    exact lt_of_le_of_lt hy2 hy1

end GenericHomOpNorm

/-! ## The fibrewise intrinsic operator-norm contraction bound

For a fibrewise continuous-linear operator `A : TensorRSSpace r a I x →L TensorRSSpace r c I x` whose
domain / codomain carry the `g`-fibre inner products (`tensorRS_riemannianBundle`), the intrinsic
squared fibre norm of the image is controlled by the squared `g`-fibre operator norm of `A` with no
dimension factor.  This is the sharp operator-norm fibre-norm bound, proved through the intrinsic
fibre-norm / `g`-bundle-norm bridge `riemannianFiberNormSq_eq_bundle_norm_sq'`. -/

section FibrewiseBound

variable (g : SmoothRiemannianMetric I M) (r a c : ℕ) (x : M)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The sharp intrinsic operator-norm fibre-norm bound on the second-order Hom-bundle.**  Install
the domain / codomain `(r, a)` / `(r, c)`-tensor `g`-fibre Riemannian bundle instances, under which
each fibre is a finite-dimensional inner-product space whose squared norm is `riemannianFiberNormSq`
(the bridge `riemannianFiberNormSq_eq_bundle_norm_sq'`).  For any fibrewise operator
`A : TensorRSSpace r a I x →L TensorRSSpace r c I x` the action obeys the squared `g`-fibre
operator-norm bound
```
rfns(A v) ≤ ‖A‖² · rfns(v)
```
with **no dimension factor**, where `‖A‖` is the `g`-fibre operator norm of `A` (its operator norm
measured in the installed Riemannian fibre norms).  The proof reads the bridge `rfns = ‖·‖²` on both
fibres, under which the claim is the square of the fundamental operator-norm inequality
`‖A v‖ ≤ ‖A‖ · ‖v‖` (`ContinuousLinearMap.le_opNorm`). -/
lemma homTensorRS_riemannianFiberNormSq_clm_apply_le
    (A : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (v : TensorRSSpace r a I x) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r a
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r c I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r c
    riemannianFiberNormSq (I := I) (M := M) g r c x (A v) ≤
      ‖A‖ ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r a x v := by
  letI instA : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r a
  letI instC : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r c I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r c
  rw [riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g r c x (A v),
    riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g r a x v]
  have hle : ‖A v‖ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
  calc ‖A v‖ ^ 2 ≤ (‖A‖ * ‖v‖) ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = ‖A‖ ^ 2 * ‖v‖ ^ 2 := by ring

end FibrewiseBound

/-! ## The continuous `g`-fibre operator norm of a smooth Hom-bundle section

The single genuinely-irreducible analytic content of the payoff: the `g`-fibre operator norm
`x ↦ ‖Ψ x‖` of a smooth full Hom-bundle section `Ψ` is continuous in the base point.  This is the
exact full-Hom analogue of the curvature-operator frame-energy continuity
`exists_continuous_riemannOp_tensorCovS_frameEnergy_bound` (`CurvatureFrameEnergyContinuity`): the
operator is assembled from the smooth metric `g` and the smooth section `Ψ`, the `g`-fibre inner
products on the domain / codomain tensor fibres vary continuously with `x`
(`tensorRSRiemannianInnerCLM_continuous`, packaged as `tensorRS_isContinuousRiemannianBundle`), and
`Ψ` varies continuously in the model trivialisation (`hΨ`), so the intrinsic `g`-fibre operator norm
`‖Ψ x‖` is a continuous (never chart-selection-*uniform*) function of `x`.  Proved by specialising the
generic continuous-Riemannian-bundle result `continuous_homBundle_opNorm_generic` above. -/

section OpNormContinuity

variable (g : SmoothRiemannianMetric I M) (r a c : ℕ)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **`g`-fibre operator-norm continuity of a smooth full Hom-bundle section.**  For a smooth
full Hom-bundle field `Ψ : Π x, TensorRSSpace r a I x →L TensorRSSpace r c I x` on a closed Riemannian
manifold the intrinsic `g`-fibre operator norm `x ↦ ‖Ψ x‖` — the operator norm of `Ψ x` measured in
the installed `(r, a)` / `(r, c)`-tensor `g`-fibre Riemannian bundle norms — is a *continuous*
function of the base point:
```
Continuous (fun x => ‖Ψ x‖).
```

This is the single genuinely-irreducible analytic content of the Hom-bundle envelope — the exact
full-Hom analogue of the curvature line's frame-energy continuity
`exists_continuous_riemannOp_tensorCovS_frameEnergy_bound`; the uniform bound
`exists_uniform_homTensorRS_opNorm_sq` is proved on top of it by "continuous on compact ⟹ bounded".

**Proof.**  This is the specialisation of the generic Hom-bundle operator-norm continuity
`continuous_homBundle_opNorm_generic` (proved above for an arbitrary pair of continuous Riemannian
vector bundles) to the `(r, a)`- and `(r, c)`-tensor bundles, whose continuous-Riemannian-bundle
structure is `tensorRS_isContinuousRiemannianBundle`.  The generic proof reads `Ψ` through the local
trivialisations at the base point: the conjugated operator into the *fixed* fibre `E₁ x₀ →L E₂ x₀` is
continuous (`continuousAt_hom_bundle` + composition with the fixed trivialisation maps) and agrees
with `Ψ x₀` at `x₀`, while the trivialisation transports distort the `g`-fibre norm by a factor
arbitrarily close to `1` (`eventually_norm_symmL_trivializationAt_self_comp_lt` and its companion),
giving the two-sided multiplicative pinch and the `r → 1` squeeze via `tendsto_order`.  This is the
chart-locality-free route: the operator norm is the *intrinsic* `g`-fibre operator norm, never the
chart-trivialisation operator-norm scalar (unbounded on multi-chart manifolds); the trivialisation
enters only as the continuity tool.

**Non-vacuity.**  This is a genuine continuity statement about the `g`-fibre operator norm of `Ψ`,
not a degenerate predicate: it constrains `Ψ` through its operator norm and is *false* for a
discontinuous operator-norm assignment (e.g. an operator-valued field jumping between two distinct
fibre norms), so it is not satisfiable by an arbitrary section. -/
theorem continuous_homTensorRS_opNorm
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r a
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r c I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r c
    Continuous (fun x : M => ‖Ψ x‖) := by
  letI instA : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r a
  letI instC : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r c I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r c
  exact continuous_homBundle_opNorm_generic
    (F₁ := TensorRSModel r a ℝ E) (F₂ := TensorRSModel r c ℝ E)
    (E₁ := fun z : M => TensorRSSpace r a I z) (E₂ := fun z : M => TensorRSSpace r c I z)
    Ψ hΨ.continuous

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **Uniform `g`-fibre squared operator-norm bound of a smooth full Hom-bundle section.**
For a smooth full Hom-bundle field `Ψ : Π x, TensorRSSpace r a I x →L TensorRSSpace r c I x` on a
closed Riemannian manifold there is a *single* nonnegative constant `C`, uniform over `M`, bounding,
at every base point `x`, the squared `g`-fibre operator norm of `Ψ x` (the operator norm measured in
the installed `(r, a)` / `(r, c)`-tensor `g`-fibre Riemannian bundle norms):
```
‖Ψ x‖² ≤ C.
```

This is the exact full-Hom analogue of the curvature line's uniform constant
`exists_uniform_riemannOp_tensorCovS_dualFrameEnergy_const`; the continuous version
`exists_continuous_homTensorRS_opNorm_sq` is proved on top of it by `continuous_const`, exactly as
`exists_continuous_riemannOp_tensorCovS_frameEnergy_bound` is proved on top of its uniform constant.

**Proof.**  By the posited `g`-fibre operator-norm continuity `continuous_homTensorRS_opNorm` the map
`x ↦ ‖Ψ x‖` is continuous, hence so is `x ↦ ‖Ψ x‖²` (`Continuous.pow`); on the compact `M` its range
is compact (`isCompact_range`) and therefore bounded above (`IsCompact.bddAbove`), giving a constant
`C₀` with `‖Ψ x‖² ≤ C₀` at every `x`.  Take `C := max C₀ 0 ≥ 0`, which also bounds `‖Ψ x‖²`.  This is
the chart-locality-free route: the operator norm is the *intrinsic* `g`-fibre operator norm, never
the chart-trivialisation operator-norm scalar (unbounded on multi-chart manifolds).

**Non-vacuity.**  A degenerate `C = 0` is rejected: at any `x` where `Ψ x ≠ 0` there is a fibre
tensor `v` with `‖Ψ x v‖_g > 0`, forcing `‖Ψ x‖² > 0` and hence `C > 0`; the smallest valid value is
the genuine uniform squared `g`-fibre operator-norm sup, positive for a nonzero `Ψ`. -/
theorem exists_uniform_homTensorRS_opNorm_sq
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r a
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r c I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r c
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : M, ‖Ψ x‖ ^ 2 ≤ C := by
  letI instA : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r a
  letI instC : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r c I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r c
  have hcont : Continuous (fun x : M => ‖Ψ x‖) :=
    continuous_homTensorRS_opNorm (I := I) (M := M) g r a c Ψ hΨ
  have hcont_sq : Continuous (fun x : M => ‖Ψ x‖ ^ 2) := hcont.pow 2
  obtain ⟨C₀, hC₀⟩ := (isCompact_range hcont_sq).bddAbove
  refine ⟨max C₀ 0, le_max_right _ _, fun x => ?_⟩
  exact le_trans (hC₀ (Set.mem_range_self x)) (le_max_left _ _)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **Continuous `g`-fibre squared operator norm of a smooth full Hom-bundle section.**  For a smooth
full Hom-bundle field `Ψ : Π x, TensorRSSpace r a I x →L TensorRSSpace r c I x` on a closed Riemannian
manifold there is a *continuous* nonnegative function `N : M → ℝ` that dominates, at every base point
`x`, the squared `g`-fibre operator norm of `Ψ x` (the operator norm measured in the installed
`(r, a)` / `(r, c)`-tensor `g`-fibre Riemannian bundle norms):
```
‖Ψ x‖² ≤ N x.
```

**Proof.**  By the uniform bound `exists_uniform_homTensorRS_opNorm_sq` there is a single nonnegative
constant `C` with `‖Ψ x‖² ≤ C` at every `x`; take the constant function `N := fun _ => C`, which is
continuous (`continuous_const`) and nonnegative, and dominates `‖Ψ x‖²` at every point.  This is the
exact full-Hom analogue of the proved curvature-operator frame-energy continuity
`exists_continuous_riemannOp_tensorCovS_frameEnergy_bound`, which is likewise the constant continuous
envelope of its posited uniform curvature constant.

**Non-vacuity.**  A degenerate `N ≡ 0` is rejected: at any `x` where `Ψ x ≠ 0` there is a fibre
tensor `v` with `‖Ψ x v‖_g > 0`, forcing `‖Ψ x‖² > 0` and hence `N x > 0`; the smallest valid value
is the genuine squared `g`-fibre operator norm, positive wherever `Ψ x ≠ 0`. -/
theorem exists_continuous_homTensorRS_opNorm_sq
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r a
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r c I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r c
    ∃ N : M → ℝ, Continuous N ∧ (∀ x : M, 0 ≤ N x) ∧ ∀ x : M, ‖Ψ x‖ ^ 2 ≤ N x := by
  obtain ⟨C, hC_nonneg, hC_bound⟩ :=
    exists_uniform_homTensorRS_opNorm_sq (I := I) (M := M) g r a c Ψ hΨ
  exact ⟨fun _ => C, continuous_const, fun _ => hC_nonneg, hC_bound⟩

end OpNormContinuity

/-! ## The payoff: the continuous per-point `g`-fibre contraction envelope

The reason this file exists.  Assembled from the fibrewise intrinsic operator bound and the
continuity of the squared `g`-fibre operator norm, the smooth full Hom-bundle section `Ψ` admits a
continuous nonnegative per-point envelope `Cop` for the fibrewise contraction `rfns(Ψ x v) ≤ Cop x ·
rfns(v)`.  This is the general envelope of which the rank-`r` curvature operator-field bound
`exists_continuous_riemannianFiberNormSq_homSection_clm_le` is the curvature instance. -/

section Payoff

variable (g : SmoothRiemannianMetric I M) (r a c : ℕ)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
/-- **The continuous per-point `g`-fibre contraction envelope of a smooth full Hom-bundle section
(the payoff, the general envelope).**  For a *fixed* smooth full Hom-bundle field
`Ψ : Π x, TensorRSSpace r a I x →L TensorRSSpace r c I x` on a closed Riemannian manifold there is a
continuous nonnegative `Cop : M → ℝ` with the per-point fibrewise contraction bound
```
rfns(Ψ x v) ≤ Cop x · rfns(v)
```
at every point `x` and every `(r, a)`-tensor fibre value `v`.

**Proof.**  Take `Cop x := ‖Ψ x‖²_g`, the squared `g`-fibre operator norm of `Ψ x`; it is continuous
and nonnegative as a continuous dominating envelope `N` by `exists_continuous_homTensorRS_opNorm_sq`.
The fibrewise bound `rfns(Ψ x v) ≤ ‖Ψ x‖²_g · rfns(v)` is the sharp intrinsic operator-norm fibre-
norm bound `homTensorRS_riemannianFiberNormSq_clm_apply_le`, and `‖Ψ x‖²_g · rfns(v) ≤ N x · rfns(v)`
since `rfns(v) ≥ 0`.  This is the exact full-Hom analogue of the proved continuous per-point
curvature-operator envelope `exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional`,
proved generically for an arbitrary smooth Hom-bundle section.

**Non-vacuity.**  A degenerate `Cop ≡ 0` is rejected: the bound at any `v` with `rfns(v) > 0` and
`Ψ x v ≠ 0` forces `Cop x > 0`; the smallest valid value is the genuine squared `g`-fibre operator
norm `‖Ψ x‖²_g`, positive wherever `Ψ x ≠ 0`. -/
theorem exists_continuous_riemannianFiberNormSq_homTensorRS_section_clm_le
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    ∃ Cop : M → ℝ, Continuous Cop ∧ (∀ x : M, 0 ≤ Cop x) ∧
      ∀ (x : M) (v : TensorRSSpace r a I x),
        riemannianFiberNormSq (I := I) (M := M) g r c x (Ψ x v) ≤
          Cop x * riemannianFiberNormSq (I := I) (M := M) g r a x v := by
  letI instA : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r a
  letI instC : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r c I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r c
  obtain ⟨N, hN_cont, hN_nonneg, hN_bound⟩ :=
    exists_continuous_homTensorRS_opNorm_sq (I := I) (M := M) g r a c Ψ hΨ
  refine ⟨N, hN_cont, hN_nonneg, fun x v => ?_⟩
  refine le_trans (homTensorRS_riemannianFiberNormSq_clm_apply_le
    (I := I) (M := M) g r a c x (Ψ x) v) ?_
  exact mul_le_mul_of_nonneg_right (hN_bound x)
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g r a x v)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
/-- **The uniform `g`-fibre contraction bound of a smooth full Hom-bundle section.**  For a *fixed*
smooth full Hom-bundle field `Ψ : Π x, TensorRSSpace r a I x →L TensorRSSpace r c I x` on a closed
Riemannian manifold there is a single nonnegative constant `C`, uniform over `M`, with the per-point
fibrewise contraction bound
```
rfns(Ψ x v) ≤ C · rfns(v)
```
for every point `x` and every `(r, a)`-tensor fibre value `v`.

**Proof.**  By the continuous per-point envelope
`exists_continuous_riemannianFiberNormSq_homTensorRS_section_clm_le` there is a continuous nonnegative
`Cop : M → ℝ` with `rfns(Ψ x v) ≤ Cop x · rfns(v)`; on the compact `M` the continuous `Cop` has
bounded range (`(isCompact_univ).image Cop_cont |>.bddAbove`), so `C := max C₀ 0 ≥ Cop x` uniformly,
and `Cop x · rfns(v) ≤ C · rfns(v)` by `rfns(v) ≥ 0`.

**Non-vacuity.**  A degenerate `C < 0` is rejected: the conclusion `rfns(Ψ x v) ≤ C · rfns(v)` at any
`v` with `rfns(v) > 0` and `Ψ x v ≠ 0` forces `C > 0`; the smallest valid `C` is the genuine uniform
squared `g`-fibre operator-norm sup, positive for a nonzero `Ψ`. -/
theorem exists_uniform_riemannianFiberNormSq_homTensorRS_section_clm_le
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : M) (v : TensorRSSpace r a I x),
      riemannianFiberNormSq (I := I) (M := M) g r c x (Ψ x v) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g r a x v := by
  obtain ⟨Cop, hCop_cont, hCop_nn, hCop_bound⟩ :=
    exists_continuous_riemannianFiberNormSq_homTensorRS_section_clm_le
      (I := I) (M := M) g r a c Ψ hΨ
  have hCpt := (isCompact_univ (X := M)).image hCop_cont
  obtain ⟨C₀, hC₀⟩ := hCpt.bddAbove
  refine ⟨max C₀ 0, le_max_right _ _, fun x v => ?_⟩
  have hCop_le : Cop x ≤ max C₀ 0 :=
    le_trans (hC₀ ⟨x, Set.mem_univ _, rfl⟩) (le_max_left _ _)
  refine le_trans (hCop_bound x v) ?_
  exact mul_le_mul_of_nonneg_right hCop_le
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g r a x v)

end Payoff

end DifferentialGeometry.Integral.Connection
