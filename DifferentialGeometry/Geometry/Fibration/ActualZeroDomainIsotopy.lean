import DifferentialGeometry.Geometry.Fibration.ActualZeroDomainEstimates
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdpBlocks
import DifferentialGeometry.Geometry.Fibration.ActualFreezeScale
import DifferentialGeometry.Geometry.Fibration.ZeroDomainIsotopyProfiles
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.CoreBoundary
import DifferentialGeometry.Topology.Ehresmann.SublevelTransportLevel

/-!
# ZSP02, the kernel: the actual zero domain, its face, and the isotopy (ZH)

Lane C14-ZSP35. Blueprint `master207B.tex`, ZSP02 (`thm:fibration-actual-zero-domains`,
B:6374–6479), for ANY smooth map `f` into the block space carrying ZSP01's (ZE)
`‖J_k(f − 𝓔⁰)‖ < δ₀R_k` (`δ₀ < 1/1000`) and a derivative bound `‖df − d𝓔⁰‖ ≤ H√g` (`H < 1/100`),
with the radial-function parameters `εr < 1/2` (LC29's gradient bound `1 − εr`) and `e < 1/40`
(LC30's `|η − d/R| < e`). The chain binding is `ActualStageChainEZeroDomains`.

Instead of the blueprint's ratio `r = u/v` the family (ZH) uses the LINEAR adjusted quantity
`q = ℓ ∘ f + .4`, `ℓ(w) = R⁻¹(u_k(w) − .4v_k(w))` (`zspQCLM_ZSP35`): it is smooth everywhere, equals
`η_k` for `f = 𝓔⁰` on the band where the cutoff is one, and `q ≤ .4 ⟺ u ≤ .4v`, `q = .4 ⟺ u = .4v`,
so the sublevel/level of `h₁` are the same sets (ZD)/(ZF). The ratio `r − .4` is ZSP02's defining
function near the face (`zsp_defining_ZSP35`).

* `zsp_radial_facts_ZSP35`, `zsp_band_marker_ZSP35`, `zspQCLM_globalMap_ZSP35`, `zsp_q_close_ZSP35`
  (`|q − η| < 7δ₀/5` on the band), `zsp_q_deriv_ZSP35` ((ZC), linear form:
  `|dq(W) − dη(W)| ≤ (7/5)H √(R⁻²g(W, W))`), `zsp_q_grad_pos_ZSP35`;
* (ZH) `h_τ = ψ(η) + τχ(η)(q − η)` with the profiles of `ZeroDomainIsotopyProfiles`:
  `contMDiff_zspH0_ZSP35`, `contMDiff_zspK_ZSP35` (smooth on all of `M`),
  `zsp_level_transversal_ZSP35` (every `h_τ` submersive at its level `.4`),
  `zsp_sublevel_eq_ZSP35` (`{h₁ ≤ .4} = Z_k`, `{h₁ = .4} =` (ZF));
* `zspDomain_ZSP35` (ZD) `= B(c_k, .35R_k) ∪ f⁻¹{v_k ≥ .9R_k, u_k ≤ .4v_k}`, `zspFace_ZSP35` (ZF);
* `zsp02_kernel_ZSP35`: `Z_k` compact; a diffeomorphism of the carrier (FC34b,
  `exists_diffeomorph_image_sublevel_of_affine_family`) carries `{η_k ≤ .4}` onto `Z_k` and
  `{η_k = .4}` onto (ZF); `∂Z_k =` (ZF); `B̄(c_k, (.381 − e)R_k) ⊆ int Z_k`,
  `Z_k ⊆ B(c_k, (.402 + e)R_k)`; the face lies in `|η_k − .4| < 1/500`;
* `zsp_defining_ZSP35`: on the open `{.39 < η_k < .41} ⊇` (ZF), `v_k > .99R_k`, `r_k = u_k/v_k − .4`
  is smooth and `Z_k = {r_k ≤ 0}` there; `dr_k ≠ 0` at every face point.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

omit [CompactSpace X] in
/-- **The radial function of a zero ball near its faces** (from `radial_spec`): `η` is continuous;
`|η − R⁻¹d(·, c)| < e`; it is smooth on an open `O' ⊇ η⁻¹[1/5, 2]`; its `R⁻²g`-gradient has length
at least `1 − ε` on `η⁻¹[1/5, 2]`; the annular cutoff is `1` on `η⁻¹[3/10, 4/5]`. -/
theorem zsp_radial_facts_ZSP35 (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)
    (k : Z.finite_centres.toFinset) :
    Continuous (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial ∧
    (∀ x, |(Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x -
      ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ *
        dist x (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center| < e) ∧
    (∃ O' : Set X, IsOpen O' ∧
      (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ O' ∧
      ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial O') ∧
    (∀ x, (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x ∈ Icc (1 / 5 : ℝ) 2 →
      1 - εr ≤ Real.sqrt ((scaleMetric (((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹
        ^ 2) (pow_pos (inv_pos.mpr (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos) 2)
          g).inner x
        (gradFun (scaleMetric (((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ ^ 2)
          (pow_pos (inv_pos.mpr (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos) 2) g)
          (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x)
        (gradFun (scaleMetric (((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ ^ 2)
          (pow_pos (inv_pos.mpr (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos) 2) g)
          (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x))) ∧
    (∀ x, (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x ∈ Icc (3 / 10 : ℝ) (4 / 5) →
      Calculus.annularCutoff Calculus.cutoffProfile
        ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x) = 1) := by
  have hR := (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  obtain ⟨hlip, -, hclose, -, -, -, -, hgrad, -, hsub10, ⟨O', hO'o, hO'sub, hO'sm, -⟩, -, -, -, -,
    -, hone, -⟩ := (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial_spec
  refine ⟨@LipschitzWith.continuous X ℝ (mX.rescale
      ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹
        (inv_pos.mpr hR)).toPseudoEMetricSpace
      _ _ _ hlip, fun x => ?_, ⟨O', hO'o, hO'sub, hO'sm⟩, fun x hx => (hgrad x (hsub10 hx)).1, hone⟩
  have h1 := hclose x
  rw [@Metric.infDist_singleton X (mX.rescale ((Z.zero k.1
    ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ (inv_pos.mpr hR)).toPseudoMetricSpace] at h1
  exact h1

/-- ZSP02's linear functional `w ↦ R⁻¹(u_k(w) − .4 v_k(w))` on the block space (`u_k = (w_k)_vec 0`,
`v_k = (w_k)_mark`): the adjusted defining quantity, `q = ℓ ∘ f + 2/5` (`q ≤ .4 ⟺ u ≤ .4v`). -/
def zspQCLM_ZSP35 (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (k : Z.finite_centres.toFinset) :
    BlockSpace (fun _ : CGPTag L Z => ℝ²) →L[ℝ] ℝ :=
  ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ •
    ((EuclideanSpace.proj (0 : Fin 2)).comp
        (blockVectorCLM (V := fun _ : CGPTag L Z => ℝ²) (.inr (.inr (.inr (.inl k))))) -
      (2 / 5 : ℝ) • blockMarkerCLM (V := fun _ : CGPTag L Z => ℝ²) (.inr (.inr (.inr (.inl k)))))

theorem zspQCLM_apply_ZSP35
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (k : Z.finite_centres.toFinset)
    (y : BlockSpace (fun _ : CGPTag L Z => ℝ²)) :
    zspQCLM_ZSP35 L Z k y = ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ *
      (((y (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 -
        2 / 5 * (y (.inr (.inr (.inr (.inl k))))).snd) := by
  simp [zspQCLM_ZSP35, blockVectorCLM_apply, blockMarkerCLM_apply]

/-- `|ℓ(y)| ≤ (7/5)R⁻¹‖y_k‖ ≤ (7/5)R⁻¹‖y‖`. -/
theorem abs_zspQCLM_le_ZSP35
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (k : Z.finite_centres.toFinset)
    (y : BlockSpace (fun _ : CGPTag L Z => ℝ²)) :
    |zspQCLM_ZSP35 L Z k y| ≤ 7 / 5 * ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ *
      ‖y (.inr (.inr (.inr (.inl k))))‖ ∧
    |zspQCLM_ZSP35 L Z k y| ≤ 7 / 5 * ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ *
      ‖y‖ := by
  have hR := (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  obtain ⟨h1, h2⟩ := abs_block_components_le_GAF2 (y (.inr (.inr (.inr (.inl k)))))
  have hk : ‖y (.inr (.inr (.inr (.inl k))))‖ ≤ ‖y‖ := PiLp.norm_apply_le y _
  have hmain : |zspQCLM_ZSP35 L Z k y| ≤
      7 / 5 * ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ *
        ‖y (.inr (.inr (.inr (.inl k))))‖ := by
    rw [zspQCLM_apply_ZSP35, abs_mul, abs_of_pos (inv_pos.mpr hR)]
    have h3 : |((y (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 -
        2 / 5 * (y (.inr (.inr (.inr (.inl k))))).snd| ≤
        7 / 5 * ‖y (.inr (.inr (.inr (.inl k))))‖ := by
      calc _ ≤ |((y (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0| +
            |2 / 5 * (y (.inr (.inr (.inr (.inl k))))).snd| := abs_sub _ _
        _ ≤ _ := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 5)]; linarith
    have := mul_le_mul_of_nonneg_left h3 (inv_pos.mpr hR).le
    linarith
  refine ⟨hmain, hmain.trans ?_⟩
  exact mul_le_mul_of_nonneg_left hk (by positivity)

/-- On the band `3/10 ≤ η_k ≤ 4/5` (cutoff one) the original block is `(Rη, R)`, so
`ℓ(𝓔⁰ p) + 2/5 = η_k(p)`. -/
theorem zspQCLM_globalMap_ZSP35
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (k : Z.finite_centres.toFinset)
    {p : X} (hp : (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p ∈
      Icc (3 / 10 : ℝ) (4 / 5)) :
    zspQCLM_ZSP35 L Z k (cgpGlobalMap L Z p) + 2 / 5 =
      (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p := by
  have hR := (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hone, -⟩ :=
    (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial_spec
  obtain ⟨h1, h2⟩ := cgpGlobalMap_zeroBlock_GAF2 L Z k p
  rw [zspQCLM_apply_ZSP35, h1, h2, hone p hp]
  field_simp
  ring

/-- On the band, ZSP01's (ZE) gives `|q − η| < (7/5)δ₀` for `q = ℓ ∘ f + 2/5`. -/
theorem zsp_q_close_ZSP35
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (k : Z.finite_centres.toFinset)
    (f : X → BlockSpace (fun _ : CGPTag L Z => ℝ²)) {δ₀ : ℝ}
    (hZE : ∀ p, ‖f p (.inr (.inr (.inr (.inl k)))) -
        cgpGlobalMap L Z p (.inr (.inr (.inr (.inl k))))‖ <
      δ₀ * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)
    {p : X} (hp : (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p ∈
      Icc (3 / 10 : ℝ) (4 / 5)) :
    |zspQCLM_ZSP35 L Z k (f p) + 2 / 5 - (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p|
      < 7 / 5 * δ₀ := by
  have hR := (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  rw [← zspQCLM_globalMap_ZSP35 L Z k hp, add_sub_add_right_eq_sub, ← map_sub]
  have h1 := (abs_zspQCLM_le_ZSP35 L Z k (f p - cgpGlobalMap L Z p)).1
  have h2 : ‖(f p - cgpGlobalMap L Z p) (.inr (.inr (.inr (.inl k))))‖ <
      δ₀ * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius := hZE p
  have h3 : 7 / 5 * ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ *
      ‖(f p - cgpGlobalMap L Z p) (.inr (.inr (.inr (.inl k))))‖ < 7 / 5 * δ₀ := by
    have := mul_lt_mul_of_pos_left h2 (by positivity : (0 : ℝ) <
      7 / 5 * ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹)
    calc _ < _ := this
      _ = 7 / 5 * δ₀ := by field_simp
  linarith

/-- **(ZC) for the adjusted defining quantity** (B:6425–6442, linear form): on the open band
`3/10 < η_k < 4/5`, for every tangent vector `W`,
`|d(ℓ ∘ f)(W) − dη_k(W)| ≤ (7/5)H √(R⁻²g(W, W))`, where `H` bounds `‖df − d𝓔⁰‖` against `√g`. -/
theorem zsp_q_deriv_ZSP35
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (k : Z.finite_centres.toFinset)
    (f : X → BlockSpace (fun _ : CGPTag L Z => ℝ²))
    (hf : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag L Z => ℝ²)) ∞ f)
    (hF : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag L Z => ℝ²)) ∞ (cgpGlobalMap L Z))
    {Hd : ℝ} (hder : ∀ p (W : TangentSpace 𝓘(ℝ, E3) p), ‖mvfderiv 𝓘(ℝ, E3) f p W -
      mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap L Z) p W‖ ≤ Hd * Real.sqrt (g.inner p W W))
    {p : X} (hp : (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p ∈
      Ioo (3 / 10 : ℝ) (4 / 5)) (W : TangentSpace 𝓘(ℝ, E3) p) :
    |mvfderiv 𝓘(ℝ, E3) (fun z => zspQCLM_ZSP35 L Z k (f z)) p W -
        mvfderiv 𝓘(ℝ, E3) (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p W| ≤
      7 / 5 * Hd * Real.sqrt (((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ ^ 2 *
        g.inner p W W) := by
  have hR := (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  obtain ⟨hηc, -, ⟨O', hO'o, hO'sub, hO'sm⟩, -, -⟩ := zsp_radial_facts_ZSP35 Z k
  have hpO : p ∈ O' := hO'sub ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have hηd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
      (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p :=
    (hO'sm.contMDiffAt (hO'o.mem_nhds hpO)).mdifferentiableAt (by simp)
  have h1 := mvfderiv_clm_comp_apply_EDPE (zspQCLM_ZSP35 L Z k) ((hf p).mdifferentiableAt
    (by simp)) W
  have h2 := mvfderiv_clm_comp_apply_EDPE (zspQCLM_ZSP35 L Z k) ((hF p).mdifferentiableAt
    (by simp)) W
  have hopen : IsOpen {z | 3 / 10 < (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z ∧
      (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z < 4 / 5} :=
    (isOpen_lt continuous_const hηc).inter (isOpen_lt hηc continuous_const)
  have hev : (fun z => zspQCLM_ZSP35 L Z k (cgpGlobalMap L Z z)) =ᶠ[𝓝 p]
      (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial - fun _ => 2 / 5 := by
    filter_upwards [hopen.mem_nhds hp] with z hz
    have := zspQCLM_globalMap_ZSP35 L Z k (p := z) ⟨hz.1.le, hz.2.le⟩
    simp only [Pi.sub_apply]
    linarith
  have hη : mvfderiv 𝓘(ℝ, E3) (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p W =
      zspQCLM_ZSP35 L Z k (mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap L Z) p W) := by
    rw [← h2, mvfderiv_congr_EDPE hev, mvfderiv_sub hηd mdifferentiableAt_const,
      mvfderiv_const, sub_zero]
  rw [h1, hη, ← map_sub]
  have h3 := (abs_zspQCLM_le_ZSP35 L Z k (mvfderiv 𝓘(ℝ, E3) f p W -
    mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap L Z) p W)).2
  have h4 := mul_le_mul_of_nonneg_left (hder p W) (by positivity : (0 : ℝ) ≤
    7 / 5 * ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹)
  rw [sqrt_inv_sq_mul_FC19 hR]
  calc _ ≤ _ := h3
    _ ≤ _ := h4
    _ = _ := by ring

/-- **Transversality of the whole isotopy family (ZH) at its level `.4`** (B:6462–6465): for
`τ ∈ [0, 1]` and every point `p` with `h_τ(p) = .4`, where
`h_τ = ψ(η_k) + τχ(η_k)(q − η_k)`, `q = ℓ ∘ f + 2/5`, the differential of `h_τ` at `p` is onto
(given (ZE) with `δ₀ < 1/1000`, the derivative bound `H < 1/100` and LC29's `εr < 1/2`). -/
theorem zsp_level_transversal_ZSP35
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (k : Z.finite_centres.toFinset)
    (f : X → BlockSpace (fun _ : CGPTag L Z => ℝ²))
    (hf : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag L Z => ℝ²)) ∞ f)
    (hF : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag L Z => ℝ²)) ∞ (cgpGlobalMap L Z))
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1 / 1000)
    (hZE : ∀ p, ‖f p (.inr (.inr (.inr (.inl k)))) -
        cgpGlobalMap L Z p (.inr (.inr (.inr (.inl k))))‖ <
      δ₀ * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)
    {Hd : ℝ} (hHd : Hd < 1 / 100) (hder : ∀ p (W : TangentSpace 𝓘(ℝ, E3) p),
      ‖mvfderiv 𝓘(ℝ, E3) f p W - mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap L Z) p W‖ ≤
        Hd * Real.sqrt (g.inner p W W))
    (hεr : εr < 1 / 2) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) {p : X}
    (hlev : zspPsi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p) +
      τ * (zspChi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p) *
        (zspQCLM_ZSP35 L Z k (f p) + 2 / 5 -
          (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p)) = 2 / 5) :
    Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun z =>
      zspPsi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) +
        τ * (zspChi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
          (zspQCLM_ZSP35 L Z k (f z) + 2 / 5 -
            (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z))) p) := by
  have hR := (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  obtain ⟨hηc, -, ⟨O', hO'o, hO'sub, hO'sm⟩, hgrad, -⟩ := zsp_radial_facts_ZSP35 Z k
  -- the level lies where `ψ = id` and `χ = 1`
  have hloc : |(Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p - 2 / 5| < 1 / 500 :=
    zsp_level_location_ZSP35 hτ (fun h1 h2 => by
      have := zsp_q_close_ZSP35 L Z k f hZE (p := p) ⟨by linarith, by linarith⟩
      linarith) hlev
  obtain ⟨hl1, hl2⟩ := abs_lt.mp hloc
  have hpO : p ∈ O' := hO'sub ⟨by linarith, by linarith⟩
  have hηd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
      (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p :=
    (hO'sm.contMDiffAt (hO'o.mem_nhds hpO)).mdifferentiableAt (by simp)
  have hqd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun z => zspQCLM_ZSP35 L Z k (f z)) p :=
    (((zspQCLM_ZSP35 L Z k).contDiff.contMDiff.comp hf) p).mdifferentiableAt (by simp)
  have hopen : IsOpen {z | 34 / 100 < (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z ∧
      (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z < 46 / 100} :=
    (isOpen_lt continuous_const hηc).inter (isOpen_lt hηc continuous_const)
  have hev : (fun z =>
      zspPsi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) +
        τ * (zspChi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
          (zspQCLM_ZSP35 L Z k (f z) + 2 / 5 -
            (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z))) =ᶠ[𝓝 p]
      (fun z => (1 - τ) * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) +
        (fun z => τ * zspQCLM_ZSP35 L Z k (f z)) + fun _ => τ * (2 / 5) := by
    filter_upwards [hopen.mem_nhds ⟨by linarith, by linarith⟩] with z hz
    rw [zspPsi_eq_self_ZSP35 (by linarith [hz.1]) (by linarith [hz.2]),
      zspChi_eq_one_ZSP35 hz.1.le hz.2.le]
    simp only [Pi.add_apply]
    ring
  set gR := scaleMetric (((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ ^ 2)
    (pow_pos (inv_pos.mpr (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos) 2) g
    with hgR
  set W := gradFun gR (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p with hW
  have hn := hgrad p ⟨by linarith, by linarith⟩
  set n := Real.sqrt (gR.inner p W W) with hn_def
  have hn0 : 0 < n := by linarith
  have hin : gR.inner p W W = n ^ 2 := by
    rw [hn_def, Real.sq_sqrt]
    exact le_of_lt (Real.sqrt_pos.mp hn0)
  have hdη : mvfderiv 𝓘(ℝ, E3) (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p W =
      n ^ 2 := by
    rw [← hin]
    exact (inner_gradFun gR _ p W).symm
  have hdq := zsp_q_deriv_ZSP35 L Z k f hf hF hder (p := p) ⟨by linarith, by linarith⟩ W
  have hsq : Real.sqrt (((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ ^ 2 *
      g.inner p W W) = n := rfl
  rw [hsq] at hdq
  have hval : mvfderiv 𝓘(ℝ, E3) ((fun z => (1 - τ) *
      (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) +
        (fun z => τ * zspQCLM_ZSP35 L Z k (f z)) + fun _ => τ * (2 / 5)) p W =
      (1 - τ) * mvfderiv 𝓘(ℝ, E3) (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p W +
        τ * mvfderiv 𝓘(ℝ, E3) (fun z => zspQCLM_ZSP35 L Z k (f z)) p W := by
    have hA : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun z => (1 - τ) *
        (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) p := hηd.const_smul (1 - τ)
    have hB : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun z => τ * zspQCLM_ZSP35 L Z k (f z)) p :=
      hqd.const_smul τ
    rw [mvfderiv_add (hA.add hB) mdifferentiableAt_const, mvfderiv_const, add_zero,
      mvfderiv_add hA hB]
    rw [mvfderiv_const_mul _ (1 - τ) hηd, mvfderiv_const_mul _ τ hqd]
    rfl
  have hpos : 0 < mvfderiv 𝓘(ℝ, E3) ((fun z => (1 - τ) *
      (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) +
        (fun z => τ * zspQCLM_ZSP35 L Z k (f z)) + fun _ => τ * (2 / 5)) p W := by
    rw [hval, hdη]
    obtain ⟨hd1, hd2⟩ := abs_le.mp hdq
    have hτ0 := hτ.1
    have hτ1 := hτ.2
    nlinarith
  rw [← mvfderiv_congr_EDPE hev] at hpos
  refine DifferentialGeometry.Topology.Ehresmann.surjective_of_ne_zero_FC19 _ fun h0 => ?_
  have h00 : mvfderiv 𝓘(ℝ, E3) (fun z =>
      zspPsi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) +
        τ * (zspChi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
          (zspQCLM_ZSP35 L Z k (f z) + 2 / 5 -
            (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z))) p W = 0 := by
    unfold mvfderiv
    rw [h0]
    rfl
  linarith

omit [CompactSpace X] in
/-- `h₀ = ψ ∘ η_k` is smooth on the whole carrier (`ψ` is constant near the possibly nonsmooth
core and far region; elsewhere `η_k` is in its smooth window). -/
theorem contMDiff_zspH0_ZSP35 (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)
    (k : Z.finite_centres.toFinset) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞
      (fun z => zspPsi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z)) := by
  obtain ⟨hηc, -, ⟨O', hO'o, hO'sub, hO'sm⟩, -, -⟩ := zsp_radial_facts_ZSP35 Z k
  intro p
  by_cases hlo : (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p < 3 / 10
  · have hev : (fun z => zspPsi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z))
        =ᶠ[𝓝 p] fun _ => (3 / 10 : ℝ) := by
      filter_upwards [(isOpen_lt hηc continuous_const).mem_nhds hlo] with z hz
      exact zspPsi_eq_low_ZSP35 (le_of_lt hz)
    exact contMDiffAt_const.congr_of_eventuallyEq hev
  by_cases hhi : 1 / 2 < (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p
  · have hev : (fun z => zspPsi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z))
        =ᶠ[𝓝 p] fun _ => (1 / 2 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const hηc).mem_nhds hhi] with z hz
      exact zspPsi_eq_high_ZSP35 (le_of_lt hz)
    exact contMDiffAt_const.congr_of_eventuallyEq hev
  push Not at hlo hhi
  have hpO : p ∈ O' := hO'sub ⟨by linarith, by linarith⟩
  exact contDiff_zspPsi_ZSP35.contMDiff.contMDiffAt.comp p
    (hO'sm.contMDiffAt (hO'o.mem_nhds hpO))

/-- `k_f = χ(η_k)(q − η_k)` is smooth on the whole carrier (`χ ∘ η_k` vanishes near every point
outside the smooth window of `η_k`). -/
theorem contMDiff_zspK_ZSP35
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (k : Z.finite_centres.toFinset)
    (f : X → BlockSpace (fun _ : CGPTag L Z => ℝ²))
    (hf : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag L Z => ℝ²)) ∞ f) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (fun z =>
      zspChi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
        (zspQCLM_ZSP35 L Z k (f z) + 2 / 5 -
          (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z)) := by
  obtain ⟨hηc, -, ⟨O', hO'o, hO'sub, hO'sm⟩, -, -⟩ := zsp_radial_facts_ZSP35 Z k
  intro p
  by_cases hlo : (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p < 33 / 100
  · have hev : (fun z =>
        zspChi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
          (zspQCLM_ZSP35 L Z k (f z) + 2 / 5 -
            (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z)) =ᶠ[𝓝 p]
        fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt hηc continuous_const).mem_nhds hlo] with z hz
      rw [zspChi_eq_zero_ZSP35 (Or.inl (le_of_lt hz)), zero_mul]
    exact contMDiffAt_const.congr_of_eventuallyEq hev
  by_cases hhi : 47 / 100 < (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p
  · have hev : (fun z =>
        zspChi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
          (zspQCLM_ZSP35 L Z k (f z) + 2 / 5 -
            (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z)) =ᶠ[𝓝 p]
        fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const hηc).mem_nhds hhi] with z hz
      rw [zspChi_eq_zero_ZSP35 (Or.inr (le_of_lt hz)), zero_mul]
    exact contMDiffAt_const.congr_of_eventuallyEq hev
  push Not at hlo hhi
  have hpO : p ∈ O' := hO'sub ⟨by linarith, by linarith⟩
  have hη := hO'sm.contMDiffAt (hO'o.mem_nhds hpO)
  have hq : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (fun z => zspQCLM_ZSP35 L Z k (f z)) p :=
    ((zspQCLM_ZSP35 L Z k).contDiff.contMDiff.comp hf) p
  exact (contDiff_zspChi_ZSP35.contMDiff.contMDiffAt.comp p hη).mul
    ((hq.add contMDiffAt_const).sub hη)

/-- **ZSP02's actual zero domain** (ZD): `Z_k = B(c_k, .35R_k) ∪ f⁻¹{v_k ≥ .9R_k, u_k ≤ .4v_k}`
(`u_k/v_k ≤ .4` written as `u_k ≤ .4v_k` on `v_k ≥ .9R_k > 0`). -/
def zspDomain_ZSP35 (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (k : Z.finite_centres.toFinset)
    (f : X → BlockSpace (fun _ : CGPTag L Z => ℝ²)) : Set X :=
  ball (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center
      (35 / 100 * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) ∪
    {p | 9 / 10 * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius ≤
        (f p (.inr (.inr (.inr (.inl k))))).snd ∧
      ((f p (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 ≤
        2 / 5 * (f p (.inr (.inr (.inr (.inl k))))).snd}

/-- **ZSP02's face set** (ZF): `f⁻¹{v_k ≥ .9R_k, u_k = .4v_k}`. -/
def zspFace_ZSP35 (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (k : Z.finite_centres.toFinset)
    (f : X → BlockSpace (fun _ : CGPTag L Z => ℝ²)) : Set X :=
  {p | 9 / 10 * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius ≤
      (f p (.inr (.inr (.inr (.inl k))))).snd ∧
    ((f p (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 =
      2 / 5 * (f p (.inr (.inr (.inr (.inl k))))).snd}

/-- **The two ends of (ZH)** (B:6466–6472): with (ZE) (`δ₀ < 1/1000`) and `e < 1/40`, the sublevel
and level of `h₁ = ψ(η_k) + χ(η_k)(q − η_k)` at `.4` are exactly ZSP02's domain `Z_k` and its face
set (ZF). -/
theorem zsp_sublevel_eq_ZSP35
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (k : Z.finite_centres.toFinset)
    (f : X → BlockSpace (fun _ : CGPTag L Z => ℝ²)) {δ₀ : ℝ} (hδ₀ : δ₀ < 1 / 1000)
    (hZE : ∀ p, ‖f p (.inr (.inr (.inr (.inl k)))) -
        cgpGlobalMap L Z p (.inr (.inr (.inr (.inl k))))‖ <
      δ₀ * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) (he : e < 1 / 40) :
    {z | zspPsi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) +
        zspChi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
          (zspQCLM_ZSP35 L Z k (f z) + 2 / 5 -
            (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) ≤ 2 / 5} =
      zspDomain_ZSP35 L Z k f ∧
    {z | zspPsi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) +
        zspChi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
          (zspQCLM_ZSP35 L Z k (f z) + 2 / 5 -
            (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) = 2 / 5} =
      zspFace_ZSP35 L Z k f := by
  have hR := (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  obtain ⟨-, hcl, -, -, hone⟩ := zsp_radial_facts_ZSP35 Z k
  have hrad := zsp02_original_radial L Z k f hδ₀ hZE
  have hann := zsp02_original_annulus L Z k f hδ₀ hZE
  have h45 : (4 / 10 : ℝ) = 2 / 5 := by norm_num
  -- pointwise facts
  have hq : ∀ z, zspQCLM_ZSP35 L Z k (f z) + 2 / 5 - 2 / 5 =
      ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ *
        (((f z (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 -
          2 / 5 * (f z (.inr (.inr (.inr (.inl k))))).snd) := fun z => by
    rw [add_sub_cancel_right, zspQCLM_apply_ZSP35]
  have hqle : ∀ z, zspQCLM_ZSP35 L Z k (f z) + 2 / 5 ≤ 2 / 5 ↔
      ((f z (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 ≤
        2 / 5 * (f z (.inr (.inr (.inr (.inl k))))).snd := fun z => by
    rw [← sub_nonpos, hq z]
    constructor
    · intro h
      by_contra hc
      push Not at hc
      have : 0 < ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ *
          (((f z (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 -
            2 / 5 * (f z (.inr (.inr (.inr (.inl k))))).snd) :=
        mul_pos (inv_pos.mpr hR) (by linarith)
      linarith
    · intro h
      exact mul_nonpos_of_nonneg_of_nonpos (inv_pos.mpr hR).le (by linarith)
  have hqeq : ∀ z, zspQCLM_ZSP35 L Z k (f z) + 2 / 5 = 2 / 5 ↔
      ((f z (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 =
        2 / 5 * (f z (.inr (.inr (.inr (.inl k))))).snd := fun z => by
    rw [← sub_eq_zero, hq z, mul_eq_zero, sub_eq_zero]
    simp [hR.ne']
  have hvband : ∀ z, (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z ∈
      Icc (3 / 10 : ℝ) (4 / 5) →
        (1 - δ₀) * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius <
        (f z (.inr (.inr (.inr (.inl k))))).snd := fun z hb => by
    obtain ⟨-, hF2⟩ := cgpGlobalMap_zeroBlock_GAF2 L Z k z
    obtain ⟨-, hc2⟩ := abs_block_components_le_GAF2 (f z (.inr (.inr (.inr (.inl k)))) -
      cgpGlobalMap L Z z (.inr (.inr (.inr (.inl k)))))
    rw [WithLp.sub_snd, hF2, hone z hb, mul_one] at hc2
    have := (abs_lt.mp (hc2.trans_lt (hZE z))).1
    linarith
  have hball : ∀ z, z ∈ ball (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center
      (35 / 100 * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) ↔
      ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ *
        dist z (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center < 35 / 100 := fun z => by
    rw [mem_ball, inv_mul_lt_iff₀ hR]
    constructor <;> intro h <;> linarith
  -- the domain
  have hdom : ∀ z, zspPsi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) +
      zspChi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
        (zspQCLM_ZSP35 L Z k (f z) + 2 / 5 -
          (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) ≤ 2 / 5 ↔
      z ∈ zspDomain_ZSP35 L Z k f := by
    intro z
    have hd := abs_lt.mp (hcl z)
    obtain ⟨c0, c1⟩ := zspChi_mem_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z)
    rw [zspDomain_ZSP35, mem_union, hball z]
    simp only [mem_ofPred_eq]
    by_cases hA : (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z < 3 / 10
    · rw [zspPsi_eq_low_ZSP35 hA.le, zspChi_eq_zero_ZSP35 (Or.inl (by linarith)), zero_mul,
        add_zero]
      exact ⟨fun _ => Or.inl (by linarith), fun _ => by norm_num⟩
    by_cases hB : 1 / 2 < (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z
    · rw [zspPsi_eq_high_ZSP35 hB.le, zspChi_eq_zero_ZSP35 (Or.inr (by linarith)), zero_mul,
        add_zero]
      refine ⟨fun h => by norm_num at h, ?_⟩
      rintro (h | ⟨hv, hu⟩)
      · linarith
      · have := (hrad z hv).2.1 (by rw [h45]; exact hu)
        linarith
    push Not at hA hB
    by_cases hC : (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z < 381 / 1000
    · obtain ⟨-, hv, hu⟩ := hann z hA hC
      rw [h45] at hu
      refine ⟨fun _ => Or.inr ⟨by linarith, hu.le⟩, fun _ => ?_⟩
      have hqlt : zspQCLM_ZSP35 L Z k (f z) + 2 / 5 < 2 / 5 := by
        have := (hqle z).mpr hu.le
        rcases this.lt_or_eq with h | h
        · exact h
        · exact absurd ((hqeq z).mp h) hu.ne
      by_cases h31 : (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z < 31 / 100
      · rw [zspChi_eq_zero_ZSP35 (Or.inl (by linarith)), zero_mul, add_zero]
        exact zspPsi_le_iff_ZSP35.mpr (by linarith)
      · push Not at h31
        rw [zspPsi_eq_self_ZSP35 h31 (by linarith)]
        nlinarith
    push Not at hC
    have hv := hvband z ⟨hA, by linarith⟩
    have hclose := zsp_q_close_ZSP35 L Z k f hZE (p := z) ⟨hA, by linarith⟩
    have hnb : ¬ ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ *
        dist z (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center < 35 / 100 := by
      intro h
      linarith
    have hv9 : 9 / 10 * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius ≤
        (f z (.inr (.inr (.inr (.inl k))))).snd := by nlinarith
    rw [or_iff_right hnb, and_iff_right hv9, ← hqle z]
    by_cases hD : (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z ≤ 46 / 100
    · rw [zspPsi_eq_self_ZSP35 (by linarith) (by linarith), zspChi_eq_one_ZSP35 (by linarith) hD,
        one_mul, add_sub_cancel]
    · push Not at hD
      have hq4 : 2 / 5 < zspQCLM_ZSP35 L Z k (f z) + 2 / 5 := by
        have := (abs_lt.mp hclose).1
        linarith
      refine ⟨fun h => ?_, fun h => by linarith⟩
      by_cases h49 : (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z ≤ 49 / 100
      · rw [zspPsi_eq_self_ZSP35 (by linarith) h49] at h
        by_cases hχ : zspChi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) ≤
            1 / 2
        · nlinarith
        · push Not at hχ
          nlinarith
      · push Not at h49
        rw [zspChi_eq_zero_ZSP35 (Or.inr (by linarith)), zero_mul, add_zero,
          zspPsi_le_iff_ZSP35] at h
        linarith
  refine ⟨Set.ext hdom, Set.ext fun z => ?_⟩
  simp only [mem_ofPred_eq, zspFace_ZSP35]
  constructor
  · intro h
    have hloc := zsp_level_location_ZSP35
      (η := (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z)
      (q := zspQCLM_ZSP35 L Z k (f z) + 2 / 5) (τ := 1) ⟨zero_le_one, le_rfl⟩ (fun h1 h2 => by
        have := zsp_q_close_ZSP35 L Z k f hZE (p := z) ⟨by linarith, by linarith⟩
        linarith) (by rw [one_mul]; exact h)
    obtain ⟨hl1, hl2⟩ := abs_lt.mp hloc
    rw [zspPsi_eq_self_ZSP35 (by linarith) (by linarith), zspChi_eq_one_ZSP35 (by linarith)
      (by linarith), one_mul, add_sub_cancel] at h
    have hv := hvband z ⟨by linarith, by linarith⟩
    exact ⟨by nlinarith, (hqeq z).mp h⟩
  · rintro ⟨hv, hu⟩
    have hloc := (hrad z hv).2.2 (by rw [h45]; exact hu)
    obtain ⟨hl1, hl2⟩ := abs_lt.mp hloc
    rw [zspPsi_eq_self_ZSP35 (by linarith) (by linarith), zspChi_eq_one_ZSP35 (by linarith)
      (by linarith), one_mul, add_sub_cancel]
    exact (hqeq z).mpr hu

/-- **ZSP02, the kernel** (B:6374–6479) for a smooth map `f` carrying ZSP01's (ZE)
(`δ₀ < 1/1000`) and a derivative bound `‖df − d𝓔⁰‖ ≤ H√g` (`H < 1/100`), with LC29's `εr < 1/2`
and LC30's `e < 1/40`: the domain `Z_k` is compact; a diffeomorphism of the carrier (FC34b's
transport along (ZH)) carries `{η_k ≤ .4}` onto `Z_k` and `{η_k = .4}` onto the face set (ZF);
`∂Z_k` is exactly (ZF); `B̄(c_k, (.381 − e)R_k) ⊆ int Z_k` and `Z_k ⊆ B(c_k, (.402 + e)R_k)`; the
face lies in `|η_k − .4| < 1/500`. -/
theorem zsp02_kernel_ZSP35
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (k : Z.finite_centres.toFinset)
    (f : X → BlockSpace (fun _ : CGPTag L Z => ℝ²))
    (hf : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag L Z => ℝ²)) ∞ f)
    (hF : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag L Z => ℝ²)) ∞ (cgpGlobalMap L Z))
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1 / 1000)
    (hZE : ∀ p, ‖f p (.inr (.inr (.inr (.inl k)))) -
        cgpGlobalMap L Z p (.inr (.inr (.inr (.inl k))))‖ <
      δ₀ * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)
    {Hd : ℝ} (hHd : Hd < 1 / 100) (hder : ∀ p (W : TangentSpace 𝓘(ℝ, E3) p),
      ‖mvfderiv 𝓘(ℝ, E3) f p W - mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap L Z) p W‖ ≤
        Hd * Real.sqrt (g.inner p W W))
    (hεr : εr < 1 / 2) (he : e < 1 / 40) :
    IsCompact (zspDomain_ZSP35 L Z k f) ∧
    (∃ Ψ : X ≃ₘ⟮𝓘(ℝ, E3), 𝓘(ℝ, E3)⟯ X,
      Ψ '' {z | (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z ≤ 2 / 5} =
        zspDomain_ZSP35 L Z k f ∧
      Ψ '' {z | (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z = 2 / 5} =
        zspFace_ZSP35 L Z k f) ∧
    frontier (zspDomain_ZSP35 L Z k f) = zspFace_ZSP35 L Z k f ∧
    closedBall (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center
        ((381 / 1000 - e) * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) ⊆
      interior (zspDomain_ZSP35 L Z k f) ∧
    zspDomain_ZSP35 L Z k f ⊆ ball (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center
        ((402 / 1000 + e) * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) ∧
    ∀ z ∈ zspFace_ZSP35 L Z k f,
      |(Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z - 2 / 5| < 1 / 500 := by
  have hR := (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  obtain ⟨hηc, hcl, -, -, -⟩ := zsp_radial_facts_ZSP35 Z k
  obtain ⟨hsub, hlev⟩ := zsp_sublevel_eq_ZSP35 L Z k f hδ₀ hZE he
  have hrad := zsp02_original_radial L Z k f hδ₀ hZE
  have hann := zsp02_original_annulus L Z k f hδ₀ hZE
  have h45 : (4 / 10 : ℝ) = 2 / 5 := by norm_num
  have hh0 := contMDiff_zspH0_ZSP35 Z k
  have hk := contMDiff_zspK_ZSP35 L Z k f hf
  have hh1c : Continuous fun z =>
      zspPsi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) +
        zspChi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
          (zspQCLM_ZSP35 L Z k (f z) + 2 / 5 -
            (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) :=
    (hh0.add hk).continuous
  have hclosed : IsClosed (zspDomain_ZSP35 L Z k f) := by
    rw [← hsub]
    exact isClosed_le hh1c continuous_const
  have he0 : 0 < e := lt_of_le_of_lt (abs_nonneg _) (hcl (Z.zero k.1
    ((Set.Finite.mem_toFinset _).mp k.2)).center)
  refine ⟨hclosed.isCompact, ?_, ?_, ?_, ?_, fun z hz => ?_⟩
  rotate_left 4
  · have h := (hrad z hz.1).2.2 (by rw [h45]; exact hz.2)
    obtain ⟨h1, h2⟩ := abs_lt.mp h
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  · -- FC34b along (ZH)
    obtain ⟨Ψ, h1, h2⟩ :=
      DifferentialGeometry.Topology.Ehresmann.exists_diffeomorph_image_sublevel_of_affine_family
      hh0 hk (2 / 5) fun τ hτ p hp =>
        zsp_level_transversal_ZSP35 L Z k f hf hF hδ₀ hZE hHd hder hεr hτ hp
    refine ⟨Ψ, ?_, ?_⟩
    · rw [← hsub, ← h1]
      congr 1
      ext z
      exact zspPsi_le_iff_ZSP35.symm
    · rw [← hlev, ← h2]
      congr 1
      ext z
      exact zspPsi_eq_iff_ZSP35.symm
  · -- the boundary is the regular level
    rw [← hsub, ← hlev]
    refine frontier_sublevel_eq_level_of_regular (I := 𝓘(ℝ, E3)) hh1c fun x hx => ⟨?_, ?_⟩
    · exact ((hh0.add hk) x).of_le (by norm_num)
    · have hs := zsp_level_transversal_ZSP35 L Z k f hf hF hδ₀ hZE hHd hder hεr (τ := 1)
        ⟨zero_le_one, le_rfl⟩ (p := x) (by rw [one_mul]; exact hx)
      have heq : (fun z =>
          zspPsi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) +
            1 * (zspChi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
              (zspQCLM_ZSP35 L Z k (f z) + 2 / 5 -
                (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z))) = fun z =>
          zspPsi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) +
            zspChi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
              (zspQCLM_ZSP35 L Z k (f z) + 2 / 5 -
                (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) := by
        funext z
        rw [one_mul]
      rw [heq] at hs
      intro h0
      obtain ⟨v, hv⟩ := hs 1
      rw [h0] at hv
      exact absurd (show (0 : ℝ) = 1 from hv) zero_ne_one
  · -- the closed ball inside the interior
    have hUo : IsOpen (ball (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center
        (35 / 100 * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) ∪
        {z | 3 / 10 < (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z ∧
          (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z < 381 / 1000}) :=
      isOpen_ball.union ((isOpen_lt continuous_const hηc).inter (isOpen_lt hηc continuous_const))
    refine Subset.trans ?_ (interior_maximal ?_ hUo)
    · intro z hz
      rw [mem_closedBall] at hz
      by_cases hb : dist z (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center <
          35 / 100 * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius
      · exact Or.inl hb
      · push Not at hb
        have hd := abs_lt.mp (hcl z)
        have h1 : 35 / 100 ≤ ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ *
            dist z (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center := by
          rw [le_inv_mul_iff₀ hR]
          linarith
        have h2 : ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ *
            dist z (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center ≤ 381 / 1000 - e := by
          rw [inv_mul_le_iff₀ hR]
          linarith
        exact Or.inr ⟨by linarith, by linarith⟩
    · rintro z (hz | ⟨h1, h2⟩)
      · exact Or.inl hz
      · obtain ⟨-, hv, hu⟩ := hann z h1.le h2
        rw [h45] at hu
        exact Or.inr ⟨by linarith, hu.le⟩
  · -- the domain inside the ball
    rintro z (hz | ⟨hv, hu⟩)
    · refine ball_subset_ball ?_ hz
      nlinarith
    · have hη := (hrad z hv).2.1 (by rw [h45]; exact hu)
      have hd := abs_lt.mp (hcl z)
      rw [mem_ball]
      have h3 : ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ *
          dist z (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center < 402 / 1000 + e := by
        linarith
      rw [inv_mul_lt_iff₀ hR] at h3
      linarith

/-- On the band (cutoff one), (ZE) keeps the adjusted marker above `(1 − δ₀)R_k`. -/
theorem zsp_band_marker_ZSP35
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (k : Z.finite_centres.toFinset)
    (f : X → BlockSpace (fun _ : CGPTag L Z => ℝ²)) {δ₀ : ℝ}
    (hZE : ∀ p, ‖f p (.inr (.inr (.inr (.inl k)))) -
        cgpGlobalMap L Z p (.inr (.inr (.inr (.inl k))))‖ <
      δ₀ * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)
    {z : X} (hb : (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z ∈
      Icc (3 / 10 : ℝ) (4 / 5)) :
    (1 - δ₀) * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius <
      (f z (.inr (.inr (.inr (.inl k))))).snd := by
  obtain ⟨-, -, -, -, hone⟩ := zsp_radial_facts_ZSP35 Z k
  obtain ⟨-, hF2⟩ := cgpGlobalMap_zeroBlock_GAF2 L Z k z
  obtain ⟨-, hc2⟩ := abs_block_components_le_GAF2 (f z (.inr (.inr (.inr (.inl k)))) -
    cgpGlobalMap L Z z (.inr (.inr (.inr (.inl k)))))
  rw [WithLp.sub_snd, hF2, hone z hb, mul_one] at hc2
  have := (abs_lt.mp (hc2.trans_lt (hZE z))).1
  linarith

/-- On the band `3/10 < η_k < 4/5`, the adjusted functional increases strictly along the
`R⁻²g`-gradient of `η_k`: `d(ℓ ∘ f)(∇η_k) > 0` (given `H < 1/100`, `εr < 1/2`). -/
theorem zsp_q_grad_pos_ZSP35
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (k : Z.finite_centres.toFinset)
    (f : X → BlockSpace (fun _ : CGPTag L Z => ℝ²))
    (hf : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag L Z => ℝ²)) ∞ f)
    (hF : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag L Z => ℝ²)) ∞ (cgpGlobalMap L Z))
    {Hd : ℝ} (hHd : Hd < 1 / 100) (hder : ∀ p (W : TangentSpace 𝓘(ℝ, E3) p),
      ‖mvfderiv 𝓘(ℝ, E3) f p W - mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap L Z) p W‖ ≤
        Hd * Real.sqrt (g.inner p W W))
    (hεr : εr < 1 / 2) {p : X} (hp : (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p ∈
      Ioo (3 / 10 : ℝ) (4 / 5)) :
    0 < mvfderiv 𝓘(ℝ, E3) (fun z => zspQCLM_ZSP35 L Z k (f z)) p
      (gradFun (scaleMetric (((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ ^ 2)
        (pow_pos (inv_pos.mpr (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos) 2) g)
        (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p) := by
  obtain ⟨-, -, -, hgrad, -⟩ := zsp_radial_facts_ZSP35 Z k
  set gR := scaleMetric (((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ ^ 2)
    (pow_pos (inv_pos.mpr (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos) 2) g
    with hgR
  set W := gradFun gR (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p with hW
  have hn := hgrad p ⟨by linarith [hp.1], by linarith [hp.2]⟩
  set n := Real.sqrt (gR.inner p W W) with hn_def
  have hn0 : 0 < n := by linarith
  have hin : gR.inner p W W = n ^ 2 := by
    rw [hn_def, Real.sq_sqrt]
    exact le_of_lt (Real.sqrt_pos.mp hn0)
  have hdη : mvfderiv 𝓘(ℝ, E3) (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p W =
      n ^ 2 := by
    rw [← hin]
    exact (inner_gradFun gR _ p W).symm
  have hdq := zsp_q_deriv_ZSP35 L Z k f hf hF hder hp W
  have hsq : Real.sqrt (((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ ^ 2 *
      g.inner p W W) = n := rfl
  rw [hsq, hdη] at hdq
  obtain ⟨hd1, -⟩ := abs_le.mp hdq
  nlinarith

/-- **ZSP02's defining function** (B:6392–6393): on the open neighbourhood `{.39 < η_k < .41}` of
the face, `v_k > .99R_k`, `r_k = u_k/v_k − .4` is smooth and `Z_k` is `{r_k ≤ 0}` there; at every
face point the differential of `r_k` is nonzero. -/
theorem zsp_defining_ZSP35
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (k : Z.finite_centres.toFinset)
    (f : X → BlockSpace (fun _ : CGPTag L Z => ℝ²))
    (hf : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag L Z => ℝ²)) ∞ f)
    (hF : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag L Z => ℝ²)) ∞ (cgpGlobalMap L Z))
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1 / 1000)
    (hZE : ∀ p, ‖f p (.inr (.inr (.inr (.inl k)))) -
        cgpGlobalMap L Z p (.inr (.inr (.inr (.inl k))))‖ <
      δ₀ * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)
    {Hd : ℝ} (hHd : Hd < 1 / 100) (hder : ∀ p (W : TangentSpace 𝓘(ℝ, E3) p),
      ‖mvfderiv 𝓘(ℝ, E3) f p W - mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap L Z) p W‖ ≤
        Hd * Real.sqrt (g.inner p W W))
    (hεr : εr < 1 / 2) (he : e < 1 / 40) :
    ∃ O : Set X, IsOpen O ∧ zspFace_ZSP35 L Z k f ⊆ O ∧
      (∀ z ∈ O, 99 / 100 * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius <
          (f z (.inr (.inr (.inr (.inl k))))).snd ∧
        ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (fun y => ((f y (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
          (f y (.inr (.inr (.inr (.inl k))))).snd - 2 / 5) z ∧
        (z ∈ zspDomain_ZSP35 L Z k f ↔ ((f z (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
          (f z (.inr (.inr (.inr (.inl k))))).snd - 2 / 5 ≤ 0)) ∧
      ∀ z ∈ zspFace_ZSP35 L Z k f, mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
        (fun y => ((f y (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
          (f y (.inr (.inr (.inr (.inl k))))).snd - 2 / 5) z ≠ 0 := by
  have hR := (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  obtain ⟨hηc, hcl, -, -, -⟩ := zsp_radial_facts_ZSP35 Z k
  have hrad := zsp02_original_radial L Z k f hδ₀ hZE
  have h45 : (4 / 10 : ℝ) = 2 / 5 := by norm_num
  have hu : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞
      (fun y => ((f y (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0) :=
    ((EuclideanSpace.proj (0 : Fin 2)).comp (blockVectorCLM
      (V := fun _ : CGPTag L Z => ℝ²) (.inr (.inr (.inr (.inl k)))))).contDiff.comp_contMDiff hf
  have hv : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (fun y => (f y (.inr (.inr (.inr (.inl k))))).snd) :=
    (blockMarkerCLM (V := fun _ : CGPTag L Z => ℝ²)
      (.inr (.inr (.inr (.inl k))))).contDiff.comp_contMDiff hf
  have hface : ∀ z ∈ zspFace_ZSP35 L Z k f,
      |(Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z - 4 / 10| < 2 / 1000 :=
    fun z hz => (hrad z hz.1).2.2 (by rw [h45]; exact hz.2)
  refine ⟨{z | 39 / 100 < (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z ∧
      (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z < 41 / 100},
    (isOpen_lt continuous_const hηc).inter (isOpen_lt hηc continuous_const), fun z hz => ?_,
    fun z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨h1, h2⟩ := abs_lt.mp (hface z hz)
    exact ⟨by linarith, by linarith⟩
  · have hvz := zsp_band_marker_ZSP35 L Z k f hZE (z := z) ⟨by linarith [hz.1], by linarith [hz.2]⟩
    have hv0 : 0 < (f z (.inr (.inr (.inr (.inl k))))).snd := by nlinarith
    refine ⟨by nlinarith, ((hu z).div₀ (hv z) hv0.ne').sub contMDiffAt_const, ?_⟩
    have hd := abs_lt.mp (hcl z)
    have hnb : z ∉ ball (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center
        (35 / 100 * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) := by
      rw [mem_ball, not_lt]
      have h3 : 35 / 100 ≤ ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ *
          dist z (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center := by
        linarith [hz.1]
      rw [le_inv_mul_iff₀ hR] at h3
      linarith
    rw [zspDomain_ZSP35, mem_union, or_iff_right hnb, mem_ofPred_eq, sub_nonpos,
      div_le_iff₀ hv0]
    exact ⟨fun h => h.2, fun h => ⟨by nlinarith, h⟩⟩
  · -- the defining function has nonzero differential on the face
    obtain ⟨h1, h2⟩ := abs_lt.mp (hface z hz)
    have hvz := zsp_band_marker_ZSP35 L Z k f hZE (z := z) ⟨by linarith, by linarith⟩
    have hv0 : 0 < (f z (.inr (.inr (.inr (.inl k))))).snd := by nlinarith
    have hpos := zsp_q_grad_pos_ZSP35 L Z k f hf hF hHd hder hεr (p := z)
      ⟨by linarith, by linarith⟩
    have hℓd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun y => zspQCLM_ZSP35 L Z k (f y)) z :=
      (((zspQCLM_ZSP35 L Z k).contDiff.contMDiff.comp hf) z).mdifferentiableAt (by simp)
    have hRv : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun y =>
        (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius /
          (f y (.inr (.inr (.inr (.inl k))))).snd) z :=
      ((contMDiffAt_const.div₀ (hv z) hv0.ne').mdifferentiableAt (by simp))
    have hev : (fun y => ((f y (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
          (f y (.inr (.inr (.inr (.inl k))))).snd - 2 / 5) =ᶠ[𝓝 z]
        (fun y => zspQCLM_ZSP35 L Z k (f y)) * fun y =>
          (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius /
            (f y (.inr (.inr (.inr (.inl k))))).snd := by
      filter_upwards [(isOpen_lt continuous_const (hv.continuous)).mem_nhds hv0] with y hy
      simp only [Pi.mul_apply, zspQCLM_apply_ZSP35]
      field_simp
    have hℓz : zspQCLM_ZSP35 L Z k (f z) = 0 := by
      rw [zspQCLM_apply_ZSP35, hz.2, sub_self, mul_zero]
    have hval := mvfderiv_mul hℓd hRv
    rw [hℓz, zero_smul, zero_add] at hval
    intro h0
    have h00 : mvfderiv 𝓘(ℝ, E3) (fun y => ((f y (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
        (f y (.inr (.inr (.inr (.inl k))))).snd - 2 / 5) z
          (gradFun (scaleMetric (((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ ^ 2)
            (pow_pos (inv_pos.mpr (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos) 2)
              g) (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) = 0 := by
      unfold mvfderiv
      rw [h0]
      rfl
    rw [mvfderiv_congr_EDPE hev, hval] at h00
    have hRv0 : 0 < (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius /
        (f z (.inr (.inr (.inr (.inl k))))).snd := div_pos hR hv0
    have : 0 < ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius /
        (f z (.inr (.inr (.inr (.inl k))))).snd) * mvfderiv 𝓘(ℝ, E3)
          (fun y => zspQCLM_ZSP35 L Z k (f y)) z
          (gradFun (scaleMetric (((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ ^ 2)
            (pow_pos (inv_pos.mpr (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos) 2)
              g) (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) :=
      mul_pos hRv0 hpos
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul] at h00
    linarith

end DifferentialGeometry.Geometry.Collapse
