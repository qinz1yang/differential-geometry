import DifferentialGeometry.Geometry.Fibration.ActualStagePerturbedRows
import DifferentialGeometry.Geometry.Fibration.ActualStagePlaneTypes

/-!
# CFS10 on the native output: the global buffered graph certificate and its consequences

Blueprint `master207B.tex`, CFS10 (`cor:fibration-full-tube-from-buffered-graphs`, B:2353–2390).
The "single smooth embedded `k`-manifold `W`" is the zero set `W = O.Z` of a native output
`O : Cfs15StageOutput` (CFS13–CFS14's construction; on the actual stage clouds `O` comes from
`cfs14_row_CFSA` / `cfs15_row_CFSA` or the slots of `Gaf02Chain`). With `a = ε/3`, `R = r_x`, `m = K`:

* the row's hypotheses hold for this `W`: (GB) `‖D^q g_x‖ ≤ a r_x^{1−q}` (`q ≤ K + 1`) for the graph
  over `B_{L_x}(0, 4r_x)`, `G_x ⊆ W` and (IS) `W ∩ B(x, 3r_x) = G_x ∩ B(x, 3r_x)` (restriction of CFS13's
  graph, as in CFS14's proof);
* its conclusions: `W ∩ N_r(S)` properly embedded in `N_r(S)`; one smooth nearest-point submersion
  `P : N_r(S) → W`; CFS09's scaled estimates relative to `P_{A_x}` on every `B(x, r_x)` (`|P − π| ≤ 3aR`,
  `‖DP − π‖ ≤ 8a`, `‖D^q(P − π)‖ ≤ c_q a R^{1−q}` with `c_q = 1`); and on `W ∩ B(x, r_x)` the normal
  projectors are within `2a` of `P_x` (new: the tangent space of `W` is the graph of `Dg_x`).

* `norm_starProjection_sub_le_two_mul_CFSA`: two one-sided `a`-bounds give `‖π_R − π_L‖ ≤ 2a`.
* `Cfs15StageOutput.graph_tangent_CFSA`: `u + Dg_x(t)u ∈ T_wW` at a graph point `w ∈ Ω`.
* `Cfs15StageOutput.cfs10_normal_CFSA`: the `2a` normal clause.
* `Cfs15StageOutput.cfs10_row_CFSA`: the whole row (certificate + conclusions) on `W = O.Z`.
* Consumer `cfs10_firstStagePlanes_normal_CFSA`: on the actual first stage cloud with the enhanced
  plane witness (dimension from `A.dimension`), the `2a` normal clause for any native output.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter DifferentialGeometry.Analysis
open scoped ContDiff Manifold Topology InnerProductSpace

namespace GC.MetricGeometry

section Gap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **Two one-sided bounds give the projector gap `2a`** (the two-term identity of CFS03 / CFS10):
`π_R − π_L = (I − π_L)π_R − π_L(I − π_R)`. -/
theorem norm_starProjection_sub_le_two_mul_CFSA (L R : Submodule ℝ H) [L.HasOrthogonalProjection]
    [R.HasOrthogonalProjection] {a : ℝ} (ha : 0 ≤ a)
    (hR : ∀ v ∈ R, ‖v - L.starProjection v‖ ≤ a * ‖v‖)
    (hL : ∀ u ∈ L, ‖u - R.starProjection u‖ ≤ a * ‖u‖) :
    ‖R.starProjection - L.starProjection‖ ≤ 2 * a := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
  have hsplit : (R.starProjection - L.starProjection) z =
      (R.starProjection z - L.starProjection (R.starProjection z)) -
        L.starProjection (z - R.starProjection z) := by
    rw [sub_apply, map_sub]
    abel
  have h1 : ‖R.starProjection z - L.starProjection (R.starProjection z)‖ ≤ a * ‖z‖ :=
    (hR _ (R.starProjection_apply_mem z)).trans
      (mul_le_mul_of_nonneg_left (R.norm_starProjection_apply_le z) ha)
  have h2 : ‖L.starProjection (z - R.starProjection z)‖ ≤ a * ‖z‖ := by
    set w := L.starProjection (z - R.starProjection z) with hwdef
    have hw : w ∈ L := L.starProjection_apply_mem _
    have hinner : ‖w‖ ^ 2 = ⟪w - R.starProjection w, z⟫_ℝ := by
      rw [← real_inner_self_eq_norm_sq]
      calc ⟪w, w⟫_ℝ = ⟪w, L.starProjection (z - R.starProjection z)⟫_ℝ := by rw [← hwdef]
        _ = ⟪L.starProjection w, z - R.starProjection z⟫_ℝ :=
          (L.inner_starProjection_left_eq_right w _).symm
        _ = ⟪w, z⟫_ℝ - ⟪w, R.starProjection z⟫_ℝ := by
          rw [L.starProjection_eq_self_iff.mpr hw, inner_sub_right]
        _ = ⟪w, z⟫_ℝ - ⟪R.starProjection w, z⟫_ℝ := by
          rw [R.inner_starProjection_left_eq_right w z]
        _ = ⟪w - R.starProjection w, z⟫_ℝ := by rw [inner_sub_left]
    have hle : ‖w‖ ^ 2 ≤ a * ‖w‖ * ‖z‖ := by
      rw [hinner]
      calc ⟪w - R.starProjection w, z⟫_ℝ ≤ ‖w - R.starProjection w‖ * ‖z‖ :=
            real_inner_le_norm _ _
        _ ≤ a * ‖w‖ * ‖z‖ := mul_le_mul_of_nonneg_right (hL w hw) (norm_nonneg z)
    rcases (norm_nonneg w).eq_or_lt with h0 | hpos
    · rw [← h0]
      positivity
    · have : ‖w‖ * ‖w‖ ≤ (a * ‖z‖) * ‖w‖ := by nlinarith
      exact le_of_mul_le_mul_right this hpos
  rw [hsplit]
  calc _ ≤ ‖R.starProjection z - L.starProjection (R.starProjection z)‖ +
        ‖L.starProjection (z - R.starProjection z)‖ := norm_sub_le _ _
    _ ≤ a * ‖z‖ + a * ‖z‖ := add_le_add h1 h2
    _ = 2 * a * ‖z‖ := by ring

/-- For `t ∈ L` and `n ∈ Lᗮ`, `‖t‖ ≤ ‖t + n‖`. -/
theorem norm_le_norm_add_orthogonal_CFSA (L : Submodule ℝ H) {t n : H} (ht : t ∈ L)
    (hn : n ∈ Lᗮ) : ‖t‖ ≤ ‖t + n‖ := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_real (Submodule.inner_right_of_mem_orthogonal ht hn)
  have h0 : ‖t‖ * ‖t‖ ≤ ‖t + n‖ * ‖t + n‖ := by nlinarith [mul_self_nonneg ‖n‖]
  exact (mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)).mpr h0

end Gap

section Output

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  {k K : ℕ} {ε cw : ℝ} {S T : Set H} {r : H → ℝ} {P : H → Submodule ℝ H}

namespace Cfs15StageOutput

/-- **The tangent space of `W` contains the graph of `Dg_x`.** At a graph point
`w = x + (t₀, g_x t₀) ∈ Ω` (`|t₀| < 4ε⁻¹r_x`), every `u + Dg_x(t₀)u` (`u ∈ L_x`) lies in the range of
`Da(w)`: `a ∘ γ = γ` near `t₀` for `γ(t) = x + (t, g_x t)` (retraction on `W ∩ Ω`). -/
theorem graph_tangent_CFSA (O : Cfs15StageOutput k K ε cw S T r P) (x : S) {t₀ : P x}
    (ht₀ : t₀ ∈ ball (0 : P x) (4 * ε⁻¹ * r x))
    (hw : (x : H) + orthogonalCoordinateSum (P x) (t₀, O.g x t₀) ∈ cfs15Omega_C15 S r)
    (u : P x) :
    (u : H) + (fderiv ℝ (O.g x) t₀ u : H) ∈ LinearMap.range
      (fderiv ℝ O.ambient ((x : H) + orthogonalCoordinateSum (P x) (t₀, O.g x t₀))).toLinearMap := by
  let γ : P x → H := fun t => (x : H) + orthogonalCoordinateSum (P x) (t, O.g x t)
  have hgd : DifferentiableAt ℝ (O.g x) t₀ :=
    ((O.graph_smooth x).contDiffAt (isOpen_ball.mem_nhds ht₀)).differentiableAt (by simp)
  let Dγ : P x →L[ℝ] H := (orthogonalCoordinateSum (P x)).comp
    ((ContinuousLinearMap.id ℝ (P x)).prod (fderiv ℝ (O.g x) t₀))
  have hγd : HasFDerivAt γ Dγ t₀ :=
    (((orthogonalCoordinateSum (P x)).hasFDerivAt.comp t₀
      ((hasFDerivAt_id t₀).prodMk hgd.hasFDerivAt)).const_add (x : H))
  have hev : (fun t => O.ambient (γ t)) =ᶠ[𝓝 t₀] γ := by
    have h1 : ∀ᶠ t in 𝓝 t₀, γ t ∈ cfs15Omega_C15 S r :=
      hγd.continuousAt.preimage_mem_nhds ((cfs15Omega_C15 S r).isOpen.mem_nhds hw)
    have h2 : ∀ᶠ t in 𝓝 t₀, t ∈ ball (0 : P x) (4 * ε⁻¹ * r x) := isOpen_ball.mem_nhds ht₀
    filter_upwards [h1, h2] with t hΩt hbt
    have hZ : γ t ∈ O.Z := (O.graph_mem x t hbt).2
    rw [O.ambient_eq (γ t) hΩt, O.retraction ⟨γ t, hZ⟩ hΩt]
  have hDa : DifferentiableAt ℝ O.ambient (γ t₀) := (O.ambient_contDiffAt hw).differentiableAt (by simp)
  have huniq := (hDa.hasFDerivAt.comp t₀ hγd).unique (hγd.congr_of_eventuallyEq hev)
  refine ⟨Dγ u, ?_⟩
  have h := congrArg (fun A : P x →L[ℝ] H => A u) huniq
  simp only [ContinuousLinearMap.comp_apply] at h
  change (fderiv ℝ O.ambient (γ t₀)) (Dγ u) = _
  rw [h]
  rfl

/-- **CFS10's normal clause on `W = O.Z`**: for planes of dimension `k`, on `W ∩ B(x, r_x)` the
normal projectors are within `2a = 2ε/3` of `P_x` (the tangent space IS the graph of `Dg_x`,
`‖Dg_x‖ ≤ a`, and the two-term identity). -/
theorem cfs10_normal_CFSA (O : Cfs15StageOutput k K ε cw S T r P)
    (hdim : ∀ x ∈ S, Module.finrank ℝ (P x) = k) (x : S) (z : O.Z)
    (hz : (z : H) ∈ ball (x : H) (r x)) :
    let _ := O.cs
    ‖actualZeroSetNormalProjector k O.Z z - (P x)ᗮ.starProjection‖ ≤ 2 * (ε / 3) := by
  let _ := O.cs
  have hrx := O.radius_pos x x.2
  have hε := O.eps_pos
  have hε1 : ε ≤ 1 := O.eps_le.trans (by norm_num)
  have hinv : 1 ≤ ε⁻¹ := one_le_inv₀ hε |>.mpr hε1
  have hz3 : (z : H) ∈ O.Z ∩ ball (x : H) (3 * ε⁻¹ * r x) :=
    ⟨z.2, ball_subset_ball (by nlinarith) hz⟩
  rw [O.graph_eq x] at hz3
  obtain ⟨⟨t₀, ht₀, hzt⟩, -⟩ := hz3
  have hzΩ : (z : H) ∈ cfs15Omega_C15 S r := mem_cfs15Omega_of_mem_C15 x.2 hz
  have hpz : O.p ⟨z, hzΩ⟩ = z := O.retraction z hzΩ
  obtain ⟨hTS, hfin⟩ := O.range_fderiv_ambient_CFSA hzΩ
  rw [hpz] at hTS hfin
  have hDg : ‖fderiv ℝ (O.g x) t₀‖ ≤ ε / 3 := by
    have h := O.graph_jets x t₀ ht₀ 1 (by omega)
    rw [norm_iteratedFDeriv_one] at h
    have he : ε / 3 * r x * (r x)⁻¹ ^ 1 = ε / 3 := by field_simp
    linarith
  have hmem : ∀ u : P x, (u : H) + (fderiv ℝ (O.g x) t₀ u : H) ∈
      actualZeroSetTangentSpace k O.Z z := by
    intro u
    have h := O.graph_tangent_CFSA x ht₀ (hzt ▸ hzΩ) u
    rw [← hzt, hTS] at h
    exact h
  have ha : 0 ≤ ε / 3 := by positivity
  -- one-sided bound from `L_x`
  have hL : ∀ u ∈ P x, ‖u - (actualZeroSetTangentSpace k O.Z z).starProjection u‖ ≤
      ε / 3 * ‖u‖ := by
    intro u hu
    calc ‖u - (actualZeroSetTangentSpace k O.Z z).starProjection u‖ =
          Metric.infDist u (actualZeroSetTangentSpace k O.Z z : Set H) := by
          simpa only [dist_eq_norm] using
            (actualZeroSetTangentSpace k O.Z z).dist_starProjection_eq_infDist u
      _ ≤ dist u (u + (fderiv ℝ (O.g x) t₀ ⟨u, hu⟩ : H)) :=
          Metric.infDist_le_dist_of_mem (hmem ⟨u, hu⟩)
      _ = ‖fderiv ℝ (O.g x) t₀ ⟨u, hu⟩‖ := by
          rw [dist_eq_norm, sub_add_cancel_left, norm_neg]
          rfl
      _ ≤ ‖fderiv ℝ (O.g x) t₀‖ * ‖(⟨u, hu⟩ : P x)‖ := (fderiv ℝ (O.g x) t₀).le_opNorm _
      _ ≤ ε / 3 * ‖u‖ := mul_le_mul_of_nonneg_right hDg (norm_nonneg _)
  -- the tangent space is the graph of `Dg`
  let Gr : P x →ₗ[ℝ] H := (P x).subtype + (P x)ᗮ.subtype ∘ₗ (fderiv ℝ (O.g x) t₀).toLinearMap
  have hGr : ∀ u : P x, Gr u = (u : H) + (fderiv ℝ (O.g x) t₀ u : H) := fun _ => rfl
  have hGrinj : Function.Injective Gr := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have h0 : (P x).starProjection (Gr u) = (u : H) := by
      rw [hGr, map_add, (P x).starProjection_eq_self_iff.mpr u.2,
        (Submodule.starProjection_apply_eq_zero_iff (P x)).mpr (fderiv ℝ (O.g x) t₀ u).2, add_zero]
    rw [hu, map_zero] at h0
    exact Subtype.ext h0.symm
  have hle : LinearMap.range Gr ≤ actualZeroSetTangentSpace k O.Z z := by
    rintro _ ⟨u, rfl⟩
    exact hmem u
  have hGreq : LinearMap.range Gr = actualZeroSetTangentSpace k O.Z z :=
    Submodule.eq_of_le_of_finrank_le hle
      (by rw [hfin, LinearMap.finrank_range_of_inj hGrinj, hdim x x.2])
  -- one-sided bound from the tangent space
  have hR : ∀ v ∈ actualZeroSetTangentSpace k O.Z z, ‖v - (P x).starProjection v‖ ≤
      ε / 3 * ‖v‖ := by
    intro v hv
    rw [← hGreq] at hv
    obtain ⟨u, rfl⟩ := hv
    have hpr : (P x).starProjection (Gr u) = (u : H) := by
      rw [hGr, map_add, (P x).starProjection_eq_self_iff.mpr u.2,
        (Submodule.starProjection_apply_eq_zero_iff (P x)).mpr (fderiv ℝ (O.g x) t₀ u).2, add_zero]
    rw [hpr, hGr, add_sub_cancel_left]
    calc ‖(fderiv ℝ (O.g x) t₀ u : H)‖ = ‖fderiv ℝ (O.g x) t₀ u‖ := rfl
      _ ≤ ‖fderiv ℝ (O.g x) t₀‖ * ‖u‖ := (fderiv ℝ (O.g x) t₀).le_opNorm _
      _ ≤ ε / 3 * ‖(u : H)‖ := mul_le_mul_of_nonneg_right hDg (norm_nonneg _)
      _ ≤ ε / 3 * ‖(u : H) + (fderiv ℝ (O.g x) t₀ u : H)‖ :=
          mul_le_mul_of_nonneg_left (norm_le_norm_add_orthogonal_CFSA (P x) u.2
            (fderiv ℝ (O.g x) t₀ u).2) ha
  have hgap := norm_starProjection_sub_le_two_mul_CFSA (P x) (actualZeroSetTangentSpace k O.Z z)
    ha hR hL
  change ‖(actualZeroSetTangentSpace k O.Z z)ᗮ.starProjection - (P x)ᗮ.starProjection‖ ≤ _
  rw [Submodule.starProjection_orthogonal, Submodule.starProjection_orthogonal]
  have heq : (ContinuousLinearMap.id ℝ H - (actualZeroSetTangentSpace k O.Z z).starProjection) -
      (ContinuousLinearMap.id ℝ H - (P x).starProjection) =
      -((actualZeroSetTangentSpace k O.Z z).starProjection - (P x).starProjection) := by abel
  rw [heq, norm_neg]
  exact hgap

/-- **CFS10 on `W = O.Z`** (`a = ε/3`, `R = r_x`, `m = K`; planes of dimension `k`). The row's
hypotheses hold for this single `W`: the graph `g_x` over `B_{L_x}(0, 4r_x)` is smooth with (GB)
`‖D^q g_x‖ ≤ a r_x^{1−q}` (`q ≤ K + 1`), `G_x ⊆ W`, and (IS) `W ∩ B(x, 3r_x) = G_x ∩ B(x, 3r_x)`.
Its conclusions: `W ∩ N_r(S)` is properly embedded in `N_r(S)`; `p : N_r(S) → W` is ONE smooth
nearest-point submersion (unique nearest points in the whole `W`); on every `B(x, r_x)`, with
`P = ι ∘ p = O.ambient`, CFS09's estimates `|P − P_{A_x}| ≤ 3aR`, `‖DP − π‖ ≤ 8a` and
`‖D^q(P − P_{A_x})‖ ≤ c_q a R^{1−q}` (`2 ≤ q ≤ K`, `c_q = 1`); and on `W ∩ B(x, r_x)` the normal
projectors are within `2a` of `P_x`. -/
theorem cfs10_row_CFSA (O : Cfs15StageOutput k K ε cw S T r P)
    (hdim : ∀ x ∈ S, Module.finrank ℝ (P x) = k) :
    (∀ x : S,
      ContDiffOn ℝ ∞ (O.g x) (ball 0 (4 * r x)) ∧
      (∀ q ≤ K + 1, ∀ t ∈ ball (0 : P x) (4 * r x),
        ‖iteratedFDeriv ℝ q (O.g x) t‖ ≤ (ε / 3) * r x * ((r x)⁻¹) ^ q) ∧
      (∀ t ∈ ball (0 : P x) (4 * r x), (x : H) + orthogonalCoordinateSum (P x) (t, O.g x t) ∈ O.Z) ∧
      O.Z ∩ ball (x : H) (3 * r x) =
        {z : H | ∃ t ∈ ball (0 : P x) (4 * r x),
          z = (x : H) + orthogonalCoordinateSum (P x) (t, O.g x t)} ∩ ball (x : H) (3 * r x)) ∧
    IsProperMap (Subtype.val :
      {z : (⋃ x ∈ S, ball x (r x) : Set H) | (z : H) ∈ O.Z} → (⋃ x ∈ S, ball x (r x) : Set H)) ∧
    (let _ := O.cs
     _root_.Manifold.IsSubmersion 𝓘(ℝ, H) 𝓘(ℝ, Fin k → ℝ) ∞ O.p ∧
      (∀ z : cfs15Omega_C15 S r,
        IsMinOn (fun y => dist (z : H) y) O.Z (O.p z : H) ∧
          (∀ y ∈ O.Z, IsMinOn (fun w => dist (z : H) w) O.Z y → y = (O.p z : H))) ∧
      ∀ x ∈ S, ∀ z ∈ ball x (r x),
        ‖O.ambient z - (x + (P x).starProjection (z - x))‖ ≤ 3 * (ε / 3) * r x ∧
        ‖fderiv ℝ O.ambient z - (P x).starProjection‖ ≤ 8 * (ε / 3) ∧
        ∀ q, 2 ≤ q → q ≤ K →
          ‖iteratedFDeriv ℝ q (fun y => O.ambient y - (x + (P x).starProjection (y - x))) z‖ ≤
            1 * (ε / 3) * r x * ((r x)⁻¹) ^ q) ∧
    (let _ := O.cs
     ∀ x : S, ∀ z : O.Z, (z : H) ∈ ball (x : H) (r x) →
      ‖actualZeroSetNormalProjector k O.Z z - (P x)ᗮ.starProjection‖ ≤ 2 * (ε / 3)) := by
  have hε := O.eps_pos
  have hε1 : ε ≤ 1 := O.eps_le.trans (by norm_num)
  have hinv : 1 ≤ ε⁻¹ := one_le_inv₀ hε |>.mpr hε1
  have hsub4 : ∀ x : S, ball (0 : P x) (4 * r x) ⊆ ball (0 : P x) (4 * ε⁻¹ * r x) := fun x =>
    ball_subset_ball (by have := O.radius_pos x x.2; nlinarith)
  refine ⟨fun x => ⟨(O.graph_smooth x).mono (hsub4 x),
    fun q hq t ht => O.graph_jets x t (hsub4 x ht) q hq,
    fun t ht => (O.graph_mem x t (hsub4 x ht)).2, ?_⟩, O.proper_over,
    ⟨O.submersion, O.nearest, fun x hx z hz => ?_⟩, fun x z hz => O.cfs10_normal_CFSA hdim x z hz⟩
  · have hrx := O.radius_pos x x.2
    have h3 : ball (x : H) (3 * r x) ⊆ ball (x : H) (3 * ε⁻¹ * r x) := ball_subset_ball (by nlinarith)
    ext z
    constructor
    · rintro ⟨hzZ, hzb⟩
      have hz3 : z ∈ O.Z ∩ ball (x : H) (3 * ε⁻¹ * r x) := ⟨hzZ, h3 hzb⟩
      rw [O.graph_eq x] at hz3
      obtain ⟨⟨t, -, rfl⟩, -⟩ := hz3
      refine ⟨⟨t, ?_, rfl⟩, hzb⟩
      rw [mem_ball, dist_zero_right]
      have hle := norm_le_norm_add_orthogonal_CFSA (P x) t.2 (O.g x t).2
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left] at hzb
      have heq : orthogonalCoordinateSum (P x) (t, O.g x t) = (t : H) + (O.g x t : H) := rfl
      rw [heq] at hzb
      have : ‖t‖ = ‖(t : H)‖ := rfl
      linarith
    · rintro ⟨⟨t, ht, rfl⟩, hzb⟩
      exact ⟨(O.graph_mem x t (hsub4 x ht)).2, hzb⟩
  · have hvd := O.ambient_value_deriv hx hz
    have hrx := O.radius_pos x hx
    refine ⟨by linarith [hvd.1], by linarith [hvd.2.2], fun q _ hqK => ?_⟩
    rw [one_mul]
    exact O.ambient_jets ⟨x, hx⟩ z hz q hqK

end Cfs15StageOutput

end Output

end GC.MetricGeometry

open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14G_CFSA {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b =
      ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14G_CFSA {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b =
      ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14G_CFSA {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b =
      ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **Consumer: CFS10's `2a` normal clause on the actual first stage cloud**: for the enhanced
first-stage plane witness `A` (planes of dimension `2` on `S₁`) and any native output `O` on `S₁` with
radius `Σρ(A.rsel x₀ x)` and plane `A.plane` (e.g. from `cfs15_firstStagePlanes_CFSA`), the normal
projectors of `W = O.Z` on `W ∩ B(x, r_x)` are within `2ε/3` of `P_x`. -/
theorem cfs10_firstStagePlanes_normal_CFSA {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b =
      ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Γ sg eg : ℝ} (A : FirstStagePlanes_PLN P Γ sg eg) (x₀ : X) {Kj : ℕ}
    {εa cw : ℝ}
    (O : Cfs15StageOutput (gafStageDim 0) Kj εa cw (gafCloud P.toLocalChartFamily P.zero 0)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 0) (fun x => sg * ρ (A.rsel x₀ x)) A.plane) :
    let _ := O.cs
    ∀ x : gafCloud P.toLocalChartFamily P.zero 0, ∀ z : O.Z,
      (z : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∈
        ball (x : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
          (sg * ρ (A.rsel x₀ x)) →
      ‖actualZeroSetNormalProjector (gafStageDim 0) O.Z z - (A.plane x)ᗮ.starProjection‖ ≤
        2 * (εa / 3) :=
  (O.cfs10_row_CFSA fun x hx => (A.dimension x hx).1).2.2.2

end DifferentialGeometry.Geometry.Collapse
