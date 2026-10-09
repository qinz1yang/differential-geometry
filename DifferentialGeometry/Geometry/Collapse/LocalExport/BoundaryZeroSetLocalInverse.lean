import DifferentialGeometry.Geometry.Fibration.ActualStageChainSubmersionInputs
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# O-WF G1a: a smooth local inverse of a coordinate on a CFS15 zero set (local one-sheet)

The LOCAL replacement of CGP07's one-sheet property (lane O-WF; the global CGP07 record needs the
rough graphs, which the boundary chain does not carry). Two generic statements:

* `exists_smooth_localInverse_OWF` (inverse function theorem with smoothness on a whole ball):
  `Φ : E → F` smooth on an open `U ∋ t₀` with bijective `DΦ(t₀)` has an open `V ∋ t₀`, `V ⊆ U`,
  a radius `δ > 0` and `ψ : F → E` smooth on `B(Φ t₀, δ)` with `ψ b ∈ V`, `Φ (ψ b) = b` on the
  ball and `ψ (Φ t) = t` for `t ∈ V` with `Φ t` in the ball;
* `Cfs15StageOutput.exists_localInverse_OWF`: for a CFS15 output `O`, a point `z ∈ B(x, r_x)` of
  a reference ball and a linear coordinate `κ : H →L F` with `dim F = dim P_x` and `κ ∘ Da(z)`
  onto, `κ` has a smooth local inverse `ζ` on the zero set `Z` near `a(z)`: an open `V ∋ a(z)`,
  `δ > 0`, `ζ` smooth on `B(κ a(z), δ)` with `ζ b ∈ Z ∩ V`, `κ (ζ b) = b`, and
  `κ w ∈ B(κ a(z), δ)`, `ζ (κ w) = w` for every `w ∈ Z ∩ V` (in particular `κ` is injective on
  `Z ∩ V`). Route: `O.graph_eq` writes `Z ∩ B(x, 3ε⁻¹r_x)` as the graph `G(t) = x + (t, g_x t)`,
  `a = G ∘ τ ∘ a` near `z` (`τ = π_{P x}(· − x)`), so `κ ∘ Da(z) = κ ∘ DG(t₀) ∘ τ ∘ Da(z)` and
  `κ ∘ DG(t₀) : P x → F` is onto, hence bijective; the first statement for `Φ = κ ∘ G`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open scoped ContDiff Topology
open GC.MetricGeometry DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

/-- **Inverse function theorem with a smooth inverse on a whole ball** (see the module
docstring). -/
theorem exists_smooth_localInverse_OWF {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {Φ : E → F} {U : Set E} (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U) {t₀ : E} (ht₀ : t₀ ∈ U)
    (hbij : Bijective (fderiv ℝ Φ t₀)) :
    ∃ (V : Set E) (δ : ℝ) (ψ : F → E), IsOpen V ∧ t₀ ∈ V ∧ V ⊆ U ∧ 0 < δ ∧
      ContDiffOn ℝ ∞ ψ (ball (Φ t₀) δ) ∧
      (∀ b ∈ ball (Φ t₀) δ, ψ b ∈ V ∧ Φ (ψ b) = b) ∧
      (∀ t ∈ V, Φ t ∈ ball (Φ t₀) δ → ψ (Φ t) = t) := by
  set e₀ : E ≃L[ℝ] F := ContinuousLinearEquiv.ofBijective (fderiv ℝ Φ t₀)
    (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2) with he₀
  have hd : ContDiffAt ℝ ∞ Φ t₀ := hΦ.contDiffAt (hU.mem_nhds ht₀)
  have hf' : HasFDerivAt Φ (e₀ : E →L[ℝ] F) t₀ := by
    rw [he₀, ContinuousLinearEquiv.coe_ofBijective]
    exact (hd.differentiableAt (by simp)).hasFDerivAt
  let h := hd.toOpenPartialHomeomorph Φ hf' (by simp)
  have hcoe : (h : E → F) = Φ := rfl
  -- the open set of parameters with invertible derivative
  let Vinv : Set E := U ∩ (fderiv ℝ Φ) ⁻¹' range ((↑) : (E ≃L[ℝ] F) → E →L[ℝ] F)
  have hVinv : IsOpen Vinv :=
    (hΦ.continuousOn_fderiv_of_isOpen hU (by simp)).isOpen_inter_preimage hU
      ContinuousLinearEquiv.isOpen
  let V : Set E := h.source ∩ Vinv
  have hV : IsOpen V := h.open_source.inter hVinv
  have ht₀V : t₀ ∈ V :=
    ⟨hd.mem_toOpenPartialHomeomorph_source hf' (by simp), ht₀, e₀, by
      rw [he₀, ContinuousLinearEquiv.coe_ofBijective]⟩
  have hT : IsOpen (h '' V) := h.isOpen_image_of_subset_source hV inter_subset_left
  have hΦt₀ : Φ t₀ ∈ h '' V := ⟨t₀, ht₀V, rfl⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hT (Φ t₀) hΦt₀
  have hinv : ∀ b ∈ ball (Φ t₀) δ, h.symm b ∈ V ∧ Φ (h.symm b) = b ∧ b ∈ h.target := by
    intro b hb
    obtain ⟨t, htV, rfl⟩ := hball hb
    have hts : h.symm (h t) = t := h.left_inv htV.1
    refine ⟨by rw [hts]; exact htV, by rw [hts]; rfl, h.map_source htV.1⟩
  refine ⟨V, δ, h.symm, hV, ht₀V, fun t ht => ht.2.1, hδ, ?_, fun b hb => ⟨(hinv b hb).1,
    (hinv b hb).2.1⟩, fun t ht _ => h.left_inv ht.1⟩
  intro b hb
  obtain ⟨hbV, -, hbT⟩ := hinv b hb
  obtain ⟨-, hbU, e, he⟩ := hbV
  have hcd : ContDiffAt ℝ ∞ Φ (h.symm b) := hΦ.contDiffAt (hU.mem_nhds hbU)
  have hfd : HasFDerivAt (h : E → F) (e : E →L[ℝ] F) (h.symm b) := by
    rw [hcoe, he]
    exact (hcd.differentiableAt (by simp)).hasFDerivAt
  exact (h.contDiffAt_symm hbT hfd hcd).contDiffWithinAt

section Zero

variable {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {k K : ℕ} {ε cw : ℝ} {Sc T : Set H} {r : H → ℝ} {P : H → Submodule ℝ H}

/-- The graph map of a CFS15 output at a cloud point is smooth on the graph's parameter ball. -/
theorem _root_.GC.MetricGeometry.Cfs15StageOutput.graphMap_contDiffOn_OWF
    (O : Cfs15StageOutput k K ε cw Sc T r P)
    (x : Sc) :
    ContDiffOn ℝ ∞ (fun s : P x => (x : H) + orthogonalCoordinateSum (P x) (s, O.g x s))
      (ball 0 (4 * ε⁻¹ * r x)) :=
  contDiffOn_const.add ((orthogonalCoordinateSum (P x)).contDiff.comp_contDiffOn
    (contDiffOn_id.prodMk (O.graph_smooth x)))

/-- **A smooth local inverse of `κ` on the zero set near `a(z)`** (local one-sheet; see the module
docstring). -/
theorem _root_.GC.MetricGeometry.Cfs15StageOutput.exists_localInverse_OWF
    (O : Cfs15StageOutput k K ε cw Sc T r P)
    (x : Sc) {z : H} (hz : z ∈ ball (x : H) (r x)) (κ : H →L[ℝ] F)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ (P x))
    (hsurj : ∀ v : F, ∃ u : H, κ (fderiv ℝ O.ambient z u) = v) :
    ∃ (V : Set H) (δ : ℝ) (ζ : F → H), IsOpen V ∧ O.ambient z ∈ V ∧ 0 < δ ∧
      ContDiffOn ℝ ∞ ζ (ball (κ (O.ambient z)) δ) ∧
      (∀ b ∈ ball (κ (O.ambient z)) δ, ζ b ∈ O.Z ∩ V ∧ κ (ζ b) = b) ∧
      (∀ w ∈ O.Z ∩ V, κ w ∈ ball (κ (O.ambient z)) δ ∧ ζ (κ w) = w) := by
  have hε := O.eps_pos
  have hε1 := O.eps_le
  have hr := O.radius_pos x x.2
  have hinv : 10 ≤ ε⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hε]
    linarith
  set L : Submodule ℝ H := P x with hL
  let G : L → H := fun s => (x : H) + orthogonalCoordinateSum L (s, O.g x s)
  let τ : H → L := fun w => L.orthogonalProjectionOnto (w - x)
  have hτc : Continuous τ :=
    (L.orthogonalProjectionOnto : H →L[ℝ] L).continuous.comp (continuous_id.sub continuous_const)
  have hav := O.ambient_value_deriv x.2 hz
  -- every zero near `x` is `G (τ w)`
  have hgraph : ∀ w ∈ O.Z ∩ ball (x : H) (3 * ε⁻¹ * r x),
      w = G (τ w) ∧ τ w ∈ ball (0 : L) (4 * ε⁻¹ * r x) := by
    intro w hw
    have hw' := hw
    rw [O.graph_eq x] at hw'
    obtain ⟨⟨t, ht, hwt⟩, -⟩ := hw'
    have hτ : τ w = t := by
      change L.orthogonalProjectionOnto (w - x) = t
      rw [hwt]
      exact orthogonalProjectionOnto_graph_BASP L x t (O.g x t)
    rw [hτ]
    exact ⟨hwt, ht⟩
  have hτG : ∀ t : L, τ (G t) = t := fun t => orthogonalProjectionOnto_graph_BASP L x t (O.g x t)
  -- `a(z)` is a zero close to `x`
  have hzΩ := mem_cfs15Omega_of_mem_C15 x.2 hz
  have haz : ‖O.ambient z - x‖ ≤ 2 * r x := by
    have h1 : ‖(P x).starProjection (z - x)‖ ≤ ‖z - x‖ :=
      Submodule.norm_starProjection_apply_le _ _
    have h2 : ‖z - x‖ < r x := by
      rw [← dist_eq_norm]
      exact hz
    have h3 : ‖O.ambient z - x‖ ≤ ‖O.ambient z - (x + (P x).starProjection (z - x))‖ +
        ‖(P x).starProjection (z - x)‖ := by
      have := norm_add_le (O.ambient z - (x + (P x).starProjection (z - x)))
        ((P x).starProjection (z - x))
      rwa [show O.ambient z - (x + (P x).starProjection (z - x)) + (P x).starProjection (z - x) =
        O.ambient z - x by abel] at this
    have h4 : ε * r x ≤ r x := by nlinarith
    linarith [hav.1]
  have h3r : 2 * r x < 3 * ε⁻¹ * r x := by nlinarith
  have hball : O.ambient z ∈ ball (x : H) (3 * ε⁻¹ * r x) := by
    rw [mem_ball, dist_eq_norm]
    linarith
  have hcont : ContinuousAt O.ambient z := (O.ambient_contDiffAt hzΩ).continuousAt
  have hev : O.ambient =ᶠ[𝓝 z] fun y => G (τ (O.ambient y)) := by
    have h1 : ∀ᶠ y in 𝓝 z, y ∈ ball (x : H) (r x) := isOpen_ball.mem_nhds hz
    have h2 : ∀ᶠ y in 𝓝 z, O.ambient y ∈ ball (x : H) (3 * ε⁻¹ * r x) :=
      hcont.eventually (isOpen_ball.mem_nhds hball)
    filter_upwards [h1, h2] with y hy1 hy2
    exact (hgraph _ ⟨O.ambient_mem (mem_cfs15Omega_of_mem_C15 x.2 hy1), hy2⟩).1
  have hgz := hgraph _ ⟨O.ambient_mem hzΩ, hball⟩
  set t₀ : L := τ (O.ambient z) with ht₀
  -- the parameter `t₀` lies in the smaller ball `B(0, 2ε⁻¹r)`
  have ht₀U : t₀ ∈ ball (0 : L) (2 * ε⁻¹ * r x) := by
    rw [mem_ball_zero_iff]
    have h1 : ‖t₀‖ ≤ ‖O.ambient z - x‖ := by
      change ‖L.orthogonalProjectionOnto (O.ambient z - x)‖ ≤ _
      exact L.norm_orthogonalProjectionOnto_apply_le _
    have h2 : 2 * r x < 2 * ε⁻¹ * r x := by nlinarith
    linarith
  have hsub : ball (0 : L) (2 * ε⁻¹ * r x) ⊆ ball (0 : L) (4 * ε⁻¹ * r x) :=
    ball_subset_ball (by nlinarith)
  have hGs := O.graphMap_contDiffOn_OWF x
  have hgd : DifferentiableAt ℝ (O.g x) t₀ :=
    ((O.graph_smooth x).contDiffAt (isOpen_ball.mem_nhds hgz.2)).differentiableAt (by simp)
  have hG := hasFDerivAt_orthogonalGraph_BPRE L (O.g x) (x : H) hgd
  have hτd : HasFDerivAt τ (L.orthogonalProjectionOnto : H →L[ℝ] L) (O.ambient z) := by
    have h := (L.orthogonalProjectionOnto : H →L[ℝ] L).hasFDerivAt (x := O.ambient z - x)
    exact h.comp (O.ambient z) ((hasFDerivAt_id _).sub_const (x : H))
  have had : HasFDerivAt O.ambient (fderiv ℝ O.ambient z) z := hav.2.1.hasFDerivAt
  have hcomp := hG.comp z (hτd.comp z had)
  have hfd : fderiv ℝ O.ambient z =
      (L.subtypeL + Lᗮ.subtypeL.comp (fderiv ℝ (O.g x) t₀)).comp
        ((L.orthogonalProjectionOnto : H →L[ℝ] L).comp (fderiv ℝ O.ambient z)) :=
    hev.fderiv_eq.trans hcomp.fderiv
  -- `Φ = κ ∘ G` has bijective derivative at `t₀`
  let Φ : L → F := fun s => κ (G s)
  have hΦs : ContDiffOn ℝ ∞ Φ (ball (0 : L) (2 * ε⁻¹ * r x)) :=
    κ.contDiff.comp_contDiffOn (hGs.mono hsub)
  have hΦd : fderiv ℝ Φ t₀ = κ.comp (L.subtypeL + Lᗮ.subtypeL.comp (fderiv ℝ (O.g x) t₀)) :=
    (κ.hasFDerivAt.comp t₀ hG).fderiv
  have hΦsurj : Surjective (fderiv ℝ Φ t₀) := by
    intro v
    obtain ⟨u, hu⟩ := hsurj v
    refine ⟨(L.orthogonalProjectionOnto : H →L[ℝ] L) (fderiv ℝ O.ambient z u), ?_⟩
    rw [hΦd, ← hu]
    conv_rhs => rw [hfd]
    rfl
  have hΦbij : Bijective (fderiv ℝ Φ t₀) := by
    have hfin : Module.finrank ℝ L = Module.finrank ℝ F := hdim.symm
    refine ⟨?_, hΦsurj⟩
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin
      (f := (fderiv ℝ Φ t₀ : L →ₗ[ℝ] F))).mpr hΦsurj
  obtain ⟨VL, δ, ψ, hVL, ht₀V, hVLU, hδ, hψs, hψb, hψl⟩ :=
    exists_smooth_localInverse_OWF isOpen_ball hΦs ht₀U hΦbij
  have hκaz : κ (O.ambient z) = Φ t₀ := by
    change κ (O.ambient z) = κ (G (τ (O.ambient z)))
    rw [← hgz.1]
  -- the open set `V` and the local inverse `ζ = G ∘ ψ`
  let V : Set H := ball (x : H) (3 * ε⁻¹ * r x) ∩ τ ⁻¹' VL ∩ κ ⁻¹' ball (Φ t₀) δ
  have hV : IsOpen V :=
    (isOpen_ball.inter (hVL.preimage hτc)).inter (isOpen_ball.preimage κ.continuous)
  have hGball : ∀ t ∈ ball (0 : L) (2 * ε⁻¹ * r x), G t ∈ ball (x : H) (3 * ε⁻¹ * r x) ∧
      G t ∈ O.Z := by
    intro t ht
    have ht4 := hsub ht
    obtain ⟨hgn, hmem⟩ := O.graph_mem x t ht4
    refine ⟨?_, hmem⟩
    rw [mem_ball, dist_eq_norm]
    have heq : G t - x = (t : H) + ((O.g x t : Lᗮ) : H) := by
      change (x : H) + orthogonalCoordinateSum L (t, O.g x t) - x = _
      rw [add_sub_cancel_left]
      rfl
    rw [heq]
    have h1 := norm_add_le (t : H) ((O.g x t : Lᗮ) : H)
    have h2 : ‖(t : H)‖ < 2 * ε⁻¹ * r x := by
      rw [mem_ball_zero_iff] at ht
      exact ht
    have h3 : ‖((O.g x t : Lᗮ) : H)‖ ≤ r x / 4 := hgn
    have h4 : r x / 4 ≤ ε⁻¹ * r x := by nlinarith
    change ‖(t : H)‖ + ‖((O.g x t : Lᗮ) : H)‖ ≥ ‖(t : H) + ((O.g x t : Lᗮ) : H)‖ at h1
    linarith
  refine ⟨V, δ, fun b => G (ψ b), hV, ⟨⟨hball, ht₀V⟩, by
      change κ (O.ambient z) ∈ ball (Φ t₀) δ
      rw [hκaz]
      exact mem_ball_self hδ⟩, hδ, ?_, ?_, ?_⟩
  · rw [hκaz]
    exact (hGs.mono hsub).comp hψs fun b hb => hVLU (hψb b hb).1
  · intro b hb
    rw [hκaz] at hb
    obtain ⟨hbV, hbΦ⟩ := hψb b hb
    obtain ⟨hGb, hGZ⟩ := hGball _ (hVLU hbV)
    refine ⟨⟨hGZ, ⟨hGb, ?_⟩, ?_⟩, hbΦ⟩
    · change τ (G (ψ b)) ∈ VL
      rw [hτG]
      exact hbV
    · change Φ (ψ b) ∈ ball (Φ t₀) δ
      rw [hbΦ]
      exact hb
  · rintro w ⟨hwZ, ⟨hwb, hwV⟩, hwκ⟩
    have hgw := hgraph w ⟨hwZ, hwb⟩
    have hκw : κ w = Φ (τ w) := by
      change κ w = κ (G (τ w))
      rw [← hgw.1]
    refine ⟨by rw [hκaz]; exact hwκ, ?_⟩
    change G (ψ (κ w)) = w
    rw [hκw, hψl (τ w) hwV (by rw [← hκw]; exact hwκ), ← hgw.1]

end Zero

end DifferentialGeometry.Geometry.Collapse
