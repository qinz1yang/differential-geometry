import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.Boundary.LocalApproximation
import DifferentialGeometry.Geometry.Fibration.ManifoldBlockDerivative

/-!
# Lipschitz functions have bounded differentials, corners allowed (lane B-DFB, G3a)

On a smooth manifold with corners (no `Boundaryless`, no completeness, no metric-space instance),
a `C¹` real function which is `L`-Lipschitz near `p` for the extended `g`-length distance
`riemannianEDistOf g` has `|df_p(v)| ≤ L |v|_g` for EVERY tangent vector at `p`, boundary points
included (the boundaryless complete versions are `abs_mvfderiv_le_of_lipschitzOn_riem`,
`abs_mvfderiv_le_of_lipschitzWith_riemannianEDistOf`).

* `abs_fderivWithin_le_of_lipschitz_convex_BDFB` (real analysis): on a convex set `s` with nonempty
  interior, a function `C¹` within `s` at `z₀` and `C`-Lipschitz near `z₀` for the seminorm
  `‖A ·‖` has `|D ψ(z₀) w| ≤ C ‖A w‖` — the bound holds at interior points of `s` (two-sided
  difference quotients), and the within-derivative is continuous on `s ∩ u`, whose interior
  points accumulate at `z₀` (`Convex.closure_interior_eq_closure_of_nonempty_interior`).
* `trivializationAt_symmL_self_BDFB`: the tangent trivialization at `p` is the identity at `p`.
* `abs_mvfderiv_le_of_lipschitz_riemannianEDistOf_BDFB` (the manifold statement): in the chart at
  `p`, `metricChartEuclideanEquiv g p` is `κ`-bi-Lipschitz for `riemannianEDistOf g` near `p`
  (`exists_open_chart_euclidean_comparison`, corners allowed) and `‖A v‖ = |v|_g`; let `κ → 1`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

section RealAnalysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **Lipschitz ⇒ bounded within-derivative on a convex set with nonempty interior.** -/
theorem abs_fderivWithin_le_of_lipschitz_convex_BDFB {s : Set E} (hs : Convex ℝ s)
    (hs' : (interior s).Nonempty) {ψ : E → ℝ} {z₀ : E} (hz₀ : z₀ ∈ s)
    (hψ : ContDiffWithinAt ℝ 1 ψ s z₀) {V : Set E} (hV : V ∈ 𝓝[s] z₀) (A : E →L[ℝ] F)
    {C : ℝ} (hC : 0 ≤ C) (hlip : ∀ z ∈ V, ∀ z' ∈ V, |ψ z - ψ z'| ≤ C * ‖A (z - z')‖) (w : E) :
    |fderivWithin ℝ ψ s z₀ w| ≤ C * ‖A w‖ := by
  obtain ⟨u, hu, hz₀u, hCu⟩ := hψ.contDiffOn' le_rfl (by simp)
  rw [insert_eq_of_mem hz₀] at hCu
  have huniq : UniqueDiffOn ℝ (s ∩ u) := (uniqueDiffOn_convex hs hs').inter hu
  have hcont : ContinuousOn (fun z => fderivWithin ℝ ψ (s ∩ u) z) (s ∩ u) :=
    hCu.continuousOn_fderivWithin huniq le_rfl
  obtain ⟨O, hO, hz₀O, hOV⟩ := mem_nhdsWithin.mp hV
  have hTo : IsOpen (interior s ∩ (u ∩ O)) := isOpen_interior.inter (hu.inter hO)
  have hTsub : interior s ∩ (u ∩ O) ⊆ s ∩ u := fun z hz => ⟨interior_subset hz.1, hz.2.1⟩
  have hTV : ∀ z ∈ interior s ∩ (u ∩ O), z ∈ V := fun z hz => hOV ⟨hz.2.2, interior_subset hz.1⟩
  have hbound : ∀ z ∈ interior s ∩ (u ∩ O),
      |fderivWithin ℝ ψ (s ∩ u) z w| ≤ C * ‖A w‖ := by
    intro z hz
    have hn : s ∩ u ∈ 𝓝 z := inter_mem (mem_interior_iff_mem_nhds.mp hz.1) (hu.mem_nhds hz.2.1)
    have hd : DifferentiableAt ℝ ψ z :=
      ((hCu.differentiableOn one_ne_zero) z (hTsub hz)).differentiableAt hn
    rw [fderivWithin_of_mem_nhds hn]
    have hline : HasDerivAt (fun τ : ℝ => z + τ • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add z
    have hcomp : HasDerivAt (fun τ : ℝ => ψ (z + τ • w)) (fderiv ℝ ψ z w) 0 :=
      hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    have hev : ∀ᶠ τ in 𝓝 (0 : ℝ), z + τ • w ∈ interior s ∩ (u ∩ O) := by
      have hc : Continuous fun τ : ℝ => z + τ • w := by fun_prop
      exact hc.continuousAt.preimage_mem_nhds (by simpa using hTo.mem_nhds hz)
    have hle := hcomp.le_of_lip' (C := C * ‖A w‖) (by positivity) (by
      filter_upwards [hev] with τ hτ
      have h1 := hlip _ (hTV _ hτ) z (hTV z hz)
      have he : A (z + τ • w - z) = τ • A w := by
        rw [add_sub_cancel_left, map_smul]
      rw [he, norm_smul, Real.norm_eq_abs] at h1
      rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, zero_smul, add_zero]
      calc |ψ (z + τ • w) - ψ z| ≤ C * (|τ| * ‖A w‖) := h1
        _ = C * ‖A w‖ * |τ| := by ring)
    simpa only [Real.norm_eq_abs] using hle
  have hclos : z₀ ∈ closure (interior s ∩ (u ∩ O)) := by
    have h1 : z₀ ∈ closure (interior s) := by
      rw [hs.closure_interior_eq_closure_of_nonempty_interior hs']
      exact subset_closure hz₀
    rw [mem_closure_iff_nhds] at h1 ⊢
    intro N hN
    obtain ⟨y, hy1, hy2⟩ :=
      h1 (N ∩ (u ∩ O)) (inter_mem hN ((hu.inter hO).mem_nhds ⟨hz₀u, hz₀O⟩))
    exact ⟨y, hy1.1, hy2, hy1.2⟩
  have hcw : ContinuousWithinAt (fun z => |fderivWithin ℝ ψ (s ∩ u) z w|)
      (interior s ∩ (u ∩ O)) z₀ :=
    (((hcont z₀ ⟨hz₀, hz₀u⟩).mono hTsub).clm_apply continuousWithinAt_const).abs
  have hfin := ContinuousWithinAt.closure_le hclos hcw continuousWithinAt_const hbound
  rwa [fderivWithin_inter (hu.mem_nhds hz₀u)] at hfin

end RealAnalysis

section Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

omit [FiniteDimensional ℝ E] in
/-- The tangent trivialization at `p`, read at `p`, is the identity. -/
theorem trivializationAt_symmL_self_BDFB (p : M) (w : E) :
    (trivializationAt E (TangentSpace I) p).symmL ℝ p w = w := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source H p)]
  exact (tangentBundleCore I M).coordChange_self (achart H p) p (mem_chart_source H p) w

/-- **Lipschitz for the `g`-length distance ⇒ `|df(v)| ≤ L |v|_g`, corners allowed.** A real
function, `C¹` at `p`, which is `L`-Lipschitz for `riemannianEDistOf g` on a neighbourhood of `p`
has differential at most `L |v|_g` on every tangent vector at `p` (boundary points included). -/
theorem abs_mvfderiv_le_of_lipschitz_riemannianEDistOf_BDFB [RegularSpace M]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {p : M} (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 1 f p)
    {L : ℝ} (hL : 0 ≤ L) {U : Set M} (hU : U ∈ 𝓝 p)
    (hlip : ∀ x ∈ U, ∀ y ∈ U,
      ENNReal.ofReal |f x - f y| ≤ ENNReal.ofReal L * riemannianEDistOf g x y)
    (v : TangentSpace I p) :
    |mvfderiv I f p v| ≤ L * Real.sqrt (g.inner p v v) := by
  set φ := extChartAt I p with hφ
  set A := metricChartEuclideanEquiv g p with hA
  have hAv : ∀ w : E, ‖A w‖ = Real.sqrt (g.inner p w w) := fun w => by
    rw [hA, metricChartEuclideanEquiv_norm, trivializationAt_symmL_self_BDFB]
  have hψ : ContDiffWithinAt ℝ 1 (f ∘ φ.symm) (range I) (φ p) := by
    have h := (contMDiffAt_iff.mp hf).2
    simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp] using h
  have hD : mvfderiv I f p v = fderivWithin ℝ (f ∘ φ.symm) (range I) (φ p) v := by
    rw [mvfderiv_apply_LC, (hf.mdifferentiableAt one_ne_zero).mfderiv]
    simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      Function.id_comp, hφ]
    rfl
  have hz₀ : φ p ∈ range I := extChartAt_target_subset_range p (mem_extChartAt_target p)
  have hκ : ∀ κ : ℝ, 1 < κ → |mvfderiv I f p v| ≤ L * κ * Real.sqrt (g.inner p v v) := by
    intro κ hκ
    obtain ⟨U', hU'o, hpU', -, hcmp⟩ := exists_open_chart_euclidean_comparison g p hκ
    have hWn : U ∩ U' ∈ 𝓝 p := inter_mem hU (hU'o.mem_nhds hpU')
    have hreal : ∀ x ∈ U ∩ U', ∀ y ∈ U ∩ U',
        |f x - f y| ≤ L * κ * ‖A (φ y) - A (φ x)‖ := by
      intro x hx y hy
      have h1 := hlip x hx.1 y hy.1
      have h2 := (hcmp x hx.2 y hy.2).2
      have h3 : ENNReal.ofReal |f x - f y| ≤ ENNReal.ofReal (L * κ * ‖A (φ y) - A (φ x)‖) :=
        calc ENNReal.ofReal |f x - f y| ≤ ENNReal.ofReal L * riemannianEDistOf g x y := h1
          _ ≤ ENNReal.ofReal L * (ENNReal.ofReal κ * ENNReal.ofReal ‖A (φ y) - A (φ x)‖) := by
            gcongr
          _ = ENNReal.ofReal (L * κ * ‖A (φ y) - A (φ x)‖) := by
            rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul hL, mul_assoc]
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h3
    have hV : φ.target ∩ φ.symm ⁻¹' (U ∩ U') ∈ 𝓝[range I] (φ p) := by
      refine inter_mem (extChartAt_target_mem_nhdsWithin p) ?_
      rw [← map_extChartAt_symm_nhdsWithin_range (I := I) p] at hWn
      exact hWn
    have hlipψ : ∀ z ∈ φ.target ∩ φ.symm ⁻¹' (U ∩ U'), ∀ z' ∈ φ.target ∩ φ.symm ⁻¹' (U ∩ U'),
        |(f ∘ φ.symm) z - (f ∘ φ.symm) z'| ≤
          L * κ * ‖(A : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) (z - z')‖ := by
      intro z hz z' hz'
      have h := hreal _ hz.2 _ hz'.2
      rw [φ.right_inv hz.1, φ.right_inv hz'.1] at h
      calc |(f ∘ φ.symm) z - (f ∘ φ.symm) z'| ≤ L * κ * ‖A z' - A z‖ := h
        _ = L * κ * ‖(A : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) (z - z')‖ := by
          rw [ContinuousLinearEquiv.coe_coe, map_sub, norm_sub_rev]
    have h := abs_fderivWithin_le_of_lipschitz_convex_BDFB I.convex_range I.nonempty_interior hz₀
      hψ hV (A : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) (by positivity) hlipψ v
    rw [hD]
    calc |fderivWithin ℝ (f ∘ φ.symm) (range I) (φ p) v|
        ≤ L * κ * ‖(A : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) v‖ := h
      _ = L * κ * Real.sqrt (g.inner p v v) := by
          rw [ContinuousLinearEquiv.coe_coe]
          exact congrArg (fun t => L * κ * t) (hAv v)
  set b := L * Real.sqrt (g.inner p v v) with hb
  have hb0 : 0 ≤ b := mul_nonneg hL (Real.sqrt_nonneg _)
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have hκ' := hκ (1 + ε / (b + 1)) (by have := div_pos hε (by linarith : (0 : ℝ) < b + 1); linarith)
  have he : L * (1 + ε / (b + 1)) * Real.sqrt (g.inner p v v) = b + b * (ε / (b + 1)) := by
    rw [hb]; ring
  rw [he] at hκ'
  have hlt : b * (ε / (b + 1)) < ε := by
    rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
    nlinarith
  linarith

end Manifold

end DifferentialGeometry.Geometry.Collapse
