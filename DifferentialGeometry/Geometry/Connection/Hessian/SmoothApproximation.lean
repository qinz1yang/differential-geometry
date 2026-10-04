import DifferentialGeometry.Geometry.Connection.Hessian.ChartEstimate
import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Boundary.RelativeEuclidean

/-!
# `C²` smooth approximation on a compact set, with covariant first and second derivatives

`exists_smooth_approx_C2_on_compact`: on a compact manifold `M` (the model may have boundary)
with a smooth Riemannian metric `g`, let `u` be of class `C²` on an open set `U` of interior points
and `B ⊆ U` compact. For every `ε > 0` there is a smooth `η : M → ℝ` with, at every `y ∈ B`,
`|η - u| < ε`, `|d(η - u)(X)| ≤ ε |X|_g` and `|Hess_g(η - u)(X, Y)| ≤ ε |X|_g |Y|_g`, where `Hess_g`
is the EXISTING Hessian `(CovariantDerivative.trivial I M ℝ).hessian (LeviCivita g)`.

Route: `η` is a member of the relative approximating sequence of `ρ u` (`ρ` a cutoff equal to `1`
near `B`, `exists_smooth_seq_rel_chart_tendsto_normedSpace` with `k = 2`); near each point of `B`
the chart bounds `abs_mvfderiv_le_chart`, `abs_hessian_le_chart` and
`exists_norm_trivToE_le_sqrt_inner` turn chart `C²` convergence on a closed ball into the
covariant bounds; compactness of `B` (`eventually_forall_of_isCompact_of_local`) finishes.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Geometry.Connection

open DifferentialGeometry.Topology.Manifold.SmoothApproximation
open DifferentialGeometry.CheegerGromovCompactness

/-- An eventual property holding uniformly near every point of a compact set holds uniformly on
the compact set. -/
theorem eventually_forall_of_isCompact_of_local {X ι : Type*} [TopologicalSpace X]
    {l : Filter ι} {K : Set X} (hK : IsCompact K) {P : ι → X → Prop}
    (h : ∀ x ∈ K, ∃ V ∈ 𝓝 x, ∀ᶠ j in l, ∀ y ∈ V, P j y) : ∀ᶠ j in l, ∀ y ∈ K, P j y := by
  refine hK.induction_on (p := fun S => ∀ᶠ j in l, ∀ y ∈ S, P j y) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun j y hy => absurd hy (notMem_empty y)
  · intro s t hst ht
    exact ht.mono fun j hj y hy => hj y (hst hy)
  · intro s t hs ht
    exact (hs.and ht).mono fun j hj y hy => hy.elim (hj.1 y) (hj.2 y)
  · intro x hx
    obtain ⟨V, hV, hP⟩ := h x hx
    exact ⟨V, mem_nhdsWithin_of_mem_nhds hV, hP⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M]

/-- A function `C²` on an open set of interior points agrees near a compact subset with a global
`C²` function that is smooth on a neighbourhood `O ⊇ closure O' ⊇ ∂M`. -/
theorem exists_C2_extension_eq_near_compact {u : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hUi : U ⊆ I.interior M) (hu : ContMDiffOn I 𝓘(ℝ, ℝ) 2 u U) {B : Set M}
    (hB : IsCompact B) (hBU : B ⊆ U) :
    ∃ (v : M → ℝ) (V O O' : Set M), IsOpen V ∧ B ⊆ V ∧ V ⊆ U ∧ EqOn v u V ∧
      ContMDiff I 𝓘(ℝ, ℝ) 2 v ∧ IsOpen O ∧ I.boundary M ⊆ O' ∧ closure O' ⊆ O ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ v O := by
  obtain ⟨V₁, hV₁, hBV₁, hV₁cl⟩ := normal_exists_closure_subset hB.isClosed hU hBU
  obtain ⟨V₂, hV₂, hV₁V₂, hV₂cl⟩ := normal_exists_closure_subset isClosed_closure hU hV₁cl
  obtain ⟨V₃, hV₃, hV₂V₃, hV₃cl⟩ := normal_exists_closure_subset isClosed_closure hU hV₂cl
  obtain ⟨χ, hχ0, hχ1, -⟩ := exists_contMDiffMap_zero_one_of_isClosed (n := (⊤ : ℕ∞)) I
    (isClosed_closure : IsClosed (closure V₁)) hV₂.isClosed_compl
    (disjoint_compl_right_iff_subset.mpr hV₁V₂)
  have hχs : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ := χ.contMDiff
  set v : M → ℝ := fun y => (1 - χ y) * u y with hvdef
  have hvu : EqOn v u V₁ := fun y hy => by
    simp only [hvdef, hχ0 (subset_closure hy), Pi.zero_apply, sub_zero, one_mul]
  have hv0 : ∀ y, y ∉ V₂ → v y = 0 := fun y hy => by
    simp only [hvdef, hχ1 hy, Pi.one_apply, sub_self, zero_mul]
  have hv : ContMDiff I 𝓘(ℝ, ℝ) 2 v := by
    intro y
    by_cases hy : y ∈ U
    · exact ((contMDiffAt_const.sub (hχs y)).of_le (by simp)).mul
        (hu.contMDiffAt (hU.mem_nhds hy))
    · have hy' : y ∉ closure V₂ := fun h => hy (hV₂cl h)
      refine (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hy'] with z hz
      exact hv0 z fun h => hz (subset_closure h)
  refine ⟨v, V₁, (closure V₂)ᶜ, (closure V₃)ᶜ, hV₁, hBV₁, subset_closure.trans hV₁cl, hvu, hv,
    isClosed_closure.isOpen_compl, ?_, ?_, ?_⟩
  · intro y hy hy3
    exact (I.isInteriorPoint_iff_not_isBoundaryPoint y).mp (hUi (hV₃cl hy3)) hy
  · rw [closure_compl]
    exact compl_subset_compl.mpr (hV₂V₃.trans (interior_maximal subset_closure hV₃))
  · exact contMDiffOn_const.congr fun y hy => hv0 y fun h => hy (subset_closure h)

/-- **`C²` smooth approximation on a compact set with covariant bounds.** -/
theorem exists_smooth_approx_C2_on_compact (g : SmoothRiemannianMetric I M) {u : M → ℝ}
    {U : Set M} (hU : IsOpen U) (hUi : U ⊆ I.interior M) (hu : ContMDiffOn I 𝓘(ℝ, ℝ) 2 u U)
    {B : Set M} (hB : IsCompact B) (hBU : B ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ η ∧ ∀ y ∈ B, |η y - u y| < ε ∧
      (∀ X : TangentSpace I y,
        |mvfderiv I (fun y => η y - u y) y X| ≤ ε * Real.sqrt (g.inner y X X)) ∧
      ∀ X Y : TangentSpace I y,
        |(CovariantDerivative.trivial I M ℝ).hessian (LeviCivita g) (fun y => η y - u y) y X Y| ≤
          ε * Real.sqrt (g.inner y X X) * Real.sqrt (g.inner y Y Y) := by
  obtain ⟨v, V, O, O', hV, hBV, -, hvu, hv, hO, hbO', hO'O, hvO⟩ :=
    exists_C2_extension_eq_near_compact hU hUi hu hB hBU
  obtain ⟨us, hus, -, hunif, hchart⟩ :=
    exists_smooth_seq_rel_chart_tendsto_normedSpace 2 hv hO hbO' hO'O hvO
  have hC0 : ∀ᶠ j in atTop, ∀ y ∈ B, |us j y - u y| < ε := by
    filter_upwards [Metric.tendstoUniformly_iff.mp hunif ε hε] with j hj y hy
    rw [← hvu (hBV hy), ← Real.dist_eq, dist_comm]
    exact hj y
  have hloc : ∀ y₀ ∈ B, ∃ N ∈ 𝓝 y₀, ∀ᶠ j in atTop, ∀ y ∈ N, y ∈ B →
      (∀ X : TangentSpace I y,
        |mvfderiv I (fun y => us j y - u y) y X| ≤ ε * Real.sqrt (g.inner y X X)) ∧
      ∀ X Y : TangentSpace I y,
        |(CovariantDerivative.trivial I M ℝ).hessian (LeviCivita g)
            (fun y => us j y - u y) y X Y| ≤
          ε * Real.sqrt (g.inner y X X) * Real.sqrt (g.inner y Y Y) := by
    intro y₀ hy₀
    set ψ := extChartAt I y₀ with hψ
    have hy₀U : y₀ ∈ U := hBU hy₀
    have hint₀ : ψ y₀ ∈ interior ψ.target :=
      interior_maximal inter_subset_left (isOpen_extChartAt_target_inter_interior (I := I) y₀)
        ⟨mem_extChartAt_target y₀, hUi hy₀U⟩
    set Ω : Set E := interior ψ.target ∩ ψ.symm ⁻¹' V with hΩ
    have hΩo : IsOpen Ω :=
      ((continuousOn_extChartAt_symm y₀).mono interior_subset).isOpen_inter_preimage
        isOpen_interior hV
    have hy₀Ω : ψ y₀ ∈ Ω := by
      refine ⟨hint₀, ?_⟩
      change ψ.symm (ψ y₀) ∈ V
      rw [ψ.left_inv (mem_extChartAt_source y₀)]
      exact hBV hy₀
    obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.mp hΩo _ hy₀Ω
    set Kc := Metric.closedBall (ψ y₀) (r / 2) with hKcdef
    have hKc : IsCompact Kc := isCompact_closedBall _ _
    have hKcΩ : Kc ⊆ Ω := (Metric.closedBall_subset_ball (half_lt_self hr)).trans hrΩ
    have hKcint : Kc ⊆ interior ψ.target := hKcΩ.trans inter_subset_left
    have hKct : Kc ⊆ ψ.target := hKcint.trans interior_subset
    have hKcr : Kc ⊆ interior (range I) :=
      hKcint.trans (interior_mono (extChartAt_target_subset_range y₀))
    obtain ⟨CΓ, hCΓ⟩ :=
      hKc.exists_bound_of_continuousOn ((continuousOn_christoffelBound g y₀).mono hKcint)
    obtain ⟨Cg, hCg0, hCg⟩ := exists_norm_trivToE_le_sqrt_inner g y₀ (S := ψ.symm '' Kc)
      (hKc.image_of_continuousOn ((continuousOn_extChartAt_symm y₀).mono hKct))
      (by
        rintro _ ⟨z, hz, rfl⟩
        rw [← extChartAt_source (I := I)]
        exact ψ.map_target (hKct hz))
    set P : ℝ := (1 + Cg) ^ 2 * (1 + |CΓ|) with hPdef
    have hP : 0 < P := by positivity
    set δ' : ℝ := ε / P with hδ'def
    have hδ' : 0 < δ' := div_pos hε hP
    have hδP : δ' * P = ε := div_mul_cancel₀ ε hP.ne'
    have hδCg : δ' * Cg ≤ ε := by
      rw [← hδP]
      refine mul_le_mul_of_nonneg_left ?_ hδ'.le
      nlinarith [abs_nonneg CΓ]
    have hδH : (δ' + δ' * |CΓ|) * Cg * Cg ≤ ε := by
      rw [← hδP]
      have h1 : (δ' + δ' * |CΓ|) * Cg * Cg = δ' * ((1 + |CΓ|) * Cg ^ 2) := by ring
      rw [h1]
      refine mul_le_mul_of_nonneg_left ?_ hδ'.le
      rw [hPdef, mul_comm ((1 + Cg) ^ 2)]
      exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    obtain ⟨k0, hk0⟩ := hchart y₀ Kc hKc hKct hKcr δ' hδ'
    refine ⟨ψ.source ∩ ψ ⁻¹' Metric.ball (ψ y₀) (r / 2),
      inter_mem (extChartAt_source_mem_nhds y₀)
        ((continuousAt_extChartAt y₀).preimage_mem_nhds
          (Metric.ball_mem_nhds _ (half_pos hr))), ?_⟩
    filter_upwards [eventually_ge_atTop k0] with k hk y hyN hyB
    obtain ⟨hysrc, hyball⟩ := hyN
    set z := ψ y with hz
    have hzK : z ∈ Kc := Metric.ball_subset_closedBall hyball
    have hyU : y ∈ U := hBU hyB
    have hysrc' : y ∈ (chartAt H y₀).source := by rw [← extChartAt_source (I := I)]; exact hysrc
    have hyg : y ∈ chartLeviCivitaGoodSet (I := I) y₀ :=
      ⟨⟨hysrc, by rw [TangentBundle.trivializationAt_baseSet]; exact hysrc'⟩, hKcint hzK⟩
    have hfC2 : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (fun y => us k y - u y) y :=
      ((hus k y).of_le (by simp)).sub (hu.contMDiffAt (hU.mem_nhds hyU))
    set D : E → ℝ := fun z => us k (ψ.symm z) - v (ψ.symm z) with hDdef
    have hev : ((fun y => us k y - u y) ∘ ψ.symm) =ᶠ[𝓝 z] D := by
      filter_upwards [hΩo.mem_nhds (hKcΩ hzK)] with z' hz'
      change us k (ψ.symm z') - u (ψ.symm z') = us k (ψ.symm z') - v (ψ.symm z')
      rw [hvu hz'.2]
    have hD1 : ‖fderiv ℝ ((fun y => us k y - u y) ∘ ψ.symm) z‖ ≤ δ' := by
      rw [hev.fderiv_eq, ← norm_iteratedFDeriv_one]
      exact hk0 k hk 1 (by norm_num) z hzK
    have hD2 : ‖fderiv ℝ (fderiv ℝ ((fun y => us k y - u y) ∘ ψ.symm)) z‖ ≤ δ' := by
      rw [hev.fderiv.fderiv_eq, ← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
      exact hk0 k hk 2 le_rfl z hzK
    have hCΓz : christoffelBound g y₀ z ≤ |CΓ| := by
      have h := hCΓ z hzK
      rw [Real.norm_eq_abs] at h
      exact (le_abs_self _).trans (h.trans (le_abs_self _))
    have hgy : ∀ X : TangentSpace I y, ‖trivToE I y₀ y X‖ ≤ Cg * Real.sqrt (g.inner y X X) :=
      hCg y ⟨z, hzK, ψ.left_inv hysrc⟩
    refine ⟨fun X => ?_, fun X Y => ?_⟩
    · have hfd : MDiffAt (fun y => us k y - u y) y := hfC2.mdifferentiableAt (by norm_num)
      calc |mvfderiv I (fun y => us k y - u y) y X|
          ≤ ‖fderiv ℝ ((fun y => us k y - u y) ∘ ψ.symm) z‖ * ‖trivToE I y₀ y X‖ :=
            abs_mvfderiv_le_chart hysrc' (hKcint hzK) hfd X
        _ ≤ δ' * (Cg * Real.sqrt (g.inner y X X)) :=
            mul_le_mul hD1 (hgy X) (norm_nonneg _) hδ'.le
        _ ≤ ε * Real.sqrt (g.inner y X X) := by
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right hδCg (Real.sqrt_nonneg _)
    · have hcb := christoffelBound_nonneg g y₀ z
      calc |(CovariantDerivative.trivial I M ℝ).hessian (LeviCivita g)
              (fun y => us k y - u y) y X Y|
          ≤ (‖fderiv ℝ (fderiv ℝ ((fun y => us k y - u y) ∘ ψ.symm)) z‖ +
              ‖fderiv ℝ ((fun y => us k y - u y) ∘ ψ.symm) z‖ * christoffelBound g y₀ z) *
              ‖trivToE I y₀ y X‖ * ‖trivToE I y₀ y Y‖ := abs_hessian_le_chart g hyg hfC2 X Y
        _ ≤ (δ' + δ' * |CΓ|) * (Cg * Real.sqrt (g.inner y X X)) *
              (Cg * Real.sqrt (g.inner y Y Y)) := by
            gcongr
            · exact hgy X
            · exact hgy Y
        _ = ((δ' + δ' * |CΓ|) * Cg * Cg) * Real.sqrt (g.inner y X X) *
              Real.sqrt (g.inner y Y Y) := by ring
        _ ≤ ε * Real.sqrt (g.inner y X X) * Real.sqrt (g.inner y Y Y) := by
            gcongr
  obtain ⟨j, hj1, hj2⟩ := (hC0.and (eventually_forall_of_isCompact_of_local hB hloc)).exists
  exact ⟨us j, hus j, fun y hy => ⟨hj1 y hy, (hj2 y hy hy).1, (hj2 y hy hy).2⟩⟩

end DifferentialGeometry.Geometry.Connection
