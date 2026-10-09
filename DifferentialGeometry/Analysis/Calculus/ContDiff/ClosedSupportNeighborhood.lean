import DifferentialGeometry.Analysis.Calculus.ContDiff.Support
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Smooth extension on a neighbourhood of the image (CFS18)

Source: `docs/geometrization/blueprint/master207B.tex:3010–3051`, lemma
`lem:fibration-closed-support-neighborhood` (CFS18), its proof (`:3029–3043`) and the closing
paragraph (`:3044–3051`) with the counterexample showing that a nonzero-value condition cannot
replace the closed-support hypothesis.

Write `supp_O ψ = closure (support ψ ∩ O) ∩ O` for the support of `ψ` relative to `O`.

* `exists_isOpen_relative_tsupport_subset` (tier 1): if `K ⊆ O` and `K ∩ supp_O ψ ⊆ U` with
  `O`, `U` open, then some open `V` with `K ⊆ V ⊆ O` has `supp_V ψ ⊆ U`. The blueprint's
  `V = O \ (supp_O ψ \ U)` is used.
* `contDiffOn_piecewise_closedSupport_adjustment` (tier 2): if `supp_V ψ ⊆ U`, the piecewise map
  `z ↦ z + ψ z • h z` on `U`, `z ↦ z` off `U`, is `C^n` on `V` as soon as `ψ` is `C^n` on `V`
  and `h` is `C^n` on `V ∩ U`.
* `exists_contDiffOn_closedSupport_adjustment`: the two tiers together (the CFS18 statement).
* Tier 3 (factored case): `exists_preimage_isOpen_relative_tsupport_subset`,
  `piecewise_adjustment_comp_eq` and `exists_contDiffOn_closedSupport_adjustment_factor` for a
  continuous linear split surjection `π : H → Q` with section `ι`; the orthogonal projection
  onto a closed subspace is `orthogonal_piecewise_adjustment`.

Two consumers record why the hypotheses are as they are:

* `not_exists_isOpen_relative_tsupport_subset_of_not_isOpen`: openness of `U` cannot be dropped
  from tier 1 (`ψ = id` on `ℝ`, `K = U = {0}`). The blueprint states `U` open; the plan's draft
  statement omitted `hU`.
* `nonzeroValue_insufficient_of_flat` / `expNegInvGlue_nonzeroValue_insufficient`: the
  blueprint's counterexample (`O = ℝ`, `K = {0}`, `U = (0, ∞)`, `ψ` positive exactly on
  `(0, ∞)`). The nonzero values of `ψ` on `K` lie in `U` vacuously, but the closed-support
  hypothesis fails, no `V` as in tier 1 exists, and for the smooth `h = ψ⁻¹` on `U` the piecewise
  map is discontinuous at `0`, so it is not even `C^0` on any neighbourhood of `K`. The blueprint
  uses `e^{-1/t²}`; the general lemma only needs `ψ = 0` on `(-∞, 0]` and `ψ > 0` on `(0, ∞)`, and
  the instance uses Mathlib's smooth `expNegInvGlue` (`e^{-1/t}`), which has the same support.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

/-! ## Tier 1: an open neighbourhood with relatively closed support inside `U` -/

/-- CFS18, first sentence: shrinking `O` to `V = O \ (supp_O ψ \ U)` keeps `K` and puts the
relative closed support inside `U`. Only the topology of `H` is used. -/
theorem exists_isOpen_relative_tsupport_subset {H : Type*} [TopologicalSpace H]
    {O U K : Set H} (hO : IsOpen O) (hU : IsOpen U) (hKO : K ⊆ O) {ψ : H → ℝ}
    (hsupp : K ∩ (closure (support ψ ∩ O) ∩ O) ⊆ U) :
    ∃ V : Set H, IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ closure (support ψ ∩ V) ∩ V ⊆ U := by
  refine ⟨O ∩ (closure (support ψ ∩ O) ∩ Uᶜ)ᶜ, ?_, ?_, inter_subset_left, ?_⟩
  · exact hO.inter (isClosed_closure.inter hU.isClosed_compl).isOpen_compl
  · intro k hk
    exact ⟨hKO hk, fun hk' => hk'.2 (hsupp ⟨hk, hk'.1, hKO hk⟩)⟩
  · rintro x ⟨hxcl, _, hxnot⟩
    by_contra hxU
    exact hxnot ⟨closure_mono (inter_subset_inter_right _ inter_subset_left) hxcl, hxU⟩

/-- Off `U`, inside `V`, the function vanishes when the relative closed support lies in `U`. -/
theorem eq_zero_of_relative_tsupport_subset {H : Type*} [TopologicalSpace H]
    {U V : Set H} {ψ : H → ℝ} (hsupp : closure (support ψ ∩ V) ∩ V ⊆ U)
    {z : H} (hzV : z ∈ V) (hzU : z ∉ U) : ψ z = 0 := by
  by_contra hne
  exact hzU (hsupp ⟨subset_closure ⟨hne, hzV⟩, hzV⟩)

/-! ## Tier 2: smoothness of the piecewise adjustment -/

section Adjustment

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- CFS18, second sentence: the adjustment `z + ψ z • h z` on `V ∩ U`, the identity on `V \ U`,
is `C^n` on `V`. Every point of `V \ U` has a neighbourhood in `V` on which `ψ` vanishes, so the
map is the identity there. -/
theorem contDiffOn_piecewise_closedSupport_adjustment
    {n : ℕ∞ω} {U V : Set H} [∀ z, Decidable (z ∈ U)] (hU : IsOpen U) (hV : IsOpen V)
    {ψ : H → ℝ} {h : H → H}
    (hψ : ContDiffOn ℝ n ψ V) (hh : ContDiffOn ℝ n h (V ∩ U))
    (hsupp : closure (support ψ ∩ V) ∩ V ⊆ U) :
    ContDiffOn ℝ n (U.piecewise (fun z => z + ψ z • h z) id) V := by
  intro x hxV
  by_cases hxU : x ∈ U
  · have hmem : V ∩ U ∈ 𝓝 x := (hV.inter hU).mem_nhds ⟨hxV, hxU⟩
    have hf : ContDiffAt ℝ n (fun z => z + ψ z • h z) x :=
      (contDiffOn_id.add ((hψ.mono inter_subset_left).smul hh)).contDiffAt hmem
    have heq : U.piecewise (fun z => z + ψ z • h z) id =ᶠ[𝓝 x] (fun z => z + ψ z • h z) := by
      filter_upwards [hU.mem_nhds hxU] with z hz
      exact piecewise_eq_of_mem _ _ _ hz
    exact (hf.congr_of_eventuallyEq heq).contDiffWithinAt
  · have hxcl : x ∉ closure (support ψ ∩ V) := fun hcl => hxU (hsupp ⟨hcl, hxV⟩)
    have heq : U.piecewise (fun z => z + ψ z • h z) id =ᶠ[𝓝 x] id := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxcl, hV.mem_nhds hxV]
        with z hz hzV
      by_cases hzU : z ∈ U
      · have hψz : ψ z = 0 := by
          by_contra hne
          exact hz (subset_closure ⟨hne, hzV⟩)
        simp [piecewise_eq_of_mem _ _ _ hzU, hψz]
      · simp [piecewise_eq_of_notMem _ _ _ hzU]
    exact (contDiffAt_id.congr_of_eventuallyEq heq).contDiffWithinAt

/-- The piecewise adjustment is the identity at every point where `ψ` vanishes. -/
theorem piecewise_adjustment_eq_self_of_eq_zero {U : Set H} [∀ z, Decidable (z ∈ U)]
    {ψ : H → ℝ} {h : H → H} {z : H} (hz : ψ z = 0) :
    U.piecewise (fun z => z + ψ z • h z) id z = z := by
  by_cases hzU : z ∈ U
  · simp [piecewise_eq_of_mem _ _ _ hzU, hz]
  · simp [piecewise_eq_of_notMem _ _ _ hzU]

/-- CFS18 as one statement: from `K ∩ supp_O ψ ⊆ U` (relative closed support) one gets an open
`V`, `K ⊆ V ⊆ O`, on which the piecewise adjustment is `C^n`; on `V \ U` the cutoff vanishes and
the adjustment is the identity, and on `V ∩ U` it is the given formula. -/
theorem exists_contDiffOn_closedSupport_adjustment
    {n : ℕ∞ω} {O U K : Set H} [∀ z, Decidable (z ∈ U)]
    (hO : IsOpen O) (hU : IsOpen U) (hKO : K ⊆ O) {ψ : H → ℝ} {h : H → H}
    (hψ : ContDiffOn ℝ n ψ O) (hh : ContDiffOn ℝ n h (O ∩ U))
    (hsupp : K ∩ (closure (support ψ ∩ O) ∩ O) ⊆ U) :
    ∃ V : Set H, IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧
      closure (support ψ ∩ V) ∩ V ⊆ U ∧
      ContDiffOn ℝ n (U.piecewise (fun z => z + ψ z • h z) id) V ∧
      (∀ z ∈ V, z ∉ U → ψ z = 0) ∧
      EqOn (U.piecewise (fun z => z + ψ z • h z) id) id (V \ U) ∧
      EqOn (U.piecewise (fun z => z + ψ z • h z) id) (fun z => z + ψ z • h z) (V ∩ U) := by
  obtain ⟨V, hV, hKV, hVO, hVsupp⟩ := exists_isOpen_relative_tsupport_subset hO hU hKO hsupp
  refine ⟨V, hV, hKV, hVO, hVsupp, ?_, ?_, ?_, ?_⟩
  · exact contDiffOn_piecewise_closedSupport_adjustment hU hV (hψ.mono hVO)
      (hh.mono (inter_subset_inter_left _ hVO)) hVsupp
  · intro z hzV hzU
    exact eq_zero_of_relative_tsupport_subset hVsupp hzV hzU
  · intro z hz
    exact piecewise_eq_of_notMem _ _ _ hz.2
  · intro z hz
    exact piecewise_eq_of_mem _ _ _ hz.2

end Adjustment

/-! ## Tier 3: the factored case -/

section Factored

variable {H Q : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]

/-- A continuous linear map with a continuous linear section is open. -/
theorem isOpenMap_of_rightInverse_continuousLinearMap (π : H →L[ℝ] Q) (ι : Q →L[ℝ] H)
    (hπι : ∀ q, π (ι q) = q) : IsOpenMap π :=
  IsOpenMap.of_sections fun x =>
    ⟨fun q => x + ι (q - π x), (by fun_prop : Continuous fun q => x + ι (q - π x)).continuousAt,
      by simp, fun q => by simp [hπι]⟩

/-- The support of `χ ∘ π` relative to `π⁻¹ O_Q` is the preimage of the support of `χ` relative
to `O_Q` (`π` open, continuous). -/
theorem preimage_relative_tsupport_eq (π : H →L[ℝ] Q) (ι : Q →L[ℝ] H)
    (hπι : ∀ q, π (ι q) = q) (χ : Q → ℝ) (OQ : Set Q) :
    closure (support (χ ∘ π) ∩ π ⁻¹' OQ) ∩ π ⁻¹' OQ =
      π ⁻¹' (closure (support χ ∩ OQ) ∩ OQ) := by
  rw [support_comp_eq_preimage, ← preimage_inter,
    ← (isOpenMap_of_rightInverse_continuousLinearMap π ι hπι).preimage_closure_eq_closure_preimage
      π.continuous, preimage_inter]

/-- CFS18, factored case, tier 1: with `O = π⁻¹ O_Q`, `U = π⁻¹ T` and `ψ = χ ∘ π`, the
neighbourhood `V` can be taken as `π⁻¹ V_Q` for an open `V_Q ⊆ O_Q` with `supp_{V_Q} χ ⊆ T`. -/
theorem exists_preimage_isOpen_relative_tsupport_subset (π : H →L[ℝ] Q) (ι : Q →L[ℝ] H)
    (hπι : ∀ q, π (ι q) = q) {OQ T : Set Q} {K : Set H} (hOQ : IsOpen OQ) (hT : IsOpen T)
    (hKO : K ⊆ π ⁻¹' OQ) {χ : Q → ℝ}
    (hsupp : K ∩ (closure (support (χ ∘ π) ∩ π ⁻¹' OQ) ∩ π ⁻¹' OQ) ⊆ π ⁻¹' T) :
    ∃ VQ : Set Q, IsOpen VQ ∧ K ⊆ π ⁻¹' VQ ∧ VQ ⊆ OQ ∧
      closure (support χ ∩ VQ) ∩ VQ ⊆ T ∧
      closure (support (χ ∘ π) ∩ π ⁻¹' VQ) ∩ π ⁻¹' VQ ⊆ π ⁻¹' T := by
  rw [preimage_relative_tsupport_eq π ι hπι] at hsupp
  have hsuppQ : π '' K ∩ (closure (support χ ∩ OQ) ∩ OQ) ⊆ T := by
    rintro _ ⟨⟨k, hk, rfl⟩, hkcl⟩
    exact hsupp ⟨hk, hkcl⟩
  obtain ⟨VQ, hVQ, hKVQ, hVQO, hVQsupp⟩ :=
    exists_isOpen_relative_tsupport_subset hOQ hT (image_subset_iff.mpr hKO) hsuppQ
  refine ⟨VQ, hVQ, image_subset_iff.mp hKVQ, hVQO, hVQsupp, ?_⟩
  rw [preimage_relative_tsupport_eq π ι hπι]
  exact preimage_mono hVQsupp

/-- CFS18, factored case, the formula: with `ψ = χ ∘ π` and `h = ι ∘ h_Q ∘ π`, the adjustment is
`z ↦ z + ι (Ψ_Q (π z) - π z)` where `Ψ_Q` is the adjustment on `Q`. -/
theorem piecewise_adjustment_comp_eq (π : H →L[ℝ] Q) (ι : Q →L[ℝ] H)
    {T : Set Q} [∀ q, Decidable (q ∈ T)]
    [∀ z, Decidable (z ∈ π ⁻¹' T)] (χ : Q → ℝ) (hQ : Q → Q) (z : H) :
    (π ⁻¹' T).piecewise (fun z => z + (χ ∘ π) z • (ι ∘ hQ ∘ π) z) id z =
      z + ι (T.piecewise (fun q => q + χ q • hQ q) id (π z) - π z) := by
  by_cases hz : π z ∈ T
  · rw [piecewise_eq_of_mem _ _ _ (show z ∈ π ⁻¹' T from hz), piecewise_eq_of_mem _ _ _ hz]
    simp
  · rw [piecewise_eq_of_notMem _ _ _ (show z ∉ π ⁻¹' T from hz),
      piecewise_eq_of_notMem _ _ _ hz]
    simp

/-- The factored adjustment covers the adjustment on `Q` and fixes the `ker π` component
`z - ι (π z)`. -/
theorem piecewise_adjustment_comp_factor (π : H →L[ℝ] Q) (ι : Q →L[ℝ] H)
    (hπι : ∀ q, π (ι q) = q) {T : Set Q} [∀ q, Decidable (q ∈ T)]
    [∀ z, Decidable (z ∈ π ⁻¹' T)] (χ : Q → ℝ) (hQ : Q → Q) (z : H) :
    π ((π ⁻¹' T).piecewise (fun z => z + (χ ∘ π) z • (ι ∘ hQ ∘ π) z) id z) =
        T.piecewise (fun q => q + χ q • hQ q) id (π z) ∧
      (π ⁻¹' T).piecewise (fun z => z + (χ ∘ π) z • (ι ∘ hQ ∘ π) z) id z -
          ι (π ((π ⁻¹' T).piecewise (fun z => z + (χ ∘ π) z • (ι ∘ hQ ∘ π) z) id z)) =
        z - ι (π z) := by
  have hformula := piecewise_adjustment_comp_eq (T := T) π ι χ hQ z
  have hπ : π ((π ⁻¹' T).piecewise (fun z => z + (χ ∘ π) z • (ι ∘ hQ ∘ π) z) id z) =
      T.piecewise (fun q => q + χ q • hQ q) id (π z) := by
    rw [hformula, map_add, hπι, add_sub_cancel]
  refine ⟨hπ, ?_⟩
  rw [hπ, hformula, map_sub]
  abel

/-- CFS18, factored case, smoothness: the neighbourhood is `π⁻¹ V_Q` and the factored adjustment
is `C^n` on it. -/
theorem exists_contDiffOn_closedSupport_adjustment_factor (π : H →L[ℝ] Q) (ι : Q →L[ℝ] H)
    (hπι : ∀ q, π (ι q) = q) {n : ℕ∞ω} {OQ T : Set Q} {K : Set H}
    [∀ z, Decidable (z ∈ π ⁻¹' T)] (hOQ : IsOpen OQ) (hT : IsOpen T)
    (hKO : K ⊆ π ⁻¹' OQ) {χ : Q → ℝ} {hQ : Q → Q}
    (hχ : ContDiffOn ℝ n χ OQ) (hhQ : ContDiffOn ℝ n hQ (OQ ∩ T))
    (hsupp : K ∩ (closure (support (χ ∘ π) ∩ π ⁻¹' OQ) ∩ π ⁻¹' OQ) ⊆ π ⁻¹' T) :
    ∃ VQ : Set Q, IsOpen VQ ∧ K ⊆ π ⁻¹' VQ ∧ VQ ⊆ OQ ∧
      closure (support χ ∩ VQ) ∩ VQ ⊆ T ∧
      ContDiffOn ℝ n
        ((π ⁻¹' T).piecewise (fun z => z + (χ ∘ π) z • (ι ∘ hQ ∘ π) z) id) (π ⁻¹' VQ) := by
  obtain ⟨VQ, hVQ, hKVQ, hVQO, hVQsupp, hVsupp⟩ :=
    exists_preimage_isOpen_relative_tsupport_subset π ι hπι hOQ hT hKO hsupp
  refine ⟨VQ, hVQ, hKVQ, hVQO, hVQsupp, ?_⟩
  have hψ : ContDiffOn ℝ n (χ ∘ π) (π ⁻¹' VQ) :=
    (hχ.mono hVQO).comp π.contDiff.contDiffOn (mapsTo_preimage _ _)
  have hh : ContDiffOn ℝ n (ι ∘ hQ ∘ π) (π ⁻¹' VQ ∩ π ⁻¹' T) := by
    refine ι.contDiff.comp_contDiffOn ?_
    exact (hhQ.mono (inter_subset_inter_left _ hVQO)).comp π.contDiff.contDiffOn
      (fun z hz => hz)
  exact contDiffOn_piecewise_closedSupport_adjustment (hT.preimage π.continuous)
    (hVQ.preimage π.continuous) hψ hh hVsupp

end Factored

section Orthogonal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- CFS18, factored case for an orthogonal projection `π` onto a closed subspace `Q`: the
adjustment is `(q, q⊥) ↦ (q + χ q • h_Q q, q⊥)`, that is, it covers the adjustment on `Q` and
fixes the `Qᗮ` component. -/
theorem orthogonal_piecewise_adjustment (Q : Submodule ℝ E) [Q.HasOrthogonalProjection]
    {T : Set Q} [∀ q, Decidable (q ∈ T)]
    [∀ z, Decidable (z ∈ Q.orthogonalProjectionOnto ⁻¹' T)] (χ : Q → ℝ) (hQ : Q → Q) (z : E) :
    Q.orthogonalProjectionOnto ((Q.orthogonalProjectionOnto ⁻¹' T).piecewise
        (fun z => z + (χ ∘ Q.orthogonalProjectionOnto) z •
          (Q.subtypeL ∘ hQ ∘ Q.orthogonalProjectionOnto) z) id z) =
        T.piecewise (fun q => q + χ q • hQ q) id (Q.orthogonalProjectionOnto z) ∧
      (Q.orthogonalProjectionOnto ⁻¹' T).piecewise
          (fun z => z + (χ ∘ Q.orthogonalProjectionOnto) z •
            (Q.subtypeL ∘ hQ ∘ Q.orthogonalProjectionOnto) z) id z -
          Q.starProjection ((Q.orthogonalProjectionOnto ⁻¹' T).piecewise
            (fun z => z + (χ ∘ Q.orthogonalProjectionOnto) z •
              (Q.subtypeL ∘ hQ ∘ Q.orthogonalProjectionOnto) z) id z) =
        z - Q.starProjection z :=
  piecewise_adjustment_comp_factor Q.orthogonalProjectionOnto Q.subtypeL
    (fun q => Q.orthogonalProjectionOnto_mem_subspace_eq_self q) χ hQ z

end Orthogonal

/-! ## Consumers -/

section Consumers

/-- Openness of `U` cannot be dropped from tier 1: for `ψ = id` on `ℝ` and `K = U = {0}` the
hypothesis `K ∩ supp ψ ⊆ U` holds, but no open `V ∋ 0` has `supp_V ψ ⊆ {0}`. -/
theorem not_exists_isOpen_relative_tsupport_subset_of_not_isOpen :
    ({0} : Set ℝ) ∩ (closure (support (fun t : ℝ => t) ∩ univ) ∩ univ) ⊆ {0} ∧
      ¬ ∃ V : Set ℝ, IsOpen V ∧ ({0} : Set ℝ) ⊆ V ∧
        closure (support (fun t : ℝ => t) ∩ V) ∩ V ⊆ {0} := by
  refine ⟨fun x hx => hx.1, ?_⟩
  rintro ⟨V, hV, h0V, hsub⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV 0 (h0V rfl)
  have hmem : ε / 2 ∈ V := hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    exact half_lt_self hε)
  have hne : ε / 2 ≠ 0 := (half_pos hε).ne'
  exact hne (hsub ⟨subset_closure ⟨hne, hmem⟩, hmem⟩)

/-- The blueprint's counterexample (`master207B.tex:3046–3050`) in general form: for `ψ` vanishing
on `(-∞, 0]` and positive on `(0, ∞)`, `O = ℝ`, `K = {0}`, `U = (0, ∞)`,

1. every nonzero value of `ψ` on `K` lies in `U` (vacuously),
2. the closed-support hypothesis `K ∩ supp ψ ⊆ U` fails,
3. no open `V ⊇ K` has `supp_V ψ ⊆ U`, and
4. for `h = ψ⁻¹`, which is `C^n` on `U` whenever `ψ` is, the piecewise adjustment is not
   continuous on any open `V ∋ 0`: it is `t + 1` for `t > 0` and `t` for `t ≤ 0`.

So the nonzero-value condition cannot replace the closed-support hypothesis in either tier. -/
theorem nonzeroValue_insufficient_of_flat {ψ : ℝ → ℝ} (hψ0 : ∀ t ≤ 0, ψ t = 0)
    (hψpos : ∀ t, 0 < t → 0 < ψ t) [∀ t, Decidable (t ∈ Ioi (0 : ℝ))] :
    (∀ t ∈ ({0} : Set ℝ), ψ t ≠ 0 → t ∈ Ioi (0 : ℝ)) ∧
      ¬ ({0} : Set ℝ) ∩ (closure (support ψ ∩ univ) ∩ univ) ⊆ Ioi 0 ∧
      (¬ ∃ V : Set ℝ, IsOpen V ∧ ({0} : Set ℝ) ⊆ V ∧ closure (support ψ ∩ V) ∩ V ⊆ Ioi 0) ∧
      ∀ V : Set ℝ, IsOpen V → (0 : ℝ) ∈ V →
        ¬ ContinuousOn ((Ioi (0 : ℝ)).piecewise (fun t => t + ψ t • (ψ t)⁻¹) id) V := by
  -- `0` is in the closure of `support ψ ∩ V` for every neighbourhood `V` of `0`.
  have hcl : ∀ V : Set ℝ, IsOpen V → (0 : ℝ) ∈ V → (0 : ℝ) ∈ closure (support ψ ∩ V) := by
    intro V hV h0V
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hV 0 h0V
    set t := min (ε / 2) (δ / 2) with ht
    have htpos : 0 < t := lt_min (half_pos hε) (half_pos hδ)
    have htδ : t < δ := (min_le_right _ _).trans_lt (half_lt_self hδ)
    have htε : t < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
    refine ⟨t, ⟨(hψpos t htpos).ne', hball ?_⟩, ?_⟩
    · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos htpos]
      exact htδ
    · rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos htpos]
      exact htε
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro t rfl ht
    exact (ht (hψ0 0 le_rfl)).elim
  · intro hsub
    have h0 : (0 : ℝ) ∈ ({0} : Set ℝ) ∩ (closure (support ψ ∩ univ) ∩ univ) :=
      ⟨rfl, hcl univ isOpen_univ (mem_univ 0), mem_univ 0⟩
    exact (lt_irrefl (0 : ℝ)) (hsub h0)
  · rintro ⟨V, hV, h0V, hsub⟩
    exact (lt_irrefl (0 : ℝ)) (hsub ⟨hcl V hV (h0V rfl), h0V rfl⟩)
  · intro V hV h0V hcont
    have hval0 : (Ioi (0 : ℝ)).piecewise (fun t => t + ψ t • (ψ t)⁻¹) id 0 = 0 :=
      piecewise_eq_of_notMem _ _ _ (show (0 : ℝ) ∉ Ioi 0 from lt_irrefl (0 : ℝ))
    have hvalpos : ∀ t, 0 < t →
        (Ioi (0 : ℝ)).piecewise (fun t => t + ψ t • (ψ t)⁻¹) id t = t + 1 := by
      intro t ht
      rw [piecewise_eq_of_mem _ _ _ (show t ∈ Ioi (0 : ℝ) from ht), smul_eq_mul,
        mul_inv_cancel₀ (hψpos t ht).ne']
    have hcont0 := (hcont 0 h0V).continuousAt (hV.mem_nhds h0V)
    rw [Metric.continuousAt_iff] at hcont0
    obtain ⟨δ, hδ, hδball⟩ := hcont0 (1 / 2) (by norm_num)
    set t := min (δ / 2) (1 / 2) with ht
    have htpos : 0 < t := lt_min (half_pos hδ) (by norm_num)
    have htδ : dist t 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos htpos]
      exact (min_le_left _ _).trans_lt (half_lt_self hδ)
    have hfar := hδball htδ
    rw [hvalpos t htpos, hval0, Real.dist_eq, sub_zero, abs_of_pos (by linarith)] at hfar
    linarith

/-- The counterexample instance with Mathlib's smooth flat function `expNegInvGlue`
(`e^{-1/t}` for `t > 0`, `0` otherwise). `ψ` is `C^∞` and `h = ψ⁻¹` is `C^∞` on `U = (0, ∞)`, so
all smoothness hypotheses of tier 2 hold except the closed-support one, and the conclusion fails. -/
theorem expNegInvGlue_nonzeroValue_insufficient [∀ t, Decidable (t ∈ Ioi (0 : ℝ))] :
    ContDiff ℝ ∞ expNegInvGlue ∧
      ContDiffOn ℝ ∞ (fun t => (expNegInvGlue t)⁻¹) (Ioi 0) ∧
      (∀ t ∈ ({0} : Set ℝ), expNegInvGlue t ≠ 0 → t ∈ Ioi (0 : ℝ)) ∧
      ¬ ({0} : Set ℝ) ∩ (closure (support expNegInvGlue ∩ univ) ∩ univ) ⊆ Ioi 0 ∧
      (¬ ∃ V : Set ℝ, IsOpen V ∧ ({0} : Set ℝ) ⊆ V ∧
        closure (support expNegInvGlue ∩ V) ∩ V ⊆ Ioi 0) ∧
      ∀ V : Set ℝ, IsOpen V → (0 : ℝ) ∈ V →
        ¬ ContDiffOn ℝ 0
          ((Ioi (0 : ℝ)).piecewise (fun t => t + expNegInvGlue t • (expNegInvGlue t)⁻¹) id) V := by
  obtain ⟨h1, h2, h3, h4⟩ := nonzeroValue_insufficient_of_flat (ψ := expNegInvGlue)
    (fun t ht => expNegInvGlue.zero_of_nonpos ht) (fun t ht => expNegInvGlue.pos_of_pos ht)
  refine ⟨expNegInvGlue.contDiff, ?_, h1, h2, h3, fun V hV h0V hsmooth =>
    h4 V hV h0V hsmooth.continuousOn⟩
  exact expNegInvGlue.contDiff.contDiffOn.inv fun t ht => (expNegInvGlue.pos_of_pos ht).ne'

/-- A positive instance of the factored case on `ℝ × ℝ` with `π = fst`, `ι = inl`: the flat cutoff
`χ = expNegInvGlue`, the target `T = (-1, ∞)` and `h_Q q = (q + 1)⁻¹`, which blows up at the edge
of `T`. Along `K = {0} × ℝ` the adjustment `(q, p) ↦ (q + χ q (q + 1)⁻¹, p)` is smooth on a
neighbourhood `π⁻¹ V_Q`, and it fixes the second coordinate. -/
theorem prod_fst_closedSupport_adjustment_example
    [∀ z, Decidable (z ∈ (ContinuousLinearMap.fst ℝ ℝ ℝ) ⁻¹' Ioi (-1 : ℝ))] :
    ∃ VQ : Set ℝ, IsOpen VQ ∧ ({0} ×ˢ univ : Set (ℝ × ℝ)) ⊆ Prod.fst ⁻¹' VQ ∧
      ContDiffOn ℝ ∞
        (((ContinuousLinearMap.fst ℝ ℝ ℝ) ⁻¹' Ioi (-1 : ℝ)).piecewise
          (fun z => z + (expNegInvGlue ∘ ContinuousLinearMap.fst ℝ ℝ ℝ) z •
            (ContinuousLinearMap.inl ℝ ℝ ℝ ∘ (fun q : ℝ => (q + 1)⁻¹) ∘
              ContinuousLinearMap.fst ℝ ℝ ℝ) z) id)
        (Prod.fst ⁻¹' VQ) ∧
      ∀ z : ℝ × ℝ,
        (((ContinuousLinearMap.fst ℝ ℝ ℝ) ⁻¹' Ioi (-1 : ℝ)).piecewise
          (fun z => z + (expNegInvGlue ∘ ContinuousLinearMap.fst ℝ ℝ ℝ) z •
            (ContinuousLinearMap.inl ℝ ℝ ℝ ∘ (fun q : ℝ => (q + 1)⁻¹) ∘
              ContinuousLinearMap.fst ℝ ℝ ℝ) z) id z).2 = z.2 := by
  classical
  have hπι : ∀ q : ℝ, ContinuousLinearMap.fst ℝ ℝ ℝ (ContinuousLinearMap.inl ℝ ℝ ℝ q) = q :=
    fun q => rfl
  have hhQ : ContDiffOn ℝ ∞ (fun q : ℝ => (q + 1)⁻¹) (univ ∩ Ioi (-1)) := by
    refine (contDiffOn_id.add contDiffOn_const).inv ?_
    intro q hq
    have : (-1 : ℝ) < q := hq.2
    simp only [id]
    linarith
  obtain ⟨VQ, hVQ, hKVQ, -, -, hsmooth⟩ :=
    exists_contDiffOn_closedSupport_adjustment_factor (K := ({0} ×ˢ univ : Set (ℝ × ℝ)))
      (OQ := univ) (T := Ioi (-1 : ℝ))
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (ContinuousLinearMap.inl ℝ ℝ ℝ) hπι isOpen_univ
      isOpen_Ioi (fun _ _ => mem_univ _) expNegInvGlue.contDiff.contDiffOn hhQ
      (by
        rintro z ⟨⟨hz, -⟩, -⟩
        change (-1 : ℝ) < z.1
        rw [show z.1 = 0 from hz]
        norm_num)
  refine ⟨VQ, hVQ, hKVQ, hsmooth, fun z => ?_⟩
  have hfix := (piecewise_adjustment_comp_factor (T := Ioi (-1 : ℝ)) (ContinuousLinearMap.fst ℝ ℝ ℝ)
    (ContinuousLinearMap.inl ℝ ℝ ℝ) hπι expNegInvGlue (fun q : ℝ => (q + 1)⁻¹) z).2
  have h2 := congrArg Prod.snd hfix
  simpa using h2

end Consumers

end DifferentialGeometry.Analysis
