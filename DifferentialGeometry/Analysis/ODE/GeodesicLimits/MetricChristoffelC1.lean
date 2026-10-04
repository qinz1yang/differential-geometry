import DifferentialGeometry.Analysis.ODE.GeodesicLimits.ShortGeodesics
import DifferentialGeometry.Geometry.Geodesic.Equation.MetricSprayFiniteRegularity
import DifferentialGeometry.Analysis.Calculus.MapConvergence.FiniteComposition
import DifferentialGeometry.Analysis.Calculus.MapConvergence.FiniteRegularity
import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.CoefficientPullback

/-!
# `C²` convergence of metric coefficients gives `C¹` convergence of Christoffel fields (LFR09)

Adapter (1) of LFR09 (lane CM-L3): for chart metric coefficients `b i → b∞` in `C²` on the compact
subsets of an open set `U` (all coercive on `U`), the Christoffel fields
`x ↦ raisedKoszulOp (b x) (fderiv b x)` (the second component of the tree's `metricSpray b`)
converge in `C¹` on compact subsets of `U`.

* `mapCPConvergenceOn_raisedKoszulOp_of_C2`: the adapter (composition of the `C¹` map
  `(B, D) ↦ raisedKoszulOp B D`, on the open set of coercive `B`, with the `C¹`-convergent jets
  `x ↦ (b x, Db x)`; tree `MapCPConvergenceOn.comp_finite`).
* `exists_short_geodesics_of_metric_C2`: the LFR09 chart kernel in coefficient form — `C²`
  metrics `b i → b∞` in `C²`: uniform short joining geodesics of the `b i` (no `C³` anywhere).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Metric
open scoped Topology NNReal

namespace DifferentialGeometry.Analysis.ODE.GeodesicLimits

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.MetricKoszul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ContinuousDualEquiv E]

omit [FiniteDimensional ℝ E] [ContinuousDualEquiv E] in
/-- Order-one convergence of the first jets `x ↦ (b x, Db x)` from order-two convergence. -/
theorem mapCPConvergenceOn_jet_of_C2 {U : Set E} (hU : IsOpen U)
    {b : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ} {bInf : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hb : ∀ i, ContDiffOn ℝ 2 (b i) U) (hbInf : ContDiffOn ℝ 2 bInf U)
    {K : Set E} (hKU : K ⊆ U) (hconv : MapCPConvergenceOn K 2 b bInf) :
    MapCPConvergenceOn K 1 (fun i x => (b i x, fderiv ℝ (b i) x))
      (fun x => (bInf x, fderiv ℝ bInf x)) := by
  have hd : ∀ {c : E → E →L[ℝ] E →L[ℝ] ℝ}, ContDiffOn ℝ 2 c U → ∀ x ∈ K,
      DifferentiableAt ℝ c x ∧ DifferentiableAt ℝ (fderiv ℝ c) x := fun hc x hx =>
    ⟨(hc.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt (by norm_num),
      ((hc.fderiv_of_isOpen hU (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).contDiffAt
        (hU.mem_nhds (hKU hx))).differentiableAt one_ne_zero⟩
  have h0 := forall_norm_sub_le_of_mapCPConvergenceOn_one (hconv.mono_order (by norm_num))
    (fun i x hx => (hd (hb i) x hx).1) (fun x hx => (hd hbInf x hx).1)
  have h1 := forall_norm_sub_le_of_mapCPConvergenceOn_one
    (finite_fderiv_convergence hU hKU 1 hb hbInf hconv)
    (fun i x hx => (hd (hb i) x hx).2) (fun x hx => (hd hbInf x hx).2)
  have hpair : ∀ {c : E → E →L[ℝ] E →L[ℝ] ℝ}, ContDiffOn ℝ 2 c U → ∀ x ∈ K,
      HasFDerivAt (fun y => (c y, fderiv ℝ c y))
        ((fderiv ℝ c x).prod (fderiv ℝ (fderiv ℝ c) x)) x := fun hc x hx =>
    (hd hc x hx).1.hasFDerivAt.prodMk (hd hc x hx).2.hasFDerivAt
  refine mapCPConvergenceOn_one_of_forall_norm_sub_le
    (Eventually.of_forall fun i x hx => (hpair (hb i) x hx).differentiableAt)
    (fun x hx => (hpair hbInf x hx).differentiableAt) ?_ ?_
  · intro ε hε
    filter_upwards [h0 ε hε, h1 ε hε] with i hi0 hi1 x hx
    rw [Prod.mk_sub_mk, Prod.norm_mk]
    exact max_le (hi0 x hx).1 (hi1 x hx).1
  · intro ε hε
    filter_upwards [h0 ε hε, h1 ε hε] with i hi0 hi1 x hx
    rw [(hpair (hb i) x hx).fderiv, (hpair hbInf x hx).fderiv]
    refine ContinuousLinearMap.opNorm_le_bound _ hε.le fun v => ?_
    have e1 := (fderiv ℝ (b i) x - fderiv ℝ bInf x).le_opNorm v
    have e2 := (fderiv ℝ (fderiv ℝ (b i)) x - fderiv ℝ (fderiv ℝ bInf) x).le_opNorm v
    rw [sub_apply] at e1 e2
    rw [sub_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.prod_apply, Prod.mk_sub_mk, Prod.norm_mk]
    exact max_le (e1.trans (mul_le_mul_of_nonneg_right (hi0 x hx).2 (norm_nonneg _)))
      (e2.trans (mul_le_mul_of_nonneg_right (hi1 x hx).2 (norm_nonneg _)))

omit [FiniteDimensional ℝ E] in
/-- `raisedKoszulOp` along `C^n` families of coercive forms and `3`-tensors, over an arbitrary
normed domain `F` (the tree's `raisedKoszulOp_contDiffOn` has domain `E` itself). -/
theorem raisedKoszulOp_contDiffOn_of_domain [FiniteDimensional ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : WithTop ℕ∞} {U : Set F}
    {g : F → E →L[ℝ] E →L[ℝ] ℝ}
    {D : F → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ}
    (hg : ContDiffOn ℝ n g U) (hD : ContDiffOn ℝ n D U)
    (hco : ∀ x ∈ U, IsCoercive (g x)) :
    ContDiffOn ℝ n (fun x => raisedKoszulOp (g x) (D x)) U := by
  let gram : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E) :=
    ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E
      (ContinuousDualEquiv.equiv (E := E)).symm.toContinuousLinearMap
  let riesz : (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ]
      (E →L[ℝ] E →L[ℝ] E) :=
    (ContinuousLinearMap.compL ℝ E (E →L[ℝ] E →L[ℝ] ℝ) (E →L[ℝ] E)
      (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E
        (ContinuousDualEquiv.equiv (E := E)).symm.toContinuousLinearMap)).comp
      koszulCovCLM
  let post : (E →L[ℝ] E) →L[ℝ]
      (E →L[ℝ] E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E →L[ℝ] E) :=
    (ContinuousLinearMap.compL ℝ E (E →L[ℝ] E) (E →L[ℝ] E)).comp
      (ContinuousLinearMap.compL ℝ E E E)
  have hunit : ∀ x ∈ U, IsUnit (gram (g x)) := by
    intro x hx
    let eB : E ≃L[ℝ] (E →L[ℝ] ℝ) :=
      ContinuousLinearEquiv.ofBijective (g x)
        (LinearMap.ker_eq_bot.mpr (hco x hx).bilin_injective)
        (LinearMap.range_eq_top.mpr (CoerciveBilinInverse.surjective (hco x hx)))
    let e : E ≃L[ℝ] E := eB.trans (ContinuousDualEquiv.equiv (E := E)).symm
    exact ⟨e.toUnit, rfl⟩
  have hgram : ContDiffOn ℝ n (fun x => gram (g x)) U :=
    gram.contDiff.comp_contDiffOn hg
  have hinv : ContDiffOn ℝ n (fun x => Ring.inverse (gram (g x))) U :=
    (DifferentialGeometry.Analysis.contDiffOn_ringInverse
      (R := E →L[ℝ] E) (𝕜 := ℝ) n).comp hgram hunit
  have hriesz : ContDiffOn ℝ n (fun x => riesz (D x)) U :=
    riesz.contDiff.comp_contDiffOn hD
  change ContDiffOn ℝ n (fun x => post (Ring.inverse (gram (g x))) (riesz (D x))) U
  exact post.isBoundedBilinearMap.contDiff.comp₂_contDiffOn hinv hriesz

/-- **Adapter (1) of LFR09.** `C²` convergence of coercive chart metric coefficients gives `C¹`
convergence of their Christoffel fields on compact subsets. -/
theorem mapCPConvergenceOn_raisedKoszulOp_of_C2 {U : Set E} (hU : IsOpen U)
    {b : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ} {bInf : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hb : ∀ i, ContDiffOn ℝ 2 (b i) U) (hbInf : ContDiffOn ℝ 2 bInf U)
    (hbco : ∀ i, ∀ x ∈ U, IsCoercive (b i x)) (hco : ∀ x ∈ U, IsCoercive (bInf x))
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) (hconv : MapCPConvergenceOn K 2 b bInf) :
    MapCPConvergenceOn K 1 (fun i x => raisedKoszulOp (b i x) (fderiv ℝ (b i) x))
      (fun x => raisedKoszulOp (bInf x) (fderiv ℝ bInf x)) := by
  set V : Set ((E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) :=
    {p | IsCoercive p.1} with hV_def
  have hV : IsOpen V := isOpen_iff_mem_nhds.mpr fun p hp =>
    eventually_isCoercive_of_continuousAt continuous_fst.continuousAt hp
  have hΦ : ContDiffOn ℝ ((1 : ℕ) : ℕ∞)
      (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) => raisedKoszulOp p.1 p.2) V :=
    raisedKoszulOp_contDiffOn_of_domain contDiffOn_fst contDiffOn_snd fun p hp => hp
  have hjet : ∀ {c : E → E →L[ℝ] E →L[ℝ] ℝ}, ContDiffOn ℝ 2 c U →
      ContDiffOn ℝ ((1 : ℕ) : ℕ∞) (fun y => (c y, fderiv ℝ c y)) U := fun hc => by
    have h := (hc.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).prodMk
      (hc.fderiv_of_isOpen hU (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2))
    exact_mod_cast h
  have hconst : ∀ S, IsCompact S → S ⊆ V → MapCPConvergenceOn S 1
      (fun (_ : ℕ) (p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) =>
        raisedKoszulOp p.1 p.2)
      (fun p => raisedKoszulOp p.1 p.2) := fun S _ _ ε hε =>
    ⟨0, fun k _ r _ x _ => by
      simp only [mapDerivNorm, sub_self, iteratedFDeriv_fun_zero, Pi.zero_apply]
      exact (le_of_eq ContinuousMultilinearMap.opNorm_zero).trans hε.le⟩
  have hmap : MapsTo (fun x => (bInf x, fderiv ℝ bInf x)) U V := fun x hx => hco x hx
  have hmapk : ∀ i, MapsTo (fun x => (b i x, fderiv ℝ (b i) x)) U V := fun i x hx => hbco i x hx
  have hjetconv := mapCPConvergenceOn_jet_of_C2 hU hb hbInf hKU hconv
  have hP : ProperSpace ((E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) :=
    FiniteDimensional.proper ℝ _
  have h := MapCPConvergenceOn.comp_finite (p := 1) hU hV hK hKU hjetconv hconst
    (fun i => hjet (hb i)) (hjet hbInf) (fun _ => hΦ) hΦ hmap hmapk
  exact h

/-- **LFR09, chart kernel in coefficient form.** Coercive `C²` chart metrics `b i → b∞` in `C²` on
the compact subsets of `U`, `C ⊆ U` compact: there are `τ, L > 0` such that, for a tail of `i`, any
`x ∈ C` and `y` with `‖y - x‖ ≤ τ` are joined by a `b i`-geodesic `γ : [0, 1] → U` (chart geodesic
equation of `metricSpray (b i)`) with `‖γ'‖ ≤ L ‖y - x‖`. -/
theorem exists_short_geodesics_of_metric_C2 {U : Set E} (hU : IsOpen U)
    {b : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ} {bInf : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hb : ∀ i, ContDiffOn ℝ 2 (b i) U) (hbInf : ContDiffOn ℝ 2 bInf U)
    (hbco : ∀ i, ∀ x ∈ U, IsCoercive (b i x)) (hco : ∀ x ∈ U, IsCoercive (bInf x))
    (hconv : ∀ K, IsCompact K → K ⊆ U → MapCPConvergenceOn K 2 b bInf) {C : Set E}
    (hC : IsCompact C) (hCU : C ⊆ U) :
    ∃ τ L : ℝ, 0 < τ ∧ 0 < L ∧ ∀ᶠ i in atTop, ∀ x ∈ C, ∀ y : E,
      ‖y - x‖ ≤ τ → ∃ γ γ' : ℝ → E, γ 0 = x ∧ γ 1 = y ∧ ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U ∧
        HasDerivWithinAt γ (γ' t) (Icc 0 1) t ∧
        HasDerivWithinAt γ' (-(raisedKoszulOp (b i (γ t)) (fderiv ℝ (b i) (γ t)) (γ' t) (γ' t)))
          (Icc 0 1) t ∧ ‖γ' t‖ ≤ L * ‖y - x‖ := by
  have hΓ : ∀ {c : E → E →L[ℝ] E →L[ℝ] ℝ}, ContDiffOn ℝ 2 c U → (∀ x ∈ U, IsCoercive (c x)) →
      ContDiffOn ℝ 1 (fun x => raisedKoszulOp (c x) (fderiv ℝ c x)) U := fun hc hcco =>
    raisedKoszulOp_contDiffOn (hc.of_le (by norm_num))
      (hc.fderiv_of_isOpen hU (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)) hcco
  exact exists_short_geodesics_of_isCompact hU (fun i => hΓ (hb i) (hbco i)) (hΓ hbInf hco)
    (fun K hK hKU => mapCPConvergenceOn_raisedKoszulOp_of_C2 hU hb hbInf hbco hco hK hKU
      (hconv K hK hKU)) hC hCU

end DifferentialGeometry.Analysis.ODE.GeodesicLimits
