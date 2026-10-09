import DifferentialGeometry.Geometry.Connection.Hessian
import DifferentialGeometry.Geometry.Connection.Trivial
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Operator.Hessian.Trace.ChartGramRegularity
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

/-!
# The Hessian of a `C²` scalar in a chart, and chart bounds (boundary allowed)

Let `g` be a smooth Riemannian metric on `M` (the model may have boundary) and `α : M`, with
`ψ = extChartAt I α`. At a point `x` of the Levi-Civita good set of the chart at `α` (chart source,
`ψ x` in the interior of the chart target) and for `f` of class `C²` at `x`, with `F = f ∘ ψ⁻¹`:

* `hessian_chartConstField`: for the field `chartConstField I α w` with constant chart vector `w`,
  `Hess f (X, w) = D²F(ψ x)(ψ_* X, w) - DF(ψ x)(Γ_x(w, X))`, where `Γ_x = christoffelCorrection`
  and `Hess = (CovariantDerivative.trivial I M ℝ).hessian (LeviCivita g)` is the EXISTING Hessian
  (`Geometry/Connection/Hessian.lean`);
* `abs_hessian_le_chart`: `|Hess f (X, Y)| ≤ (‖D²F‖ + ‖DF‖ · CΓ(ψ x)) ‖ψ_* X‖ ‖ψ_* Y‖`, with the
  explicit `CΓ = christoffelBound g α`, continuous on the interior of the chart target;
* `abs_mvfderiv_le_chart`: `|df (X)| ≤ ‖DF‖ ‖ψ_* X‖`;
* `exists_norm_trivToE_le_sqrt_inner`: on a compact subset of the chart source,
  `‖ψ_* X‖ ≤ C √(g(X, X))` (positive definite Gram matrix, compactness).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry.Geometry.Connection

open DifferentialGeometry.Tensor.Coordinates (chartModelBasis)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] in
/-- A scalar `C²` at a point of a chart whose image lies in the interior of the chart target has a
`C²` coordinate expression there. -/
theorem contDiffAt_comp_extChartAt_symm {α x : M} (hx : x ∈ (chartAt H α).source)
    (hint : extChartAt I α x ∈ interior (extChartAt I α).target) {f : M → ℝ}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x) :
    ContDiffAt ℝ 2 (f ∘ (extChartAt I α).symm) (extChartAt I α x) := by
  have h := ((contMDiffAt_iff_of_mem_source (I' := 𝓘(ℝ, ℝ)) (y := f x) hx
    (mem_chart_source ℝ (f x))).mp hf).2
  have hr : range I ∈ 𝓝 (extChartAt I α x) :=
    mem_of_superset (isOpen_interior.mem_nhds hint)
      (interior_subset.trans (extChartAt_target_subset_range α))
  simpa using h.contDiffAt hr

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem mvfderiv_eq_of_eventuallyEq {x : M} {h₁ h₂ : M → ℝ} (hh : h₁ =ᶠ[𝓝 x] h₂) :
    mvfderiv I h₁ x = mvfderiv I h₂ x := by
  unfold mvfderiv
  rw [hh.mfderiv_eq, hh.eq_of_nhds]
  rfl

variable (I) in
/-- The vector field whose coordinate vector in the chart at `α` is the constant `w`. -/
def chartConstField (α : M) (w : E) : Π y : M, TangentSpace I y :=
  fun y => trivFromE I α y w

omit [FiniteDimensional ℝ E] in
theorem chartESectionRepr_chartConstField {α y : M}
    (hy : y ∈ (trivializationAt E (TangentSpace I) α).baseSet) (w : E) :
    chartESectionRepr (I := I) α (chartConstField I α w) y = w :=
  trivToE_trivFromE I α hy w

omit [FiniteDimensional ℝ E] in
theorem chartESectionRepr_chartConstField_eventuallyEq {α x : M}
    (hint : extChartAt I α x ∈ interior (extChartAt I α).target) (w : E) :
    (chartESectionRepr (I := I) α (chartConstField I α w) ∘ (extChartAt I α).symm)
      =ᶠ[𝓝 (extChartAt I α x)] fun _ => w := by
  filter_upwards [isOpen_interior.mem_nhds hint] with z hz
  apply chartESectionRepr_chartConstField
  rw [TangentBundle.trivializationAt_baseSet, ← extChartAt_source (I := I)]
  exact (extChartAt I α).map_target (interior_subset hz)

omit [FiniteDimensional ℝ E] in
theorem mdifferentiableAt_chartConstField {α x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) (w : E) :
    MDiffAt (T% (chartConstField I α w)) x := by
  rw [mdifferentiableAt_section_iff_chartE_fderiv I α _
    (chartLeviCivitaGoodSet_mem_chartAt_source hx) (chartLeviCivitaGoodSet_mem_baseSet hx)
    (chartLeviCivitaGoodSet_extChartAt_mem_interior hx)]
  exact (differentiableAt_const w).congr_of_eventuallyEq
    (chartESectionRepr_chartConstField_eventuallyEq
      (chartLeviCivitaGoodSet_extChartAt_mem_interior hx) w)

/-- The Levi-Civita derivative of a chart-constant field is the Christoffel correction. -/
theorem leviCivita_chartConstField [T2Space M] (g : SmoothRiemannianMetric I M) {α x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) (w : E) (X : TangentSpace I x) :
    (LeviCivita g) (chartConstField I α w) x X =
      trivFromE I α x (christoffelCorrection g α x w X) := by
  rw [LeviCivita_chart_apply g α hx (mdifferentiableAt_chartConstField hx w) X,
    chartLeviCivita_apply g α _ hx X,
    (chartESectionRepr_chartConstField_eventuallyEq
      (chartLeviCivitaGoodSet_extChartAt_mem_interior hx) w).fderiv_eq,
    chartESectionRepr_chartConstField (chartLeviCivitaGoodSet_mem_baseSet hx)]
  simp

/-- **The Hessian in a chart.** For `f` of class `C²` at a point of the good set of the chart at
`α`, the EXISTING Hessian evaluated on a chart-constant second slot is the coordinate second
derivative minus the Christoffel term. -/
theorem hessian_chartConstField [T2Space M] (g : SmoothRiemannianMetric I M) {α x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) {f : M → ℝ}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x) (X : TangentSpace I x) (w : E) :
    (CovariantDerivative.trivial I M ℝ).hessian (LeviCivita g) f x X (chartConstField I α w x) =
      fderiv ℝ (fderiv ℝ (f ∘ (extChartAt I α).symm)) (extChartAt I α x) (trivToE I α x X) w -
        fderiv ℝ (f ∘ (extChartAt I α).symm) (extChartAt I α x)
          (christoffelCorrection g α x w X) := by
  set ψ := extChartAt I α with hψ
  set F : E → ℝ := f ∘ ψ.symm with hF
  have hsrc := chartLeviCivitaGoodSet_mem_chartAt_source hx
  have hint := chartLeviCivitaGoodSet_extChartAt_mem_interior hx
  have hbase := chartLeviCivitaGoodSet_mem_baseSet hx
  have hFc : ContDiffAt ℝ 2 F (ψ x) := contDiffAt_comp_extChartAt_symm hsrc hint hf
  have hdF : DifferentiableAt ℝ (fderiv ℝ F) (ψ x) :=
    (hFc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hσ : ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) 2 (T% f) x :=
    (contMDiffAt_section (F := ℝ) (E := Bundle.Trivial M ℝ) x).mpr hf
  rw [(CovariantDerivative.trivial I M ℝ).hessian_apply_of_contMDiffAt inferInstance
    (LeviCivita g) hσ (mdifferentiableAt_chartConstField hx w) X]
  simp only [CovariantDerivative.trivial_apply]
  have hfd : MDiffAt f x := hf.mdifferentiableAt (by norm_num)
  rw [leviCivita_chartConstField g hx w X, mfderiv_scalar_eq_chart_fderiv I α f hsrc hint hfd,
    trivToE_trivFromE I α hbase]
  congr 1
  -- the first term: `y ↦ df_y (w)` is `G ∘ ψ` near `x`, `G z = DF(z) w`
  set G : E → ℝ := fun z => fderiv ℝ F z w with hG
  have hGd : DifferentiableAt ℝ G (ψ x) := hdF.clm_apply (differentiableAt_const w)
  have hFev : ∀ᶠ y in 𝓝 x, y ∈ chartLeviCivitaGoodSet (I := I) α ∧
      DifferentiableAt ℝ F (ψ y) := by
    have h1 : ∀ᶠ z in 𝓝 (ψ x), ContDiffAt ℝ 2 F z := hFc.eventually (by decide)
    have h2 := (continuousAt_extChartAt' (I := I)
      (by rw [extChartAt_source]; exact hsrc)).tendsto.eventually h1
    filter_upwards [(chartLeviCivitaGoodSet_isOpen α).mem_nhds hx, h2] with y hy1 hy2
    exact ⟨hy1, hy2.differentiableAt (by norm_num)⟩
  have hev : (fun y => mvfderiv I f y (chartConstField I α w y)) =ᶠ[𝓝 x] G ∘ ψ := by
    filter_upwards [hFev] with y ⟨hyg, hyd⟩
    have hysrc := chartLeviCivitaGoodSet_mem_chartAt_source hyg
    have hfy : MDiffAt f y := by
      have hloc : (F ∘ ψ) =ᶠ[𝓝 y] f := by
        filter_upwards [extChartAt_source_mem_nhds' (I := I)
          (by rw [extChartAt_source]; exact hysrc)] with y' hy'
        change f (ψ.symm (ψ y')) = f y'
        rw [ψ.left_inv hy']
      exact (hyd.mdifferentiableAt.comp y
        (mdifferentiableAt_extChartAt hysrc)).congr_of_eventuallyEq hloc.symm
    change mvfderiv I f y (trivFromE I α y w) = G (ψ y)
    rw [mfderiv_scalar_eq_chart_fderiv I α f hysrc
      (chartLeviCivitaGoodSet_extChartAt_mem_interior hyg) hfy,
      trivToE_trivFromE I α (chartLeviCivitaGoodSet_mem_baseSet hyg)]
  have hcongr : mvfderiv I (fun y => mvfderiv I f y (chartConstField I α w y)) x =
      mvfderiv I (G ∘ ψ) x := mvfderiv_eq_of_eventuallyEq hev
  have hGψ : MDiffAt (G ∘ ψ) x :=
    hGd.mdifferentiableAt.comp x (mdifferentiableAt_extChartAt hsrc)
  have hback : (G ∘ ψ) ∘ ψ.symm =ᶠ[𝓝 (ψ x)] G := by
    filter_upwards [isOpen_interior.mem_nhds hint] with z hz
    change G (ψ (ψ.symm z)) = G z
    rw [ψ.right_inv (interior_subset hz)]
  rw [hcongr, mfderiv_scalar_eq_chart_fderiv I α (G ∘ ψ) hsrc hint hGψ, hback.fderiv_eq,
    hG, fderiv_clm_apply hdF (differentiableAt_const w)]
  simp

/-! ### Bounds -/

/-- The Christoffel weight `Σ ‖e_i*‖ ‖e_j*‖ |Γ_ij^k| ‖e_k‖` of the chart at `α`. -/
def christoffelBound (g : SmoothRiemannianMetric I M) (α : M) (z : E) : ℝ :=
  ∑ i, ∑ j, ∑ k, ‖((chartModelBasis E).coord i).toContinuousLinearMap‖ *
    ‖((chartModelBasis E).coord j).toContinuousLinearMap‖ *
      |DifferentialGeometry.Geometry.Operator.chartChristoffel g α i j k z| *
        ‖chartModelBasis E k‖

theorem christoffelBound_nonneg (g : SmoothRiemannianMetric I M) (α : M) (z : E) :
    0 ≤ christoffelBound g α z :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
    positivity

theorem continuousOn_christoffelBound (g : SmoothRiemannianMetric I M) (α : M) :
    ContinuousOn (christoffelBound g α) (interior (extChartAt I α).target) := by
  unfold christoffelBound
  refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
    continuousOn_finsetSum _ fun k _ => ?_
  exact (continuousOn_const.mul
    (DifferentialGeometry.Geometry.Operator.chartChristoffel_contDiffOn_interior g α i j
      k).continuousOn.abs).mul continuousOn_const

omit [IsManifold I ∞ M] in
theorem abs_chartModelBasis_repr_le (a : E) (i : Fin (Module.finrank ℝ E)) :
    |(chartModelBasis E).repr a i| ≤
      ‖((chartModelBasis E).coord i).toContinuousLinearMap‖ * ‖a‖ := by
  have h := (((chartModelBasis E).coord i).toContinuousLinearMap).le_opNorm a
  rw [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply, Real.norm_eq_abs] at h
  exact h

theorem norm_christoffelCorrection_le (g : SmoothRiemannianMetric I M) (α x : M) (w : E)
    (X : TangentSpace I x) :
    ‖christoffelCorrection g α x w X‖ ≤
      christoffelBound g α (extChartAt I α x) * ‖trivToE I α x X‖ * ‖w‖ := by
  rw [christoffelCorrection_apply]
  set a := trivToE I α x X
  calc _ ≤ ∑ i, ∑ j, ∑ k, ‖((chartModelBasis E).repr a i * (chartModelBasis E).repr w j *
          DifferentialGeometry.Geometry.Operator.chartChristoffel g α i j k
            (extChartAt I α x)) • chartModelBasis E k‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun j _ => norm_sum_le _ _))
    _ ≤ ∑ i, ∑ j, ∑ k, ‖((chartModelBasis E).coord i).toContinuousLinearMap‖ *
          ‖((chartModelBasis E).coord j).toContinuousLinearMap‖ *
            |DifferentialGeometry.Geometry.Operator.chartChristoffel g α i j k
              (extChartAt I α x)| * ‖chartModelBasis E k‖ * ‖a‖ * ‖w‖ := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          Finset.sum_le_sum fun k _ => ?_
        rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul]
        have h1 := abs_chartModelBasis_repr_le a i
        have h2 := abs_chartModelBasis_repr_le w j
        have h3 := abs_nonneg (DifferentialGeometry.Geometry.Operator.chartChristoffel g α i j k
          (extChartAt I α x))
        have h4 := norm_nonneg (chartModelBasis E k)
        have h5 := abs_nonneg ((chartModelBasis E).repr a i)
        have h6 := abs_nonneg ((chartModelBasis E).repr w j)
        calc |(chartModelBasis E).repr a i| * |(chartModelBasis E).repr w j| *
              |DifferentialGeometry.Geometry.Operator.chartChristoffel g α i j k
                (extChartAt I α x)| * ‖chartModelBasis E k‖
            ≤ (‖((chartModelBasis E).coord i).toContinuousLinearMap‖ * ‖a‖) *
                (‖((chartModelBasis E).coord j).toContinuousLinearMap‖ * ‖w‖) *
                |DifferentialGeometry.Geometry.Operator.chartChristoffel g α i j k
                  (extChartAt I α x)| * ‖chartModelBasis E k‖ := by gcongr
          _ = _ := by ring
    _ = _ := by simp only [christoffelBound, Finset.sum_mul]

/-- **Chart bound for the Hessian.** -/
theorem abs_hessian_le_chart [T2Space M] (g : SmoothRiemannianMetric I M) {α x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) {f : M → ℝ}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x) (X Y : TangentSpace I x) :
    |(CovariantDerivative.trivial I M ℝ).hessian (LeviCivita g) f x X Y| ≤
      (‖fderiv ℝ (fderiv ℝ (f ∘ (extChartAt I α).symm)) (extChartAt I α x)‖ +
        ‖fderiv ℝ (f ∘ (extChartAt I α).symm) (extChartAt I α x)‖ *
          christoffelBound g α (extChartAt I α x)) *
        ‖trivToE I α x X‖ * ‖trivToE I α x Y‖ := by
  have hY : Y = chartConstField I α (trivToE I α x Y) x :=
    (trivFromE_trivToE I α (chartLeviCivitaGoodSet_mem_baseSet hx) Y).symm
  conv_lhs => rw [hY]
  rw [hessian_chartConstField g hx hf X]
  set D2 := fderiv ℝ (fderiv ℝ (f ∘ (extChartAt I α).symm)) (extChartAt I α x)
  set D1 := fderiv ℝ (f ∘ (extChartAt I α).symm) (extChartAt I α x)
  set a := trivToE I α x X
  set b := trivToE I α x Y
  set CΓ := christoffelBound g α (extChartAt I α x)
  have h1 : |D2 a b| ≤ ‖D2‖ * ‖a‖ * ‖b‖ := by
    rw [← Real.norm_eq_abs]
    exact ((D2 a).le_opNorm b).trans (mul_le_mul_of_nonneg_right (D2.le_opNorm a)
      (norm_nonneg b))
  have h2 : |D1 (christoffelCorrection g α x b X)| ≤ ‖D1‖ * (CΓ * ‖a‖ * ‖b‖) := by
    rw [← Real.norm_eq_abs]
    exact (D1.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (norm_christoffelCorrection_le g α x b X) (norm_nonneg D1))
  calc |D2 a b - D1 (christoffelCorrection g α x b X)|
      ≤ |D2 a b| + |D1 (christoffelCorrection g α x b X)| := abs_sub _ _
    _ ≤ ‖D2‖ * ‖a‖ * ‖b‖ + ‖D1‖ * (CΓ * ‖a‖ * ‖b‖) := add_le_add h1 h2
    _ = (‖D2‖ + ‖D1‖ * CΓ) * ‖a‖ * ‖b‖ := by ring

omit [FiniteDimensional ℝ E] in
/-- **Chart bound for the differential.** -/
theorem abs_mvfderiv_le_chart {α x : M} (hx : x ∈ (chartAt H α).source)
    (hint : extChartAt I α x ∈ interior (extChartAt I α).target) {f : M → ℝ}
    (hf : MDiffAt f x) (X : TangentSpace I x) :
    |mvfderiv I f x X| ≤
      ‖fderiv ℝ (f ∘ (extChartAt I α).symm) (extChartAt I α x)‖ * ‖trivToE I α x X‖ := by
  rw [mfderiv_scalar_eq_chart_fderiv I α f hx hint hf, ← Real.norm_eq_abs]
  exact ContinuousLinearMap.le_opNorm _ _

/-- **The chart norm is controlled by the metric on compact sets.** On a compact subset of the
chart source at `α`, `‖ψ_* X‖ ≤ C √(g(X, X))`. -/
theorem exists_norm_trivToE_le_sqrt_inner (g : SmoothRiemannianMetric I M) (α : M) {S : Set M}
    (hS : IsCompact S) (hSb : S ⊆ (chartAt H α).source) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ S, ∀ X : TangentSpace I y,
      ‖trivToE I α y X‖ ≤ C * Real.sqrt (g.inner y X X) := by
  classical
  set n := Module.finrank ℝ E
  set b := chartModelBasis E
  set G : M → Matrix (Fin n) (Fin n) ℝ := fun y =>
    DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g α y with hGdef
  set Q : M × (Fin n → ℝ) → ℝ := fun p => star p.2 ⬝ᵥ (G p.1 *ᵥ p.2) with hQdef
  have hbase : (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
    TangentBundle.trivializationAt_baseSet α
  have hGc : ∀ i j, ContinuousOn (fun y => G y i j) (chartAt H α).source := fun i j => by
    rw [← hbase]
    exact (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_entry_contMDiffOn g α i
      j).continuousOn
  have hQeq : Q = fun p => ∑ i, p.2 i * ∑ j, G p.1 i j * p.2 j := by
    funext p
    simp [hQdef, dotProduct, Matrix.mulVec]
  have hQc : ContinuousOn Q (S ×ˢ univ) := by
    rw [hQeq]
    refine continuousOn_finsetSum _ fun i _ => ?_
    refine ((continuous_apply i).comp continuous_snd).continuousOn.mul ?_
    refine continuousOn_finsetSum _ fun j _ => ?_
    exact ((hGc i j).comp continuous_fst.continuousOn fun p hp => hSb hp.1).mul
      ((continuous_apply j).comp continuous_snd).continuousOn
  have hQsmul : ∀ y (t : ℝ) (c : Fin n → ℝ), Q (y, t • c) = t ^ 2 * Q (y, c) := by
    intro y t c
    simp only [hQdef, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
      smul_eq_mul, star_trivial]
    ring
  have hQpos : ∀ y ∈ S, ∀ c : Fin n → ℝ, c ≠ 0 → 0 < Q (y, c) := by
    intro y hy c hc
    have hpd := DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_posDef g α
      (hbase ▸ hSb hy)
    exact hpd.dotProduct_mulVec_pos hc
  -- a uniform quadratic lower bound
  obtain ⟨lam, hlam, hQ⟩ : ∃ lam : ℝ, 0 < lam ∧ ∀ y ∈ S, ∀ c : Fin n → ℝ,
      lam * ‖c‖ ^ 2 ≤ Q (y, c) := by
    have hT : IsCompact (S ×ˢ Metric.sphere (0 : Fin n → ℝ) 1) :=
      hS.prod (isCompact_sphere 0 1)
    rcases (S ×ˢ Metric.sphere (0 : Fin n → ℝ) 1).eq_empty_or_nonempty with hE | hNE
    · refine ⟨1, one_pos, fun y hy c => ?_⟩
      by_cases hc : c = 0
      · simp [hc, hQdef]
      · exfalso
        have hcn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
        have hmem : (y, ‖c‖⁻¹ • c) ∈ S ×ˢ Metric.sphere (0 : Fin n → ℝ) 1 := by
          refine ⟨hy, ?_⟩
          rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hcn]
        rw [hE] at hmem
        exact hmem
    · obtain ⟨p₀, hp₀, hmin⟩ := hT.exists_isMinOn hNE
        (hQc.mono (prod_mono subset_rfl (subset_univ _)))
      have hc₀ : p₀.2 ≠ 0 := by
        intro h
        have := hp₀.2
        rw [mem_sphere_zero_iff_norm, h, norm_zero] at this
        exact zero_ne_one this
      refine ⟨Q p₀, hQpos p₀.1 hp₀.1 p₀.2 hc₀, fun y hy c => ?_⟩
      by_cases hc : c = 0
      · simp [hc, hQdef]
      · have hcn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
        have hmem : (y, ‖c‖⁻¹ • c) ∈ S ×ˢ Metric.sphere (0 : Fin n → ℝ) 1 := by
          refine ⟨hy, ?_⟩
          rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hcn]
        have h1 : Q p₀ ≤ Q (y, ‖c‖⁻¹ • c) := hmin hmem
        have h2 : c = ‖c‖ • (‖c‖⁻¹ • c) := by
          rw [smul_smul, mul_inv_cancel₀ hcn, one_smul]
        calc Q p₀ * ‖c‖ ^ 2 ≤ ‖c‖ ^ 2 * Q (y, ‖c‖⁻¹ • c) := by
              rw [mul_comm]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = Q (y, c) := by rw [← hQsmul, ← h2]
  -- the bound
  set Bsum : ℝ := ∑ i, ‖b i‖ with hBsum
  have hB0 : 0 ≤ Bsum := Finset.sum_nonneg fun i _ => norm_nonneg _
  refine ⟨Bsum / Real.sqrt lam, div_nonneg hB0 (Real.sqrt_nonneg _), fun y hy X => ?_⟩
  set a := trivToE I α y X with ha
  set c : Fin n → ℝ := b.equivFun a with hc
  have hya : y ∈ (trivializationAt E (TangentSpace I) α).baseSet := hbase ▸ hSb hy
  have hX : ∑ i, c i • DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber α i y = X := by
    have h1 : ∑ i, c i • DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber α i y =
        trivFromE I α y (∑ i, c i • b i) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul]
      rfl
    rw [h1, hc, b.sum_equivFun a, ha, trivFromE_trivToE I α hya]
  have hgX : g.inner y X X = Q (y, c) := by
    rw [hQdef]
    dsimp only
    rw [DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_dotProduct_mulVec, hX]
  have hanorm : ‖a‖ ≤ Bsum * ‖c‖ := by
    have ha' : a = ∑ i, c i • b i := (b.sum_equivFun a).symm
    calc ‖a‖ = ‖∑ i, c i • b i‖ := by rw [← ha']
      _ ≤ ∑ i, ‖c i • b i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖c‖ * ‖b i‖ := Finset.sum_le_sum fun i _ => by
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_right (norm_le_pi_norm c i) (norm_nonneg _)
      _ = Bsum * ‖c‖ := by rw [← Finset.mul_sum, mul_comm]
  have hcs : ‖c‖ * Real.sqrt lam ≤ Real.sqrt (g.inner y X X) := by
    rw [Real.le_sqrt (by positivity) (metric_inner_self_nonneg g y X), mul_pow,
      Real.sq_sqrt hlam.le, hgX, mul_comm]
    exact hQ y hy c
  have hsl : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  calc ‖a‖ ≤ Bsum * ‖c‖ := hanorm
    _ = Bsum / Real.sqrt lam * (‖c‖ * Real.sqrt lam) := by field_simp
    _ ≤ Bsum / Real.sqrt lam * Real.sqrt (g.inner y X X) :=
        mul_le_mul_of_nonneg_left hcs (div_nonneg hB0 hsl.le)

end DifferentialGeometry.Geometry.Connection
