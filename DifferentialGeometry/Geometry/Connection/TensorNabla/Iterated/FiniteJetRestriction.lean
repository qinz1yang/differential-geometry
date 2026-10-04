import DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.Metric
import DifferentialGeometry.Geometry.Connection.TensorNabla.Naturality.MetricRestriction
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Restriction
import DifferentialGeometry.Geometry.Connection.TensorNabla.Connection.Tangent

/-!
# Open restriction of the metric covariant derivative of an arbitrary section

For every section (no regularity), the metric covariant derivatives of all orders commute with
restriction to an open subset, and so do their fibre norms.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter TopologicalSpace DifferentialGeometry.TensorLieDeriv
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem finiteJetR_cov_tangentConst (G : SmoothRiemannianMetric I M) (U : Opens M)
    [T2Space U] (x : U) (v : E) (w : TangentSpace I x) :
    (leviCivitaConnectionOfMetric (G.restrictOpen U)
        (tangentConstInChart (𝕜 := ℝ) (I := I) x v) x) w =
      (leviCivitaConnectionOfMetric G (tangentConstInChart (𝕜 := ℝ) (I := I) (x : M) v)
        (x : M)) w := by
  let e := trivializationAt E (TangentSpace I : M → Type _) (x : M)
  have hx : (x : M) ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) (x : M)
  have hsec : ∀ _ : Unit, CMDiff[e.baseSet] ∞
      (T% (tangentConstInChart (𝕜 := ℝ) (I := I) (x : M) v : (p : M) → TangentSpace I p)) :=
    fun _ => tangentConstInChart_contMDiffOn_baseSet (𝕜 := ℝ) (I := I) (M := M) (n := ∞)
      (x : M) v
  obtain ⟨Y, hY⟩ := exists_contMDiffSection_eqOn_nhd (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) hsec e.open_baseSet hx
  have hYM : ∀ᶠ p in 𝓝 (x : M), Y () p =
      tangentConstInChart (𝕜 := ℝ) (I := I) (x : M) v p := hY.mono fun p hp => hp ()
  -- on `M`
  have hM : leviCivitaConnectionOfMetric G (tangentConstInChart (𝕜 := ℝ) (I := I) (x : M) v)
      (x : M) = leviCivitaConnectionOfMetric G (fun p : M => Y () p) (x : M) := by
    refine (leviCivitaConnectionOfMetric G).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      ?_ ?_ Filter.univ_mem (hYM.mono fun p hp => hp.symm)
    · exact ((hsec ()).contMDiffAt (e.open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
    · exact ((Y ()).contMDiff (x : M)).mdifferentiableAt (by simp)
  -- on `U`
  have hUeq : ∀ᶠ p in 𝓝 x, tangentConstInChart (𝕜 := ℝ) (I := I) x v p =
      restrictOpenTangentField (I := I) U (fun y : M => Y () y) p := by
    have hnb : {p : U | (p : M) ∈ (chartAt H (x : M)).source ∧ Y () (p : M) =
        tangentConstInChart (𝕜 := ℝ) (I := I) (x : M) v (p : M)} ∈ 𝓝 x :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds
        (inter_mem ((chartAt H (x : M)).open_source.mem_nhds (mem_chart_source H (x : M))) hYM)
    filter_upwards [hnb] with p hp
    rw [restrictOpenTangentField_apply, hp.2]
    have hsrc : p ∈ (chartAt H x).source := by
      rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]
      exact hp.1
    simp only [tangentConstInChart_apply]
    rw [TangentBundle.symmL_trivializationAt_eq_core hsrc,
      TangentBundle.symmL_trivializationAt_eq_core hp.1,
      tangentCoordChange_opens (I := I) x p p hp.1]
    rfl
  have hU : leviCivitaConnectionOfMetric (G.restrictOpen U)
      (tangentConstInChart (𝕜 := ℝ) (I := I) x v) x =
      leviCivitaConnectionOfMetric (G.restrictOpen U)
        (restrictOpenTangentField (I := I) U (fun y : M => Y () y)) x := by
    refine (leviCivitaConnectionOfMetric (G.restrictOpen U)).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      ?_ ?_ Filter.univ_mem hUeq
    · exact ((tangentConstInChart_contMDiffOn_baseSet (𝕜 := ℝ) (I := I) (M := U) (n := ∞)
        x v).contMDiffAt ((trivializationAt E (TangentSpace I : U → Type _) x).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt E (TangentSpace I) x))).mdifferentiableAt (by simp)
    · exact ((restrictOpenTangentSection U (Y ())).contMDiff x).mdifferentiableAt (by simp)
  rw [hU, hM]
  exact metricCov_restrictOpen_globalSection G U (Y ()) x w

private theorem finiteJetR_connEnd (G : SmoothRiemannianMetric I M) (U : Opens M) [T2Space U]
    (x : U) :
    connectionEndomorphismInChartL (𝕜 := ℝ) (I := I) (M := U)
        (leviCivitaConnectionOfMetric (G.restrictOpen U)) x (extChartAt I x x) =
      connectionEndomorphismInChartL (𝕜 := ℝ) (I := I) (M := M)
        (leviCivitaConnectionOfMetric G) (x : M) (extChartAt I (x : M) (x : M)) := by
  have hxs : (x : M) ∈ (chartAt H (x : M)).source := mem_chart_source H (x : M)
  have hxsU : x ∈ (chartAt H x).source := mem_chart_source H x
  ext X v
  rw [connectionEndomorphismInChartL_apply_of_mem (𝕜 := ℝ) (I := I) _ x
      (mem_extChartAt_target (I := I) x),
    connectionEndomorphismInChartL_apply_of_mem (𝕜 := ℝ) (I := I) _ (x : M)
      (mem_extChartAt_target (I := I) (x : M)),
    extChartAt_to_inv, extChartAt_to_inv,
    TangentBundle.symmL_trivializationAt_eq_core hxsU,
    TangentBundle.symmL_trivializationAt_eq_core hxs,
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hxsU,
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hxs,
    tangentCoordChange_opens (I := I) x x x hxs, finiteJetR_cov_tangentConst]
  rfl

omit [CompleteSpace E] [T2Space M] in
/-- The restriction of an arbitrary section to an open subset, read in the subset's fibres. -/
private theorem finiteJetR_model_eq {s : ℕ} (U : Opens M) (A : (x : M) → Tensor0SSpace s I x)
    (x : U) {y : E} (hy : y ∈ (extChartAt I x).target) :
    tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := U) s x
        (fun z : U => Tensor0SSpace.ofModel (I := I) (x := z)
          (Tensor0SSpace.toModel (A (z : M)))) y =
      tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s (x : M) A y := by
  have hsrc := (extChartAt I x).map_target hy
  rw [extChartAt_source, TopologicalSpace.Opens.chartAt_eq,
    OpenPartialHomeomorph.subtypeRestr_source] at hsrc
  have hval : (((extChartAt I x).symm y : U) : M) = (extChartAt I (x : M)).symm y := by
    have hyt : I.symm y ∈ (chartAt H x).target := by
      rw [extChartAt_target] at hy
      exact hy.1
    rw [TopologicalSpace.Opens.chartAt_eq] at hyt
    have h := (chartAt H (x : M)).subtypeRestr_symm_apply ⟨x⟩ hyt
    simp only [extChartAt, OpenPartialHomeomorph.extend, PartialEquiv.coe_trans_symm,
      ModelWithCorners.toPartialEquiv_coe_symm, OpenPartialHomeomorph.coe_toPartialEquiv_symm,
      Function.comp_apply, TopologicalSpace.Opens.chartAt_eq] at h ⊢
    exact h
  unfold tensor0SModelInChart
  rw [tensor0SModelAt_opens s x ((extChartAt I x).symm y) hsrc]
  rw [hval]

omit [CompleteSpace E] [T2Space M] in
private theorem finiteJetR_model_center {r : ℕ} (x : M) (B : Tensor0SSpace r I x) (c : Fin r → E) :
    tensor0SModelAt (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r x x B c = B c := by
  rw [tensor0SModelAt_apply, TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source H x)]
  congr 1
  funext a
  exact (tangentBundleCore I M).coordChange_self (achart H x) x
    (by simp) (c a)

/-- **Open restriction (G1.d).** For an arbitrary section, the metric covariant derivative
commutes with restriction to an open subset. -/
theorem metricCovariantDerivative_restrictOpen (G : SmoothRiemannianMetric I M) (U : Opens M)
    [T2Space U] {s : ℕ} (A : (x : M) → Tensor0SSpace s I x) (x : U) :
    metricCovariantDerivative (G.restrictOpen U) s
        (fun z : U => Tensor0SSpace.ofModel (I := I) (x := z)
          (Tensor0SSpace.toModel (A (z : M)))) x =
      Tensor0SSpace.ofModel (I := I) (x := x)
        (Tensor0SSpace.toModel (metricCovariantDerivative G s A (x : M))) := by
  have hxs : (x : M) ∈ (chartAt H (x : M)).source := mem_chart_source H (x : M)
  have hfd : fderivWithin ℝ (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := U) s x
        (fun z : U => Tensor0SSpace.ofModel (I := I) (x := z)
          (Tensor0SSpace.toModel (A (z : M))))) (Set.range I) (extChartAt I x x) =
      fderivWithin ℝ (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
        (x : M) A) (Set.range I) (extChartAt I (x : M) (x : M)) := by
    apply Filter.EventuallyEq.fderivWithin_eq_of_mem _
      (extChartAt_target_subset_range x (mem_extChartAt_target (I := I) x))
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x] with y hy
    exact finiteJetR_model_eq U A x hy
  -- compare through the model at the centre of the subset
  apply tensor0SSpace_ext (I := I) (s + 1) x
  intro slots
  rw [← finiteJetR_model_center (M := U) x (metricCovariantDerivative (G.restrictOpen U) s
      (fun z : U => Tensor0SSpace.ofModel (I := I) (x := z)
        (Tensor0SSpace.toModel (A (z : M)))) x) slots,
    ← finiteJetR_model_center (M := U) x (Tensor0SSpace.ofModel (I := I) (x := x)
      (Tensor0SSpace.toModel (metricCovariantDerivative G s A (x : M)))) slots]
  congr 1
  rw [tensor0SModelAt_opens (s + 1) x x hxs]
  unfold metricCovariantDerivative
  rw [tensor0SModelAt_trivializationAt_symm, tensor0SModelAt_trivializationAt_symm, hfd,
    finiteJetR_connEnd G U x]
  congr 1
  exact tensor0SModelAt_opens s x x hxs (A x)

/-- The iterated version of the open restriction, for every order. -/
theorem iteratedMetricCovariantDerivative_restrictOpen (G : SmoothRiemannianMetric I M)
    (U : Opens M) [T2Space U] {s : ℕ} (A : (x : M) → Tensor0SSpace s I x) (k : ℕ) (x : U) :
    iteratedMetricCovariantDerivative (G.restrictOpen U) s
        (fun z : U => Tensor0SSpace.ofModel (I := I) (x := z)
          (Tensor0SSpace.toModel (A (z : M)))) k x =
      Tensor0SSpace.ofModel (I := I) (x := x)
        (Tensor0SSpace.toModel (iteratedMetricCovariantDerivative G s A k (x : M))) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      have hfun : iteratedMetricCovariantDerivative (G.restrictOpen U) s
          (fun z : U => Tensor0SSpace.ofModel (I := I) (x := z)
            (Tensor0SSpace.toModel (A (z : M)))) k =
          fun z : U => Tensor0SSpace.ofModel (I := I) (x := z)
            (Tensor0SSpace.toModel (iteratedMetricCovariantDerivative G s A k (z : M))) :=
        funext ih
      change metricCovariantDerivative (G.restrictOpen U) (s + k)
          (iteratedMetricCovariantDerivative (G.restrictOpen U) s _ k) x = _
      rw [hfun, metricCovariantDerivative_restrictOpen]
      rfl

/-- Fibre norms of the iterated covariant derivatives agree on an open subset. -/
theorem tensor0SFiberNorm_iteratedMetricCovariantDerivative_restrictOpen
    (G : SmoothRiemannianMetric I M) (U : Opens M) [T2Space U] {s : ℕ}
    (A : (x : M) → Tensor0SSpace s I x) (k : ℕ) (x : U) :
    tensor0SFiberNorm (G.restrictOpen U) x (s + k)
        (iteratedMetricCovariantDerivative (G.restrictOpen U) s
          (fun z : U => Tensor0SSpace.ofModel (I := I) (x := z)
            (Tensor0SSpace.toModel (A (z : M)))) k x) =
      tensor0SFiberNorm G (x : M) (s + k) (iteratedMetricCovariantDerivative G s A k (x : M)) := by
  rw [iteratedMetricCovariantDerivative_restrictOpen]
  unfold tensor0SFiberNorm
  rw [normSq0S_restrictOpen_apply]
  rfl

end DifferentialGeometry.Geometry.Connection
