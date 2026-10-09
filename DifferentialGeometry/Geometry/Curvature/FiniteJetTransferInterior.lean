import DifferentialGeometry.Geometry.Curvature.FiniteJetTransfer

/-!
# Second-order numerator transfer by jet replacement at interior points, ambient charts

The jet replacement transfer `abs_metricRm04_sub_le_of_chart_jet_replacement` reads its jet
hypotheses in the charts of the open subset `U`. At an intrinsic interior point the chart
representatives on `U` agree near the base point with those of the ambient manifold, and
derivatives within the model range are ordinary Fréchet derivatives. This file restates the
transfer with ambient chart hypotheses: an arbitrary section `T` (the finite datum) and a section
`T'` which, on `U`, is the difference of the smooth metric `g'` and the reference metric.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter TopologicalSpace DifferentialGeometry.TensorLieDeriv
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [CompleteSpace E] in
/-- The restriction of an arbitrary section to an open subset, read in the subset's fibres and
charts, agrees with the ambient chart representative on the subset's chart target. -/
private theorem finiteJetI_model_eq {s : ℕ} (U : Opens M) (A : (x : M) → Tensor0SSpace s I x)
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

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
private theorem finiteJetI_center (U : Opens M) (x : U) :
    extChartAt I x x = extChartAt I (x : M) x := by
  simp only [extChartAt, OpenPartialHomeomorph.extend, PartialEquiv.coe_trans,
    ModelWithCorners.toPartialEquiv_coe, OpenPartialHomeomorph.toFun_eq_coe, Function.comp_apply,
    TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_coe]
  rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
private theorem finiteJetI_target_mem_nhds (U : Opens M) (x : U)
    (hx : I.IsInteriorPoint (x : M)) :
    (extChartAt I x).target ∈ 𝓝 (extChartAt I (x : M) x) := by
  have h := extChartAt_target_mem_nhdsWithin (I := I) x
  rw [finiteJetI_center U x, nhdsWithin_eq_nhds.mpr (mem_interior_iff_mem_nhds.mp hx)] at h
  exact h

omit [CompleteSpace E] in
private theorem finiteJetI_eventuallyEq {s : ℕ} (U : Opens M) (A : (x : M) → Tensor0SSpace s I x)
    (x : U) (hx : I.IsInteriorPoint (x : M)) :
    tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := U) s x
        (fun z : U => Tensor0SSpace.ofModel (I := I) (x := z)
          (Tensor0SSpace.toModel (A (z : M)))) =ᶠ[𝓝 (extChartAt I (x : M) x)]
      tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s (x : M) A := by
  filter_upwards [finiteJetI_target_mem_nhds U x hx] with y hy
  exact finiteJetI_model_eq U A x hy

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
/-- Near an interior point of the model range, derivatives within the range are Fréchet
derivatives, to second order. -/
private theorem finiteJetI_fderivWithin {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {y₀ : E} (hy₀ : y₀ ∈ interior (range I)) :
    fderivWithin ℝ f (range I) y₀ = fderiv ℝ f y₀ ∧
      fderivWithin ℝ (fderivWithin ℝ f (range I)) (range I) y₀ = fderiv ℝ (fderiv ℝ f) y₀ := by
  have hmem : range I ∈ 𝓝 y₀ := mem_interior_iff_mem_nhds.mp hy₀
  refine ⟨fderivWithin_of_mem_nhds hmem, ?_⟩
  have hev : fderivWithin ℝ f (range I) =ᶠ[𝓝 y₀] fderiv ℝ f := by
    filter_upwards [isOpen_interior.mem_nhds hy₀] with y hy
    exact fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hy)
  rw [fderivWithin_of_mem_nhds hmem, hev.fderiv_eq]

variable [T2Space M]

/-- **Jet replacement transfer at interior points, ambient charts.** Let `x` be an intrinsic
interior point lying in an open set `U` without boundary, `T` an arbitrary section of
`(0,2)`-tensors with `k ≤ 2` norms at most `ε ≤ 1/2` at `x`, and `T'` a section which on `U` is
the difference of a smooth metric `g'` on `U` and the reference metric. If the ambient chart
representatives of `T` and `T'` at `x` are `C²` with the same second-order jet, the curvature
numerators of `g'` and of the reference metric differ by at most `ε (360 + K)`. -/
theorem abs_metricRm04_sub_le_of_chart_jet_replacement_interior (G : SmoothRiemannianMetric I M)
    (U : Opens M) [T2Space U] [BoundarylessManifold I U] (g' : SmoothRiemannianMetric I U)
    (T T' : (x : M) → Tensor0SSpace 2 I x) (x : U) {ε K : ℝ} (hε : ε ≤ 1 / 2)
    (hsmall : ∀ k : ℕ, k ≤ 2 → tensor0SFiberNorm G x (2 + k)
      (iteratedMetricCovariantDerivative G 2 T k x) ≤ ε)
    (hx : I.IsInteriorPoint (x : M))
    (hT : ContDiffAt ℝ 2
      (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2 (x : M) T)
      (extChartAt I (x : M) x))
    (hT' : ContDiffAt ℝ 2
      (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2 (x : M) T')
      (extChartAt I (x : M) x))
    (h0 : tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2 (x : M) T
        (extChartAt I (x : M) x) =
      tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2 (x : M) T'
        (extChartAt I (x : M) x))
    (h1 : fderiv ℝ (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2 (x : M) T)
        (extChartAt I (x : M) x) =
      fderiv ℝ (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2 (x : M) T')
        (extChartAt I (x : M) x))
    (h2 : fderiv ℝ (fderiv ℝ
        (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2 (x : M) T))
        (extChartAt I (x : M) x) =
      fderiv ℝ (fderiv ℝ
        (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2 (x : M) T'))
        (extChartAt I (x : M) x))
    (hg' : ∀ z : U, finiteMetricDifference g' (G.restrictOpen U) z =
      Tensor0SSpace.ofModel (I := I) (x := z) (Tensor0SSpace.toModel (T' (z : M))))
    (hmodel : ∀ u v w : TangentSpace I x,
      let r := riemannOp (LeviCivita (G.restrictOpen U)) x u v w
      Real.sqrt ((G.restrictOpen U).inner x r r) ≤
        K * Real.sqrt ((G.restrictOpen U).inner x u u) *
          Real.sqrt ((G.restrictOpen U).inner x v v) *
          Real.sqrt ((G.restrictOpen U).inner x w w))
    (v w : TangentSpace I x) :
    |metricRm04StandardAt g' x v w w v - metricRm04StandardAt G (x : M) v w w v| ≤
      ε * (360 + K) * G.inner x v v * G.inner x w w := by
  have hc := finiteJetI_center (I := I) U x
  have hrange : extChartAt I x x ∈ interior (range I) := by
    rw [hc]
    exact hx
  have eT := finiteJetI_eventuallyEq U T x hx
  have eT' := finiteJetI_eventuallyEq U T' x hx
  have hS : finiteMetricDifference g' (G.restrictOpen U) =
      fun z : U => Tensor0SSpace.ofModel (I := I) (x := z)
        (Tensor0SSpace.toModel (T' (z : M))) := funext hg'
  obtain ⟨dT1, dT2⟩ := finiteJetI_fderivWithin (I := I)
    (f := tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := U) 2 x
      (fun z : U => Tensor0SSpace.ofModel (I := I) (x := z) (Tensor0SSpace.toModel (T (z : M)))))
    hrange
  obtain ⟨dS1, dS2⟩ := finiteJetI_fderivWithin (I := I)
    (f := tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := U) 2 x
      (finiteMetricDifference g' (G.restrictOpen U))) hrange
  rw [hc] at dT1 dT2 dS1 dS2
  refine abs_metricRm04_sub_le_of_chart_jet_replacement G U g' T x hε hsmall ?_ ?_ ?_ ?_ ?_
    hmodel v w
  · rw [hc]
    exact (hT.congr_of_eventuallyEq eT).contDiffWithinAt
  · rw [hc, hS]
    exact (hT'.congr_of_eventuallyEq eT').contDiffWithinAt
  · rw [hc, hS, eT.eq_of_nhds, eT'.eq_of_nhds]
    exact h0
  · rw [hc, dT1, dS1, hS, eT.fderiv_eq, eT'.fderiv_eq]
    exact h1
  · rw [hc, dT2, dS2, hS]
    have e2 : fderiv ℝ (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := U) 2 x
        (fun z : U => Tensor0SSpace.ofModel (I := I) (x := z)
          (Tensor0SSpace.toModel (T (z : M))))) =ᶠ[𝓝 (extChartAt I (x : M) x)]
        fderiv ℝ (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
          (x : M) T) :=
      eT.eventuallyEq_nhds.mono fun y hy => Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hy
    have e2' : fderiv ℝ (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := U) 2 x
        (fun z : U => Tensor0SSpace.ofModel (I := I) (x := z)
          (Tensor0SSpace.toModel (T' (z : M))))) =ᶠ[𝓝 (extChartAt I (x : M) x)]
        fderiv ℝ (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
          (x : M) T') :=
      eT'.eventuallyEq_nhds.mono fun y hy => Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hy
    rw [e2.fderiv_eq, e2'.fderiv_eq]
    exact h2

end DifferentialGeometry.Geometry.Curvature
