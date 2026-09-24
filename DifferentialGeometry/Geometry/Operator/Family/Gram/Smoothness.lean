import DifferentialGeometry.Geometry.Operator.Family.Gram.Basic

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry.Curvature

open Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.Measure
open Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (∞ : WithTop ℕ∞) M]

theorem chartGramOp_smooth {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (alpha : M) {K : Set E}
    (hK : K ⊆ interior (extChartAt I alpha).target) :
    ContDiffOn Real ∞ (chartGramOp (I := I) G alpha) (D.regular ×ˢ K) := by
  classical
  have hentry : ∀ i j : Fin (Module.finrank Real E),
      ContDiffOn Real ∞
        (fun p : Real × E =>
          chartGramOnE (I := I) (G.metric p.1) alpha i j p.2)
        (D.regular ×ˢ K) := by
    intro i j
    exact (hG.chartGramOnE_contDiffOn Subset.rfl alpha i j).mono
      (prod_mono_right hK)
  have hbilin : ContDiffOn Real ∞
      (fun p : Real × E =>
        chartGramBilin (E := E) (I := I) (M := M) (G.metric p.1) alpha
          ((extChartAt I alpha).symm p.2))
      (D.regular ×ˢ K) := by
    rw [contDiffOn_clm_apply]
    intro v
    rw [contDiffOn_clm_apply]
    intro w
    have hscalar : ContDiffOn Real ∞
        (fun p : Real × E =>
          ∑ j : Fin (Module.finrank Real E), ∑ k : Fin (Module.finrank Real E),
            chartGramOnE (I := I) (G.metric p.1) alpha j k p.2 *
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun v j *
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun w k)
        (D.regular ×ˢ K) := by
      exact ContDiffOn.sum fun j _ => ContDiffOn.sum fun k _ =>
        ((hentry j k).mul contDiffOn_const).mul contDiffOn_const
    simpa only [chartGramBilin_apply, chartGramOnE_def] using hscalar
  exact (IsCoercive.gramCLM (F := E)).contDiff.comp_contDiffOn hbilin

end DifferentialGeometry.Geometry.Curvature

end

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Curvature

open Geometry.Operator DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

private def gramBasisOp (i j : Fin (Module.finrank ℝ E)) : E →L[ℝ] E :=
  IsCoercive.gramCLM ((chartCoordCLM E i).smulRight (chartCoordCLM E j))

omit [I.Boundaryless] in
private theorem chartGramOp_eq_sum_basis (G : MetricConnectionFamilyOn (I := I) (M := M) D)
    (p : M) (z : ℝ × E) :
    chartGramOp G p z = ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) (G.metric z.1) p i j z.2 • gramBasisOp (E := E) i j := by
  change IsCoercive.gramCLM (∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) (G.metric z.1) p i j z.2 •
          (chartCoordCLM E i).smulRight (chartCoordCLM E j)) = _
  simp only [map_sum, map_smul, gramBasisOp]

private theorem chartGramOp_spatial_hasFDerivAt
    (G : MetricConnectionFamilyOn (I := I) (M := M) D) (p : M)
    (t : ℝ) {x : E} (hx : x ∈ (extChartAt I p).target) :
    HasFDerivAt (fun y : E => chartGramOp G p (t, y))
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (fderiv ℝ (chartGramOnE (I := I) (G.metric t) p i j) x).smulRight
          (gramBasisOp (E := E) i j)) x := by
  have hd (i j : Fin (Module.finrank ℝ E)) :=
    ((chartGramOnE_contDiffOn (I := I) (G.metric t) p i j).contDiffAt
      ((isOpen_extChartAt_target (I := I) p).mem_nhds hx)).differentiableAt (by simp)
  have h := HasFDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) fun j _ =>
      (hd i j).hasFDerivAt.smul_const (gramBasisOp (E := E) i j)
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun y =>
    chartGramOp_eq_sum_basis G p (t, y))

theorem chartGramOp_spatial_fderiv_continuousOn
    (G : MetricConnectionFamilyOn (I := I) (M := M) D) (p : M)
    {U : Set (ℝ × E)} (hU : ∀ z ∈ U, z.2 ∈ (extChartAt I p).target)
    (hentry : ∀ i j : Fin (Module.finrank ℝ E), ContinuousOn
      (fun z : ℝ × E => iteratedFDeriv ℝ 1
        (chartGramOnE (I := I) (G.metric z.1) p i j) z.2) U) :
    ContinuousOn (fun z : ℝ × E => fderiv ℝ
      (fun y : E => chartGramOp G p (z.1, y)) z.2) U := by
  have hd (i j : Fin (Module.finrank ℝ E)) : ContinuousOn
      (fun z : ℝ × E => fderiv ℝ
        (chartGramOnE (I := I) (G.metric z.1) p i j) z.2) U := by
    rw [continuousOn_clm_apply]
    intro w
    have h := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => E) ℝ
      (fun _ : Fin 1 => w)).continuous.comp_continuousOn (hentry i j)
    exact h.congr fun z _ => by
      simp only [Function.comp_apply]
      exact (iteratedFDeriv_one_apply (fun _ : Fin 1 => w)).symm
  have hterm (i j : Fin (Module.finrank ℝ E)) : ContinuousOn
      (fun z : ℝ × E =>
        (fderiv ℝ (chartGramOnE (I := I) (G.metric z.1) p i j) z.2).smulRight
          (gramBasisOp (E := E) i j)) U := by
    rw [continuousOn_clm_apply]
    intro w
    exact ((hd i j).clm_apply continuousOn_const).smul continuousOn_const
  have hsum := continuousOn_finsetSum Finset.univ fun i _ =>
    continuousOn_finsetSum Finset.univ fun j _ => hterm i j
  exact hsum.congr fun z hz =>
    (chartGramOp_spatial_hasFDerivAt G p z.1 (hU z hz)).fderiv

omit [I.Boundaryless] in
theorem chartGramOp_spatial_fderiv_eq
    (G : MetricConnectionFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (p : M) {t : ℝ} {x : E} (ht : t ∈ D.regular)
    (hx : x ∈ interior (extChartAt I p).target) :
    fderiv ℝ (fun y : E => chartGramOp G p (t, y)) x =
      (fderiv ℝ (chartGramOp G p) (t, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ E) := by
  have hs := chartGramOp_smooth hG p (K := interior (extChartAt I p).target) Subset.rfl
  have hd := (hs.contDiffAt
    ((D.regular_isOpen.prod isOpen_interior).mem_nhds (show (t, x) ∈
      D.regular ×ˢ interior (extChartAt I p).target from ⟨ht, hx⟩))).differentiableAt (by simp)
  have hi : HasFDerivAt (fun y : E => (t, y)) (ContinuousLinearMap.inr ℝ ℝ E) x :=
    (hasFDerivAt_const (𝕜 := ℝ) (x := x) (c := t)).prodMk (hasFDerivAt_id x)
  exact (hd.hasFDerivAt.comp x hi).fderiv

end DifferentialGeometry.Geometry.Curvature

end
