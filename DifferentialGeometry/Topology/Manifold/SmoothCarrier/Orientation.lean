import DifferentialGeometry.Topology.Manifold.SmoothCarrier.Basic
import DifferentialGeometry.Topology.Manifold.OrientationCover
import DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

theorem SmoothCarrier.det_fderiv_extChartAt_pos {E X ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MetricSpace X] (A : SmoothCompatibleAtlas E X ι)
    (hpos : ∀ i j, ∀ u ∈ ((A.chart i).symm.trans (A.chart j)).source,
      0 < (fderiv ℝ ((A.chart i).symm.trans (A.chart j)) u).det)
    (c d x : SmoothCarrier A) (hx : x ∈ (chartAt E c).source ∩ (chartAt E d).source) :
    0 < (fderiv ℝ (extChartAt 𝓘(ℝ, E) d ∘ (extChartAt 𝓘(ℝ, E) c).symm)
      (extChartAt 𝓘(ℝ, E) c x)).det := by
  obtain ⟨hxc, hxd⟩ := hx
  obtain ⟨i, hi⟩ := chart_mem_atlas E c
  obtain ⟨j, hj⟩ := chart_mem_atlas E d
  have hmem : chartAt E c x ∈ ((chartAt E c).symm.trans (chartAt E d)).source := by
    refine ⟨(chartAt E c).map_source hxc, ?_⟩
    change (chartAt E c).symm (chartAt E c x) ∈ (chartAt E d).source
    rw [(chartAt E c).left_inv hxc]
    exact hxd
  have hfun : (extChartAt 𝓘(ℝ, E) d ∘ (extChartAt 𝓘(ℝ, E) c).symm : E → E) =
      ⇑((chartAt E c).symm.trans (chartAt E d)) := by
    rw [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
      OpenPartialHomeomorph.coe_trans]
  have hpt : extChartAt 𝓘(ℝ, E) c x = chartAt E c x := by
    rw [extChartAt_coe, Function.comp_apply, modelWithCornersSelf_coe, id_eq]
  rw [hfun, hpt]
  rw [← hi, ← hj, SmoothCarrier.chart_symm_trans_chart] at hmem ⊢
  exact hpos i j _ hmem

def SmoothCarrier.chartOrientation {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MetricSpace X] (A : SmoothCompatibleAtlas E X ι) {n : ℕ} (oE : Orientation ℝ E (Fin n))
    (y : SmoothCarrier A) : Orientation ℝ (TangentSpace 𝓘(ℝ, E) y) (Fin n) :=
  Orientation.map (Fin n) (tangentChartEquiv 𝓘(ℝ, E) (SmoothCarrier A) y y
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ, E)) y)).symm oE

theorem SmoothCarrier.map_tangentChartEquiv_chartOrientation {E X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MetricSpace X]
    (A : SmoothCompatibleAtlas E X ι) {n : ℕ} (hdim : Module.finrank ℝ E = n)
    (hpos : ∀ i j, ∀ u ∈ ((A.chart i).symm.trans (A.chart j)).source,
      0 < (fderiv ℝ ((A.chart i).symm.trans (A.chart j)) u).det)
    (oE : Orientation ℝ E (Fin n)) (p y : SmoothCarrier A)
    (hy : y ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).baseSet) :
    Orientation.map (Fin n) (tangentChartEquiv 𝓘(ℝ, E) (SmoothCarrier A) p y hy)
      (SmoothCarrier.chartOrientation A oE y) = oE := by
  have hyy : y ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) y).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ, E)) y
  have hC : ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) y).linearEquivAt ℝ y hyy).symm.trans
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).linearEquivAt ℝ y hy) =
      (Bundle.Trivialization.coordChangeL ℝ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) y)
        (trivializationAt E (TangentSpace 𝓘(ℝ, E)) p) y).toLinearEquiv :=
    (Bundle.Trivialization.coe_coordChangeL' (R := ℝ) (trivializationAt E (TangentSpace 𝓘(ℝ, E)) y)
      (trivializationAt E (TangentSpace 𝓘(ℝ, E)) p) ⟨hyy, hy⟩).symm
  have hyp : y ∈ (chartAt E p).source := by
    rw [← TangentBundle.trivializationAt_baseSet (I := 𝓘(ℝ, E)) p]
    exact hy
  have hx : y ∈ (chartAt E y).source ∩ (chartAt E p).source := ⟨mem_chart_source E y, hyp⟩
  have hch : DifferentialGeometry.VectorBundle.orientationChange
      (tangentBundleCore 𝓘(ℝ, E) (SmoothCarrier A)) (achart E y) (achart E p) y oE = oE :=
    (tangent_orientation_transition_positive hdim y p y hx oE).mpr
      (SmoothCarrier.det_fderiv_extChartAt_pos A hpos y p y hx)
  unfold DifferentialGeometry.VectorBundle.orientationChange at hch
  unfold SmoothCarrier.chartOrientation DifferentialGeometry.tangentChartEquiv
  rw [DifferentialGeometry.VectorBundle.map_orientation_trans_between, hC]
  exact hch

theorem SmoothCarrier.isCompatibleOrientation_chartOrientation {E X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MetricSpace X]
    (A : SmoothCompatibleAtlas E X ι) {n : ℕ} (hdim : Module.finrank ℝ E = n)
    (hpos : ∀ i j, ∀ u ∈ ((A.chart i).symm.trans (A.chart j)).source,
      0 < (fderiv ℝ ((A.chart i).symm.trans (A.chart j)) u).det)
    (oE : Orientation ℝ E (Fin n)) :
    DifferentialGeometry.VectorBundle.IsCompatibleOrientation (F := E)
      (TangentSpace 𝓘(ℝ, E) : SmoothCarrier A → Type _)
      (SmoothCarrier.chartOrientation A oE) := by
  intro x
  refine ⟨trivializationAt E (TangentSpace 𝓘(ℝ, E)) x, inferInstance,
    (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).baseSet,
    (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ, E)) x),
    fun _ hy => hy, oE, fun y hy => ?_⟩
  have hL : ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).continuousLinearEquivAt ℝ y
      hy).toLinearEquiv = tangentChartEquiv 𝓘(ℝ, E) (SmoothCarrier A) x y hy :=
    LinearEquiv.ext fun _ => rfl
  rw [hL]
  exact SmoothCarrier.map_tangentChartEquiv_chartOrientation A hdim hpos oE x y hy

theorem SmoothCarrier.exists_manifoldOrientation {E X ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MetricSpace X] (A : SmoothCompatibleAtlas E X ι)
    {n : ℕ} (hdim : Module.finrank ℝ E = n)
    (hpos : ∀ i j, ∀ u ∈ ((A.chart i).symm.trans (A.chart j)).source,
      0 < (fderiv ℝ ((A.chart i).symm.trans (A.chart j)) u).det)
    (oE : Orientation ℝ E (Fin n)) :
    ∃ O : ManifoldOrientation 𝓘(ℝ, E) (SmoothCarrier A) n,
      ∀ (p x : SmoothCarrier A)
        (hx : x ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).baseSet),
        O.inChart p x hx = oE := by
  obtain ⟨O, hO⟩ := exists_manifoldOrientation_eq_of_compatibleOrientation 𝓘(ℝ, E) hdim
    (SmoothCarrier.chartOrientation A oE)
    (SmoothCarrier.isCompatibleOrientation_chartOrientation A hdim hpos oE)
  refine ⟨O, fun p x hx => ?_⟩
  unfold DifferentialGeometry.ManifoldOrientation.inChart
  rw [hO]
  exact SmoothCarrier.map_tangentChartEquiv_chartOrientation A hdim hpos oE p x hx

end DifferentialGeometry.Topology.Manifold
