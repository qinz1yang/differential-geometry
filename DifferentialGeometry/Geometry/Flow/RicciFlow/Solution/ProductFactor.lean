import DifferentialGeometry.Geometry.Metric.Family.ProductSlice
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.ProductLine

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
set_option backward.isDefEq.respectTransparency false in
private theorem mfderiv_prod_zero (x : M) (v : TangentSpace I x) :
    mfderiv I (I.prod 𝓘(ℝ, ℝ)) (fun y : M => (y, (0 : ℝ))) x v = (v, 0) := by
  exact congrArg (fun L => L v)
    (mfderiv_prod_left (I := I) (I' := 𝓘(ℝ, ℝ)) (x₀ := x) (y₀ := (0 : ℝ)))

set_option backward.isDefEq.respectTransparency false in
private theorem metricRicciAt_prod_real_horizontal
    (g : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    metricRicciAt (g.prod (euclideanMetric (E := ℝ))) (x, 0)
        (fun i => (v i, 0)) = metricRicciAt g x v := by
  have hv : v = vec2 (v 0) (v 1) := by
    funext i
    fin_cases i <;> rfl
  have hw : (fun i => (v i, (0 : ℝ))) =
      vec2 (I := I.prod 𝓘(ℝ, ℝ)) (x := (x, (0 : ℝ))) (v 0, 0) (v 1, 0) := by
    funext i
    fin_cases i <;> rfl
  rw [hw, metricRicciAt_apply_eq_ricciTensor, ricciTensor_productMetric]
  conv_rhs => rw [hv, metricRicciAt_apply_eq_ricciTensor]
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem metricRm04At_prod_real_horizontal
    (g : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 4 → TangentSpace I x) :
    metricRm04At (g.prod (euclideanMetric (E := ℝ))) (x, 0)
        (fun i => (v i, 0)) = metricRm04At g x v := by
  rw [metricRm04At_productMetric_apply]
  have hz : metricRm04At (euclideanMetric (E := ℝ)) (0 : ℝ)
      (fun _ : Fin 4 => (0 : ℝ)) = 0 :=
    (metricRm04At (euclideanMetric (E := ℝ)) (0 : ℝ)).map_coord_zero
      (i := 0) rfl
  rw [hz, add_zero]

set_option backward.isDefEq.respectTransparency false in
private theorem scalar_prod_real_slice
    {D : RealTimeInterval}
    (S : SolutionOn (I := I.prod 𝓘(ℝ, ℝ)) (M := M × ℝ) D)
    (t : ℝ)
    (hprod : S.family.metric t =
      ((S.family.metric t).sliceFst (0 : ℝ)).prod (euclideanMetric (E := ℝ)))
    (x : M) :
    S.scalar t (x, 0) = metricScalarAt ((S.family.metric t).sliceFst (0 : ℝ)) x := by
  change metricScalarAt (S.family.metric t) (x, 0) = _
  conv_lhs => rw [hprod]
  rw [metricScalarAt_productMetric,
    metricScalarAt_eq_zero_of_finrank_le_one (euclideanMetric (E := ℝ))
      (by simp : Module.finrank ℝ ℝ ≤ 1), add_zero]

set_option backward.isDefEq.respectTransparency false in
theorem isSolutionOn_sliceFst_of_prod_euclidean
    {D : RealTimeInterval}
    (S : SolutionOn (I := I.prod 𝓘(ℝ, ℝ)) (M := M × ℝ) D)
    (hS : IsSolutionOn S)
    (hprod : ∀ t ∈ D.carrier, S.family.metric t =
      ((S.family.metric t).sliceFst (0 : ℝ)).prod (euclideanMetric (E := ℝ))) :
    IsSolutionOn ({ base := { metric := fun t =>
      (S.family.metric t).sliceFst (0 : ℝ) } } : SolutionOn (I := I) (M := M) D) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let g : ℝ → SmoothRiemannianMetric I M :=
    fun t => (S.family.metric t).sliceFst (0 : ℝ)
  let Y : M → M × ℝ := fun x => (x, 0)
  have hY : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞ Y :=
    contMDiff_id.prodMk contMDiff_const
  have hmetric : MetricFamilySmoothOn D g := hS.smoothMetric.sliceFst 0
  have hscalar (t : ℝ) (ht : t ∈ D.carrier) (x : M) :
      S.scalar t (x, 0) = metricScalarAt (g t) x :=
    scalar_prod_real_slice S t (hprod t ht) x
  apply isSolutionOn_of_reg g hmetric
  · intro t ht x v w
    have hder := metricDerivAt S hS ⟨t, ht⟩ (x, 0) (v, 0) (w, 0)
    have hric : ricciTensor (S.family.metric t) (x, 0) (v, 0) (w, 0) =
        ricciTensor (g t) x v w := by
      rw [hprod t (D.regular_subset ht), ricciTensor_productMetric]
      simp only [map_zero, add_zero]
      rfl
    have hder' : HasDerivAt
        (fun s : ℝ => (S.family.metric s).inner (x, 0) (v, 0) (w, 0))
        (-2 * ricciTensor (S.family.metric t) (x, 0) (v, 0) (w, 0)) t := by
      simpa only [SolutionOn.ricciAt, SolutionFamily.ricciAt,
        metricRicciAt_apply_eq_ricciTensor, SolutionOn.family_metric] using hder
    rw [hric] at hder'
    exact hder'
  · have hmap : Continuous (fun p : ℝ × M => (p.1, Y p.2)) :=
      continuous_fst.prodMk (hY.continuous.comp continuous_snd)
    apply (hS.scalarCont.comp hmap.continuousOn
      (fun p hp => ⟨hp.1, mem_univ _⟩)).congr
    intro p hp
    exact (hscalar p.1 hp.1 p.2).symm
  · intro t ht x
    exact (hS.scalarTime ht (Subset.refl _) (x, 0)).congr
      (fun s hs => (hscalar s hs x).symm) (hscalar t ht x).symm
  · have hpull := tensor0SFamilyContinuousOnSet.pullback_of_contMDiff
      (fun t x => S.ricci t x) hS.ricciCont Y (hY.of_le (by norm_num))
    apply hpull.congr
    intro t ht x
    apply ContinuousMultilinearMap.ext
    intro v
    change metricRicciAt (S.family.metric t) (x, 0)
      (fun i => mfderiv I (I.prod 𝓘(ℝ, ℝ)) Y x (v i)) = _
    simp only [Y, mfderiv_prod_zero]
    rw [hprod t ht]
    exact metricRicciAt_prod_real_horizontal (g t) x v
  · have hpull := tensor0SFamilyContinuousOnSet.pullback_of_contMDiff
      (fun t x => S.base.rm04 t x) hS.rm04Cont Y (hY.of_le (by norm_num))
    apply hpull.congr
    intro t ht x
    apply ContinuousMultilinearMap.ext
    intro v
    change metricRm04At (S.family.metric t) (x, 0)
      (fun i => mfderiv I (I.prod 𝓘(ℝ, ℝ)) Y x (v i)) = _
    simp only [Y, mfderiv_prod_zero]
    rw [hprod t ht]
    exact metricRm04At_prod_real_horizontal (g t) x v


end DifferentialGeometry.PDE.RicciFlow
