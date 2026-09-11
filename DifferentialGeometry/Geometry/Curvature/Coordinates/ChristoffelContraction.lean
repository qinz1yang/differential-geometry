import DifferentialGeometry.Geometry.Connection.LeviCivita.Chart.Koszul
import DifferentialGeometry.Geometry.Curvature.Coordinates.RiemannTensorBridge


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Tensor.Coordinates
open Bundle Manifold Set
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem
open scoped Manifold ContDiff _root_.Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]

private theorem connectionCoefficient_differentiableAt
    (g : SmoothRiemannianMetric I M) (p : M) (y : E)
    (hy : y ∈ interior (extChartAt I p).target)
    (i j k : Fin (Module.finrank ℝ E)) :
    DifferentiableAt ℝ (chartChristoffel g p i j k) y :=
  ((chartChristoffel_contDiffOn_interior g p i j k).contDiffAt
    (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)


theorem chartChristoffelContraction_fderiv_apply
    (g : SmoothRiemannianMetric I M) (p : M) (y : E)
    (hy : y ∈ interior (extChartAt I p).target) (v w u : E) :
    fderiv ℝ (chartChristoffelContraction g p v w) y u =
      ∑ k : Fin (Module.finrank ℝ E),
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          fderiv ℝ (chartChristoffel g p i j k) y u *
            chartCoord i v * chartCoord j w) • chartModelBasis E k := by
  classical
  have hd (i j k : Fin (Module.finrank ℝ E)) :=
    connectionCoefficient_differentiableAt g p y hy i j k
  have hc (k : Fin (Module.finrank ℝ E)) :
      DifferentiableAt ℝ (fun z => ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), chartChristoffel g p i j k z *
          chartCoord i v * chartCoord j w) y :=
    DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_sum fun j _ =>
      ((hd i j k).mul_const (chartCoord i v)).mul_const (chartCoord j w)
  unfold chartChristoffelContraction
  rw [fderiv_fun_sum (fun k _ => (hc k).smul_const (chartModelBasis E k)), sum_apply]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [fderiv_smul_const (hc k), ContinuousLinearMap.smulRight_apply]
  congr 1
  rw [fderiv_fun_sum (fun i _ => DifferentiableAt.fun_sum fun j _ =>
    ((hd i j k).mul_const (chartCoord i v)).mul_const (chartCoord j w)), sum_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [fderiv_fun_sum (fun j _ =>
    ((hd i j k).mul_const (chartCoord i v)).mul_const (chartCoord j w)), sum_apply]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [fderiv_mul_const ((hd i j k).mul_const (chartCoord i v)),
    fderiv_mul_const (hd i j k)]
  simp only [smul_apply, smul_eq_mul]
  ring


theorem chartCoord_chartChristoffelContraction
    (g : SmoothRiemannianMetric I M) (p : M) (y v w : E)
    (k : Fin (Module.finrank ℝ E)) :
    chartCoord k (chartChristoffelContraction g p v w y) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartChristoffel g p i j k y * chartCoord i v * chartCoord j w := by
  classical
  simp only [chartChristoffelContraction, chartCoord, Module.Basis.repr_sum_self]


theorem chartCoord_fderiv_chartChristoffelContraction
    (g : SmoothRiemannianMetric I M) (p : M) (y : E)
    (hy : y ∈ interior (extChartAt I p).target) (v w u : E)
    (k : Fin (Module.finrank ℝ E)) :
    chartCoord k (fderiv ℝ (chartChristoffelContraction g p v w) y u) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          partialDeriv l (chartChristoffel g p i j k) y *
            chartCoord l u * chartCoord i v * chartCoord j w := by
  classical
  rw [chartChristoffelContraction_fderiv_apply g p y hy]
  simp only [chartCoord, Module.Basis.repr_sum_self]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  have hdir : fderiv ℝ (chartChristoffel g p i j k) y u =
      ∑ l : Fin (Module.finrank ℝ E),
        partialDeriv l (chartChristoffel g p i j k) y * (chartModelBasis E).repr u l := by
    conv_lhs => arg 2; rw [← (chartModelBasis E).sum_repr u]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro l _hl
    rw [map_smul]
    change (chartModelBasis E).repr u l * fderiv ℝ (chartChristoffel g p i j k) y
      (chartModelBasis E l) = _
    unfold partialDeriv
    ring
  rw [hdir, Finset.sum_mul, Finset.sum_mul]

private theorem sum_four_transpose {A : Type*} [Fintype A]
    (f : A → A → A → A → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) = ∑ j, ∑ l, ∑ i, ∑ k, f i j k l := by
  calc
    _ = ∑ j, ∑ i, ∑ k, ∑ l, f i j k l := Finset.sum_comm
    _ = ∑ j, ∑ i, ∑ l, ∑ k, f i j k l :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

private theorem curvature_contraction_coordinates {A : Type*} [Fintype A]
    (G : A → A → A → ℝ) (D : A → A → A → A → ℝ)
    (u v w : A → ℝ) (l : A) :
    (∑ i, ∑ j, ∑ k, u i * v j * w k *
      (D j i k l - D k i j l + ∑ m, (G j m l * G i k m - G k m l * G i j m))) =
      (∑ i, ∑ k, ∑ j, D j i k l * v j * u i * w k) -
      (∑ i, ∑ j, ∑ k, D k i j l * w k * u i * v j) +
      (∑ j, ∑ m, G j m l * v j * (∑ i, ∑ k, G i k m * u i * w k)) -
      (∑ k, ∑ m, G k m l * w k * (∑ i, ∑ j, G i j m * u i * v j)) := by
  have h1 : (∑ i, ∑ j, ∑ k, u i * v j * w k * D j i k l) =
      ∑ i, ∑ k, ∑ j, D j i k l * v j * u i * w k := by
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _hk
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have h2 : (∑ i, ∑ j, ∑ k, u i * v j * w k * D k i j l) =
      ∑ i, ∑ j, ∑ k, D k i j l * w k * u i * v j := by
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    apply Finset.sum_congr rfl
    intro k _hk
    ring
  have h3 : (∑ i, ∑ j, ∑ k, ∑ m, u i * v j * w k * (G j m l * G i k m)) =
      ∑ j, ∑ m, ∑ i, ∑ k, G j m l * v j * (G i k m * u i * w k) := by
    rw [sum_four_transpose]
    apply Finset.sum_congr rfl
    intro j _hj
    apply Finset.sum_congr rfl
    intro m _hm
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro k _hk
    ring
  have h4 : (∑ i, ∑ j, ∑ k, ∑ m, u i * v j * w k * (G k m l * G i j m)) =
      ∑ k, ∑ m, ∑ i, ∑ j, G k m l * w k * (G i j m * u i * v j) := by
    calc
      _ = ∑ i, ∑ k, ∑ j, ∑ m, u i * v j * w k * (G k m l * G i j m) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ k, ∑ m, ∑ i, ∑ j, u i * v j * w k * (G k m l * G i j m) :=
        sum_four_transpose _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _hk
        apply Finset.sum_congr rfl
        intro m _hm
        apply Finset.sum_congr rfl
        intro i _hi
        apply Finset.sum_congr rfl
        intro j _hj
        ring
  simp only [mul_add, mul_sub, Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  rw [h1, h2, h3, h4]
  ring


theorem chartRiemannCLM_model_eq_contractions [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) (v w u : E) :
    centeredChartTangentEquiv (I := I) x
        (chartRiemannCLM g x
          ((centeredChartTangentEquiv (I := I) x).symm v)
          ((centeredChartTangentEquiv (I := I) x).symm w)
          ((centeredChartTangentEquiv (I := I) x).symm u)) =
      fderiv ℝ (chartChristoffelContraction g x u w) (extChartAt I x x) v -
      fderiv ℝ (chartChristoffelContraction g x u v) (extChartAt I x x) w +
      chartChristoffelContraction g x v
        (chartChristoffelContraction g x u w (extChartAt I x x)) (extChartAt I x x) -
      chartChristoffelContraction g x w
        (chartChristoffelContraction g x u v (extChartAt I x x)) (extChartAt I x x) := by
  classical
  let y := extChartAt I x x
  have hy : y ∈ interior (extChartAt I x).target := by
    rw [(isOpen_extChartAt_target (I := I) x).interior_eq]
    exact (extChartAt I x).map_source (mem_extChartAt_source x)
  apply (chartModelBasis E).repr.injective
  ext l
  have hcoordAdd (a b : E) : chartCoord l (a + b) = chartCoord l a + chartCoord l b := by
    simp only [chartCoord, map_add, Finsupp.add_apply]
  have hcoordSub (a b : E) : chartCoord l (a - b) = chartCoord l a - chartCoord l b := by
    simp only [chartCoord, map_sub, Finsupp.sub_apply]
  change chartCoord l _ = chartCoord l _
  rw [chart_riemann_clm_model_apply]
  have hleft : chartCoord l
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          (chartCoord i u * chartCoord j v * chartCoord k w *
            chartRiemannTensor g x i j k m y) • chartModelBasis E m) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E), chartCoord i u * chartCoord j v * chartCoord k w *
          chartRiemannTensor g x i j k l y := by
    change (chartModelBasis E).coord l _ = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    simp only [Module.Basis.coord_apply, Module.Basis.repr_sum_self]
  change chartCoord l
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          (chartCoord i u * chartCoord j v * chartCoord k w *
            chartRiemannTensor g x i j k m y) • chartModelBasis E m) = _
  rw [hleft]
  simp only [hcoordAdd, hcoordSub,
    chartCoord_fderiv_chartChristoffelContraction g x (extChartAt I x x) hy,
    chartCoord_chartChristoffelContraction, chartRiemannTensor_def]
  exact curvature_contraction_coordinates (chartChristoffel g x · · · y)
    (fun a i j k => partialDeriv a (chartChristoffel g x i j k) y)
    (fun i => chartCoord i u) (fun j => chartCoord j v) (fun k => chartCoord k w) l

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
