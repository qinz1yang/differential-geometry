import DifferentialGeometry.Tensor.Coordinates.Field
import DifferentialGeometry.Geometry.Connection.ChartBridge.TensorDerivative
import DifferentialGeometry.Geometry.Metric.Convergence.Coordinates.JetOperators
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.MapConvergence

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Filter Set
open scoped Manifold ContDiff _root_.Topology BigOperators
open DifferentialGeometry.Analysis DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance covariantTensorC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
private local instance covariantTensorC2 : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

private def chartTensorComponent {r : ℕ}
    (A : Tensor0SField (I := I) (M := M) (n := ∞) r) (p : M) :
    E → (Fin r → CoordinateIdx (𝕜 := ℝ) E) → ℝ :=
  fun y slots => A ((extChartAt I p).symm y)
    (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm y))

private def chartConstantFrame : CoordinateIdx (𝕜 := ℝ) E →
    (x : E) → TangentSpace 𝓘(ℝ, E) x :=
  fun i _ => chartModelBasis E i

private theorem chartIterCov_eq_iterCovComp {r : ℕ}
    (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (I := I) (M := M) (n := ∞) r) (p : M)
    {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I p).target) (a : ℕ) :
    ∀ y ∈ W, ∀ slots : Fin (r + a) → CoordinateIdx (𝕜 := ℝ) E,
      chartTensorComponent (iterCov (I := I) g r T a) p y slots =
        iterCovComp (I := 𝓘(ℝ, E)) (chartConstantFrame (E := E))
          (fun z i j k => chartChristoffel (I := I) g p i j k z)
          (chartTensorComponent T p) a y slots := by
  classical
  induction a with
  | zero => intro y hy slots; rfl
  | succ a ih =>
      intro y hy slots
      let x := (extChartAt I p).symm y
      have hx : x ∈ chartLeviCivitaGoodSet (I := I) p :=
        (mem_chartLeviCivitaGoodSet_iff_mem_extChartAt_source (I := I) p x).2
          ((extChartAt I p).map_target (hWt hy))
      have hright : extChartAt I p x = y := (extChartAt I p).right_inv (hWt hy)
      have hreal : TotalNabla0SRealizes (I := I) (r + a)
          (metricCov (I := I) g) (iterCov (I := I) g r T a)
          (iterCov (I := I) g r T (a + 1)) :=
        iterCov_realizes g T a
      have hstep := totalNabla0S_chartComponent g
        (iterCov (I := I) g r T a) (iterCov (I := I) g r T (a + 1))
        hreal p hx (slots 0) (Fin.tail slots)
      have hslots : Fin.cons (chartBasisVecFiber (I := I) p (slots 0) x)
          (fun r => chartBasisVecFiber (I := I) p (Fin.tail slots r) x) =
            (fun r => chartBasisVecFiber (I := I) p (slots r) x) := by
        funext r
        exact Fin.cases rfl (fun _ => rfl) r
      rw [hright] at hstep
      have hev : (fun z => chartTensorComponent (iterCov (I := I) g r T a) p z
          (Fin.tail slots)) =ᶠ[𝓝 y]
            (fun z => iterCovComp (I := 𝓘(ℝ, E)) (chartConstantFrame (E := E))
              (fun w i j k => chartChristoffel (I := I) g p i j k w)
              (chartTensorComponent T p) a z
              (Fin.tail slots)) :=
        Filter.eventually_of_mem (hW.mem_nhds hy) fun z hz => ih z hz (Fin.tail slots)
      calc
        _ = fderiv ℝ (fun z => chartTensorComponent (iterCov (I := I) g r T a)
              p z (Fin.tail slots)) y (chartModelBasis E (slots 0)) -
            ∑ d : Fin (r + a), ∑ k : CoordinateIdx (𝕜 := ℝ) E,
              chartChristoffel (I := I) g p (slots 0) (Fin.tail slots d) k y *
                chartTensorComponent (iterCov (I := I) g r T a) p y
                  (Function.update (Fin.tail slots) d k) :=
          (congrArg (fun w => iterCov (I := I) g r T (a + 1) x w) hslots).symm.trans hstep
        _ = _ := by
          rw [iterCovComp_succ]
          unfold covDerivStepComp frameDirectionalDerivatives
          rw [DifferentialGeometry.mvfderiv_real_eq_mfderiv, mfderiv_eq_fderiv]
          rw [hev.fderiv_eq]
          congr 1
          apply Finset.sum_congr rfl
          intro r _
          apply Finset.sum_congr rfl
          intro j _
          rw [ih y hy]

theorem iterCov_chart_components_mapCInf {r : ℕ}
    (g : ℕ → SmoothRiemannianMetric I M) (g₀ : SmoothRiemannianMetric I M)
    (A : ℕ → Tensor0SField (I := I) (M := M) (n := ∞) r)
    (A₀ : Tensor0SField (I := I) (M := M) (n := ∞) r) (p : M)
    {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I p).target)
    (hgram : ∀ i j : CoordinateIdx (𝕜 := ℝ) E, MapCInfConvergenceOnCompacts W
      (fun n => chartGramOnE (I := I) (g n) p i j) (chartGramOnE (I := I) g₀ p i j))
    (hbase : MapCInfConvergenceOnCompacts W
      (fun n y (slots : Fin r → CoordinateIdx (𝕜 := ℝ) E) =>
        A n ((extChartAt I p).symm y)
          (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm y)))
      (fun y (slots : Fin r → CoordinateIdx (𝕜 := ℝ) E) =>
        A₀ ((extChartAt I p).symm y)
          (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm y))))
    (a : ℕ) :
    MapCInfConvergenceOnCompacts W
      (fun n y (slots : Fin (r + a) → CoordinateIdx (𝕜 := ℝ) E) =>
        iterCov (I := I) (g n) r (A n) a ((extChartAt I p).symm y)
          (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm y)))
      (fun y (slots : Fin (r + a) → CoordinateIdx (𝕜 := ℝ) E) =>
        iterCov (I := I) g₀ r A₀ a ((extChartAt I p).symm y)
          (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm y))) := by
  let chr (m : SmoothRiemannianMetric I M) (y : E)
      (i j k : CoordinateIdx (𝕜 := ℝ) E) := chartChristoffel (I := I) m p i j k y
  have hcc (m : SmoothRiemannianMetric I M) : ContDiffOn ℝ ∞ (chr m) W :=
    contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => contDiffOn_pi.mpr fun k =>
      (chartChristoffel_contDiffOn_interior (I := I) m p i j k).mono
        (interior_maximal hWt hW)
  have hbc (T : Tensor0SField (I := I) (M := M) (n := ∞) r) :
      ContDiffOn ℝ ∞ (chartTensorComponent T p) W :=
    contDiffOn_pi.mpr fun slots => tensor_field_chart_components_contDiffOn T p hWt slots
  have hc : MapCInfConvergenceOnCompacts W (fun n => chr (g n)) (chr g₀) := by
    apply mapCInfConvergence_pi hW
    · intro i
      apply mapCInfConvergence_pi hW
      · intro j
        exact mapCInfConvergence_pi hW
          (fun k => mapCInfConvergence_chartChristoffel_of_gram g g₀ p hW hWt hgram i j k)
          (fun k n => contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp (hcc (g n)) i) j) k)
          (fun k => contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp (hcc g₀) i) j) k)
      · intro j n
        exact contDiffOn_pi.mp (contDiffOn_pi.mp (hcc (g n)) i) j
      · intro j
        exact contDiffOn_pi.mp (contDiffOn_pi.mp (hcc g₀) i) j
    · intro i n
      exact contDiffOn_pi.mp (hcc (g n)) i
    · intro i
      exact contDiffOn_pi.mp (hcc g₀) i
  have h := iter_comp_convergence hW (fun i => chartModelBasis E i)
    (fun n => chr (g n)) (chr g₀) (fun n => chartTensorComponent (A n) p)
    (chartTensorComponent A₀ p) hc hbase
    (fun n => hcc (g n)) (hcc g₀) (fun n => hbc (A n)) (hbc A₀) a
  exact h.congr hW
    (fun n y hy => funext fun slots => chartIterCov_eq_iterCovComp (g n) (A n) p hW hWt a y hy slots)
    (fun y hy => funext fun slots => chartIterCov_eq_iterCovComp g₀ A₀ p hW hWt a y hy slots)

end DifferentialGeometry.CheegerGromovCompactness
