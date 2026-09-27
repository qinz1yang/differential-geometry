import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessNormContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ClosedWindowTimeJets
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Existence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.LaplacianBoundScaling


set_option autoImplicit false
noncomputable section
open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem mapCInf_sub_on_open {V : Set E} (hV : IsOpen V)
    {f g : ℕ → E → ℝ} {f₀ g₀ : E → ℝ}
    (hf : MapCInfConvergenceOnCompacts V f f₀) (hg : MapCInfConvergenceOnCompacts V g g₀)
    (hfc : ∀ n, ContDiffOn ℝ ∞ (f n) V) (hf₀c : ContDiffOn ℝ ∞ f₀ V)
    (hgc : ∀ n, ContDiffOn ℝ ∞ (g n) V) (hg₀c : ContDiffOn ℝ ∞ g₀ V) :
    MapCInfConvergenceOnCompacts V (fun n y => f n y - g n y) (fun y => f₀ y - g₀ y) := by
  have hp := mapCInfConvergence_prodMk hV hf hg hfc hf₀c hgc hg₀c
  have hsubc : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => z.1 - z.2) Set.univ :=
    contDiffOn_fst.sub contDiffOn_snd
  have hcomp := MapCInfConvergenceOnCompacts.comp hV isOpen_univ hp
    (mapCInfConvergence_const (U := (Set.univ : Set (ℝ × ℝ))) (fun z : ℝ × ℝ => z.1 - z.2))
    (fun n => (hfc n).prodMk (hgc n)) (hf₀c.prodMk hg₀c)
    (fun _ => hsubc) hsubc
    (mapsTo_univ _ _) (fun _ => mapsTo_univ _ _)
  exact hcomp

end Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance normalizedNormC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)


theorem weighted_error_covariant_norm_tendsto
    (g : ℝ → SmoothRiemannianMetric I M)
    (A B : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2) (p : M)
    {V : Set E} (hV : IsOpen V) (hVt : V ⊆ (extChartAt I p).target)
    {J L : Set ℝ}
    (hgram : ∀ i j : Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
      (fun z : ℝ × E => chartGramOnE (I := I) (g z.1) p i j z.2) (L ×ˢ V))
    (hA : ∀ slots : Fin 2 → Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
      (fun z : ℝ × E => A z.1 ((extChartAt I p).symm z.2)
        (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z.2))) (J ×ˢ V))
    (hB : ∀ slots : Fin 2 → Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
      (fun z : ℝ × E => B z.1 ((extChartAt I p).symm z.2)
        (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z.2))) (L ×ˢ V))
    (tau upsilon : ℕ → ℝ) (htau : ∀ n, tau n ∈ J) (hupsilon : ∀ n, upsilon n ∈ L)
    {t u : ℝ} (ht : t ∈ J) (hu : u ∈ L)
    (htlim : Tendsto tau atTop (𝓝 t)) (hulim : Tendsto upsilon atTop (𝓝 u))
    (c alpha beta : ℕ → ℝ) (hc : ∀ n, 0 < c n)
    {c₀ alpha₀ beta₀ : ℝ} (hc₀ : 0 < c₀)
    (hclim : Tendsto c atTop (𝓝 c₀))
    (halim : Tendsto alpha atTop (𝓝 alpha₀)) (hblim : Tendsto beta atTop (𝓝 beta₀))
    {K : Set E} (hK : IsCompact K) (hKV : K ⊆ V)
    (z : ℕ → E) (hzK : ∀ n, z n ∈ K) {z₀ : E} (hz₀ : z₀ ∈ K)
    (hz : Tendsto z atTop (𝓝 z₀)) (a : ℕ) :
    Tendsto (fun n => tensor02CovDerivNormWith (I := I) a
      (alpha n • A (tau n) - beta n • B (upsilon n))
      (scaleMetric (c n) (hc n) (g (upsilon n)))
      (scaleMetric (c n) (hc n) (g (upsilon n))) ((extChartAt I p).symm (z n)))
      atTop (𝓝 (tensor02CovDerivNormWith (I := I) a
        (alpha₀ • A t - beta₀ • B u)
        (scaleMetric c₀ hc₀ (g u)) (scaleMetric c₀ hc₀ (g u)) ((extChartAt I p).symm z₀))) := by
  apply tensor02_covariant_norm_tendsto_of_smooth_chart_convergence
    (fun n => scaleMetric (c n) (hc n) (g (upsilon n))) (scaleMetric c₀ hc₀ (g u))
    (fun n => alpha n • A (tau n) - beta n • B (upsilon n))
    (alpha₀ • A t - beta₀ • B u) p hV hVt ?_ ?_ hK hKV z hzK hz₀ hz a
  · intro i j
    convert mapCInfConvergenceOnCompacts_smul_of_tendsto_parameter
      (G := fun s y => chartGramOnE (I := I) (g s) p i j y)
      hV (hgram i j) upsilon hupsilon hu hulim c hclim using 1
    · funext n y
      simp [chartGramOnE,
        DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply, scaleMetric_inner]
    · funext y
      simp [chartGramOnE,
        DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply, scaleMetric_inner]
  · intro slots
    let f (s : ℝ) (y : E) := A s ((extChartAt I p).symm y)
      (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm y))
    let k (s : ℝ) (y : E) := B s ((extChartAt I p).symm y)
      (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm y))
    have hfc (s : ℝ) (hs : s ∈ J) : ContDiffOn ℝ ∞ (f s) V :=
      (hA slots).comp (f := fun y => (s, y)) (contDiffOn_const.prodMk contDiffOn_id)
        (fun _ hy => ⟨hs, hy⟩)
    have hkc (s : ℝ) (hs : s ∈ L) : ContDiffOn ℝ ∞ (k s) V :=
      (hB slots).comp (f := fun y => (s, y)) (contDiffOn_const.prodMk contDiffOn_id)
        (fun _ hy => ⟨hs, hy⟩)
    have hh := mapCInf_sub_on_open hV
      (mapCInfConvergenceOnCompacts_smul_of_tendsto_parameter
        (G := f) hV (hA slots) tau htau ht htlim alpha halim)
      (mapCInfConvergenceOnCompacts_smul_of_tendsto_parameter
        (G := k) hV (hB slots) upsilon hupsilon hu hulim beta hblim)
      (fun n => contDiffOn_const.mul (hfc (tau n) (htau n)))
      (contDiffOn_const.mul (hfc t ht))
      (fun n => contDiffOn_const.mul (hkc (upsilon n) (hupsilon n)))
      (contDiffOn_const.mul (hkc u hu))
    simpa only [ContMDiffSection.coe_sub, ContMDiffSection.coe_smul, Pi.sub_apply,
      Pi.smul_apply, Tensor0SSpace.sub_apply, Tensor0SSpace.smul_apply, smul_eq_mul] using hh

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
