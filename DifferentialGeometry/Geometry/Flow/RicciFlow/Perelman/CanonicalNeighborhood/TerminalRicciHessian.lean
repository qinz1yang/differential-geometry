import DifferentialGeometry.Geometry.Connection.ChartBridge.TensorDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalRicciJetOperators
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ConcurrentRicciEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Regularity.Joint
import DifferentialGeometry.Tensor.RSTensor.Coordinates.CoordinateBasis

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open Bundle Filter Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

export DifferentialGeometry.Geometry.Connection (totalNabla0S_chartComponent)

private def chartNablaRicComponent (g : SmoothRiemannianMetric I M) (p : M)
    (a i j : CoordinateIdx (𝕜 := ℝ) E) (y : E) : ℝ :=
  let x := (extChartAt I p).symm y
  metricNablaRic (I := I) g x
    (vec3 (chartBasisVecFiber (I := I) p a x) (chartBasisVecFiber (I := I) p i x)
      (chartBasisVecFiber (I := I) p j x))

private def chartNabla2RicComponent (g : SmoothRiemannianMetric I M) (p : M)
    (d a i j : CoordinateIdx (𝕜 := ℝ) E) (y : E) : ℝ :=
  let x := (extChartAt I p).symm y
  metricNabla2Ric (I := I) g x
    (vec4 (chartBasisVecFiber (I := I) p d x) (chartBasisVecFiber (I := I) p a x)
      (chartBasisVecFiber (I := I) p i x) (chartBasisVecFiber (I := I) p j x))

omit [SigmaCompactSpace M] in
private theorem chartNablaRicComponent_eq [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (p : M) (a i j : CoordinateIdx (𝕜 := ℝ) E)
    {y : E} (hy : y ∈ (extChartAt I p).target) :
    chartNablaRicComponent g p a i j y =
      partialDeriv (E := E) a (chartRicciTensor (I := I) g p i j) y -
        ∑ k, chartChristoffel (I := I) g p a i k y * chartRicciTensor (I := I) g p k j y -
        ∑ k, chartChristoffel (I := I) g p a j k y * chartRicciTensor (I := I) g p i k y := by
  let x := (extChartAt I p).symm y
  let K : Fin 3 → CoordinateIdx (𝕜 := ℝ) E := Fin.cons a (Fin.cons i (fun _ => j))
  have hxgood : x ∈ chartLeviCivitaGoodSet (I := I) p :=
    (mem_chartLeviCivitaGoodSet_iff_mem_extChartAt_source (I := I) p x).2
      ((extChartAt I p).map_target hy)
  have hright : extChartAt I p x = y := (extChartAt I p).right_inv hy
  have hraw := nablaRicChartComp (I := I) g (metricRicci (I := I) g) (fun _ => rfl) p K hxgood
  have hslots : (fun r : Fin 3 => chartBasisVecFiber (I := I) p (K r) x) =
      vec3 (chartBasisVecFiber (I := I) p a x) (chartBasisVecFiber (I := I) p i x)
        (chartBasisVecFiber (I := I) p j x) := by
    funext r
    fin_cases r <;> rfl
  rw [hslots, show K 0 = a from rfl, show K 1 = i from rfl,
    show K 2 = j from rfl, hright] at hraw
  exact hraw

omit [SigmaCompactSpace M] in
private theorem chartNabla2RicComponent_eq [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (p : M) (d a i j : CoordinateIdx (𝕜 := ℝ) E)
    {y : E} (hy : y ∈ (extChartAt I p).target) :
    chartNabla2RicComponent g p d a i j y =
      partialDeriv (E := E) d (chartNablaRicComponent g p a i j) y -
        ∑ k, chartChristoffel (I := I) g p d a k y * chartNablaRicComponent g p k i j y -
        ∑ k, chartChristoffel (I := I) g p d i k y * chartNablaRicComponent g p a k j y -
        ∑ k, chartChristoffel (I := I) g p d j k y * chartNablaRicComponent g p a i k y := by
  classical
  let x := (extChartAt I p).symm y
  let slots : Fin 3 → CoordinateIdx (𝕜 := ℝ) E := Fin.cons a (Fin.cons i (fun _ => j))
  have hxgood : x ∈ chartLeviCivitaGoodSet (I := I) p :=
    (mem_chartLeviCivitaGoodSet_iff_mem_extChartAt_source (I := I) p x).2
      ((extChartAt I p).map_target hy)
  have hright : extChartAt I p x = y := (extChartAt I p).right_inv hy
  have hreal : TotalNabla0SRealizes (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      3 (metricCov (I := I) g) (metricNablaRic (I := I) g) (metricNabla2Ric (I := I) g) := by
    exact totalNabla0S_realizes (𝕜 := ℝ) (I := I) 3 (metricCov (I := I) g)
      (metricNablaRic (I := I) g)
      (totalNabla0S_regularity (I := I) 3 (metricCov (I := I) g) (metricCov_smooth (I := I) g)
        (metricNablaRic (I := I) g))
  have hstep := totalNabla0S_chartComponent g (metricNablaRic (I := I) g)
    (metricNabla2Ric (I := I) g) hreal p hxgood d slots
  have hvec (z : M) : (fun r : Fin 3 => chartBasisVecFiber (I := I) p (slots r) z) =
      vec3 (chartBasisVecFiber (I := I) p a z) (chartBasisVecFiber (I := I) p i z)
        (chartBasisVecFiber (I := I) p j z) := by
    funext r
    fin_cases r <;> rfl
  have hcons : Fin.cons (chartBasisVecFiber (I := I) p d x)
      (fun r : Fin 3 => chartBasisVecFiber (I := I) p (slots r) x) =
      vec4 (chartBasisVecFiber (I := I) p d x) (chartBasisVecFiber (I := I) p a x)
        (chartBasisVecFiber (I := I) p i x) (chartBasisVecFiber (I := I) p j x) := by
    funext r
    fin_cases r <;> rfl
  have hupdate₀ (k : CoordinateIdx (𝕜 := ℝ) E) :
      (fun r => chartBasisVecFiber (I := I) p (Function.update slots 0 k r) x) =
      vec3 (chartBasisVecFiber (I := I) p k x) (chartBasisVecFiber (I := I) p i x)
        (chartBasisVecFiber (I := I) p j x) := by
    funext r
    fin_cases r <;> simp [slots, vec3, Function.update]
    rfl
  have hupdate₁ (k : CoordinateIdx (𝕜 := ℝ) E) :
      (fun r => chartBasisVecFiber (I := I) p (Function.update slots 1 k r) x) =
      vec3 (chartBasisVecFiber (I := I) p a x) (chartBasisVecFiber (I := I) p k x)
        (chartBasisVecFiber (I := I) p j x) := by
    funext r
    fin_cases r <;> simp [slots, vec3, Function.update]
    rfl
  have hupdate₂ (k : CoordinateIdx (𝕜 := ℝ) E) :
      (fun r => chartBasisVecFiber (I := I) p (Function.update slots 2 k r) x) =
      vec3 (chartBasisVecFiber (I := I) p a x) (chartBasisVecFiber (I := I) p i x)
        (chartBasisVecFiber (I := I) p k x) := by
    funext r
    fin_cases r <;> simp [slots, vec3, Function.update]
  rw [hcons, hright, Fin.sum_univ_three] at hstep
  simp only [hvec, hupdate₀, hupdate₁, hupdate₂,
    show slots 0 = a from rfl, show slots 1 = i from rfl, show slots 2 = j from rfl] at hstep
  unfold partialDeriv chartNabla2RicComponent chartNablaRicComponent
  simpa only [x, sub_add_eq_sub_sub] using hstep

open DifferentialGeometry.CheegerGromovCompactness

omit [FiniteDimensional ℝ E] in
theorem mapCInfConvergence_scalar_binopOn {W : Set E} (hW : IsOpen W)
    (B : ℝ × ℝ → ℝ) (hB : ContDiff ℝ ∞ B)
    {f h : ℕ → E → ℝ} {f₀ h₀ : E → ℝ}
    (hf : MapCInfConvergenceOnCompacts W f f₀) (hh : MapCInfConvergenceOnCompacts W h h₀)
    (hfc : ∀ n, ContDiffOn ℝ ∞ (f n) W) (hf₀c : ContDiffOn ℝ ∞ f₀ W)
    (hhc : ∀ n, ContDiffOn ℝ ∞ (h n) W) (hh₀c : ContDiffOn ℝ ∞ h₀ W) :
    MapCInfConvergenceOnCompacts W (fun n y => B (f n y, h n y)) (fun y => B (f₀ y, h₀ y)) := by
  exact MapCInfConvergenceOnCompacts.comp hW isOpen_univ
    (mapCInfConvergence_prodMk hW hf hh hfc hf₀c hhc hh₀c) (mapCInfConvergence_const B)
    (fun n => (hfc n).prodMk (hhc n)) (hf₀c.prodMk hh₀c)
    (fun _ => hB.contDiffOn) hB.contDiffOn (fun _ _ => Set.mem_univ _)
    (fun _ _ _ => Set.mem_univ _)

omit [FiniteDimensional ℝ E] in
theorem mapCInfConvergence_sumOn {J : Type*} {W : Set E} (hW : IsOpen W) (s : Finset J)
    {f : J → ℕ → E → ℝ} {f₀ : J → E → ℝ}
    (hf : ∀ i, MapCInfConvergenceOnCompacts W (f i) (f₀ i))
    (hfc : ∀ i n, ContDiffOn ℝ ∞ (f i n) W) (hf₀c : ∀ i, ContDiffOn ℝ ∞ (f₀ i) W) :
    MapCInfConvergenceOnCompacts W (fun n y => ∑ i ∈ s, f i n y) (fun y => ∑ i ∈ s, f₀ i y) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simpa only [Finset.sum_empty] using (mapCInfConvergence_const (fun _ : E => (0 : ℝ)) (U := W))
  | @insert i s his ih =>
      have hsum := mapCInfConvergence_scalar_binopOn hW (fun z => z.1 + z.2)
        (contDiff_fst.add contDiff_snd) (hf i) ih (hfc i) (hf₀c i)
        (fun n => ContDiffOn.sum fun j _ => hfc j n) (ContDiffOn.sum fun j _ => hf₀c j)
      simpa only [Finset.sum_insert his] using hsum

omit [FiniteDimensional ℝ E] in
private theorem mapCInfConvergence_fderivApplyOn {W : Set E} (hW : IsOpen W)
    {f : ℕ → E → ℝ} {f₀ : E → ℝ} (hf : MapCInfConvergenceOnCompacts W f f₀)
    (hfc : ∀ n, ContDiffOn ℝ ∞ (f n) W) (hf₀c : ContDiffOn ℝ ∞ f₀ W) (v : E) :
    MapCInfConvergenceOnCompacts W (fun n y => fderiv ℝ (f n) y v) (fun y => fderiv ℝ f₀ y v) := by
  exact mapCInfConvergence_clm hW (ContinuousLinearMap.apply ℝ ℝ v)
    (hf.fderivOn hW hfc hf₀c)
    (fun n => (hfc n).fderiv_of_isOpen hW (m := ∞) (by simp))
    (hf₀c.fderiv_of_isOpen hW (m := ∞) (by simp))

omit [SigmaCompactSpace M] in
private theorem chartNablaRicComponent_smooth [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (p : M) (a i j : CoordinateIdx (𝕜 := ℝ) E)
    {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I p).target) :
    ContDiffOn ℝ ∞ (chartNablaRicComponent g p a i j) W := by
  have hRi (u v : CoordinateIdx (𝕜 := ℝ) E) :=
    (chartRicciTensor_contDiffOn_interior (I := I) g p u v).mono (interior_maximal hWt hW)
  have hGa (u v w : CoordinateIdx (𝕜 := ℝ) E) :=
    (chartChristoffel_contDiffOn_interior (I := I) g p u v w).mono (interior_maximal hWt hW)
  have hpart : ContDiffOn ℝ ∞ (fun y => partialDeriv (E := E) a
      (chartRicciTensor (I := I) g p i j) y) W :=
    ((hRi i j).fderiv_of_isOpen hW (m := ∞) (by simp)).clm_apply contDiffOn_const
  exact ((hpart.sub (ContDiffOn.sum fun k _ => (hGa a i k).mul (hRi k j))).sub
    (ContDiffOn.sum fun k _ => (hGa a j k).mul (hRi i k))).congr
      (fun y hy => chartNablaRicComponent_eq g p a i j (hWt hy))

omit [SigmaCompactSpace M] in
private theorem mapCInfConvergence_chartNablaRic_of_gram [I.Boundaryless]
    (g : ℕ → SmoothRiemannianMetric I M) (g₀ : SmoothRiemannianMetric I M) (p : M)
    {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I p).target)
    (hgram : ∀ i j : CoordinateIdx (𝕜 := ℝ) E, MapCInfConvergenceOnCompacts W
      (fun n => chartGramOnE (I := I) (g n) p i j) (chartGramOnE (I := I) g₀ p i j))
    (a i j : CoordinateIdx (𝕜 := ℝ) E) :
    MapCInfConvergenceOnCompacts W (fun n => chartNablaRicComponent (g n) p a i j)
      (chartNablaRicComponent g₀ p a i j) := by
  have hRi (u v) := mapCInfConvergence_chartRicci_of_gram g g₀ p hW hWt hgram u v
  have hGa (u v w) := mapCInfConvergence_chartChristoffel_of_gram g g₀ p hW hWt hgram u v w
  have hRc (h : SmoothRiemannianMetric I M) (u v) :=
    (chartRicciTensor_contDiffOn_interior (I := I) h p u v).mono (interior_maximal hWt hW)
  have hGc (h : SmoothRiemannianMetric I M) (u v w) :=
    (chartChristoffel_contDiffOn_interior (I := I) h p u v w).mono (interior_maximal hWt hW)
  have hprod (u v w l m) := mapCInfConvergence_scalar_binopOn hW (fun z => z.1 * z.2)
    (contDiff_fst.mul contDiff_snd) (hGa u v w) (hRi l m)
    (fun n => hGc (g n) u v w) (hGc g₀ u v w)
    (fun n => hRc (g n) l m) (hRc g₀ l m)
  have hs₁ := mapCInfConvergence_sumOn hW Finset.univ (fun k => hprod a i k k j)
    (fun k n => (hGc (g n) a i k).mul (hRc (g n) k j))
    (fun k => (hGc g₀ a i k).mul (hRc g₀ k j))
  have hs₂ := mapCInfConvergence_sumOn hW Finset.univ (fun k => hprod a j k i k)
    (fun k n => (hGc (g n) a j k).mul (hRc (g n) i k))
    (fun k => (hGc g₀ a j k).mul (hRc g₀ i k))
  have hpart := mapCInfConvergence_fderivApplyOn hW (hRi i j)
    (fun n => hRc (g n) i j) (hRc g₀ i j) (chartModelBasis E a)
  have hpc (h : SmoothRiemannianMetric I M) : ContDiffOn ℝ ∞
      (fun y => partialDeriv (E := E) a (chartRicciTensor (I := I) h p i j) y) W :=
    ((hRc h i j).fderiv_of_isOpen hW (m := ∞) (by simp)).clm_apply contDiffOn_const
  have hs₁c (h : SmoothRiemannianMetric I M) : ContDiffOn ℝ ∞
      (fun y => ∑ k, chartChristoffel (I := I) h p a i k y * chartRicciTensor (I := I) h p k j y) W :=
    ContDiffOn.sum fun k _ => (hGc h a i k).mul (hRc h k j)
  have hs₂c (h : SmoothRiemannianMetric I M) : ContDiffOn ℝ ∞
      (fun y => ∑ k, chartChristoffel (I := I) h p a j k y * chartRicciTensor (I := I) h p i k y) W :=
    ContDiffOn.sum fun k _ => (hGc h a j k).mul (hRc h i k)
  have hfirst := mapCInfConvergence_scalar_binopOn hW (fun z => z.1 - z.2)
    (contDiff_fst.sub contDiff_snd) hpart hs₁
    (fun n => hpc (g n)) (hpc g₀) (fun n => hs₁c (g n)) (hs₁c g₀)
  have hresult := mapCInfConvergence_scalar_binopOn hW (fun z => z.1 - z.2)
    (contDiff_fst.sub contDiff_snd) hfirst hs₂
    (fun n => (hpc (g n)).sub (hs₁c (g n))) ((hpc g₀).sub (hs₁c g₀))
    (fun n => hs₂c (g n)) (hs₂c g₀)
  exact hresult.congr hW
    (fun n y hy => chartNablaRicComponent_eq (g n) p a i j (hWt hy))
    (fun y hy => chartNablaRicComponent_eq g₀ p a i j (hWt hy))

omit [SigmaCompactSpace M] in
private theorem mapCInfConvergence_chartNabla2Ric_of_gram [I.Boundaryless]
    (g : ℕ → SmoothRiemannianMetric I M) (g₀ : SmoothRiemannianMetric I M) (p : M)
    {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I p).target)
    (hgram : ∀ i j : CoordinateIdx (𝕜 := ℝ) E, MapCInfConvergenceOnCompacts W
      (fun n => chartGramOnE (I := I) (g n) p i j) (chartGramOnE (I := I) g₀ p i j))
    (d a i j : CoordinateIdx (𝕜 := ℝ) E) :
    MapCInfConvergenceOnCompacts W (fun n => chartNabla2RicComponent (g n) p d a i j)
      (chartNabla2RicComponent g₀ p d a i j) := by
  have hN (u v w) := mapCInfConvergence_chartNablaRic_of_gram g g₀ p hW hWt hgram u v w
  have hGa (u v w) := mapCInfConvergence_chartChristoffel_of_gram g g₀ p hW hWt hgram u v w
  have hNc (h : SmoothRiemannianMetric I M) (u v w) :=
    chartNablaRicComponent_smooth h p u v w hW hWt
  have hGc (h : SmoothRiemannianMetric I M) (u v w) :=
    (chartChristoffel_contDiffOn_interior (I := I) h p u v w).mono (interior_maximal hWt hW)
  have hprod (u v w l m r) := mapCInfConvergence_scalar_binopOn hW (fun z => z.1 * z.2)
    (contDiff_fst.mul contDiff_snd) (hGa u v w) (hN l m r)
    (fun n => hGc (g n) u v w) (hGc g₀ u v w)
    (fun n => hNc (g n) l m r) (hNc g₀ l m r)
  have hs₁ := mapCInfConvergence_sumOn hW Finset.univ (fun k => hprod d a k k i j)
    (fun k n => (hGc (g n) d a k).mul (hNc (g n) k i j))
    (fun k => (hGc g₀ d a k).mul (hNc g₀ k i j))
  have hs₂ := mapCInfConvergence_sumOn hW Finset.univ (fun k => hprod d i k a k j)
    (fun k n => (hGc (g n) d i k).mul (hNc (g n) a k j))
    (fun k => (hGc g₀ d i k).mul (hNc g₀ a k j))
  have hs₃ := mapCInfConvergence_sumOn hW Finset.univ (fun k => hprod d j k a i k)
    (fun k n => (hGc (g n) d j k).mul (hNc (g n) a i k))
    (fun k => (hGc g₀ d j k).mul (hNc g₀ a i k))
  have hpart := mapCInfConvergence_fderivApplyOn hW (hN a i j)
    (fun n => hNc (g n) a i j) (hNc g₀ a i j) (chartModelBasis E d)
  have hpc (h : SmoothRiemannianMetric I M) : ContDiffOn ℝ ∞
      (fun y => partialDeriv (E := E) d (chartNablaRicComponent h p a i j) y) W :=
    ((hNc h a i j).fderiv_of_isOpen hW (m := ∞) (by simp)).clm_apply contDiffOn_const
  have hs₁c (h : SmoothRiemannianMetric I M) : ContDiffOn ℝ ∞
      (fun y => ∑ k, chartChristoffel (I := I) h p d a k y * chartNablaRicComponent h p k i j y) W :=
    ContDiffOn.sum fun k _ => (hGc h d a k).mul (hNc h k i j)
  have hs₂c (h : SmoothRiemannianMetric I M) : ContDiffOn ℝ ∞
      (fun y => ∑ k, chartChristoffel (I := I) h p d i k y * chartNablaRicComponent h p a k j y) W :=
    ContDiffOn.sum fun k _ => (hGc h d i k).mul (hNc h a k j)
  have hs₃c (h : SmoothRiemannianMetric I M) : ContDiffOn ℝ ∞
      (fun y => ∑ k, chartChristoffel (I := I) h p d j k y * chartNablaRicComponent h p a i k y) W :=
    ContDiffOn.sum fun k _ => (hGc h d j k).mul (hNc h a i k)
  have hfirst := mapCInfConvergence_scalar_binopOn hW (fun z => z.1 - z.2)
    (contDiff_fst.sub contDiff_snd) hpart hs₁
    (fun n => hpc (g n)) (hpc g₀) (fun n => hs₁c (g n)) (hs₁c g₀)
  have hsecond := mapCInfConvergence_scalar_binopOn hW (fun z => z.1 - z.2)
    (contDiff_fst.sub contDiff_snd) hfirst hs₂
    (fun n => (hpc (g n)).sub (hs₁c (g n))) ((hpc g₀).sub (hs₁c g₀))
    (fun n => hs₂c (g n)) (hs₂c g₀)
  have hresult := mapCInfConvergence_scalar_binopOn hW (fun z => z.1 - z.2)
    (contDiff_fst.sub contDiff_snd) hsecond hs₃
    (fun n => ((hpc (g n)).sub (hs₁c (g n))).sub (hs₂c (g n)))
    (((hpc g₀).sub (hs₁c g₀)).sub (hs₂c g₀))
    (fun n => hs₃c (g n)) (hs₃c g₀)
  exact hresult.congr hW
    (fun n y hy => chartNabla2RicComponent_eq (g n) p d a i j (hWt hy))
    (fun y hy => chartNabla2RicComponent_eq g₀ p d a i j (hWt hy))

end Geometry

section Flow

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor.Multilinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private theorem solution_chartNabla2Ric_tendsto_terminal
    [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular) (p : M) (d c i j : CoordinateIdx (𝕜 := ℝ) E) :
    Tendsto (fun t => chartNabla2RicComponent (S.base.metric t) p d c i j (extChartAt I p p))
      (𝓝[<] b) (𝓝 (chartNabla2RicComponent (S.base.metric b) p d c i j (extChartAt I p p))) := by
  obtain ⟨W, hW, hpW, hWt, hgram⟩ := solution_chartGram_jets_tendsto_terminal
    S hS hab hslab hreg p
  apply Filter.tendsto_of_seq_tendsto
  intro τ hτ
  have hseq (u v : CoordinateIdx (𝕜 := ℝ) E) : MapCInfConvergenceOnCompacts W
      (fun n => chartGramOnE (I := I) (S.base.metric (τ n)) p u v)
      (chartGramOnE (I := I) (S.base.metric b) p u v) := by
    intro Q _hQ hQW m
    apply mapCPConvergenceOn_of_tendstoUniformlyOn hW hQW
      (fun n => ((chartGramOnE_contDiffOn (I := I) (S.base.metric (τ n)) p u v).mono hWt).of_le
        (by exact_mod_cast le_top))
      (((chartGramOnE_contDiffOn (I := I) (S.base.metric b) p u v).mono hWt).of_le
        (by exact_mod_cast le_top))
    intro q _hq
    exact ((hgram q u v).seq_tendstoUniformlyOn τ hτ).mono hQW
  exact tendsto_of_cInf (mapCInfConvergence_chartNabla2Ric_of_gram
    (fun n => S.base.metric (τ n)) (S.base.metric b) p hW hWt hseq d c i j) hpW

theorem solution_metricNabla2Ric_continuousWithinAt_terminal
    [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular) (x : M) :
    ContinuousWithinAt (fun t => metricNabla2Ric (S.base.metric t) x) (Set.Iio b) b := by
  classical
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x
  let hframe := e.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) (chartModelBasis E)
  let β := hframe.toBasisAt hx
  let B : Module.Basis (Fin 4 → CoordinateIdx (𝕜 := ℝ) E) ℝ (Tensor0SSpace 4 I x) :=
    tensor0SBasis (I := I) β 4
  have hβ (k : CoordinateIdx (𝕜 := ℝ) E) : β k = chartBasisVecFiber (I := I) x k x := by
    rw [IsLocalFrameOn.toBasisAt_coe]
    exact localFrame_eq_chartBasisVec x hx k
  have hleft : (extChartAt I x).symm (extChartAt I x x) = x :=
    (extChartAt I x).left_inv (mem_extChartAt_source x)
  have hcoeff (σ : Fin 4 → CoordinateIdx (𝕜 := ℝ) E) :
      Tendsto (fun t => B.equivFun (metricNabla2Ric (S.base.metric t) x) σ)
        (𝓝[<] b) (𝓝 (B.equivFun (metricNabla2Ric (S.base.metric b) x) σ)) := by
    simp only [Module.Basis.equivFun_apply, B, tensor0SBasis_repr, component0S_apply]
    have hslots : (fun r => β (σ r)) =
        vec4 (chartBasisVecFiber (I := I) x (σ 0) x)
          (chartBasisVecFiber (I := I) x (σ 1) x)
          (chartBasisVecFiber (I := I) x (σ 2) x)
          (chartBasisVecFiber (I := I) x (σ 3) x) := by
      funext r
      fin_cases r <;> exact hβ _
    rw [hslots]
    have hlimit := solution_chartNabla2Ric_tendsto_terminal
      S hS hab hslab hreg x (σ 0) (σ 1) (σ 2) (σ 3)
    dsimp only [chartNabla2RicComponent] at hlimit
    rw [hleft] at hlimit
    exact hlimit
  have hsum : ContinuousWithinAt
      (fun t => (∑ σ, B.repr (metricNabla2Ric (S.base.metric t) x) σ • B σ : Tensor0SSpace 4 I x))
      (Set.Iio b) b :=
    tendsto_finsetSum Finset.univ fun σ _ => (hcoeff σ).smul tendsto_const_nhds
  simpa only [B.sum_repr] using hsum

theorem solution_metricNabla2Ric_eval_continuousWithinAt_terminal
    [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular) (x : M) (v : Fin 4 → TangentSpace I x) :
    ContinuousWithinAt (fun t => metricNabla2Ric (S.base.metric t) x v) (Set.Iio b) b := by
  let e := tensor0SSpaceContinuousLinearEquiv (I := I) (M := M) 4 x
  let w := fun r => tangentSpaceModelContinuousLinearEquiv (I := I) x (v r)
  let ev := ContinuousMultilinearMap.apply ℝ (fun _ : Fin 4 => E) ℝ w
  have h := ev.continuous.continuousAt.comp_continuousWithinAt
    (e.continuous.continuousAt.comp_continuousWithinAt
      (solution_metricNabla2Ric_continuousWithinAt_terminal S hS hab hslab hreg x))
  change ContinuousWithinAt (fun t => e (metricNabla2Ric (S.base.metric t) x) w)
    (Set.Iio b) b at h
  simpa only [e, w, tensor0SSpace_continuousLinearEquiv_apply_apply,
    ContinuousLinearEquiv.symm_apply_apply] using h

end Flow

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
