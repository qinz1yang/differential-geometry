import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalCurvatureJets
import DifferentialGeometry.Tensor.Multilinear.Bundle.Evaluation


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open CanonicalNeighborhood.FiniteHorn
open Bundle Filter Set
open scoped Manifold ContDiff _root_.Topology BigOperators
open DifferentialGeometry.Analysis DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Tensor.Multilinear
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem
open CanonicalNeighborhood

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

local instance terminalCurvatureC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
local instance terminalCurvatureC2 : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

private def chartTensorComponent {r : ℕ}
    (A : Tensor0SField (I := I) (M := M) (n := ∞) r) (p : M) :
    E → (Fin r → CoordinateIdx (𝕜 := ℝ) E) → ℝ :=
  fun y slots => A ((extChartAt I p).symm y)
    (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm y))

private def chartConstantFrame : CoordinateIdx (𝕜 := ℝ) E →
    (x : E) → TangentSpace 𝓘(ℝ, E) x :=
  fun i _ => chartModelBasis E i

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [BoundarylessManifold I M] in
private theorem chartRiemann_smooth (g : SmoothRiemannianMetric I M) (p : M)
    {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I p).target)
    (i j k l : CoordinateIdx (𝕜 := ℝ) E) :
    ContDiffOn ℝ ∞ (chartRiemannTensor (I := I) g p i j k l) W := by
  have hG (u v w : CoordinateIdx (𝕜 := ℝ) E) :=
    (chartChristoffel_contDiffOn_interior (I := I) g p u v w).mono
      (interior_maximal hWt hW)
  have hd (a u v w : CoordinateIdx (𝕜 := ℝ) E) :
      ContDiffOn ℝ ∞ (partialDeriv (E := E) a (chartChristoffel (I := I) g p u v w)) W :=
    ((hG u v w).fderiv_of_isOpen hW (m := ∞) (by simp)).clm_apply contDiffOn_const
  exact ((hd j i k l).sub (hd k i j l)).add
    (ContDiffOn.sum fun m _ => ((hG j m l).mul (hG i k m)).sub
      ((hG k m l).mul (hG i j m)))

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [BoundarylessManifold I M] in
private theorem mapCInfConvergence_chartRiemann_of_gram
    (g : ℕ → SmoothRiemannianMetric I M) (g₀ : SmoothRiemannianMetric I M) (p : M)
    {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I p).target)
    (hgram : ∀ i j : CoordinateIdx (𝕜 := ℝ) E, MapCInfConvergenceOnCompacts W
      (fun n => chartGramOnE (I := I) (g n) p i j) (chartGramOnE (I := I) g₀ p i j))
    (i j k l : CoordinateIdx (𝕜 := ℝ) E) :
    MapCInfConvergenceOnCompacts W (fun n => chartRiemannTensor (I := I) (g n) p i j k l)
      (chartRiemannTensor (I := I) g₀ p i j k l) := by
  have h := mapCInfConvergence_chartJetOperator g g₀ p hW hWt hgram
    (fun J => jetRiemann (chartModelBasis E) J i j k l)
    (fun _ hJ => contDiffAt_jetRiemann (chartModelBasis E) hJ i j k l)
  have heq (m : SmoothRiemannianMetric I M) (y : E) (hy : y ∈ W) :
      chartRiemannTensor (I := I) m p i j k l y =
        jetRiemann (chartModelBasis E) (jet2 (chartGramPi (I := I) m p) y) i j k l := by
    have hc : ContDiffOn ℝ ∞ (chartGramPi (I := I) m p) W :=
      contDiffOn_pi.mpr fun u => contDiffOn_pi.mpr fun v =>
        (chartGramOnE_contDiffOn (I := I) m p u v).mono hWt
    have hd := hc.fderiv_of_isOpen hW (m := ∞) (by simp)
    exact chartRiemann_eq_jet m p ((interior_maximal hWt hW) hy)
      ((hc.contDiffAt (hW.mem_nhds hy)).differentiableAt (by simp))
      (Filter.eventually_of_mem (hW.mem_nhds hy) fun z hz =>
        (hc.contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp))
      ((hd.contDiffAt (hW.mem_nhds hy)).differentiableAt (by simp)) i j k l
  exact h.congr hW (fun n y hy => heq (g n) y hy) (fun y hy => heq g₀ y hy)

omit [SigmaCompactSpace M] in
private theorem chartRmComponent_eq (g : SmoothRiemannianMetric I M) (p : M)
    (slots : Fin 4 → CoordinateIdx (𝕜 := ℝ) E)
    {y : E} (hy : y ∈ (extChartAt I p).target) :
    chartTensorComponent (metricRm04 (I := I) g) p y slots =
      ∑ l : CoordinateIdx (𝕜 := ℝ) E,
        chartRiemannTensor (I := I) g p (slots 2) (slots 0) (slots 1) l y *
          chartGramOnE (I := I) g p (slots 3) l y := by
  have hx : (extChartAt I p).symm y ∈ chartLeviCivitaGoodSet (I := I) p :=
    (mem_chartLeviCivitaGoodSet_iff_mem_extChartAt_source (I := I) p _).2
      ((extChartAt I p).map_target hy)
  dsimp only [chartTensorComponent]
  rw [metricRm04_apply, rm04_coord_eq g p slots hx, (extChartAt I p).right_inv hy]
  rfl

omit [SigmaCompactSpace M] in
private theorem chartRmComponent_smooth (g : SmoothRiemannianMetric I M) (p : M)
    {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I p).target)
    (slots : Fin 4 → CoordinateIdx (𝕜 := ℝ) E) :
    ContDiffOn ℝ ∞ (fun y => chartTensorComponent (metricRm04 (I := I) g) p y slots) W := by
  have hc : ContDiffOn ℝ ∞ (fun y => ∑ l : CoordinateIdx (𝕜 := ℝ) E,
      chartRiemannTensor (I := I) g p (slots 2) (slots 0) (slots 1) l y *
        chartGramOnE (I := I) g p (slots 3) l y) W :=
    ContDiffOn.sum fun l _ => (chartRiemann_smooth g p hW hWt _ _ _ l).mul
      ((chartGramOnE_contDiffOn (I := I) g p (slots 3) l).mono hWt)
  exact hc.congr fun y hy => chartRmComponent_eq g p slots (hWt hy)

omit [SigmaCompactSpace M] in
private theorem mapCInfConvergence_chartRmComponent_of_gram
    (g : ℕ → SmoothRiemannianMetric I M) (g₀ : SmoothRiemannianMetric I M) (p : M)
    {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I p).target)
    (hgram : ∀ i j : CoordinateIdx (𝕜 := ℝ) E, MapCInfConvergenceOnCompacts W
      (fun n => chartGramOnE (I := I) (g n) p i j) (chartGramOnE (I := I) g₀ p i j))
    (slots : Fin 4 → CoordinateIdx (𝕜 := ℝ) E) :
    MapCInfConvergenceOnCompacts W
      (fun n y => chartTensorComponent (metricRm04 (I := I) (g n)) p y slots)
      (fun y => chartTensorComponent (metricRm04 (I := I) g₀) p y slots) := by
  have hR (l : CoordinateIdx (𝕜 := ℝ) E) :=
    mapCInfConvergence_chartRiemann_of_gram g g₀ p hW hWt hgram (slots 2) (slots 0) (slots 1) l
  have hRc (m : SmoothRiemannianMetric I M) (l : CoordinateIdx (𝕜 := ℝ) E) :=
    chartRiemann_smooth m p hW hWt (slots 2) (slots 0) (slots 1) l
  have hGc (m : SmoothRiemannianMetric I M) (l : CoordinateIdx (𝕜 := ℝ) E) :=
    (chartGramOnE_contDiffOn (I := I) m p (slots 3) l).mono hWt
  have hp (l : CoordinateIdx (𝕜 := ℝ) E) :=
    mapCInfConvergence_scalar_binopOn hW (fun z : ℝ × ℝ => z.1 * z.2)
      (contDiff_fst.mul contDiff_snd) (hR l) (hgram (slots 3) l)
      (fun n => hRc (g n) l) (hRc g₀ l) (fun n => hGc (g n) l) (hGc g₀ l)
  have hsum := mapCInfConvergence_sumOn hW Finset.univ hp
    (fun l n => (hRc (g n) l).mul (hGc (g n) l)) (fun l => (hRc g₀ l).mul (hGc g₀ l))
  exact hsum.congr hW (fun n y hy => chartRmComponent_eq (g n) p slots (hWt hy))
    (fun y hy => chartRmComponent_eq g₀ p slots (hWt hy))

omit [SigmaCompactSpace M] [BoundarylessManifold I M] in
private theorem chartNablaRm_eq_iterCovComp {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : ℝ) (p : M)
    {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I p).target) (a : ℕ) :
    ∀ y ∈ W, ∀ slots : Fin (4 + a) → CoordinateIdx (𝕜 := ℝ) E,
      chartTensorComponent (nablaKRm04Field (I := I) S t a) p y slots =
        iterCovComp (I := 𝓘(ℝ, E)) (chartConstantFrame (E := E))
          (fun z i j k => chartChristoffel (I := I) (S.base.metric t) p i j k z)
          (chartTensorComponent (metricRm04 (I := I) (S.base.metric t)) p) a y slots := by
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
      have hreal : TotalNabla0SRealizes (I := I) (4 + a)
          (metricCov (I := I) (S.base.metric t)) (nablaKRm04Field (I := I) S t a)
          (nablaKRm04Field (I := I) S t (a + 1)) :=
        nablaKRm04Field_realizes S t a
      have hstep := totalNabla0S_chartComponent (S.base.metric t)
        (nablaKRm04Field (I := I) S t a) (nablaKRm04Field (I := I) S t (a + 1))
        hreal p hx (slots 0) (Fin.tail slots)
      have hslots : Fin.cons (chartBasisVecFiber (I := I) p (slots 0) x)
          (fun r => chartBasisVecFiber (I := I) p (Fin.tail slots r) x) =
            (fun r => chartBasisVecFiber (I := I) p (slots r) x) := by
        funext r
        exact Fin.cases rfl (fun _ => rfl) r
      rw [hright] at hstep
      have hev : (fun z => chartTensorComponent (nablaKRm04Field (I := I) S t a) p z
          (Fin.tail slots)) =ᶠ[𝓝 y]
            (fun z => iterCovComp (I := 𝓘(ℝ, E)) (chartConstantFrame (E := E))
              (fun w i j k => chartChristoffel (I := I) (S.base.metric t) p i j k w)
              (chartTensorComponent (metricRm04 (I := I) (S.base.metric t)) p) a z
              (Fin.tail slots)) :=
        Filter.eventually_of_mem (hW.mem_nhds hy) fun z hz => ih z hz (Fin.tail slots)
      calc
        _ = fderiv ℝ (fun z => chartTensorComponent (nablaKRm04Field (I := I) S t a)
              p z (Fin.tail slots)) y (chartModelBasis E (slots 0)) -
            ∑ r : Fin (4 + a), ∑ k : CoordinateIdx (𝕜 := ℝ) E,
              chartChristoffel (I := I) (S.base.metric t) p (slots 0) (Fin.tail slots r) k y *
                chartTensorComponent (nablaKRm04Field (I := I) S t a) p y
                  (Function.update (Fin.tail slots) r k) :=
          (congrArg (fun w => nablaKRm04Field (I := I) S t (a + 1) x w) hslots).symm.trans hstep
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


omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [BoundarylessManifold I M] in
theorem tensor_field_chart_components_contDiffOn {r : ℕ}
    (A : Tensor0SField (I := I) (M := M) (n := ∞) r) (p : M)
    {W : Set E} (hWt : W ⊆ (extChartAt I p).target)
    (slots : Fin r → CoordinateIdx (𝕜 := ℝ) E) :
    ContDiffOn ℝ ∞ (fun y => A ((extChartAt I p).symm y)
      (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm y))) W := by
  apply contMDiffOn_iff_contDiffOn.mp
  intro y hy
  let e := trivializationAt E (TangentSpace I : M → Type _) p
  have hx : (extChartAt I p).symm y ∈ e.baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    have hs := (extChartAt I p).map_target (hWt hy)
    rwa [extChartAt_source_eq_chartAt_source] at hs
  have ha := TensorMultilinear.contMDiffAt_section_apply (I := I)
    (T := fun x => A x) (A.contMDiff ((extChartAt I p).symm y))
    (v := fun j x => chartBasisVecFiber (I := I) p (slots j) x)
    (fun j => (chartBasisVec_contMDiffOn (I := I) p (slots j) _ hx).contMDiffAt
      (e.open_baseSet.mem_nhds hx))
  exact ha.comp_contMDiffWithinAt y ((contMDiffOn_extChartAt_symm p).mono hWt y hy)

omit [SigmaCompactSpace M] in
theorem spatial_curvature_jets_mapCInf_of_gram {D D₀ : RealTimeInterval}
    (S : ℕ → SolutionOn (I := I) (M := M) D) (S₀ : SolutionOn (I := I) (M := M) D₀)
    (τ : ℕ → ℝ) (t₀ : ℝ) (p : M)
    {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I p).target)
    (hgram : ∀ i j : CoordinateIdx (𝕜 := ℝ) E, MapCInfConvergenceOnCompacts W
      (fun n => chartGramOnE (I := I) ((S n).base.metric (τ n)) p i j)
      (chartGramOnE (I := I) (S₀.base.metric t₀) p i j)) (a : ℕ) :
    MapCInfConvergenceOnCompacts W
      (fun n y (slots : Fin (4 + a) → CoordinateIdx (𝕜 := ℝ) E) =>
        nablaKRm04Field (S n) (τ n) a ((extChartAt I p).symm y)
        (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm y)))
      (fun y (slots : Fin (4 + a) → CoordinateIdx (𝕜 := ℝ) E) =>
        nablaKRm04Field S₀ t₀ a ((extChartAt I p).symm y)
        (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm y))) := by
  let g (n : ℕ) := (S n).base.metric (τ n)
  let g₀ := S₀.base.metric t₀
  let chr (m : SmoothRiemannianMetric I M) (y : E)
      (i j k : CoordinateIdx (𝕜 := ℝ) E) := chartChristoffel (I := I) m p i j k y
  let base (m : SmoothRiemannianMetric I M) := chartTensorComponent (metricRm04 (I := I) m) p
  have hcc (m : SmoothRiemannianMetric I M) : ContDiffOn ℝ ∞ (chr m) W :=
    contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => contDiffOn_pi.mpr fun k =>
      (chartChristoffel_contDiffOn_interior (I := I) m p i j k).mono
        (interior_maximal hWt hW)
  have hbc (m : SmoothRiemannianMetric I M) : ContDiffOn ℝ ∞ (base m) W :=
    contDiffOn_pi.mpr fun slots => chartRmComponent_smooth m p hW hWt slots
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
  have hb : MapCInfConvergenceOnCompacts W (fun n => base (g n)) (base g₀) :=
    mapCInfConvergence_pi hW
      (fun slots => mapCInfConvergence_chartRmComponent_of_gram g g₀ p hW hWt hgram slots)
      (fun slots n => contDiffOn_pi.mp (hbc (g n)) slots)
      (fun slots => contDiffOn_pi.mp (hbc g₀) slots)
  have h := iter_comp_convergence hW (fun i => chartModelBasis E i)
    (fun n => chr (g n)) (chr g₀) (fun n => base (g n)) (base g₀) hc hb
    (fun n => hcc (g n)) (hcc g₀) (fun n => hbc (g n)) (hbc g₀) a
  exact h.congr hW
    (fun n y hy => funext fun slots => chartNablaRm_eq_iterCovComp (S n) (τ n) p hW hWt a y hy slots)
    (fun y hy => funext fun slots => chartNablaRm_eq_iterCovComp S₀ t₀ p hW hWt a y hy slots)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
