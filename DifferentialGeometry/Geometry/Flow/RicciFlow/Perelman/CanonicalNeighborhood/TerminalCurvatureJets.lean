import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalRicciHessian
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.MapConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Regularity

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Bundle Filter Set
open scoped Manifold ContDiff BigOperators
open DifferentialGeometry.Analysis DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Tensor.Multilinear
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem

section Geometry

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
private theorem mapCInfConv_chartRiemann_of_gram
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
private theorem mapCInfConv_chartRmComponent_of_gram
    (g : ℕ → SmoothRiemannianMetric I M) (g₀ : SmoothRiemannianMetric I M) (p : M)
    {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I p).target)
    (hgram : ∀ i j : CoordinateIdx (𝕜 := ℝ) E, MapCInfConvergenceOnCompacts W
      (fun n => chartGramOnE (I := I) (g n) p i j) (chartGramOnE (I := I) g₀ p i j))
    (slots : Fin 4 → CoordinateIdx (𝕜 := ℝ) E) :
    MapCInfConvergenceOnCompacts W
      (fun n y => chartTensorComponent (metricRm04 (I := I) (g n)) p y slots)
      (fun y => chartTensorComponent (metricRm04 (I := I) g₀) p y slots) := by
  have hR (l : CoordinateIdx (𝕜 := ℝ) E) :=
    mapCInfConv_chartRiemann_of_gram g g₀ p hW hWt hgram (slots 2) (slots 0) (slots 1) l
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

omit [SigmaCompactSpace M] in
private theorem mapCInfConv_chartNablaRm_of_gram {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (τ : ℕ → ℝ) (b : ℝ) (p : M)
    {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I p).target)
    (hgram : ∀ i j : CoordinateIdx (𝕜 := ℝ) E, MapCInfConvergenceOnCompacts W
      (fun n => chartGramOnE (I := I) (S.base.metric (τ n)) p i j)
      (chartGramOnE (I := I) (S.base.metric b) p i j)) (a : ℕ) :
    MapCInfConvergenceOnCompacts W
      (fun n => chartTensorComponent (nablaKRm04Field (I := I) S (τ n) a) p)
      (chartTensorComponent (nablaKRm04Field (I := I) S b a) p) := by
  let chr (t : ℝ) (y : E) (i j k : CoordinateIdx (𝕜 := ℝ) E) :=
    chartChristoffel (I := I) (S.base.metric t) p i j k y
  let base (t : ℝ) := chartTensorComponent (metricRm04 (I := I) (S.base.metric t)) p
  have hcc (t : ℝ) : ContDiffOn ℝ ∞ (chr t) W :=
    contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => contDiffOn_pi.mpr fun k =>
      (chartChristoffel_contDiffOn_interior (I := I) (S.base.metric t) p i j k).mono
        (interior_maximal hWt hW)
  have hbc (t : ℝ) : ContDiffOn ℝ ∞ (base t) W :=
    contDiffOn_pi.mpr fun slots => chartRmComponent_smooth (S.base.metric t) p hW hWt slots
  have hc : MapCInfConvergenceOnCompacts W (fun n => chr (τ n)) (chr b) := by
    apply mapCInfConvergence_pi hW
    · intro i
      apply mapCInfConvergence_pi hW
      · intro j
        exact mapCInfConvergence_pi hW
          (fun k => mapCInfConvergence_chartChristoffel_of_gram
            (fun n => S.base.metric (τ n))
            (S.base.metric b) p hW hWt hgram i j k)
          (fun k n => contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp (hcc (τ n)) i) j) k)
          (fun k => contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp (hcc b) i) j) k)
      · intro j n
        exact contDiffOn_pi.mp (contDiffOn_pi.mp (hcc (τ n)) i) j
      · intro j
        exact contDiffOn_pi.mp (contDiffOn_pi.mp (hcc b) i) j
    · intro i n
      exact contDiffOn_pi.mp (hcc (τ n)) i
    · intro i
      exact contDiffOn_pi.mp (hcc b) i
  have hb : MapCInfConvergenceOnCompacts W (fun n => base (τ n)) (base b) :=
    mapCInfConvergence_pi hW
      (fun slots => mapCInfConv_chartRmComponent_of_gram (fun n => S.base.metric (τ n))
        (S.base.metric b) p hW hWt hgram slots)
      (fun slots n => contDiffOn_pi.mp (hbc (τ n)) slots)
      (fun slots => contDiffOn_pi.mp (hbc b) slots)
  have h := iter_comp_convergence hW (fun i => chartModelBasis E i)
    (fun n => chr (τ n)) (chr b) (fun n => base (τ n)) (base b) hc hb
    (fun n => hcc (τ n)) (hcc b) (fun n => hbc (τ n)) (hbc b) a
  exact h.congr hW
    (fun n y hy => funext fun slots => chartNablaRm_eq_iterCovComp S (τ n) p hW hWt a y hy slots)
    (fun y hy => funext fun slots => chartNablaRm_eq_iterCovComp S b p hW hWt a y hy slots)

end Geometry

section Flow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

local instance terminalCurvatureFlowC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
local instance terminalCurvatureFlowC2 : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

private theorem solution_chartNablaRm_tendsto_terminal
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular) (p : M) (k : ℕ)
    (slots : Fin (4 + k) → CoordinateIdx (𝕜 := ℝ) E) :
    Tendsto (fun t => chartTensorComponent (nablaKRm04Field (I := I) S t k) p
      (extChartAt I p p) slots) (𝓝[<] b)
        (𝓝 (chartTensorComponent (nablaKRm04Field (I := I) S b k) p (extChartAt I p p) slots)) := by
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
  exact ((continuous_apply slots).tendsto _).comp
    (tendsto_of_cInf (mapCInfConv_chartNablaRm_of_gram S τ b p hW hWt hseq k) hpW)

theorem solution_nablaKRm04_continuousWithinAt_terminal
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular) (k : ℕ) (x : M) :
    ContinuousWithinAt (fun t => nablaKRm04Field (I := I) S t k x) (Set.Iio b) b := by
  classical
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x
  let hframe := e.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) (chartModelBasis E)
  let β := hframe.toBasisAt hx
  let B : Module.Basis (Fin (4 + k) → CoordinateIdx (𝕜 := ℝ) E) ℝ
      (Tensor0SSpace (4 + k) I x) := tensor0SBasis (I := I) β (4 + k)
  have hβ (i : CoordinateIdx (𝕜 := ℝ) E) : β i = chartBasisVecFiber (I := I) x i x := by
    rw [IsLocalFrameOn.toBasisAt_coe]
    rw [e.localFrame_apply_of_mem_baseSet (chartModelBasis E) hx]
    rw [Bundle.Trivialization.basisAt, Module.Basis.map_apply]
    change (e.linearEquivAt ℝ x hx).symm (chartModelBasis E i) =
      e.symmL ℝ x (chartModelBasis E i)
    rw [e.symmL_apply hx]
    rfl
  have hleft : (extChartAt I x).symm (extChartAt I x x) = x :=
    (extChartAt I x).left_inv (mem_extChartAt_source x)
  have hcoeff (slots : Fin (4 + k) → CoordinateIdx (𝕜 := ℝ) E) :
      Tendsto (fun t => B.equivFun (nablaKRm04Field (I := I) S t k x) slots)
        (𝓝[<] b) (𝓝 (B.equivFun (nablaKRm04Field (I := I) S b k x) slots)) := by
    simp only [Module.Basis.equivFun_apply, B, tensor0SBasis_repr, component0S_apply]
    simp only [hβ]
    have h := solution_chartNablaRm_tendsto_terminal S hS hab hslab hreg x k slots
    dsimp only [chartTensorComponent] at h
    rw [hleft] at h
    exact h
  have hsum : ContinuousWithinAt
      (fun t => (∑ slots, B.repr (nablaKRm04Field (I := I) S t k x) slots • B slots :
        Tensor0SSpace (4 + k) I x)) (Set.Iio b) b :=
    tendsto_finsetSum Finset.univ fun slots _ => (hcoeff slots).smul tendsto_const_nhds
  simpa only [B.sum_repr] using hsum

theorem solution_nablaKRm04_eval_continuousWithinAt_terminal
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular) (k : ℕ) (x : M)
    (v : Fin (4 + k) → TangentSpace I x) :
    ContinuousWithinAt (fun t => nablaKRm04Field (I := I) S t k x v) (Set.Iic b) b := by
  apply continuousWithinAt_Iio_iff_Iic.mp
  let e := tensor0SSpaceContinuousLinearEquiv (I := I) (M := M) (4 + k) x
  let w := fun r => tangentSpaceModelContinuousLinearEquiv (I := I) x (v r)
  let ev := ContinuousMultilinearMap.apply ℝ (fun _ : Fin (4 + k) => E) ℝ w
  have h := ev.continuous.continuousAt.comp_continuousWithinAt
    (e.continuous.continuousAt.comp_continuousWithinAt
      (solution_nablaKRm04_continuousWithinAt_terminal S hS hab hslab hreg k x))
  change ContinuousWithinAt (fun t => e (nablaKRm04Field (I := I) S t k x) w) (Set.Iio b) b at h
  simpa only [e, w, tensor0SSpace_continuousLinearEquiv_apply_apply,
    ContinuousLinearEquiv.symm_apply_apply] using h

theorem solution_nablaKRm04NormSqIntrinsic_continuousWithinAt_terminal
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular) (k : ℕ) (x : M) :
    ContinuousWithinAt (fun t => nablaKRm04NormSqIntrinsic (I := I) S k t x)
      (Set.Iic b) b := by
  classical
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x
  let G (t : ℝ) := chartGramMatrix (I := I) (S.base.metric t) x x
  have hGij (i j : CoordinateIdx (𝕜 := ℝ) E) :
      ContinuousWithinAt (fun t => G t i j) (Set.Iic b) b := by
    apply (continuousWithinAt_Icc_iff_Iic hab).mp
    exact ((hS.smoothMetric.coeff_cont x
      (chartBasisVecFiber (I := I) x i x) (chartBasisVecFiber (I := I) x j x)).mono
        hslab) b ⟨hab.le, le_rfl⟩
  have hG : ContinuousWithinAt G (Set.Iic b) b :=
    continuousWithinAt_pi.mpr fun i => continuousWithinAt_pi.mpr fun j => hGij i j
  have hdet : (G b).det ≠ 0 := (chartGramMatrix_det_pos (I := I) (S.base.metric b) x hx).ne'
  have hRinv : ContinuousAt (Ring.inverse : ℝ → ℝ) (G b).det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  have hGinvc : ContinuousWithinAt (fun t => (G t)⁻¹) (Set.Iic b) b :=
    Filter.Tendsto.comp (continuousAt_matrix_inv _ hRinv) hG
  have hGinvij (i j : CoordinateIdx (𝕜 := ℝ) E) :
      ContinuousWithinAt (fun t => (G t)⁻¹ i j) (Set.Iic b) b :=
    continuousWithinAt_pi.mp (continuousWithinAt_pi.mp hGinvc i) j
  let β := chartBasisFamily (I := I) x hx
  have hslots (slots : Fin (4 + k) → CoordinateIdx (𝕜 := ℝ) E) :
      ContinuousWithinAt (fun t => nablaKRm04Field (I := I) S t k x
        (fun r => β (slots r))) (Set.Iic b) b :=
    solution_nablaKRm04_eval_continuousWithinAt_terminal S hS hab hslab hreg k x _
  have heq (t : ℝ) : nablaKRm04NormSqIntrinsic (I := I) S k t x =
      ∑ slots : Fin (4 + k) → CoordinateIdx (𝕜 := ℝ) E,
        ∑ slots' : Fin (4 + k) → CoordinateIdx (𝕜 := ℝ) E,
          (∏ r : Fin (4 + k), (G t)⁻¹ (slots r) (slots' r)) *
            nablaKRm04Field (I := I) S t k x (fun r => β (slots r)) *
            nablaKRm04Field (I := I) S t k x (fun r => β (slots' r)) := by
    have hinv : MetricInverseInBasis (I := I) (S.base.metric t) x β
        (fun i j => (G t)⁻¹ i j) := by
      simpa only [G, β, chartInvGramMatrix] using
        chartInvGram_inverse (I := I) (S.base.metric t) x hx
    rw [nablaKRm04NormSqIntrinsic, normSq0S_eq_coord (I := I) (S.base.metric t) x (4 + k)
      β (fun i j => (G t)⁻¹ i j) hinv]
    rfl
  simp only [heq]
  refine tendsto_finsetSum _ fun slots _ => tendsto_finsetSum _ fun slots' _ => ?_
  have hp : ContinuousWithinAt
      (fun t => ∏ r : Fin (4 + k), (G t)⁻¹ (slots r) (slots' r)) (Set.Iic b) b :=
    tendsto_finsetProd _ fun r _ => hGinvij (slots r) (slots' r)
  exact (hp.mul (hslots slots)).mul (hslots slots')

theorem solution_nablaKRm04NormSqIntrinsic_le_terminal
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular) (k : ℕ) (x : M) {C : ℝ}
    (hbound : ∀ᶠ t in 𝓝[<] b, nablaKRm04NormSqIntrinsic (I := I) S k t x ≤ C) :
    nablaKRm04NormSqIntrinsic (I := I) S k b x ≤ C := by
  have hc := solution_nablaKRm04NormSqIntrinsic_continuousWithinAt_terminal
    S hS hab hslab hreg k x
  exact le_of_tendsto (hc.mono Set.Iio_subset_Iic_self) hbound

end Flow

section Ancient

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem terminalJetContinuous_of_ancientFlow
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) :
    TerminalJetContinuous (I := I3) F 0 := by
  intro k x v
  exact solution_nablaKRm04_eval_continuousWithinAt_terminal F.S F.isSolution
    (a := (-1 : ℝ)) (b := 0) (by norm_num) (fun _ ht => ht.2)
    (fun _ ht => ht.2) k x v

theorem isAncientKappaSolutionTerminal_of_ancient {kappa : ℝ} {D : RealTimeInterval}
    {F : PointedFlowData.{u, 0, 0} I3 D}
    (hF : IsAncientKappaSolution (I := I3) kappa F) :
    IsAncientKappaSolutionTerminal (I := I3) kappa F := by
  refine ⟨hF, ?_⟩
  intro k x v
  apply solution_nablaKRm04_eval_continuousWithinAt_terminal F.S F.isSolution
    (a := (-1 : ℝ)) (b := 0) (by norm_num) _ _ k x v
  · intro t ht
    rw [hF.carrier_eq]
    exact ht.2
  · intro t ht
    rw [hF.regular_eq]
    exact ht.2

end Ancient

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
