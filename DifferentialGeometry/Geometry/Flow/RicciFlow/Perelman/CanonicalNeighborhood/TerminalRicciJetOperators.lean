import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalChartJets
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Composition
import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.ChartBridge
import DifferentialGeometry.Geometry.Connection.ChartBridge.Curvature.DifferentiatedBasisIdentityOffCenter

set_option autoImplicit false
noncomputable section
open Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor.Coordinates
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Analysis DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Operator

section Calculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem mapCInfConvergence_jet2 {U : Set E} (hU : IsOpen U)
    {G : ℕ → E → F} {Ginf : E → F}
    (h : MapCInfConvergenceOnCompacts U G Ginf)
    (hG : ∀ k, ContDiffOn ℝ ∞ (G k) U) (hGinf : ContDiffOn ℝ ∞ Ginf U) :
    MapCInfConvergenceOnCompacts U (fun k => jet2 (G k)) (jet2 Ginf) := by
  have hd (k : ℕ) := (hG k).fderiv_of_isOpen hU (m := ∞) (by simp)
  have hdi := hGinf.fderiv_of_isOpen hU (m := ∞) (by simp)
  have hdd (k : ℕ) := (hd k).fderiv_of_isOpen hU (m := ∞) (by simp)
  have hddi := hdi.fderiv_of_isOpen hU (m := ∞) (by simp)
  have h1 := h.fderivOn hU hG hGinf
  have h2 := h1.fderivOn hU hd hdi
  exact mapCInfConvergence_prodMk hU h (mapCInfConvergence_prodMk hU h1 h2 hd hdi hdd hddi)
    hG hGinf (fun k => (hd k).prodMk (hdd k)) (hdi.prodMk hddi)

end Calculus

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local instance terminalRicciJetC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

private theorem chartGramPi_smooth (g : SmoothRiemannianMetric I M) (p : M)
    {W : Set E} (hWt : W ⊆ (extChartAt I p).target) :
    ContDiffOn ℝ ∞ (chartGramPi (I := I) g p) W := by
  exact contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j =>
    (chartGramOnE_contDiffOn (I := I) g p i j).mono hWt

private theorem chartGram_jet2_smooth (g : SmoothRiemannianMetric I M) (p : M)
    {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I p).target) :
    ContDiffOn ℝ ∞ (jet2 (chartGramPi (I := I) g p)) W := by
  have h := chartGramPi_smooth g p hWt
  have h1 := h.fderiv_of_isOpen hW (m := ∞) (by simp)
  exact h.prodMk (h1.prodMk (h1.fderiv_of_isOpen hW (m := ∞) (by simp)))

private theorem chartGram_jet2_det_ne (g : SmoothRiemannianMetric I M) (p : M)
    {y : E} (hy : y ∈ (extChartAt I p).target) :
    (Matrix.of (jet2 (chartGramPi (I := I) g p) y).1).det ≠ 0 := by
  have hbase : (extChartAt I p).symm y ∈
      (trivializationAt E (TangentSpace I) p).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    have hs := (extChartAt I p).map_target hy
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at hs
  have heq : Matrix.of (jet2 (chartGramPi (I := I) g p) y).1 =
      chartGramMatrix (I := I) g p ((extChartAt I p).symm y) := by
    ext i j
    simp only [jet2, chartGramPi, chartGramOnE_def, Matrix.of_apply]
  rw [heq]
  exact (chartGramMatrix_det_pos (I := I) g p hbase).ne'

private theorem mapCInfConvergence_chartJetOperator
    (g : ℕ → SmoothRiemannianMetric I M) (ginf : SmoothRiemannianMetric I M)
    (p : M) {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I p).target)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E), MapCInfConvergenceOnCompacts W
      (fun k => chartGramOnE (I := I) (g k) p i j)
      (chartGramOnE (I := I) ginf p i j))
    (A : MatJet E (Module.finrank ℝ E) → ℝ)
    (hA : ∀ J : MatJet E (Module.finrank ℝ E), (Matrix.of J.1).det ≠ 0 →
      ContDiffAt ℝ ∞ A J) :
    MapCInfConvergenceOnCompacts W
      (fun k y => A (jet2 (chartGramPi (I := I) (g k) p) y))
      (fun y => A (jet2 (chartGramPi (I := I) ginf p) y)) := by
  have hmatrix : MapCInfConvergenceOnCompacts W
      (fun k => chartGramPi (I := I) (g k) p) (chartGramPi (I := I) ginf p) := by
    apply mapCInfConvergence_pi hW
    · intro i
      exact mapCInfConvergence_pi hW (hgram i)
        (fun j k => (chartGramOnE_contDiffOn (I := I) (g k) p i j).mono hWt)
        (fun j => (chartGramOnE_contDiffOn (I := I) ginf p i j).mono hWt)
    · intro i k
      exact contDiffOn_pi.mpr fun j =>
        (chartGramOnE_contDiffOn (I := I) (g k) p i j).mono hWt
    · intro i
      exact contDiffOn_pi.mpr fun j =>
        (chartGramOnE_contDiffOn (I := I) ginf p i j).mono hWt
  have hjets := mapCInfConvergence_jet2 hW hmatrix
    (fun k => chartGramPi_smooth (g k) p hWt) (chartGramPi_smooth ginf p hWt)
  let V := {J : MatJet E (Module.finrank ℝ E) | (Matrix.of J.1).det ≠ 0}
  have hdet : Continuous (fun J : MatJet E (Module.finrank ℝ E) => (Matrix.of J.1).det) :=
    (contDiff_det_of_entries (fun J : MatJet E (Module.finrank ℝ E) => Matrix.of J.1)
      (fun i j => contDiff_jetVal i j)).continuous
  have hV : IsOpen V := isOpen_ne.preimage hdet
  have hAc : ContDiffOn ℝ ∞ A V := fun J hJ => (hA J hJ).contDiffWithinAt
  let Mat := Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ
  have : FiniteDimensional ℝ Mat := inferInstance
  have : FiniteDimensional ℝ (E →L[ℝ] Mat) := ContinuousLinearMap.finiteDimensional
  have : FiniteDimensional ℝ (E →L[ℝ] E →L[ℝ] Mat) := ContinuousLinearMap.finiteDimensional
  have : ProperSpace Mat := FiniteDimensional.proper ℝ Mat
  have : ProperSpace (E →L[ℝ] Mat) := FiniteDimensional.proper ℝ (E →L[ℝ] Mat)
  have : ProperSpace (E →L[ℝ] E →L[ℝ] Mat) :=
    FiniteDimensional.proper ℝ (E →L[ℝ] E →L[ℝ] Mat)
  have : ProperSpace (MatJet E (Module.finrank ℝ E)) :=
    (inferInstance : ProperSpace (Mat × (E →L[ℝ] Mat) × (E →L[ℝ] E →L[ℝ] Mat)))
  exact MapCInfConvergenceOnCompacts.comp hW hV hjets (mapCInfConvergence_const A)
    (fun k => chartGram_jet2_smooth (g k) p hW hWt)
    (chartGram_jet2_smooth ginf p hW hWt) (fun _ => hAc) hAc
    (fun _ hy => chartGram_jet2_det_ne ginf p (hWt hy))
    (fun k _ hy => chartGram_jet2_det_ne (g k) p (hWt hy))

theorem mapCInfConvergence_chartChristoffel_of_gram
    (g : ℕ → SmoothRiemannianMetric I M) (ginf : SmoothRiemannianMetric I M)
    (p : M) {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I p).target)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E), MapCInfConvergenceOnCompacts W
      (fun k => chartGramOnE (I := I) (g k) p i j)
      (chartGramOnE (I := I) ginf p i j)) (i j k : Fin (Module.finrank ℝ E)) :
    MapCInfConvergenceOnCompacts W (fun n => chartChristoffel (I := I) (g n) p i j k)
      (chartChristoffel (I := I) ginf p i j k) := by
  have hh := mapCInfConvergence_chartJetOperator g ginf p hW hWt hgram
    (fun J => jetChristoffel (chartModelBasis E) J i j k)
    (fun _ hJ => contDiffAt_jetChristoffel (chartModelBasis E) hJ i j k)
  have heq (h : SmoothRiemannianMetric I M) (y : E) (hy : y ∈ W) :=
    chartChristoffel_eq_jet h p
      (((chartGramPi_smooth h p hWt).contDiffAt (hW.mem_nhds hy)).differentiableAt (by simp))
      i j k
  exact hh.congr hW (fun n y hy => heq (g n) y hy) (fun y hy => heq ginf y hy)

theorem mapCInfConvergence_chartRicci_of_gram
    (g : ℕ → SmoothRiemannianMetric I M) (ginf : SmoothRiemannianMetric I M)
    (p : M) {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I p).target)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E), MapCInfConvergenceOnCompacts W
      (fun k => chartGramOnE (I := I) (g k) p i j)
      (chartGramOnE (I := I) ginf p i j)) (i j : Fin (Module.finrank ℝ E)) :
    MapCInfConvergenceOnCompacts W (fun n => chartRicciTensor (I := I) (g n) p i j)
      (chartRicciTensor (I := I) ginf p i j) := by
  have hh := mapCInfConvergence_chartJetOperator g ginf p hW hWt hgram
    (fun J => jetRicci (chartModelBasis E) J i j)
    (fun _ hJ => contDiffAt_jetRicci (chartModelBasis E) hJ i j)
  have heq (h : SmoothRiemannianMetric I M) (y : E) (hy : y ∈ W) :
      chartRicciTensor (I := I) h p i j y =
        jetRicci (chartModelBasis E) (jet2 (chartGramPi (I := I) h p) y) i j := by
    have hc := chartGramPi_smooth h p hWt
    have hd := hc.fderiv_of_isOpen hW (m := ∞) (by simp)
    have hnear : ∀ᶠ z in 𝓝 y, z ∈ W := hW.mem_nhds hy
    apply chartRicci_eq_jet h p ((interior_maximal hWt hW) hy)
      ((hc.contDiffAt (hW.mem_nhds hy)).differentiableAt (by simp))
      (hnear.mono fun z hz =>
        (hc.contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp))
      ((hd.contDiffAt (hW.mem_nhds hy)).differentiableAt (by simp)) i j
  exact hh.congr hW (fun n y hy => heq (g n) y hy) (fun y hy => heq ginf y hy)

end Geometry

section Flow

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem solution_chartRicci_jets_tendsto_terminal
    [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular) (p : M) :
    ∃ W : Set E, IsOpen W ∧ extChartAt I p p ∈ W ∧ W ⊆ (extChartAt I p).target ∧
      ∀ r : ℕ, ∀ i j : Fin (Module.finrank ℝ E), ∀ K : Set E, IsCompact K → K ⊆ W →
        TendstoUniformlyOn (fun t => iteratedFDeriv ℝ r
          (chartRicciTensor (I := I) (S.base.metric t) p i j))
          (iteratedFDeriv ℝ r (chartRicciTensor (I := I) (S.base.metric b) p i j))
          (𝓝[<] b) K := by
  obtain ⟨W, hW, hpW, hWt, hgram⟩ := solution_chartGram_jets_tendsto_terminal
    S hS hab hslab hreg p
  refine ⟨W, hW, hpW, hWt, ?_⟩
  intro r i j K hK hKW
  apply tendstoUniformlyOn_of_seq_tendstoUniformlyOn
  intro τ hτ
  have hseq (u v : Fin (Module.finrank ℝ E)) : MapCInfConvergenceOnCompacts W
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
  have hric := mapCInfConvergence_chartRicci_of_gram (fun n => S.base.metric (τ n))
    (S.base.metric b) p hW hWt hseq i j
  exact hric.tendstoUniformlyOn_iteratedFDeriv hW hK hKW
    (fun n => (chartRicciTensor_contDiffOn_interior (I := I) (S.base.metric (τ n)) p i j).mono
      (interior_maximal hWt hW))
    ((chartRicciTensor_contDiffOn_interior (I := I) (S.base.metric b) p i j).mono
      (interior_maximal hWt hW)) r

end Flow

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
