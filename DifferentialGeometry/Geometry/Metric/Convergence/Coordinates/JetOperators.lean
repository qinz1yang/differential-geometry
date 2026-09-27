import DifferentialGeometry.Analysis.Calculus.MapConvergence.Jet
import DifferentialGeometry.Geometry.Curvature.Coordinates.ScalarTrace
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Parameter
import DifferentialGeometry.Analysis.Calculus.MapConvergence.UniformParameter
import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.ChartBridge
import DifferentialGeometry.Geometry.Connection.ChartBridge.Curvature.DifferentiatedBasisIdentityOffCenter

set_option autoImplicit false
noncomputable section
open Bundle Filter Set
open scoped Manifold ContDiff Topology BigOperators
namespace DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Analysis DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection (chartLeviCivitaGoodSet
  chartLeviCivitaGoodSet_eq_extChartAt_source ricciTensor_chartBasisVec_alpha_eq)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance coordinateJetC1 : IsManifold I 1 M :=
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

theorem mapCInfConvergence_chartJetOperator
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
  let : NormedAddCommGroup (MatJet E (Module.finrank ℝ E)) :=
    inferInstanceAs (NormedAddCommGroup (Mat × (E →L[ℝ] Mat) × (E →L[ℝ] E →L[ℝ] Mat)))
  let : NormedSpace ℝ (MatJet E (Module.finrank ℝ E)) :=
    inferInstanceAs (NormedSpace ℝ (Mat × (E →L[ℝ] Mat) × (E →L[ℝ] E →L[ℝ] Mat)))
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

private theorem chartRicciTensor_eq_jet_of_mem
    (g : SmoothRiemannianMetric I M) (p : M) {W : Set E}
    (hW : IsOpen W) (hWt : W ⊆ (extChartAt I p).target) {y : E} (hy : y ∈ W)
    (i j : Fin (Module.finrank ℝ E)) :
    chartRicciTensor (I := I) g p i j y =
      jetRicci (chartModelBasis E) (jet2 (chartGramPi (I := I) g p) y) i j := by
  have hc := chartGramPi_smooth g p hWt
  have hd := hc.fderiv_of_isOpen hW (m := ∞) (by simp)
  have hnear : ∀ᶠ z in 𝓝 y, z ∈ W := hW.mem_nhds hy
  apply chartRicci_eq_jet g p ((interior_maximal hWt hW) hy)
    ((hc.contDiffAt (hW.mem_nhds hy)).differentiableAt (by simp))
    (hnear.mono fun z hz =>
      (hc.contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp))
    ((hd.contDiffAt (hW.mem_nhds hy)).differentiableAt (by simp)) i j

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
        jetRicci (chartModelBasis E) (jet2 (chartGramPi (I := I) h p) y) i j :=
    chartRicciTensor_eq_jet_of_mem h p hW hWt hy i j
  exact hh.congr hW (fun n y hy => heq (g n) y hy) (fun y hy => heq ginf y hy)


theorem mapCInfConvergence_chartInvGram_of_gram
    (g : ℕ → SmoothRiemannianMetric I M) (g₀ : SmoothRiemannianMetric I M)
    (p : M) {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I p).target)
    (hgram : ∀ i j : CoordinateIdx (𝕜 := ℝ) E, MapCInfConvergenceOnCompacts W
      (fun n => chartGramOnE (I := I) (g n) p i j)
      (chartGramOnE (I := I) g₀ p i j)) (i j : CoordinateIdx (𝕜 := ℝ) E) :
    MapCInfConvergenceOnCompacts W (fun n => chartInvGramOnE (I := I) (g n) p i j)
      (chartInvGramOnE (I := I) g₀ p i j) := by
  have hh := mapCInfConvergence_chartJetOperator g g₀ p hW hWt hgram
    (fun J => (Matrix.of J.1)⁻¹ i j)
    (fun _ hJ => contDiffAt_jetInvGram hJ i j)
  exact hh.congr hW (fun n y _ => (jet2_chartGram_invGram (g n) p y i j).symm)
    (fun y _ => (jet2_chartGram_invGram g₀ p y i j).symm)

theorem uniform_spatial_jets_chartJetOperator_of_gram
    {P : Type*} [TopologicalSpace P] {S : Set P} (hS : IsSeqCompact S)
    (g : ℕ → P → SmoothRiemannianMetric I M) (g₀ : P → SmoothRiemannianMetric I M)
    (p : M) {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I p).target)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E), ∀ K : Set E, IsCompact K → K ⊆ W →
      ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ S, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ r (chartGramOnE (I := I) (g n t) p i j) y -
          iteratedFDeriv ℝ r (chartGramOnE (I := I) (g₀ t) p i j) y‖ ≤ epsilon)
    (hcont : ∀ i j : Fin (Module.finrank ℝ E), ∀ r : ℕ, ContinuousOn
      (fun z : P × E => iteratedFDeriv ℝ r (chartGramOnE (I := I) (g₀ z.1) p i j) z.2)
      (S ×ˢ W))
    (A : MatJet E (Module.finrank ℝ E) → ℝ)
    (hA : ∀ J : MatJet E (Module.finrank ℝ E), (Matrix.of J.1).det ≠ 0 →
      ContDiffAt ℝ ∞ A J)
    {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W) (r : ℕ) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ S, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ r (fun z => A (jet2 (chartGramPi (I := I) (g n t) p) z)) y -
        iteratedFDeriv ℝ r (fun z => A (jet2 (chartGramPi (I := I) (g₀ t) p) z)) y‖ ≤ epsilon := by
  have hmodel (τ : ℕ → P) (hτ : ∀ n, τ n ∈ S) (t : P) (ht : t ∈ S)
      (htend : Tendsto τ atTop (𝓝 t)) (i j : Fin (Module.finrank ℝ E)) :
      MapCInfConvergenceOnCompacts W
        (fun n => chartGramOnE (I := I) (g₀ (τ n)) p i j)
        (chartGramOnE (I := I) (g₀ t) p i j) :=
    mapCInfConvergenceOnCompacts_of_continuous_spatial_jets hW
      (fun q _ => (chartGramOnE_contDiffOn (I := I) (g₀ q) p i j).mono hWt)
      (hcont i j) τ hτ ht htend
  have hsmooth (h : SmoothRiemannianMetric I M) :
      ContDiffOn ℝ ∞ (fun z => A (jet2 (chartGramPi (I := I) h p) z)) W := by
    intro y hy
    exact (hA _ (chartGram_jet2_det_ne h p (hWt hy))).comp_contDiffWithinAt y
      (chartGram_jet2_smooth h p hW hWt y hy)
  apply uniform_spatial_jets_of_sequential_convergence hW hS
    (fun n t y => A (jet2 (chartGramPi (I := I) (g n t) p) y))
    (fun t y => A (jet2 (chartGramPi (I := I) (g₀ t) p) y))
    (fun n t _ => hsmooth (g n t)) (fun t _ => hsmooth (g₀ t)) _ _ hK hKW r
  · intro θ hθ τ hτ t ht htend
    apply mapCInfConvergence_chartJetOperator (fun n => g (θ n) (τ n)) (g₀ t) p hW hWt _ A hA
    intro i j
    exact mapCInfConvergenceOnCompacts_of_uniform_spatial_jets hW
      (fun n t => chartGramOnE (I := I) (g n t) p i j)
      (fun t => chartGramOnE (I := I) (g₀ t) p i j)
      (fun n t _ => (chartGramOnE_contDiffOn (I := I) (g n t) p i j).mono hWt)
      (fun t _ => (chartGramOnE_contDiffOn (I := I) (g₀ t) p i j).mono hWt)
      (hgram i j) θ hθ τ hτ ht (hmodel τ hτ t ht htend i j)
  · intro τ hτ t ht htend
    exact mapCInfConvergence_chartJetOperator (fun n => g₀ (τ n)) (g₀ t) p hW hWt
      (hmodel τ hτ t ht htend) A hA

theorem uniform_spatial_jets_chartInvGram_of_gram
    {P : Type*} [TopologicalSpace P] {S : Set P} (hS : IsSeqCompact S)
    (g : ℕ → P → SmoothRiemannianMetric I M) (g₀ : P → SmoothRiemannianMetric I M)
    (p : M) {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I p).target)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E), ∀ K : Set E, IsCompact K → K ⊆ W →
      ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ S, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ r (chartGramOnE (I := I) (g n t) p i j) y -
          iteratedFDeriv ℝ r (chartGramOnE (I := I) (g₀ t) p i j) y‖ ≤ epsilon)
    (hcont : ∀ i j : Fin (Module.finrank ℝ E), ∀ r : ℕ, ContinuousOn
      (fun z : P × E => iteratedFDeriv ℝ r (chartGramOnE (I := I) (g₀ z.1) p i j) z.2)
      (S ×ˢ W))
    (i j : Fin (Module.finrank ℝ E))
    {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W) (r : ℕ) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ S, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ r (chartInvGramOnE (I := I) (g n t) p i j) y -
        iteratedFDeriv ℝ r (chartInvGramOnE (I := I) (g₀ t) p i j) y‖ ≤ epsilon := by
  have h := uniform_spatial_jets_chartJetOperator_of_gram hS g g₀ p hW hWt hgram hcont
    (fun J => (Matrix.of J.1)⁻¹ i j) (fun _ hJ => contDiffAt_jetInvGram hJ i j) hK hKW r
  simpa only [jet2_chartGram_invGram] using h

theorem uniform_spatial_jets_chartChristoffel_of_gram
    {P : Type*} [TopologicalSpace P] {S : Set P} (hS : IsSeqCompact S)
    (g : ℕ → P → SmoothRiemannianMetric I M) (g₀ : P → SmoothRiemannianMetric I M)
    (p : M) {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I p).target)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E), ∀ K : Set E, IsCompact K → K ⊆ W →
      ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ S, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ r (chartGramOnE (I := I) (g n t) p i j) y -
          iteratedFDeriv ℝ r (chartGramOnE (I := I) (g₀ t) p i j) y‖ ≤ epsilon)
    (hcont : ∀ i j : Fin (Module.finrank ℝ E), ∀ r : ℕ, ContinuousOn
      (fun z : P × E => iteratedFDeriv ℝ r (chartGramOnE (I := I) (g₀ z.1) p i j) z.2)
      (S ×ˢ W))
    (i j k : Fin (Module.finrank ℝ E))
    {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W) (r : ℕ) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ S, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ r (chartChristoffel (I := I) (g n t) p i j k) y -
        iteratedFDeriv ℝ r (chartChristoffel (I := I) (g₀ t) p i j k) y‖ ≤ epsilon := by
  have heq (h : SmoothRiemannianMetric I M) (y : E) (hy : y ∈ W) :
      iteratedFDeriv ℝ r (chartChristoffel (I := I) h p i j k) y =
        iteratedFDeriv ℝ r (fun z =>
          jetChristoffel (chartModelBasis E) (jet2 (chartGramPi (I := I) h p) z) i j k) y := by
    have hnear : chartChristoffel (I := I) h p i j k =ᶠ[𝓝 y]
        (fun z => jetChristoffel (chartModelBasis E) (jet2 (chartGramPi (I := I) h p) z) i j k) := by
      filter_upwards [hW.mem_nhds hy] with z hz
      have hcd := chartGramPi_smooth h p hWt
      exact chartChristoffel_eq_jet h p
        ((hcd.contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp)) i j k
    exact (hnear.iteratedFDeriv ℝ r).eq_of_nhds
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := uniform_spatial_jets_chartJetOperator_of_gram hS g g₀ p hW hWt hgram hcont
    (fun J => jetChristoffel (chartModelBasis E) J i j k)
    (fun _ hJ => contDiffAt_jetChristoffel (chartModelBasis E) hJ i j k) hK hKW r epsilon hepsilon
  refine ⟨N, fun n hn t ht y hy => ?_⟩
  rw [heq (g n t) y (hKW hy), heq (g₀ t) y (hKW hy)]
  exact hN n hn t ht y hy

theorem uniform_spatial_jets_chartRicci_of_gram
    {P : Type*} [TopologicalSpace P] {S : Set P} (hS : IsSeqCompact S)
    (g : ℕ → P → SmoothRiemannianMetric I M) (g₀ : P → SmoothRiemannianMetric I M)
    (p : M) {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I p).target)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E), ∀ K : Set E, IsCompact K → K ⊆ W →
      ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ S, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ r (chartGramOnE (I := I) (g n t) p i j) y -
          iteratedFDeriv ℝ r (chartGramOnE (I := I) (g₀ t) p i j) y‖ ≤ epsilon)
    (hcont : ∀ i j : Fin (Module.finrank ℝ E), ∀ r : ℕ, ContinuousOn
      (fun z : P × E => iteratedFDeriv ℝ r (chartGramOnE (I := I) (g₀ z.1) p i j) z.2)
      (S ×ˢ W))
    (i j : Fin (Module.finrank ℝ E))
    {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W) (r : ℕ) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ S, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ r (chartRicciTensor (I := I) (g n t) p i j) y -
        iteratedFDeriv ℝ r (chartRicciTensor (I := I) (g₀ t) p i j) y‖ ≤ epsilon := by
  have heq (h : SmoothRiemannianMetric I M) (y : E) (hy : y ∈ W) :
      iteratedFDeriv ℝ r (chartRicciTensor (I := I) h p i j) y =
        iteratedFDeriv ℝ r (fun z =>
          jetRicci (chartModelBasis E) (jet2 (chartGramPi (I := I) h p) z) i j) y := by
    have hnear : chartRicciTensor (I := I) h p i j =ᶠ[𝓝 y]
        (fun z => jetRicci (chartModelBasis E) (jet2 (chartGramPi (I := I) h p) z) i j) := by
      filter_upwards [hW.mem_nhds hy] with z hz
      exact chartRicciTensor_eq_jet_of_mem h p hW hWt hz i j
    exact (hnear.iteratedFDeriv ℝ r).eq_of_nhds
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := uniform_spatial_jets_chartJetOperator_of_gram hS g g₀ p hW hWt hgram hcont
    (fun J => jetRicci (chartModelBasis E) J i j)
    (fun _ hJ => contDiffAt_jetRicci (chartModelBasis E) hJ i j) hK hKW r epsilon hepsilon
  refine ⟨N, fun n hn t ht y hy => ?_⟩
  rw [heq (g n t) y (hKW hy), heq (g₀ t) y (hKW hy)]
  exact hN n hn t ht y hy

theorem uniform_spatial_jets_metricScalar_of_gram
    [I.Boundaryless] [T2Space M]
    {P : Type*} [TopologicalSpace P] {S : Set P} (hS : IsSeqCompact S)
    (g : ℕ → P → SmoothRiemannianMetric I M) (g₀ : P → SmoothRiemannianMetric I M)
    (p : M) {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I p).target)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E), ∀ K : Set E, IsCompact K → K ⊆ W →
      ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ S, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ r (chartGramOnE (I := I) (g n t) p i j) y -
          iteratedFDeriv ℝ r (chartGramOnE (I := I) (g₀ t) p i j) y‖ ≤ epsilon)
    (hcont : ∀ i j : Fin (Module.finrank ℝ E), ∀ r : ℕ, ContinuousOn
      (fun z : P × E => iteratedFDeriv ℝ r (chartGramOnE (I := I) (g₀ z.1) p i j) z.2)
      (S ×ˢ W))
    {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W) (r : ℕ) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ S, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ r (fun z => metricScalarAt (g n t) ((extChartAt I p).symm z)) y -
        iteratedFDeriv ℝ r (fun z => metricScalarAt (g₀ t) ((extChartAt I p).symm z)) y‖ ≤ epsilon := by
  let A : MatJet E (Module.finrank ℝ E) → ℝ := fun J =>
    ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      (Matrix.of J.1)⁻¹ i j * jetRicci (chartModelBasis E) J i j
  have hA (J : MatJet E (Module.finrank ℝ E)) (hJ : (Matrix.of J.1).det ≠ 0) :
      ContDiffAt ℝ ∞ A J := by
    exact ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun j _ =>
      (contDiffAt_jetInvGram hJ i j).mul (contDiffAt_jetRicci (chartModelBasis E) hJ i j)))
  have hscalar (h : SmoothRiemannianMetric I M) {y : E} (hy : y ∈ W) :
      metricScalarAt h ((extChartAt I p).symm y) = A (jet2 (chartGramPi (I := I) h p) y) := by
    have hx : (extChartAt I p).symm y ∈ chartLeviCivitaGoodSet (I := I) p := by
      rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) p]
      exact (extChartAt I p).map_target (hWt hy)
    have hxy := (extChartAt I p).right_inv (hWt hy)
    rw [DifferentialGeometry.PDE.RicciFlow.metricScalar_chartTrace_eq h p hx]
    dsimp only [A]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [ricciTensor_chartBasisVec_alpha_eq (I := I) h p i j hx, hxy,
      jet2_chartGram_invGram, chartRicciTensor_eq_jet_of_mem h p hW hWt hy i j]
  have heq (h : SmoothRiemannianMetric I M) (y : E) (hy : y ∈ W) :
      iteratedFDeriv ℝ r (fun z => metricScalarAt h ((extChartAt I p).symm z)) y =
        iteratedFDeriv ℝ r (fun z => A (jet2 (chartGramPi (I := I) h p) z)) y := by
    have hnear : (fun z => metricScalarAt h ((extChartAt I p).symm z)) =ᶠ[𝓝 y]
        (fun z => A (jet2 (chartGramPi (I := I) h p) z)) := by
      filter_upwards [hW.mem_nhds hy] with z hz
      exact hscalar h hz
    exact (hnear.iteratedFDeriv ℝ r).eq_of_nhds
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := uniform_spatial_jets_chartJetOperator_of_gram hS g g₀ p hW hWt hgram hcont
    A hA hK hKW r epsilon hepsilon
  refine ⟨N, fun n hn t ht y hy => ?_⟩
  rw [heq (g n t) y (hKW hy), heq (g₀ t) y (hKW hy)]
  exact hN n hn t ht y hy

end DifferentialGeometry.CheegerGromovCompactness
