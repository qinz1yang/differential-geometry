import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Data.SmoothSolutions

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open _root_.Tensor0SBundle
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold Topology ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [I.Boundaryless]

theorem forward_uniqueness_connection_speed_norm_sq_le
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) {a b : ℝ}
    (h1smooth : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) α p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (h2smooth : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₂ p.1) α p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (h1pde : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₁ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₁ t) x v w) (Ici a) t)
    (h2pde : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₂ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₂ t) x v w) (Ici a) t)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : M)
    {Λric Λ B₁ B₃ : ℝ}
    (hΛric : normSq0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x) ≤ Λric)
    (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ v : TangentSpace I x, (g₁ t).inner x v v ≤ Λ * (g₂ t).inner x v v)
    (hB₁ : normSq0S (I := I) (g₁ t) x 3
      (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.ricciSection (I := I) (metricCov (I := I) (g₂ t))
          (metricCov_smooth (I := I) (g₂ t))) x) ≤ B₁)
    (hB₃ : normSq0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₂ t) x) ≤ B₃) :
    let K : ℝ := 2 * (200 * ((Module.finrank ℝ E : ℝ) ^ 6 + 1))
    let C_A := max (8 * Λric + K * ((1 + Λ) ^ 2 * (B₁ + B₃))) K
    normSq0S (I := I) (g₁ t) x 3
      (connSpeed (I := I) g₁ g₂ (forwardUniquenessAvec (I := I) g₁ g₂) t x) ≤
      C_A * (forwardUniqueDensity (I := I) g₁ g₂ t x +
        normSq0S (I := I) (g₁ t) x 5
          (metricNabla0S (I := I) (g₁ t) (forwardUniquenessSfield (I := I) g₁ g₂ t) x)) := by
  have hab : a < b := ht.1.trans ht.2
  have hΛric0 : 0 ≤ Λric := (normSq0S_nonneg (I := I) (g₁ t) x 2 _).trans hΛric
  have hB₁0 : 0 ≤ B₁ := (normSq0S_nonneg (I := I) (g₁ t) x 3 _).trans hB₁
  have hB₃0 : 0 ≤ B₃ := (normSq0S_nonneg (I := I) (g₁ t) x 2 _).trans hB₃
  let K : ℝ := 2 * (200 * ((Module.finrank ℝ E : ℝ) ^ 6 + 1))
  let L : ℝ := (1 + Λ) ^ 2 * (B₁ + B₃)
  let C_A : ℝ := max (8 * Λric + K * L) K
  let frame := chartFrame I x
  let hframe := chartFrame_isFrame I x
  have hu : IsOpen (trivializationAt E (TangentSpace I) x).baseSet :=
    (trivializationAt E (TangentSpace I) x).open_baseSet
  have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := chartFrame_mem I x
  let Ric₁ : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 :=
    CovariantDerivative.ricciSection (I := I) (metricCov (I := I) (g₁ t))
      (metricCov_smooth (I := I) (g₁ t))
  let Ric₂ : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 :=
    CovariantDerivative.ricciSection (I := I) (metricCov (I := I) (g₂ t))
      (metricCov_smooth (I := I) (g₂ t))
  have hRic₁ : ∀ y : M, Ric₁ y = metricRicciAt (I := I) (g₁ t) y := by
    intro y
    exact CovariantDerivative.ricciSection_apply (I := I) (metricCov (I := I) (g₁ t))
      (metricCov_smooth (I := I) (g₁ t)) y
  have hRic₂ : ∀ y : M, Ric₂ y = metricRicciAt (I := I) (g₂ t) y := by
    intro y
    exact CovariantDerivative.ricciSection_apply (I := I) (metricCov (I := I) (g₂ t))
      (metricCov_smooth (I := I) (g₂ t)) y
  have hS : IsRmDiffField (I := I) (g₁ t) (g₂ t) (forwardUniquenessSfield (I := I) g₁ g₂ t) :=
    fun y => forwardUniquenessSfield_apply (I := I) g₁ g₂ t y
  have hgInv₁ : MetricInverseInBasis (I := I) (g₁ t) x (hframe.toBasisAt hx)
      (fun i j => chartFrameInv (I := I) g₁ x t x i j) := by
    have hlocal := localFrameInv_real (I := I) (D := (RealTimeInterval.univ 0))
      (solutionOfMetric (I := I) (D := (RealTimeInterval.univ 0)) g₁)
      (chartFrame I x) (chartFrame_isFrameTop I x)
    simpa [MetricInverseInBasis, InvMetricLocal, chartFrameInv, metricCompInFrame,
      frame, hframe] using hlocal t x hx
  have hgInv₂ : MetricInverseInBasis (I := I) (g₂ t) x (hframe.toBasisAt hx)
      (fun i j => chartFrameInv (I := I) g₂ x t x i j) := by
    have hlocal := localFrameInv_real (I := I) (D := (RealTimeInterval.univ 0))
      (solutionOfMetric (I := I) (D := (RealTimeInterval.univ 0)) g₂)
      (chartFrame I x) (chartFrame_isFrameTop I x)
    simpa [MetricInverseInBasis, InvMetricLocal, chartFrameInv, metricCompInFrame,
      frame, hframe] using hlocal t x hx
  have hNR₁ : ∀ d i j : Fin (Module.finrank Real E),
      chartNablaRic (I := I) g₁ x t x d i j =
        component0S (I := I) (hframe.toBasisAt hx)
          (metricNabla0S (I := I) (g₁ t) Ric₁ x)
          (fun s : Fin 3 => if s = 0 then d else if s = 1 then i else j) := by
    intro d i j
    have hreal := nablaRicReal_frame (I := I) (solutionOfMetric (I := I) (D := (RealTimeInterval.univ 0)) g₁) t
      (chartFrame I x) hframe hu hx d i j
    have hslots :
        (fun s : Fin 3 =>
          (hframe.toBasisAt hx) (if s = 0 then d else if s = 1 then i else j)) =
          DifferentialGeometry.Geometry.Curvature.vec3 (I := I)
            (chartFrame I x d x) (chartFrame I x i x) (chartFrame I x j x) := by
      funext s
      fin_cases s <;>
        simp [DifferentialGeometry.Geometry.Curvature.vec3]
    rw [component0S_apply, hslots, metricNabla0S_apply]
    convert hreal.symm using 1 <;>
      simp [chartNablaRic, Ric₁, nablaRicComp, solutionOfMetric, SolutionOn.family,
        SolutionOn.ricci, SolutionFamily.connection, SolutionFamily.ricci, metricRicci,
        metricCov]
    rfl
  have hNR₂ : ∀ d i j : Fin (Module.finrank Real E),
      chartNablaRic (I := I) g₂ x t x d i j =
        component0S (I := I) (hframe.toBasisAt hx)
          (metricNabla0S (I := I) (g₂ t) Ric₂ x)
          (fun s : Fin 3 => if s = 0 then d else if s = 1 then i else j) := by
    intro d i j
    have hreal := nablaRicReal_frame (I := I) (solutionOfMetric (I := I) (D := (RealTimeInterval.univ 0)) g₂) t
      (chartFrame I x) hframe hu hx d i j
    have hslots :
        (fun s : Fin 3 =>
          (hframe.toBasisAt hx) (if s = 0 then d else if s = 1 then i else j)) =
          DifferentialGeometry.Geometry.Curvature.vec3 (I := I)
            (chartFrame I x d x) (chartFrame I x i x) (chartFrame I x j x) := by
      funext s
      fin_cases s <;>
        simp [DifferentialGeometry.Geometry.Curvature.vec3]
    rw [component0S_apply, hslots, metricNabla0S_apply]
    convert hreal.symm using 1 <;>
      simp [chartNablaRic, Ric₂, nablaRicComp, solutionOfMetric, SolutionOn.family,
        SolutionOn.ricci, SolutionFamily.connection, SolutionFamily.ricci, metricRicci,
        metricCov]
    rfl
  have hΓcoeff := forwardUniquenessGamma (I := I) g₁ g₂ hab h1smooth h2smooth h1pde h2pde
    t ht x
  have hΓ : ∀ i j k : Fin (Module.finrank Real E),
      HasDerivAt
        (fun r : Real =>
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₁ r)) frame hframe x i j k -
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₂ r)) frame hframe x i j k)
        (christoffelEvolutionRHSInFrame (M := M) (chartFrameInv (I := I) g₁ x)
            (chartNablaRic (I := I) g₁ x) t x i j k -
          christoffelEvolutionRHSInFrame (M := M) (chartFrameInv (I := I) g₂ x)
            (chartNablaRic (I := I) g₂ x) t x i j k) t := by
    intro i j k
    have hval :
        hframe.coeff k x
            ((forwardUniquenessAvec (I := I) g₁ g₂ t x (frame j x)) (frame i x)) =
          christoffelEvolutionRHSInFrame (M := M) (chartFrameInv (I := I) g₁ x)
              (chartNablaRic (I := I) g₁ x) t x i j k -
            christoffelEvolutionRHSInFrame (M := M) (chartFrameInv (I := I) g₂ x)
              (chartNablaRic (I := I) g₂ x) t x i j k := by
      simpa [forwardUniquenessAvec, christoffelDiffSpeed, frame, hframe] using
        (coeff_bilinOfComp (I := I) (chartFrame I x) (chartFrame_isFrame I x) hx
          (fun i j k =>
            christoffelEvolutionRHSInFrame (M := M) (chartFrameInv (I := I) g₁ x)
                (chartNablaRic (I := I) g₁ x) t x i j k -
              christoffelEvolutionRHSInFrame (M := M) (chartFrameInv (I := I) g₂ x)
                (chartNablaRic (I := I) g₂ x) t x i j k) i j k)
    simpa only [frame, hframe, hval] using hΓcoeff i j k
  have hA : ∀ X Y : TangentSpace I x,
      HasDerivAt
        (fun r : Real =>
          CovariantDerivative.difference (metricCov (I := I) (g₁ r))
            (metricCov (I := I) (g₂ r)) x Y X)
        ((forwardUniquenessAvec (I := I) g₁ g₂ t x Y) X) t :=
    fun X Y => connectionDifferenceVec_hasDerivAt (I := I) g₁ g₂ frame hframe hu hx
      (forwardUniquenessAvec (I := I) g₁ g₂ t) hΓcoeff X Y
  have hmain := connectionDifferenceDot_normSq_le (I := I) g₁ g₂ (forwardUniquenessAvec (I := I) g₁ g₂ t)
    frame hframe hu hx (forwardUniquenessSfield (I := I) g₁ g₂ t) hS Ric₁ Ric₂ hRic₁ hRic₂
    (chartFrameInv (I := I) g₁ x) (chartFrameInv (I := I) g₂ x) hgInv₁ hgInv₂
    (chartNablaRic (I := I) g₁ x) (chartNablaRic (I := I) g₂ x) hNR₁ hNR₂ hΓ hA
    hΛric hΛ0 hΛ hB₁ hB₃
  have hmetric0 : 0 ≤ metricDiffSq (I := I) (g₁ t) (g₂ t) x :=
    by
      rw [metricDiffSq_def]
      exact normSq0S_nonneg (I := I) (g₁ t) x 2 _
  have hden0 : 0 ≤ forwardUniqueDensity (I := I) g₁ g₂ t x :=
    density_nonneg (I := I) g₁ g₂ t x
  have hdiss0 : 0 ≤ normSq0S (I := I) (g₁ t) x 5
      (metricNabla0S (I := I) (g₁ t) (forwardUniquenessSfield (I := I) g₁ g₂ t) x) :=
    normSq0S_nonneg (I := I) (g₁ t) x 5 _
  have hpair : metricDiffSq (I := I) (g₁ t) (g₂ t) x +
      connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x ≤
        forwardUniqueDensity (I := I) g₁ g₂ t x := by
    rw [forwardUniqueDensity]
    exact le_add_of_nonneg_right (by
      rw [rmDiffSq_def]
      exact normSq0S_nonneg (I := I) (g₁ t) x 4 _)
  have hconn : connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x ≤
      forwardUniqueDensity (I := I) g₁ g₂ t x :=
    (le_add_of_nonneg_left hmetric0).trans hpair
  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  have hL0 : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg (sq_nonneg _) (add_nonneg hB₁0 hB₃0)
  have hfirst :
      8 * Λric * connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x ≤
        8 * Λric * forwardUniqueDensity (I := I) g₁ g₂ t x :=
    mul_le_mul_of_nonneg_left hconn (mul_nonneg (by positivity) hΛric0)
  have hsecond :
      K * (nablaRmDiffSq (I := I) (g₁ t) (forwardUniquenessSfield (I := I) g₁ g₂ t) x +
          L * (metricDiffSq (I := I) (g₁ t) (g₂ t) x +
            connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x)) ≤
        K * (normSq0S (I := I) (g₁ t) x 5
            (metricNabla0S (I := I) (g₁ t) (forwardUniquenessSfield (I := I) g₁ g₂ t) x) +
          L * forwardUniqueDensity (I := I) g₁ g₂ t x) := by
    apply mul_le_mul_of_nonneg_left _ hK0
    rw [nablaRmDiffSq, nablaRmDiff]
    exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hpair hL0)
  calc
    normSq0S (I := I) (g₁ t) x 3
        (connSpeed (I := I) g₁ g₂ (forwardUniquenessAvec (I := I) g₁ g₂) t x) ≤
        8 * Λric * connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x +
          K * (nablaRmDiffSq (I := I) (g₁ t) (forwardUniquenessSfield (I := I) g₁ g₂ t) x +
            L * (metricDiffSq (I := I) (g₁ t) (g₂ t) x +
              connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x)) := by
      simpa [connSpeed, K, L, mul_assoc] using hmain
    _ ≤ 8 * Λric * forwardUniqueDensity (I := I) g₁ g₂ t x +
          K * (normSq0S (I := I) (g₁ t) x 5
              (metricNabla0S (I := I) (g₁ t) (forwardUniquenessSfield (I := I) g₁ g₂ t) x) +
            L * forwardUniqueDensity (I := I) g₁ g₂ t x) :=
      add_le_add hfirst hsecond
    _ = (8 * Λric + K * L) * forwardUniqueDensity (I := I) g₁ g₂ t x +
          K * normSq0S (I := I) (g₁ t) x 5
            (metricNabla0S (I := I) (g₁ t) (forwardUniquenessSfield (I := I) g₁ g₂ t) x) := by ring
    _ ≤ C_A * forwardUniqueDensity (I := I) g₁ g₂ t x +
          C_A * normSq0S (I := I) (g₁ t) x 5
            (metricNabla0S (I := I) (g₁ t) (forwardUniquenessSfield (I := I) g₁ g₂ t) x) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hden0)
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hdiss0)
    _ = C_A * (forwardUniqueDensity (I := I) g₁ g₂ t x +
          normSq0S (I := I) (g₁ t) x 5
            (metricNabla0S (I := I) (g₁ t) (forwardUniquenessSfield (I := I) g₁ g₂ t) x)) := by ring

omit [T2Space M] [I.Boundaryless] in
private theorem trace_time_derivative_eq {x : M} {t : Real}
    (g : Real → SmoothRiemannianMetric I M)
    (Q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hg : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g r).inner x X Y)
        ((-2 : Real) * Q (fun a : Fin 2 => if a = 0 then X else Y)) t) :
    traceTimeDerivMetric (I := I) g t x =
      (-2 : Real) * metricTracePair0SAt (I := I) (g t) Q := by
  classical
  have htrace : traceTimeDerivMetric (I := I) g t x =
      Matrix.trace ((chartGramMatrix (I := I) (g t) x x)⁻¹ *
        (Matrix.of fun i j : Fin (Module.finrank Real E) =>
          deriv (fun r : Real => chartGramMatrix (I := I) (g r) x x i j) t)) :=
    traceTimeDerivMetric_eq (I := I) g t x
  have hdG : (Matrix.of fun i j : Fin (Module.finrank Real E) =>
        deriv (fun r : Real => chartGramMatrix (I := I) (g r) x x i j) t) =
      Matrix.of fun i j : Fin (Module.finrank Real E) =>
        (-2 : Real) * Q (fun a : Fin 2 => if a = 0 then chartBasisVecFiber (I := I) x i x
          else chartBasisVecFiber (I := I) x j x) := by
    ext i j
    simpa only [Matrix.of_apply, chartGramMatrix_apply] using
      (hg (chartBasisVecFiber (I := I) x i x) (chartBasisVecFiber (I := I) x j x)).deriv
  have hInvSymm : ∀ i j : Fin (Module.finrank Real E),
      ((chartGramMatrix (I := I) (g t) x x)⁻¹) j i =
        ((chartGramMatrix (I := I) (g t) x x)⁻¹) i j := by
    intro i j
    have hHerm := (chartGramMatrix_isHermitian (I := I) (g t) x x).inv
    simpa only [star_trivial] using hHerm.apply i j
  have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have hscalar : metricTracePair0SAt (I := I) (g t) Q =
      ∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
        ((chartGramMatrix (I := I) (g t) x x)⁻¹) i j *
          Q (fun a : Fin 2 => if a = 0 then chartBasisVecFiber (I := I) x i x
            else chartBasisVecFiber (I := I) x j x) := by
    rw [metricTracePair0SAt_eq_sum_basis (I := I) (g t) (chartBasisFamily (I := I) x hx) _
      (chartInvGram_inverse (I := I) (g t) x hx) Q]
    simp only [chartBasisFamily_apply,
      DifferentialGeometry.Geometry.Operator.chartInvGramMatrix]
    rfl
  rw [htrace, hdG]
  calc
    Matrix.trace ((chartGramMatrix (I := I) (g t) x x)⁻¹ *
        (Matrix.of fun i j : Fin (Module.finrank Real E) =>
          (-2 : Real) * Q (fun a : Fin 2 => if a = 0 then chartBasisVecFiber (I := I) x i x
            else chartBasisVecFiber (I := I) x j x))) =
        Matrix.trace ((Matrix.of fun i j : Fin (Module.finrank Real E) =>
            (-2 : Real) * Q (fun a : Fin 2 => if a = 0 then chartBasisVecFiber (I := I) x i x
              else chartBasisVecFiber (I := I) x j x)) *
          (chartGramMatrix (I := I) (g t) x x)⁻¹) := by
      rw [Matrix.trace_mul_comm]
    _ = ∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
          ((-2 : Real) * Q (fun a : Fin 2 => if a = 0 then chartBasisVecFiber (I := I) x i x
            else chartBasisVecFiber (I := I) x j x)) *
            ((chartGramMatrix (I := I) (g t) x x)⁻¹) j i := by
      simp [Matrix.trace, Matrix.mul_apply]
    _ = (-2 : Real) * (∑ i : Fin (Module.finrank Real E),
          ∑ j : Fin (Module.finrank Real E),
            ((chartGramMatrix (I := I) (g t) x x)⁻¹) i j *
              Q (fun a : Fin 2 => if a = 0 then chartBasisVecFiber (I := I) x i x
                else chartBasisVecFiber (I := I) x j x)) := by
      simp_rw [hInvSymm]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    _ = (-2 : Real) * metricTracePair0SAt (I := I) (g t) Q := by rw [hscalar]

theorem forward_uniqueness_rate_rest_le
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) {a b : ℝ}
    (h1smooth : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) α p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (h2smooth : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₂ p.1) α p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (h1pde : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₁ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₁ t) x v w) (Ici a) t)
    (h2pde : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₂ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₂ t) x v w) (Ici a) t)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : M)
    {Λric Λ B₁ B₃ δ : ℝ} (hδ : 0 < δ)
    (hΛric : normSq0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x) ≤ Λric)
    (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ v : TangentSpace I x, (g₁ t).inner x v v ≤ Λ * (g₂ t).inner x v v)
    (hB₁ : normSq0S (I := I) (g₁ t) x 3
      (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.ricciSection (I := I) (metricCov (I := I) (g₂ t))
          (metricCov_smooth (I := I) (g₂ t))) x) ≤ B₁)
    (hB₃ : normSq0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₂ t) x) ≤ B₃) :
    let n : ℝ := Module.finrank ℝ E
    let K := 2 * (200 * (n ^ 6 + 1))
    let C_A := max (8 * Λric + K * ((1 + Λ) ^ 2 * (B₁ + B₃))) K
    let C_R := (4 * n ^ 6 + 6 * n ^ 8 + 8 * n ^ 10) * Real.sqrt Λric
    rateRest (I := I) g₁ g₂
      (connSpeed (I := I) g₁ g₂ (forwardUniquenessAvec (I := I) g₁ g₂)) t x ≤
      (C_R + 4 * n ^ 4 + 1 + δ * C_A + δ⁻¹ + Real.sqrt (n * Λric)) *
        forwardUniqueDensity (I := I) g₁ g₂ t x +
      δ * C_A * normSq0S (I := I) (g₁ t) x 5
        (metricNabla0S (I := I) (g₁ t) (forwardUniquenessSfield (I := I) g₁ g₂ t) x) := by
  let n : ℝ := Module.finrank ℝ E
  let K := 2 * (200 * (n ^ 6 + 1))
  let C_A := max (8 * Λric + K * ((1 + Λ) ^ 2 * (B₁ + B₃))) K
  let C_R := (4 * n ^ 6 + 6 * n ^ 8 + 8 * n ^ 10) * Real.sqrt Λric
  let C_Ric := n ^ 4
  let C_V := Real.sqrt (n * Λric)
  let Adot := connSpeed (I := I) g₁ g₂ (forwardUniquenessAvec (I := I) g₁ g₂)
  let Sfield := forwardUniquenessSfield (I := I) g₁ g₂ t
  have hpde := pde_hasDerivAt (I := I) g₁ h1pde ht x
  have hAdot : normSq0S (I := I) (g₁ t) x 3 (Adot t x) ≤
      C_A * (forwardUniqueDensity (I := I) g₁ g₂ t x +
        normSq0S (I := I) (g₁ t) x 5 (metricNabla0S (I := I) (g₁ t) Sfield x)) :=
    forward_uniqueness_connection_speed_norm_sq_le (I := I) g₁ g₂
      h1smooth h2smooth h1pde h2pde ht x hΛric hΛ0 hΛ hB₁ hB₃
  have hRic : normSq0S (I := I) (g₁ t) x 2
      (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x) ≤
      C_Ric * forwardUniqueDensity (I := I) g₁ g₂ t x := ricciSlabLe g₁ g₂ t x
  have hvol : (1 / 2 : ℝ) * traceTimeDerivMetric (I := I) g₁ t x ≤ C_V := by
    have hsq := (tracePairSq_le (I := I) (g₁ t) x (metricRicciAt (I := I) (g₁ t) x)).trans
      (mul_le_mul_of_nonneg_left hΛric (by positivity))
    have habs : |metricTracePair0SAt (I := I) (g₁ t) (metricRicciAt (I := I) (g₁ t) x)| ≤
        Real.sqrt (n * Λric) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hsq
    rw [trace_time_derivative_eq g₁ (metricRicciAt (I := I) (g₁ t) x) hpde]
    have hneg := (neg_le_abs (metricTracePair0SAt (I := I) (g₁ t)
      (metricRicciAt (I := I) (g₁ t) x))).trans habs
    dsimp only [C_V]
    linarith
  have hreact :
      movingReact0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x)
          (metricDiffAt (I := I) (g₁ t) (g₂ t) x) +
        movingReact0S (I := I) (g₁ t) x 3 (metricRicciAt (I := I) (g₁ t) x)
          (connectionDifferenceLowAt (I := I) (g₁ t) (g₂ t) x) +
        movingReact0S (I := I) (g₁ t) x 4 (metricRicciAt (I := I) (g₁ t) x)
          (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) ≤
        C_R * forwardUniqueDensity (I := I) g₁ g₂ t x := by
    have hstep (s : ℕ) (W : Tensor0SSpace s I x)
        (hW : normSq0S (I := I) (g₁ t) x s W ≤ forwardUniqueDensity (I := I) g₁ g₂ t x) :
        movingReact0S (I := I) (g₁ t) x s (metricRicciAt (I := I) (g₁ t) x) W ≤
          2 * (s : ℝ) * n ^ (2 * s + 2) * Real.sqrt Λric *
            forwardUniqueDensity (I := I) g₁ g₂ t x := by
      have hcoef : (0 : ℝ) ≤ 2 * (s : ℝ) * n ^ (2 * s + 2) := by positivity
      have hprod := mul_le_mul (Real.sqrt_le_sqrt hΛric) hW
        (normSq0S_nonneg (I := I) (g₁ t) x s W) (Real.sqrt_nonneg Λric)
      refine (le_abs_self _).trans ((movingReactAbs_le (I := I) g₁
        (metricRicciAt (I := I) (g₁ t) x) W hpde).trans ?_)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod hcoef
    have h2 := hstep 2 (metricDiffAt (I := I) (g₁ t) (g₂ t) x)
      (by simpa [metricDiffSq_def] using metricDiffSq_le_dens (I := I) g₁ g₂ t x)
    have h3 := hstep 3 (connectionDifferenceLowAt (I := I) (g₁ t) (g₂ t) x)
      (by simpa [connectionDifferenceSq_def] using connectionDifferenceSq_le_dens (I := I) g₁ g₂ t x)
    have h4 := hstep 4 (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x)
      (by simpa [rmDiffSq_def] using rmDiffSq_le_dens (I := I) g₁ g₂ t x)
    norm_num at h2 h3 h4
    dsimp only [C_R]
    linarith
  have hdens := density_nonneg (I := I) g₁ g₂ t x
  have hhdot : normSq0S (I := I) (g₁ t) x 2 (metricDiffDot (I := I) g₁ g₂ t x) =
      4 * normSq0S (I := I) (g₁ t) x 2
        (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x) := by
    rw [metricDiffDot, normSq0S_smul]
    ring
  have hh : 2 * inner0S (I := I) (g₁ t) x 2 (metricDiffDot (I := I) g₁ g₂ t x)
        (metricDiffAt (I := I) (g₁ t) (g₂ t) x) ≤
      (4 * C_Ric + 1) * forwardUniqueDensity (I := I) g₁ g₂ t x := by
    refine le_trans (two_inner0S_le (I := I) (g₁ t) x 2 _ _) ?_
    have hm : normSq0S (I := I) (g₁ t) x 2 (metricDiffAt (I := I) (g₁ t) (g₂ t) x) =
        metricDiffSq (I := I) (g₁ t) (g₂ t) x := (metricDiffSq_def (I := I) _ _ x).symm
    have hmle := metricDiffSq_le_dens (I := I) g₁ g₂ t x
    have hR := hRic
    have hexp : (4 * C_Ric + 1) * forwardUniqueDensity (I := I) g₁ g₂ t x =
        4 * (C_Ric * forwardUniqueDensity (I := I) g₁ g₂ t x) +
          forwardUniqueDensity (I := I) g₁ g₂ t x := by ring
    rw [hhdot, hm]
    linarith
  have hA : 2 * inner0S (I := I) (g₁ t) x 3 (Adot t x)
        (connectionDifferenceLowAt (I := I) (g₁ t) (g₂ t) x) ≤
      (δ * C_A + δ⁻¹) * forwardUniqueDensity (I := I) g₁ g₂ t x +
        δ * C_A * normSq0S (I := I) (g₁ t) x 5
          (metricNabla0S (I := I) (g₁ t) Sfield x) := by
    refine le_trans (two_inner0S_le_eps (I := I) (g₁ t) x 3 _ _ hδ) ?_
    have hc : normSq0S (I := I) (g₁ t) x 3 (connectionDifferenceLowAt (I := I) (g₁ t) (g₂ t) x) =
        connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x := (connectionDifferenceSq_def (I := I) _ _ x).symm
    have hcle := connectionDifferenceSq_le_dens (I := I) g₁ g₂ t x
    have hAd : δ * normSq0S (I := I) (g₁ t) x 3 (Adot t x) ≤
        δ * (C_A * (forwardUniqueDensity (I := I) g₁ g₂ t x +
          normSq0S (I := I) (g₁ t) x 5
            (metricNabla0S (I := I) (g₁ t) Sfield x))) :=
      mul_le_mul_of_nonneg_left hAdot hδ.le
    have hexp : δ * (C_A * (forwardUniqueDensity (I := I) g₁ g₂ t x +
          normSq0S (I := I) (g₁ t) x 5
            (metricNabla0S (I := I) (g₁ t) Sfield x))) =
        δ * C_A * forwardUniqueDensity (I := I) g₁ g₂ t x +
          δ * C_A * normSq0S (I := I) (g₁ t) x 5
            (metricNabla0S (I := I) (g₁ t) Sfield x) := by ring
    have hcmul : δ⁻¹ * connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x ≤
        δ⁻¹ * forwardUniqueDensity (I := I) g₁ g₂ t x :=
      mul_le_mul_of_nonneg_left hcle (by positivity)
    have hexp2 : (δ * C_A + δ⁻¹) * forwardUniqueDensity (I := I) g₁ g₂ t x =
        δ * C_A * forwardUniqueDensity (I := I) g₁ g₂ t x +
          δ⁻¹ * forwardUniqueDensity (I := I) g₁ g₂ t x := by ring
    rw [hc]
    linarith
  have hv : (1 / 2 : Real) * traceTimeDerivMetric (I := I) g₁ t x *
        forwardUniqueDensity (I := I) g₁ g₂ t x ≤
      C_V * forwardUniqueDensity (I := I) g₁ g₂ t x :=
    mul_le_mul_of_nonneg_right hvol hdens
  have hr := hreact
  have hfinal : (C_R + 4 * C_Ric + 1 + δ * C_A + δ⁻¹ + C_V) *
        forwardUniqueDensity (I := I) g₁ g₂ t x =
      C_R * forwardUniqueDensity (I := I) g₁ g₂ t x +
        ((4 * C_Ric + 1) * forwardUniqueDensity (I := I) g₁ g₂ t x +
          ((δ * C_A + δ⁻¹) * forwardUniqueDensity (I := I) g₁ g₂ t x +
            C_V * forwardUniqueDensity (I := I) g₁ g₂ t x)) := by ring
  rw [rateRest]
  linarith

end DifferentialGeometry.PDE.RicciFlow
