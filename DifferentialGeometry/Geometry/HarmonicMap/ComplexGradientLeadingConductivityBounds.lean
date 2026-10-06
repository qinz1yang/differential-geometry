import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientLeadingConductivity
import DifferentialGeometry.Analysis.Calculus.Taylor.VanishingSlope

set_option autoImplicit false

noncomputable section

open Set Metric Filter Manifold Bundle DifferentialGeometry
open DifferentialGeometry.Tensor.Coordinates
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry

/-- The real coordinate action of a two by two matrix, with the operator norm
on the complex plane rather than an entrywise matrix norm. -/
def complexPlaneMatrixOperator (A : Matrix (Fin 2) (Fin 2) ℝ) : ℂ →L[ℝ] ℂ :=
  A 0 0 • (Complex.reCLM.smulRight (1 : ℂ)) +
  A 0 1 • (Complex.imCLM.smulRight (1 : ℂ)) +
  A 1 0 • (Complex.reCLM.smulRight Complex.I) +
  A 1 1 • (Complex.imCLM.smulRight Complex.I)

private theorem complexPlaneMatrixOperator_one :
    complexPlaneMatrixOperator 1 = ContinuousLinearMap.id ℝ ℂ := by
  ext z
  apply Complex.ext <;> simp [complexPlaneMatrixOperator, Complex.real_smul]

private theorem complexPlaneMatrixOperator_zero_derivative
    {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    {A : T → Matrix (Fin 2) (Fin 2) ℝ} {a : T}
    (hA : HasFDerivAt A (0 : T →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ) a) :
    HasFDerivAt (fun t => complexPlaneMatrixOperator (A t)) (0 : T →L[ℝ] (ℂ →L[ℝ] ℂ)) a := by
  have hentry (i j : Fin 2) : HasFDerivAt (fun t => A t i j) (0 : T →L[ℝ] ℝ) a := by
    simpa using! (hasFDerivAt_pi'.mp (hasFDerivAt_pi'.mp hA i) j)
  simpa [complexPlaneMatrixOperator, Pi.add_apply] using!
    (((hentry 0 0).smul_const (Complex.reCLM.smulRight (1 : ℂ))).add
      ((hentry 0 1).smul_const (Complex.imCLM.smulRight (1 : ℂ)))).add
      ((hentry 1 0).smul_const (Complex.reCLM.smulRight Complex.I)) |>.add
      ((hentry 1 1).smul_const (Complex.imCLM.smulRight Complex.I))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Local finite-jet bounds for the literal leading graph conductivity in the
original metric. The slope derivative vanishes by the center Gram identity.
The returned norm is the real operator norm on the complex plane. -/
theorem chartLeadingPlaneProjection_conductivity_jet_bounds
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {p x : M}
    (hsrc : x ∈ (chartAt E p).source)
    {b : Fin (Module.finrank ℝ E) → ℂ} (hb : b ≠ 0)
    (hnull : (∑ i, ∑ j, (chartGramMatrix g p x i j : ℂ) * b i * b j) = 0)
    {N : E} (hN : chartLeadingPlaneProjection g p x b N = 0)
    (hunit : chartGramBilin g p x N N = 1)
    (L : ℂ →L[ℝ] E)
    (hL : ∀ w, L w = (chartModelBasis E).equivFunL.symm
      (fun i => (2 : ℝ) * (w * b i).re)) (c : ℂ) :
    let Y : (ℂ × ℝ) × (ℂ →L[ℝ] ℝ) → E := fun q =>
      extChartAt 𝓘(ℝ, E) p x + L (q.1.1 - c) + q.1.2 • N
    let G : ((ℂ × ℝ) × (ℂ →L[ℝ] ℝ)) → Matrix (Fin 2) (Fin 2) ℝ := fun q i j =>
      chartGramBilin g p ((extChartAt 𝓘(ℝ, E) p).symm (Y q))
        (L (![1, Complex.I] i) + q.2 (![1, Complex.I] i) • N)
        (L (![1, Complex.I] j) + q.2 (![1, Complex.I] j) • N)
    let A := fun q => complexPlaneMatrixOperator
      (Analysis.planarConductivity (G q 0 0) (G q 1 1) (G q 0 1))
    ContDiffAt ℝ 2 A ((c, 0), 0) ∧ A ((c, 0), 0) = ContinuousLinearMap.id ℝ ℂ ∧
      ∃ r C : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 < C ∧
      (∀ q ∈ ball ((c, (0 : ℝ)), (0 : ℂ →L[ℝ] ℝ)) r,
        ‖A q - ContinuousLinearMap.id ℝ ℂ‖ ≤ C * (‖q.1 - (c, 0)‖ + ‖q.2‖ ^ 2) ∧
        ‖fderiv ℝ A q‖ ≤ C ∧
        ‖(fderiv ℝ A q).comp (ContinuousLinearMap.inr ℝ (ℂ × ℝ) (ℂ →L[ℝ] ℝ))‖ ≤
          C * ‖q - ((c, 0), 0)‖) ∧
      ∀ q ∈ ball ((c, (0 : ℝ)), (0 : ℂ →L[ℝ] ℝ)) r,
        Y q ∈ (extChartAt 𝓘(ℝ, E) p).target ∧
        0 < G q 0 0 * G q 1 1 - G q 0 1 ^ 2 := by
  classical
  let Y : (ℂ × ℝ) × (ℂ →L[ℝ] ℝ) → E := fun q =>
    extChartAt 𝓘(ℝ, E) p x + L (q.1.1 - c) + q.1.2 • N
  let V : ((ℂ × ℝ) × (ℂ →L[ℝ] ℝ)) → Fin 2 → E := fun q i =>
    L (![1, Complex.I] i) + q.2 (![1, Complex.I] i) • N
  let G : ((ℂ × ℝ) × (ℂ →L[ℝ] ℝ)) → Matrix (Fin 2) (Fin 2) ℝ := fun q i j =>
    chartGramBilin g p ((extChartAt 𝓘(ℝ, E) p).symm (Y q)) (V q i) (V q j)
  let A := fun q => complexPlaneMatrixOperator
    (Analysis.planarConductivity (G q 0 0) (G q 1 1) (G q 0 1))
  change ContDiffAt ℝ 2 A ((c, 0), 0) ∧ A ((c, 0), 0) = ContinuousLinearMap.id ℝ ℂ ∧ _
  have hchart : extChartAt 𝓘(ℝ, E) p x ∈ (extChartAt 𝓘(ℝ, E) p).target :=
    (extChartAt 𝓘(ℝ, E) p).map_source (by simpa only [extChartAt_source] using hsrc)
  have hinverse : (extChartAt 𝓘(ℝ, E) p).symm (extChartAt 𝓘(ℝ, E) p x) = x :=
    (extChartAt 𝓘(ℝ, E) p).left_inv (by simpa only [extChartAt_source] using hsrc)
  have hYslice (ell : ℂ →L[ℝ] ℝ) :
      Y ((c, 0), ell) = extChartAt 𝓘(ℝ, E) p x := by
    simp only [Y, sub_self, map_zero, zero_smul, add_zero]
  have hGslice (ell : ℂ →L[ℝ] ℝ) (i j : Fin 2) :
      G ((c, 0), ell) i j = chartGramBilin g p x
        (L (![1, Complex.I] i) + ell (![1, Complex.I] i) • N)
        (L (![1, Complex.I] j) + ell (![1, Complex.I] j) • N) := by
    change chartGramBilin g p ((extChartAt 𝓘(ℝ, E) p).symm (Y ((c, 0), ell)))
      (L (![1, Complex.I] i) + ell (![1, Complex.I] i) • N)
      (L (![1, Complex.I] j) + ell (![1, Complex.I] j) • N) = _
    rw [hYslice, hinverse]
  have hY : ContDiff ℝ ∞ Y := by dsimp [Y]; fun_prop
  have hV (i : Fin 2) : ContDiff ℝ ∞ (fun q => V q i) := by dsimp [V]; fun_prop
  let D := Y ⁻¹' (extChartAt 𝓘(ℝ, E) p).target
  have hD : IsOpen D := (isOpen_extChartAt_target p).preimage hY.continuous
  have hbaseD : ((c, (0 : ℝ)), (0 : ℂ →L[ℝ] ℝ)) ∈ D := by simpa [D, Y] using hchart
  have hG (i j : Fin 2) : ContDiffOn ℝ ∞ (fun q => G q i j) D := by
    have hcoeff (k l : Fin (Module.finrank ℝ E)) :
        ContDiffOn ℝ ∞ (fun q => chartGramMatrix g p
          ((extChartAt 𝓘(ℝ, E) p).symm (Y q)) k l) D :=
      (Operator.chartGramOnE_contDiffOn g p k l).comp hY.contDiffOn (fun _ h => h)
    have hcoord (k : Fin (Module.finrank ℝ E)) (i : Fin 2) :
        ContDiffOn ℝ ∞ (fun q => (chartModelBasis E).equivFun (V q i) k) D :=
      (chartCoordCLM E k).contDiff.comp_contDiffOn (hV i).contDiffOn
    have hsum := ContDiffOn.sum (fun k (_ : k ∈ Finset.univ) =>
      ContDiffOn.sum (fun l (_ : l ∈ Finset.univ) =>
        ((hcoeff k l).mul (hcoord k i)).mul (hcoord l j)))
    simpa only [G, chartGramBilin_apply] using hsum
  obtain ⟨κ, hκ, hgram⟩ :=
    chartLeadingPlaneProjection_lift_normal_gram g hsrc hb hnull hN hunit
  have hbaseG (i j : Fin 2) : G ((c, 0), 0) i j =
      κ * ((![1, Complex.I] i).re * (![1, Complex.I] j).re +
        (![1, Complex.I] i).im * (![1, Complex.I] j).im) := by
    simpa only [hGslice, zero_apply, zero_smul, add_zero, hL, mul_zero] using
      hgram (![1, Complex.I] i) (![1, Complex.I] j) 0 0
  have hdet0 : 0 < G ((c, 0), 0) 0 0 * G ((c, 0), 0) 1 1 - G ((c, 0), 0) 0 1 ^ 2 := by
    simpa [hbaseG] using mul_pos hκ hκ
  let U := D ∩ {q | 0 < G q 0 0 * G q 1 1 - G q 0 1 ^ 2}
  have hUnear : U ∈ 𝓝 ((c, (0 : ℝ)), (0 : ℂ →L[ℝ] ℝ)) := by
    refine inter_mem (hD.mem_nhds hbaseD) ?_
    exact ((((hG 0 0).contDiffAt (hD.mem_nhds hbaseD)).continuousAt.mul
      ((hG 1 1).contDiffAt (hD.mem_nhds hbaseD)).continuousAt).sub
      (((hG 0 1).contDiffAt (hD.mem_nhds hbaseD)).continuousAt.pow 2)).eventually
      (lt_mem_nhds hdet0)
  have hentry (i j : Fin 2) : ContDiffAt ℝ 2
      (fun q => Analysis.planarConductivity (G q 0 0) (G q 1 1) (G q 0 1) i j) ((c, 0), 0) :=
    ((Analysis.contDiffOn_planarConductivity ((hG 0 0).mono inter_subset_left)
      ((hG 1 1).mono inter_subset_left) ((hG 0 1).mono inter_subset_left)
      (fun _ h => h.2) i j).contDiffAt hUnear).of_le (by simp)
  have hA : ContDiffAt ℝ 2 A ((c, 0), 0) := by
    exact (((hentry 0 0).smul contDiffAt_const |>.add
      ((hentry 0 1).smul contDiffAt_const)).add
      ((hentry 1 0).smul contDiffAt_const)).add ((hentry 1 1).smul contDiffAt_const)
  let SlopeA := fun ell : ℂ →L[ℝ] ℝ =>
    Analysis.planarConductivity (G ((c, 0), ell) 0 0)
      (G ((c, 0), ell) 1 1) (G ((c, 0), ell) 0 1)
  have hcenter : SlopeA 0 = 1 ∧ HasFDerivAt SlopeA
      (0 : (ℂ →L[ℝ] ℝ) →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ) (0 : ℂ →L[ℝ] ℝ) := by
    simpa only [SlopeA, hGslice, hL] using!
      chartLeadingPlaneProjection_center_conductivity g hsrc hb hnull hN hunit
  have hA0 : A ((c, 0), 0) = ContinuousLinearMap.id ℝ ℂ := by
    change complexPlaneMatrixOperator (SlopeA 0) = _
    rw [hcenter.1, complexPlaneMatrixOperator_one]
  have hslope : HasFDerivAt (fun ell : ℂ →L[ℝ] ℝ => A ((c, 0), ell))
      (0 : (ℂ →L[ℝ] ℝ) →L[ℝ] (ℂ →L[ℝ] ℂ)) (0 : ℂ →L[ℝ] ℝ) :=
    complexPlaneMatrixOperator_zero_derivative hcenter.2
  have hin : HasFDerivAt (fun ell : ℂ →L[ℝ] ℝ => ((c, (0 : ℝ)), ell))
      (ContinuousLinearMap.inr ℝ (ℂ × ℝ) (ℂ →L[ℝ] ℝ)) (0 : ℂ →L[ℝ] ℝ) :=
    (hasFDerivAt_const (c, (0 : ℝ)) (0 : ℂ →L[ℝ] ℝ)).prodMk (hasFDerivAt_id _)
  have hzero : (fderiv ℝ A ((c, 0), 0)).comp
      (ContinuousLinearMap.inr ℝ (ℂ × ℝ) (ℂ →L[ℝ] ℝ)) = 0 :=
    (((hA.differentiableAt (by norm_num)).hasFDerivAt.comp _ hin).unique hslope)
  obtain ⟨r, C, hr, hr1, hC, hbound⟩ :=
    Analysis.exists_local_bounds_of_vanishing_slope_derivative hA hzero
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hUnear
  let s : ℝ := min r δ
  have hs : 0 < s := lt_min hr hδ
  refine ⟨hA, hA0, s, C, hs, (min_le_left r δ).trans hr1, hC, ?_, ?_⟩
  · intro q hq
    simpa only [hA0] using hbound q (ball_subset_ball (min_le_left r δ) hq)
  · intro q hq
    have hqU := hδsub (ball_subset_ball (min_le_right r δ) hq)
    exact ⟨hqU.1, hqU.2⟩

end DifferentialGeometry.Geometry
