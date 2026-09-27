import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessParabolicTransport

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff

theorem recenterScale_bounds (A : ℝ) :
    A < max (A + 1) 3 ∧ 2 < max (A + 1) 3 := by
  constructor
  · linarith [le_max_left (A + 1) (3 : ℝ)]
  · linarith [le_max_right (A + 1) (3 : ℝ)]

theorem parabolicTime_mem_recenteredWindow {Hd s B u : ℝ} (hB : 0 < B)
    (hs : s ≤ 0) (hu : u ∈ Set.Icc (-(B * (Hd + s))) 0) :
    parabolicTime s B u ∈ Set.Icc (-Hd) 0 := by
  have hlo : -(Hd + s) ≤ u / B := by
    apply (le_div_iff₀ hB).2
    nlinarith [hu.1]
  have hhi : u / B ≤ 0 := div_nonpos_of_nonpos_of_nonneg hu.2 hB.le
  change -Hd ≤ s + u / B ∧ s + u / B ≤ 0
  constructor <;> linarith

theorem recenteredDepth_ge_half {Hd s B : ℝ} (hB : 0 ≤ B)
    (hs : -(Hd / 2) ≤ s) :
    B * Hd / 2 ≤ B * (Hd + s) := by
  nlinarith [mul_le_mul_of_nonneg_left hs hB]

theorem tendsto_recenteredDepth {iota : Type*} {l : Filter iota}
    {Hd s : iota → ℝ} {B : ℝ} (hB : 0 < B)
    (hHd : Filter.Tendsto Hd l Filter.atTop)
    (hs : ∀ᶠ i in l, -(Hd i / 2) ≤ s i) :
    Filter.Tendsto (fun i => B * (Hd i + s i)) l Filter.atTop := by
  refine Filter.tendsto_atTop.2 fun b => ?_
  filter_upwards [hHd.eventually_ge_atTop (2 * b / B), hs] with i hi hsi
  have hmul := (div_le_iff₀ hB).1 hi
  have hhalf := recenteredDepth_ge_half hB.le hsi
  nlinarith

theorem rescalePinchingFunction_rescale (B Q : ℝ) (Phi : ℝ → ℝ) :
    rescalePinchingFunction B (rescalePinchingFunction Q Phi) =
      rescalePinchingFunction (B * Q) Phi := by
  funext u
  simp only [rescalePinchingFunction, mul_inv]
  have harg : Q * (B * u) = B * Q * u := by ring
  rw [harg]
  ring

theorem recentered_noncollapse_scale {B : ℝ} (hB : 0 ≤ B) (Q sigma : ℝ) :
    Real.sqrt B * (Real.sqrt Q * sigma) = Real.sqrt (B * Q) * sigma := by
  rw [Real.sqrt_mul hB]
  ring

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 1 M] {D : RealTimeInterval}

theorem isGoodPoint_recentered_of_two_le
    (S : SolutionOn (I := I) (M := M) D)
    {Hd s B eps kappa : ℝ} (hB : 1 ≤ B) (hs : s ≤ 0)
    (hts : s ∈ D.carrier)
    (hgood : ∀ (x : M) (t : ℝ), t ∈ Set.Icc (-Hd) 0 →
      2 ≤ S.scalar t x → IsGoodPoint.{u, uE, uH} (I := I) eps kappa S x t)
    {x : M} {u : ℝ} (hu : u ∈ Set.Icc (-(B * (Hd + s))) 0)
    (hR : 2 ≤ (parabolicSolution S s B (lt_of_lt_of_le zero_lt_one hB) hts).scalar u x) :
    IsGoodPoint.{u, uE, uH} (I := I) eps kappa
      (parabolicSolution S s B (lt_of_lt_of_le zero_lt_one hB) hts) x u := by
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  apply (isGoodPoint_paraSolution_iff S s B hBpos hts u x eps kappa).2
  apply hgood x (parabolicTime s B u) (parabolicTime_mem_recenteredWindow hBpos hs hu)
  have hdiv : 2 ≤ S.scalar (parabolicTime s B u) x / B := by
    simpa only [parabolicSolution_scalar, div_eq_mul_inv, mul_comm] using hR
  have hmul := (le_div_iff₀ hBpos).1 hdiv
  linarith

theorem recenteredSource_inputs [T2Space M] [SigmaCompactSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    {Hd s B eps kappa rho : ℝ} (hB : 2 < B)
    (hs : s ∈ Set.Icc (-Hd) 0)
    (hwindow : Set.Icc (-Hd) 0 ⊆ D.carrier)
    {Phi : ℝ → ℝ}
    (hpinch : PhiAlmostNonnegative (I := I) (M := M) S (Set.Icc (-Hd) 0) Phi)
    (hnc : SpatiallyKappaNoncollapsedBelowScale (I := I) S kappa rho)
    (hgood : ∀ (x : M) (t : ℝ), t ∈ Set.Icc (-Hd) 0 →
      2 ≤ S.scalar t x → IsGoodPoint.{u, uE, uH} (I := I) eps kappa S x t)
    {w : M} (hw : S.scalar s w = B) :
    let hBpos : 0 < B := lt_trans (by norm_num : (0 : ℝ) < 2) hB
    let SR := parabolicSolution S s B hBpos (hwindow hs)
    SR.scalar 0 w = 1 ∧
      IsGoodPoint.{u, uE, uH} (I := I) eps kappa SR w 0 ∧
      Set.Icc (-(B * (Hd + s))) 0 ⊆ (parabolicInterval D s B (hwindow hs)).carrier ∧
      (∀ (x : M) (u : ℝ), u ∈ Set.Icc (-(B * (Hd + s))) 0 →
        2 ≤ SR.scalar u x → IsGoodPoint.{u, uE, uH} (I := I) eps kappa SR x u) ∧
      PhiAlmostNonnegative (I := I) (M := M) SR (Set.Icc (-(B * (Hd + s))) 0)
        (rescalePinchingFunction B Phi) ∧
      SpatiallyKappaNoncollapsedBelowScale (I := I) SR kappa (Real.sqrt B * rho) := by
  dsimp only
  have hBpos : 0 < B := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [parabolicSolution_scalar, parabolicTime_zero, hw]
    exact inv_mul_cancel₀ hBpos.ne'
  · apply (isGoodPoint_paraSolution_iff S s B hBpos (hwindow hs) 0 w eps kappa).2
    rw [parabolicTime_zero]
    exact hgood w s hs (by rw [hw]; exact hB.le)
  · intro u hu
    exact hwindow (parabolicTime_mem_recenteredWindow hBpos hs.2 hu)
  · intro x u hu hR
    exact isGoodPoint_recentered_of_two_le S (by linarith) hs.2 (hwindow hs)
      hgood hu hR
  · have htransport := phiAlmostNonnegative_paraSolution S hBpos (hwindow hs) hpinch
    intro u hu x
    exact htransport u (parabolicTime_mem_recenteredWindow hBpos hs.2 hu) x
  · exact parabolic_spatial_noncollapse S s B hBpos (hwindow hs) kappa rho hnc

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

end
