import DifferentialGeometry.Analysis.Calculus.Derivative.ClippedReciprocal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import DifferentialGeometry.Analysis.Calculus.Derivative.LeftEndpoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RmNormFromEigenvalues

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.CheegerGromovCompactness

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

theorem lipschitzOnWith_inv_max_scalar
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (hbound : ∀ x : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2)
    (x : P.Carrier) :
    LipschitzOnWith C (fun t => (max q (G.flow.scalar t x))⁻¹) (Ioo a s) := by
  apply DifferentialGeometry.Analysis.lipschitzOnWith_inv_max_of_quadratic_deriv_bound
    (r' := fun t => derivWithin (fun v => G.flow.scalar v x) (Iic t) t) hq ordConnected_Ioo
  · intro t ht
    exact (G.equation.scalarTime (K := Ioo a s) ht Ioo_subset_Ico_self x).continuousWithinAt
  · intro t ht _
    exact hasDerivWithinAt_left_of_mem_nhdsLE
      (G.equation.scalarTime (K := Ioo a s) ht Ioo_subset_Ico_self x)
      (mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds ht.1 ht.2))
  · exact hbound x

theorem mem_terminalRegularRegion_of_inv_max_scalar_gt
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (hbound : ∀ x : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : PhiAlmostNonnegative G.flow (Ico a s) Phi)
    {x : P.Carrier} {t : ℝ} (ht : t ∈ Ioo a s)
    (hsmall : 4 * C * (s - t) < (max q (G.flow.scalar t x))⁻¹) :
    x ∈ G.terminalRegularRegion := by
  let B := max q (G.flow.scalar t x)
  have hB : 0 < B := hq.trans_le (le_max_left _ _)
  let U : Set P.Carrier := {y | (2 * B)⁻¹ < (max q (G.flow.scalar t y))⁻¹}
  have hcont : Continuous (fun y : P.Carrier => (max q (G.flow.scalar t y))⁻¹) := by
    apply (continuous_const.max (scalarSmoothOfSolution G.flow t).continuous).inv₀
    intro y
    exact ne_of_gt (hq.trans_le (le_max_left _ _))
  have hU : IsOpen U := isOpen_lt continuous_const hcont
  have hxU : x ∈ U := by
    exact (inv_lt_inv₀ (by positivity : 0 < 2 * B) hB).mpr (by linarith)
  have hsmall' : C * (s - t) < (4 * B)⁻¹ := by
    change 4 * C * (s - t) < B⁻¹ at hsmall
    have hb := inv_pos.mpr hB
    rw [mul_inv]
    nlinarith
  have hscalar : ∀ y ∈ U, ∀ v ∈ Ico t s, G.flow.scalar v y ≤ 4 * B := by
    intro y hy v hv
    have hvl : v ∈ Ioo a s := ⟨ht.1.trans_le hv.1, hv.2⟩
    have h := (G.lipschitzOnWith_inv_max_scalar hq hbound y).dist_le_mul v hvl t ht
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hv.1)] at h
    have htime : C * (v - t) ≤ C * (s - t) :=
      mul_le_mul_of_nonneg_left (by linarith [hv.2]) C.coe_nonneg
    have hpos : (4 * B)⁻¹ < (max q (G.flow.scalar v y))⁻¹ := by
      have heq : (2 * B)⁻¹ = 2 * (4 * B)⁻¹ := by
        field_simp
        ring
      change (2 * B)⁻¹ < (max q (G.flow.scalar t y))⁻¹ at hy
      rw [heq] at hy
      have hh := neg_le_abs ((max q (G.flow.scalar v y))⁻¹ - (max q (G.flow.scalar t y))⁻¹)
      linarith
    have hmax : max q (G.flow.scalar v y) < 4 * B :=
      (inv_lt_inv₀ (by positivity) (hq.trans_le (le_max_left _ _))).mp hpos
    exact (le_max_right _ _).trans hmax.le
  obtain ⟨C3, hC3, hbridge⟩ := exists_rmNormLeOfCurvatureOperatorBounds.{u} ThreeModel
  have hnorm := hbridge P.Carrier G.flow
  refine ⟨U, hU, hxU, t, ⟨ht.1.le, ht.2⟩,
    2 * C3 * (B + Phi (4 * B) + Phi 0), by
      have := hPhi.pos (4 * B)
      have := hPhi.pos 0
      positivity, ?_⟩
  intro y hy v hv
  exact sqrt_rmNormSq_le_of_scalar_le hC3 hnorm hPhi hpinch (by simp [ThreeSpace])
    ⟨ht.1.le.trans hv.1, hv.2⟩ y hB (hscalar y hy v hv)

theorem inv_max_scalar_le_of_not_mem_terminalRegularRegion
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (hbound : ∀ x : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : PhiAlmostNonnegative G.flow (Ico a s) Phi)
    {x : P.Carrier} (hx : x ∉ G.terminalRegularRegion) {t : ℝ} (ht : t ∈ Ioo a s) :
    (max q (G.flow.scalar t x))⁻¹ ≤ 4 * C * (s - t) := by
  apply le_of_not_gt
  exact fun h => hx (G.mem_terminalRegularRegion_of_inv_max_scalar_gt hq hbound hPhi hpinch ht h)

theorem exists_uniform_scalar_lower_bound_on_nonregular_region
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (hbound : ∀ x : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : PhiAlmostNonnegative G.flow (Ico a s) Phi) (A : ℝ) :
    ∃ d ∈ Ico a s, ∀ t ∈ Ioo d s, ∀ x : P.Carrier,
      x ∉ G.terminalRegularRegion → A < G.flow.scalar t x := by
  let B := max q A
  have hB : 0 < B := hq.trans_le (le_max_left _ _)
  have hlim : Tendsto (fun t : ℝ => 4 * C * (s - t)) (𝓝[<] s) (𝓝 0) := by
    have hi : Tendsto (fun t : ℝ => t) (𝓝[<] s) (𝓝 s) := tendsto_id'.mpr nhdsWithin_le_nhds
    simpa using ((tendsto_const_nhds (x := s)).sub hi).const_mul (4 * (C : ℝ))
  have hsmall : ∀ᶠ t in 𝓝[<] s, 4 * C * (s - t) < B⁻¹ :=
    hlim.eventually (Iio_mem_nhds (inv_pos.mpr hB))
  obtain ⟨d, hd, hwindow⟩ := (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset G.lt).mp hsmall
  refine ⟨d, hd, ?_⟩
  intro t ht x hx
  have hrec := G.inv_max_scalar_le_of_not_mem_terminalRegularRegion
    hq hbound hPhi hpinch hx ⟨hd.1.trans_lt ht.1, ht.2⟩
  have hmax : B < max q (G.flow.scalar t x) :=
    (inv_lt_inv₀ (hq.trans_le (le_max_left _ _)) hB).mp (hrec.trans_lt (hwindow ht))
  rcases lt_max_iff.mp hmax with h | h
  · exact (not_lt_of_ge (le_max_left q A) h).elim
  · exact (le_max_right q A).trans_lt h

theorem exists_nhds_scalar_lower_bound_of_not_mem_terminalRegularRegion
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (hbound : ∀ x : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : PhiAlmostNonnegative G.flow (Ico a s) Phi)
    {x : P.Carrier} (hx : x ∉ G.terminalRegularRegion) (A : ℝ) :
    ∃ U : Set P.Carrier, IsOpen U ∧ x ∈ U ∧
      ∃ d ∈ Ico a s, ∀ t ∈ Ioo d s, ∀ y ∈ U, A < G.flow.scalar t y := by
  let B := max q A
  have hB : 0 < B := hq.trans_le (le_max_left _ _)
  have hlim : Tendsto (fun t : ℝ => 5 * C * (s - t)) (𝓝[<] s) (𝓝 0) := by
    have hi : Tendsto (fun t : ℝ => t) (𝓝[<] s) (𝓝 s) := tendsto_id'.mpr nhdsWithin_le_nhds
    simpa using ((tendsto_const_nhds (x := s)).sub hi).const_mul (5 * (C : ℝ))
  obtain ⟨d, hd, hwindow⟩ := (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset G.lt).mp
    (hlim.eventually (Iio_mem_nhds (inv_pos.mpr hB)))
  let t₀ := (d + s) / 2
  have ht₀ : t₀ ∈ Ioo d s := ⟨by dsimp [t₀]; linarith [hd.2], by dsimp [t₀]; linarith [hd.2]⟩
  have ht₀a : t₀ ∈ Ioo a s := ⟨hd.1.trans_lt ht₀.1, ht₀.2⟩
  let U : Set P.Carrier := {y | (max q (G.flow.scalar t₀ y))⁻¹ < B⁻¹ - C * (s - t₀)}
  have hcont : Continuous (fun y : P.Carrier => (max q (G.flow.scalar t₀ y))⁻¹) := by
    apply (continuous_const.max (scalarSmoothOfSolution G.flow t₀).continuous).inv₀
    intro y
    exact ne_of_gt (hq.trans_le (le_max_left _ _))
  have hxU : x ∈ U := by
    have hrec := G.inv_max_scalar_le_of_not_mem_terminalRegularRegion hq hbound hPhi hpinch hx ht₀a
    have hs₀ : 5 * C * (s - t₀) < B⁻¹ := hwindow ht₀
    change (max q (G.flow.scalar t₀ x))⁻¹ < B⁻¹ - C * (s - t₀)
    nlinarith
  refine ⟨U, isOpen_lt hcont continuous_const, hxU, t₀, ⟨ht₀a.1.le, ht₀a.2⟩, ?_⟩
  intro t ht y hy
  have hta : t ∈ Ioo a s := ⟨ht₀a.1.trans ht.1, ht.2⟩
  have h := (G.lipschitzOnWith_inv_max_scalar hq hbound y).dist_le_mul t hta t₀ ht₀a
  rw [Real.dist_eq, Real.dist_eq, abs_of_pos (sub_pos.mpr ht.1)] at h
  have htime : C * (t - t₀) ≤ C * (s - t₀) :=
    mul_le_mul_of_nonneg_left (by linarith [ht.2]) C.coe_nonneg
  have hrec : (max q (G.flow.scalar t y))⁻¹ < B⁻¹ := by
    change (max q (G.flow.scalar t₀ y))⁻¹ < B⁻¹ - C * (s - t₀) at hy
    have hh := le_abs_self ((max q (G.flow.scalar t y))⁻¹ - (max q (G.flow.scalar t₀ y))⁻¹)
    linarith
  have hmax : B < max q (G.flow.scalar t y) :=
    (inv_lt_inv₀ (hq.trans_le (le_max_left _ _)) hB).mp hrec
  rcases lt_max_iff.mp hmax with hq' | hR
  · exact (not_lt_of_ge (le_max_left q A) hq').elim
  · exact (le_max_right q A).trans_lt hR

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
