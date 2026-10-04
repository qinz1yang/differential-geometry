import DifferentialGeometry.Geometry.Collapse.RescaledLimits.LimitVolume
import DifferentialGeometry.Geometry.Collapse.InducedVolumeComparison

/-!
# LC07: vanishing normalized volume gives a low-dimensional limit

Blueprint 207A, LC07 (`prop:collapse-low-dimensional-limit`, A:20198). Under the LC05
hypotheses, if moreover `w i > 0`, `w i → 0` and the volume level `w i` is attained at a radius
`r i ≤ 2 ρ i` (`Vol B(p i, r i) = w i r i³`), then a subsequence of `(X i, ρ i⁻² g i, p i)`
converges to a complete proper geodesic space with nonnegative four-point comparison and
Hausdorff dimension at most two.

The blueprint asks for the FIRST volume scale `r_{p_i}(w_i)`; any attained radius suffices (LC03
uses nothing else), so the statement below is stronger.

* `connectedSpace_of_aligned_metric`: a nonempty manifold whose metric realizes `g` is connected.
* `ballVolume_rescaled_two_le_of_buffer`: LC03 in the aligned convention, from the LC05 buffer.
* `exists_rescaled_pointed_limit_dimH_le_two`: LC07.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- `∫₀¹ sinh² ≥ 0`, the sign of the constant `C_H = 3 ∫₀¹ sinh²` of LC03. -/
theorem integral_sinh_sq_nonneg : 0 ≤ ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2 :=
  intervalIntegral.integral_nonneg zero_le_one fun t _ => sq_nonneg (Real.sinh t)

section Single

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [SigmaCompactSpace M] in
/-- A nonempty manifold whose metric realizes the length distance of `g` is path connected, hence
connected: finite distances force the existence of paths. -/
theorem connectedSpace_of_aligned_metric (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) (p : M) :
    ConnectedSpace M := by
  have : PathConnectedSpace M := by
    refine ⟨⟨p⟩, fun x y => ?_⟩
    by_contra h
    have hp : IsEmpty (Path x y) := not_nonempty_iff.mp h
    have hinf : riemannianEDistOf g x y = ⊤ := by
      rw [edistOf_iInf]
      exact le_antisymm le_top (le_iInf fun γ => (hp.false γ).elim)
    rw [hmetric] at hinf
    exact ENNReal.ofReal_ne_top hinf
  infer_instance

/-- LC03 in the aligned convention: if the level `w` is attained at a radius `r ≤ 2ρ` and the
LC05 buffer `sec ≥ -(Lρ)⁻²` on `B(p, Lρ)` holds with `L ≥ 2`, then the radius-`2` ball of
`ρ⁻² g` has volume at most `8 C_H w`, `C_H = 3 ∫₀¹ sinh²`. -/
theorem ballVolume_rescaled_two_le_of_buffer [CompleteSpace M] (hdim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) (p : M)
    {w r ρ L : ℝ} (hw : 0 < w) (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r ≤ 2 * ρ) (hL : 2 ≤ L)
    (hvol : ballVolume g p r = ENNReal.ofReal (w * r ^ 3))
    (hsec : ∀ y ∈ riemannianBallOf g p (L * ρ), SectionalBoundedBelowAt g y (-((L * ρ) ^ 2)⁻¹)) :
    ballVolume (scaleMetric (ρ⁻¹ ^ 2) (pow_pos (inv_pos.mpr hρ) 2) g) p 2 ≤
      ENNReal.ofReal (8 * (3 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) * w) := by
  have : ConnectedSpace M := connectedSpace_of_aligned_metric g hmetric p
  have : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  have hg : RiemannianMetricComplete (I := I) g :=
    (riemannianMetricComplete_iff_completeSpace hmetric).mpr inferInstance
  have h2L : 2 * ρ ≤ L * ρ := mul_le_mul_of_nonneg_right hL hρ.le
  have hsec2 : ∀ y ∈ riemannianBallOf g p (2 * ρ),
      SectionalBoundedBelowAt g y (-((2 * ρ) ^ 2)⁻¹) := by
    intro y hy
    have hy' : y ∈ riemannianBallOf g p (L * ρ) :=
      lt_of_lt_of_le hy (ENNReal.ofReal_le_ofReal h2L)
    refine (hsec y hy').mono (neg_le_neg ?_)
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h2L 2)
  have hupper := ballVolume_rescaled_two_le_of_attained g hg hdim p hw hr hρ hrρ hvol hsec2
  have hscale : scaleMetric (ρ ^ 2)⁻¹ (inv_pos.mpr (sq_pos_of_pos hρ)) g =
      scaleMetric (ρ⁻¹ ^ 2) (pow_pos (inv_pos.mpr hρ) 2) g := by
    simp only [inv_pow]
  rw [hscale] at hupper
  let : MetricSpace M := m.rescale ρ⁻¹ (inv_pos.mpr hρ)
  have : CompleteSpace M :=
    (m.rescale_completeSpace_iff ρ⁻¹ (inv_pos.mpr hρ)).mpr inferInstance
  have hfin := ballVolume_lt_top_of_completeSpace
    (scaleMetric (ρ⁻¹ ^ 2) (pow_pos (inv_pos.mpr hρ) 2) g)
    (riemannianEDistOf_scaleMetric_inv_sq_eq_rescale (m := m) g hmetric hρ) p 2
  have hC := integral_sinh_sq_nonneg
  exact (ENNReal.le_ofReal_iff_toReal_le hfin.ne (by positivity)).mpr hupper

end Single

section Sequence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : ℕ → Type u} [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
  [∀ i, IsManifold I ∞ (X i)] [∀ i, SigmaCompactSpace (X i)] [∀ i, CompleteSpace (X i)]

/-- **LC07** for actual sequences: vanishing normalized volume at an attained level below twice
the scale gives a subsequential pointed limit of Hausdorff dimension at most two. -/
theorem exists_rescaled_pointed_limit_dimH_le_two (hdim : Module.finrank ℝ E = 3)
    (g : ∀ i, SmoothRiemannianMetric I (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i) {ρ L w r : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i) (hL : Tendsto L atTop atTop)
    (hsec : ∀ i, ∀ y ∈ riemannianBallOf (g i) (p i) (L i * ρ i),
      SectionalBoundedBelowAt (g i) y (-((L i * ρ i) ^ 2)⁻¹))
    (hw : ∀ i, 0 < w i) (hwzero : Tendsto w atTop (𝓝 0)) (hr : ∀ i, 0 < r i)
    (hrρ : ∀ i, r i ≤ 2 * ρ i)
    (hvol : ∀ i, ballVolume (g i) (p i) (r i) = ENNReal.ofReal (w i * r i ^ 3)) :
    ∃ (Y : Type) (m : MetricSpace Y),
      letI := m
      ∃ (q : Y) (φ : ℕ → ℕ), StrictMono φ ∧ CompleteSpace Y ∧ ProperSpace Y ∧
        @PointedGHConverges (fun i => X (φ i))
          (fun i => (mX (φ i)).rescale (ρ (φ i))⁻¹ (inv_pos.mpr (hρ (φ i)))) Y m
          (fun i => p (φ i)) q ∧
        dimH (univ : Set Y) ≤ 2 ∧ fourPointComparison 0 (univ : Set Y) ∧
        ∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
          f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (f s) (f t) = dist a b * dist s t := by
  have : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  obtain ⟨Y, m, q, φ, hφ, hcomplete, hproper, hconv, -, hcomp, hseg, -, -⟩ :=
    exists_rescaled_pointed_limit_of_sectional_buffer g hmetric p hρ hL hsec
  let := m
  refine ⟨Y, m, q, φ, hφ, hcomplete, hproper, hconv, ?_, hcomp, hseg⟩
  by_contra hfail
  obtain ⟨v, hv, hlower⟩ := eventually_rescaled_ballVolume_lower_of_dimH_gt_two
    (X := fun i => X (φ i)) (mX := fun i => mX (φ i)) hdim (fun i => g (φ i))
    (fun i => hmetric (φ i)) (fun i => p (φ i)) (fun i => hρ (φ i))
    (hL.comp hφ.tendsto_atTop) (fun i => hsec (φ i)) hconv (lt_of_not_ge hfail)
  have hφL := (hL.comp hφ.tendsto_atTop).eventually (eventually_ge_atTop 2)
  have hsmall : ∀ᶠ i in atTop, 8 * (3 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) * w (φ i) < v := by
    have hlim : Tendsto (fun i => 8 * (3 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) * w (φ i))
        atTop (𝓝 0) := by
      simpa using (hwzero.comp hφ.tendsto_atTop).const_mul
        (8 * (3 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2))
    exact hlim.eventually (gt_mem_nhds hv)
  obtain ⟨i, hi, hiL, hismall⟩ := (hlower.and (hφL.and hsmall)).exists
  have hup := ballVolume_rescaled_two_le_of_buffer (m := mX (φ i)) hdim (g (φ i))
    (hmetric (φ i)) (p (φ i)) (hw (φ i)) (hr (φ i)) (hρ (φ i)) (hrρ (φ i)) hiL (hvol (φ i))
    (hsec (φ i))
  have hC := integral_sinh_sq_nonneg
  have := (ENNReal.ofReal_le_ofReal_iff (by have := hw (φ i); positivity)).mp (hi.trans hup)
  linarith

end Sequence

end DifferentialGeometry.Geometry.Collapse
