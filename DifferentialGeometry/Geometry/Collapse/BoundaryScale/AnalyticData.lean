import DifferentialGeometry.Geometry.Collapse.BoundaryScale.StandingSequence
import DifferentialGeometry.Geometry.Collapse.NormalizedCenterData
import DifferentialGeometry.Geometry.Comparison.Volume.BishopGromovBoundaryBuffer

/-!
# Boundary analytic data (BSA06 kernels) and the metric envelope MC19 (BSA05 kernel)

Blueprint 207B, BSA06 (`B:7979`) and BSA05 (`B:7915`). Along the standing inequality
`2 n r_p(1/n) < R_p` (BSA04.a), with `u = r_p(w')`, `1/n ≤ w'`, and any `0 < ρ ≤ 2u` (the smooth
scale of BSA05 is DATA here), the LPA01 conclusions hold for the normalized metric `ρ⁻² g`:
* the sectional buffer on the scaled ball of radius `n/4`, at EVERY point (boundary included);
* the whole-ball derivative bounds `2^{K+2} A'(2R + 2, w')` for `2R + 2 < n`, at EVERY point;
* the LC04 volume lower bound `w'/(24 ∫₀¹ sinh²) ≤ vol B(p, ρ)/ρ³` at centers with
  `u < d(p, ∂W)`, in particular at centers with `d(p, ∂W) > 10` once BSA01.c (`R_p ≤ d + 3`) holds.
  Near the boundary this clause needs the convex-boundary comparison BSA02 (not available).
A positive first volume scale is attained exactly (`ballVolume_firstVolumeScale_eq_of_pos`), on
any compact manifold. MC19: a pairwise envelope inequality gives a Lipschitz function between the
two scales (`exists_lipschitz_between_of_envelope`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian GC.Endpoint
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- MC19: if `l p - K d(p, q) ≤ u q` for all `p, q`, the envelope
`f p = sup_q (l q - K d(p, q))` is `K`-Lipschitz with `l ≤ f ≤ u`. -/
theorem exists_lipschitz_between_of_envelope {X : Type*} [PseudoMetricSpace X]
    {l v : X → ℝ} {K : ℝ} (hK : 0 ≤ K) (henv : ∀ p q, l p - K * dist p q ≤ v q) :
    ∃ f : X → ℝ, LipschitzWith (Real.toNNReal K) f ∧ ∀ p, l p ≤ f p ∧ f p ≤ v p := by
  have hbdd : ∀ p : X, BddAbove (Set.range fun q => l q - K * dist p q) := by
    intro p
    refine ⟨v p, ?_⟩
    rintro _ ⟨q, rfl⟩
    have h := henv q p
    rwa [dist_comm] at h
  have hKK : ((Real.toNNReal K : ℝ≥0) : ℝ) = K := Real.coe_toNNReal _ hK
  refine ⟨fun p => ⨆ q, (l q - K * dist p q), ?_, fun p => ?_⟩
  · apply LipschitzWith.of_le_add_mul
    intro x y
    have : Nonempty X := ⟨x⟩
    rw [hKK]
    apply ciSup_le
    intro q
    have h1 := le_ciSup (hbdd y) q
    have h2 := dist_triangle y x q
    rw [dist_comm y x] at h2
    nlinarith
  · have : Nonempty X := ⟨p⟩
    refine ⟨?_, ?_⟩
    · have h := le_ciSup (hbdd p) p
      simpa only [dist_self, mul_zero, sub_zero] using h
    · apply ciSup_le
      intro q
      have h := henv q p
      rwa [dist_comm] at h

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

omit [CompleteSpace E] in
/-- A positive first volume scale is attained exactly, on any compact manifold (boundary allowed;
no small-ball estimate is used). -/
theorem ballVolume_firstVolumeScale_eq_of_pos (g : SmoothRiemannianMetric I M) (p : M)
    {w : ℝ} (hw : 0 < w) (hpos : 0 < firstVolumeScale g p w) :
    ballVolume g p (firstVolumeScale g p w) =
      ENNReal.ofReal (w * firstVolumeScale g p w ^ 3) := by
  set S : Set ℝ := {r | 0 < r ∧ (ballVolume g p r).toReal ≤ w * r ^ 3} with hSdef
  have hS : S.Nonempty := exists_ballVolume_toReal_le_cube g p hw
  have hB : BddBelow S := ⟨0, fun _ hr => hr.1.le⟩
  have hu : firstVolumeScale g p w = sInf S := rfl
  have hle : (ballVolume g p (firstVolumeScale g p w)).toReal ≤
      w * firstVolumeScale g p w ^ 3 := by
    have : NeBot (𝓝[S] (firstVolumeScale g p w)) :=
      mem_closure_iff_nhdsWithin_neBot.mp (hu ▸ csInf_mem_closure hS hB)
    have hF : ContinuousWithinAt (fun r : ℝ => w * r ^ 3) S (firstVolumeScale g p w) :=
      (by fun_prop : Continuous fun r : ℝ => w * r ^ 3).continuousAt.continuousWithinAt
    apply ge_of_tendsto hF
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (ballVolume_toReal_monotone g p (hu ▸ csInf_le hB hr)).trans hr.2
  have hge := le_ballVolume_toReal_firstVolumeScale_of_pos g p hpos
  rw [← ENNReal.ofReal_toReal (ballVolume_ne_top g p (firstVolumeScale g p w)),
    le_antisymm hle hge]

omit [CompactSpace M] [CompleteSpace E] in
/-- The standing inequality bounds the curvature scale below by `n r_p(w')` for `1/n ≤ w'`. -/
theorem ofReal_mul_firstVolumeScale_le_of_standing [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (p : M) {n w' : ℝ} (hn : 0 < n)
    (hstand : ENNReal.ofReal (2 * n * firstVolumeScale g p n⁻¹) < curvatureRadius g p)
    (hwn : n⁻¹ ≤ w') :
    ENNReal.ofReal (n * firstVolumeScale g p w') < curvatureRadius g p := by
  have hle := firstVolumeScale_anti_of_le g p (inv_pos.mpr hn) hwn
  have h0 := firstVolumeScale_nonneg g p w'
  refine (ENNReal.ofReal_le_ofReal ?_).trans_lt hstand
  nlinarith

/-- BSA06, sectional clause at EVERY point: the normalized metric `ρ⁻² g` has sectional curvature
at least `-(n/4)⁻²` on its ball of radius `n/4`. -/
theorem normalizedCenterMetric_sectional_of_standing (g : SmoothRiemannianMetric I M) (p : M)
    {n w' ρ : ℝ} (hn : 0 < n)
    (hstand : ENNReal.ofReal (2 * n * firstVolumeScale g p n⁻¹) < curvatureRadius g p)
    (hwn : n⁻¹ ≤ w') (hρ : 0 < ρ) (hρu : ρ ≤ 2 * firstVolumeScale g p w') :
    ∀ y ∈ riemannianBallOf (normalizedCenterMetric g ρ hρ) p (n / 4),
      SectionalBoundedBelowAt (normalizedCenterMetric g ρ hρ) y (-((n / 4) ^ 2)⁻¹) := by
  have hu : 0 < firstVolumeScale g p w' := by linarith
  exact normalizedCenterMetric_sectional_buffer g p hn hu hρ hρu
    (ofReal_mul_firstVolumeScale_le_of_standing g p hn hstand hwn).le

/-- BSA06, derivative clause at EVERY point: the whole-ball bounds
`2^{K+2} A'(2R + 2, w')` for `ρ⁻² g` on its balls of radius `R`, `2R + 2 < n`. -/
theorem normalizedCenterMetric_derivative_bounds_of_standing
    (g : SmoothRiemannianMetric I M) (p : M) {K : ℕ} {A : ℝ → ℝ} {δ n w' ρ : ℝ}
    (hderiv : curvatureDerivativesControlled g K A δ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w)
    (hn : 1 < n) (hδn : δ * n ^ 4 ≤ 1)
    (hstand : ENNReal.ofReal (2 * n * firstVolumeScale g p n⁻¹) < curvatureRadius g p)
    (hwn : n⁻¹ ≤ w') (hwc : w' < euclideanThreeUnitBallVolume)
    (hρ : 0 < ρ) (hρu : ρ ≤ 2 * firstVolumeScale g p w') :
    ∀ R, 0 < R → 2 * R + 2 < n → ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf (normalizedCenterMetric g ρ hρ) p R,
        curvatureDerivativeNorm (normalizedCenterMetric g ρ hρ) k y ≤
          (2 : ℝ) ^ (K + 2) * boundaryDerivativeConstant A K (2 * R + 2) w' := by
  have hu : 0 < firstVolumeScale g p w' := by linarith
  have hnpos : 0 < n := zero_lt_one.trans hn
  have hw' : 0 < w' := (inv_pos.mpr hnpos).trans_le hwn
  have hAnn : ∀ C, 0 < C → 0 ≤ boundaryDerivativeConstant A K C w' := by
    intro C _
    have hD1 : 1 ≤ max 1 C := le_max_left _ _
    have hD3 : 0 < (max 1 C) ^ 3 := by positivity
    have harg : 0 < ((max 1 C) ^ 3)⁻¹ * w' := by positivity
    have hargc : ((max 1 C) ^ 3)⁻¹ * w' < euclideanThreeUnitBallVolume :=
      (mul_le_of_le_one_left hw'.le (inv_le_one_of_one_le₀ (one_le_pow₀ hD1))).trans_lt hwc
    have hterm : 0 ≤ A (((max 1 C) ^ 3)⁻¹ * w') * ((max 1 C) ^ (0 + 2))⁻¹ :=
      mul_nonneg (hA _ harg hargc).le (by positivity)
    exact hterm.trans (Finset.le_sup'
      (fun j => A (((max 1 C) ^ 3)⁻¹ * w') * ((max 1 C) ^ (j + 2))⁻¹)
      (Finset.mem_range.mpr (Nat.succ_pos K)))
  exact normalizedCenterMetric_derivative_bounds g p K
    (fun C => boundaryDerivativeConstant A K C w') hu hρ hρu hAnn
    (fun C _ hCn => curvatureDerivativeNorm_le_on_firstVolumeScale_ball g hderiv hn hδn
      hstand hCn hwn hwc)

end General

section Carrier

variable (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier)

/-- BSA06, volume clause at buffered centers: if `u = r_p(w') < d(p, ∂W)`, the LC04 lower bound
`w'/(24 ∫₀¹ sinh²) ≤ vol B(p, ρ)/ρ³` holds for `0 < ρ ≤ 2u`. -/
theorem volume_lower_at_modified_scale_of_standing (p : W.Carrier) {n w' ρ : ℝ}
    (hn : 1 ≤ n)
    (hstand : ENNReal.ofReal (2 * n * firstVolumeScale g p n⁻¹) < curvatureRadius g p)
    (hwn : n⁻¹ ≤ w') (hρ : 0 < ρ) (hρu : ρ ≤ 2 * firstVolumeScale g p w')
    (hdepth : ENNReal.ofReal (firstVolumeScale g p w') < distanceToBoundary W g p) :
    0 < w' / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ∧
      w' / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ≤ (ballVolume g p ρ).toReal / ρ ^ 3 := by
  have hnpos : 0 < n := zero_lt_one.trans_le hn
  have hw' : 0 < w' := (inv_pos.mpr hnpos).trans_le hwn
  have hu : 0 < firstVolumeScale g p w' := by linarith
  have hscale : ENNReal.ofReal (firstVolumeScale g p w') < curvatureRadius g p := by
    refine (ENNReal.ofReal_le_ofReal ?_).trans_lt
      (ofReal_mul_firstVolumeScale_le_of_standing g p hnpos hstand hwn)
    nlinarith
  exact volume_lower_at_modified_scale_of_distanceToBoundary W g p hw' hu hρ hρu hdepth
    (ballVolume_firstVolumeScale_eq_of_pos g p hw' hu)
    (fun q hq => sectionalBoundedBelowAt_of_lt_curvatureRadius g hscale hq)

/-- BSA06, volume clause at centers with `d(p, ∂W) > 10`, given BSA01.c (`R_p ≤ d + 3`). -/
theorem volume_lower_at_modified_scale_of_standing_of_ten_lt (p : W.Carrier) {n w' ρ : ℝ}
    (hn : 1 ≤ n)
    (hstand : ENNReal.ofReal (2 * n * firstVolumeScale g p n⁻¹) < curvatureRadius g p)
    (hwn : n⁻¹ ≤ w') (hρ : 0 < ρ) (hρu : ρ ≤ 2 * firstVolumeScale g p w')
    (hd : ENNReal.ofReal 10 < distanceToBoundary W g p)
    (hR : curvatureRadius g p ≤ distanceToBoundary W g p + ENNReal.ofReal 3) :
    0 < w' / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ∧
      w' / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ≤ (ballVolume g p ρ).toReal / ρ ^ 3 := by
  refine volume_lower_at_modified_scale_of_standing W g p hn hstand hwn hρ hρu ?_
  by_cases htop : distanceToBoundary W g p = ⊤
  · rw [htop]
    exact ENNReal.ofReal_lt_top
  set D := (distanceToBoundary W g p).toReal with hDdef
  have hDeq : distanceToBoundary W g p = ENNReal.ofReal D := (ENNReal.ofReal_toReal htop).symm
  rw [hDeq] at hd hR ⊢
  have hD : 10 < D := (ENNReal.ofReal_lt_ofReal_iff'.mp hd).1
  rw [← ENNReal.ofReal_add (by linarith) (by norm_num)] at hR
  have hnpos : 0 < n := zero_lt_one.trans_le hn
  have h2 : 2 * n * firstVolumeScale g p n⁻¹ < D + 3 :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mp (hstand.trans_le hR)
  have hle := firstVolumeScale_anti_of_le g p (inv_pos.mpr hnpos) hwn
  apply (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr
  have h0 := firstVolumeScale_nonneg g p w'
  nlinarith

end Carrier

end DifferentialGeometry.Geometry.Collapse
