import DifferentialGeometry.Geometry.Collapse.CurvatureScale
import DifferentialGeometry.Geometry.Collapse.CompactBounds

set_option autoImplicit false
noncomputable section
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Collapse
universe u

theorem exists_common_curvature_derivative_bound_for_families (K : ℕ)
    (ι : ℕ → Type*)
    (W : (j : ℕ) → ι j → CompactCarrier.{u})
    (g : (j : ℕ) → (i : ι j) → SmoothRiemannianMetric (W j i).model (W j i).Carrier)
    (R : ℕ → ℝ → ℝ) (B : ℕ → ℝ)
    (hR : ∀ j w, 0 < R j w) (hB : ∀ j, 0 ≤ B j)
    (radius_bound : ∀ j (i : ι j) (p : (W j i).Carrier) (w r : ℝ), 0 < w →
      w < euclideanThreeUnitBallVolume → 0 < r →
      ENNReal.ofReal r < curvatureRadius (g j i) p →
      ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (g j i) p r → r ≤ R j w)
    (derivative_bound : ∀ j (i : ι j) (k : ℕ), k ≤ K → ∀ p : (W j i).Carrier,
      curvatureDerivativeNorm (g j i) k p ≤ B j)
    (eventual_bound : ∀ w : ℝ, 0 < w → w < euclideanThreeUnitBallVolume →
      ∃ N : ℕ, ∃ C : ℝ, 0 < C ∧
        ∀ j, N ≤ j → ∀ (i : ι j) (p : (W j i).Carrier) (r : ℝ), 0 < r →
          ENNReal.ofReal r < curvatureRadius (g j i) p →
          ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (g j i) p r →
          ∀ k : ℕ, k ≤ K → ∀ q ∈ riemannianBallOf (g j i) p r,
            curvatureDerivativeNorm (g j i) k q ≤ C * (r ^ (k + 2))⁻¹) :
    ∃ A : ℝ → ℝ,
      (∀ w, 0 < w → 0 < A w) ∧
      ∀ j (i : ι j) (w₀ : ℝ), 0 < w₀ → curvatureDerivativesControlled (g j i) K A w₀ := by
  classical
  choose! N C hCpos hbound using eventual_bound
  let D : ℕ → ℝ → ℝ := fun j w => B j * (max 1 (R j w)) ^ (K + 2)
  have hD : ∀ j w, 0 ≤ D j w := fun j w =>
    mul_nonneg (hB j) (pow_nonneg (le_trans (hR j w).le (le_max_right _ _)) _)
  let A : ℝ → ℝ := fun w =>
    if 0 < w ∧ w < euclideanThreeUnitBallVolume then
      max (C w) (∑ i ∈ Finset.range (N w), D i w) + 1 else 1
  refine ⟨A, ?_, ?_⟩
  · intro w hw
    simp only [A]
    split_ifs with h
    · have : 0 ≤ max (C w) (∑ i ∈ Finset.range (N w), D i w) :=
        le_max_of_le_right (Finset.sum_nonneg fun i _ => hD i w)
      linarith
    · exact one_pos
  · intro j i w₀ hw₀ p w r hw₀w hwc hr hrR hv k hk q hq
    have hw : 0 < w := lt_of_lt_of_le hw₀ hw₀w
    have hA : A w = max (C w) (∑ i ∈ Finset.range (N w), D i w) + 1 := by
      simp only [A, if_pos (And.intro hw hwc)]
    rw [hA]
    have hrk : 0 < r ^ (k + 2) := pow_pos hr _
    rcases le_or_gt (N w) j with hj | hj
    · have htail := hbound w hw hwc j hj i p r hr hrR hv k hk q hq
      refine le_trans htail ?_
      apply mul_le_mul_of_nonneg_right _ (inv_nonneg.2 hrk.le)
      have : C w ≤ max (C w) (∑ i ∈ Finset.range (N w), D i w) := le_max_left _ _
      linarith
    · have h1 := derivative_bound j i k hk q
      refine le_trans h1 ?_
      rw [le_mul_inv_iff₀ hrk]
      have hrR' : r ≤ R j w := radius_bound j i p w r hw hwc hr hrR hv
      have hr1 : r ≤ max 1 (R j w) := le_trans hrR' (le_max_right _ _)
      have hpow : r ^ (k + 2) ≤ (max 1 (R j w)) ^ (K + 2) := by
        calc r ^ (k + 2) ≤ (max 1 (R j w)) ^ (k + 2) := pow_le_pow_left₀ hr.le hr1 _
          _ ≤ (max 1 (R j w)) ^ (K + 2) := pow_le_pow_right₀ (le_max_left _ _) (by omega)
      have hDj : B j * r ^ (k + 2) ≤ D j w := mul_le_mul_of_nonneg_left hpow (hB j)
      have hsum : D j w ≤ ∑ i ∈ Finset.range (N w), D i w :=
        Finset.single_le_sum (fun i _ => hD i w) (Finset.mem_range.2 hj)
      have : ∑ i ∈ Finset.range (N w), D i w ≤ max (C w) (∑ i ∈ Finset.range (N w), D i w) :=
        le_max_right _ _
      linarith

theorem exists_common_curvature_derivative_bound_of_volume_tests (K : ℕ)
    (W : ℕ → CompactCarrier.{u})
    (g : (j : ℕ) → SmoothRiemannianMetric (W j).model (W j).Carrier)
    (R : ℕ → ℝ → ℝ) (B : ℕ → ℝ)
    (hR : ∀ j w, 0 < R j w) (hB : ∀ j, 0 ≤ B j)
    (radius_bound : ∀ j (p : (W j).Carrier) (w r : ℝ), 0 < w →
      w < euclideanThreeUnitBallVolume → 0 < r →
      ENNReal.ofReal r < curvatureRadius (g j) p →
      ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (g j) p r → r ≤ R j w)
    (derivative_bound : ∀ j (k : ℕ), k ≤ K → ∀ p : (W j).Carrier,
      curvatureDerivativeNorm (g j) k p ≤ B j)
    (eventual_bound : ∀ w : ℝ, 0 < w → w < euclideanThreeUnitBallVolume →
      ∃ N : ℕ, ∃ C : ℝ, 0 < C ∧
        ∀ j, N ≤ j → ∀ (p : (W j).Carrier) (r : ℝ), 0 < r →
          ENNReal.ofReal r < curvatureRadius (g j) p →
          ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (g j) p r →
          ∀ k : ℕ, k ≤ K → ∀ q ∈ riemannianBallOf (g j) p r,
            curvatureDerivativeNorm (g j) k q ≤ C * (r ^ (k + 2))⁻¹) :
    ∃ A : ℝ → ℝ,
      (∀ w, 0 < w → 0 < A w) ∧
      ∀ j (w₀ : ℝ), 0 < w₀ → curvatureDerivativesControlled (g j) K A w₀ := by
  exact exists_common_curvature_derivative_bound_for_families K (fun _ => Unit)
    (fun j _ => W j) (fun j _ => g j) R B hR hB
    (fun j _ => radius_bound j) (fun j _ => derivative_bound j)
    (fun w hw hc => by
      obtain ⟨N, C, hC, h⟩ := eventual_bound w hw hc
      exact ⟨N, C, hC, fun j hj _ => h j hj⟩) |>.imp fun A h =>
        ⟨h.1, fun j => h.2 j ()⟩

theorem exists_common_curvature_derivative_bound (K : ℕ)
    (W : ℕ → CompactCarrier.{u})
    (g : (j : ℕ) → SmoothRiemannianMetric (W j).model (W j).Carrier)
    (R B : ℕ → ℝ) (hR : ∀ j, 0 < R j) (hB : ∀ j, 0 ≤ B j)
    (radius_bound : ∀ j (p : (W j).Carrier) (r : ℝ), 0 < r →
      ENNReal.ofReal r < curvatureRadius (g j) p → r ≤ R j)
    (derivative_bound : ∀ j (k : ℕ), k ≤ K → ∀ p : (W j).Carrier,
      curvatureDerivativeNorm (g j) k p ≤ B j)
    (eventual_bound : ∀ w : ℝ, 0 < w → w < euclideanThreeUnitBallVolume →
      ∃ N : ℕ, ∃ C : ℝ, 0 < C ∧
        ∀ j, N ≤ j → ∀ (p : (W j).Carrier) (r : ℝ), 0 < r →
          ENNReal.ofReal r < curvatureRadius (g j) p →
          ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (g j) p r →
          ∀ k : ℕ, k ≤ K → ∀ q ∈ riemannianBallOf (g j) p r,
            curvatureDerivativeNorm (g j) k q ≤ C * (r ^ (k + 2))⁻¹) :
    ∃ A : ℝ → ℝ,
      (∀ w, 0 < w → 0 < A w) ∧
      ∀ j (w₀ : ℝ), 0 < w₀ → curvatureDerivativesControlled (g j) K A w₀ := by
  exact exists_common_curvature_derivative_bound_of_volume_tests K W g (fun j _ => R j) B
    (fun j _ => hR j) hB (fun j p _ r _ _ hr hρ _ => radius_bound j p r hr hρ)
    derivative_bound eventual_bound


theorem exists_common_curvature_derivative_bound_of_eventual (K : ℕ)
    (ι : ℕ → Type*) [∀ j, Finite (ι j)]
    (W : (j : ℕ) → ι j → CompactCarrier.{u})
    (g : (j : ℕ) → (i : ι j) → SmoothRiemannianMetric (W j i).model (W j i).Carrier)
    (eventual_bound : ∀ w : ℝ, 0 < w → w < euclideanThreeUnitBallVolume →
      ∃ N : ℕ, ∃ C : ℝ, 0 < C ∧
        ∀ j, N ≤ j → ∀ (i : ι j) (p : (W j i).Carrier) (r : ℝ), 0 < r →
          ENNReal.ofReal r < curvatureRadius (g j i) p →
          ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (g j i) p r →
          ∀ k : ℕ, k ≤ K → ∀ q ∈ riemannianBallOf (g j i) p r,
            curvatureDerivativeNorm (g j i) k q ≤ C * (r ^ (k + 2))⁻¹) :
    ∃ A : ℝ → ℝ,
      (∀ w, 0 < w → 0 < A w) ∧
      ∀ j (i : ι j) (w₀ : ℝ), 0 < w₀ → curvatureDerivativesControlled (g j i) K A w₀ := by
  classical
  let _ (j : ℕ) : Fintype (ι j) := Fintype.ofFinite (ι j)
  choose b hbpos hb using fun j i => exists_bound_curvatureDerivativeNorm_of_compactSpace (g j i) K
  choose! R _hRpos hR using fun j i w hw => exists_radius_bound_of_volume_lower (W j i) (g j i) w hw
  let B : ℕ → ℝ := fun j => ∑ i : ι j, b j i
  let L : ℕ → ℝ → ℝ := fun j w => 1 + ∑ i : ι j, max 1 (R j i w)
  have hL : ∀ j w, 0 < L j w := by
    intro j w
    have : 0 ≤ ∑ i : ι j, max 1 (R j i w) :=
      Finset.sum_nonneg fun i _ => (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
    dsimp [L]
    linarith
  have hB : ∀ j, 0 ≤ B j := fun j => Finset.sum_nonneg fun i _ => hbpos j i
  apply exists_common_curvature_derivative_bound_for_families K ι W g L B hL hB
  · intro j i p w r hw _ hr _ hv
    have hsum : max 1 (R j i w) ≤ ∑ i : ι j, max 1 (R j i w) :=
      Finset.single_le_sum (fun l _ => (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left 1 (R j l w)))
        (Finset.mem_univ i)
    have hrR := hR j i w hw p r hr hv
    have := le_max_right 1 (R j i w)
    dsimp [L]
    linarith
  · intro j i k hk p
    exact (hb j i k hk p).trans (Finset.single_le_sum (fun l _ => hbpos j l) (Finset.mem_univ i))
  · exact eventual_bound

end DifferentialGeometry.Geometry.Collapse
