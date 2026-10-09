import DifferentialGeometry.Geometry.Measure.LocalIsometrySection
import DifferentialGeometry.Geometry.Measure.CoveringBall
import Mathlib.GroupTheory.OrderOfElement

noncomputable section

open Set Function MeasureTheory
open scoped Manifold ContDiff ENNReal
open DifferentialGeometry.Integral.Measure (riemannianVolumeMeasure)

namespace DifferentialGeometry.Geometry.Measure

variable {E F H H' X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [T2Space X] [SigmaCompactSpace X]
  [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold J ∞ Y]
  [T2Space Y] [SigmaCompactSpace Y]

private local instance : MeasurableSpace X := borel X
private local instance : BorelSpace X := ⟨rfl⟩
private local instance : MeasurableSpace Y := borel Y
private local instance : BorelSpace Y := ⟨rfl⟩

theorem nat_mul_volume_ball_le_of_short_deck_displacement
    {G : Type*} [Group G] [MulAction G X] [ContinuousConstSMul G X]
    (g : SmoothRiemannianMetric I X) (h : SmoothRiemannianMetric J Y)
    {p : X → Y} (hp : IsLocalDiffeomorph I J ∞ p) (hcover : IsCoveringMap p)
    (hpull : localPullMetric h p hp = g)
    (hproj : ∀ (a : G) (y : X), p (a • y) = p y)
    (hfree : ∀ a : G, a ≠ 1 → ∀ y : X, a • y ≠ y)
    (hiso : ∀ (a : G) (y z : X), riemannianEDistOf g (a • y) (a • z) = riemannianEDistOf g y z)
    (hvol : ∀ a : G, MeasurePreserving (fun y : X => a • y)
      (riemannianVolumeMeasure I X g) (riemannianVolumeMeasure I X g))
    (a : G) (ha : ¬ IsOfFinOrder a) (x : X) (R δ : ℝ) (hR : 0 < R) (hδ : 0 ≤ δ)
    (hshort : riemannianEDistOf g x (a • x) ≤ ENNReal.ofReal δ) (N : ℕ) :
    (N : ℝ≥0∞) * riemannianVolumeMeasure J Y h (riemannianBallOf h (p x) R) ≤
      riemannianVolumeMeasure I X g (riemannianBallOf g x (R + ((N - 1 : ℕ) : ℝ) * δ)) := by
  let V : TopologicalSpace.Opens X := ⟨riemannianBallOf g x R,
    isOpen_lt (Riemannian.continuous_riemannianEDist g x) continuous_const⟩
  have hmetric (y : X) (v w : TangentSpace I y) :
      g.inner y v w = h.inner (p y) (mfderiv I J p y v) (mfderiv I J p y w) := by
    rw [← hpull, localPullMetric_inner]
  obtain ⟨D, hD, hDV, hbij, hDvol⟩ :=
    exists_measurable_subset_bijOn_volume_eq_of_local_isometry g h p hp V hmetric
  have himage : p '' (V : Set X) = riemannianBallOf h (p x) R :=
    Metric.image_riemannianBallOf_of_coveringMap_localPullMetric g h hp hcover hpull x R
  rw [himage] at hDvol
  let S (i : Fin N) : Set X := (fun y : X => a ^ (i : ℕ) • y) '' D
  have hSmeas (i : Fin N) : MeasurableSet (S i) :=
    (Homeomorph.smul (a ^ (i : ℕ))).measurableEmbedding.measurableSet_image.mpr hD
  have hSvol (i : Fin N) : riemannianVolumeMeasure I X g (S i) =
      riemannianVolumeMeasure I X g D := by
    have he : (fun y : X => a ^ (i : ℕ) • y) ⁻¹' S i = D := by
      exact Set.preimage_image_eq _ (MulAction.injective (a ^ (i : ℕ)))
    have hm := (hvol (a ^ (i : ℕ))).measure_preimage (hSmeas i).nullMeasurableSet
    rw [he] at hm
    exact hm.symm
  have hSdisj : Pairwise (Disjoint on S) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro y ⟨u, hu, rfl⟩ ⟨v, hv, huv⟩
    dsimp only at huv
    have hpv : p v = p u := by
      rw [← hproj (a ^ (j : ℕ)) v, huv, hproj]
    have hvu : v = u := hbij.injOn hv hu hpv
    subst v
    have hneq : (a ^ (i : ℕ))⁻¹ * a ^ (j : ℕ) ≠ 1 := by
      intro he
      apply hij
      apply Fin.ext
      exact injective_pow_iff_not_isOfFinOrder.mpr ha (inv_mul_eq_one.mp he)
    apply hfree _ hneq u
    rw [mul_smul, huv, inv_smul_smul]
  have hpow (n : ℕ) : riemannianEDistOf g x (a ^ n • x) ≤ ENNReal.ofReal ((n : ℝ) * δ) := by
    induction n with
    | zero => simp [riemannianEDistOf_self]
    | succ n ih =>
      calc
        riemannianEDistOf g x (a ^ (n + 1) • x) ≤
            riemannianEDistOf g x (a ^ n • x) +
              riemannianEDistOf g (a ^ n • x) (a ^ (n + 1) • x) :=
          riemannianEDistOf_triangle g _ _ _
        _ = riemannianEDistOf g x (a ^ n • x) + riemannianEDistOf g x (a • x) := by
          rw [pow_succ, mul_smul, hiso]
        _ ≤ ENNReal.ofReal ((n : ℝ) * δ) + ENNReal.ofReal δ := add_le_add ih hshort
        _ = ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * δ) := by
          rw [← ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg n) hδ) hδ]
          congr 1
          push_cast
          ring
  have hsubset : (⋃ i, S i) ⊆ riemannianBallOf g x (R + ((N - 1 : ℕ) : ℝ) * δ) := by
    intro y hy
    obtain ⟨i, u, hu, rfl⟩ := mem_iUnion.mp hy
    have huR : riemannianEDistOf g x u < ENNReal.ofReal R := hDV hu
    have hn : (i : ℕ) ≤ N - 1 := Nat.le_sub_one_of_lt i.isLt
    have hbound : riemannianEDistOf g x (a ^ (i : ℕ) • x) ≤
        ENNReal.ofReal (((N - 1 : ℕ) : ℝ) * δ) :=
      (hpow i).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hδ))
    calc
      riemannianEDistOf g x (a ^ (i : ℕ) • u) ≤
          riemannianEDistOf g x (a ^ (i : ℕ) • x) +
            riemannianEDistOf g (a ^ (i : ℕ) • x) (a ^ (i : ℕ) • u) :=
        riemannianEDistOf_triangle g _ _ _
      _ = riemannianEDistOf g x (a ^ (i : ℕ) • x) + riemannianEDistOf g x u := by rw [hiso]
      _ < ENNReal.ofReal (((N - 1 : ℕ) : ℝ) * δ) + ENNReal.ofReal R :=
        ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound) hbound huR
      _ = ENNReal.ofReal (R + ((N - 1 : ℕ) : ℝ) * δ) := by
        rw [← ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg _) hδ) hR.le, add_comm]
  calc
    (N : ℝ≥0∞) * riemannianVolumeMeasure J Y h (riemannianBallOf h (p x) R) =
        ∑' i : Fin N, riemannianVolumeMeasure I X g (S i) := by
      simp only [hSvol, hDvol, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    _ = riemannianVolumeMeasure I X g (⋃ i, S i) := (measure_iUnion hSdisj hSmeas).symm
    _ ≤ riemannianVolumeMeasure I X g (riemannianBallOf g x (R + ((N - 1 : ℕ) : ℝ) * δ)) :=
      measure_mono hsubset

end DifferentialGeometry.Geometry.Measure
