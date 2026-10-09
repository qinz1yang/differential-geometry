import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongWindowSpliceCylC12X

/-!
# Strong neck from closeness to shifted, rescaled cylinders (C12X, O-C12X-S16H G4c)

After the frame change of the far-early branch of `hwin`, the normalized flow at each target time
`s ∈ [-1, 0]` is close to `cyl2 (s + e s) (c s)` (its own reference), with `e s` and `c s - 1`
small (shift from the scalar normalization, axial factor from the pre/post normalization
mismatch).  This file converts that into the input of the Splice core (G4b):

* `exists_background_close_of_cyl2_close_C12X`: closeness to `cyl2 (s + e) c` ⇒ closeness to the
  background `cylFam s` with reference `cylFam 0`, uniformly on the neck buffer;
* `exists_strongNeck_of_cyl2_close_C12X`: hence a strong `ε`-neck
  (`exists_strongNeck_of_uniform_close_C12X`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

private local instance s16h_sphereDim3 :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

private local instance s16h_bufferSigma3 (ε : ℝ) : SigmaCompactSpace (spatialNeckBuffer ε) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen SpatialNeckCylinderModel
      (spatialNeckBuffer ε).isOpen)

/-- **Shift, stretch and reference change.**  Closeness to a slightly time-shifted, axially
rescaled cylinder `cyl2 (s + e) c` (measured with itself as reference) gives closeness to the
background `cylFam s` with the fixed reference `cylFam 0`, uniformly on the neck buffer. -/
theorem exists_background_close_of_cyl2_close_C12X (ε : ℝ) (p : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∀ (g : SmoothRiemannianMetric SpatialNeckCylinderModel (spatialNeckBuffer ε))
      (s e c : ℝ), s ∈ Icc (-1 : ℝ) 0 → |e| < η → |c - 1| < η →
      (∀ q ≤ p, ∀ x : spatialNeckBuffer ε,
        metricDerivNorm q g ((cyl2_C12X (s + e) c).restrictOpen (spatialNeckBuffer ε))
          ((cyl2_C12X (s + e) c).restrictOpen (spatialNeckBuffer ε)) x < η) →
      ∀ q ≤ p, ∀ x : spatialNeckBuffer ε,
        metricDerivNorm q g (strongNeckBackgroundMetric ε s) (strongNeckBackgroundMetric ε 0) x
          < δ := by
  let U := spatialNeckBuffer ε
  obtain ⟨D, hD, hRC⟩ := exists_cyl2_reference_bound_C12X ε p
  let Kc : Set SpatialNeckCylinder := univ ×ˢ Icc (-(ε⁻¹ + 1)) (ε⁻¹ + 1)
  have hKc : IsCompact Kc := isCompact_univ.prod isCompact_Icc
  have hUK (x : U) : x.val ∈ Kc := by
    have hx := x.2
    change -ε⁻¹ - 1 < x.val.2 ∧ x.val.2 < ε⁻¹ + 1 at hx
    exact ⟨mem_univ _, by linarith [hx.1], by linarith [hx.2]⟩
  have hshift (q : ℕ) := exists_cyl2_shift_small_C12X q hKc (half_pos hδ)
  choose η₂ hη₂ hsm using hshift
  let ηs : ℝ := (Finset.range (p + 1)).inf' ⟨0, by simp⟩ η₂
  have hηs : 0 < ηs := (Finset.lt_inf'_iff _).mpr fun q _ => hη₂ q
  let η₁ : ℝ := δ / (2 * (D + 1) * ((p : ℝ) + 1))
  have hη₁ : 0 < η₁ := by positivity
  refine ⟨min (1 / 2) (min ηs η₁), by positivity, ?_⟩
  intro g s e c hs he hc hclose q hq x
  have hmin1 : min (1 / 2) (min ηs η₁) ≤ 1 / 2 := min_le_left _ _
  have hmin2 : min (1 / 2) (min ηs η₁) ≤ ηs := (min_le_right _ _).trans (min_le_left _ _)
  have hmin3 : min (1 / 2) (min ηs η₁) ≤ η₁ := (min_le_right _ _).trans (min_le_right _ _)
  have he' := abs_lt.mp (he.trans_le hmin1)
  have hc' := abs_lt.mp (hc.trans_le hmin1)
  have ha : (s + e, c) ∈ cylBox_C12X :=
    ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, ⟨by linarith, by linarith⟩⟩
  have hb : ((s, 1) : ℝ × ℝ) ∈ cylBox_C12X :=
    ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, ⟨by norm_num, by norm_num⟩⟩
  have h0 : ((0, 1) : ℝ × ℝ) ∈ cylBox_C12X :=
    ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩
  rw [strongNeckBackgroundMetric_eq_cylFam_C12X ε s hs.2,
    strongNeckBackgroundMetric_eq_cylFam_C12X ε 0 le_rfl,
    ← cyl2_one_C12X (show s < 1 by linarith [hs.2]), ← cyl2_one_C12X (show (0 : ℝ) < 1 by norm_num)]
  have htri := metricDerivNorm_triangle q g ((cyl2_C12X (s + e) c).restrictOpen U)
    ((cyl2_C12X s 1).restrictOpen U) ((cyl2_C12X 0 1).restrictOpen U) x
  have h1 : metricDerivNorm q g ((cyl2_C12X (s + e) c).restrictOpen U)
      ((cyl2_C12X 0 1).restrictOpen U) x < δ / 2 := by
    have hrc := hRC (s + e, c) ha (0, 1) h0 g ((cyl2_C12X (s + e) c).restrictOpen U) q hq x
    have hsum : (∑ k ∈ Finset.range (p + 1), metricDerivNorm k g
        ((cyl2_C12X (s + e) c).restrictOpen U) ((cyl2_C12X (s + e) c).restrictOpen U) x) ≤
        ((p : ℝ) + 1) * min (1 / 2) (min ηs η₁) := by
      calc _ ≤ ∑ _k ∈ Finset.range (p + 1), min (1 / 2) (min ηs η₁) :=
            Finset.sum_le_sum fun k hk =>
              (hclose k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) x).le
        _ = ((p : ℝ) + 1) * min (1 / 2) (min ηs η₁) := by simp
    have hp1 : (0 : ℝ) < (p : ℝ) + 1 := by positivity
    calc _ ≤ D * (((p : ℝ) + 1) * min (1 / 2) (min ηs η₁)) :=
          hrc.trans (mul_le_mul_of_nonneg_left hsum hD)
      _ ≤ D * (((p : ℝ) + 1) * η₁) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmin3 hp1.le) hD
      _ < δ / 2 := by
          dsimp only [η₁]
          rw [← mul_assoc, mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [mul_pos hδ hp1]
  have h2 : metricDerivNorm q ((cyl2_C12X (s + e) c).restrictOpen U)
      ((cyl2_C12X s 1).restrictOpen U) ((cyl2_C12X 0 1).restrictOpen U) x < δ / 2 := by
    rw [metricDerivNorm_restrictOpen]
    have hηq : ηs ≤ η₂ q := Finset.inf'_le _ (Finset.mem_range.mpr (by omega))
    refine hsm q (s + e, c) (s, 1) (0, 1) ha hb h0 ?_ ?_ x.val (hUK x)
    · change |s + e - s| < η₂ q
      rw [add_sub_cancel_left]
      exact (he.trans_le hmin2).trans_le hηq
    · exact (hc.trans_le hmin2).trans_le hηq
  linarith

universe u

/-- **Strong neck from closeness to shifted, rescaled cylinders.**  For `ε ∈ (0, 1/11)` and a
depth buffer `μ > 0` there are `δ > 0`, `p` such that: if the flow lives on the window
`[t - (1 + μ) R⁻¹, t]` and, at every `s ∈ [-1, 0]`, its normalized pullback by a neck embedding
is `δ`-close in `C^p` to `cyl2 (s + e s) (c s)` (as its own reference) with `|e s|, |c s - 1| < δ`,
then `x₀` is the center of a strong `ε`-neck at time `t`. -/
theorem exists_strongNeck_of_cyl2_close_C12X {ε μ : ℝ} (hε : 0 < ε) (hε11 : ε < 1 / 11)
    (hμ : 0 < μ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ p : ℕ, ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] {D : RealTimeInterval}
      (S : SolutionOn (I := I3) (M := M) D), IsSolutionOn S →
      ∀ (t : ℝ) (yStar : SpatialNeckSphere) (f : C(spatialNeckBuffer ε, M))
        (hf : _root_.Manifold.IsSmoothEmbedding SpatialNeckCylinderModel I3 ∞ f) (x₀ : M),
        f (spatialNeckCentralPoint ε hε yStar) = x₀ → ∀ hQ : 0 < S.scalar t x₀,
      Icc (t - (1 + μ) * (S.scalar t x₀)⁻¹) t ⊆ D.carrier →
      Ioo (t - (1 + μ) * (S.scalar t x₀)⁻¹) t ⊆ D.regular →
      ∀ e c : ℝ → ℝ, (∀ s ∈ Icc (-1 : ℝ) 0, |e s| < δ ∧ |c s - 1| < δ) →
      (∀ s ∈ Icc (-1 : ℝ) 0, ∀ q ≤ p, ∀ x : spatialNeckBuffer ε,
        metricDerivNorm q (strongNeckNormalizedMetric S x₀ t hQ hf s)
          ((cyl2_C12X (s + e s) (c s)).restrictOpen (spatialNeckBuffer ε))
          ((cyl2_C12X (s + e s) (c s)).restrictOpen (spatialNeckBuffer ε)) x < δ) →
      Nonempty (StrongNeck S ε x₀ t) := by
  obtain ⟨δb, hδb, pb, hwrap⟩ := exists_strongNeck_of_uniform_close_C12X.{u} hε hε11 hμ
  obtain ⟨η, hη, hcomb⟩ := exists_background_close_of_cyl2_close_C12X ε pb hδb
  refine ⟨η, hη, pb, ?_⟩
  intro M _ _ _ _ _ D S hS t yStar f hf x₀ hx₀ hQ hwin hreg e c hec hclose
  exact hwrap S hS t yStar f hf x₀ hx₀ hQ hwin hreg fun s hs q hq x =>
    hcomb _ s (e s) (c s) hs (hec s hs).1 (hec s hs).2 (fun q' hq' x' => hclose s hs q' hq' x')
      q hq x

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
