import DifferentialGeometry.Geometry.Metric.Comparison.CurveLength
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section

open Manifold Set
open scoped ContDiff Manifold ENNReal

namespace DifferentialGeometry

private theorem exp_mul_sub_one_le
    {K R d : ℝ} (hK : 0 ≤ K) (hd : d ∈ Icc (0 : ℝ) R) :
    Real.exp (K * d) - 1 ≤ K * Real.exp (K * R) * d := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-(K * d)))
    (Real.exp_pos (K * d)).le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  have he : Real.exp (K * d) ≤ Real.exp (K * R) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hd.2 hK)
  calc
    Real.exp (K * d) - 1 ≤ K * d * Real.exp (K * d) := by linarith
    _ ≤ K * d * Real.exp (K * R) := mul_le_mul_of_nonneg_left he (mul_nonneg hK hd.1)
    _ = K * Real.exp (K * R) * d := by ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_lipschitzOnWith_riemannianEDistOf_toReal_of_le_exp_mul
    (g : ℝ → SmoothRiemannianMetric I M) {a b K : ℝ}
    (hcmp : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ p q : M,
      riemannianEDistOf (g s) p q ≤
        ENNReal.ofReal (Real.exp (K * |s - t|)) * riemannianEDistOf (g t) p q)
    (x y : ℝ → M) (Cx Cy : NNReal)
    (hx : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      riemannianEDistOf (g a) (x s) (x t) ≤ ENNReal.ofReal ((Cx : ℝ) * |t - s|))
    (hy : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      riemannianEDistOf (g a) (y s) (y t) ≤ ENNReal.ofReal ((Cy : ℝ) * |t - s|))
    (hfinite : riemannianEDistOf (g a) (x a) (y a) ≠ ⊤) :
    ∃ L : NNReal, LipschitzOnWith L
      (fun u ↦ (riemannianEDistOf (g u) (x u) (y u)).toReal) (Icc a b) := by
  by_cases hab : a ≤ b
  swap
  · refine ⟨0, LipschitzOnWith.of_dist_le_mul ?_⟩
    intro s hs
    exact False.elim (hab (hs.1.trans hs.2))
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  let d (t : ℝ) (p q : M) := riemannianEDistOf (g t) p q
  let K0 : ℝ := max K 0
  let R : ℝ := b - a
  have hK0 : 0 ≤ K0 := le_max_right K 0
  have hR : 0 ≤ R := sub_nonneg.mpr hab
  have hcmp0 : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ p q : M,
      d s p q ≤ ENNReal.ofReal (Real.exp (K0 * |s - t|)) * d t p q := by
    intro s hs t ht p q
    exact (hcmp s hs t ht p q).trans (mul_le_mul'
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (le_max_left K 0) (abs_nonneg _)))) le_rfl)
  have hxfin (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc a b) :
      d a (x s) (x t) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hx s hs t ht)
  have hyfin (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc a b) :
      d a (y s) (y t) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hy s hs t ht)
  have hxyfin (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc a b) :
      d a (x s) (y t) ≠ ⊤ := by
    apply ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mpr ⟨hxfin s hs a ha, ENNReal.add_ne_top.mpr
        ⟨hfinite, hyfin a ha t ht⟩⟩)
    exact (riemannianEDistOf_triangle (g a) (x s) (x a) (y t)).trans
      (add_le_add le_rfl (riemannianEDistOf_triangle (g a) (x a) (y a) (y t)))
  have hfin_time (u : ℝ) (hu : u ∈ Icc a b) (p q : M) (hfin : d a p q ≠ ⊤) :
      d u p q ≠ ⊤ := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) (hcmp0 u hu a ha p q)
  have hcmp_real (u : ℝ) (hu : u ∈ Icc a b) (v : ℝ) (hv : v ∈ Icc a b)
      (p q : M) (hfin : d v p q ≠ ⊤) :
      (d u p q).toReal ≤ Real.exp (K0 * |u - v|) * (d v p q).toReal := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)
      (hcmp0 u hu v hv p q)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] using h
  let A : ℝ := Real.exp (K0 * R)
  let C : ℝ := A * ((Cx : ℝ) + (Cy : ℝ))
  have hA : 0 ≤ A := (Real.exp_pos _).le
  have hC : 0 ≤ C := mul_nonneg hA (add_nonneg Cx.2 Cy.2)
  have hmove (u : ℝ) (hu : u ∈ Icc a b) (v : ℝ) (hv : v ∈ Icc a b)
      (z : ℝ → M) (Cz : NNReal)
      (hz : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        d a (z s) (z t) ≤ ENNReal.ofReal ((Cz : ℝ) * |t - s|)) :
      (d v (z u) (z v)).toReal ≤ A * (Cz : ℝ) * |v - u| := by
    have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hz u hu v hv)
    have hdist := hcmp_real v hv a ha (z u) (z v) hfin
    have hva : |v - a| ≤ R := by
      rw [abs_of_nonneg (sub_nonneg.mpr hv.1)]
      exact sub_le_sub_right hv.2 a
    have hexp : Real.exp (K0 * |v - a|) ≤ A :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hva hK0)
    have hzreal : (d a (z u) (z v)).toReal ≤ (Cz : ℝ) * |v - u| :=
      (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hz u hu v hv)).trans_eq
        (ENNReal.toReal_ofReal (mul_nonneg Cz.2 (abs_nonneg (v - u))))
    calc
      (d v (z u) (z v)).toReal ≤
          Real.exp (K0 * |v - a|) * (d a (z u) (z v)).toReal := hdist
      _ ≤ A * (d a (z u) (z v)).toReal :=
        mul_le_mul_of_nonneg_right hexp ENNReal.toReal_nonneg
      _ ≤ A * ((Cz : ℝ) * |v - u|) := mul_le_mul_of_nonneg_left hzreal hA
      _ = A * (Cz : ℝ) * |v - u| := by ring
  let F : ℝ → ℝ := fun u ↦ (d u (x u) (y u)).toReal
  have hstep (u : ℝ) (hu : u ∈ Icc a b) (v : ℝ) (hv : v ∈ Icc a b) :
      F v ≤ Real.exp (K0 * |v - u|) * F u + C * |v - u| := by
    have htri1 := riemannianEDistOf_toReal_triangle (g v) (x v) (x u) (y v)
      (hfin_time v hv _ _ (hxfin v hv u hu))
      (hfin_time v hv _ _ (hxyfin u hu v hv))
    have htri2 := riemannianEDistOf_toReal_triangle (g v) (x u) (y u) (y v)
      (hfin_time v hv _ _ (hxyfin u hu u hu))
      (hfin_time v hv _ _ (hyfin u hu v hv))
    rw [riemannianEDistOf_comm (g v) (x v) (x u)] at htri1
    have hxu := hmove u hu v hv x Cx hx
    have hyu := hmove u hu v hv y Cy hy
    have hxy := hcmp_real v hv u hu (x u) (y u)
      (hfin_time u hu _ _ (hxyfin u hu u hu))
    calc
      F v ≤ (d v (x u) (x v)).toReal + (d v (x u) (y v)).toReal := htri1
      _ ≤ (d v (x u) (x v)).toReal +
          ((d v (x u) (y u)).toReal + (d v (y u) (y v)).toReal) :=
        add_le_add le_rfl htri2
      _ ≤ A * (Cx : ℝ) * |v - u| +
          (Real.exp (K0 * |v - u|) * F u + A * (Cy : ℝ) * |v - u|) :=
        add_le_add hxu (add_le_add hxy hyu)
      _ = Real.exp (K0 * |v - u|) * F u + C * |v - u| := by
        dsimp only [C]
        ring
  let B : ℝ := A * F a + C * R
  have hB : 0 ≤ B :=
    add_nonneg (mul_nonneg hA ENNReal.toReal_nonneg) (mul_nonneg hC hR)
  have hFbound (u : ℝ) (hu : u ∈ Icc a b) : F u ≤ B := by
    have hua : |u - a| ≤ R := by
      rw [abs_of_nonneg (sub_nonneg.mpr hu.1)]
      exact sub_le_sub_right hu.2 a
    have hexp : Real.exp (K0 * |u - a|) ≤ A :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hua hK0)
    exact (hstep a ha u hu).trans (add_le_add
      (mul_le_mul_of_nonneg_right hexp ENNReal.toReal_nonneg)
      (mul_le_mul_of_nonneg_left hua hC))
  refine ⟨Real.toNNReal (K0 * A * B + C), LipschitzOnWith.of_le_add_mul' _ ?_⟩
  intro u hu v hv
  have hd : |u - v| ∈ Icc (0 : ℝ) R := by
    refine ⟨abs_nonneg _, ?_⟩
    change |u - v| ≤ b - a
    rw [abs_sub_le_iff]
    constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]
  have he1 : 1 ≤ Real.exp (K0 * |u - v|) :=
    Real.one_le_exp_iff.mpr (mul_nonneg hK0 hd.1)
  have hediff : Real.exp (K0 * |u - v|) - 1 ≤ K0 * A * |u - v| :=
    exp_mul_sub_one_le hK0 hd
  have hsub : F u - F v ≤ (K0 * A * B + C) * |u - v| := by
    calc
      F u - F v ≤ Real.exp (K0 * |u - v|) * F v + C * |u - v| - F v :=
        sub_le_sub_right (hstep v hv u hu) (F v)
      _ = (Real.exp (K0 * |u - v|) - 1) * F v + C * |u - v| := by ring
      _ ≤ (Real.exp (K0 * |u - v|) - 1) * B + C * |u - v| :=
        add_le_add (mul_le_mul_of_nonneg_left (hFbound v hv) (sub_nonneg.mpr he1)) le_rfl
      _ ≤ (K0 * A * |u - v|) * B + C * |u - v| :=
        add_le_add (mul_le_mul_of_nonneg_right hediff hB) le_rfl
      _ = (K0 * A * B + C) * |u - v| := by ring
  rw [Real.dist_eq]
  exact sub_le_iff_le_add'.mp hsub

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_lipschitzOnWith_riemannianEDistOf_toReal_of_le_exp_mul_of_contMDiffOn
    (g : ℝ → SmoothRiemannianMetric I M) {a b K : ℝ}
    (hcmp : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ p q : M,
      riemannianEDistOf (g s) p q ≤
        ENNReal.ofReal (Real.exp (K * |s - t|)) * riemannianEDistOf (g t) p q)
    (x y : ℝ → M)
    (hx : ContMDiffOn 𝓘(ℝ, ℝ) I 1 x (Icc a b))
    (hy : ContMDiffOn 𝓘(ℝ, ℝ) I 1 y (Icc a b))
    (hfinite : riemannianEDistOf (g a) (x a) (y a) ≠ ⊤) :
    ∃ L : NNReal, LipschitzOnWith L
      (fun u ↦ (riemannianEDistOf (g u) (x u) (y u)).toReal) (Icc a b) := by
  obtain ⟨Cx, hCx⟩ := exists_riemannianEDistOf_le_mul_abs_sub (g a) hx
  obtain ⟨Cy, hCy⟩ := exists_riemannianEDistOf_le_mul_abs_sub (g a) hy
  exact exists_lipschitzOnWith_riemannianEDistOf_toReal_of_le_exp_mul
    g hcmp x y Cx Cy hCx hCy hfinite

end DifferentialGeometry
