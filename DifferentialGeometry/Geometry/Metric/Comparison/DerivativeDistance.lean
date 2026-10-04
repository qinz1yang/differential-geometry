import Mathlib.Geometry.Manifold.Riemannian.Basic
import DifferentialGeometry.Geometry.Metric.Path.Composition

set_option autoImplicit false

noncomputable section
open Bundle Filter Manifold Set MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace Manifold

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [PseudoEMetricSpace M] [ChartedSpace H M]
  [PseudoEMetricSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [RiemannianBundle (fun x : N => TangentSpace J x)]
  [IsRiemannianManifold I M] [IsRiemannianManifold J N]

omit [IsRiemannianManifold I M] [IsRiemannianManifold J N] in
private theorem map_path_length_le
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I J 1 f U) {γ : ℝ → M} {a b : ℝ} {C : ℝ≥0}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (hmem : MapsTo γ (Icc a b) U)
    (hspeed : ∀ t ∈ Ioo a b, ∀ v : TangentSpace I (γ t),
      ‖mfderiv I J f (γ t) v‖ₑ ≤ (C : ℝ≥0∞) * ‖v‖ₑ) :
    pathELength J (f ∘ γ) a b ≤ (C : ℝ≥0∞) * pathELength I γ a b := by
  apply pathELength_comp_le_of_enorm_mfderiv_le f C
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (hγ.contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt one_ne_zero
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (hf.contMDiffAt (hU.mem_nhds (hmem (mem_Icc_of_Ioo ht)))).mdifferentiableAt
      one_ne_zero
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hspeed t ht _

private theorem image_eball_le_of_speed
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I J 1 f U) {x y : M} {r R : ℝ} {C : ℝ≥0}
    (hrR : r ≤ R) (hsub : Metric.closedEBall x (ENNReal.ofReal R) ⊆ U)
    (hspeed : ∀ z ∈ Metric.closedEBall x (ENNReal.ofReal R),
      ∀ v : TangentSpace I z, ‖mfderiv I J f z v‖ₑ ≤ (C : ℝ≥0∞) * ‖v‖ₑ)
    (hxy : edist x y < ENNReal.ofReal r) :
    edist (f x) (f y) ≤ (C : ℝ≥0∞) * ENNReal.ofReal r := by
  rw [IsRiemannianManifold.out (I := I)] at hxy
  obtain ⟨γ, hγ0, hγ1, hγ, hlength⟩ := exists_lt_of_riemannianEDist_lt hxy
  have hstay : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ Metric.closedEBall x (ENNReal.ofReal R) := by
    intro t ht
    rw [Metric.mem_closedEBall, edist_comm, IsRiemannianManifold.out (I := I)]
    calc
      _ ≤ pathELength I γ 0 t :=
        riemannianEDist_le_pathELength (hγ.mono (Icc_subset_Icc le_rfl ht.2)) hγ0 rfl ht.1
      _ ≤ pathELength I γ 0 1 := pathELength_mono le_rfl ht.2
      _ ≤ ENNReal.ofReal r := hlength.le
      _ ≤ ENNReal.ofReal R := ENNReal.ofReal_le_ofReal hrR
  have hcomp := hf.comp hγ (fun t ht => hsub (hstay t ht))
  have hl := map_path_length_le hU hf hγ (fun t ht => hsub (hstay t ht))
    (fun t ht => hspeed _ (hstay t (mem_Icc_of_Ioo ht)))
  rw [IsRiemannianManifold.out (I := J)]
  calc
    _ ≤ pathELength J (f ∘ γ) 0 1 :=
      riemannianEDist_le_pathELength hcomp (by simp [hγ0]) (by simp [hγ1]) zero_le_one
    _ ≤ (C : ℝ≥0∞) * pathELength I γ 0 1 := hl
    _ ≤ (C : ℝ≥0∞) * ENNReal.ofReal r := mul_le_mul_right hlength.le _

theorem edist_map_le_mul_of_enorm_mfderiv_le_on_closedEBall
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I J 1 f U) {x y : M} {R : ℝ} {C : ℝ≥0}
    (hsub : Metric.closedEBall x (ENNReal.ofReal R) ⊆ U)
    (hspeed : ∀ z ∈ Metric.closedEBall x (ENNReal.ofReal R),
      ∀ v : TangentSpace I z, ‖mfderiv I J f z v‖ₑ ≤ (C : ℝ≥0∞) * ‖v‖ₑ)
    (hxy : edist x y < ENNReal.ofReal R) :
    edist (f x) (f y) ≤ (C : ℝ≥0∞) * edist x y := by
  have hfinite : edist x y ≠ ⊤ := ne_top_of_lt hxy
  have hd : (edist x y).toReal < R := ENNReal.toReal_lt_of_lt_ofReal hxy
  have htend : Tendsto (fun r : ℝ => (C : ℝ≥0∞) * ENNReal.ofReal r)
      (𝓝[>] (edist x y).toReal) (𝓝 ((C : ℝ≥0∞) * edist x y)) := by
    have h := ((ENNReal.continuous_const_mul (a := (C : ℝ≥0∞)) ENNReal.coe_ne_top).comp
      ENNReal.continuous_ofReal).tendsto (edist x y).toReal
    simpa only [Function.comp_def, ENNReal.ofReal_toReal hfinite] using
      h.mono_left (nhdsWithin_le_nhds (s := Ioi (edist x y).toReal))
  apply ge_of_tendsto htend
  apply eventually_nhdsWithin_iff.mpr
  filter_upwards [eventually_lt_nhds hd] with r hrR hdr
  apply image_eball_le_of_speed hU hf hrR.le hsub hspeed
  rw [← ENNReal.ofReal_toReal hfinite]
  exact (ENNReal.ofReal_lt_ofReal_iff (ENNReal.toReal_nonneg.trans_lt hdr)).mpr hdr

end Manifold
