import DifferentialGeometry.Geometry.Metric.Distance.Basic
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff ENNReal Manifold

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [RegularSpace M]

theorem lt_iInf_riemannianEDistOf_of_le_near_set
    (g : SmoothRiemannianMetric I M) (f : M → ℝ≥0∞) (S : Set M)
    (hf : ∀ x y, f x ≤ f y + riemannianEDistOf g x y)
    {c r : ℝ} (hc : 0 ≤ c) (hcr : c < r)
    (hnear : ∀ q, (⨅ b : S, riemannianEDistOf g q b) < ENNReal.ofReal r →
      f q ≤ ENNReal.ofReal c)
    {p : M} (hfar : ENNReal.ofReal c < ⨅ b : S, riemannianEDistOf g p b)
    (hfinite : (⨅ b : S, riemannianEDistOf g p b) ≠ ⊤) :
    f p < ⨅ b : S, riemannianEDistOf g p b := by
  let r₀ : ℝ := (c + r) / 2
  have hc₀ : c < r₀ := by dsimp [r₀]; linarith
  have hr₀ : r₀ < r := by dsimp [r₀]; linarith
  have hnear₀ : ∀ q, (⨅ b : S, riemannianEDistOf g q b) ≤ ENNReal.ofReal r₀ →
      f q ≤ ENNReal.ofReal c := by
    intro q hq
    exact hnear q (hq.trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff (hc.trans_lt hcr)).mpr hr₀))
  by_cases hnear_p : (⨅ b : S, riemannianEDistOf g p b) ≤ ENNReal.ofReal r₀
  · exact (hnear₀ p hnear_p).trans_lt hfar
  have hrfar : ENNReal.ofReal r₀ < ⨅ b : S, riemannianEDistOf g p b :=
    lt_of_not_ge hnear_p
  let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let _ : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  let d : ℝ≥0∞ := ⨅ b : S, riemannianEDistOf g p b
  have hd : d ≠ ⊤ := hfinite
  have hr : 0 < r₀ := hc.trans_lt hc₀
  let D : ℝ := d.toReal + (r₀ - c) / 2
  have hD : 0 < D := by
    dsimp [D]
    have hd0 : 0 ≤ d.toReal := ENNReal.toReal_nonneg
    linarith
  have hdD : d < ENNReal.ofReal D := by
    rw [← ENNReal.ofReal_toReal hd]
    exact (ENNReal.ofReal_lt_ofReal_iff hD).mpr (by dsimp [D]; linarith)
  obtain ⟨b, hpb⟩ := iInf_lt_iff.mp hdD
  obtain ⟨γ, hγ0, hγ1, hγ, hlength⟩ := exists_lt_of_riemannianEDist_lt hpb
  have hcont : ContinuousOn (fun t : ℝ => riemannianEDistOf g b (γ t)) (Icc 0 1) := by
    change ContinuousOn (fun t : ℝ => edist (b : M) (γ t)) (Icc 0 1)
    exact (continuous_const.edist continuous_id).comp_continuousOn hγ.continuousOn
  have hbp : ENNReal.ofReal r₀ ≤ riemannianEDistOf g b p := by
    rw [riemannianEDistOf_comm]
    exact hrfar.le.trans (iInf_le (fun b : S => riemannianEDistOf g p b) b)
  obtain ⟨t, ht, hbt⟩ := intermediate_value_Icc' zero_le_one hcont
    (show ENNReal.ofReal r₀ ∈ Icc (riemannianEDistOf g b (γ 1))
        (riemannianEDistOf g b (γ 0)) by
      rw [hγ0, hγ1, riemannianEDistOf_self]
      exact ⟨bot_le, hbp⟩)
  have hqb : riemannianEDistOf g (γ t) b = ENNReal.ofReal r₀ := by
    rw [riemannianEDistOf_comm]
    exact hbt
  have hq : f (γ t) ≤ ENNReal.ofReal c :=
    hnear₀ _ ((iInf_le (fun b : S => riemannianEDistOf g (γ t) b) b).trans_eq hqb)
  have hprefix : riemannianEDistOf g p (γ t) ≤ pathELength I γ 0 t :=
    riemannianEDist_le_pathELength (hγ.mono (Icc_subset_Icc le_rfl ht.2)) hγ0 rfl ht.1
  have htail : ENNReal.ofReal r₀ ≤ pathELength I γ t 1 := by
    rw [← hqb]
    exact riemannianEDist_le_pathELength (hγ.mono (Icc_subset_Icc ht.1 le_rfl))
      rfl hγ1 ht.2
  have hfp : f p ≤ ENNReal.ofReal c + pathELength I γ 0 t :=
    (hf p (γ t)).trans (add_le_add hq hprefix)
  have hsum : f p + ENNReal.ofReal r₀ < d + ENNReal.ofReal r₀ := by
    calc f p + ENNReal.ofReal r₀
        ≤ (ENNReal.ofReal c + pathELength I γ 0 t) + pathELength I γ t 1 :=
          add_le_add hfp htail
      _ = ENNReal.ofReal c + pathELength I γ 0 1 := by
          rw [add_assoc, pathELength_add ht.1 ht.2]
      _ < ENNReal.ofReal c + ENNReal.ofReal D :=
          ENNReal.add_lt_add_left ENNReal.ofReal_ne_top hlength
      _ = ENNReal.ofReal (c + D) := (ENNReal.ofReal_add hc hD.le).symm
      _ < ENNReal.ofReal (d.toReal + r₀) :=
          (ENNReal.ofReal_lt_ofReal_iff
            (add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg hr)).mpr (by
              dsimp [D]
              linarith)
      _ = d + ENNReal.ofReal r₀ := by
          rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hr.le, ENNReal.ofReal_toReal hd]
  exact (ENNReal.add_lt_add_iff_right ENNReal.ofReal_ne_top).mp hsum

end DifferentialGeometry.Geometry.Metric
