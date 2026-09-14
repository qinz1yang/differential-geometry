import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Geometry.Metric.Path.Composition
import DifferentialGeometry.Topology.FirstExit

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open DifferentialGeometry.Geometry.Riemannian
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_ball_subset_of_frontier_gap
    (g : SmoothRiemannianMetric I M) {A V : Set M} (hV : IsOpen V)
    (hAV : closure A ⊆ V) (f : M → ℝ) (hf : ContMDiffOn I 𝓘(ℝ) 1 f V)
    (C : NNReal)
    (hdf : ∀ q ∈ interior A, ∀ v : TangentSpace I q,
      |mvfderiv I f q v| ≤ (C : ℝ) * Real.sqrt (g.inner q v v))
    {p : M} (hp : p ∈ interior A) {d r : ℝ} (hd : 0 < d)
    (hfront : ∀ q ∈ frontier A, d ≤ |f q - f p|) (hmargin : (C : ℝ) * r ≤ d) :
    {y : M | riemannianEDistOf g p y < ENNReal.ofReal r} ⊆ interior A := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  intro y hy
  change riemannianEDist I p y < ENNReal.ofReal r at hy
  obtain ⟨γ, hγ0, hγ1, hγ, hγlen⟩ := exists_lt_of_riemannianEDist_lt hy
  by_contra hyA
  obtain ⟨t, ht, hbefore, hboundary⟩ :=
    exists_first_exit_frontier_of_not_mem_interior zero_lt_one hγ.continuousOn
      (hγ0 ▸ hp) (hγ1 ▸ hyA)
  have hmaps : MapsTo γ (Icc 0 t) V := by
    intro s hs
    apply hAV
    by_cases hst : s = t
    · subst s
      exact frontier_subset_closure hboundary
    · exact subset_closure (interior_subset (hbefore s ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩))
  have hcomp : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ) 1 (f ∘ γ) (Icc 0 t) :=
    hf.comp (hγ.mono (Icc_subset_Icc le_rfl ht.2)) hmaps
  have hγd : ∀ᵐ s ∂volume.restrict (Ioo 0 t), MDifferentiableAt 𝓘(ℝ) I γ s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact (hγ.contMDiffAt (Icc_mem_nhds hs.1 (hs.2.trans_le ht.2))).mdifferentiableAt one_ne_zero
  have hfd : ∀ᵐ s ∂volume.restrict (Ioo 0 t), MDifferentiableAt I 𝓘(ℝ) f (γ s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact (hf.contMDiffAt (hV.mem_nhds (hmaps ⟨hs.1.le, hs.2.le⟩))).mdifferentiableAt one_ne_zero
  have hnorm : ∀ᵐ s ∂volume.restrict (Ioo 0 t),
      ‖mfderiv I 𝓘(ℝ) f (γ s) (mfderiv 𝓘(ℝ) I γ s 1)‖ₑ ≤
        (C : ENNReal) * ‖mfderiv 𝓘(ℝ) I γ s 1‖ₑ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    rw [enorm_tangentSpace_vectorSpace]
    change ‖mvfderiv I f (γ s) (mfderiv 𝓘(ℝ) I γ s 1)‖ₑ ≤
      (C : ENNReal) * ‖mfderiv 𝓘(ℝ) I γ s 1‖ₑ
    erw [tensor0SBundle_enorm_eq_riemannianBundle_enorm g]
    rw [← ofReal_norm, Real.norm_eq_abs, ← ENNReal.ofReal_coe_nnreal]
    erw [← ENNReal.ofReal_mul C.property]
    exact ENNReal.ofReal_le_ofReal (hdf (γ s) (hbefore s ⟨hs.1.le, hs.2⟩) _)
  have hlength : pathELength 𝓘(ℝ) (f ∘ γ) 0 t ≤
      (C : ENNReal) * pathELength I γ 0 1 :=
    (pathELength_comp_le_of_enorm_mfderiv_le f C hγd hfd hnorm).trans
      (mul_le_mul_right (pathELength_mono le_rfl ht.2) _)
  have hshort : (C : ENNReal) * pathELength I γ 0 1 < ENNReal.ofReal d := by
    by_cases hC : C = 0
    · simpa only [hC, ENNReal.coe_zero, zero_mul] using ENNReal.ofReal_pos.mpr hd
    · calc
        _ < (C : ENNReal) * ENNReal.ofReal r :=
          ENNReal.mul_lt_mul_right (by exact_mod_cast hC) ENNReal.coe_ne_top hγlen
        _ = ENNReal.ofReal ((C : ℝ) * r) := by
          rw [← ENNReal.ofReal_coe_nnreal]
          exact (ENNReal.ofReal_mul (q := r) C.property).symm
        _ ≤ ENNReal.ofReal d := ENNReal.ofReal_le_ofReal hmargin
  have hfdist : ENNReal.ofReal |f (γ t) - f p| ≤ pathELength 𝓘(ℝ) (f ∘ γ) 0 t := by
    have h := riemannianEDist_le_pathELength hcomp rfl rfl ht.1.le
    rw [← IsRiemannianManifold.out (I := 𝓘(ℝ)), edist_dist, Real.dist_eq] at h
    simpa only [Function.comp_apply, hγ0, abs_sub_comm] using h
  exact (not_lt_of_ge (ENNReal.ofReal_le_ofReal (hfront (γ t) hboundary)))
    (hfdist.trans_lt (hlength.trans_lt hshort))

end DifferentialGeometry.Geometry.Metric
