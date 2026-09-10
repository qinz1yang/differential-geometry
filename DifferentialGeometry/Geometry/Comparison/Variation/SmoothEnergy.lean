import DifferentialGeometry.Geometry.Comparison.Variation.CurveEnergy
import DifferentialGeometry.Topology.Manifold.SmoothInterval

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem curveEnergyDensity_contDiff (g : SmoothRiemannianMetric I M)
    (f : ℝ × ℝ → M) (hf : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ f) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => g.inner (f p)
      (mfderiv 𝓘(ℝ, ℝ) I (fun t => f (p.1, t)) p.2 1)
      (mfderiv 𝓘(ℝ, ℝ) I (fun t => f (p.1, t)) p.2 1)) := by
  have hconst : ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℝ × ℝ)).tangent ∞
      (fun p : ℝ × ℝ => (⟨p, (0, 1)⟩ : TangentBundle 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ))) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have hvel := (hf.contMDiff_tangentMap (m := ∞) (by simp)).comp hconst
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hi := ContMDiff.inner_bundle (F := E) (B := M)
    (E := TangentSpace I) hvel hvel
  have hs (p : ℝ × ℝ) :
      mfderiv 𝓘(ℝ, ℝ) I (fun t => f (p.1, t)) p.2 1 =
      mfderiv 𝓘(ℝ, ℝ × ℝ) I f p (0, 1) := by
    have hinc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun t : ℝ => (p.1, t)) := by
      exact (contDiff_const.prodMk contDiff_id).contMDiff
    have hc := mfderiv_comp p.2 (hf.mdifferentiable (by simp) (p.1, p.2))
      (hinc.mdifferentiable (by simp) p.2)
    have hd : fderiv ℝ (fun t : ℝ => (p.1, t)) p.2 =
        (0 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℝ) :=
      ((hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)).fderiv
    rw [mfderiv_eq_fderiv, hd] at hc
    exact congrArg (fun A => A (1 : ℝ)) hc
  have heq : (fun p : ℝ × ℝ => g.inner (f p)
      (mfderiv 𝓘(ℝ, ℝ) I (fun t => f (p.1, t)) p.2 1)
      (mfderiv 𝓘(ℝ, ℝ) I (fun t => f (p.1, t)) p.2 1)) =
      (fun p : ℝ × ℝ => g.inner (f p)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I f p (0, 1))
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I f p (0, 1))) := by
    ext p
    rw [hs]
  rw [heq]
  exact hi.contDiff


theorem curveEnergy_contDiff (g : SmoothRiemannianMetric I M)
    (f : ℝ × ℝ → M) (hf : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ f) (L : ℝ) :
    ContDiff ℝ ∞ (fun s => curveEnergy (I := I) g (fun t => f (s, t)) 0 L) := by
  by_cases hL : L = 0
  · subst L
    simpa [curveEnergy] using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ)))
  let D := fun p : ℝ × ℝ => g.inner (f p)
      (mfderiv 𝓘(ℝ, ℝ) I (fun t => f (p.1, t)) p.2 1)
      (mfderiv 𝓘(ℝ, ℝ) I (fun t => f (p.1, t)) p.2 1)
  have hD : ContDiff ℝ ∞ D := curveEnergyDensity_contDiff g f hf
  have hrescale : ContDiff ℝ ∞ (fun p : ℝ × ℝ => D (p.1, L * p.2)) :=
    hD.comp (contDiff_fst.prodMk (contDiff_const.mul contDiff_snd))
  have hInt := DifferentialGeometry.Analysis.Calculus.contDiffOn_paramIntervalIntegral
    (fun s t : ℝ => D (s, L * t)) hrescale.contDiffOn
  have hsmooth := (contDiffOn_univ.mp hInt).const_smul L
  convert hsmooth using 1
  ext s
  rw [intervalIntegral.integral_comp_mul_left (fun t => D (s, t)) hL]
  simp only [mul_zero, mul_one, smul_smul, mul_inv_cancel₀ hL, one_smul]
  rfl

theorem curveEnergy_contDiffOn_of_smooth_near_strip (g : SmoothRiemannianMetric I M)
    (f : ℝ × ℝ → M) {L ε : ℝ} (hL : 0 ≤ L)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hsub : (Ioo (-ε) ε ×ˢ Icc 0 L) ⊆ U)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ f U) :
    ContDiffOn ℝ ∞ (fun s => curveEnergy (I := I) g (fun t => f (s, t)) 0 L) (Ioo (-ε) ε) := by
  intro s hs
  obtain ⟨d, hd, heq⟩ := DifferentialGeometry.Topology.Manifold.exists_global_smooth_variation_eq_near_slice
    (s := s) hL hU (fun p hp => hsub ⟨by simpa only [Set.mem_singleton_iff.mp hp.1] using hs, hp.2⟩) hf
  have heqE : (fun r => curveEnergy (I := I) g (fun t => d (r, t)) 0 L) =ᶠ[𝓝 s]
      (fun r => curveEnergy (I := I) g (fun t => f (r, t)) 0 L) := by
    filter_upwards [heq] with r hr
    unfold curveEnergy
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hL] at ht
    have hbase := (hr t ht).eq_of_nhds
    have hderiv := (hr t ht).mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I)
    dsimp only
    rw [hbase, hderiv]
    rfl
  exact ((curveEnergy_contDiff g d hd L).contDiffAt.congr_of_eventuallyEq heqE.symm).contDiffWithinAt

end DifferentialGeometry.Geometry.Riemannian.Variation
