import DifferentialGeometry.Topology.LoopSpace.Regular
import DifferentialGeometry.Analysis.Calculus.Derivative.AffineCurveFamilies









noncomputable section

open Set Function ContinuousMap Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Topology

variable {K E F : Type*} [TopologicalSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]



theorem exists_regular_affine_homotopy (e : M → F)
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 e) {r : F → M} {U : Set F}
    (hU : IsOpen U) (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 r U)
    (hleft : ∀ q, r (e q) = q) (Γ : K → regularLoop E M)
    (hΓ : Continuous[inferInstance, regularLoopTopology e he] Γ)
    (B : C(K, freeLoop F)) (hB : ∀ k, ContDiff ℝ 1 (fun t : ℝ => B k (t : loopCircle)))
    (hdB : Continuous (fun p : K × ℝ => deriv (fun t : ℝ => B p.1 (t : loopCircle)) p.2))
    (hregion : ∀ (τ : unitInterval) k θ,
      e ((Γ k).val θ) + (τ : ℝ) • (B k θ - e ((Γ k).val θ)) ∈ U) :
    ∃ H : unitInterval × K → regularLoop E M,
      Continuous[inferInstance, regularLoopTopology e he] H ∧
      (∀ τ k θ, (H (τ, k)).val θ =
        r (e ((Γ k).val θ) + (τ : ℝ) • (B k θ - e ((Γ k).val θ)))) ∧
      (∀ k, H (0, k) = Γ k) ∧
      (∀ k θ, (H (1, k)).val θ = r (B k θ)) := by
  obtain ⟨hcA, hdA⟩ := (continuous_regularLoop_iff e he Γ).mp hΓ
  let v : (unitInterval × K) × loopCircle → F := fun p =>
    e ((Γ p.1.2).val p.2) + (p.1.1 : ℝ) • (B p.1.2 p.2 - e ((Γ p.1.2).val p.2))
  have hproj : Continuous (fun p : (unitInterval × K) × loopCircle => (p.1.2, p.2)) :=
    (continuous_snd.comp continuous_fst).prodMk continuous_snd
  have hc : Continuous v := (hcA.comp hproj).add
    ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).smul
      ((B.uncurry.continuous.comp hproj).sub (hcA.comp hproj)))
  have hvU (p : (unitInterval × K) × loopCircle) : v p ∈ U := hregion p.1.1 p.1.2 p.2
  let J : C(unitInterval × K, freeLoop M) :=
    (⟨r ∘ v, hr.continuousOn.comp_continuous hc hvU⟩ :
      C((unitInterval × K) × loopCircle, M)).curry
  have hv₁ (p : unitInterval × K) : ContDiff ℝ 1 (fun t : ℝ => v (p, (t : loopCircle))) := by
    change ContDiff ℝ 1 (fun t : ℝ => e ((Γ p.2).val (t : loopCircle)) +
      (p.1 : ℝ) • (B p.2 (t : loopCircle) - e ((Γ p.2).val (t : loopCircle))))
    exact (regularLoop_embedded_contDiff e he (Γ p.2)).add
      ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (p.1 : ℝ))).smul
        ((hB p.2).sub (regularLoop_embedded_contDiff e he (Γ p.2))))
  have hJ₁ (p : unitInterval × K) :
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (fun t : ℝ => J p (t : loopCircle)) := by
    intro t
    change ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1
      (r ∘ fun s : ℝ => v (p, (s : loopCircle))) t
    exact ((hr _ (hvU (p, (t : loopCircle)))).contMDiffAt
      (hU.mem_nhds (hvU (p, (t : loopCircle))))).comp t (hv₁ p).contMDiff.contMDiffAt
  let H : unitInterval × K → regularLoop E M := fun p => ⟨J p, hJ₁ p⟩
  refine ⟨H, ?_, fun _ _ _ => rfl, ?_, ?_⟩
  · apply (continuous_regularLoop_iff e he H).mpr
    refine ⟨he.continuous.comp J.uncurry.continuous, ?_⟩
    have hcReal : Continuous (fun p : (unitInterval × K) × ℝ => v (p.1, (p.2 : loopCircle))) :=
      hc.comp (continuous_fst.prodMk ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd))
    have hdv : Continuous (fun p : (unitInterval × K) × ℝ =>
        deriv (fun t : ℝ => v (p.1, (t : loopCircle))) p.2) := by
      change Continuous (fun p : (unitInterval × K) × ℝ =>
        deriv (fun t : ℝ => e ((Γ p.1.2).val (t : loopCircle)) +
          (p.1.1 : ℝ) • (B p.1.2 (t : loopCircle) - e ((Γ p.1.2).val (t : loopCircle)))) p.2)
      exact DifferentialGeometry.Analysis.continuous_deriv_affine_family
        (f := fun p : K × ℝ => e ((Γ p.1).val (p.2 : loopCircle)))
        (g := fun p : K × ℝ => B p.1 (p.2 : loopCircle))
        (a := fun τ : unitInterval => (τ : ℝ))
        (fun k => (regularLoop_embedded_contDiff e he (Γ k)).differentiable one_ne_zero)
        (fun k => (hB k).differentiable one_ne_zero) continuous_subtype_val hdA hdB
    exact DifferentialGeometry.Analysis.continuous_deriv_family_comp hU
      (he.comp_contMDiffOn hr).contDiffOn (fun p => (hv₁ p).differentiable one_ne_zero)
      hcReal hdv (fun p => hvU (p.1, (p.2 : loopCircle)))
  · intro k
    apply Subtype.ext
    apply ContinuousMap.ext
    intro θ
    change r (e ((Γ k).val θ) + (0 : ℝ) • _) = (Γ k).val θ
    rw [zero_smul, add_zero, hleft]
  · intro k θ
    change r (e ((Γ k).val θ) + (1 : ℝ) • (B k θ - e ((Γ k).val θ))) = _
    rw [one_smul, ← add_sub_assoc, add_sub_cancel_left]

end DifferentialGeometry.Topology
