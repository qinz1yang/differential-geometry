import DifferentialGeometry.Analysis.Integration.Lp.BoundedComposition
import DifferentialGeometry.Analysis.Sobolev.Euclidean.LipschitzWitness
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.WeakLimit
import DifferentialGeometry.Analysis.Integration.Lp.QuadraticLowerSemicontinuity
import DifferentialGeometry.Analysis.Sobolev.Euclidean.DirichletEnergy.WeakLowerSemicontinuity

section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_memW1pWitness_comp_of_ae_tendsto_of_lipschitz
    {X : Type*} [TopologicalSpace X] {Ω : Set E}
    [IsFiniteMeasure (volume.restrict Ω)]
    {Φ : X → ℝ} (hΦ : Continuous Φ) {D : ℝ} (hD : ∀ p, ‖Φ p‖ ≤ D)
    (U : ℕ → E → X) (v : E → X)
    (hLip : ∀ n, ∃ K : ℝ≥0, LipschitzWith K (Φ ∘ U n))
    (hae : ∀ᵐ x ∂volume.restrict Ω,
      Tendsto (fun n => U n x) atTop (𝓝 (v x)))
    {B : ℝ} (hB : ∀ n, (∫ x in Ω, ‖fderiv ℝ (Φ ∘ U n) x‖ ^ 2) ≤ B) :
    ∃ (hs : ∀ n, DeGiorgi.MemW1pWitness 2 (Φ ∘ U n) Ω)
      (σ : ℕ → ℕ) (hv : DeGiorgi.MemW1pWitness 2 (Φ ∘ v) Ω),
      (∀ n x i, (hs n).weakGrad x i =
        fderiv ℝ (Φ ∘ U n) x (EuclideanSpace.single i 1)) ∧
      StrictMono σ ∧
      Tendsto (fun n => eLpNorm (fun x => Φ (U n x) - Φ (v x))
        2 (volume.restrict Ω)) atTop (𝓝 0) ∧
      ‖DeGiorgi.gradLpOfWitness hv‖ ≤ Real.sqrt B ∧
      (∀ z : Lp E 2 (volume.restrict Ω),
        Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hs (σ n))) z) atTop
          (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness hv) z))) ∧
      (∫ x in Ω, ‖hv.weakGrad x‖ ^ 2) ≤
        liminf (fun n => ∫ x in Ω, ‖fderiv ℝ (Φ ∘ U n) x‖ ^ 2) atTop := by
  choose K hK using hLip
  have hfm (n : ℕ) : MemLp (Φ ∘ U n) 2 (volume.restrict Ω) :=
    MemLp.of_bound (hK n).continuous.aestronglyMeasurable D
      (Eventually.of_forall fun x => hD (U n x))
  have hdfm (n : ℕ) : MemLp (fderiv ℝ (Φ ∘ U n)) 2 (volume.restrict Ω) :=
    MemLp.of_bound (measurable_fderiv ℝ (Φ ∘ U n)).aestronglyMeasurable (K n)
      (Eventually.of_forall fun x => norm_fderiv_le_of_lipschitz ℝ (hK n))
  choose hs hrep hnorm using fun n =>
    exists_memW1pWitness_fderiv_of_lipschitz (hK n) (hfm n) (hdfm n)
  have hbound (n : ℕ) : ‖DeGiorgi.gradLpOfWitness (hs n)‖ ≤ Real.sqrt B := by
    rw [DeGiorgi.gradLpOfWitness, Lp.norm_toLp, hnorm n]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (Analysis.Integration.eLpNorm_two_le_of_integral_norm_sq_le (hdfm n) (hB n))).trans_eq
      (ENNReal.toReal_ofReal (Real.sqrt_nonneg B))
  obtain ⟨hvm, hL2⟩ := MeasureTheory.memLp_and_tendsto_eLpNorm_comp_of_ae_tendsto_of_bounded
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    hΦ hD (fun n => (hfm n).aestronglyMeasurable) hae
  let q : ℕ → ℝ := fun n => ∫ x in Ω, ‖fderiv ℝ (Φ ∘ U n) x‖ ^ 2
  have hqlo : IsBoundedUnder (· ≥ ·) atTop q := by
    refine ⟨0, ?_⟩
    change ∀ᶠ n in atTop, 0 ≤ q n
    exact Eventually.of_forall fun n => integral_nonneg fun x => sq_nonneg _
  have hqhi : IsCoboundedUnder (· ≥ ·) atTop q :=
    isCoboundedUnder_ge_of_eventually_le atTop (Eventually.of_forall hB)
  obtain ⟨ρ, hρq, hρ⟩ := exists_seq_tendsto_liminf hqhi hqlo
  obtain ⟨θ, hθ, hρθ⟩ := strictMono_subseq_of_tendsto_atTop hρ
  let τ := ρ ∘ θ
  have hτ : StrictMono τ := hρθ
  have hτq : Tendsto (fun n => q (τ n)) atTop (𝓝 (liminf q atTop)) :=
    hρq.comp hθ.tendsto_atTop
  obtain ⟨ψ, hv, hψ, hvbound, hweak⟩ :=
    exists_memW1pWitness_of_tendsto_L2_norm_bounded
      (fun n => hs (τ n)) hvm (fun n => hbound (τ n)) (hL2.comp hτ.tendsto_atTop)
  let σ := τ ∘ ψ
  have hσ : StrictMono σ := hτ.comp hψ
  refine ⟨hs, σ, hv, hrep, hσ, hL2, hvbound, hweak, ?_⟩
  let Q : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
  have hdual (F : Lp E 2 (volume.restrict Ω) →L[ℝ] ℝ) :
      Tendsto (fun n => F (DeGiorgi.gradLpOfWitness (hs (σ n)))) atTop
        (𝓝 (F (DeGiorgi.gradLpOfWitness hv))) := by
    have hF (w : Lp E 2 (volume.restrict Ω)) :
        F w = inner ℝ w ((_root_.InnerProductSpace.toDual ℝ _).symm F) := by
      rw [real_inner_comm, _root_.InnerProductSpace.toDual_symm_apply]
    simpa only [hF, σ, Function.comp_apply] using
      hweak ((_root_.InnerProductSpace.toDual ℝ _).symm F)
  have hlsc := integral_quadratic_le_liminf_of_weak (μ := volume.restrict Ω)
    (fun _ _ => Q) (fun _ => Q)
    (fun _ _ _ => aestronglyMeasurable_const) (fun _ _ => aestronglyMeasurable_const)
    (fun _ => ‖Q‖) ‖Q‖ (fun _ => Eventually.of_forall fun _ => le_rfl)
    (Eventually.of_forall fun _ => le_rfl)
    (fun δ hδ => Eventually.of_forall fun _ => Eventually.of_forall fun _ => by
      have he : Q - Q = 0 := by
        ext x y
        change Q x y - Q x y = 0
        exact sub_self _
      rw [he]
      exact (ContinuousLinearMap.opNorm_zero : ‖(0 : E →L[ℝ] E →L[ℝ] ℝ)‖ = 0).le.trans hδ.le)
    (fun _ => Eventually.of_forall fun _ x => by
      change 0 ≤ inner ℝ x x
      exact real_inner_self_nonneg)
    (fun n => DeGiorgi.gradLpOfWitness (hs (σ n))) (DeGiorgi.gradLpOfWitness hv) hdual
  have hQ (w : Lp E 2 (volume.restrict Ω)) :
      (∫ x in Ω, Q (w x) (w x)) = ‖w‖ ^ 2 := by
    change inner ℝ w w = ‖w‖ ^ 2
    exact real_inner_self_eq_norm_sq w
  have henergy (n : ℕ) : ‖DeGiorgi.gradLpOfWitness (hs n)‖ ^ 2 = q n := by
    rw [DeGiorgi.gradLpOfWitness, Lp.norm_toLp, hnorm n]
    simpa only [q, eLpNorm_norm] using
      (Analysis.Integration.integral_sq_eq_l2 (hdfm n).norm).symm
  simp only [hQ, henergy] at hlsc
  have hσq : Tendsto (fun n => q (σ n)) atTop (𝓝 (liminf q atTop)) := by
    simpa only [σ, Function.comp_def] using hτq.comp hψ.tendsto_atTop
  rw [hσq.liminf_eq] at hlsc
  rw [norm_gradLpOfWitness_sq_eq_integral] at hlsc
  exact hlsc

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

end
