import DifferentialGeometry.Topology.LoopSpace.SmoothingC1
import DifferentialGeometry.Analysis.Calculus.Compactness.Superposition
import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.Families










noncomputable section

open Set Function ContinuousMap Manifold
open scoped Topology ContDiff

namespace DifferentialGeometry.Topology

variable {K F G : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]



theorem smoothPeriodic_uniform_C1_superposition (Γ : C(K, freeLoop F))
    (hΓ : ∀ k, ContDiff ℝ 1 (fun t : ℝ => Γ k (t : loopCircle)))
    (hd : Continuous (fun p : K × ℝ => deriv (fun t : ℝ => Γ p.1 (t : loopCircle)) p.2))
    {g : F → G} {U : Set F} (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U)
    (hmap : ∀ k θ, Γ k θ ∈ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ φ : ContDiffBump (0 : ℝ), φ.rOut < δ → ∀ k t,
      DifferentialGeometry.Analysis.smoothPeriodic φ (fun s : ℝ => Γ k (s : loopCircle)) t ∈ U ∧
      dist (g (DifferentialGeometry.Analysis.smoothPeriodic φ (fun s : ℝ => Γ k (s : loopCircle)) t))
        (g (Γ k (t : loopCircle))) < ε ∧
      dist (deriv (fun x => g (DifferentialGeometry.Analysis.smoothPeriodic φ
          (fun s : ℝ => Γ k (s : loopCircle)) x)) t)
        (deriv (fun s : ℝ => g (Γ k (s : loopCircle))) t) < ε := by
  let D : K → freeLoop F := fun k => regularLoopDerivative (id : F → F) contMDiff_id
    ⟨Γ k, (hΓ k).contMDiff⟩
  have hD : Continuous D := continuous_periodicLoop_family hd _
  let c : K × loopCircle → F × F := fun p => (Γ p.1 p.2, D p.1 p.2)
  have hc : Continuous c := Γ.uncurry.continuous.prodMk
    ((FreeLoop.continuous_family_iff D).mp hD)
  let J : F × F → G × G := fun p => (g p.1, fderiv ℝ g p.1 p.2)
  have hJU : ContinuousOn J (U ×ˢ univ) := by
    have h₀ : ContinuousOn (fun p : F × F => g p.1) (U ×ˢ univ) :=
      hg.continuousOn.comp continuous_fst.continuousOn (fun p hp => hp.1)
    have h₁ : ContinuousOn (fun p : F × F => fderiv ℝ g p.1) (U ×ˢ univ) :=
      (hg.continuousOn_fderiv_of_isOpen hU le_rfl).comp
      continuous_fst.continuousOn (fun p hp => hp.1)
    exact h₀.prodMk (h₁.clm_apply continuous_snd.continuousOn)
  have hcU : range c ⊆ U ×ˢ univ := by
    rintro _ ⟨p, rfl⟩
    exact ⟨hmap p.1 p.2, mem_univ _⟩
  obtain ⟨a, ha, haJ⟩ := DifferentialGeometry.Analysis.exists_uniform_superposition_radius
    hc (hU.prod isOpen_univ) hcU hJU hε
  obtain ⟨δ, hδ, hδΓ⟩ := smoothPeriodic_uniform_C1_approximation Γ hΓ hd ha
  refine ⟨δ, hδ, fun φ hφ k t => ?_⟩
  let b := DifferentialGeometry.Analysis.smoothPeriodic φ (fun s : ℝ => Γ k (s : loopCircle))
  have hbt := hδΓ φ hφ k t
  have hpair : dist (b t, deriv b t) (c (k, (t : loopCircle))) < a := by
    exact max_lt hbt.1 hbt.2
  obtain ⟨hbU, hJ⟩ := haJ (k, (t : loopCircle)) (b t, deriv b t) hpair
  have hb : ContDiff ℝ ∞ b := DifferentialGeometry.Analysis.smoothPeriodic_contDiff φ
    ((Γ k).continuous.comp (AddCircle.continuous_mk' (1 : ℝ)))
  have hgb := ((hg _ hbU.1).contDiffAt (hU.mem_nhds hbU.1)).differentiableAt one_ne_zero
  have hgo := ((hg _ (hmap k (t : loopCircle))).contDiffAt
    (hU.mem_nhds (hmap k (t : loopCircle)))).differentiableAt one_ne_zero
  have hdnew : deriv (fun x => g (b x)) t = fderiv ℝ g (b t) (deriv b t) :=
    (hgb.hasFDerivAt.comp_hasDerivAt t ((hb.differentiable (by simp)) t).hasDerivAt).deriv
  have hdold : deriv (fun s : ℝ => g (Γ k (s : loopCircle))) t =
      fderiv ℝ g (Γ k (t : loopCircle)) (deriv (fun s : ℝ => Γ k (s : loopCircle)) t) :=
    (hgo.hasFDerivAt.comp_hasDerivAt t ((hΓ k).differentiable one_ne_zero t).hasDerivAt).deriv
  change max (dist (g (b t)) (g (Γ k (t : loopCircle))))
    (dist (fderiv ℝ g (b t) (deriv b t))
      (fderiv ℝ g (Γ k (t : loopCircle)) (deriv (fun s : ℝ => Γ k (s : loopCircle)) t))) < ε at hJ
  refine ⟨hbU.1, (max_lt_iff.mp hJ).1, ?_⟩
  rw [hdnew, hdold]
  exact (max_lt_iff.mp hJ).2

end DifferentialGeometry.Topology
