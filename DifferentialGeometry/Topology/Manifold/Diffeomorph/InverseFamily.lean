import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.ManifoldDerivative

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem isLocalDiffeomorphOn_diffeomorph_family
    (Ψ : ℝ → (M ≃ₘ⟮I, I⟯ M)) {U : Set ℝ} (hU : IsOpen U)
    (hΨ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => Ψ q.1 q.2) (U ×ˢ univ)) :
    IsLocalDiffeomorphOn (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun q : ℝ × M => (q.1, Ψ q.1 q.2)) (U ×ˢ univ) := by
  let F : ℝ × M → ℝ × M := fun q => (q.1, Ψ q.1 q.2)
  have hF : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞ F
      (U ×ˢ univ) := contMDiffOn_fst.prodMk hΨ
  apply hF.isLocalDiffeomorphOn_of_isInvertible_mfderiv (hU.prod isOpen_univ) (by simp)
  intro p hp
  have hd : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) I
      (fun q : ℝ × M => Ψ q.1 q.2) p :=
    (hΨ.contMDiffAt ((hU.prod isOpen_univ).mem_nhds hp)).mdifferentiableAt (by simp)
  let A := (Ψ p.1).mfderivToContinuousLinearEquiv (by simp) p.2
  let B := mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => Ψ s p.2) p.1
  let L := (ContinuousLinearEquiv.refl ℝ ℝ).skewProd A B
  refine ⟨L, ?_⟩
  ext v
  rw [mfderiv_prodMk mdifferentiableAt_fst hd, mfderiv_fst]
  change (v.1, A v.2 + B v.1) = (v.1, mfderiv (𝓘(ℝ, ℝ).prod I) I
    (fun q : ℝ × M => Ψ q.1 q.2) p v)
  congr 1
  rw [mfderiv_prod_eq_add_apply hd, add_comm]
  rfl

theorem contMDiffOn_diffeomorph_family_symm
    (Ψ : ℝ → (M ≃ₘ⟮I, I⟯ M)) {U : Set ℝ} (hU : IsOpen U)
    (hΨ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => Ψ q.1 q.2) (U ×ˢ univ)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (Ψ q.1).symm q.2) (U ×ˢ univ) := by
  let F : ℝ × M → ℝ × M := fun q => (q.1, Ψ q.1 q.2)
  let G : ℝ × M → ℝ × M := fun q => (q.1, (Ψ q.1).symm q.2)
  have hlocal := isLocalDiffeomorphOn_diffeomorph_family Ψ hU hΨ
  have hinj : Function.Injective F := by
    rintro ⟨s, x⟩ ⟨t, y⟩ h
    have hst : s = t := congrArg Prod.fst h
    subst t
    have hxy : Ψ s x = Ψ s y := congrArg Prod.snd h
    exact Prod.ext rfl ((Ψ s).injective hxy)
  have hFG : ∀ q, F (G q) = q := by
    rintro ⟨s, x⟩
    exact Prod.ext rfl ((Ψ s).apply_symm_apply x)
  intro q hq
  have hGq : G q ∈ U ×ˢ (univ : Set M) := ⟨hq.1, mem_univ _⟩
  let hloc : IsLocalDiffeomorphAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞ F (G q) :=
    hlocal ⟨G q, hGq⟩
  have hsource : q ∈ hloc.localInverse.source := by
    simpa only [hFG q] using hloc.localInverse_mem_source
  have heq : G =ᶠ[𝓝 q] hloc.localInverse := by
    filter_upwards [hloc.localInverse_open_source.mem_nhds hsource] with r hr
    apply hinj
    rw [hFG r, hloc.localInverse_right_inv hr]
  have hi : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      hloc.localInverse q := by
    simpa only [hFG q] using hloc.localInverse_contMDiffAt
  exact (contMDiffAt_snd.comp q (hi.congr_of_eventuallyEq heq)).contMDiffWithinAt

end DifferentialGeometry.Topology.Manifold
