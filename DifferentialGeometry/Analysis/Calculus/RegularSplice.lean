import DifferentialGeometry.Analysis.Calculus.CutoffPerturbation

set_option autoImplicit false
noncomputable section
open Set Metric Filter Function
open scoped Topology ContDiff
namespace Poincare.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


def splice (f g : E → E) (ρ : E → ℝ) (x : E) : E :=
  f x + ρ x • (g x - f x)


theorem fderiv_splice_of_eq_zero {f g : E → E} {ρ : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hρ : DifferentiableAt ℝ ρ x) (hn : ∀ᶠ y in 𝓝 x, 0 ≤ ρ y) (hz : ρ x = 0) :
    fderiv ℝ (splice f g ρ) x = fderiv ℝ f x := by
  have hm : IsLocalMin ρ x := by simpa only [IsLocalMin, IsMinFilter, hz] using hn
  simpa [splice, hz, hm.fderiv_eq_zero] using!
    (hf.hasFDerivAt.add (hρ.hasFDerivAt.smul (hg.hasFDerivAt.sub hf.hasFDerivAt))).fderiv


theorem fderiv_splice_of_eq_one {f g : E → E} {ρ : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hρ : DifferentiableAt ℝ ρ x) (hn : ∀ᶠ y in 𝓝 x, ρ y ≤ 1) (hz : ρ x = 1) :
    fderiv ℝ (splice f g ρ) x = fderiv ℝ g x := by
  have hm : IsLocalMax ρ x := by simpa only [IsLocalMax, IsMaxFilter, hz] using hn
  simpa [splice, hz, hm.fderiv_eq_zero] using!
    (hf.hasFDerivAt.add (hρ.hasFDerivAt.smul (hg.hasFDerivAt.sub hf.hasFDerivAt))).fderiv

variable [FiniteDimensional ℝ E]

theorem exists_regular_ball_splice {f g : E → E} (a : E) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) {U P : Set E} (hU : IsOpen U)
    (hRU : closedBall a R ⊆ U) (hP : IsClosed P)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hfreg : ∀ x ∈ U, f x = 0 → (fderiv ℝ f x).det ≠ 0)
    (hgreg : ∀ x ∈ U, g x = 0 → (fderiv ℝ g x).det ≠ 0)
    (hagree : ∀ x ∈ P ∩ U, f =ᶠ[𝓝 x] g) :
    ∃ G : E → E, ContDiffOn ℝ ∞ G U ∧ EqOn G g (closedBall a r) ∧
      EqOn G f (ball a R)ᶜ ∧ EqOn G f (P ∩ U) ∧
      (∀ x ∈ U, G x = 0 → (fderiv ℝ G x).det ≠ 0) ∧
      {x | x ∈ closedBall a R ∧ G x = 0}.Finite := by
  let ρ : ContDiffBump a := ⟨r, R, hr, hrR⟩
  let F := splice f g ρ
  let Ω := ball a R \ (P ∪ closedBall a r)
  have hΩ : IsOpen Ω := isOpen_ball.sdiff (hP.union isClosed_closedBall)
  have hF : ContDiffOn ℝ ∞ F U := hf.add (ρ.contDiff.contDiffOn.smul (hg.sub hf))
  have hfixed : ∀ x ∈ U, x ∉ Ω → F x = 0 → (fderiv ℝ F x).det ≠ 0 := by
    intro x hx hxo hz
    have hfd := (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    have hgd := (hg.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    have hρd : DifferentiableAt ℝ (ρ : E → ℝ) x :=
      (ρ.contDiff (n := (⊤ : ℕ∞))).contDiffAt.differentiableAt (by simp)
    by_cases hxp : x ∈ P
    · have he : F =ᶠ[𝓝 x] f := by
        filter_upwards [hagree x ⟨hxp, hx⟩] with y hy
        simp [F, splice, hy]
      rw [he.fderiv_eq]
      exact hfreg x hx (he.self_of_nhds.symm.trans hz)
    · by_cases hxr : x ∈ closedBall a r
      · have hρx : ρ x = 1 := ρ.one_of_mem_closedBall hxr
        rw [fderiv_splice_of_eq_one hfd hgd hρd
          (Eventually.of_forall (fun _ => ρ.le_one)) hρx]
        exact hgreg x hx (by simpa [F, splice, hρx] using hz)
      · have hxR : x ∉ ball a R := fun h => hxo ⟨h, fun hh => hh.elim hxp hxr⟩
        have hρx : ρ x = 0 := ρ.zero_of_le_dist (not_lt.mp hxR)
        rw [fderiv_splice_of_eq_zero hfd hgd hρd
          (Eventually.of_forall (fun _ => ρ.nonneg)) hρx]
        exact hfreg x hx (by simpa [F, splice, hρx] using hz)
  obtain ⟨G, hG, _, heq, _, hreg⟩ :=
    exists_small_regular_perturbation_fixed hU hΩ hF hfixed zero_lt_one
  refine ⟨G, hG, ?_, ?_, ?_, hreg, ?_⟩
  · intro x hx
    rw [heq (fun h => h.2 (Or.inr hx))]
    simp [F, splice, ρ.one_of_mem_closedBall hx]
  · intro x hx
    rw [heq (fun h => hx h.1)]
    simp [F, splice, ρ.zero_of_le_dist (not_lt.mp hx)]
  · intro x hx
    rw [heq (fun h => h.2 (Or.inl hx.1))]
    simp [F, splice, (hagree x hx).self_of_nhds]
  · exact finite_regular_fiber (isCompact_closedBall a R)
      (fun x hx => (hG.contDiffAt (hU.mem_nhds (hRU hx))).of_le (by simp)) 0
      (fun x hx => hreg x (hRU hx))

theorem exists_regular_ball_splice_preserving_germs {f g : E → E} (a : E) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) {U A : Set E} (hU : IsOpen U)
    (hRU : closedBall a R ⊆ U) (hA : IsCompact A) (hAU : A ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hfreg : ∀ x ∈ U, f x = 0 → (fderiv ℝ f x).det ≠ 0)
    (hgreg : ∀ x ∈ U, g x = 0 → (fderiv ℝ g x).det ≠ 0)
    (hagree : ∀ x ∈ A, f =ᶠ[𝓝 x] g) :
    ∃ G : E → E, ContDiffOn ℝ ∞ G U ∧ EqOn G g (closedBall a r) ∧
      EqOn G f (ball a R)ᶜ ∧ (∀ x ∈ A, G =ᶠ[𝓝 x] f) ∧
      (∀ x ∈ U, G x = 0 → (fderiv ℝ G x).det ≠ 0) ∧
      {x | x ∈ closedBall a R ∧ G x = 0}.Finite := by
  let O := U ∩ {x | f =ᶠ[𝓝 x] g}
  have hO : IsOpen O := hU.inter isOpen_setOfPred_eventually_nhds
  have hAO : A ⊆ O := fun x hx => ⟨hAU hx, hagree x hx⟩
  obtain ⟨Q, hQ, hAQ, hQO⟩ := hA.exists_isOpen_closure_subset (hO.mem_nhdsSet.mpr hAO)
  obtain ⟨G, hG, hinner, houter, hfixed, hreg, hfinite⟩ :=
    exists_regular_ball_splice a hr hrR hU hRU isClosed_closure hf hg hfreg hgreg
      (fun x hx => (hQO hx.1).2)
  refine ⟨G, hG, hinner, houter, ?_, hreg, hfinite⟩
  intro x hx
  filter_upwards [hQ.mem_nhds (hAQ hx)] with y hy
  exact hfixed ⟨subset_closure hy, (hQO (subset_closure hy)).1⟩

end Poincare.Calculus
