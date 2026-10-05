import DifferentialGeometry.Topology.Manifold.RegularLevel.RegularSublevelSlice

/-!
# The boundary-defining function of a regular sublevel is regular on the boundary

For a regular sublevel `{Ψ = 0, 0 ≤ B}` (`regularSublevelChartedSpace`: `dΨ` onto on the sublevel,
`d(Ψ, B)` onto on `{Ψ = 0, B = 0}`), the restriction of `B` to the sublevel has nonzero
differential at every boundary point (`regularSublevel_mfderiv_ne_zero`): the image of the
differential of the inclusion has dimension `d + 1` and would lie in `ker d(Ψ, B)`, of dimension `d`.

Lane LFR28-ROW3 (review 44, R1 item (4)): the regularity input of the polar re-modelling
`exists_diskDiffeomorph_polar_of_boundaryDefining` for the fibre of an edge disk packet.
-/

set_option autoImplicit false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Manifold.RegularLevel

section RegularSublevel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {d : ℕ}

/-- **The boundary-defining function of a regular sublevel is regular on its boundary.** On
`{Ψ = 0, 0 ≤ B}` with its regular-sublevel structure, the restriction of `B` has nonzero
differential at every boundary point `B = 0`. -/
theorem regularSublevel_mfderiv_ne_zero (hdim : Module.finrank ℝ E = d + 1 + Module.finrank ℝ G)
    {Ψ : M → G} (hΨ : ContMDiff I 𝓘(ℝ, G) ∞ Ψ) {B : M → ℝ} (hB : ContMDiff I 𝓘(ℝ, ℝ) ∞ B)
    (hreg : ∀ x, Ψ x = 0 → 0 ≤ B x → Surjective (mfderiv I 𝓘(ℝ, G) Ψ x))
    (hregb : ∀ x, Ψ x = 0 → B x = 0 →
      Surjective (mfderiv I 𝓘(ℝ, G × ℝ) (fun y => (Ψ y, B y)) x))
    (x : {x : M // Ψ x = 0 ∧ 0 ≤ B x}) (hx : B x = 0) :
    letI := regularSublevelChartedSpace hdim hΨ hB hreg hregb
    mfderiv (𝓡∂ (d + 1)) 𝓘(ℝ, ℝ) (fun y : {x : M // Ψ x = 0 ∧ 0 ≤ B x} => B y) x ≠ 0 := by
  let _ := regularSublevelChartedSpace hdim hΨ hB hreg hregb
  intro h0
  have hι : ContMDiff (𝓡∂ (d + 1)) I ∞ (Subtype.val : {x : M // Ψ x = 0 ∧ 0 ≤ B x} → M) :=
    regularSublevel_contMDiff_val hdim hΨ hB hreg hregb
  have hιd : MDifferentiableAt (𝓡∂ (d + 1)) I
      (Subtype.val : {x : M // Ψ x = 0 ∧ 0 ≤ B x} → M) x := (hι x).mdifferentiableAt (by simp)
  have hinj := regularSublevel_mfderiv_val_injective hdim hΨ hB hreg hregb x
  have hBd : MDifferentiableAt I 𝓘(ℝ, ℝ) B (x : M) := (hB (x : M)).mdifferentiableAt (by simp)
  have hΨd : MDifferentiableAt I 𝓘(ℝ, G) Ψ (x : M) := (hΨ (x : M)).mdifferentiableAt (by simp)
  have h1 : (mfderiv I 𝓘(ℝ, ℝ) B (x : M)).comp
      (mfderiv (𝓡∂ (d + 1)) I (Subtype.val : {x : M // Ψ x = 0 ∧ 0 ≤ B x} → M) x) = 0 := by
    rw [← mfderiv_comp x hBd hιd]
    exact h0
  have h2 : (mfderiv I 𝓘(ℝ, G) Ψ (x : M)).comp
      (mfderiv (𝓡∂ (d + 1)) I (Subtype.val : {x : M // Ψ x = 0 ∧ 0 ≤ B x} → M) x) = 0 := by
    rw [← mfderiv_comp x hΨd hιd]
    have hc : Ψ ∘ (Subtype.val : {x : M // Ψ x = 0 ∧ 0 ≤ B x} → M) = fun _ => (0 : G) :=
      funext fun y => y.2.1
    rw [hc]
    exact mfderiv_const
  have hP : HasMFDerivAt I 𝓘(ℝ, G × ℝ) (fun y => (Ψ y, B y)) (x : M)
      ((mfderiv I 𝓘(ℝ, G) Ψ (x : M)).prod (mfderiv I 𝓘(ℝ, ℝ) B (x : M))) :=
    ⟨hΨd.hasMFDerivAt.1.prodMk hBd.hasMFDerivAt.1, hΨd.hasMFDerivAt.2.prodMk hBd.hasMFDerivAt.2⟩
  have hsurj := hregb (x : M) x.2.1 hx
  rw [hP.mfderiv] at hsurj
  set L : E →ₗ[ℝ] G × ℝ :=
    ((mfderiv I 𝓘(ℝ, G) Ψ (x : M)).prod (mfderiv I 𝓘(ℝ, ℝ) B (x : M))).toLinearMap with hLdef
  set Dι : EuclideanSpace ℝ (Fin (d + 1)) →ₗ[ℝ] E :=
    (mfderiv (𝓡∂ (d + 1)) I (Subtype.val : {x : M // Ψ x = 0 ∧ 0 ≤ B x} → M) x).toLinearMap
    with hDιdef
  have hle : LinearMap.range Dι ≤ LinearMap.ker L := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker]
    have e1 : (mfderiv I 𝓘(ℝ, ℝ) B (x : M)) (Dι v) = 0 := ContinuousLinearMap.ext_iff.mp h1 v
    have e2 : (mfderiv I 𝓘(ℝ, G) Ψ (x : M)) (Dι v) = 0 := ContinuousLinearMap.ext_iff.mp h2 v
    change ((mfderiv I 𝓘(ℝ, G) Ψ (x : M)) (Dι v), (mfderiv I 𝓘(ℝ, ℝ) B (x : M)) (Dι v)) = 0
    rw [Prod.mk_eq_zero]
    exact ⟨e2, e1⟩
  have hrange : LinearMap.range L = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have h3 : Module.finrank ℝ (LinearMap.range Dι) = d + 1 := by
    have hinj' : Injective Dι := hinj
    rw [LinearMap.finrank_range_of_inj hinj', finrank_euclideanSpace_fin]
  have h4 := LinearMap.finrank_range_add_finrank_ker L
  rw [hrange, finrank_top, Module.finrank_prod, Module.finrank_self, hdim] at h4
  have h5 := Submodule.finrank_mono hle
  omega

end RegularSublevel

end DifferentialGeometry.Manifold.RegularLevel
