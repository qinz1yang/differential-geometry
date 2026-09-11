import DifferentialGeometry.Geometry.Comparison.Busemann.Support.SmoothDistanceLaplacian

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Topology

section CompactPerturbation

variable {X : Type*} [TopologicalSpace X]

theorem exists_pos_perturbation_lt_on_compact
    {K : Set X} (hK : IsCompact K) {f h : X → ℝ} {m : ℝ}
    (hf : ContinuousOn f K) (hh : ContinuousOn h K)
    (hf_le : ∀ x ∈ K, f x ≤ m)
    (hnegative : ∀ x ∈ K, f x = m → h x < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, f x + δ * h x < m := by
  let S : Set X := {x ∈ K | 0 ≤ h x}
  have hS : IsCompact S := by
    let : CompactSpace K := isCompact_iff_compactSpace.mp hK
    have hclosed : IsClosed {x : K | 0 ≤ h x} :=
      isClosed_le continuous_const hh.domRestrict
    have himage := hclosed.isCompact.image continuous_subtype_val
    convert himage using 1
    ext x
    simp [S, and_comm]
  by_cases hne : S.Nonempty
  · obtain ⟨z, hz, hmax⟩ := hS.exists_isMaxOn hne (hf.mono fun _ hx => hx.1)
    have hgap : 0 < m - f z := by
      apply sub_pos.mpr
      refine lt_of_le_of_ne (hf_le z hz.1) ?_
      intro heq
      exact not_lt_of_ge hz.2 (hnegative z hz.1 heq)
    obtain ⟨B, hB⟩ := hK.bddAbove_image hh
    let C : ℝ := max B 0 + 1
    have hC : 0 < C := add_pos_of_nonneg_of_pos (le_max_right B 0) zero_lt_one
    let δ : ℝ := (m - f z) / C
    have hδ : 0 < δ := div_pos hgap hC
    have hδC : δ * C = m - f z := div_mul_cancel₀ _ hC.ne'
    refine ⟨δ, hδ, fun x hx => ?_⟩
    by_cases hhx : 0 ≤ h x
    · have hfx : f x ≤ f z := hmax ⟨hx, hhx⟩
      have hxB : h x ≤ B := hB (mem_image_of_mem h hx)
      have hxC : h x < C := by
        dsimp only [C]
        linarith [le_max_left B 0]
      have hsmall := mul_lt_mul_of_pos_left hxC hδ
      linarith
    · have hprod : δ * h x < 0 := mul_neg_of_pos_of_neg hδ (lt_of_not_ge hhx)
      linarith [hf_le x hx]
  · refine ⟨1, zero_lt_one, fun x hx => ?_⟩
    have hhx : h x < 0 := by
      by_contra hbad
      exact hne ⟨x, hx, le_of_not_gt hbad⟩
    linarith [hf_le x hx]


theorem exists_interior_max_of_boundary_perturbation
    {K : Set X} (hK : IsCompact K) {p : X} (hp : p ∈ interior K)
    {f h : X → ℝ} (hf : ContinuousOn f K) (hh : ContinuousOn h K)
    (hmax : ∀ x ∈ K, f x ≤ f p) (hzero : h p = 0)
    (hnegative : ∀ x ∈ K \ interior K, f x = f p → h x < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ z ∈ interior K,
      IsMaxOn (fun x => f x + δ * h x) K z := by
  obtain ⟨δ, hδ, hboundary⟩ := exists_pos_perturbation_lt_on_compact
    (hK.diff isOpen_interior) (hf.mono sdiff_subset) (hh.mono sdiff_subset)
    (fun x hx => hmax x hx.1) hnegative
  have hpK : p ∈ K := interior_subset hp
  have hcont : ContinuousOn (fun x => f x + δ * h x) K :=
    hf.add (continuousOn_const.mul hh)
  obtain ⟨z, hz, hzmax⟩ := hK.exists_isMaxOn ⟨p, hpK⟩ hcont
  have hzint : z ∈ interior K := by
    by_contra hznot
    have hlt := hboundary z ⟨hz, hznot⟩
    have hge := hzmax hpK
    change f p + δ * h p ≤ f z + δ * h z at hge
    rw [hzero, mul_zero, add_zero] at hge
    exact not_lt_of_ge hge hlt
  exact ⟨δ, hδ, z, hzint, hzmax⟩

end CompactPerturbation

section LocalLaplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

omit [FiniteDimensional ℝ E] in
private theorem eventually_mdifferentiable_of_smooth {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f x) :
    ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) f y := by
  have h : ∀ᶠ y in 𝓝 x, ContMDiffAt I 𝓘(ℝ, ℝ) 1 f y :=
    (contMDiffAt_iff_contMDiffAt_nhds (by decide)).mp (hf.of_le (by simp))
  exact h.mono fun _ hy => hy.mdifferentiableAt (by simp)

private theorem laplacian_neg_of_contMDiffAt
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f x) :
    laplacian (I := I) (LeviCivita (I := I) g) g (fun y => -f y) x =
      -laplacian (I := I) (LeviCivita (I := I) g) g f x := by
  have h := laplacian_smul_at (I := I) (LeviCivita (I := I) g) g (-1 : ℝ)
    (eventually_mdifferentiable_of_smooth hf)
    ((gradientFun_contMDiffAt (I := I) g hf).mdifferentiableAt (by simp))
  have heq : (-1 : ℝ) • f = fun y => -f y := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, neg_one_mul]
  rw [heq, neg_one_mul] at h
  exact h

private theorem laplacian_add_of_contMDiffAt
    (g : SmoothRiemannianMetric I M) {f h : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f x)
    (hh : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ h x) :
    laplacian (I := I) (LeviCivita (I := I) g) g (fun y => f y + h y) x =
      laplacian (I := I) (LeviCivita (I := I) g) g f x +
        laplacian (I := I) (LeviCivita (I := I) g) g h x := by
  have hsub := laplacian_sub_of_contMDiffAt (I := I)
    (LeviCivita (I := I) g) g hf hh.neg
  rw [laplacian_neg_of_contMDiffAt (I := I) g hh] at hsub
  simpa only [sub_neg_eq_add] using hsub

theorem false_of_positive_laplacian_boundary_perturbation [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {K : Set M} (hK : IsCompact K) {p : M} (hp : p ∈ interior K)
    {f h : M → ℝ} (hf : ContinuousOn f K)
    (hh : ∀ x ∈ K, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ h x)
    (hmax : ∀ x ∈ K, f x ≤ f p) (hzero : h p = 0)
    (hnegative : ∀ x ∈ K \ interior K, f x = f p → h x < 0)
    (hlap : ∀ x ∈ interior K,
      0 < laplacian (I := I) (LeviCivita (I := I) g) g h x)
    (hsupport : ∀ x ∈ interior K, ∀ ε : ℝ, 0 < ε → ∃ φ : M → ℝ,
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ φ x ∧ φ x = f x ∧
        (∀ᶠ y in 𝓝 x, φ y ≤ f y) ∧
        -ε < laplacian (I := I) (LeviCivita (I := I) g) g φ x) : False := by
  have hhcont : ContinuousOn h K := fun x hx => (hh x hx).continuousAt.continuousWithinAt
  obtain ⟨δ, hδ, z, hz, hpertmax⟩ := exists_interior_max_of_boundary_perturbation
    hK hp hf hhcont hmax hzero hnegative
  let L : ℝ := laplacian (I := I) (LeviCivita (I := I) g) g h z
  have hL : 0 < L := hlap z hz
  have hε : 0 < δ * L / 2 := div_pos (mul_pos hδ hL) (by norm_num)
  obtain ⟨φ, hφ, hcontact, hbelow, hφlap⟩ := hsupport z hz (δ * L / 2) hε
  have hhz := hh z (interior_subset hz)
  have hscaled : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => δ * h y) z :=
    contMDiffAt_const.mul hhz
  have hlocal := hpertmax.isLocalMax (mem_interior_iff_mem_nhds.mp hz)
  have hψmax : IsLocalMax (fun y => φ y + δ * h y) z := by
    filter_upwards [hbelow, hlocal] with y hy hmaxy
    change φ y + δ * h y ≤ φ z + δ * h z
    rw [hcontact]
    linarith
  have hnonpos := laplacian_le_of_smooth_upper_support (I := I) g
    (hφ.add hscaled) contMDiffAt_const rfl hψmax
  rw [laplacian_const] at hnonpos
  change laplacian (I := I) (LeviCivita (I := I) g) g
    (fun y => φ y + δ * h y) z ≤ 0 at hnonpos
  rw [laplacian_add_of_contMDiffAt (I := I) g hφ hscaled] at hnonpos
  have hscale := laplacian_smul_at (I := I) (LeviCivita (I := I) g) g δ
    (eventually_mdifferentiable_of_smooth hhz)
    ((gradientFun_contMDiffAt (I := I) g hhz).mdifferentiableAt (by simp))
  change laplacian (I := I) (LeviCivita (I := I) g) g (fun y => δ * h y) z = δ * L at hscale
  rw [hscale] at hnonpos
  linarith

end LocalLaplacian

end DifferentialGeometry.Geometry.Topology

end
