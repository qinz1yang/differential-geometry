import DifferentialGeometry.Topology.Handle.SphereChartSign
import DifferentialGeometry.Topology.Handle.BallPairExtension
import DifferentialGeometry.Topology.Diffeomorph.SphereIsotopy

/-!
# Two boundary disks of the unit ball of `ℝ³`

Chapter-14 assembly, item L1 (lane ASM-L1), group G2: the exact two-disk normalization of route A
(design `docs/geometrization/chapter14/design-fc39-fc42-assembly-20261004.md` §3 "L1", step 2, as
corrected by review item 2: two disks, orientation signs, simultaneous extension relative to the
first disk).

`exists_diffeomorph_closedBall_eqOn_two_boundary_disks`: two germs `F₀`, `F₁` of partial
diffeomorphisms of `ℝ³`, defined near two disjoint disks of the unit sphere, each mapping the sphere
to itself and the closed ball into itself, with Jacobians of the same sign, are realized near the
two disks by ONE diffeomorphism `Q` of `ℝ³` preserving the closed unit ball. The first disk contains
a closed round cap `{a ≤ ⟪θ, p₀⟫}`, near which `Q = F₀`; near any compact part `K₁` of the second
disk, `Q = F₁`.

Route:
1. `Q₀` (tree, one disk): `PartialDiffeomorph.exists_diffeomorph_eqOn_of_boundary_disk_chart`;
2. `F₁' = Q₀⁻¹ ∘ F₁` is a sphere germ with positive Jacobian, and its sphere chart `ψ₁ = F₁' ∘ φ₁`
   has the orientation of `φ₁` in the stereographic chart from `p₀` (`det_stereoChart_comp_mul_pos`);
3. a sphere isotopy fixing a neighbourhood of the cap moves `φ₁` to `ψ₁`
   (`exists_sphere_isotopy_eqOn_disk_off_cap`), extended radially to `C₁`
   (`Diffeomorph.exists_isotopy_extension_sphere_product_collar`);
4. the remaining collar germ `C₁⁻¹ ∘ F₁'` fixes the sphere near the second disk and is realized by a
   ball-preserving isotopy supported in a half-space away from the cap
   (`PartialDiffeomorph.exists_contDiff_compact_isotopy_eqOn_neighborhood_of_eqOn_sphere`);
5. `Q = Q₀ ∘ C₁ ∘ Φ 1`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Function
open scoped ContDiff Manifold InnerProductSpace Topology

namespace DifferentialGeometry.Topology.Handle

local instance fact_finrank_three_ASML1B :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

/-- A homeomorphism of `ℝ³` preserving the closed unit ball preserves the unit sphere. -/
theorem image_unitSphere_of_image_closedBall (Q : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3))
    (hQ : Q '' closedBall 0 1 = closedBall 0 1) : Q '' sphere 0 1 = sphere 0 1 := by
  rw [← frontier_closedBall (0 : EuclideanSpace ℝ (Fin 3)) one_ne_zero, Q.image_frontier, hQ]

/-- The Jacobian of a global diffeomorphism of `ℝ³` has constant sign. -/
theorem det_fderiv_diffeomorph_pos_iff {Q : EuclideanSpace ℝ (Fin 3) ≃ₘ[ℝ]
    EuclideanSpace ℝ (Fin 3)} (x y : EuclideanSpace ℝ (Fin 3)) :
    0 < (fderiv ℝ Q x).det ↔ 0 < (fderiv ℝ Q y).det :=
  DifferentialGeometry.Analysis.det_fderiv_pos_iff_of_preconnected Q.toPartialDiffeomorph
    (by
      change IsPreconnected (univ : Set (EuclideanSpace ℝ (Fin 3)))
      exact isPreconnected_univ)
    (mem_univ x) (mem_univ y)

/-- The Jacobian of the inverse of a global diffeomorphism. -/
theorem det_fderiv_symm_mul (Q : EuclideanSpace ℝ (Fin 3) ≃ₘ[ℝ] EuclideanSpace ℝ (Fin 3))
    (z : EuclideanSpace ℝ (Fin 3)) :
    (fderiv ℝ Q.symm z).det * (fderiv ℝ Q (Q.symm z)).det = 1 := by
  have hQ : HasFDerivAt Q (fderiv ℝ Q (Q.symm z)) (Q.symm z) :=
    ((Q.contMDiff.contDiff.differentiable (by simp)) _).hasFDerivAt
  have hQs : HasFDerivAt Q.symm (fderiv ℝ Q.symm z) z :=
    ((Q.symm.contMDiff.contDiff.differentiable (by simp)) _).hasFDerivAt
  have hcomp : HasFDerivAt (fun w => Q (Q.symm w)) ((fderiv ℝ Q (Q.symm z)).comp
      (fderiv ℝ Q.symm z)) z := hQ.comp z hQs
  have hid : (fun w => Q (Q.symm w)) = id := funext fun w => Q.apply_symm_apply w
  rw [hid] at hcomp
  have h : (fderiv ℝ Q (Q.symm z)).comp (fderiv ℝ Q.symm z) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) := hcomp.unique (hasFDerivAt_id z)
  have hdet : ((fderiv ℝ Q (Q.symm z) : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) ∘ₗ
      (fderiv ℝ Q.symm z : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3))).det = 1 := by
    change (((fderiv ℝ Q (Q.symm z)).comp (fderiv ℝ Q.symm z) :
      EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)).det = 1
    rw [h]
    exact LinearMap.det_id
  rw [LinearMap.det_comp] at hdet
  change (fderiv ℝ Q.symm z : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)).det *
    (fderiv ℝ Q (Q.symm z) : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)).det = 1
  rw [mul_comm]
  exact hdet

/-- **Two boundary disks of the unit ball (route A, exact normalization).** Germs `F₀`, `F₁` of
`ℝ³` near two disjoint disks of the unit sphere (disk charts `φ₀`, `φ₁` on `closedBall 0 R`), each
mapping the sphere to itself and the closed ball into itself, with Jacobians of the same sign: one
diffeomorphism `Q` of `ℝ³` with `Q (closedBall 0 1) = closedBall 0 1` agrees with `F₀` on a
neighbourhood of the round cap `{a ≤ ⟪θ, p₀⟫} ⊆ φ₀ (ball 0 R)` and with `F₁` on a neighbourhood
of a compact `K₁ ⊆ φ₁ (ball 0 R)`. The second disk avoids the cap, and its `F₁`-image avoids the
`F₀`-image of the cap. -/
theorem exists_diffeomorph_closedBall_eqOn_two_boundary_disks
    (F₀ F₁ : PartialDiffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3))
      (EuclideanSpace ℝ (Fin 3)) ∞)
    (φ₀ φ₁ : PartialDiffeomorph (𝓡 2) (𝓡 2) (EuclideanSpace ℝ (Fin 2))
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)
    {R : ℝ} (hR : 0 < R) (hφ₀ : closedBall 0 R ⊆ φ₀.source) (hφ₁ : closedBall 0 R ⊆ φ₁.source)
    (hF₀ : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) R,
      (φ₀ x : EuclideanSpace ℝ (Fin 3)) ∈ F₀.source)
    (hF₁ : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) R,
      (φ₁ x : EuclideanSpace ℝ (Fin 3)) ∈ F₁.source)
    (hbd₀ : MapsTo F₀ (sphere 0 1 ∩ F₀.source) (sphere 0 1))
    (hbd₁ : MapsTo F₁ (sphere 0 1 ∩ F₁.source) (sphere 0 1))
    (hside₀ : MapsTo F₀ (closedBall 0 1 ∩ F₀.source) (closedBall 0 1))
    (hside₁ : MapsTo F₁ (closedBall 0 1 ∩ F₁.source) (closedBall 0 1))
    (p₀ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) {a : ℝ} (ha : -1 < a) (ha' : a < 1)
    (hcap : {θ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 |
      a ≤ ⟪(θ : EuclideanSpace ℝ (Fin 3)), (p₀ : EuclideanSpace ℝ (Fin 3))⟫_ℝ} ⊆ φ₀ '' ball 0 R)
    (hφ₁cap : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) R,
      ⟪(φ₁ x : EuclideanSpace ℝ (Fin 3)), (p₀ : EuclideanSpace ℝ (Fin 3))⟫_ℝ < a)
    (hdisj : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) R,
      ∀ θ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        a ≤ ⟪(θ : EuclideanSpace ℝ (Fin 3)), (p₀ : EuclideanSpace ℝ (Fin 3))⟫_ℝ →
          F₁ (φ₁ x : EuclideanSpace ℝ (Fin 3)) ≠ F₀ (θ : EuclideanSpace ℝ (Fin 3)))
    (hori : 0 < (fderiv ℝ F₀ (p₀ : EuclideanSpace ℝ (Fin 3))).det *
      (fderiv ℝ F₁ (φ₁ 0 : EuclideanSpace ℝ (Fin 3))).det)
    {K₁ : Set (EuclideanSpace ℝ (Fin 3))} (hK₁ : IsCompact K₁)
    (hK₁φ : K₁ ⊆ Subtype.val '' (φ₁ '' ball 0 R)) :
    ∃ Q : EuclideanSpace ℝ (Fin 3) ≃ₘ[ℝ] EuclideanSpace ℝ (Fin 3),
      Q '' closedBall 0 1 = closedBall 0 1 ∧
      (∃ V₀ : Set (EuclideanSpace ℝ (Fin 3)), IsOpen V₀ ∧
        Subtype.val '' {θ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 |
          a ≤ ⟪(θ : EuclideanSpace ℝ (Fin 3)), (p₀ : EuclideanSpace ℝ (Fin 3))⟫_ℝ} ⊆ V₀ ∧
        V₀ ⊆ F₀.source ∧ EqOn Q F₀ V₀) ∧
      (∃ V₁ : Set (EuclideanSpace ℝ (Fin 3)), IsOpen V₁ ∧ K₁ ⊆ V₁ ∧ V₁ ⊆ F₁.source ∧
        EqOn Q F₁ V₁) := by
  classical
  let E3 := EuclideanSpace ℝ (Fin 3)
  let S := sphere (0 : E3) 1
  -- the cap and the first disk (tree, one disk)
  let σ : Set S := {θ | a ≤ ⟪(θ : E3), (p₀ : E3)⟫_ℝ}
  have hσclosed : IsClosed σ :=
    isClosed_le continuous_const (continuous_subtype_val.inner continuous_const)
  have hKσc : IsCompact (Subtype.val '' σ) :=
    hσclosed.isCompact.image continuous_subtype_val
  have hKσφ : Subtype.val '' σ ⊆ Subtype.val '' (φ₀ '' ball 0 R) := image_mono hcap
  obtain ⟨Q₀, hQ₀ball, V₀, hV₀, hKV₀, hV₀F, hQ₀F⟩ :=
    PartialDiffeomorph.exists_diffeomorph_eqOn_of_boundary_disk_chart 1 F₀ φ₀ hR hφ₀ hF₀ hbd₀
      hside₀ hKσc hKσφ
  have hpp : ⟪(p₀ : E3), (p₀ : E3)⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p₀]
    norm_num
  have hp₀σ : p₀ ∈ σ := by
    change a ≤ ⟪(p₀ : E3), (p₀ : E3)⟫_ℝ
    rw [hpp]
    exact ha'.le
  have hp₀V₀ : (p₀ : E3) ∈ V₀ := hKV₀ ⟨p₀, hp₀σ, rfl⟩
  -- `Q₀` preserves the sphere and the ball, and its Jacobian has the sign of that of `F₀`
  have hQ₀sph : Q₀ '' sphere 0 1 = sphere 0 1 :=
    image_unitSphere_of_image_closedBall Q₀.toHomeomorph hQ₀ball
  have hQ₀symm_sph (z : E3) (hz : z ∈ sphere (0 : E3) 1) : Q₀.symm z ∈ sphere (0 : E3) 1 := by
    rw [← hQ₀sph] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [Q₀.symm_apply_apply]
    exact hw
  have hQ₀symm_ball (z : E3) (hz : z ∈ closedBall (0 : E3) 1) :
      Q₀.symm z ∈ closedBall (0 : E3) 1 := by
    rw [← hQ₀ball] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [Q₀.symm_apply_apply]
    exact hw
  have hdQ₀ : fderiv ℝ Q₀ (p₀ : E3) = fderiv ℝ F₀ (p₀ : E3) :=
    Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hV₀.mem_nhds hp₀V₀) hQ₀F)
  -- the transported second germ
  let F₁' := F₁.trans Q₀.symm.toPartialDiffeomorph
  have hF₁'s (z : E3) : z ∈ F₁'.source ↔ z ∈ F₁.source :=
    ⟨fun h => h.1, fun h => ⟨h, mem_univ _⟩⟩
  have hF₁' (z : E3) : F₁' z = Q₀.symm (F₁ z) := rfl
  have hbd₁' : MapsTo F₁' (sphere 0 1 ∩ F₁'.source) (sphere 0 1) := fun z hz =>
    hQ₀symm_sph _ (hbd₁ ⟨hz.1, (hF₁'s z).mp hz.2⟩)
  have hside₁' : MapsTo F₁' (closedBall 0 1 ∩ F₁'.source) (closedBall 0 1) := fun z hz =>
    hQ₀symm_ball _ (hside₁ ⟨hz.1, (hF₁'s z).mp hz.2⟩)
  have h0R : (0 : EuclideanSpace ℝ (Fin 2)) ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) R :=
    mem_closedBall_self hR.le
  have hdet' : 0 < (fderiv ℝ F₁' (φ₁ 0 : E3)).det := by
    have hF₁d : HasFDerivAt F₁ (fderiv ℝ F₁ (φ₁ 0 : E3)) (φ₁ 0 : E3) :=
      ((F₁.contMDiffOn.contDiffOn.contDiffAt
        (F₁.open_source.mem_nhds (hF₁ 0 h0R))).differentiableAt (by simp)).hasFDerivAt
    have hQd : HasFDerivAt Q₀.symm (fderiv ℝ Q₀.symm (F₁ (φ₁ 0 : E3))) (F₁ (φ₁ 0 : E3)) :=
      ((Q₀.symm.contMDiff.contDiff.differentiable (by simp)) _).hasFDerivAt
    have hcomp : fderiv ℝ F₁' (φ₁ 0 : E3) =
        (fderiv ℝ Q₀.symm (F₁ (φ₁ 0 : E3))).comp (fderiv ℝ F₁ (φ₁ 0 : E3)) :=
      (hQd.comp (φ₁ 0 : E3) hF₁d).fderiv
    have hdetc : (fderiv ℝ F₁' (φ₁ 0 : E3)).det =
        (fderiv ℝ Q₀.symm (F₁ (φ₁ 0 : E3))).det * (fderiv ℝ F₁ (φ₁ 0 : E3)).det := by
      rw [hcomp]
      exact LinearMap.det_comp _ _
    have hinv := det_fderiv_symm_mul Q₀ (F₁ (φ₁ 0 : E3))
    have hsign := det_fderiv_diffeomorph_pos_iff (Q := Q₀) (Q₀.symm (F₁ (φ₁ 0 : E3))) (p₀ : E3)
    rw [hdQ₀] at hsign
    rw [hdetc]
    set q := (fderiv ℝ Q₀.symm (F₁ (φ₁ 0 : E3))).det
    set r := (fderiv ℝ Q₀ (Q₀.symm (F₁ (φ₁ 0 : E3)))).det
    set d0 := (fderiv ℝ F₀ (p₀ : E3)).det
    set d1 := (fderiv ℝ F₁ (φ₁ 0 : E3)).det
    have hd0ne : d0 ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hori
      exact lt_irrefl 0 hori
    have hrne : r ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hinv
      norm_num at hinv
    rcases lt_or_gt_of_ne hd0ne with hd0 | hd0
    · have hr : r < 0 := by
        rcases lt_or_gt_of_ne hrne with hr' | hr'
        · exact hr'
        · exact absurd (hsign.mp hr') (not_lt.mpr hd0.le)
      have hq : q < 0 := by nlinarith
      have hd1 : d1 < 0 := by nlinarith
      nlinarith
    · have hr : 0 < r := hsign.mpr hd0
      have hq : 0 < q := by nlinarith
      have hd1 : 0 < d1 := by nlinarith
      positivity
  -- the sphere chart of the second disk after `F₁'`
  have hne : (φ₁.source ∩ (fun x => (φ₁ x : E3)) ⁻¹' F₁'.source).Nonempty :=
    ⟨0, hφ₁ h0R, (hF₁'s _).mpr (hF₁ 0 h0R)⟩
  obtain ⟨ψ₁, hψ₁s, hψ₁⟩ := exists_partialDiffeomorph_sphereChartComp F₁' φ₁ hbd₁' hne
  have hψ₁src : closedBall (0 : EuclideanSpace ℝ (Fin 2)) R ⊆ ψ₁.source := fun x hx => by
    rw [hψ₁s]
    exact ⟨hφ₁ hx, (hF₁'s _).mpr (hF₁ x hx)⟩
  have hψ₁cap : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) R,
      ⟪(ψ₁ x : E3), (p₀ : E3)⟫_ℝ < a := by
    intro x hx
    by_contra hge
    have hσ : ψ₁ x ∈ σ := not_lt.mp hge
    have hV : ((ψ₁ x : S) : E3) ∈ V₀ := hKV₀ ⟨ψ₁ x, hσ, rfl⟩
    apply hdisj x hx (ψ₁ x) hσ
    rw [← hQ₀F hV, hψ₁ x (hψ₁src hx), hF₁', Q₀.apply_symm_apply]
  have hne_p (θ : S) (hθ : ⟪(θ : E3), (p₀ : E3)⟫_ℝ < a) : θ ≠ p₀ := by
    rintro rfl
    linarith
  have hori2 := det_stereoChart_comp_mul_pos p₀ F₁' hbd₁' hside₁' φ₁ ψ₁ (hφ₁ h0R)
    (hne_p _ (hφ₁cap 0 h0R)) (hne_p _ (hψ₁cap 0 h0R)) ((hF₁'s _).mpr (hF₁ 0 h0R))
    (by
      filter_upwards [ψ₁.open_source.mem_nhds (hψ₁src h0R)] with x hx
      exact hψ₁ x hx)
    hdet'
  -- the sphere isotopy off the cap and its radial extension
  obtain ⟨h, hh, hhi, hh0, hh1, U, hU, hσU, hUfix⟩ :=
    exists_sphere_isotopy_eqOn_disk_off_cap p₀ ha ha' φ₁ ψ₁ hR hφ₁ hψ₁src hφ₁cap hψ₁cap hori2
  obtain ⟨H, -, -, -, hHnorm, -, hHcollar, hHimage⟩ :=
    Diffeomorph.exists_isotopy_extension_sphere_product_collar h hh hhi hh0
  let C₁ := H 1
  have hC₁ball : C₁ '' closedBall 0 1 = closedBall 0 1 := (hHimage 1 1).1
  have hC₁φ (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) R) :
      C₁ (φ₁ x : E3) = (ψ₁ x : E3) := by
    have h1 := (hHcollar 1 (φ₁ x) 1 ⟨by norm_num, by norm_num⟩).1
    rw [one_smul, one_smul, hh1 x hx] at h1
    exact h1
  -- `C₁` is the identity on a neighbourhood of the cap
  let V₀' : Set E3 := {z | z ≠ 0 ∧ 1 / 2 < ‖z‖ ∧ ‖z‖ < 3 / 2 ∧
    DifferentialGeometry.Topology.Manifold.sphereDirection p₀ z ∈ U}
  have hV₀' : IsOpen V₀' := by
    have hdir : ContinuousOn (DifferentialGeometry.Topology.Manifold.sphereDirection p₀)
        ({0}ᶜ : Set E3) :=
      (DifferentialGeometry.Topology.Manifold.contMDiffOn_sphereDirection (n := 2) p₀).continuousOn
    have h1 : IsOpen ({0}ᶜ ∩ DifferentialGeometry.Topology.Manifold.sphereDirection p₀ ⁻¹' U) :=
      hdir.isOpen_inter_preimage isOpen_compl_singleton hU
    have h2 : IsOpen {z : E3 | 1 / 2 < ‖z‖ ∧ ‖z‖ < 3 / 2} :=
      (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
    convert h1.inter h2 using 1
    ext z
    simp only [V₀', mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_compl_iff, mem_singleton_iff]
    tauto
  have hdirz (z : E3) (hz : z ≠ 0) :
      ‖z‖ • (DifferentialGeometry.Topology.Manifold.sphereDirection p₀ z : E3) = z := by
    rw [DifferentialGeometry.Topology.Manifold.coe_sphereDirection p₀ hz, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]
  have hC₁fix (z : E3) (hz : z ∈ V₀') : C₁ z = z := by
    obtain ⟨hz0, hz1, hz2, hzU⟩ := hz
    have h1 := (hHcollar 1 (DifferentialGeometry.Topology.Manifold.sphereDirection p₀ z) ‖z‖
      ⟨hz1.le, hz2.le⟩).1
    rw [hdirz z hz0, (hUfix 1 _ hzU).1] at h1
    rw [hdirz z hz0] at h1
    exact h1
  have hKσV₀' : Subtype.val '' σ ⊆ V₀' := by
    rintro _ ⟨θ, hθ, rfl⟩
    have hθ0 : (θ : E3) ≠ 0 := ne_zero_of_mem_unit_sphere θ
    have hθn : ‖(θ : E3)‖ = 1 := norm_eq_of_mem_sphere θ
    refine ⟨hθ0, by rw [hθn]; norm_num, by rw [hθn]; norm_num, ?_⟩
    have hdθ : DifferentialGeometry.Topology.Manifold.sphereDirection p₀ (θ : E3) = θ := by
      apply Subtype.ext
      rw [DifferentialGeometry.Topology.Manifold.coe_sphereDirection p₀ hθ0, hθn, inv_one,
        one_smul]
    rw [hdθ]
    exact hσU hθ
  -- the collar germ of the second disk
  have hpatch : IsOpen (φ₁ '' ball (0 : EuclideanSpace ℝ (Fin 2)) R) :=
    φ₁.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_ball
      (ball_subset_closedBall.trans hφ₁)
  obtain ⟨W₁, hW₁, hW₁S⟩ := _root_.Topology.IsInducing.subtypeVal.isOpen_iff.mp hpatch
  let G := DifferentialGeometry.Topology.PartialDiffeomorph.restrict
    (F₁'.trans C₁.symm.toPartialDiffeomorph) W₁ hW₁
  have hGs : G.source = F₁'.source ∩ W₁ := by
    ext z
    change ((z ∈ F₁'.source ∧ F₁' z ∈ (univ : Set E3)) ∧ z ∈ W₁) ↔ _
    simp only [mem_univ, and_true, mem_inter_iff]
  have hG (z : E3) : G z = C₁.symm (F₁' z) := rfl
  have hfixed : EqOn G id (sphere (0 : E3) 1 ∩ G.source) := by
    intro z hz
    change G z = z
    have hzW : z ∈ W₁ := (hGs ▸ hz.2).2
    have hzpatch : (⟨z, hz.1⟩ : S) ∈ φ₁ '' ball 0 R := by
      rw [← hW₁S]
      exact hzW
    obtain ⟨x, hx, hxeq⟩ := hzpatch
    have he : (φ₁ x : E3) = z := congrArg Subtype.val hxeq
    have hxc := ball_subset_closedBall hx
    rw [hG, ← he, ← hψ₁ x (hψ₁src hxc), ← hC₁φ x hxc, C₁.symm_apply_apply]
  have hKG : K₁ ⊆ sphere (0 : E3) 1 ∩ G.source := by
    intro z hz
    obtain ⟨θ, ⟨x, hx, hxθ⟩, hθz⟩ := hK₁φ hz
    have he : (φ₁ x : E3) = z := (congrArg Subtype.val hxθ).trans hθz
    refine ⟨hθz ▸ θ.property, ?_⟩
    rw [hGs]
    refine ⟨(hF₁'s z).mpr (he ▸ hF₁ x (ball_subset_closedBall hx)), ?_⟩
    have hθW : θ ∈ Subtype.val ⁻¹' W₁ := by
      rw [hW₁S]
      exact ⟨x, hx, hxθ⟩
    exact hθz ▸ hθW
  have hGside : MapsTo G (closedBall 0 1 ∩ G.source) (closedBall 0 1) := by
    intro z hz
    rw [mem_closedBall_zero_iff, hG, (hHnorm 1 (F₁' z)).2]
    exact mem_closedBall_zero_iff.mp (hside₁' ⟨hz.1, (hGs ▸ hz.2).1⟩)
  -- a half-space separating `K₁` from the cap
  obtain ⟨a₂, ha₂, hK₁a₂⟩ : ∃ a₂ < a, ∀ z ∈ K₁, ⟪z, (p₀ : E3)⟫_ℝ < a₂ := by
    rcases K₁.eq_empty_or_nonempty with hemp | hK₁ne
    · exact ⟨a - 1, by linarith, fun z hz => by rw [hemp] at hz; exact hz.elim⟩
    · have hcont : Continuous (fun z : E3 => ⟪z, (p₀ : E3)⟫_ℝ) :=
        continuous_id.inner continuous_const
      obtain ⟨z₀, hz₀, hmax⟩ := hK₁.exists_isMaxOn hK₁ne hcont.continuousOn
      have hz₀a : ⟪z₀, (p₀ : E3)⟫_ℝ < a := by
        obtain ⟨θ, ⟨x, hx, hxθ⟩, hθz⟩ := hK₁φ hz₀
        rw [← hθz, ← hxθ]
        exact hφ₁cap x (ball_subset_closedBall hx)
      refine ⟨(⟪z₀, (p₀ : E3)⟫_ℝ + a) / 2, by linarith, fun z hz => ?_⟩
      have := hmax hz
      simp only [mem_ofPred_eq] at this
      linarith
  let O : Set E3 := {z | ⟪z, (p₀ : E3)⟫_ℝ < a₂}
  let N₀ : Set E3 := {z | a₂ < ⟪z, (p₀ : E3)⟫_ℝ}
  have hcontp : Continuous (fun z : E3 => ⟪z, (p₀ : E3)⟫_ℝ) :=
    continuous_id.inner continuous_const
  have hO : IsOpen O := isOpen_lt hcontp continuous_const
  have hN₀ : IsOpen N₀ := isOpen_lt continuous_const hcontp
  have hK₁O : K₁ ⊆ O := hK₁a₂
  have hKσN₀ : Subtype.val '' σ ⊆ N₀ := by
    rintro _ ⟨θ, hθ, rfl⟩
    exact lt_of_lt_of_le ha₂ hθ
  obtain ⟨V, hV, hK₁V, hVG, Φ, -, -, -, hΦ1, -, hΦball, L, -, hLO, hLfix⟩ :=
    G.exists_contDiff_compact_isotopy_eqOn_neighborhood_of_eqOn_sphere (c := 0) one_pos hfixed
      hK₁ hKG hGside hO hK₁O
  -- assembly
  let Q := (Φ 1).trans (C₁.trans Q₀)
  have hQ (z : E3) : Q z = Q₀ (C₁ (Φ 1 z)) := rfl
  refine ⟨Q, ?_, ⟨V₀ ∩ V₀' ∩ N₀, (hV₀.inter hV₀').inter hN₀,
    fun z hz => ⟨⟨hKV₀ hz, hKσV₀' hz⟩, hKσN₀ hz⟩, fun z hz => hV₀F hz.1.1, ?_⟩,
    ⟨V, hV, hK₁V, fun z hz => (hF₁'s z).mp (hGs ▸ hVG hz).1, ?_⟩⟩
  · change (Q₀ ∘ C₁ ∘ Φ 1) '' closedBall 0 1 = closedBall 0 1
    rw [image_comp, image_comp, hΦball 1 ⟨zero_le_one, le_rfl⟩, hC₁ball]
    exact hQ₀ball
  · intro z hz
    have hzL : z ∉ L := fun hzL => by
      have h1 : z ∈ O := hLO hzL
      have h2 : z ∈ N₀ := hz.2
      change ⟪z, (p₀ : E3)⟫_ℝ < a₂ at h1
      change a₂ < ⟪z, (p₀ : E3)⟫_ℝ at h2
      linarith
    rw [hQ, (hLfix 1).1 hzL, id, hC₁fix z hz.1.2]
    exact hQ₀F hz.1.1
  · intro z hz
    rw [hQ, hΦ1 hz, hG, C₁.apply_symm_apply, hF₁', Q₀.apply_symm_apply]

end DifferentialGeometry.Topology.Handle
