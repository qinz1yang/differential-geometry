import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspBoundaryOpenness
import DifferentialGeometry.Topology.Manifold.Diffeomorph.InvFunOnSmooth

/-!
# The inverse coordinate of a cusp collar is `C¹` up to the boundary

For a cusp embedding `e : CuspEmbedding W g K δ X`:

* `CuspEmbedding.contMDiffOn_invFunOn`: the inverse `invFunOn e.toFun cuspDomain` is `C¹` on the
  open collar `e '' cuspDomain`, boundary points included;
* `CuspEmbedding.exists_partialDiffeomorph_cuspDomain`: `e` restricted to the cusp domain is a
  `C¹` partial diffeomorphism onto the open collar;
* `CuspEmbedding.exists_lift`: a `C¹` curve of the carrier with values in the collar is `e ∘ c`
  for a `C¹` curve `c` of the cusp domain (curve lifting).

Inputs: openness up to height `0` (`CuspEmbedding.isOpen_image`), injectivity on the domain
(`isEmbedding`), invertibility of `mfderiv` (`immersion` + equal dimension 3), and the on-a-set
inverse theorem `contMDiffOn_invFunOn_of_isInvertible_mfderiv` (corners allowed).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
  {δ : ℝ} {X : Set W.Carrier}

/-- A cusp embedding is injective on the cusp domain. -/
theorem CuspEmbedding.injOn_cuspDomain (e : CuspEmbedding W g K δ X) :
    InjOn e.toFun cuspDomain := by
  intro x hx y hy hxy
  have h := e.isEmbedding.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy
  exact congrArg Subtype.val h

/-- The differential of a cusp embedding is invertible on the cusp domain. -/
theorem CuspEmbedding.isInvertible_mfderiv (e : CuspEmbedding W g K δ X) {p : CuspHalfSpace}
    (hp : p ∈ cuspDomain) : (mfderiv halfCollarModel W.model e.toFun p).IsInvertible := by
  have hdim : Module.finrank ℝ
      ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    simp [Module.finrank_prod]
  let L : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) := mfderiv halfCollarModel W.model e.toFun p
  exact ⟨(L.toLinearMap.linearEquivOfInjective (e.immersion p hp) hdim).toContinuousLinearEquiv,
    ContinuousLinearMap.ext fun v => rfl⟩

/-- **The inverse coordinate is `C¹` up to the boundary.** -/
theorem CuspEmbedding.contMDiffOn_invFunOn (e : CuspEmbedding W g K δ X) :
    ContMDiffOn W.model halfCollarModel 1 (invFunOn e.toFun cuspDomain)
      (e.toFun '' cuspDomain) :=
  Topology.Manifold.contMDiffOn_invFunOn_of_isInvertible_mfderiv isOpen_cuspDomain
    (e.contMDiffOn.of_le (by exact_mod_cast Nat.le_add_left 1 K)) e.injOn_cuspDomain
    (fun _ hV hVo => e.isOpen_image hVo hV) fun _ hp => e.isInvertible_mfderiv hp

/-- A cusp embedding is a `C¹` partial diffeomorphism from the cusp domain onto the open collar
`e '' cuspDomain` (boundary included). -/
theorem CuspEmbedding.exists_partialDiffeomorph_cuspDomain (e : CuspEmbedding W g K δ X) :
    ∃ Φ : PartialDiffeomorph halfCollarModel W.model CuspHalfSpace W.Carrier 1,
      Φ.source = cuspDomain ∧ Φ.target = e.toFun '' cuspDomain ∧ EqOn e.toFun Φ cuspDomain ∧
      EqOn Φ.symm (invFunOn e.toFun cuspDomain) (e.toFun '' cuspDomain) :=
  ⟨{ toFun := e.toFun
     invFun := invFunOn e.toFun cuspDomain
     source := cuspDomain
     target := e.toFun '' cuspDomain
     map_source' := fun _ hx => mem_image_of_mem _ hx
     map_target' := fun _ hy => invFunOn_mem hy
     left_inv' := fun _ hx => e.injOn_cuspDomain.leftInvOn_invFunOn hx
     right_inv' := fun _ hy => invFunOn_eq hy
     open_source := isOpen_cuspDomain
     open_target := e.isOpen_image_cuspDomain
     contMDiffOn_toFun := e.contMDiffOn.of_le (by exact_mod_cast Nat.le_add_left 1 K)
     contMDiffOn_invFun := e.contMDiffOn_invFunOn }, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- **Curve lifting.** A `C¹` curve of the carrier on a set `s` with values in the collar
`e '' cuspDomain` is `e ∘ c` on `s` for a `C¹` curve `c` of the cusp domain. -/
theorem CuspEmbedding.exists_lift (e : CuspEmbedding W g K δ X) {γ : ℝ → W.Carrier}
    {s : Set ℝ} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) W.model 1 γ s)
    (hγU : MapsTo γ s (e.toFun '' cuspDomain)) :
    ∃ c : ℝ → CuspHalfSpace, ContMDiffOn 𝓘(ℝ, ℝ) halfCollarModel 1 c s ∧ MapsTo c s cuspDomain ∧
      ∀ t ∈ s, e.toFun (c t) = γ t :=
  ⟨invFunOn e.toFun cuspDomain ∘ γ, e.contMDiffOn_invFunOn.comp hγ hγU,
    fun _ ht => invFunOn_mem (hγU ht), fun _ ht => invFunOn_eq (hγU ht)⟩

end DifferentialGeometry.Geometry.Collapse
