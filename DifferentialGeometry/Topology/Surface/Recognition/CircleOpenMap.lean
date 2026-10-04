import DifferentialGeometry.Topology.FundamentalGroup.Sphere
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# No open map from a compact simply connected space onto the circle (FC40b, part R1)

A continuous map `p : Y → Circle` from a compact, simply connected, locally path-connected space lifts
through `Circle.exp : ℝ → Circle`.  At a maximum of the lift, `p` cannot be open.  The projection of a
locally trivial bundle is open, so no such `Y` (for example the two-sphere) is the
total space of a circle bundle over the circle.  This is the recognition statement R1 of lane W4-FCb's
sheet ("S² is not a closed circle-bundle surface"), proved without the Euler characteristic.
-/

set_option autoImplicit false

open Set Function Topology Filter

namespace DifferentialGeometry.Topology.Surface

/-- **FC40b (R1), kernel.** A compact, simply connected, locally path-connected space has no
continuous open map to the circle. -/
theorem not_isOpenMap_circle {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [SimplyConnectedSpace Y] [LocallyPathConnectedSpace Y] {p : Y → Circle}
    (hp : Continuous p) : ¬ IsOpenMap p := by
  intro hpo
  obtain ⟨y₀⟩ : Nonempty Y := inferInstance
  obtain ⟨t₀, ht₀⟩ := Circle.exp_surjective (p y₀)
  obtain ⟨F, ⟨-, hF⟩, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    ⟨p, hp⟩ y₀ t₀ ht₀
  have hFp : ∀ y, Circle.exp (F y) = p y := fun y => congrFun hF y
  obtain ⟨y₁, -, hmax⟩ := isCompact_univ.exists_isMaxOn univ_nonempty F.continuous.continuousOn
  set M := F y₁
  have hle : ∀ y, F y ≤ M := fun y => hmax (mem_univ y)
  let V : Set Y := F ⁻¹' Ioo (M - 1) (M + 1)
  have hV : IsOpen V := isOpen_Ioo.preimage F.continuous
  have hy₁ : y₁ ∈ V := ⟨by linarith, by linarith⟩
  have hnhds : p '' V ∈ 𝓝 (Circle.exp M) := by
    have hM : Circle.exp M = p y₁ := hFp y₁
    rw [hM]
    exact (hpo V hV).mem_nhds (mem_image_of_mem p hy₁)
  have htend : Tendsto (fun ε : ℝ => Circle.exp (M + ε)) (𝓝[>] 0) (𝓝 (Circle.exp M)) := by
    have hc : Continuous (fun ε : ℝ => Circle.exp (M + ε)) :=
      Circle.exp.continuous.comp (continuous_const.add continuous_id)
    have := hc.tendsto 0
    simp only [add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Circle.exp (M + ε) ∈ p '' V := htend hnhds
  have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)) fun _ hx => hx.2
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Circle.exp (M + ε) ∈ p '' V ∧ ε < 1 := h1.and h2
  obtain ⟨ε, ⟨⟨y, hyV, hy⟩, hε1⟩, hε0⟩ := (hev.and self_mem_nhdsWithin).exists
  rw [← hFp y] at hy
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hy
  have hFy : M - 1 < F y := hyV.1
  have hFyle : F y ≤ M := hle y
  have hε0' : (0 : ℝ) < ε := hε0
  have hpi : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
  rcases lt_or_ge m 0 with hneg | hnonneg
  · have hm1 : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_iff.mpr hneg
    nlinarith
  · have hm0 : (0 : ℝ) ≤ m := by exact_mod_cast hnonneg
    nlinarith

/-- The projection of a locally trivial bundle is an open map (a point over `U` forces the fibre
to be nonempty). -/
theorem isOpenMap_of_localTrivialization {Y B F : Type*} [TopologicalSpace Y]
    [TopologicalSpace B] [TopologicalSpace F] (p : Y → B)
    (hloc : ∀ z, ∃ U ∈ 𝓝 z, ∃ e : p ⁻¹' U ≃ₜ U × F, ∀ x : p ⁻¹' U, ((e x).1 : B) = p x) :
    IsOpenMap p := by
  intro O hO
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨y, hyO, rfl⟩
  obtain ⟨U, hU, e, he⟩ := hloc (p y)
  have hyU : y ∈ p ⁻¹' U := show p y ∈ U from mem_of_mem_nhds hU
  let O' : Set (p ⁻¹' U) := Subtype.val ⁻¹' O
  have hO' : IsOpen O' := hO.preimage continuous_subtype_val
  -- the image of `O'` in `U × F`, projected to `U`, is open in `U`
  have hA : IsOpen (Prod.fst '' (e '' O')) := isOpenMap_fst _ (e.isOpenMap _ hO')
  obtain ⟨G, hG, hGeq⟩ := isOpen_induced_iff.mp hA
  have hzG : p y ∈ G := by
    have hmem : (⟨p y, hyU⟩ : U) ∈ Prod.fst '' (e '' O') :=
      ⟨e ⟨y, hyU⟩, ⟨⟨y, hyU⟩, hyO, rfl⟩, Subtype.ext (he ⟨y, hyU⟩)⟩
    rw [← hGeq] at hmem
    exact hmem
  refine Filter.mem_of_superset (Filter.inter_mem hU (hG.mem_nhds hzG)) ?_
  rintro z ⟨hzU, hzGz⟩
  have hmem : (⟨z, hzU⟩ : U) ∈ Prod.fst '' (e '' O') := by
    rw [← hGeq]
    exact hzGz
  obtain ⟨q, ⟨x, hxO, rfl⟩, hq⟩ := hmem
  refine ⟨x, hxO, ?_⟩
  rw [← he x, hq]

/-- **FC40b (R1), bundle form.** A compact, simply connected, locally path-connected space is not
the total space of a locally trivial bundle over the circle. -/
theorem not_exists_localTrivialization_circle {Y F : Type*} [TopologicalSpace Y]
    [CompactSpace Y] [SimplyConnectedSpace Y] [LocallyPathConnectedSpace Y]
    [TopologicalSpace F] :
    ¬ ∃ p : Y → Circle, Continuous p ∧
      ∀ z, ∃ U ∈ 𝓝 z, ∃ e : p ⁻¹' U ≃ₜ U × F, ∀ x : p ⁻¹' U, ((e x).1 : Circle) = p x := by
  rintro ⟨p, hp, hloc⟩
  exact not_isOpenMap_circle hp (isOpenMap_of_localTrivialization p hloc)

/-- The two-sphere is locally path-connected (it is a manifold modelled on the plane). -/
theorem locallyPathConnectedSpace_sphereTwo : LocallyPathConnectedSpace SphereTwo :=
  ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) SphereTwo

/-- **FC40b (R1), the sheet's statement.** The two-sphere is not the total space of a locally trivial
circle bundle over the circle. -/
theorem not_exists_circleBundle_sphereTwo :
    ¬ ∃ p : SphereTwo → Circle, Continuous p ∧
      ∀ z, ∃ U ∈ 𝓝 z, ∃ e : p ⁻¹' U ≃ₜ U × Circle, ∀ x : p ⁻¹' U, ((e x).1 : Circle) = p x :=
  have := locallyPathConnectedSpace_sphereTwo
  not_exists_localTrivialization_circle

/-- A space homeomorphic to the two-sphere has no continuous open map to the circle. -/
theorem not_isOpenMap_circle_of_homeomorph_sphereTwo {Y : Type*} [TopologicalSpace Y]
    (h : Y ≃ₜ SphereTwo) {p : Y → Circle} (hp : Continuous p) : ¬ IsOpenMap p := by
  intro hpo
  have := locallyPathConnectedSpace_sphereTwo
  have hc : Continuous (p ∘ h.symm) := hp.comp h.symm.continuous
  exact not_isOpenMap_circle hc (hpo.comp h.symm.isOpenMap)

end DifferentialGeometry.Topology.Surface
