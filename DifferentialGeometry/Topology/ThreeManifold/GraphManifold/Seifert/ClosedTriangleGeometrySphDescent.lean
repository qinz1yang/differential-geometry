import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryRelation
import DifferentialGeometry.Geometry.Thurston.SphericalScrew
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph

/-!
# Descent of a periodic chart fold to the round three-sphere

Lane B3d (design `docs/geometrization/handoffs/20261004-design-b3d-spherical-row.md`, §2). The
Hopf parametrisation `hopfParam : ModelCoordinates → RoundThree` is `2π`-periodic in the fibre
coordinate and is the inverse of the partial diffeomorphism `hopfChart a` on each slab
`a - π < t < a + π`. For an open set `Ω` of the base and a map `G : ModelCoordinates → M` which is
`2π`-periodic in the fibre coordinate, the map `sphMap G` on the round sphere
(`G` of the chart point `hopfLift u`) satisfies `sphMap G (hopfParam x) = G x`
(`sphMap_hopfParam`), is a local diffeomorphism on `sphDomain Ω = hopfParam '' planeOf⁻¹' Ω`
wherever `G` is one (`isLocalDiffeomorphAt_sphMap`), and every isometry `s3Diffeo γ` of the sphere
which is read in the chart by a map `σ` preserving `G` near `x` relates `hopfParam x` to
`hopfParam (σ x)` (`foldRel_sphMap`); `σ` need only be a local chart expression. If `G` is onto and
all pairs with the same image are related, the descended metric is a complete spherical geometry
on the compact target (`sphGeometry`, `sphGeometry_model`).
-/

set_option autoImplicit false

noncomputable section
open Set Complex
open DifferentialGeometry GC.Geometry
open scoped Topology ContDiff Manifold

namespace GC.Seifert

namespace ClosedTriangle

namespace Sph

local instance factFinrankEuclideanFourSph :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨by simp⟩

def hopfLift (u : RoundThree) : ModelCoordinates :=
  hopfChartAmbient (arg (hopfAngleCoord 0 (u : EuclideanSpace ℝ (Fin 4))))
    (u : EuclideanSpace ℝ (Fin 4))

theorem sum_sq_roundThree (u : RoundThree) :
    (u : EuclideanSpace ℝ (Fin 4)) 0 ^ 2 + (u : EuclideanSpace ℝ (Fin 4)) 1 ^ 2 +
      (u : EuclideanSpace ℝ (Fin 4)) 2 ^ 2 + (u : EuclideanSpace ℝ (Fin 4)) 3 ^ 2 = 1 := by
  have hn := EuclideanSpace.norm_sq_eq (u : EuclideanSpace ℝ (Fin 4))
  rw [mem_sphere_zero_iff_norm.mp u.2] at hn
  simp only [Fin.sum_univ_four, Real.norm_eq_abs, sq_abs, one_pow] at hn
  linarith

theorem hopfAngleCoord_arg_mem {u : EuclideanSpace ℝ (Fin 4)} (hu : u 0 ^ 2 + u 1 ^ 2 ≠ 0) :
    hopfAngleCoord (arg (hopfAngleCoord 0 u)) u ∈ slitPlane := by
  set w := hopfAngleCoord 0 u with hw
  have hw0 : w ≠ 0 := by
    intro h
    apply hu
    rw [← normSq_hopfAngleCoord 0 u, ← hw, h, map_zero]
  have hre : w.re = u 0 := by simp [hw]
  have him : w.im = u 1 := by simp [hw]
  have hpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hc : Real.cos (arg w) = u 0 / ‖w‖ := by rw [cos_arg hw0, hre]
  have hs : Real.sin (arg w) = u 1 / ‖w‖ := by rw [sin_arg, him]
  have hsq : ‖w‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
    rw [← normSq_eq_norm_sq, hw, normSq_hopfAngleCoord]
  refine mem_slitPlane_iff.2 (Or.inl ?_)
  rw [hopfAngleCoord_re, hc, hs]
  have : u 0 * (u 0 / ‖w‖) + u 1 * (u 1 / ‖w‖) = ‖w‖ := by
    field_simp
    linarith
  rw [this]
  exact hpos

theorem hopfParam_hopfLift {u : RoundThree}
    (hu : (u : EuclideanSpace ℝ (Fin 4)) 0 ^ 2 + (u : EuclideanSpace ℝ (Fin 4)) 1 ^ 2 ≠ 0) :
    hopfParam (hopfLift u) = u :=
  Subtype.ext (hopfAmbient_hopfChartAmbient _ _ (hopfAngleCoord_arg_mem hu)
    (sum_sq_roundThree u))

theorem ne_zero_of_mem_hopfChart_source {a : ℝ} {u : RoundThree} (hu : u ∈ (hopfChart a).source) :
    (u : EuclideanSpace ℝ (Fin 4)) 0 ^ 2 + (u : EuclideanSpace ℝ (Fin 4)) 1 ^ 2 ≠ 0 := by
  rw [← normSq_hopfAngleCoord a]
  exact (normSq_pos.2 (slitPlane_ne_zero hu)).ne'

theorem ne_zero_hopfParam (x : ModelCoordinates) :
    (hopfParam x : EuclideanSpace ℝ (Fin 4)) 0 ^ 2 +
      (hopfParam x : EuclideanSpace ℝ (Fin 4)) 1 ^ 2 ≠ 0 := by
  have h : hopfParam x ∈ Set.range hopfParam := ⟨x, rfl⟩
  rw [range_hopfParam] at h
  exact h

theorem hopfParam_mem_hopfChart_source (x : ModelCoordinates) :
    hopfParam x ∈ (hopfChart (x 2)).source :=
  (hopfChart (x 2)).map_target (show x ∈ (hopfChart (x 2)).target from
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)

theorem hopfChart_hopfParam (x : ModelCoordinates) : hopfChart (x 2) (hopfParam x) = x :=
  (hopfChart (x 2)).right_inv (show x ∈ (hopfChart (x 2)).target from
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)

theorem isOpen_image_hopfParam {U : Set ModelCoordinates} (hU : IsOpen U) :
    IsOpen (hopfParam '' U) := by
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨x, hx, rfl⟩
  set e := hopfChart (x 2) with he
  have hxt : x ∈ e.target := ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  refine ⟨e.symm '' (U ∩ e.target), ?_, ?_, ⟨x, ⟨hx, hxt⟩, rfl⟩⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, hy.1, rfl⟩
  · exact e.toOpenPartialHomeomorph.symm.isOpen_image_of_subset_source (hU.inter e.open_target)
      inter_subset_right

variable {M : Type*}

theorem eq_of_hopfParam_eq {G : ModelCoordinates → M}
    (hper : ∀ (x : ModelCoordinates) (m : ℤ),
      G (x + GC.Geometry.fibreShift (2 * Real.pi * m)) = G x)
    {x y : ModelCoordinates} (h : hopfParam x = hopfParam y) : G y = G x := by
  obtain ⟨h0, h1, m, hm⟩ := (hopfParam_eq_hopfParam_iff x y).1 h
  have hy : y = x + GC.Geometry.fibreShift (2 * Real.pi * m) := by
    ext i
    fin_cases i
    · simp [GC.Geometry.fibreShift, h0]
    · simp [GC.Geometry.fibreShift, h1]
    · simp [GC.Geometry.fibreShift, hm]
  rw [hy, hper]

theorem periodic_int {G : ModelCoordinates → M}
    (hper : ∀ x : ModelCoordinates, G (x + GC.Geometry.fibreShift (2 * Real.pi)) = G x)
    (x : ModelCoordinates) (m : ℤ) :
    G (x + GC.Geometry.fibreShift (2 * Real.pi * m)) = G x := by
  have hadd : ∀ (y : ModelCoordinates) (s t : ℝ),
      y + GC.Geometry.fibreShift (s + t) =
        y + GC.Geometry.fibreShift s + GC.Geometry.fibreShift t := by
    intro y s t
    ext i
    fin_cases i <;> simp [GC.Geometry.fibreShift]
    ring
  induction m using Int.induction_on generalizing x with
  | zero =>
    have : x + GC.Geometry.fibreShift (2 * Real.pi * ((0 : ℤ) : ℝ)) = x := by
      ext i
      fin_cases i <;> simp [GC.Geometry.fibreShift]
    rw [this]
  | succ n ih =>
    push_cast
    rw [show 2 * Real.pi * ((n : ℝ) + 1) = 2 * Real.pi * n + 2 * Real.pi by ring, hadd, hper]
    exact ih x
  | pred n ih =>
    have h := hper (x + GC.Geometry.fibreShift (2 * Real.pi * ((-(n : ℤ) - 1 : ℤ) : ℝ)))
    rw [← hadd] at h
    push_cast at h ⊢
    rw [← h, show 2 * Real.pi * (-(n : ℝ) - 1) + 2 * Real.pi = 2 * Real.pi * ((-(n : ℤ) : ℤ) : ℝ)
      by push_cast; ring]
    exact ih x

def sphMap (G : ModelCoordinates → M) (u : RoundThree) : M := G (hopfLift u)

theorem sphMap_hopfParam {G : ModelCoordinates → M}
    (hper : ∀ (x : ModelCoordinates) (m : ℤ),
      G (x + GC.Geometry.fibreShift (2 * Real.pi * m)) = G x)
    (x : ModelCoordinates) : sphMap G (hopfParam x) = G x :=
  eq_of_hopfParam_eq hper (hopfParam_hopfLift (ne_zero_hopfParam x)).symm

theorem sphMap_eq_of_mem_source {G : ModelCoordinates → M}
    (hper : ∀ (x : ModelCoordinates) (m : ℤ),
      G (x + GC.Geometry.fibreShift (2 * Real.pi * m)) = G x)
    {a : ℝ} {u : RoundThree} (hu : u ∈ (hopfChart a).source) :
    sphMap G u = G (hopfChart a u) := by
  have h1 : hopfParam (hopfChart a u) = u := (hopfChart a).left_inv hu
  conv_lhs => rw [← h1]
  exact sphMap_hopfParam hper _

def sphDomain (Ω : Set ℂ) (hΩ : IsOpen Ω) : TopologicalSpace.Opens RoundThree :=
  ⟨hopfParam '' (planeOf ⁻¹' Ω),
    isOpen_image_hopfParam (hΩ.preimage GC.Geometry.ScrewGroup.contDiff_planeOf.continuous)⟩

theorem hopfParam_mem_sphDomain {Ω : Set ℂ} (hΩ : IsOpen Ω) {x : ModelCoordinates}
    (hx : planeOf x ∈ Ω) : hopfParam x ∈ sphDomain Ω hΩ :=
  ⟨x, hx, rfl⟩

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem isLocalDiffeomorphAt_sphMap {G : ModelCoordinates → M}
    (hper : ∀ (x : ModelCoordinates) (m : ℤ),
      G (x + GC.Geometry.fibreShift (2 * Real.pi * m)) = G x)
    {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hG : ∀ x, planeOf x ∈ Ω → IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ G x)
    {u : RoundThree} (hu : u ∈ sphDomain Ω hΩ) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (sphMap G) u := by
  obtain ⟨x, hx, rfl⟩ := hu
  set e := hopfChart (x 2) with he
  have hs : hopfParam x ∈ e.source := hopfParam_mem_hopfChart_source x
  have hex : e (hopfParam x) = x := hopfChart_hopfParam x
  have h1 : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (G ∘ e) (hopfParam x) :=
    IsLocalDiffeomorphAt.comp
      (hf := _root_.PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ e hs)
      (hg := by rw [hex]; exact hG x hx)
  refine IsLocalDiffeomorphAt.of_eventuallyEq ?_ h1
  exact Filter.eventuallyEq_of_mem (e.open_source.mem_nhds hs)
    fun v hv => sphMap_eq_of_mem_source hper hv

theorem isLocalDiffeomorph_sphMap {G : ModelCoordinates → M}
    (hper : ∀ (x : ModelCoordinates) (m : ℤ),
      G (x + GC.Geometry.fibreShift (2 * Real.pi * m)) = G x)
    {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hG : ∀ x, planeOf x ∈ Ω → IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ G x) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun p : sphDomain Ω hΩ => sphMap G p) :=
  isLocalDiffeomorph_restrict_open (sphDomain Ω hΩ)
    fun u => isLocalDiffeomorphAt_sphMap hper hΩ hG u.2

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem foldRel_sphMap {G : ModelCoordinates → M}
    (hper : ∀ (x : ModelCoordinates) (m : ℤ),
      G (x + GC.Geometry.fibreShift (2 * Real.pi * m)) = G x)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (γ : S3Lift) (σ : ModelCoordinates → ModelCoordinates)
    {U : Set ModelCoordinates} (hU : IsOpen U) {x : ModelCoordinates} (hx : x ∈ U)
    (hUΩ : ∀ z ∈ U, planeOf z ∈ Ω) (hσΩ : ∀ z ∈ U, planeOf (σ z) ∈ Ω)
    (hσ : ∀ z ∈ U, s3Diffeo γ (hopfParam z) = hopfParam (σ z))
    (hGσ : ∀ z ∈ U, G (σ z) = G z) :
    FoldRel sphericalModelMetric (sphDomain Ω hΩ) (sphMap G) (hopfParam x) (hopfParam (σ x)) := by
  refine ⟨s3Diffeo γ, s3Diffeo_isometry γ, hσ x hx, hopfParam '' U, isOpen_image_hopfParam hU,
    ⟨x, hx, rfl⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, hUΩ z hz, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    rw [hσ z hz]
    exact ⟨σ z, hσΩ z hz, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    rw [hσ z hz, sphMap_hopfParam hper, sphMap_hopfParam hper, hGσ z hz]

variable [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M]

theorem hasThurstonAtlas_sphericalModelMetric :
    HasThurstonAtlas sphericalModelMetric .spherical :=
  ModelAtlas.refl sphericalModelMetric

def sphGeometry (G : ModelCoordinates → M)
    (hper : ∀ (x : ModelCoordinates) (m : ℤ),
      G (x + GC.Geometry.fibreShift (2 * Real.pi * m)) = G x)
    {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hG : ∀ x, planeOf x ∈ Ω → IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ G x)
    (hsurj : ∀ y : M, ∃ x, planeOf x ∈ Ω ∧ G x = y)
    (hrel : ∀ x x' : ModelCoordinates, planeOf x ∈ Ω → planeOf x' ∈ Ω → G x = G x' →
      FoldRel sphericalModelMetric (sphDomain Ω hΩ) (sphMap G) (hopfParam x) (hopfParam x')) :
    GeometricStructure (𝓡 3) M :=
  have hF := isLocalDiffeomorph_sphMap hper hΩ hG
  have hs : Function.Surjective (fun p : sphDomain Ω hΩ => sphMap G p) := fun y => by
    obtain ⟨x, hx, rfl⟩ := hsurj y
    exact ⟨⟨hopfParam x, hopfParam_mem_sphDomain hΩ hx⟩, sphMap_hopfParam hper x⟩
  have hc := metricFiberCompatible_of_foldRel sphericalModelMetric (sphDomain Ω hΩ) (sphMap G) hF
    (by
      rintro _ _ ⟨x, hx, rfl⟩ ⟨x', hx', rfl⟩ h
      rw [sphMap_hopfParam hper, sphMap_hopfParam hper] at h
      exact hrel x x' hx hx' h)
  GeometricStructure.ofFold (sphericalModelMetric.restrictOpen (sphDomain Ω hΩ))
    (hasThurstonAtlas_sphericalModelMetric.foldRestrictOpen (sphDomain Ω hΩ)) (by decide)
    (fun p : sphDomain Ω hΩ => sphMap G p) hF hs hc
    (foldMetric_complete_of_compact _ _ hF hs hc)

theorem sphGeometry_model (G : ModelCoordinates → M)
    (hper : ∀ (x : ModelCoordinates) (m : ℤ),
      G (x + GC.Geometry.fibreShift (2 * Real.pi * m)) = G x)
    {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hG : ∀ x, planeOf x ∈ Ω → IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ G x)
    (hsurj : ∀ y : M, ∃ x, planeOf x ∈ Ω ∧ G x = y)
    (hrel : ∀ x x' : ModelCoordinates, planeOf x ∈ Ω → planeOf x' ∈ Ω → G x = G x' →
      FoldRel sphericalModelMetric (sphDomain Ω hΩ) (sphMap G) (hopfParam x) (hopfParam x')) :
    (sphGeometry G hper hΩ hG hsurj hrel).model = .spherical :=
  rfl

end Sph

end ClosedTriangle

end GC.Seifert
