import DifferentialGeometry.Topology.PiecewiseLinear.SimplexParametrisation
import DifferentialGeometry.Topology.ThreeManifold.OrientationParity
import DifferentialGeometry.Topology.ThreeManifold.TorusCut.Taming
-- P0-PORT: dg-ch15 `TangentOrientationSection` is a structure (ch5: an abbrev for
-- `ManifoldOrientation ThreeModel M 3`); the bridge `ofManifoldOrientation` lives here.
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedOrientedStage
/-!
# Triangulations of oriented smooth 3-manifolds are orientable

Step A5 of route A' in `docs/geometrization/handoffs/20261003-survey-r05-orientation-bridge.md`.
Let `h : |K| ≃ₜ M` be a homeomorphism from a finite combinatorial 3-manifold onto a smooth
3-manifold with a tangent orientation `o`. The sign `simplexSign o h r S` of a 3-simplex `S` is
read off from the orientation parity of `h ∘ simplexParam r S` on the open standard simplex.
That parity is constant there (`simplexSign_eq_at`). On the flattened bipyramid over a shared
2-face, the parity of `h ∘ Φ` is constant, and the two affine charts change it by their
determinant signs. So the signs of the two cofaces cancel against the boundary coefficients
(`simplexSign_pair_cancel`), and `CoherentOrientation.ofPairCancel` gives a coherent orientation
of `K`. In particular every combinatorial triangulation of a closed oriented smooth 3-manifold is
orientable (`isTriangulationOrientable_carrier`). This discharges the orientation input of the
compressing-disc criterion for the seam tori of a smooth torus assembly
(`SmoothAssembly.incompressible_iff_isCompressingDisk`).
-/

set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Lift

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type u} [TopologicalSpace M]

noncomputable def spaceLift {K : Geometry.SimplicialComplex ℝ E} (h : K.space ≃ₜ M)
    (g : ThreeSpace → E) (y₀ : ThreeSpace) (hy₀ : g y₀ ∈ K.space) : ThreeSpace → M := by
  classical
  exact fun y => if hy : g y ∈ K.space then h ⟨g y, hy⟩ else h ⟨g y₀, hy₀⟩

theorem spaceLift_of_mem {K : Geometry.SimplicialComplex ℝ E} (h : K.space ≃ₜ M)
    {g : ThreeSpace → E} {y₀ : ThreeSpace} (hy₀ : g y₀ ∈ K.space) {y : ThreeSpace}
    (hy : g y ∈ K.space) : spaceLift h g y₀ hy₀ y = h ⟨g y, hy⟩ :=
  dite_eq_left hy

theorem continuousOn_spaceLift {K : Geometry.SimplicialComplex ℝ E} (h : K.space ≃ₜ M)
    {g : ThreeSpace → E} {y₀ : ThreeSpace} (hy₀ : g y₀ ∈ K.space) {U : Set ThreeSpace}
    (hg : ContinuousOn g U) (hm : MapsTo g U K.space) :
    ContinuousOn (spaceLift h g y₀ hy₀) U := by
  rw [continuousOn_iff_continuous_domRestrict]
  have heq : U.domRestrict (spaceLift h g y₀ hy₀) = h ∘ fun y : U => ⟨g y, hm y.2⟩ := by
    funext y
    exact spaceLift_of_mem h hy₀ (hm y.2)
  rw [heq]
  exact h.continuous.comp ((continuousOn_iff_continuous_domRestrict.mp hg).subtype_mk _)

theorem injOn_spaceLift {K : Geometry.SimplicialComplex ℝ E} (h : K.space ≃ₜ M)
    {g : ThreeSpace → E} {y₀ : ThreeSpace} (hy₀ : g y₀ ∈ K.space) {U : Set ThreeSpace}
    (hg : InjOn g U) (hm : MapsTo g U K.space) :
    InjOn (spaceLift h g y₀ hy₀) U := by
  intro y hy z hz hyz
  rw [spaceLift_of_mem h hy₀ (hm hy), spaceLift_of_mem h hy₀ (hm hz)] at hyz
  exact hg hy hz (congrArg Subtype.val (h.injective hyz))

end Lift

def parSign (a : ZMod 2) : ℤ := if a = 0 then 1 else -1

theorem parSign_add (a b : ZMod 2) : parSign (a + b) = parSign a * parSign b := by
  fin_cases a <;> fin_cases b <;> rfl

theorem parSign_mul_self (a : ZMod 2) : parSign a * parSign a = 1 := by
  fin_cases a <;> rfl

theorem parSign_eq_one_or_neg_one (a : ZMod 2) : parSign a = 1 ∨ parSign a = -1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem detSign_eq_parSign (A : ThreeSpace ≃ᵃ[ℝ] ThreeSpace) :
    detSign A =
      parSign (if 0 < LinearMap.det (A.linear : ThreeSpace →ₗ[ℝ] ThreeSpace) then 0 else 1) := by
  unfold detSign
  split_ifs <;> rfl

section Sign

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]

noncomputable def simplexParity (o : TangentOrientationSection M)
    {K : Geometry.SimplicialComplex ℝ E} (h : K.space ≃ₜ M) (r : LinearOrder E) {S : Finset E}
    (hSK : S ∈ K.faces) (hS : S.card = 4) (y : openStdSimplex3) : ZMod 2 :=
  orientedParity o isOpen_openStdSimplex3
    (continuousOn_spaceLift h (simplexParam_mapsTo_space r hSK hS barycentre3_mem_openStdSimplex3)
      (continuous_simplexParam r hS).continuousOn (simplexParam_mapsTo_space r hSK hS))
    (injOn_spaceLift h (simplexParam_mapsTo_space r hSK hS barycentre3_mem_openStdSimplex3)
      (simplexParam_injective r hSK hS).injOn (simplexParam_mapsTo_space r hSK hS)) y

noncomputable def simplexSign (o : TangentOrientationSection M)
    {K : Geometry.SimplicialComplex ℝ E} (h : K.space ≃ₜ M) (r : LinearOrder E)
    (S : Finset E) : ℤ := by
  classical
  exact if hS : S ∈ K.faces ∧ S.card = 4 then
    parSign (simplexParity o h r hS.1 hS.2 ⟨barycentre3, barycentre3_mem_openStdSimplex3⟩)
  else 0

theorem simplexSign_eq_at (o : TangentOrientationSection M)
    {K : Geometry.SimplicialComplex ℝ E} (h : K.space ≃ₜ M) (r : LinearOrder E)
    {S : Finset E} (hSK : S ∈ K.faces) (hS : S.card = 4) {y : ThreeSpace}
    (hy : y ∈ openStdSimplex3) :
    simplexSign o h r S = parSign (simplexParity o h r hSK hS ⟨y, hy⟩) := by
  rw [simplexSign, dite_eq_left ⟨hSK, hS⟩]
  congr 1
  exact orientedParity_eq_of_isPreconnected (o := o) isOpen_openStdSimplex3 _ _
    isPreconnected_openStdSimplex3 subset_rfl barycentre3_mem_openStdSimplex3 hy

end Sign

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def CoherentOrientation.ofPairCancel (r : LinearOrder E)
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces] {n : ℕ}
    (hK : IsCombinatorialManifold (n + 1) K) (σ : Finset E → ℤ)
    (htop : ∀ s ∈ K.faces, s.card = n + 2 → σ s = 1 ∨ σ s = -1)
    (hpair : ∀ t s s', t ∈ K.faces → t.card = n + 1 → s ∈ faceCofaces K t (n + 2) →
      s' ∈ faceCofaces K t (n + 2) → s ≠ s' →
        σ s * simplexBoundaryCoefficient r s t + σ s' * simplexBoundaryCoefficient r s' t = 0) :
    CoherentOrientation (n + 1) K where
  vertexOrder := r
  sign := σ
  sign_top := htop
  coherent := by
    intro f hf hfcard _
    obtain ⟨s, t, hst, hcofaces⟩ :=
      Finset.card_eq_two.mp (hK.card_faceCofaces_eq_two K hf hfcard)
    have hsco : s ∈ faceCofaces K f (n + 2) := by
      rw [hcofaces]
      exact Finset.mem_insert_self s {t}
    have htco : t ∈ faceCofaces K f (n + 2) := by
      rw [hcofaces]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self t)
    rw [orientedBoundary_eq_sum_faceCofaces, hcofaces]
    simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_singleton, hst,
      not_false_eq_true]
    exact hpair f s t hf hfcard hsco htco hst

theorem isOrientable_of_pairCancel (r : LinearOrder E) {K : Geometry.SimplicialComplex ℝ E}
    [Finite K.faces] {n : ℕ} (hK : IsCombinatorialManifold (n + 1) K) (σ : Finset E → ℤ)
    (htop : ∀ s ∈ K.faces, s.card = n + 2 → σ s = 1 ∨ σ s = -1)
    (hpair : ∀ t s s', t ∈ K.faces → t.card = n + 1 → s ∈ faceCofaces K t (n + 2) →
      s' ∈ faceCofaces K t (n + 2) → s ≠ s' →
        σ s * simplexBoundaryCoefficient r s t + σ s' * simplexBoundaryCoefficient r s' t = 0) :
    IsOrientable (n + 1) K :=
  ⟨CoherentOrientation.ofPairCancel r hK σ htop hpair⟩

end DifferentialGeometry.Topology.PiecewiseLinear

namespace DifferentialGeometry.Topology

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]

theorem simplexSign_pair_cancel (o : TangentOrientationSection M)
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces] (h : K.space ≃ₜ M)
    (r : LinearOrder E) {t s s' : Finset E} (ht : t ∈ K.faces) (htc : t.card = 3)
    (hs : s ∈ faceCofaces K t 4) (hs' : s' ∈ faceCofaces K t 4) (hne : s ≠ s') :
    simplexSign o h r s * simplexBoundaryCoefficient r s t +
      simplexSign o h r s' * simplexBoundaryCoefficient r s' t = 0 := by
  obtain ⟨W, Φ, A, A', y, y', hWo, hWc, hΦc, hΦi, hΦm, hy, hy', hAy, hAy', hev, hev', hsign⟩ :=
    exists_bipyramid r ht htc hs hs' hne
  obtain ⟨hsK, hs4, -⟩ := (mem_faceCofaces K).mp hs
  obtain ⟨hs'K, hs'4, -⟩ := (mem_faceCofaces K).mp hs'
  have hGc := continuousOn_spaceLift h (hΦm hy) hΦc hΦm
  have hGi := injOn_spaceLift h (hΦm hy) hΦi hΦm
  have key : ∀ {S : Finset E} (hSK : S ∈ K.faces) (hS4 : S.card = 4)
      (B : ThreeSpace ≃ᵃ[ℝ] ThreeSpace) {z : ThreeSpace} (hz : z ∈ W)
      (hBz : B z ∈ openStdSimplex3) (hevz : Φ =ᶠ[𝓝 z] simplexParam r hS4 ∘ B),
      orientedParity o hWo hGc hGi ⟨z, hz⟩ = simplexParity o h r hSK hS4 ⟨B z, hBz⟩ +
        if 0 < LinearMap.det (B.linear : ThreeSpace →ₗ[ℝ] ThreeSpace) then 0 else 1 := by
    intro S hSK hS4 B z hz hBz hevz
    have hy₀ := simplexParam_mapsTo_space r hSK hS4 barycentre3_mem_openStdSimplex3
    have hFc := continuousOn_spaceLift h hy₀ (continuous_simplexParam r hS4).continuousOn
      (simplexParam_mapsTo_space r hSK hS4)
    have hFi := injOn_spaceLift h hy₀ (simplexParam_injective r hSK hS4).injOn
      (simplexParam_mapsTo_space r hSK hS4)
    have hBc : Continuous B := B.continuous_of_finiteDimensional
    have hVo : IsOpen (B ⁻¹' openStdSimplex3) := isOpen_openStdSimplex3.preimage hBc
    have hm : MapsTo B (B ⁻¹' openStdSimplex3) openStdSimplex3 := fun _ hw => hw
    have hHc := hFc.comp hBc.continuousOn hm
    have hHi := hFi.comp B.injective.injOn hm
    have hcongr : spaceLift h Φ y (hΦm hy) =ᶠ[𝓝 z]
        spaceLift h (simplexParam r hS4) barycentre3 hy₀ ∘ B := by
      filter_upwards [hevz, hWo.mem_nhds hz, hVo.mem_nhds hBz] with w hw hwW hwV
      rw [Function.comp_apply, spaceLift_of_mem h (hΦm hy) (hΦm hwW),
        spaceLift_of_mem h hy₀ (simplexParam_mapsTo_space r hSK hS4 hwV)]
      exact congrArg h (Subtype.ext hw)
    rw [orientedParity_congr hWo hGc hGi hVo hHc hHi hz hBz hcongr]
    exact orientedParity_comp_affineEquiv isOpen_openStdSimplex3 hFc hFi B hVo hHc hHi hm
      ⟨z, hBz⟩
  have hconst := orientedParity_eq_of_isPreconnected (o := o) hWo hGc hGi hWc subset_rfl hy hy'
  rw [key hsK hs4 A hy hAy hev, key hs'K hs'4 A' hy' hAy' hev'] at hconst
  rw [detSign_eq_parSign, detSign_eq_parSign] at hsign
  rw [simplexSign_eq_at o h r hsK hs4 hAy, simplexSign_eq_at o h r hs'K hs'4 hAy']
  set a := simplexParity o h r hsK hs4 ⟨A y, hAy⟩
  set a' := simplexParity o h r hs'K hs'4 ⟨A' y', hAy'⟩
  set b : ZMod 2 := if 0 < LinearMap.det (A.linear : ThreeSpace →ₗ[ℝ] ThreeSpace) then 0 else 1
  set b' : ZMod 2 :=
    if 0 < LinearMap.det (A'.linear : ThreeSpace →ₗ[ℝ] ThreeSpace) then 0 else 1
  have ha : parSign a = parSign (a + b) * parSign b := by
    rw [parSign_add, mul_assoc, parSign_mul_self, mul_one]
  have ha' : parSign a' = parSign (a' + b') * parSign b' := by
    rw [parSign_add, mul_assoc, parSign_mul_self, mul_one]
  rw [ha, ha', hconst, mul_assoc, mul_assoc, ← mul_add, hsign, mul_zero]

theorem isOrientable_of_homeomorph_tangentOrientation [FiniteDimensional ℝ E]
    (o : TangentOrientationSection M) {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifold 3 K) (h : K.space ≃ₜ M) : IsOrientable 3 K := by
  classical
  let r : LinearOrder E := linearOrderOfSTO WellOrderingRel
  refine isOrientable_of_pairCancel (n := 2) r hK (simplexSign o h r) ?_ ?_
  · intro s hs hscard
    rw [simplexSign, dite_eq_left ⟨hs, hscard⟩]
    exact parSign_eq_one_or_neg_one _
  · intro t s s' ht htc hs hs' hne
    exact simplexSign_pair_cancel o h r ht htc hs hs' hne

end DifferentialGeometry.Topology

namespace GC.Topology

open DifferentialGeometry.Topology

universe u

theorem isTriangulationOrientable_carrier (P : ConnectedClosedOrientedManifold.{u} 3) :
    IsTriangulationOrientable P.Carrier := by
  intro N K _ hK ⟨h⟩
  exact isOrientable_of_homeomorph_tangentOrientation
    (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection.ofManifoldOrientation
      P.orientation) hK h

end GC.Topology

namespace GC.Endpoint
namespace SmoothAssembly

open GC.Topology DifferentialGeometry.Topology

universe u

variable {C : CompactCarrier.{u}} {G : TorusGluing C}

theorem incompressible_iff_isCompressingDisk (A : SmoothAssembly G)
    {P : ConnectedClosedOrientedManifold.{u} 3} (r : A.Reconstruction P) :
    A.Incompressible r ↔ ∀ i d, ¬ IsCompressingDisk (A.torusInPrime r i) d :=
  A.incompressible_iff_of_isTriangulationOrientable r (isTriangulationOrientable_carrier P)

end SmoothAssembly
end GC.Endpoint
