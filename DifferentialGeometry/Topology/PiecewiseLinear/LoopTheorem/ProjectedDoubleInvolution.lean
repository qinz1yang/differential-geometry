/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ProjectedDoublePoints
import DifferentialGeometry.Topology.PiecewiseLinear.CellMapTriangulation
import DifferentialGeometry.Topology.PiecewiseLinear.Product

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

def doublePointRelation {X Y : Type*} (f : X → Y) (P : Set X) : Set (X × X) :=
  {z | z.1 ∈ P ∧ z.2 ∈ P ∧ z.1 ≠ z.2 ∧ f z.1 = f z.2}

theorem mem_doublePointPreimage_iff {X Y : Type*} {f : X → Y} {P : Set X} {x : X} :
    x ∈ doublePointPreimage f P ↔ x ∈ P ∧ ∃ z ∈ P, x ≠ z ∧ f x = f z := by
  constructor
  · rintro ⟨hx, a, ha, b, hb, hab, hax, hbx⟩
    by_cases hxa : x = a
    · exact ⟨hx, b, hb, hxa ▸ hab, hbx.symm⟩
    · exact ⟨hx, a, ha, hxa, hax.symm⟩
  · rintro ⟨hx, z, hz, hxz, hfxz⟩
    exact ⟨hx, x, hx, z, hz, hxz, rfl, hfxz.symm⟩

theorem image_fst_doublePointRelation {X Y : Type*} (f : X → Y) (P : Set X) :
    Prod.fst '' doublePointRelation f P = doublePointPreimage f P := by
  ext x
  rw [mem_doublePointPreimage_iff]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨ha, hb, hab, hfab⟩, rfl⟩
    exact ⟨ha, b, hb, hab, hfab⟩
  · rintro ⟨hx, z, hz, hxz, hfxz⟩
    exact ⟨(x, z), ⟨hx, hz, hxz, hfxz⟩, rfl⟩

theorem image_doublePointPreimage {X Y : Type*} (f : X → Y) (P : Set X) :
    f '' doublePointPreimage f P = doublePointSet f P := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact hx.2
  · intro y hy
    obtain ⟨a, ha, b, hb, hab, hay, hby⟩ := hy
    exact ⟨a, ⟨ha, a, ha, b, hb, hab, rfl, hby.trans hay.symm⟩, hay⟩

theorem bijOn_fst_doublePointRelation {X Y : Type*} {f : X → Y} {P : Set X}
    (hcard : ∀ y, (P ∩ f ⁻¹' {y}).encard ≤ 2) :
    BijOn Prod.fst (doublePointRelation f P) (doublePointPreimage f P) := by
  have hinj : InjOn Prod.fst (doublePointRelation f P) := by
    intro a ha b hb hab
    have hfiber : P ∩ f ⁻¹' {f a.1} = {a.1, a.2} :=
      fiber_eq_pair_of_encard_le_two f P ha.1 ha.2.1 ha.2.2.1 rfl ha.2.2.2.symm
        (hcard (f a.1))
    have hbmem : b.2 ∈ ({a.1, a.2} : Set X) :=
      hfiber ▸ ⟨hb.2.1, hb.2.2.2.symm.trans (congrArg f hab.symm)⟩
    rcases hbmem with hb₁ | hb₂
    · exact (hb.2.2.1 (hab.symm.trans hb₁.symm)).elim
    · exact Prod.ext hab hb₂.symm
  rw [← image_fst_doublePointRelation f P]
  exact hinj.bijOn_image

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem IsPiecewiseAffineOn.isPolyhedron_doublePointRelation
    {f : E → F} {P : Set E} (hf : IsPiecewiseAffineOn f P) (hP : IsPolyhedron P)
    (hloc : IsLocallyInjective (P.domRestrict f)) : IsPolyhedron (doublePointRelation f P) := by
  obtain ⟨K, hKfin, hKP⟩ := hP.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hfK : IsPiecewiseAffineOn f K.space := hKP.symm ▸ hf
  have hlocK : IsLocallyInjective (K.space.domRestrict f) := hKP.symm ▸ hloc
  obtain ⟨R, δ, hR, hRfin, heq, hδ, hstable⟩ :=
    exists_isSubdivision_stable_locallyInjective K f hfK hlocK
  let _ : Finite R.faces := hRfin.to_subtype
  have hRP : R.space = P := hR.space_eq.trans hKP
  have heqR : EqOn (simplicialMap R f) f R.space := hR.space_eq.symm ▸ heq
  obtain ⟨hstar, -⟩ := hstable f (fun _ _ => by simpa using hδ)
  have hstarf : ∀ v ∈ R.vertices, InjOn f (starComplex R v).space := by
    intro v hv x hx z hz hxz
    have hsub := space_mono_of_faces_subset (starComplex_faces_subset R v)
    exact hstar v hv hx hz ((heqR (hsub hx)).trans (hxz.trans (heqR (hsub hz)).symm))
  choose A hA using fun s : R.faces => exists_affineMap_eqOn_simplicialMap R f s.2
  have hAf : ∀ (s : R.faces), EqOn f (A s) (convexHull ℝ (s.1 : Set E)) := by
    intro s x hx
    exact (heqR (R.convexHull_subset_space s.2 hx)).symm.trans (hA s hx)
  let I := {p : R.faces × R.faces // Disjoint p.1.val p.2.val}
  let C : I → Set (E × E) := fun p =>
    (convexHull ℝ (p.1.1.val : Set E) ×ˢ convexHull ℝ (p.1.2.val : Set E)) ∩
      (A p.1.1 ∘ Prod.fst - A p.1.2 ∘ Prod.snd) ⁻¹' {0}
  have hC : ∀ p, IsHPolytope (C p) := by
    intro p
    exact ((isHPolytope_convexHull_of_affineIndependent _ (R.indep p.1.1.2)).prod
      (isHPolytope_convexHull_of_affineIndependent _ (R.indep p.1.2.2))).inter_preimage
      (isHPolytope_singleton (0 : F))
      ((A p.1.1).comp (LinearMap.fst ℝ E E).toAffineMap -
        (A p.1.2).comp (LinearMap.snd ℝ E E).toAffineMap)
  have hrel : doublePointRelation f P = ⋃ p, C p := by
    ext z
    constructor
    · rintro ⟨hxP, hyP, hxy, hfxy⟩
      obtain ⟨s, hs, hxs⟩ := R.mem_space_iff.mp (hRP.symm ▸ hxP)
      obtain ⟨t, ht, hyt⟩ := R.mem_space_iff.mp (hRP.symm ▸ hyP)
      have hdisj := disjoint_faces_of_eq_of_injOn_starComplex R f hstarf hs ht hxs hyt hxy hfxy
      refine mem_iUnion.mpr ⟨⟨(⟨s, hs⟩, ⟨t, ht⟩), hdisj⟩, ⟨hxs, hyt⟩, ?_⟩
      change A ⟨s, hs⟩ z.1 - A ⟨t, ht⟩ z.2 = 0
      rw [← hAf ⟨s, hs⟩ hxs, ← hAf ⟨t, ht⟩ hyt, hfxy, sub_self]
    · intro hz
      obtain ⟨p, ⟨hx, hy⟩, hfeq⟩ := mem_iUnion.mp hz
      refine ⟨hRP ▸ R.convexHull_subset_space p.1.1.2 hx,
        hRP ▸ R.convexHull_subset_space p.1.2.2 hy, ?_, ?_⟩
      · intro hxy
        have hmem := R.inter_subset_convexHull p.1.1.2 p.1.2.2 ⟨hx, hxy.symm ▸ hy⟩
        rw [← Finset.coe_inter, Finset.disjoint_iff_inter_eq_empty.mp p.2,
          Finset.coe_empty, convexHull_empty] at hmem
        exact hmem
      · change A p.1.1 z.1 - A p.1.2 z.2 = 0 at hfeq
        rw [hAf p.1.1 hx, hAf p.1.2 hy]
        exact sub_eq_zero.mp hfeq
  rw [hrel]
  exact IsPolyhedron.iUnion (fun p => (hC p).isPolyhedron)

open Classical in
theorem IsPiecewiseAffineOn.isPolyhedron_doublePointPreimage
    {f : E → F} {P : Set E} (hf : IsPiecewiseAffineOn f P) (hP : IsPolyhedron P)
    (hloc : IsLocallyInjective (P.domRestrict f)) : IsPolyhedron (doublePointPreimage f P) := by
  rw [← image_fst_doublePointRelation f P]
  exact (hf.isPolyhedron_doublePointRelation hP hloc).image_affineMap
    (LinearMap.fst ℝ E E).toAffineMap

open Classical in
theorem IsPiecewiseAffineOn.isPolyhedron_doublePointSet
    {f : E → F} {P : Set E} (hf : IsPiecewiseAffineOn f P) (hP : IsPolyhedron P)
    (hloc : IsLocallyInjective (P.domRestrict f)) : IsPolyhedron (doublePointSet f P) := by
  have hQ := hf.isPolyhedron_doublePointPreimage hP hloc
  rw [← image_doublePointPreimage f P]
  exact (hf.mono_of_isPolyhedron hQ inter_subset_left).isPolyhedron_image hQ

open Classical in
theorem IsPiecewiseAffineOn.isPLHomeomorphOn_fst_doublePointRelation
    {f : E → F} {P : Set E} (hf : IsPiecewiseAffineOn f P) (hP : IsPolyhedron P)
    (hloc : IsLocallyInjective (P.domRestrict f))
    (hcard : ∀ y, (P ∩ f ⁻¹' {y}).encard ≤ 2) :
    IsPLHomeomorphOn Prod.fst (doublePointRelation f P) (doublePointPreimage f P) := by
  have hQ := hf.isPolyhedron_doublePointRelation hP hloc
  have hfst : IsPiecewiseAffineOn (Prod.fst : E × E → E) univ :=
    isPiecewiseAffineOn_of_affine (LinearMap.fst ℝ E E).toAffineMap isOpen_univ
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hQ
    (hfst.mono_of_isPolyhedron hQ (subset_univ _)) (bijOn_fst_doublePointRelation hcard)

open Classical in
theorem IsPiecewiseAffineOn.exists_isPLHomeomorphOn_doublePointPreimage_involution
    {f : E → F} {P : Set E} (hf : IsPiecewiseAffineOn f P) (hP : IsPolyhedron P)
    (hloc : IsLocallyInjective (P.domRestrict f))
    (hcard : ∀ y, (P ∩ f ⁻¹' {y}).encard ≤ 2) :
    ∃ τ : E → E, IsPLHomeomorphOn τ (doublePointPreimage f P) (doublePointPreimage f P) ∧
      ∀ x ∈ doublePointPreimage f P, τ (τ x) = x ∧ τ x ≠ x ∧ f (τ x) = f x := by
  have hπ := hf.isPLHomeomorphOn_fst_doublePointRelation hP hloc hcard
  let g := Function.invFunOn Prod.fst (doublePointRelation f P)
  let τ : E → E := Prod.snd ∘ g
  have hpair : ∀ x ∈ doublePointPreimage f P, (x, τ x) ∈ doublePointRelation f P := by
    intro x hx
    have hg : g x ∈ doublePointRelation f P := hπ.bijOn.surjOn.mapsTo_invFunOn hx
    have hgx : (g x).1 = x := hπ.bijOn.invOn_invFunOn.2 hx
    have heq : (x, τ x) = g x := Prod.ext hgx.symm rfl
    exact heq.symm ▸ hg
  have hmap : MapsTo τ (doublePointPreimage f P) (doublePointPreimage f P) := by
    intro x hx
    have h := hpair x hx
    exact mem_doublePointPreimage_iff.mpr ⟨h.2.1, x, h.1, h.2.2.1.symm, h.2.2.2.symm⟩
  have hinvol : ∀ x ∈ doublePointPreimage f P, τ (τ x) = x := by
    intro x hx
    have hp := hpair x hx
    have hswap : (τ x, x) ∈ doublePointRelation f P :=
      ⟨hp.2.1, hp.1, hp.2.2.1.symm, hp.2.2.2.symm⟩
    exact congrArg Prod.snd (hπ.bijOn.injOn (hpair (τ x) (hmap hx)) hswap rfl)
  have hbij : BijOn τ (doublePointPreimage f P) (doublePointPreimage f P) := by
    refine ⟨hmap, ?_, fun x hx => ⟨τ x, hmap hx, hinvol x hx⟩⟩
    intro x hx y hy hxy
    exact (hinvol x hx).symm.trans ((congrArg τ hxy).trans (hinvol y hy))
  have hτ : IsPiecewiseAffineOn τ (doublePointPreimage f P) :=
    hπ.symm.isPiecewiseAffineOn.affine_comp (LinearMap.snd ℝ E E).toAffineMap
  exact ⟨τ, isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn
    (hf.isPolyhedron_doublePointPreimage hP hloc) hτ hbij,
    fun x hx => ⟨hinvol x hx, (hpair x hx).2.2.1.symm, (hpair x hx).2.2.2.symm⟩⟩

namespace NormalSystem

open Classical in
theorem DoubleCoverDiagram.exists_projected_doublePointInvolution
    {S : NormalSystem E} {T : NormalSystem F} (R : DoubleCoverDiagram S T)
    (D : EmbeddedDisk T) :
    ∃ τ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      IsPolyhedron (doublePointSet (R.projection ∘ D.map) D.domain) ∧
      IsPolyhedron (doublePointPreimage (R.projection ∘ D.map) D.domain) ∧
      IsPLHomeomorphOn τ (doublePointPreimage (R.projection ∘ D.map) D.domain)
        (doublePointPreimage (R.projection ∘ D.map) D.domain) ∧
      ∀ x ∈ doublePointPreimage (R.projection ∘ D.map) D.domain,
        τ (τ x) = x ∧ τ x ≠ x ∧ R.projection (D.map (τ x)) = R.projection (D.map x) ∧
          (τ x ∈ frontier D.domain ↔ x ∈ frontier D.domain) := by
  obtain ⟨f, γ, q, rfl, -, hf, -, hloc, hcard, hpre, -, -, -, -, -⟩ :=
    R.exists_projected_map_of_embeddedDisk D
  obtain ⟨τ, hτ, hτspec⟩ := hf.exists_isPLHomeomorphOn_doublePointPreimage_involution
    D.isPLBall_domain.isPolyhedron hloc hcard
  refine ⟨τ, hf.isPolyhedron_doublePointSet D.isPLBall_domain.isPolyhedron hloc,
    hf.isPolyhedron_doublePointPreimage D.isPLBall_domain.isPolyhedron hloc,
    hτ, fun x hx => ?_⟩
  have hxτ := hτ.bijOn.mapsTo hx
  have hspec := hτspec x hx
  refine ⟨hspec.1, hspec.2.1, hspec.2.2, ?_⟩
  constructor
  · intro hfront
    apply hpre.subset
    refine ⟨hx.1, ?_⟩
    change (R.projection ∘ D.map) x ∈ S.boundaryComplex.space
    rw [← hspec.2.2]
    exact (hpre.superset hfront).2
  · intro hfront
    apply hpre.subset
    refine ⟨hxτ.1, ?_⟩
    change (R.projection ∘ D.map) (τ x) ∈ S.boundaryComplex.space
    rw [hspec.2.2]
    exact (hpre.superset hfront).2

end NormalSystem

end DifferentialGeometry.Topology.PiecewiseLinear
