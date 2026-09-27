/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ProjectedDoubleInvolution

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem IsPiecewiseAffineOn.exists_finite_doublePointSheets
    {f : E → F} {P : Set E} (hf : IsPiecewiseAffineOn f P) (hP : IsPolyhedron P)
    (hloc : IsLocallyInjective (P.domRestrict f))
    (hcard : ∀ y, (P ∩ f ⁻¹' {y}).encard ≤ 2) :
    ∃ (n : ℕ) (A B : Fin n → Set E),
      (∀ i, IsPolyhedron (A i) ∧ IsPolyhedron (B i) ∧ Disjoint (A i) (B i) ∧
        A i ⊆ doublePointPreimage f P ∧ B i ⊆ doublePointPreimage f P ∧
        IsPLHomeomorphOn f (A i) (f '' A i) ∧ IsPLHomeomorphOn f (B i) (f '' A i) ∧
        P ∩ f ⁻¹' (f '' A i) = A i ∪ B i) ∧
      ∀ y ∈ doublePointSet f P, ∃ i, f '' A i ∈ 𝓝[doublePointSet f P] y := by
  obtain ⟨K, hKfin, hKP⟩ := hP.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  obtain ⟨R, hR, hRfin, hstar⟩ :=
    exists_isSubdivision_injOn_starComplex K f (hKP.symm ▸ hloc)
  let _ : Finite R.faces := hRfin.to_subtype
  have hRP : R.space = P := hR.space_eq.trans hKP
  have hVfin : R.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn hRfin
  let _ : Finite R.vertices := hVfin.to_subtype
  let Q := doublePointPreimage f P
  have hQ : IsPolyhedron Q := hf.isPolyhedron_doublePointPreimage hP hloc
  obtain ⟨τ, hτ, hτspec⟩ :=
    hf.exists_isPLHomeomorphOn_doublePointPreimage_involution hP hloc hcard
  let A (v : R.vertices) := Q ∩ (starComplex R (v : E)).space
  let B (v : R.vertices) := τ '' A v
  have hAQ (v : R.vertices) : A v ⊆ Q := inter_subset_left
  have hBQ (v : R.vertices) : B v ⊆ Q := (image_mono (hAQ v)).trans hτ.image_eq.subset
  have hApoly (v : R.vertices) : IsPolyhedron (A v) := by
    let _ : Finite (starComplex R (v : E)).faces := (starComplex_faces_finite R v).to_subtype
    exact hQ.inter (isPolyhedron_space (starComplex R (v : E)))
  have hBpoly (v : R.vertices) : IsPolyhedron (B v) :=
    (hApoly v).image_of_isPiecewiseAffineOn
      (hτ.isPiecewiseAffineOn.mono_of_isPolyhedron (hApoly v) (hAQ v))
      (hτ.bijOn.injOn.mono (hAQ v))
  have hAinj (v : R.vertices) : InjOn f (A v) := (hstar v v.2).mono inter_subset_right
  have hBimage (v : R.vertices) : f '' B v = f '' A v := by
    rw [show B v = τ '' A v from rfl, image_image]
    exact (show EqOn (f ∘ τ) f (A v) from fun x hx => (hτspec x (hAQ v hx)).2.2).image_eq
  have hBinj (v : R.vertices) : InjOn f (B v) := by
    rintro x ⟨a, ha, rfl⟩ z ⟨b, hb, rfl⟩ hab
    apply congrArg τ
    apply hAinj v ha hb
    rw [← (hτspec a (hAQ v ha)).2.2, ← (hτspec b (hAQ v hb)).2.2]
    exact hab
  have hdisj (v : R.vertices) : Disjoint (A v) (B v) := by
    rw [Set.disjoint_left]
    rintro x hx ⟨a, ha, rfl⟩
    exact (hτspec a (hAQ v ha)).2.1 (hAinj v hx ha (hτspec a (hAQ v ha)).2.2)
  have hsat (v : R.vertices) : P ∩ f ⁻¹' (f '' A v) = A v ∪ B v := by
    apply Subset.antisymm
    · rintro x ⟨hxP, a, ha, hax⟩
      have hs := hτspec a (hAQ v ha)
      have hpair := fiber_eq_pair_of_encard_le_two f P (hAQ v ha).1
        (hτ.bijOn.mapsTo (hAQ v ha)).1 hs.2.1.symm rfl hs.2.2 (hcard (f a))
      have hxpair : x ∈ ({a, τ a} : Set E) := hpair ▸ ⟨hxP, hax.symm⟩
      rcases hxpair with hx | hx
      · exact Or.inl (hx.symm ▸ ha)
      · exact Or.inr ⟨a, ha, hx.symm⟩
    · intro x hx
      rcases hx with hx | hx
      · exact ⟨(hAQ v hx).1, mem_image_of_mem f hx⟩
      · exact ⟨(hBQ v hx).1, hBimage v ▸ mem_image_of_mem f hx⟩
  have hPL (v : R.vertices) :
      IsPLHomeomorphOn f (A v) (f '' A v) ∧ IsPLHomeomorphOn f (B v) (f '' A v) := by
    constructor
    · exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn (hApoly v)
        (hf.mono_of_isPolyhedron (hApoly v) ((hAQ v).trans inter_subset_left))
        (hAinj v).bijOn_image
    · rw [← hBimage v]
      exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn (hBpoly v)
        (hf.mono_of_isPolyhedron (hBpoly v) ((hBQ v).trans inter_subset_left))
        (hBinj v).bijOn_image
  have hneighborhood (y : F) (hy : y ∈ doublePointSet f P) :
      ∃ v : R.vertices, f '' A v ∈ 𝓝[doublePointSet f P] y := by
    obtain ⟨a, ha, b, hb, hab, hay, hby⟩ := hy
    have haQ : a ∈ Q := ⟨ha, a, ha, b, hb, hab, rfl, hby.trans hay.symm⟩
    obtain ⟨v, hv, hav⟩ := exists_vertex_mem_openStar R (hRP.symm ▸ ha)
    let U : Set Q := Subtype.val ⁻¹' openStar R v
    have hU : IsOpen U := by
      have heq : U = (Subtype.val : Q → E) ⁻¹' (avoidingUnion R v)ᶜ := by
        ext x
        exact ⟨fun hx => hx.2, fun hx => ⟨hRP.symm ▸ x.2.1, hx⟩⟩
      rw [heq]
      exact (isClosed_avoidingUnion R v).isOpen_compl.preimage continuous_subtype_val
    have hcover := isCoveringMap_doublePointProjection_of_isLocallyInjective
      hP.isCompact hf.continuousOn hloc hcard
    have himg := hcover.isOpenMap.image_mem_nhds (hU.mem_nhds (show (⟨a, haQ⟩ : Q) ∈ U from hav))
    have himg' : Subtype.val '' (doublePointProjection f P '' U) ∈
        𝓝[doublePointSet f P] (f a) := mem_nhds_subtype_iff_nhdsWithin.mp himg
    rw [hay] at himg'
    refine ⟨⟨v, hv⟩, Filter.mem_of_superset himg' ?_⟩
    rintro z ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x, ⟨x.2, ?_⟩, rfl⟩
    rw [starComplex_space R v hv]
    exact openStar_subset_closedStar R hv hx
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin R.vertices
  refine ⟨n, A ∘ e.symm, B ∘ e.symm, fun i => ?_, fun y hy => ?_⟩
  · exact ⟨hApoly (e.symm i), hBpoly (e.symm i), hdisj (e.symm i),
      hAQ (e.symm i), hBQ (e.symm i), (hPL (e.symm i)).1, (hPL (e.symm i)).2, hsat (e.symm i)⟩
  · obtain ⟨v, hv⟩ := hneighborhood y hy
    exact ⟨e v, by simpa only [Function.comp_apply, e.symm_apply_apply] using hv⟩

namespace NormalSystem

open Classical in
theorem DoubleCoverDiagram.exists_projected_doublePointSheets
    {S : NormalSystem E} {T : NormalSystem F} (R : DoubleCoverDiagram S T)
    (D : EmbeddedDisk T) :
    ∃ (n : ℕ) (A B : Fin n → Set (EuclideanSpace ℝ (Fin 2))),
      (∀ i, IsPolyhedron (A i) ∧ IsPolyhedron (B i) ∧ Disjoint (A i) (B i) ∧
        A i ⊆ doublePointPreimage (R.projection ∘ D.map) D.domain ∧
        B i ⊆ doublePointPreimage (R.projection ∘ D.map) D.domain ∧
        IsPLHomeomorphOn (R.projection ∘ D.map) (A i) ((R.projection ∘ D.map) '' A i) ∧
        IsPLHomeomorphOn (R.projection ∘ D.map) (B i) ((R.projection ∘ D.map) '' A i) ∧
        D.domain ∩ (R.projection ∘ D.map) ⁻¹' ((R.projection ∘ D.map) '' A i) = A i ∪ B i ∧
        (R.projection ∘ D.map) '' (A i ∩ frontier D.domain) =
          (R.projection ∘ D.map) '' A i ∩ S.boundaryComplex.space ∧
        (R.projection ∘ D.map) '' (B i ∩ frontier D.domain) =
          (R.projection ∘ D.map) '' A i ∩ S.boundaryComplex.space) ∧
      ∀ y ∈ doublePointSet (R.projection ∘ D.map) D.domain,
        ∃ i, (R.projection ∘ D.map) '' A i ∈
          𝓝[doublePointSet (R.projection ∘ D.map) D.domain] y := by
  obtain ⟨f, γ, q, rfl, -, hf, -, hloc, hcard, hpre, -, -, -, -, -⟩ :=
    R.exists_projected_map_of_embeddedDisk D
  obtain ⟨n, A, B, hAB, hcover⟩ := hf.exists_finite_doublePointSheets
    D.isPLBall_domain.isPolyhedron hloc hcard
  have hboundary {C : Set (EuclideanSpace ℝ (Fin 2))} (hC : C ⊆ D.domain) :
      (R.projection ∘ D.map) '' (C ∩ frontier D.domain) =
        (R.projection ∘ D.map) '' C ∩ S.boundaryComplex.space := by
    rw [← image_inter_preimage, ← hpre, ← inter_assoc, inter_eq_left.mpr hC]
  refine ⟨n, A, B, fun i => ?_, hcover⟩
  obtain ⟨hA, hB, hdisj, hAP, hBP, hAf, hBf, hsat⟩ := hAB i
  refine ⟨hA, hB, hdisj, hAP, hBP, hAf, hBf, hsat,
    hboundary (hAP.trans inter_subset_left), ?_⟩
  rw [hboundary (hBP.trans inter_subset_left), hBf.image_eq]

end NormalSystem

end DifferentialGeometry.Topology.PiecewiseLinear
