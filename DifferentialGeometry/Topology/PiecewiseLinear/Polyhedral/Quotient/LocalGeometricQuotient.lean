import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Maps.PLSubcomplexExtension
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Quotient.GeometricPolyhedralQuotient

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry _root_.Topology

noncomputable section

set_option linter.unusedSectionVars false

variable {E F M : Type*} [DecidableEq E] [DecidableEq F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace M] [T2Space M]

omit [DecidableEq E] [DecidableEq F] in
theorem exists_local_geometric_polyhedral_quotient
    (K D : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hDK : D.faces ⊆ K.faces)
    (f : E → F)
    (hf : ∀ s ∈ D.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    (hinj : ∀ s ∈ D.faces, InjOn f (convexHull ℝ (s : Set E)))
    {d : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1)
    (F₀ : C(K.space, M))
    (hF : ∀ x y : K.space, x.val ∈ D.space → y.val ∈ D.space →
      (F₀ x = F₀ y ↔ f x.val = f y.val)) :
    ∃ n : ℕ, ∃ Q : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
      ∃ q : C(K.space, Q.space), ∃ G : C(Q.space, M),
      Q.faces.Finite ∧ (∀ s ∈ Q.faces, s.card ≤ d + 1) ∧ IsQuotientMap q ∧
      (∀ x y : K.space, q x = q y ↔
        x = y ∨ (x.val ∈ D.space ∧ y.val ∈ D.space ∧ f x.val = f y.val)) ∧
      (∀ x, G (q x) = F₀ x) ∧
      IsClosedEmbedding (fun z : q '' {x | x.val ∈ D.space} => G z.val) ∧
      (∀ J : SimplicialComplex ℝ E, J.faces ⊆ K.faces →
        ∃ R : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
          R.faces ⊆ Q.faces ∧ R.space = (fun x : K.space => (q x).val) '' {x | x.val ∈ J.space} ∧
          (∀ r : ℕ, (∀ s ∈ J.faces, s.card ≤ r) → ∀ s ∈ R.faces, s.card ≤ r) ∧
          hasFacewiseAffineSections K J Q R q) ∧
      hasNondegeneratePLSubdivision K (fun x => (q x).val) := by
  classical
  obtain ⟨m, g, hg, hgaff, hginj⟩ := exists_nondegenerate_PL_extension K D hK hDK f hf hinj
  let KB := barycentricSubdivision K
  let DB := barycentricSubdivision D
  have hKBspace : KB.space = K.space := barycentricSubdivision_space K
  have hDBspace : DB.space = D.space := barycentricSubdivision_space D
  let H : KB.space ≃ₜ K.space := Homeomorph.setCongr hKBspace
  let FB : C(KB.space, M) := ⟨F₀ ∘ H, F₀.continuous.comp H.continuous⟩
  have hFB : ∀ x y : KB.space, x.val ∈ DB.space → y.val ∈ DB.space →
      (FB x = FB y ↔ g x.val = g y.val) := by
    intro x y hx hy
    have hxD := hDBspace.subset hx
    have hyD := hDBspace.subset hy
    exact (hF (H x) (H y) hxD hyD).trans (extension_fiber_iff hg hxD hyD).symm
  obtain ⟨n, Q, qB, G, hQ, hdim, hqB, hrelB, hfactorB, hembB, himagesB, hPLB⟩ :=
    exists_geometric_polyhedral_quotient_full_with_descent KB DB
      (barycentricSubdivision_finite_faces K hK) (barycentricSubdivision_faces_subset hDK)
      g hgaff hginj ((barycentricSubdivision_refines K).face_card_le hd) FB hFB
  let q : C(K.space, Q.space) := ⟨qB ∘ H.symm, qB.continuous.comp H.symm.continuous⟩
  have hq : IsQuotientMap q := hqB.comp H.symm.isQuotientMap
  have hrel : ∀ x y : K.space, q x = q y ↔
      x = y ∨ (x.val ∈ D.space ∧ y.val ∈ D.space ∧ f x.val = f y.val) := by
    intro x y
    change qB (H.symm x) = qB (H.symm y) ↔ _
    rw [hrelB, H.symm.injective.eq_iff]
    constructor
    · rintro (he | ⟨hx, hy, he⟩)
      · exact Or.inl he
      · have hxD : x.val ∈ D.space := hDBspace.subset hx
        have hyD : y.val ∈ D.space := hDBspace.subset hy
        exact Or.inr ⟨hxD, hyD, (extension_fiber_iff hg hxD hyD).mp he⟩
    · rintro (he | ⟨hx, hy, he⟩)
      · exact Or.inl he
      · exact Or.inr ⟨hDBspace.symm.subset hx, hDBspace.symm.subset hy,
          (extension_fiber_iff hg hx hy).mpr he⟩
  have hfactor : ∀ x, G (q x) = F₀ x := by
    intro x
    have he := hfactorB (H.symm x)
    change G (q x) = F₀ (H (H.symm x)) at he
    simpa only [H.apply_symm_apply] using he
  have hDimage : qB '' {x : KB.space | x.val ∈ DB.space} =
      q '' {x : K.space | x.val ∈ D.space} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨H x, hDBspace.subset hx, ?_⟩
      change qB (H.symm (H x)) = qB x
      rw [H.symm_apply_apply]
    · rintro ⟨x, hx, rfl⟩
      exact ⟨H.symm x, hDBspace.symm.subset hx, rfl⟩
  have hemb : IsClosedEmbedding (fun z : q '' {x | x.val ∈ D.space} => G z.val) := by
    rwa [hDimage] at hembB
  refine ⟨n, Q, q, G, hQ, hdim, hq, hrel, hfactor, hemb, ?_, ?_⟩
  · intro J hJK
    obtain ⟨R, hRQ, hRspace, hRdim, hsections⟩ :=
      himagesB (barycentricSubdivision J) (barycentricSubdivision_faces_subset hJK)
    refine ⟨R, hRQ, ?_, ?_, ?_⟩
    · rw [hRspace, barycentricSubdivision_space J]
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨H x, hx, ?_⟩
        change (qB (H.symm (H x))).val = (qB x).val
        rw [H.symm_apply_apply]
      · rintro ⟨x, hx, rfl⟩
        exact ⟨H.symm x, hx, rfl⟩
    · intro r hr
      apply hRdim r
      simpa only [barycentricSubdivisionIter] using barycentricSubdivisionIter_face_card_le_nat J hr 1
    · intro t ht
      obtain ⟨u, hu, B, hB⟩ := hsections t ht
      obtain ⟨s, hs, hus⟩ := barycentricSubdivision_refines J u hu
      refine ⟨s, hs, B, ?_⟩
      intro y hy
      obtain ⟨x, hxB, hxu, hqx⟩ := hB y hy
      refine ⟨H x, hxB, hus hxu, ?_⟩
      change (qB (H.symm (H x))).val = y
      rwa [H.symm_apply_apply]
  · obtain ⟨R, hR, hRspace, hRref, hRaff⟩ := hPLB
    refine ⟨R, hR, hRspace.trans hKBspace,
      hRref.trans (barycentricSubdivision_refines K), ?_⟩
    intro s hs
    obtain ⟨B, hB, hBi⟩ := hRaff s hs
    exact ⟨B, fun x hx => hB (H.symm x) hx, hBi⟩

end

end DifferentialGeometry.Topology.Engulfing
