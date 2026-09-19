/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ProjectedBoundaryCrossing
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ProjectedBoundaryHalfSpace
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ProjectedBoundaryHomotopy

/-!
# Boundary normalization preserving crossings near a closed set
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section FiberGerms

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

private theorem isPLHomeomorphOn_inter_preimage_isOpen {f : E → F} {A : Set E}
    (hf : IsPLHomeomorphOn f A (f '' A)) {U : Set F} (hU : IsOpen U) :
    IsPLHomeomorphOn f (A ∩ f ⁻¹' U) (f '' (A ∩ f ⁻¹' U)) := by
  have hinj : InjOn f (A ∩ f ⁻¹' U) := hf.bijOn.injOn.mono inter_subset_left
  refine ⟨hinj.bijOn_image, ?_, ?_⟩
  · simpa only [Function.id_comp] using
      (isPiecewiseAffineOn_id (u := U) hU).comp hf.isPiecewiseAffineOn
  · rw [image_inter_preimage]
    refine (hf.isPiecewiseAffineOn_invFunOn.inter_of_isOpen hU).congr ?_
    rintro y ⟨⟨x, hx, rfl⟩, hfx⟩
    rw [hinj.leftInvOn_invFunOn ⟨hx, hfx⟩, hf.bijOn.injOn.leftInvOn_invFunOn hx]

private theorem crossing_sheet_of_eq_fiber {f g : E → F} {P Q A : Set E} {a : E}
    {y : F} {U : Set F} (hU : IsOpen U) (hyU : y ∈ U)
    (hfiber : ∀ z ∈ U, P ∩ f ⁻¹' {z} = Q ∩ g ⁻¹' {z})
    (hg : ContinuousOn g Q) (ha : a ∈ A) (hfa : f a = y) (hAP : A ⊆ P)
    (hA : A ∈ 𝓝[P] a) (hfA : IsPLHomeomorphOn f A (f '' A)) :
    a ∈ A ∩ f ⁻¹' U ∧ g a = y ∧ A ∩ f ⁻¹' U ⊆ Q ∧
      A ∩ f ⁻¹' U ∈ 𝓝[Q] a ∧
      IsPLHomeomorphOn g (A ∩ f ⁻¹' U) (g '' (A ∩ f ⁻¹' U)) ∧
      g '' (A ∩ f ⁻¹' U) = f '' A ∩ U := by
  have hforward (x : E) (hx : x ∈ P) (hfx : f x ∈ U) : x ∈ Q ∧ g x = f x :=
    (hfiber (f x) hfx).subset ⟨hx, rfl⟩
  have hback (x : E) (hx : x ∈ Q) (hgx : g x ∈ U) : x ∈ P ∧ f x = g x :=
    (hfiber (g x) hgx).superset ⟨hx, rfl⟩
  have haU : f a ∈ U := hfa.symm ▸ hyU
  have haQ : a ∈ Q := (hforward a (hAP ha) haU).1
  have hga : g a = y := (hforward a (hAP ha) haU).2.trans hfa
  have hEq : EqOn g f (A ∩ f ⁻¹' U) := fun x hx => (hforward x (hAP hx.1) hx.2).2
  have himage : g '' (A ∩ f ⁻¹' U) = f '' A ∩ U :=
    hEq.image_eq.trans (image_inter_preimage f A U)
  refine ⟨⟨ha, haU⟩, hga, fun x hx => (hforward x (hAP hx.1) hx.2).1, ?_, ?_, himage⟩
  · obtain ⟨O, hO, hOA⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hA
    have hpre : g ⁻¹' U ∈ 𝓝[Q] a := (hg a haQ) (hga.symm ▸ hU.mem_nhds hyU)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hO, hpre] with x hxQ hxO hxU
    have hx := hback x hxQ hxU
    exact ⟨hOA ⟨hxO, hx.1⟩, show f x ∈ U from hx.2.symm ▸ hxU⟩
  · rw [hEq.image_eq]
    exact (isPLHomeomorphOn_inter_preimage_isOpen hfA hU).congr hEq

private theorem hasPLDoubleCrossingAt_of_eventually_eq_fiber {f g : E → F}
    {P Q : Set E} {y : F} (hg : ContinuousOn g Q)
    (hfiber : ∀ᶠ z in 𝓝 y, P ∩ f ⁻¹' {z} = Q ∩ g ⁻¹' {z})
    (hcross : HasPLDoubleCrossingAt f P y) : HasPLDoubleCrossingAt g Q y := by
  obtain ⟨U, hUsub, hU, hyU⟩ := mem_nhds_iff.mp hfiber
  obtain ⟨a, b, A, B, ha, hb, hfa, hfb, hAP, hBP, hdis, hA, hB, hfA, hfB, hc, hcov⟩ := hcross
  obtain ⟨ha', hga, hAQ, hA', hgA, himgA⟩ :=
    crossing_sheet_of_eq_fiber hU hyU hUsub hg ha hfa hAP hA hfA
  obtain ⟨hb', hgb, hBQ, hB', hgB, himgB⟩ :=
    crossing_sheet_of_eq_fiber hU hyU hUsub hg hb hfb hBP hB hfB
  refine ⟨a, b, A ∩ f ⁻¹' U, B ∩ f ⁻¹' U, ha', hb', hga, hgb, hAQ, hBQ,
    hdis.mono inter_subset_left inter_subset_left, hA', hB', hgA, hgB, ?_, ?_⟩
  · rw [himgA, himgB]
    apply hc.congr <;> filter_upwards [hU.mem_nhds hyU] with z hz <;> simp only [mem_inter_iff, hz,
      and_true]
  · filter_upwards [hcov, hU.mem_nhds hyU] with z hz hzU x hx
    have hx' : x ∈ P ∩ f ⁻¹' {z} := (hUsub hzU).superset hx
    have hxU : f x ∈ U := (mem_singleton_iff.mp hx'.2).symm ▸ hzU
    exact (hz hx').elim (fun h => Or.inl ⟨h, hxU⟩) (fun h => Or.inr ⟨h, hxU⟩)

private theorem hasPLBoundaryDoubleCrossingAt_of_eventually_eq_fiber {f g : E → F}
    {P Q : Set E} {M : Set F} {y : F} (hg : ContinuousOn g Q)
    (hfiber : ∀ᶠ z in 𝓝 y, P ∩ f ⁻¹' {z} = Q ∩ g ⁻¹' {z})
    (hcross : HasPLBoundaryDoubleCrossingAt f P M y) :
    HasPLBoundaryDoubleCrossingAt g Q M y := by
  obtain ⟨U, hUsub, hU, hyU⟩ := mem_nhds_iff.mp hfiber
  obtain ⟨a, b, A, B, ha, hb, hfa, hfb, hAP, hBP, hdis, hA, hB, hfA, hfB, hc, hcov⟩ := hcross
  obtain ⟨ha', hga, hAQ, hA', hgA, himgA⟩ :=
    crossing_sheet_of_eq_fiber hU hyU hUsub hg ha hfa hAP hA hfA
  obtain ⟨hb', hgb, hBQ, hB', hgB, himgB⟩ :=
    crossing_sheet_of_eq_fiber hU hyU hUsub hg hb hfb hBP hB hfB
  refine ⟨a, b, A ∩ f ⁻¹' U, B ∩ f ⁻¹' U, ha', hb', hga, hgb, hAQ, hBQ,
    hdis.mono inter_subset_left inter_subset_left, hA', hB', hgA, hgB, ?_, ?_⟩
  · rw [himgA, himgB]
    apply hc.congr (Filter.Eventually.of_forall fun _ => Iff.rfl) <;>
      filter_upwards [hU.mem_nhds hyU] with z hz <;> simp only [mem_inter_iff, hz, and_true]
  · filter_upwards [hcov, hU.mem_nhds hyU] with z hz hzU x hx
    have hx' : x ∈ P ∩ f ⁻¹' {z} := (hUsub hzU).superset hx
    have hxU : f x ∈ U := (mem_singleton_iff.mp hx'.2).symm ▸ hzU
    exact (hz hx').elim (fun h => Or.inl ⟨h, hxU⟩) (fun h => Or.inr ⟨h, hxU⟩)

end FiberGerms

private theorem eventually_eq_fiber_in_chart {X E : Type*} [TopologicalSpace X]
    {d : ℕ}
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin d)))
    {f g : E → X} (P : Set E) {y : X} (hy : y ∈ e.source)
    (hfiber : ∀ᶠ z in 𝓝 y, f ⁻¹' {z} = g ⁻¹' {z}) :
    ∀ᶠ z in 𝓝 (e y), (P ∩ f ⁻¹' e.source) ∩ (e ∘ f) ⁻¹' {z} =
      (P ∩ g ⁻¹' e.source) ∩ (e ∘ g) ⁻¹' {z} := by
  have hback : ∀ᶠ z in 𝓝 (e y), f ⁻¹' {e.symm z} = g ⁻¹' {e.symm z} := by
    have h := (e.continuousAt_symm (e.map_source hy))
      (show ∀ᶠ z in 𝓝 (e.symm (e y)), f ⁻¹' {z} = g ⁻¹' {z} from by rwa [e.left_inv hy])
    exact h
  filter_upwards [e.open_target.mem_nhds (e.map_source hy), hback] with z hz heq
  have hiff (u : E → X) (x : E) :
      x ∈ (P ∩ u ⁻¹' e.source) ∩ (e ∘ u) ⁻¹' {z} ↔ x ∈ P ∧ u x = e.symm z := by
    constructor
    · rintro ⟨⟨hxP, hxu⟩, hxz⟩
      refine ⟨hxP, ?_⟩
      have hxz' : e (u x) = z := hxz
      rw [← hxz', e.left_inv hxu]
    · rintro ⟨hxP, hxu⟩
      refine ⟨⟨hxP, ?_⟩, ?_⟩
      · change u x ∈ e.source
        rw [hxu]
        exact e.map_target hz
      · change e (u x) = z
        rw [hxu, e.right_inv hz]
  ext x
  rw [hiff f, hiff g]
  exact and_congr_right fun _ => Set.ext_iff.mp heq x

private theorem crossings_in_chart_congr_of_eventually_eq_fiber
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {d : ℕ}
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin d)))
    {f g : E → X} {P : Set E} (hf : ContinuousOn f P) (hg : ContinuousOn g P)
    {y : X} (hy : y ∈ e.source) (hfiber : ∀ᶠ z in 𝓝 y, f ⁻¹' {z} = g ⁻¹' {z}) :
    (HasPLDoubleCrossingAt (e ∘ f) (P ∩ f ⁻¹' e.source) (e y) ↔
      HasPLDoubleCrossingAt (e ∘ g) (P ∩ g ⁻¹' e.source) (e y)) ∧
      ∀ M, HasPLBoundaryDoubleCrossingAt (e ∘ f) (P ∩ f ⁻¹' e.source) M (e y) ↔
        HasPLBoundaryDoubleCrossingAt (e ∘ g) (P ∩ g ⁻¹' e.source) M (e y) := by
  have heq := eventually_eq_fiber_in_chart e P hy hfiber
  have heq' := heq.mono fun _ h => h.symm
  have hfc : ContinuousOn (e ∘ f) (P ∩ f ⁻¹' e.source) :=
    e.continuousOn.comp (hf.mono inter_subset_left) (fun _ hx => hx.2)
  have hgc : ContinuousOn (e ∘ g) (P ∩ g ⁻¹' e.source) :=
    e.continuousOn.comp (hg.mono inter_subset_left) (fun _ hx => hx.2)
  exact ⟨⟨hasPLDoubleCrossingAt_of_eventually_eq_fiber hgc heq,
    hasPLDoubleCrossingAt_of_eventually_eq_fiber hfc heq'⟩,
    fun _ => ⟨hasPLBoundaryDoubleCrossingAt_of_eventually_eq_fiber hgc heq,
      hasPLBoundaryDoubleCrossingAt_of_eventually_eq_fiber hfc heq'⟩⟩

theorem SingularTwoCell.exists_small_boundary_doubleCrossing_away_from_isClosed
    {X : Type*} [MetricSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    [HasGroupoid X (plGroupoid 3)] (D : SingularTwoCell X) {C Q : Set X}
    (hmap : MapsTo D D.domain C)
    (hproper : D.domain ∩ D ⁻¹' frontier C = frontier D.domain)
    (hloc : IsLocallyInjective (D.domain.domRestrict D))
    (hcard : ∀ z, (D.domain ∩ D ⁻¹' {z}).encard ≤ 2)
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 3)))
    (he : e ∈ (plGroupoid 3).maximalAtlas X)
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hC : ∀ x ∈ e.source, x ∈ C ↔ 0 ≤ ℓ (e x))
    (hBd : ∀ x ∈ e.source, x ∈ frontier C ↔ ℓ (e x) = 0)
    {y : X} (hy : y ∈ doublePointSet D D.domain) (hye : y ∈ e.source)
    (hQ : IsClosed Q) (hyQ : y ∉ Q) {V : Set X} (hV : V ∈ 𝓝 y) :
    ∃ O W : Set X, IsOpen O ∧ Q ⊆ O ∧ IsOpen W ∧ y ∈ W ∧
      closure W ⊆ V ∧ Disjoint O W ∧ W ⊆ e.source ∧
      ∀ ε : ℝ, 0 < ε → ∃ (A : SingularTwoCell X)
        (G : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))),
        A.domain = D.domain ∧ (∀ x, dist (A x) (D x) < ε) ∧
        MapsTo A A.domain C ∧ A.domain ∩ A ⁻¹' frontier C = frontier A.domain ∧
        A '' A.domain ∩ frontier C = range A.boundary ∧
        (∀ z ∉ V, A ⁻¹' {z} = D ⁻¹' {z}) ∧
        (∀ z ∈ O, A ⁻¹' {z} = D ⁻¹' {z}) ∧
        IsLocallyInjective (A.domain.domRestrict A) ∧
        (∀ z, (A.domain ∩ A ⁻¹' {z}).encard ≤ 2) ∧
        G.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 1 G ∧
        (∀ z ∈ W, z ∈ doublePointSet A A.domain ↔ e z ∈ G.space) ∧
        (∀ z ∈ W ∩ doublePointSet A A.domain,
          (z ∈ frontier C ∧ HasPLBoundaryDoubleCrossingAt (e ∘ A)
            (A.domain ∩ A ⁻¹' e.source) (e '' (e.source ∩ C)) (e z)) ∨
          (z ∉ frontier C ∧ HasPLDoubleCrossingAt (e ∘ A)
            (A.domain ∩ A ⁻¹' e.source) (e z))) ∧
        (∀ z ∈ O, ∀ c : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 3)), z ∈ c.source →
          (HasPLDoubleCrossingAt (c ∘ D) (D.domain ∩ D ⁻¹' c.source) (c z) ↔
            HasPLDoubleCrossingAt (c ∘ A) (A.domain ∩ A ⁻¹' c.source) (c z)) ∧
          ∀ M, HasPLBoundaryDoubleCrossingAt (c ∘ D) (D.domain ∩ D ⁻¹' c.source) M (c z) ↔
            HasPLBoundaryDoubleCrossingAt (c ∘ A) (A.domain ∩ A ⁻¹' c.source) M (c z)) ∧
        ∃ H : ContinuousMap (unitInterval × frontier D.domain) X,
          (∀ x, H (0, x) = D x) ∧ (∀ x, H (1, x) = A x) ∧
          ∀ t x, dist (H (t, x)) (D x) < ε ∧ H (t, x) ∈ frontier C ∧
            (D x ∈ O → H (t, x) = D x) := by
  obtain ⟨B, hBy, hB, hBsub⟩ :=
    exists_mem_nhds_isClosed_subset (Filter.inter_mem hV (hQ.isOpen_compl.mem_nhds hyQ))
  have hIy : interior B ∈ 𝓝 y := interior_mem_nhds.mpr hBy
  have hIBV : interior B ⊆ V := fun _ hz => (hBsub (interior_subset hz)).1
  let O := Bᶜ
  have hO : IsOpen O := hB.isOpen_compl
  have hQO : Q ⊆ O := fun z hz hzB => (hBsub hzB).2 hz
  obtain ⟨W, hW, hyW, hWI, hWe, hsmall⟩ :=
    D.exists_small_boundary_doubleCrossing_in_chart hmap hproper hloc hcard e he ℓ hℓ hC hBd
      hy hye hIy
  have hOW : Disjoint O W := Set.disjoint_left.mpr fun _ hzO hzW =>
    hzO (interior_subset (hWI (subset_closure hzW)))
  refine ⟨O, W, hO, hQO, hW, hyW, hWI.trans hIBV, hOW, hWe, fun ε hε => ?_⟩
  obtain ⟨A, G, hdom, hclose, hAC, hAbd, hAimage, hfix, hAloc, hAcard,
    hGfin, hGman, hGspace, hcross, H, hHzero, hHone, hH⟩ := hsmall ε hε
  have hfixO : ∀ z ∈ O, A ⁻¹' {z} = D ⁻¹' {z} :=
    fun z hz => hfix z (fun hzI => hz (interior_subset hzI))
  refine ⟨A, G, hdom, hclose, hAC, hAbd, hAimage,
    fun z hz => hfix z (fun hzI => hz (hIBV hzI)), hfixO, hAloc, hAcard,
    hGfin, hGman, hGspace, hcross, ?_, H, hHzero, hHone, ?_⟩
  · intro z hz c hzc
    have hAg : ContinuousOn A D.domain := hdom ▸ A.continuousOn
    have hlocal : ∀ᶠ w in 𝓝 z, D ⁻¹' {w} = A ⁻¹' {w} :=
      Filter.Eventually.mono (hO.mem_nhds hz) fun w hw => (hfixO w hw).symm
    simpa only [hdom] using
      crossings_in_chart_congr_of_eventually_eq_fiber c D.continuousOn hAg hzc hlocal
  · intro t x
    refine ⟨(hH t x).1, (hH t x).2.1, ?_⟩
    intro hxO
    exact (hH t x).2.2.2 (fun hxI => hxO (interior_subset hxI))

namespace NormalSystem

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_doubleCoverReduction_boundary_crossing_away_from_isClosed_of_not_isPLSphere
    (S : NormalSystem E)
    (hproper : S.sourceComplex.space ∩ S.singularMap ⁻¹' S.boundaryComplex.space =
      frontier S.sourceComplex.space)
    (hbase : S.basepoint = S.boundaryLoop 0)
    (hnot : ¬IsPLSphere 2 S.boundaryComponent) :
    ∃ (N : ℕ) (T : NormalSystem (EuclideanSpace ℝ (Fin N))) (R : DoubleCoverReduction S T),
      T.basepoint = T.boundaryLoop 0 ∧
      T.sourceComplex.space ∩ T.singularMap ⁻¹' T.boundaryComplex.space =
        frontier T.sourceComplex.space ∧
      ∀ D : EmbeddedDisk T,
        let K := S.manifoldComplex
        letI : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
        letI := combinatorialChartedSpace (double 3 K)
          (isCombinatorialManifold_double_succ_succ K S.isManifold)
        let ι := simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
        let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
        ∃ (G : SingularTwoCell (double 3 K).space) (γ : freeLoop S.boundaryNeighborhoodSpace)
          (q : Path S.basepoint (γ 0)),
          G.domain = D.domain ∧ γ = R.boundaryMap.comp D.boundaryLoop ∧
          EqOn (fun x => (G x : E × E × ℝ)) (ι ∘ R.projection ∘ D.map) D.domain ∧
          MapsTo G G.domain C ∧ G.domain ∩ G ⁻¹' frontier C = frontier G.domain ∧
          IsLocallyInjective (G.domain.domRestrict G) ∧
          (∀ y, (G.domain ∩ G ⁻¹' {y}).encard ≤ 2) ∧
          ¬conjugacyClassMeets (normalSystemLoopConjugacyClass S.basepoint γ q) S.normalSubgroup ∧
          ∀ y ∈ doublePointSet G G.domain ∩ frontier C,
            ∃ (e : OpenPartialHomeomorph (double 3 K).space (EuclideanSpace ℝ (Fin 3)))
              (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ),
              e ∈ (plGroupoid 3).maximalAtlas (double 3 K).space ∧ ℓ ≠ 0 ∧ y ∈ e.source ∧
              (∀ x ∈ e.source, x ∈ C ↔ 0 ≤ ℓ (e x)) ∧
              (∀ x ∈ e.source, x ∈ frontier C ↔ ℓ (e x) = 0) ∧
              ∀ Q : Set (double 3 K).space, IsClosed Q → y ∉ Q →
              ∀ V : Set (double 3 K).space, V ∈ 𝓝 y →
              ∃ O W : Set (double 3 K).space,
                IsOpen O ∧ Q ⊆ O ∧ IsOpen W ∧ y ∈ W ∧ closure W ⊆ V ∧
                Disjoint O W ∧ W ⊆ e.source ∧
              ∀ ε : ℝ, 0 < ε → ∃ (A : SingularTwoCell (double 3 K).space)
                (J : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
                (δ : freeLoop S.boundaryNeighborhoodSpace) (r : Path S.basepoint (δ 0)),
                A.domain = D.domain ∧ (∀ x, dist (A x) (G x) < ε) ∧
                MapsTo A A.domain C ∧ A.domain ∩ A ⁻¹' frontier C = frontier A.domain ∧
                A '' A.domain ∩ frontier C = range A.boundary ∧
                (∀ z ∉ V, A ⁻¹' {z} = G ⁻¹' {z}) ∧
                (∀ z ∈ O, A ⁻¹' {z} = G ⁻¹' {z}) ∧
                IsLocallyInjective (A.domain.domRestrict A) ∧
                (∀ z, (A.domain ∩ A ⁻¹' {z}).encard ≤ 2) ∧
                J.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 1 J ∧
                (∀ z ∈ W, z ∈ doublePointSet A A.domain ↔ e z ∈ J.space) ∧
                (∀ z ∈ W ∩ doublePointSet A A.domain,
                  (z ∈ frontier C ∧ HasPLBoundaryDoubleCrossingAt (e ∘ A)
                    (A.domain ∩ A ⁻¹' e.source) (e '' (e.source ∩ C)) (e z)) ∨
                  (z ∉ frontier C ∧ HasPLDoubleCrossingAt (e ∘ A)
                    (A.domain ∩ A ⁻¹' e.source) (e z))) ∧
                (∀ z ∈ O,
                  ∀ c : OpenPartialHomeomorph (double 3 K).space (EuclideanSpace ℝ (Fin 3)),
                    z ∈ c.source →
                    (HasPLDoubleCrossingAt (c ∘ G) (G.domain ∩ G ⁻¹' c.source) (c z) ↔
                      HasPLDoubleCrossingAt (c ∘ A) (A.domain ∩ A ⁻¹' c.source) (c z)) ∧
                    ∀ M, HasPLBoundaryDoubleCrossingAt (c ∘ G)
                      (G.domain ∩ G ⁻¹' c.source) M (c z) ↔
                      HasPLBoundaryDoubleCrossingAt (c ∘ A)
                        (A.domain ∩ A ⁻¹' c.source) M (c z)) ∧
                γ.Homotopic δ ∧
                range (fun θ => (δ θ : E)) =
                  range (fun x : frontier A.domain => glueSnd E E (A x)) ∧
                range (fun x => (A.boundary x : E × E × ℝ)) = ι '' range (fun θ => (δ θ : E)) ∧
                ¬conjugacyClassMeets (normalSystemLoopConjugacyClass S.basepoint δ r)
                  S.normalSubgroup := by
  classical
  obtain ⟨N, T, R, hbaseT, hproperT, hbuffer⟩ :=
    S.exists_doubleCoverReduction_boundary_mem_nhdsWithin_of_not_isPLSphere hproper hbase hnot
  refine ⟨N, T, R, hbaseT, hproperT, fun D => ?_⟩
  intro K
  let _ : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
  let _ := combinatorialChartedSpace (double 3 K)
    (isCombinatorialManifold_double_succ_succ K S.isManifold)
  let _ := combinatorialChartedSpace_hasGroupoid (double 3 K)
    (isCombinatorialManifold_double_succ_succ K S.isManifold)
  let ι := simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
  let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
  obtain ⟨G, γ, q, β, ρ, hdom, hγ, hGeq, hmap, hGproper, hloc, hcard,
    havoid, -, -, hρ, hhomotopy⟩ :=
    R.toDoubleCoverDiagram.exists_projected_boundary_loop_homotopy hbuffer D
  refine ⟨G, γ, q, hdom, hγ, hGeq, hmap, hGproper, hloc, hcard, havoid, ?_⟩
  intro y hy
  let p : K.space := ⟨S.basepoint, boundaryComplex_space_subset 3 K
    (derivedNeighborhood_space_subset S.boundaryComplex S.loopComplex S.basepoint.property)⟩
  obtain ⟨e, ℓ, he, hℓ, hye, hC, hBd⟩ :=
    exists_halfSpace_chart_glued₂_space_in_double K S.isManifold p y hy.2
  refine ⟨e, ℓ, he, hℓ, hye, hC, hBd, fun Q hQ hyQ V hV => ?_⟩
  obtain ⟨O, W, hO, hQO, hW, hyW, hWV, hOW, hWe, hsmall⟩ :=
    G.exists_small_boundary_doubleCrossing_away_from_isClosed hmap hGproper hloc hcard
      e he ℓ hℓ hC hBd hy.1 hye hQ hyQ hV
  refine ⟨O, W, hO, hQO, hW, hyW, hWV, hOW, hWe, fun ε hε => ?_⟩
  obtain ⟨A, J, hAdom, hclose, hAmap, hAproper, hAinter, hfiber, hfixed, hAloc, hAcard,
    hJfin, hJman, hJspace, hcross, hpres, H, hHzero, hHone, hH⟩ :=
    hsmall (min ε ρ) (lt_min hε hρ)
  obtain ⟨δ, r, hhom, -, hδrange, hδavoid⟩ := hhomotopy H hHzero
    (fun t x => (hH t x).2.1) (fun t x => (hH t x).1.trans_le (min_le_right _ _))
  have hδrangeA : range (fun θ => (δ θ : E)) =
      range (fun x : frontier A.domain => glueSnd E E (A x)) := by
    rw [hδrange]
    apply Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      refine ⟨⟨x, by rw [hAdom]; exact x.property⟩, ?_⟩
      exact (congrArg (fun z : (double 3 K).space => glueSnd E E z) (hHone x)).symm
    · rintro _ ⟨x, rfl⟩
      let xG : frontier G.domain := ⟨x, (congrArg frontier hAdom).subset x.property⟩
      exact ⟨xG, congrArg (fun z : (double 3 K).space => glueSnd E E z) (hHone xG)⟩
  have hιπA (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ A.domain) :
      ι (glueSnd E E (A x)) = (A x : E × E × ℝ) := by
    obtain ⟨z, hz, hzx⟩ := hAmap hx
    rw [← hzx, glueSnd_simplicialMap K (PiecewiseLinear.boundaryComplex 3 K) id hz]
  have hboundary : range (fun x => (A.boundary x : E × E × ℝ)) =
      ι '' range (fun θ => (δ θ : E)) := by
    rw [hδrangeA]
    apply Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      exact ⟨glueSnd E E (A x), ⟨x, rfl⟩, hιπA x (A.frontier_subset_domain x.property)⟩
    · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, (hιπA x (A.frontier_subset_domain x.property)).symm⟩
  exact ⟨A, J, δ, r, hAdom.trans hdom, fun x => (hclose x).trans_le (min_le_left _ _),
    hAmap, hAproper, hAinter, hfiber, hfixed, hAloc, hAcard, hJfin, hJman, hJspace, hcross,
    hpres, hhom, hδrangeA, hboundary, hδavoid⟩

end NormalSystem

end DifferentialGeometry.Topology.PiecewiseLinear
