/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CombinatorialPiece
import DifferentialGeometry.Topology.PiecewiseLinear.VertexChartTransport
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularSetTriangulation

open Set Topology
namespace DifferentialGeometry.Topology.PiecewiseLinear
universe u
theorem eq_span_singleton_of_finrank_eq_one {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {L : Submodule ℝ F}
    (hL : Module.finrank ℝ L = 1) {u : F} (hu : u ∈ L) (hu0 : u ≠ 0) : (ℝ ∙ u) = L :=
  Submodule.eq_of_le_of_finrank_eq
    ((Submodule.span_le).mpr (Set.singleton_subset_iff.mpr hu))
    (by rw [finrank_span_singleton hu0, hL])
theorem exists_ne_zero_mem_of_finrank_eq_one {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {L : Submodule ℝ F} (hL : Module.finrank ℝ L = 1) :
    ∃ u ∈ L, u ≠ 0 := by
  refine (Submodule.ne_bot_iff L).mp fun hbot => ?_
  rw [hbot, finrank_bot] at hL
  exact zero_ne_one hL
section ChartGerm
variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM : Set M}
theorem SingularTwoCell.exists_chart_ray_germ_doublePointSet
    (himage : D '' D.domain ∩ BdM = Set.range D.boundary)
    (hcross : ∀ y ∈ doublePointSet D D.domain,
      ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
        HasPLNormalDoubleCrossingAt (e ∘ D) (D.domain ∩ D ⁻¹' e.source)
          (e '' (e.source ∩ BdM)) (e y))
    {y : M} (hy : y ∈ doublePointSet D D.domain) :
    ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
      ∃ (hmap : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
        (u : EuclideanSpace ℝ (Fin 3)) (U V W : Set (EuclideanSpace ℝ (Fin 3))),
        u ≠ 0 ∧ IsOpen U ∧ IsOpen V ∧ IsOpen W ∧ e y ∈ U ∧ e y ∈ W ∧
          IsPLHomeomorphOn hmap U V ∧ hmap (e y) = 0 ∧
            ∀ w ∈ W, (w ∈ e '' (doublePointSet D D.domain ∩ e.source) ↔
              ∃ t : ℝ, (y ∈ BdM → 0 ≤ t) ∧ hmap w = t • u) := by
  obtain ⟨e, he, hye, hmap, L, hLdim, hh0, ⟨U, V, hU, hV, hyU, hPL⟩, hcase⟩ :=
    SingularTwoCell.exists_chart_germ_doublePointSet himage hcross hy
  rcases hcase with ⟨hyB, hgerm⟩ | ⟨hyB, ℓ, ⟨u, huL, hℓu⟩, hgerm⟩
  · obtain ⟨u, huL, hu0⟩ := exists_ne_zero_mem_of_finrank_eq_one hLdim
    have hspan : (ℝ ∙ u) = L := eq_span_singleton_of_finrank_eq_one hLdim huL hu0
    obtain ⟨W, hWsub, hW, hyW⟩ := mem_nhds_iff.mp hgerm
    refine ⟨e, he, hye, hmap, u, U, V, W, hu0, hU, hV, hW, hyU, hyW, hPL, hh0, ?_⟩
    intro w hwW
    have hiff : w ∈ e '' (doublePointSet D D.domain ∩ e.source) ↔ hmap w ∈ L := hWsub hwW
    rw [hiff, ← hspan, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, fun hmem => absurd hmem hyB, ht.symm⟩
    · rintro ⟨t, -, ht⟩
      exact ⟨t, ht.symm⟩
  · have hu0 : u ≠ 0 := by
      intro hzero
      rw [hzero, map_zero] at hℓu
      exact zero_ne_one hℓu
    have hspan : (ℝ ∙ u) = L := eq_span_singleton_of_finrank_eq_one hLdim huL hu0
    obtain ⟨W, hWsub, hW, hyW⟩ := mem_nhds_iff.mp hgerm
    refine ⟨e, he, hye, hmap, u, U, V, W, hu0, hU, hV, hW, hyU, hyW, hPL, hh0, ?_⟩
    intro w hwW
    have hiff : w ∈ e '' (doublePointSet D D.domain ∩ e.source) ↔
        hmap w ∈ L ∧ 0 ≤ ℓ (hmap w) := hWsub hwW
    rw [hiff]
    constructor
    · rintro ⟨hmem, hnonneg⟩
      rw [← hspan, Submodule.mem_span_singleton] at hmem
      obtain ⟨t, ht⟩ := hmem
      refine ⟨t, fun _ => ?_, ht.symm⟩
      rw [← ht, map_smul, hℓu, smul_eq_mul, mul_one] at hnonneg
      exact hnonneg
    · rintro ⟨t, hnonneg, ht⟩
      have htge : 0 ≤ t := hnonneg hyB
      refine ⟨?_, ?_⟩
      · rw [ht, ← hspan, Submodule.mem_span_singleton]
        exact ⟨t, rfl⟩
      · rw [ht, map_smul, hℓu, smul_eq_mul, mul_one]
        exact htge
end ChartGerm
section Ambient
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
open Classical in
theorem SingularTwoCell.exists_ambient_ray_germ_doublePointSet
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 3 K) :
    letI := combinatorialChartedSpace K hK
    ∀ (D : SingularTwoCell K.space) (BdM : Set K.space),
      D '' D.domain ∩ BdM = Set.range D.boundary →
      (∀ y ∈ doublePointSet D D.domain,
        ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) K.space, y ∈ e.source ∧
          HasPLNormalDoubleCrossingAt (e ∘ D) (D.domain ∩ D ⁻¹' e.source)
            (e '' (e.source ∩ BdM)) (e y)) →
      ∀ x ∈ Subtype.val '' doublePointSet D D.domain,
        ∃ (g : E → EuclideanSpace ℝ (Fin 3)) (u : EuclideanSpace ℝ (Fin 3)) (N : Set E),
          u ≠ 0 ∧ IsOpen N ∧ x ∈ N ∧ g x = 0 ∧
            IsPLHomeomorphOn g (N ∩ K.space) (g '' (N ∩ K.space)) ∧
              IsOpen (g '' (N ∩ K.space)) ∧
                ∀ z ∈ N, (z ∈ Subtype.val '' doublePointSet D D.domain ↔
                  z ∈ K.space ∧ ∃ t : ℝ,
                    (x ∈ Subtype.val '' BdM → 0 ≤ t) ∧ g z = t • u) := by
  let _ := combinatorialChartedSpace K hK
  intro D BdM himage hcross x hx
  obtain ⟨y, hyD, rfl⟩ := hx
  obtain ⟨e, he, hye, hmap, u, U, V, W, hu0, hU, hV, hW, hyU, hyW, hPL, hh0, hgerm⟩ :=
    SingularTwoCell.exists_chart_ray_germ_doublePointSet himage hcross hyD
  obtain ⟨p, hp, hpe⟩ := mem_combinatorialChartedSpace_atlas K hK he
  obtain ⟨eb, hebdef⟩ :
      ∃ f : E → EuclideanSpace ℝ (Fin 3),
        f = fun q => if hq : q ∈ K.space then (e ⟨q, hq⟩ : EuclideanSpace ℝ (Fin 3)) else 0 :=
    ⟨_, rfl⟩
  have hebval : ∀ q : K.space, eb (q : E) = e q := by
    intro q
    rw [hebdef]
    exact dite_eq_left q.2
  have hpa0 : IsPiecewiseAffineOn eb (Subtype.val '' e.source) := by
    rw [hebdef, hpe]
    exact isPiecewiseAffineOn_vertexChart K hp (hK.isPLSphere_link hp)
  have hpa0symm : IsPiecewiseAffineOn (fun w => ((e.symm w : K.space) : E)) e.target := by
    rw [hpe]
    exact isPiecewiseAffineOn_vertexChart_symm K hp (hK.isPLSphere_link hp)
  have hAopen : IsOpen (e.source ∩ e ⁻¹' (U ∩ W)) := e.isOpen_inter_preimage (hU.inter hW)
  obtain ⟨O, hOopen, hOA⟩ := isOpen_induced_iff.mp hAopen
  have hvalA : Subtype.val '' (e.source ∩ e ⁻¹' (U ∩ W)) = O ∩ K.space := by
    rw [← hOA, Subtype.image_preimage_coe]
    exact inter_comm _ _
  have hmemA : ∀ z ∈ O ∩ K.space, ∃ q : K.space, (q : E) = z ∧
      q ∈ e.source ∧ e q ∈ U ∧ e q ∈ W := by
    intro z hz
    rw [← hvalA] at hz
    obtain ⟨q, hq, hqz⟩ := hz
    exact ⟨q, hqz, hq.1, hq.2.1, hq.2.2⟩
  have hyO : (y : E) ∈ O ∩ K.space := by
    rw [← hvalA]
    exact ⟨y, ⟨hye, hyU, hyW⟩, rfl⟩
  have hsetEq : (Subtype.val '' e.source ∩ eb ⁻¹' U) ∩ O = O ∩ K.space := by
    apply Subset.antisymm
    · rintro z ⟨⟨⟨q, -, rfl⟩, -⟩, hzO⟩
      exact ⟨hzO, q.2⟩
    · intro z hz
      obtain ⟨q, hqz, hqsrc, hqU, -⟩ := hmemA z hz
      refine ⟨⟨⟨q, hqsrc, hqz⟩, ?_⟩, hz.1⟩
      change eb z ∈ U
      rw [← hqz, hebval q]
      exact hqU
  have hpa : IsPiecewiseAffineOn (hmap ∘ eb) (O ∩ K.space) := by
    rw [← hsetEq]
    exact (hPL.isPiecewiseAffineOn.comp hpa0).inter_of_isOpen hOopen
  have hinj : InjOn (hmap ∘ eb) (O ∩ K.space) := by
    intro a ha b hb hab
    obtain ⟨qa, hqa, hqasrc, hqaU, -⟩ := hmemA a ha
    obtain ⟨qb, hqb, hqbsrc, hqbU, -⟩ := hmemA b hb
    have hea : eb a = e qa := by rw [← hqa, hebval qa]
    have heb : eb b = e qb := by rw [← hqb, hebval qb]
    have hab' : hmap (e qa) = hmap (e qb) := by
      rw [← hea, ← heb]
      exact hab
    have hqab : qa = qb := e.injOn hqasrc hqbsrc (hPL.bijOn.injOn hqaU hqbU hab')
    rw [← hqa, ← hqb, hqab]
  have hebimg : eb '' (O ∩ K.space) = e '' (e.source ∩ e ⁻¹' (U ∩ W)) := by
    apply Subset.antisymm
    · rintro w ⟨z, hz, rfl⟩
      obtain ⟨q, hqz, hqsrc, hqU, hqW⟩ := hmemA z hz
      exact ⟨q, ⟨hqsrc, hqU, hqW⟩, by rw [← hqz, hebval q]⟩
    · rintro w ⟨q, hq, rfl⟩
      refine ⟨(q : E), ?_, hebval q⟩
      rw [← hvalA]
      exact ⟨q, hq, rfl⟩
  have himg : (hmap ∘ eb) '' (O ∩ K.space) = hmap '' (e '' (e.source ∩ e ⁻¹' (U ∩ W))) := by
    rw [image_comp, hebimg]
  have hAsubU : e '' (e.source ∩ e ⁻¹' (U ∩ W)) ⊆ U := by
    rintro _ ⟨q, hq, rfl⟩
    exact hq.2.1
  have hopenimg : IsOpen ((hmap ∘ eb) '' (O ∩ K.space)) := by
    rw [himg]
    exact hPL.isOpen_image_of_isOpen hV
      (e.isOpen_image_of_subset_source hAopen inter_subset_left) hAsubU
  have hinvU : ∀ z ∈ O ∩ K.space, ∀ q : K.space, (q : E) = z → q ∈ e.source →
      Function.invFunOn hmap U ((hmap ∘ eb) z) = e q := by
    intro z hz q hqz hqsrc
    obtain ⟨q', hq'z, hq'src, hq'U, -⟩ := hmemA z hz
    have hqq' : q = q' := Subtype.ext (hqz.trans hq'z.symm)
    subst hqq'
    have hexists : ∃ a ∈ U, hmap a = (hmap ∘ eb) z := by
      refine ⟨e q, hq'U, ?_⟩
      change hmap (e q) = hmap (eb z)
      rw [← hqz, hebval q]
    have hmem := Function.invFunOn_mem hexists
    have heq := Function.invFunOn_eq hexists
    refine hPL.bijOn.injOn hmem hq'U ?_
    rw [heq]
    change hmap (eb z) = hmap (e q)
    rw [← hqz, hebval q]
  have hinvpa : IsPiecewiseAffineOn (Function.invFunOn (hmap ∘ eb) (O ∩ K.space))
      ((hmap ∘ eb) '' (O ∩ K.space)) := by
    have h2 := hpa0symm.comp hPL.isPiecewiseAffineOn_invFunOn
    have hsub : (hmap ∘ eb) '' (O ∩ K.space) ⊆
        V ∩ Function.invFunOn hmap U ⁻¹' e.target := by
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨q, hqz, hqsrc, hqU, -⟩ := hmemA z hz
      constructor
      · have : (hmap ∘ eb) z = hmap (e q) := by
          change hmap (eb z) = hmap (e q)
          rw [← hqz, hebval q]
        rw [this]
        exact hPL.bijOn.mapsTo hqU
      · change Function.invFunOn hmap U ((hmap ∘ eb) z) ∈ e.target
        rw [hinvU z hz q hqz hqsrc]
        exact e.map_source hqsrc
    have h3 := h2.inter_of_isOpen hopenimg
    rw [inter_eq_right.mpr hsub] at h3
    refine h3.congr fun w hw => ?_
    obtain ⟨z, hz, rfl⟩ := hw
    obtain ⟨q, hqz, hqsrc, hqU, -⟩ := hmemA z hz
    have hfix : Function.invFunOn (hmap ∘ eb) (O ∩ K.space) ((hmap ∘ eb) z) = z := by
      have hexists : ∃ a ∈ O ∩ K.space, (hmap ∘ eb) a = (hmap ∘ eb) z := ⟨z, hz, rfl⟩
      exact hinj (Function.invFunOn_mem hexists) hz (Function.invFunOn_eq hexists)
    rw [hfix]
    change z = ((e.symm (Function.invFunOn hmap U ((hmap ∘ eb) z)) : K.space) : E)
    rw [hinvU z hz q hqz hqsrc, e.left_inv hqsrc, hqz]
  have hPLg : IsPLHomeomorphOn (hmap ∘ eb) (O ∩ K.space) ((hmap ∘ eb) '' (O ∩ K.space)) :=
    ⟨hinj.bijOn_image, hpa, hinvpa⟩
  have hBd : ((y : E) ∈ Subtype.val '' BdM) ↔ y ∈ BdM := by
    constructor
    · rintro ⟨z, hz, hzy⟩
      exact Subtype.val_injective hzy ▸ hz
    · intro h
      exact ⟨y, h, rfl⟩
  refine ⟨hmap ∘ eb, u, O, hu0, hOopen, hyO.1, ?_, hPLg, hopenimg, ?_⟩
  · change hmap (eb (y : E)) = 0
    rw [hebval y]
    exact hh0
  · intro z hzO
    by_cases hzK : z ∈ K.space
    · obtain ⟨q, hqz, hqsrc, -, hqW⟩ := hmemA z ⟨hzO, hzK⟩
      have hleft : (z ∈ Subtype.val '' doublePointSet D D.domain) ↔
          q ∈ doublePointSet D D.domain := by
        constructor
        · rintro ⟨w, hw, hwz⟩
          have : w = q := Subtype.ext (hwz.trans hqz.symm)
          exact this ▸ hw
        · intro h
          exact ⟨q, h, hqz⟩
      have hchart : (e q ∈ e '' (doublePointSet D D.domain ∩ e.source)) ↔
          q ∈ doublePointSet D D.domain := by
        constructor
        · rintro ⟨w, hw, hwq⟩
          have : w = q := e.injOn hw.2 hqsrc hwq
          exact this ▸ hw.1
        · intro h
          exact ⟨q, ⟨h, hqsrc⟩, rfl⟩
      rw [hleft, ← hchart, hgerm (e q) hqW]
      constructor
      · rintro ⟨t, ht, hteq⟩
        refine ⟨hzK, t, fun hmem => ht (hBd.mp hmem), ?_⟩
        change hmap (eb z) = t • u
        rw [← hqz, hebval q]
        exact hteq
      · rintro ⟨-, t, ht, hteq⟩
        refine ⟨t, fun hmem => ht (hBd.mpr hmem), ?_⟩
        change hmap (eb z) = t • u at hteq
        rw [← hqz, hebval q] at hteq
        exact hteq
    · constructor
      · rintro ⟨w, -, hwz⟩
        exact absurd (hwz ▸ w.2) hzK
      · rintro ⟨hz, -⟩
        exact absurd hz hzK
open Classical in
theorem SingularTwoCell.card_le_two_of_space_eq_image_doublePointSet
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 3 K) :
    letI := combinatorialChartedSpace K hK
    ∀ (D : SingularTwoCell K.space) (BdM : Set K.space)
      (G : Geometry.SimplicialComplex ℝ E),
      D '' D.domain ∩ BdM = Set.range D.boundary →
      (∀ y ∈ doublePointSet D D.domain,
        ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) K.space, y ∈ e.source ∧
          HasPLNormalDoubleCrossingAt (e ∘ D) (D.domain ∩ D ⁻¹' e.source)
            (e '' (e.source ∩ BdM)) (e y)) →
      G.space = Subtype.val '' doublePointSet D D.domain →
      ∀ s ∈ G.faces, s.card ≤ 2 := by
  let _ := combinatorialChartedSpace K hK
  intro D BdM G himage hcross hspace s hs
  refine card_le_two_of_locally_injOn_into_line (F := EuclideanSpace ℝ (Fin 3)) G
    (fun x hx => ?_) hs
  obtain ⟨g, u, N, hu0, hNopen, hxN, -, hPLg, -, hgerm⟩ :=
    SingularTwoCell.exists_ambient_ray_germ_doublePointSet K hK D BdM himage hcross x
      (hspace ▸ hx)
  refine ⟨g, ℝ ∙ u, N ∩ K.space, finrank_span_singleton hu0, ?_, hPLg.isPiecewiseAffineOn,
    hPLg.bijOn.injOn, ?_⟩
  · refine mem_nhdsWithin.mpr ⟨N, hNopen, hxN, ?_⟩
    rintro z ⟨hzN, hzG⟩
    rw [hspace] at hzG
    obtain ⟨w, -, hwz⟩ := hzG
    exact ⟨hzN, hwz ▸ w.2⟩
  · intro z hz hzG
    rw [hspace] at hzG
    obtain ⟨-, t, -, hteq⟩ := (hgerm z hz.1).mp hzG
    rw [Submodule.mem_span_singleton]
    exact ⟨t, hteq.symm⟩
end Ambient
end DifferentialGeometry.Topology.PiecewiseLinear
