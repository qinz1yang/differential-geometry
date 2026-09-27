/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GluedCellGlobalInvariants
import DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition
import DifferentialGeometry.Topology.Covering.EmbeddedProjection

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

open Classical in
theorem exists_uniformInjectivityScale_and_fiber_encard_le_two_of_close {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MetricSpace F]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (f : E → F)
    (hf : ContinuousOn f K.space) (hcard : ∀ y : F, (K.space ∩ f ⁻¹' {y}).encard ≤ 2) :
    ∃ κ ε : ℝ, 0 < κ ∧ 0 < ε ∧ ∀ g : E → F, (∀ x ∈ K.space, dist (g x) (f x) < ε) →
      StarInj K g → UniformInjectivityScale K.space g κ ∧
        ∀ y : F, (K.space ∩ g ⁻¹' {y}).encard ≤ 2 := by
  have : CompactSpace K.space := isCompact_iff_compactSpace.mp (isPolyhedron_space K).isCompact
  obtain ⟨η, hη, hηinj⟩ := exists_pos_eq_of_dist_lt_of_injOn_starComplex (F := F) K
  let C : Set (K.space × K.space × K.space) := {p |
    η ≤ dist p.1 p.2.1 ∧ η ≤ dist p.1 p.2.2 ∧ η ≤ dist p.2.1 p.2.2}
  have hC : IsClosed C :=
    (isClosed_le continuous_const (continuous_fst.dist (continuous_fst.comp continuous_snd))).inter
      ((isClosed_le continuous_const (continuous_fst.dist (continuous_snd.comp
        continuous_snd))).inter
        (isClosed_le continuous_const
          ((continuous_fst.comp continuous_snd).dist (continuous_snd.comp continuous_snd))))
  let f₀ : K.space → F := K.space.domRestrict f
  have hf₀ : Continuous f₀ := hf.comp_continuous continuous_subtype_val (fun x => x.property)
  let r : K.space × K.space × K.space → ℝ := fun p =>
    dist (f₀ p.1) (f₀ p.2.1) + dist (f₀ p.1) (f₀ p.2.2)
  have hr : Continuous r :=
    ((hf₀.comp continuous_fst).dist (hf₀.comp (continuous_fst.comp continuous_snd))).add
      ((hf₀.comp continuous_fst).dist (hf₀.comp (continuous_snd.comp continuous_snd)))
  have hrpos : ∀ p ∈ C, 0 < r p := by
    rintro ⟨x, y, z⟩ hp
    have hxy : (x : E) ≠ y := by
      intro heq
      have h := hp.1
      change η ≤ dist (x : E) y at h
      rw [heq, dist_self] at h
      exact (not_le_of_gt hη) h
    have hxz : (x : E) ≠ z := by
      intro heq
      have h := hp.2.1
      change η ≤ dist (x : E) z at h
      rw [heq, dist_self] at h
      exact (not_le_of_gt hη) h
    have hyz : (y : E) ≠ z := by
      intro heq
      have h := hp.2.2
      change η ≤ dist (y : E) z at h
      rw [heq, dist_self] at h
      exact (not_le_of_gt hη) h
    by_contra hpos
    have hle : dist (f x) (f y) + dist (f x) (f z) ≤ 0 := le_of_not_gt hpos
    have hxy0 : 0 ≤ dist (f x) (f y) := dist_nonneg
    have hxz0 : 0 ≤ dist (f x) (f z) := dist_nonneg
    have hxyf : f x = f y := dist_eq_zero.mp (by linarith)
    have hxzf : f x = f z := dist_eq_zero.mp (by linarith)
    have hsub : ({(x : E), (y : E), (z : E)} : Set E) ⊆ K.space ∩ f ⁻¹' {f x} := by
      intro w hw
      rcases hw with rfl | rfl | rfl
      · exact ⟨x.property, rfl⟩
      · exact ⟨y.property, hxyf.symm⟩
      · exact ⟨z.property, hxzf.symm⟩
    have hbound := (encard_mono hsub).trans (hcard (f x))
    rw [encard_insert_of_notMem (by simp [hxy, hxz]), encard_pair hyz] at hbound
    norm_num at hbound
  obtain ⟨m, hm, hmin⟩ : ∃ m : ℝ, 0 < m ∧ ∀ p ∈ C, m ≤ r p := by
    by_cases hne : C.Nonempty
    · obtain ⟨p, hp, hmin⟩ := hC.isCompact.exists_isMinOn hne hr.continuousOn
      exact ⟨r p, hrpos p hp, fun q hq => hmin hq⟩
    · exact ⟨1, zero_lt_one, fun p hp => False.elim (hne ⟨p, hp⟩)⟩
  refine ⟨η, m / 4, hη, by positivity, fun g hclose hstar => ⟨?_, fun y => ?_⟩⟩
  · exact fun x hx y hy hdist hxy => hηinj g hstar x hx y hy hdist hxy
  let A := K.space ∩ g ⁻¹' {y}
  by_cases hsub : A.Subsingleton
  · exact (encard_le_one_iff_subsingleton.mpr hsub).trans (by norm_num)
  obtain ⟨x, hx, z, hz, hxz⟩ := Set.not_subsingleton_iff.mp hsub
  have hsubset : A ⊆ {x, z} := by
    intro w hw
    by_cases hwx : w = x
    · exact Or.inl hwx
    by_cases hwz : w = z
    · exact Or.inr hwz
    have hgxz : g x = g z := hx.2.trans hz.2.symm
    have hgxw : g x = g w := hx.2.trans hw.2.symm
    have hp : (⟨x, hx.1⟩, ⟨z, hz.1⟩, ⟨w, hw.1⟩) ∈ C := by
      refine ⟨le_of_not_gt ?_, le_of_not_gt ?_, le_of_not_gt ?_⟩
      · intro hdist
        exact hxz (hηinj g hstar x hx.1 z hz.1 hdist hgxz)
      · intro hdist
        exact hwx (hηinj g hstar x hx.1 w hw.1 hdist hgxw).symm
      · intro hdist
        exact hwz (hηinj g hstar z hz.1 w hw.1 hdist (hz.2.trans hw.2.symm)).symm
    have hdist : ∀ a ∈ K.space, ∀ b ∈ K.space, g a = g b → dist (f a) (f b) < m / 2 := by
      intro a ha b hb hab
      have htriangle := dist_triangle (f a) (g a) (f b)
      rw [dist_comm (f a) (g a), hab] at htriangle
      have ha' := hclose a ha
      have hb' := hclose b hb
      rw [hab] at ha'
      linarith
    have hbound := hmin _ hp
    change m ≤ dist (f x) (f z) + dist (f x) (f w) at hbound
    have h1 := hdist x hx.1 z hz.1 hgxz
    have h2 := hdist x hx.1 w hw.1 hgxw
    linarith
  exact (encard_mono hsubset).trans_eq (encard_pair hxz)

section MetricAmbient

variable {M : Type u} [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem exists_normalizationPreparation_on_prescribedRegion [CompactSpace M]
    (D : SingularTwoCell M) {BdM B W V : Set M}
    (hloc : ∀ x ∈ D.domain, ∃ U ∈ 𝓝[D.domain] x, InjOn (⇑D) U)
    (hfiber : ∀ y, (D.domain ∩ ⇑D ⁻¹' {y}).encard ≤ 2)
    (hbuffer : ∀ z ∈ Set.range D.boundary, B ∈ 𝓝[BdM] z)
    (hVopen : IsOpen V) (hWV : closure W ⊆ V)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))) (hVec : V ⊆ ec.source)
    (Rc Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (hRfin : Rc.faces.Finite) (hAR : Ac.faces ⊆ Rc.faces)
    (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hAfree : Disjoint Ac.space (⇑D ⁻¹' closure W)) :
    ∃ (T : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) (κ δ ε : ℝ),
      0 < κ ∧ 0 < δ ∧ 0 < ε ∧ T.faces.Finite ∧ T.space = D.domain ∧ StarInj T (⇑D) ∧
        (∀ g : EuclideanSpace ℝ (Fin 2) → M, (∀ x ∈ D.domain, dist (g x) (D x) < δ) →
          StarInj T g → UniformInjectivityScale D.domain g κ ∧
            ∀ y, (D.domain ∩ g ⁻¹' {y}).encard ≤ 2) ∧
        (∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
          dist z (ec (D x)) < ε → z ∈ ⇑ec '' V ∧ dist (ec.symm z) (D x) < δ) ∧
        (∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
          dist z (ec (D x)) < ε → ec.symm z ∈ closure W → x ∈ Rc.space \ Ac.space) ∧
        ∀ x ∈ Rc.space ∩ frontier D.domain, ∀ z : EuclideanSpace ℝ (Fin 3),
          dist z (ec (D x)) < ε → ec.symm z ∈ BdM → B ∈ 𝓝[BdM] (ec.symm z) := by
  let _ := ‹CompactSpace M›
  let _ := hWV
  obtain ⟨T₀, hT₀fin, hT₀sp⟩ := D.isPLBall_domain.isPolyhedron.exists_simplicialComplex
  have : Finite T₀.faces := hT₀fin.to_subtype
  have hloc₀ : IsLocallyInjective (T₀.space.domRestrict ⇑D) := by
    rw [hT₀sp]
    exact Covering.isLocallyInjective_domRestrict_iff.mpr hloc
  obtain ⟨T, hT, hTfin, hTstar⟩ := exists_isSubdivision_injOn_starComplex T₀ (⇑D) hloc₀
  have : Finite T.faces := hTfin.to_subtype
  have hTsp : T.space = D.domain := hT.space_eq.trans hT₀sp
  obtain ⟨κ, δ, hκ, hδ, hcert⟩ := exists_uniformInjectivityScale_and_fiber_encard_le_two_of_close
    T (⇑D) (by rw [hTsp]; exact D.continuousOn) (by rw [hTsp]; exact hfiber)
  have : Finite Rc.faces := hRfin.to_subtype
  have : Finite Ac.faces := (hRfin.subset hAR).to_subtype
  have hRc : IsCompact Rc.space := (isPolyhedron_space Rc).isCompact
  have hAc : IsCompact Ac.space := (isPolyhedron_space Ac).isCompact
  have hAR' : Ac.space ⊆ Rc.space := space_mono_of_faces_subset hAR
  have hDR : ContinuousOn (⇑D) Rc.space := D.continuousOn.mono hRdom
  have hKA : IsCompact (⇑D '' Ac.space) := hAc.image_of_continuousOn (hDR.mono hAR')
  obtain ⟨d₀, hd₀, hd₀sub⟩ := hKA.exists_thickening_subset_open isClosed_closure.isOpen_compl
    (by
      rintro _ ⟨x, hx, rfl⟩ hxW
      exact Set.disjoint_left.mp hAfree hx hxW)
  let G : Set M := ⋃ O ∈ {O : Set M | IsOpen O ∧ O ∩ BdM ⊆ B}, O
  have hG : IsOpen G := isOpen_biUnion fun O hO => hO.1
  have hGB : ∀ m ∈ G, B ∈ 𝓝[BdM] m := by
    intro m hm
    obtain ⟨O, hO, hmO⟩ := mem_iUnion₂.mp hm
    exact mem_nhdsWithin.mpr ⟨O, hO.1, hmO, hO.2⟩
  have hKF : IsCompact (⇑D '' (Rc.space ∩ frontier D.domain)) :=
    (hRc.inter_right isClosed_frontier).image_of_continuousOn (hDR.mono inter_subset_left)
  obtain ⟨d₁, hd₁, hd₁sub⟩ := hKF.exists_thickening_subset_open hG
    (by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨O, hO, hxO, hOB⟩ := mem_nhdsWithin.mp
        (hbuffer (D x) ⟨⟨x, hx.2⟩, D.boundary_apply ⟨x, hx.2⟩⟩)
      exact mem_iUnion₂.mpr ⟨O, ⟨hO, hOB⟩, hxO⟩)
  have hKR : IsCompact (⇑D '' Rc.space) := hRc.image_of_continuousOn hDR
  have hKRV : ⇑D '' Rc.space ⊆ V := by
    rintro _ ⟨x, hx, rfl⟩
    exact hRV hx
  have hKe : IsCompact (⇑ec '' (⇑D '' Rc.space)) :=
    hKR.image_of_continuousOn (ec.continuousOn.mono (hKRV.trans hVec))
  have hVe : IsOpen (⇑ec '' V) := ec.isOpen_image_of_subset_source hVopen hVec
  obtain ⟨ε₁, hε₁, hε₁sub⟩ := hKe.exists_cthickening_subset_open hVe (image_mono hKRV)
  have hLc : IsCompact (cthickening ε₁ (⇑ec '' (⇑D '' Rc.space))) := hKe.cthickening
  have hLt : cthickening ε₁ (⇑ec '' (⇑D '' Rc.space)) ⊆ ec.target := by
    intro z hz
    obtain ⟨m, hm, rfl⟩ := hε₁sub hz
    exact ec.map_source (hVec hm)
  have huc := Metric.uniformContinuousOn_iff.mp
    (hLc.uniformContinuousOn_of_continuous (ec.continuousOn_symm.mono hLt))
  obtain ⟨ε₂, hε₂, hε₂uc⟩ := huc (min δ (min d₀ d₁)) (lt_min hδ (lt_min hd₀ hd₁))
  have hclose : ∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
      dist z (ec (D x)) < min ε₁ ε₂ →
        z ∈ ⇑ec '' V ∧ dist (ec.symm z) (D x) < min δ (min d₀ d₁) := by
    intro x hx z hz
    have hmem : ec (D x) ∈ ⇑ec '' (⇑D '' Rc.space) := ⟨D x, ⟨x, hx, rfl⟩, rfl⟩
    have hzL : z ∈ cthickening ε₁ (⇑ec '' (⇑D '' Rc.space)) :=
      mem_cthickening_of_dist_le z (ec (D x)) ε₁ _ hmem (hz.trans_le (min_le_left _ _)).le
    have hdist := hε₂uc z hzL (ec (D x)) (self_subset_cthickening _ hmem)
      (hz.trans_le (min_le_right _ _))
    rw [ec.left_inv (hVec (hRV hx))] at hdist
    exact ⟨hε₁sub hzL, hdist⟩
  refine ⟨T, κ, δ, min ε₁ ε₂, hκ, hδ, lt_min hε₁ hε₂, hTfin, hTsp, hTstar, ?_, ?_, ?_, ?_⟩
  · intro g hg hstar
    rw [← hTsp] at hg ⊢
    exact hcert g hg hstar
  · intro x hx z hz
    obtain ⟨hzV, hdist⟩ := hclose x hx z hz
    exact ⟨hzV, hdist.trans_le (min_le_left _ _)⟩
  · intro x hx z hz hzW
    refine ⟨hx, fun hxA => ?_⟩
    have hdist := (hclose x hx z hz).2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    exact hd₀sub (mem_thickening_iff.mpr ⟨D x, ⟨x, hxA, rfl⟩, hdist⟩) hzW
  · intro x hx z hz _
    have hdist := (hclose x hx.1 z hz).2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    exact hGB _ (hd₁sub (mem_thickening_iff.mpr ⟨D x, ⟨x, hx, rfl⟩, hdist⟩))

end MetricAmbient

end DifferentialGeometry.Topology.PiecewiseLinear
