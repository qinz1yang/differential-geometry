/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SingularNormalForm

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem image_inter_preimage_of_bijOn {G E : Type*} {φ : G → E} {Q : Set G} {P A : Set E}
    (hφ : BijOn φ Q P) (hAP : A ⊆ P) : φ '' (Q ∩ φ ⁻¹' A) = A := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  · intro y hy
    obtain ⟨x, hxQ, rfl⟩ := hφ.surjOn (hAP hy)
    exact ⟨x, ⟨hxQ, hy⟩, rfl⟩

variable {G E F : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem isPLHomeomorphOn_comp_inter_preimage {φ : G → E} {Q : Set G} {P A : Set E}
    {f : E → F} (hφ : IsPLHomeomorphOn φ Q P) (hAP : A ⊆ P)
    (hfA : IsPLHomeomorphOn f A (f '' A)) :
    IsPLHomeomorphOn (f ∘ φ) (Q ∩ φ ⁻¹' A) (f '' A) := by
  have himg : φ '' (Q ∩ φ ⁻¹' A) = A := image_inter_preimage_of_bijOn hφ.bijOn hAP
  have hbijφ : BijOn φ (Q ∩ φ ⁻¹' A) A :=
    ⟨fun _ hx => hx.2, hφ.bijOn.injOn.mono inter_subset_left, himg.symm.subset⟩
  have hbij : BijOn (f ∘ φ) (Q ∩ φ ⁻¹' A) (f '' A) := hfA.bijOn.comp hbijφ
  refine ⟨hbij, hfA.isPiecewiseAffineOn.comp hφ.isPiecewiseAffineOn, ?_⟩
  have hmapsP : MapsTo (Function.invFunOn f A) (f '' A) P := fun w hw =>
    hAP (hfA.bijOn.surjOn.mapsTo_invFunOn hw)
  have hcomp := hφ.isPiecewiseAffineOn_invFunOn.comp hfA.isPiecewiseAffineOn_invFunOn
  have hset : f '' A ∩ Function.invFunOn f A ⁻¹' P = f '' A := inter_eq_left.mpr hmapsP
  rw [hset] at hcomp
  refine hcomp.congr ?_
  intro w hw
  have hwA : Function.invFunOn f A w ∈ A := hfA.bijOn.surjOn.mapsTo_invFunOn hw
  have hwf : f (Function.invFunOn f A w) = w := hfA.bijOn.invOn_invFunOn.2 hw
  have hmemQ : Function.invFunOn φ Q (Function.invFunOn f A w) ∈ Q :=
    hφ.bijOn.surjOn.mapsTo_invFunOn (hAP hwA)
  have hmemA : φ (Function.invFunOn φ Q (Function.invFunOn f A w)) = Function.invFunOn f A w :=
    hφ.bijOn.invOn_invFunOn.2 (hAP hwA)
  have hmem : Function.invFunOn φ Q (Function.invFunOn f A w) ∈ Q ∩ φ ⁻¹' A :=
    ⟨hmemQ, by rw [mem_preimage, hmemA]; exact hwA⟩
  refine hbij.injOn (hbij.surjOn.mapsTo_invFunOn hw) hmem ?_
  rw [hbij.invOn_invFunOn.2 hw]
  change w = f (φ (Function.invFunOn φ Q (Function.invFunOn f A w)))
  rw [hmemA, hwf]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
theorem mem_nhdsWithin_inter_preimage {φ : G → E} {Q : Set G} {P A : Set E}
    (hφ : IsPLHomeomorphOn φ Q P) {a : E} (haP : a ∈ P) (hA : A ∈ 𝓝[P] a) :
    Q ∩ φ ⁻¹' A ∈ 𝓝[Q] Function.invFunOn φ Q a := by
  have hmem : Function.invFunOn φ Q a ∈ Q := hφ.bijOn.surjOn.mapsTo_invFunOn haP
  have hval : φ (Function.invFunOn φ Q a) = a := hφ.bijOn.invOn_invFunOn.2 haP
  have hcont : ContinuousWithinAt φ Q (Function.invFunOn φ Q a) :=
    hφ.isPiecewiseAffineOn.continuousOn _ hmem
  have htend := hcont.tendsto_nhdsWithin (t := P) hφ.bijOn.mapsTo
  rw [hval] at htend
  exact Filter.inter_mem self_mem_nhdsWithin (htend hA)

theorem HasPLDoubleCrossingAt.precomp_isPLHomeomorphOn {f : E → F} {P : Set E} {y : F}
    {φ : G → E} {Q : Set G} (hD : HasPLDoubleCrossingAt f P y)
    (hφ : IsPLHomeomorphOn φ Q P) : HasPLDoubleCrossingAt (f ∘ φ) Q y := by
  obtain ⟨a, b, A, B, ha, hb, hfa, hfb, hAP, hBP, hdis, hA, hB, hfA, hfB, hcross, hcover⟩ := hD
  refine ⟨Function.invFunOn φ Q a, Function.invFunOn φ Q b, Q ∩ φ ⁻¹' A, Q ∩ φ ⁻¹' B, ?_, ?_,
    ?_, ?_, inter_subset_left, inter_subset_left, ?_,
    mem_nhdsWithin_inter_preimage hφ (hAP ha) hA, mem_nhdsWithin_inter_preimage hφ (hBP hb) hB,
    ?_, ?_, ?_, ?_⟩
  · exact ⟨hφ.bijOn.surjOn.mapsTo_invFunOn (hAP ha),
      by rw [mem_preimage, hφ.bijOn.invOn_invFunOn.2 (hAP ha)]; exact ha⟩
  · exact ⟨hφ.bijOn.surjOn.mapsTo_invFunOn (hBP hb),
      by rw [mem_preimage, hφ.bijOn.invOn_invFunOn.2 (hBP hb)]; exact hb⟩
  · change f (φ (Function.invFunOn φ Q a)) = y
    rw [hφ.bijOn.invOn_invFunOn.2 (hAP ha)]
    exact hfa
  · change f (φ (Function.invFunOn φ Q b)) = y
    rw [hφ.bijOn.invOn_invFunOn.2 (hBP hb)]
    exact hfb
  · exact Disjoint.mono inter_subset_right inter_subset_right
      (hdis.preimage φ)
  · have h := isPLHomeomorphOn_comp_inter_preimage hφ hAP hfA
    rwa [show (f ∘ φ) '' (Q ∩ φ ⁻¹' A) = f '' A from by
      rw [image_comp, image_inter_preimage_of_bijOn hφ.bijOn hAP]]
  · have h := isPLHomeomorphOn_comp_inter_preimage hφ hBP hfB
    rwa [show (f ∘ φ) '' (Q ∩ φ ⁻¹' B) = f '' B from by
      rw [image_comp, image_inter_preimage_of_bijOn hφ.bijOn hBP]]
  · rw [image_comp, image_inter_preimage_of_bijOn hφ.bijOn hAP, image_comp,
      image_inter_preimage_of_bijOn hφ.bijOn hBP]
    exact hcross
  · filter_upwards [hcover] with z hz x hx
    have hxQ : x ∈ Q := hx.1
    have hφx : φ x ∈ P ∩ f ⁻¹' {z} := ⟨hφ.bijOn.mapsTo hxQ, hx.2⟩
    rcases hz hφx with hmem | hmem
    · exact Or.inl ⟨hxQ, hmem⟩
    · exact Or.inr ⟨hxQ, hmem⟩

theorem HasPLBoundaryDoubleCrossingAt.precomp_isPLHomeomorphOn {f : E → F} {P : Set E}
    {Mb : Set F} {y : F} {φ : G → E} {Q : Set G}
    (hD : HasPLBoundaryDoubleCrossingAt f P Mb y) (hφ : IsPLHomeomorphOn φ Q P) :
    HasPLBoundaryDoubleCrossingAt (f ∘ φ) Q Mb y := by
  obtain ⟨a, b, A, B, ha, hb, hfa, hfb, hAP, hBP, hdis, hA, hB, hfA, hfB, hcross, hcover⟩ := hD
  refine ⟨Function.invFunOn φ Q a, Function.invFunOn φ Q b, Q ∩ φ ⁻¹' A, Q ∩ φ ⁻¹' B, ?_, ?_,
    ?_, ?_, inter_subset_left, inter_subset_left, ?_,
    mem_nhdsWithin_inter_preimage hφ (hAP ha) hA, mem_nhdsWithin_inter_preimage hφ (hBP hb) hB,
    ?_, ?_, ?_, ?_⟩
  · exact ⟨hφ.bijOn.surjOn.mapsTo_invFunOn (hAP ha),
      by rw [mem_preimage, hφ.bijOn.invOn_invFunOn.2 (hAP ha)]; exact ha⟩
  · exact ⟨hφ.bijOn.surjOn.mapsTo_invFunOn (hBP hb),
      by rw [mem_preimage, hφ.bijOn.invOn_invFunOn.2 (hBP hb)]; exact hb⟩
  · change f (φ (Function.invFunOn φ Q a)) = y
    rw [hφ.bijOn.invOn_invFunOn.2 (hAP ha)]
    exact hfa
  · change f (φ (Function.invFunOn φ Q b)) = y
    rw [hφ.bijOn.invOn_invFunOn.2 (hBP hb)]
    exact hfb
  · exact Disjoint.mono inter_subset_right inter_subset_right
      (hdis.preimage φ)
  · have h := isPLHomeomorphOn_comp_inter_preimage hφ hAP hfA
    rwa [show (f ∘ φ) '' (Q ∩ φ ⁻¹' A) = f '' A from by
      rw [image_comp, image_inter_preimage_of_bijOn hφ.bijOn hAP]]
  · have h := isPLHomeomorphOn_comp_inter_preimage hφ hBP hfB
    rwa [show (f ∘ φ) '' (Q ∩ φ ⁻¹' B) = f '' B from by
      rw [image_comp, image_inter_preimage_of_bijOn hφ.bijOn hBP]]
  · rw [image_comp, image_inter_preimage_of_bijOn hφ.bijOn hAP, image_comp,
      image_inter_preimage_of_bijOn hφ.bijOn hBP]
    exact hcross
  · filter_upwards [hcover] with z hz x hx
    have hxQ : x ∈ Q := hx.1
    have hφx : φ x ∈ P ∩ f ⁻¹' {z} := ⟨hφ.bijOn.mapsTo hxQ, hx.2⟩
    rcases hz hφx with hmem | hmem
    · exact Or.inl ⟨hxQ, hmem⟩
    · exact Or.inr ⟨hxQ, hmem⟩

theorem HasPLNormalDoubleCrossingAt.precomp_isPLHomeomorphOn {f : E → F} {P : Set E}
    {Bd : Set F} {y : F} {φ : G → E} {Q : Set G}
    (hD : HasPLNormalDoubleCrossingAt f P Bd y) (hφ : IsPLHomeomorphOn φ Q P) :
    HasPLNormalDoubleCrossingAt (f ∘ φ) Q Bd y := by
  rcases hD with ⟨hyB, Mb, hcross⟩ | ⟨hyB, hcross⟩
  · exact Or.inl ⟨hyB, Mb, hcross.precomp_isPLHomeomorphOn hφ⟩
  · exact Or.inr ⟨hyB, hcross.precomp_isPLHomeomorphOn hφ⟩

omit [NormedSpace ℝ G] [FiniteDimensional ℝ G] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
theorem mem_nhdsWithin_inter_preimage_of_bijOn {φ : G → E} {Q : Set G} {P A : Set E}
    (hbij : BijOn φ Q P) (hcont : ContinuousOn φ Q) {a : E} (haP : a ∈ P)
    (hA : A ∈ 𝓝[P] a) : Q ∩ φ ⁻¹' A ∈ 𝓝[Q] Function.invFunOn φ Q a := by
  have hmem : Function.invFunOn φ Q a ∈ Q := hbij.surjOn.mapsTo_invFunOn haP
  have hval : φ (Function.invFunOn φ Q a) = a := hbij.invOn_invFunOn.2 haP
  have htend := (hcont _ hmem).tendsto_nhdsWithin (t := P) hbij.mapsTo
  rw [hval] at htend
  exact Filter.inter_mem self_mem_nhdsWithin (htend hA)

omit [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
theorem inter_preimage_eq_of_mapsTo_back {φ : G → E} {Q QBig : Set G} {P A : Set E}
    (hQ : Q ⊆ QBig) (hAP : A ⊆ P) (hback : ∀ x ∈ QBig, φ x ∈ P → x ∈ Q) :
    QBig ∩ φ ⁻¹' A = Q ∩ φ ⁻¹' A := by
  apply Subset.antisymm
  · rintro x ⟨hxB, hxA⟩
    exact ⟨hback x hxB (hAP hxA), hxA⟩
  · rintro x ⟨hxQ, hxA⟩
    exact ⟨hQ hxQ, hxA⟩

theorem HasPLDoubleCrossingAt.precomp_bijOn_of_isPLHomeomorphOn {f : E → F} {P PBig : Set E}
    {y : F} {φ : G → E} {Q QBig : Set G} (hD : HasPLDoubleCrossingAt f P y)
    (hφ : IsPLHomeomorphOn φ QBig PBig) (hbij : BijOn φ Q P) (hQ : Q ⊆ QBig) (hP : P ⊆ PBig)
    (hback : ∀ x ∈ QBig, φ x ∈ P → x ∈ Q) :
    HasPLDoubleCrossingAt (f ∘ φ) Q y := by
  obtain ⟨a, b, A, B, ha, hb, hfa, hfb, hAP, hBP, hdis, hA, hB, hfA, hfB, hcross, hcover⟩ := hD
  have hcont : ContinuousOn φ Q := hφ.isPiecewiseAffineOn.continuousOn.mono hQ
  have hsetA : QBig ∩ φ ⁻¹' A = Q ∩ φ ⁻¹' A := inter_preimage_eq_of_mapsTo_back hQ hAP hback
  have hsetB : QBig ∩ φ ⁻¹' B = Q ∩ φ ⁻¹' B := inter_preimage_eq_of_mapsTo_back hQ hBP hback
  have himgA : (f ∘ φ) '' (Q ∩ φ ⁻¹' A) = f '' A := by
    rw [image_comp, image_inter_preimage_of_bijOn hbij hAP]
  have himgB : (f ∘ φ) '' (Q ∩ φ ⁻¹' B) = f '' B := by
    rw [image_comp, image_inter_preimage_of_bijOn hbij hBP]
  refine ⟨Function.invFunOn φ Q a, Function.invFunOn φ Q b, Q ∩ φ ⁻¹' A, Q ∩ φ ⁻¹' B, ?_, ?_,
    ?_, ?_, inter_subset_left, inter_subset_left, ?_,
    mem_nhdsWithin_inter_preimage_of_bijOn hbij hcont (hAP ha) hA,
    mem_nhdsWithin_inter_preimage_of_bijOn hbij hcont (hBP hb) hB, ?_, ?_, ?_, ?_⟩
  · exact ⟨hbij.surjOn.mapsTo_invFunOn (hAP ha),
      by rw [mem_preimage, hbij.invOn_invFunOn.2 (hAP ha)]; exact ha⟩
  · exact ⟨hbij.surjOn.mapsTo_invFunOn (hBP hb),
      by rw [mem_preimage, hbij.invOn_invFunOn.2 (hBP hb)]; exact hb⟩
  · change f (φ (Function.invFunOn φ Q a)) = y
    rw [hbij.invOn_invFunOn.2 (hAP ha)]
    exact hfa
  · change f (φ (Function.invFunOn φ Q b)) = y
    rw [hbij.invOn_invFunOn.2 (hBP hb)]
    exact hfb
  · exact Disjoint.mono inter_subset_right inter_subset_right (hdis.preimage φ)
  · rw [himgA, ← hsetA]
    exact isPLHomeomorphOn_comp_inter_preimage hφ (hAP.trans hP) hfA
  · rw [himgB, ← hsetB]
    exact isPLHomeomorphOn_comp_inter_preimage hφ (hBP.trans hP) hfB
  · rw [himgA, himgB]
    exact hcross
  · filter_upwards [hcover] with z hz x hx
    have hxQ : x ∈ Q := hx.1
    have hφx : φ x ∈ P ∩ f ⁻¹' {z} := ⟨hbij.mapsTo hxQ, hx.2⟩
    rcases hz hφx with hmem | hmem
    · exact Or.inl ⟨hxQ, hmem⟩
    · exact Or.inr ⟨hxQ, hmem⟩

theorem HasPLBoundaryDoubleCrossingAt.precomp_bijOn_of_isPLHomeomorphOn {f : E → F}
    {P PBig : Set E} {Mb : Set F} {y : F} {φ : G → E} {Q QBig : Set G}
    (hD : HasPLBoundaryDoubleCrossingAt f P Mb y)
    (hφ : IsPLHomeomorphOn φ QBig PBig) (hbij : BijOn φ Q P) (hQ : Q ⊆ QBig) (hP : P ⊆ PBig)
    (hback : ∀ x ∈ QBig, φ x ∈ P → x ∈ Q) :
    HasPLBoundaryDoubleCrossingAt (f ∘ φ) Q Mb y := by
  obtain ⟨a, b, A, B, ha, hb, hfa, hfb, hAP, hBP, hdis, hA, hB, hfA, hfB, hcross, hcover⟩ := hD
  have hcont : ContinuousOn φ Q := hφ.isPiecewiseAffineOn.continuousOn.mono hQ
  have hsetA : QBig ∩ φ ⁻¹' A = Q ∩ φ ⁻¹' A := inter_preimage_eq_of_mapsTo_back hQ hAP hback
  have hsetB : QBig ∩ φ ⁻¹' B = Q ∩ φ ⁻¹' B := inter_preimage_eq_of_mapsTo_back hQ hBP hback
  have himgA : (f ∘ φ) '' (Q ∩ φ ⁻¹' A) = f '' A := by
    rw [image_comp, image_inter_preimage_of_bijOn hbij hAP]
  have himgB : (f ∘ φ) '' (Q ∩ φ ⁻¹' B) = f '' B := by
    rw [image_comp, image_inter_preimage_of_bijOn hbij hBP]
  refine ⟨Function.invFunOn φ Q a, Function.invFunOn φ Q b, Q ∩ φ ⁻¹' A, Q ∩ φ ⁻¹' B, ?_, ?_,
    ?_, ?_, inter_subset_left, inter_subset_left, ?_,
    mem_nhdsWithin_inter_preimage_of_bijOn hbij hcont (hAP ha) hA,
    mem_nhdsWithin_inter_preimage_of_bijOn hbij hcont (hBP hb) hB, ?_, ?_, ?_, ?_⟩
  · exact ⟨hbij.surjOn.mapsTo_invFunOn (hAP ha),
      by rw [mem_preimage, hbij.invOn_invFunOn.2 (hAP ha)]; exact ha⟩
  · exact ⟨hbij.surjOn.mapsTo_invFunOn (hBP hb),
      by rw [mem_preimage, hbij.invOn_invFunOn.2 (hBP hb)]; exact hb⟩
  · change f (φ (Function.invFunOn φ Q a)) = y
    rw [hbij.invOn_invFunOn.2 (hAP ha)]
    exact hfa
  · change f (φ (Function.invFunOn φ Q b)) = y
    rw [hbij.invOn_invFunOn.2 (hBP hb)]
    exact hfb
  · exact Disjoint.mono inter_subset_right inter_subset_right (hdis.preimage φ)
  · rw [himgA, ← hsetA]
    exact isPLHomeomorphOn_comp_inter_preimage hφ (hAP.trans hP) hfA
  · rw [himgB, ← hsetB]
    exact isPLHomeomorphOn_comp_inter_preimage hφ (hBP.trans hP) hfB
  · rw [himgA, himgB]
    exact hcross
  · filter_upwards [hcover] with z hz x hx
    have hxQ : x ∈ Q := hx.1
    have hφx : φ x ∈ P ∩ f ⁻¹' {z} := ⟨hbij.mapsTo hxQ, hx.2⟩
    rcases hz hφx with hmem | hmem
    · exact Or.inl ⟨hxQ, hmem⟩
    · exact Or.inr ⟨hxQ, hmem⟩

theorem HasPLNormalDoubleCrossingAt.precomp_bijOn_of_isPLHomeomorphOn {f : E → F}
    {P PBig : Set E} {Bd : Set F} {y : F} {φ : G → E} {Q QBig : Set G}
    (hD : HasPLNormalDoubleCrossingAt f P Bd y)
    (hφ : IsPLHomeomorphOn φ QBig PBig) (hbij : BijOn φ Q P) (hQ : Q ⊆ QBig) (hP : P ⊆ PBig)
    (hback : ∀ x ∈ QBig, φ x ∈ P → x ∈ Q) :
    HasPLNormalDoubleCrossingAt (f ∘ φ) Q Bd y := by
  rcases hD with ⟨hyB, Mb, hcross⟩ | ⟨hyB, hcross⟩
  · exact Or.inl ⟨hyB, Mb, hcross.precomp_bijOn_of_isPLHomeomorphOn hφ hbij hQ hP hback⟩
  · exact Or.inr ⟨hyB, hcross.precomp_bijOn_of_isPLHomeomorphOn hφ hbij hQ hP hback⟩

end DifferentialGeometry.Topology.PiecewiseLinear
