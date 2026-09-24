import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalProduct
import DifferentialGeometry.Topology.PiecewiseLinear.CircleIntersection
import DifferentialGeometry.Topology.PiecewiseLinear.CollarSectorPolyhedron
import DifferentialGeometry.Topology.PiecewiseLinear.BallHomotopy

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem nullhomotopic_inclusion_of_compact_section
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {P A : Set X} {S J : Set Y} {f : X → Y} (hA : IsCompact A) (hAP : A ⊆ P)
    (hf : ContinuousOn f P) (hmap : MapsTo f P S) (hinj : InjOn f A)
    (himage : f '' A = J) (hJS : J ⊆ S)
    (hnull : (⟨fun x : P => ⟨f x, hmap x.2⟩,
      hf.domRestrict.subtype_mk _⟩ : C(P, S)).Nullhomotopic) :
    (⟨inclusion hJS, continuous_inclusion hJS⟩ : C(J, S)).Nullhomotopic := by
  let _ : CompactSpace A := isCompact_iff_compactSpace.mp hA
  let g : A → J := fun x => ⟨f x, himage ▸ mem_image_of_mem f x.2⟩
  have hg : Continuous g := ((hf.mono hAP).domRestrict).subtype_mk _
  have hgb : Function.Bijective g := by
    refine ⟨fun x y h => Subtype.ext (hinj x.2 y.2 (congrArg Subtype.val h)), ?_⟩
    intro y
    obtain ⟨x, hx, hxy⟩ := himage.symm.subset y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let e := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective g hgb) hg
  let k : C(J, P) := ⟨fun y => ⟨e.symm y, hAP (e.symm y).2⟩,
    (continuous_subtype_val.comp e.symm.continuous).subtype_mk _⟩
  convert hnull.comp_left k using 1
  apply ContinuousMap.ext
  intro y
  exact Subtype.ext (congrArg Subtype.val (e.apply_symm_apply y)).symm

private theorem isConnected_preimage_of_two_point_fiber
    {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [T2Space Y]
    {P : Set X} {S J : Set Y} {f : X → Y} (hP : IsCompact P)
    (hJ : IsClosed J) (hJS : J ⊆ S) (hf : ContinuousOn f P)
    (hmap : MapsTo f P S) (hsurj : J ⊆ f '' P) {p : Y}
    (hconn : IsConnected (J \ {p})) (hclosure : closure (J \ {p}) = J)
    {a b : X} (hpair : ∀ x ∈ P ∩ f ⁻¹' J, ∀ y ∈ P ∩ f ⁻¹' J, f x = f y →
      x = y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a))
    (hpa : f a = p) (hpb : f b = p)
    (hnull : (⟨fun x : P => ⟨f x, hmap x.2⟩,
      hf.domRestrict.subtype_mk _⟩ : C(P, S)).Nullhomotopic)
    (hnon : ¬ (⟨inclusion hJS, continuous_inclusion hJS⟩ : C(J, S)).Nullhomotopic) :
    IsConnected (P ∩ f ⁻¹' J) := by
  let K := P ∩ f ⁻¹' J
  have hK : IsCompact K := hP.of_isClosed_subset
    (hf.preimage_isClosed_of_isClosed hP.isClosed hJ) inter_subset_left
  have hKimage : f '' K = J := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.2
    · intro hy
      obtain ⟨x, hx, rfl⟩ := hsurj hy
      exact ⟨x, ⟨hx, hy⟩, rfl⟩
  refine ⟨?_, isPreconnected_closed_iff.mpr ?_⟩
  · obtain ⟨y, hy, -⟩ := hconn.nonempty
    obtain ⟨x, hx, -⟩ := hKimage.symm ▸ hy
    exact ⟨x, hx⟩
  · intro u v hu hv hcover humeet hvmeet
    by_contra hdis
    have hdis' : ∀ x ∈ K ∩ u, x ∉ K ∩ v := by
      rintro x hx hxv
      exact hdis ⟨x, hx.1, hx.2, hxv.2⟩
    have hAc : IsCompact (K ∩ u) := hK.inter_right hu
    have hBc : IsCompact (K ∩ v) := hK.inter_right hv
    have hAclosed := (hAc.image_of_continuousOn (hf.mono
      (inter_subset_left.trans inter_subset_left))).isClosed
    have hBclosed := (hBc.image_of_continuousOn (hf.mono
      (inter_subset_left.trans inter_subset_left))).isClosed
    have hcover' : J ⊆ (f '' (K ∩ u)) ∪ (f '' (K ∩ v)) := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hKimage.symm ▸ hy
      exact (hcover hx).elim (fun h => Or.inl ⟨x, ⟨hx, h⟩, rfl⟩)
        (fun h => Or.inr ⟨x, ⟨hx, h⟩, rfl⟩)
    have hinter : ∀ y ∈ f '' (K ∩ u), y ∈ f '' (K ∩ v) → y = p := by
      rintro y ⟨x, hx, rfl⟩ ⟨z, hz, hzx⟩
      rcases hpair x hx.1 z hz.1 hzx.symm with h | h | h
      · exact (hdis' x hx (h.symm ▸ hz)).elim
      · exact h.1 ▸ hpa
      · exact h.1 ▸ hpb
    have hside : J \ {p} ⊆ f '' (K ∩ u) ∨ J \ {p} ⊆ f '' (K ∩ v) := by
      by_contra hn
      have hn := not_or.mp hn
      obtain ⟨x, hx, hxu⟩ := not_subset.mp hn.1
      obtain ⟨y, hy, hyv⟩ := not_subset.mp hn.2
      obtain ⟨z, hz, hzu, hzv⟩ := isPreconnected_closed_iff.mp hconn.isPreconnected
        _ _ hAclosed hBclosed (sdiff_subset.trans hcover')
        ⟨y, hy, (hcover' hy.1).resolve_right hyv⟩
        ⟨x, hx, (hcover' hx.1).resolve_left hxu⟩
      exact hz.2 (hinter z hzu hzv)
    have finish {A B : Set X} (hAc : IsCompact A) (hAK : A ⊆ K) (hBK : B ⊆ K)
        (hBne : B.Nonempty) (hAB : Disjoint A B) (honto : f '' A = J) : False := by
      have hinj : InjOn f A := by
        intro x hx y hy hxy
        by_contra hne
        have hab : a ∈ A ∧ b ∈ A := by
          rcases hpair x (hAK hx) y (hAK hy) hxy with h | h | h
          · exact (hne h).elim
          · exact ⟨h.1 ▸ hx, h.2 ▸ hy⟩
          · exact ⟨h.2 ▸ hy, h.1 ▸ hx⟩
        obtain ⟨z, hz⟩ := hBne
        obtain ⟨w, hw, hwz⟩ := honto.symm ▸ (hBK hz).2
        rcases hpair w (hAK hw) z (hBK hz) hwz with h | h | h
        · exact disjoint_left.mp hAB hw (h.symm ▸ hz)
        · exact disjoint_left.mp hAB hab.2 (h.2 ▸ hz)
        · exact disjoint_left.mp hAB hab.1 (h.2 ▸ hz)
      exact hnon (nullhomotopic_inclusion_of_compact_section hAc
        (hAK.trans inter_subset_left) hf hmap hinj honto hJS hnull)
    rcases hside with hside | hside
    · apply finish hAc inter_subset_left inter_subset_left hvmeet
        (disjoint_left.mpr hdis')
      exact Subset.antisymm (image_subset_iff.mpr fun x hx => hx.1.2)
        (hclosure ▸ closure_minimal hside hAclosed)
    · apply finish hBc inter_subset_left inter_subset_left humeet
        (disjoint_left.mpr fun x hx hy => hdis' x hy hx)
      exact Subset.antisymm (image_subset_iff.mpr fun x hx => hx.1.2)
        (hclosure ▸ closure_minimal hside hBclosed)


theorem IsCylindricalDiagram.isConnected_preimage_circle_of_singleton_seam
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E × ℝ → F} {P : Set E} {S J : Set F} {n : ℕ}
    (hf : IsCylindricalDiagram f P S) (hP : IsPLBall n P)
    (hends : ∀ x ∈ P, f (x, 0) = f (x, 1)) (hJ : IsPLSphere 1 J) (hJS : J ⊆ S)
    {p : F} (hinter : J ∩ f '' (P ×ˢ ({0} : Set ℝ)) = {p})
    (hnon : ¬ (⟨inclusion hJS, continuous_inclusion hJS⟩ : C(J, S)).Nullhomotopic) :
    IsConnected ((P ×ˢ Icc (0 : ℝ) 1) ∩ f ⁻¹' J) := by
  have hp := hinter.symm.subset (mem_singleton p)
  obtain ⟨⟨a, t⟩, ⟨ha, ht⟩, hap⟩ := hp.2
  have ht : t = 0 := ht
  subst t
  let T := P ×ˢ Icc (0 : ℝ) 1
  have hmap : MapsTo f T S := fun x hx => hf.image_eq ▸ mem_image_of_mem f hx
  let F : C(T, S) := ⟨fun x => ⟨f x, hmap x.2⟩,
    hf.isPiecewiseAffineOn.continuousOn.domRestrict.subtype_mk _⟩
  let _ : ContractibleSpace P := hP.contractibleSpace
  let _ : ContractibleSpace (Icc (0 : ℝ) 1) := (convex_Icc (0 : ℝ) 1).contractibleSpace
    ⟨0, le_rfl, zero_le_one⟩
  let _ : ContractibleSpace T :=
    (Homeomorph.Set.prod P (Icc (0 : ℝ) 1)).contractibleSpace_iff.mpr inferInstance
  have hnull : F.Nullhomotopic :=
    (id_nullhomotopic T).comp_right F
  apply isConnected_preimage_of_two_point_fiber (hP.isPolyhedron.isCompact.prod isCompact_Icc)
    hJ.isPolyhedron.isClosed hJS hf.isPiecewiseAffineOn.continuousOn hmap
    (hf.image_eq.symm ▸ hJS) (hJ.isConnected_sdiff_singleton_one p)
    (hJ.closure_sdiff_singleton_one p) (a := (a, 0)) (b := (a, 1))
    ?_ hap ((hends a ha).symm.trans hap) hnull hnon
  intro x hx y hy hxy
  rcases hf.eq_or_endpoints x hx.1 y hy.1 hxy with heq | heq | heq
  · exact Or.inl heq
  · have hxp : f x = p := hinter.subset ⟨hx.2, x, ⟨hx.1.1, heq.1⟩, rfl⟩
    have hxbase := (hf.eq_iff_fst_eq_and_circle_eq hends hx.1
      ⟨ha, le_rfl, zero_le_one⟩).mp (hxp.trans hap.symm)
    have hybase := (hf.eq_iff_fst_eq_and_circle_eq hends hy.1
      ⟨ha, le_rfl, zero_le_one⟩).mp (hxy.symm.trans (hxp.trans hap.symm))
    exact Or.inr (Or.inl ⟨Prod.ext hxbase.1 heq.1, Prod.ext hybase.1 heq.2⟩)
  · have hyp : f y = p := hinter.subset ⟨hy.2, y, ⟨hy.1.1, heq.2⟩, rfl⟩
    have hxbase := (hf.eq_iff_fst_eq_and_circle_eq hends hx.1
      ⟨ha, le_rfl, zero_le_one⟩).mp (hxy.trans (hyp.trans hap.symm))
    have hybase := (hf.eq_iff_fst_eq_and_circle_eq hends hy.1
      ⟨ha, le_rfl, zero_le_one⟩).mp (hyp.trans hap.symm)
    exact Or.inr (Or.inr ⟨Prod.ext hxbase.1 heq.1, Prod.ext hybase.1 heq.2⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
