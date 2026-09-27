import DifferentialGeometry.Topology.PiecewiseLinear.Orientation
import DifferentialGeometry.Topology.SimplicialSet.EulerCharacteristic
import Mathlib.AlgebraicTopology.SimplicialSet.Nonsingular

noncomputable section
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
namespace DifferentialGeometry.Topology.SimplicialComplex

universe u
variable {k ι : Type u} [Field k] [LinearOrder ι]

private def normalizedChainComplexXIso (K : PreAbstractSimplicialComplex ι) (n : ℕ) :
    ((orderedSimplicialSet K).normalizedChainComplex (ModuleCat.of k k)).X n ≅
      ModuleCat.of k (DirectSum ((orderedSimplicialSet K).nonDegenerate n) fun _ => k) := by
  classical
  exact ((orderedSimplicialSet K).isColimitCofanNormalizedChainComplex (ModuleCat.of k k) n)
    |>.coconePointUniqueUpToIso
      (ModuleCat.coproductCoconeIsColimit
        (fun _ : (orderedSimplicialSet K).nonDegenerate n => ModuleCat.of k k))

noncomputable def orderedNormalizedChainEquiv (K : PreAbstractSimplicialComplex ι)
    [Finite K.faces] (n : ℕ) :
    ((orderedSimplicialSet K).normalizedChainComplex (ModuleCat.of k k)).X n ≃ₗ[k]
      ({s : Finset ι // s ∈ K ∧ s.card = n + 1} → k) := by
  letI : Fintype ((orderedSimplicialSet K).nonDegenerate n) := Fintype.ofFinite _
  exact (normalizedChainComplexXIso (k := k) K n).toLinearEquiv |>.trans
    (DirectSum.linearEquivFunOnFintype k _ (fun _ => k)) |>.trans
    (LinearEquiv.funCongrLeft k k (orderedNondegenerateFaceEquiv K n).symm)

theorem orderedNormalizedChainEquiv_generator (K : PreAbstractSimplicialComplex ι)
    [Finite K.faces] (n : ℕ) (s : {s : Finset ι // s ∈ K ∧ s.card = n + 1}) :
    orderedNormalizedChainEquiv (k := k) K n
        (((orderedSimplicialSet K).ιNormalizedChainComplex
          (R := ModuleCat.of k k) (orderedSimplexOfFace K s.1 s.2.1 s.2.2).1).hom 1) =
      Pi.single s 1 := by
  classical
  let _ : Fintype ((orderedSimplicialSet K).nonDegenerate n) := Fintype.ofFinite _
  let x := orderedSimplexOfFace K s.1 s.2.1 s.2.2
  have hx : (orderedNondegenerateFaceEquiv K n).symm s = x := by
    rfl
  have hxs : (orderedNondegenerateFaceEquiv K n) x = s := by
    rw [← hx]
    exact (orderedNondegenerateFaceEquiv K n).apply_symm_apply s
  have hgen :
      (normalizedChainComplexXIso (k := k) K n).toLinearEquiv
          (((orderedSimplicialSet K).ιNormalizedChainComplex
            (R := ModuleCat.of k k) x.1).hom 1) =
        DirectSum.lof k ((orderedSimplicialSet K).nonDegenerate n) (fun _ => k) x 1 := by
    change ((normalizedChainComplexXIso (k := k) K n).hom.hom
        (((orderedSimplicialSet K).ιNormalizedChainComplex
          (R := ModuleCat.of k k) x.1).hom 1)) = _
    have hcomp :=
      ((orderedSimplicialSet K).isColimitCofanNormalizedChainComplex (ModuleCat.of k k) n)
        |>.comp_coconePointUniqueUpToIso_hom
          (ModuleCat.coproductCoconeIsColimit
            (fun _ : (orderedSimplicialSet K).nonDegenerate n => ModuleCat.of k k))
          ⟨x⟩
    change (orderedSimplicialSet K).ιNormalizedChainComplex x.1 ≫
        (normalizedChainComplexXIso (k := k) K n).hom =
      ModuleCat.ofHom
        (DirectSum.lof k ((orderedSimplicialSet K).nonDegenerate n) (fun _ => k) x) at hcomp
    simpa only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
      ModuleCat.hom_ofHom] using congr($(hcomp) (1 : k))
  change (LinearEquiv.funCongrLeft k k (orderedNondegenerateFaceEquiv K n).symm)
      ((DirectSum.linearEquivFunOnFintype k _ (fun _ => k))
        ((normalizedChainComplexXIso (k := k) K n).toLinearEquiv
          (((orderedSimplicialSet K).ιNormalizedChainComplex
            (R := ModuleCat.of k k) x.1).hom 1))) = _
  rw [hgen, DirectSum.linearEquivFunOnFintype_lof]
  apply funext
  intro t
  simp only [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
  by_cases h : s = t
  · subst t
    rw [hx]
    simp
  · have hxt : x ≠ (orderedNondegenerateFaceEquiv K n).symm t := by
      intro hxt
      apply h
      have := congrArg (orderedNondegenerateFaceEquiv K n) hxt
      rw [hxs, (orderedNondegenerateFaceEquiv K n).apply_symm_apply] at this
      exact this
    simp [hxt, h]

theorem orderedNormalizedChainEquiv_ι (K : PreAbstractSimplicialComplex ι)
    [Finite K.faces] (n : ℕ) (x : (orderedSimplicialSet K).nonDegenerate n) :
    orderedNormalizedChainEquiv (k := k) K n
        (((orderedSimplicialSet K).ιNormalizedChainComplex
          (R := ModuleCat.of k k) x.1).hom 1) =
      Pi.single (orderedNondegenerateFaceEquiv K n x) 1 := by
  let s := orderedNondegenerateFaceEquiv K n x
  have hy : orderedSimplexOfFace K s.1 s.2.1 s.2.2 = x := by
    exact (orderedNondegenerateFaceEquiv K n).symm_apply_apply x
  have h := orderedNormalizedChainEquiv_generator (k := k) K n s
  rw [show (orderedSimplexOfFace K s.1 s.2.1 s.2.2).1 = x.1 from
    congrArg Subtype.val hy] at h
  simpa [s] using h

noncomputable def orderedNormalizedBoundary (K : PreAbstractSimplicialComplex ι)
    [Finite K.faces] (n : ℕ) :
    ({s : Finset ι // s ∈ K ∧ s.card = n + 2} → k) →ₗ[k]
      ({s : Finset ι // s ∈ K ∧ s.card = n + 1} → k) := by
  let C := (orderedSimplicialSet K).normalizedChainComplex (ModuleCat.of k k)
  let eTop := orderedNormalizedChainEquiv (k := k) K (n + 1)
  exact (orderedNormalizedChainEquiv (k := k) K n).toLinearMap.comp
    ((C.d (n + 1) n).hom.comp eTop.symm.toLinearMap)

theorem vertices_delta_orderedSimplexOfFace (K : PreAbstractSimplicialComplex ι)
    {n : ℕ} (s : Finset ι) (hs : s ∈ K) (hn : s.card = n + 2) (i : Fin (n + 2)) :
    Finset.univ.image
        (((orderedSimplicialSet K).δ i (orderedSimplexOfFace K s hs hn).1).val.obj) =
      s.erase (s.orderEmbOfFin hn i) := by
  classical
  ext v
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase]
  constructor
  · rintro ⟨j, hj⟩
    change s.orderEmbOfFin hn (i.succAbove j) = v at hj
    refine ⟨?_, ?_⟩
    · intro hv
      have heq : i.succAbove j = i := by
        apply (s.orderEmbOfFin hn).injective
        exact hj.trans hv
      exact Fin.succAbove_ne i j heq
    · rw [← hj]
      exact Finset.orderEmbOfFin_mem s hn _
  · rintro ⟨hvi, hvs⟩
    have hvRange : v ∈ Set.range (s.orderEmbOfFin hn) := by
      rw [Finset.range_orderEmbOfFin]
      exact hvs
    obtain ⟨j, hj⟩ := hvRange
    have hji : j ≠ i := by
      intro hji
      apply hvi
      rw [← hj, hji]
    obtain ⟨q, hq⟩ := Fin.exists_succAbove_eq hji
    refine ⟨q, ?_⟩
    change s.orderEmbOfFin hn (i.succAbove q) = v
    rw [hq, hj]

def orderedFaceErase (K : PreAbstractSimplicialComplex ι) {n : ℕ}
    (s : {s : Finset ι // s ∈ K ∧ s.card = n + 2}) (i : Fin (n + 2)) :
    {t : Finset ι // t ∈ K ∧ t.card = n + 1} := by
  let v := s.1.orderEmbOfFin s.2.2 i
  have hv : v ∈ s.1 := Finset.orderEmbOfFin_mem s.1 s.2.2 i
  refine ⟨s.1.erase v, ?_, ?_⟩
  · exact (K.isRelLowerSet_faces s.2.1).2 (Finset.erase_subset v s.1)
      (Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hv, s.2.2]; omega))
  · rw [Finset.card_erase_of_mem hv, s.2.2]
    omega

theorem orderedSimplicialSet_nonDegenerate_delta (K : PreAbstractSimplicialComplex ι)
    {n : ℕ} (x : (orderedSimplicialSet K).nonDegenerate (n + 1)) (i : Fin (n + 2)) :
    (orderedSimplicialSet K).δ i x.1 ∈ (orderedSimplicialSet K).nonDegenerate n := by
  let _ : (orderedSimplicialSet K).Nonsingular := by
    unfold orderedSimplicialSet
    infer_instance
  exact SSet.nonDegenerate_δ x.2 i

theorem orderedNondegenerateFaceEquiv_delta (K : PreAbstractSimplicialComplex ι)
    {n : ℕ} (s : {s : Finset ι // s ∈ K ∧ s.card = n + 2}) (i : Fin (n + 2)) :
    orderedNondegenerateFaceEquiv K n
        ⟨(orderedSimplicialSet K).δ i (orderedSimplexOfFace K s.1 s.2.1 s.2.2).1,
          orderedSimplicialSet_nonDegenerate_delta K
            (orderedSimplexOfFace K s.1 s.2.1 s.2.2) i⟩ =
      orderedFaceErase K s i := by
  apply Subtype.ext
  exact vertices_delta_orderedSimplexOfFace K s.1 s.2.1 s.2.2 i

theorem orderedNormalizedBoundary_single (K : PreAbstractSimplicialComplex ι)
    [Finite K.faces] (n : ℕ)
    (s : {s : Finset ι // s ∈ K ∧ s.card = n + 2}) :
    orderedNormalizedBoundary (k := k) K n (Pi.single s 1) =
      ∑ i : Fin (n + 2), (-1 : k) ^ i.1 • Pi.single (orderedFaceErase K s i) 1 := by
  classical
  let X := orderedSimplicialSet K
  let x := orderedSimplexOfFace K s.1 s.2.1 s.2.2
  let C := X.normalizedChainComplex (ModuleCat.of k k)
  let eTop := orderedNormalizedChainEquiv (k := k) K (n + 1)
  have hinput : eTop.symm (Pi.single s 1) =
      (X.ιNormalizedChainComplex (R := ModuleCat.of k k) x.1).hom 1 := by
    apply eTop.injective
    simp only [eTop, LinearEquiv.apply_symm_apply]
    exact (orderedNormalizedChainEquiv_generator (k := k) K (n + 1) s).symm
  change orderedNormalizedChainEquiv (k := k) K n
      ((C.d (n + 1) n).hom (eTop.symm (Pi.single s 1))) = _
  rw [hinput]
  have hd := X.ιNormalizedChainComplex_d (R := ModuleCat.of k k) x.1
  have hd1 := congr($(hd) (1 : k))
  change (C.d (n + 1) n).hom
      ((X.ιNormalizedChainComplex (R := ModuleCat.of k k) x.1).hom 1) = _ at hd1
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_zsmul,
    LinearMap.smul_apply] at hd1
  rw [hd1, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_zsmul]
  rw [orderedNormalizedChainEquiv_ι (k := k) K n
    ⟨X.δ i x.1, orderedSimplicialSet_nonDegenerate_delta K x i⟩]
  rw [orderedNondegenerateFaceEquiv_delta K s i]
  rw [← Int.cast_smul_eq_zsmul k]
  simp

end DifferentialGeometry.Topology.SimplicialComplex

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u
variable {E : Type u}

theorem incidenceIndex_orderEmbOfFin (r : LinearOrder E) (s : Finset E)
    {n : ℕ} (hn : s.card = n) (i : Fin n) :
    incidenceIndex r s (s.orderEmbOfFin hn i) = i := by
  let _ := r
  classical
  have hfilter : s.filter (fun w => w < s.orderEmbOfFin hn i) =
      (Finset.Iio i).image (s.orderEmbOfFin hn) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Iio]
    constructor
    · rintro ⟨hws, hwi⟩
      have hwRange : w ∈ Set.range (s.orderEmbOfFin hn) := by
        rw [Finset.range_orderEmbOfFin]
        exact hws
      obtain ⟨j, rfl⟩ := hwRange
      exact ⟨j, (s.orderEmbOfFin hn).lt_iff_lt.mp hwi, rfl⟩
    · rintro ⟨j, hji, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem s hn j, (s.orderEmbOfFin hn).lt_iff_lt.mpr hji⟩
  rw [incidenceIndex, hfilter, Finset.card_image_of_injective _
    (s.orderEmbOfFin hn).injective, Fin.card_Iio]

theorem incidenceSign_orderEmbOfFin (r : LinearOrder E) (s : Finset E)
    {n : ℕ} (hn : s.card = n) (i : Fin n) :
    incidenceSign r s (s.orderEmbOfFin hn i) = (-1 : ℤ) ^ i.1 := by
  let _ := r
  rw [incidenceSign, incidenceIndex_orderEmbOfFin r s hn i]

end DifferentialGeometry.Topology.PiecewiseLinear

namespace DifferentialGeometry.Topology.SimplicialComplex

universe u
variable {k ι : Type u} [Field k] [LinearOrder ι]

theorem orderedNormalizedBoundary_single_apply (K : PreAbstractSimplicialComplex ι)
    [Finite K.faces] (n : ℕ)
    (s : {s : Finset ι // s ∈ K ∧ s.card = n + 2})
    (t : {t : Finset ι // t ∈ K ∧ t.card = n + 1}) :
    orderedNormalizedBoundary (k := k) K n (Pi.single s 1) t =
      (DifferentialGeometry.Topology.PiecewiseLinear.simplexBoundaryCoefficient
        (inferInstance : LinearOrder ι) s.1 t.1 : k) := by
  classical
  let f : ι → k := fun v =>
    if s.1.erase v = t.1 then
      (DifferentialGeometry.Topology.PiecewiseLinear.incidenceSign
        (inferInstance : LinearOrder ι) s.1 v : k)
    else 0
  calc
    orderedNormalizedBoundary (k := k) K n (Pi.single s 1) t =
        (∑ i : Fin (n + 2), (-1 : k) ^ i.1 • Pi.single (orderedFaceErase K s i) 1) t :=
      congrFun (orderedNormalizedBoundary_single (k := k) K n s) t
    _ = ∑ i : Fin (n + 2), f ((s.1.orderIsoOfFin s.2.2) i) := by
      simp only [Finset.sum_apply, Pi.smul_apply]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hst : orderedFaceErase K s i = t
      · subst t
        rw [Pi.single_eq_same]
        simp [f, orderedFaceErase,
          DifferentialGeometry.Topology.PiecewiseLinear.incidenceSign_orderEmbOfFin]
      · have hv : s.1.erase (s.1.orderEmbOfFin s.2.2 i) ≠ t.1 := by
          intro hv
          apply hst
          apply Subtype.ext
          exact hv
        rw [Pi.single_eq_of_ne (fun h => hst h.symm)]
        simp [f, hv]
    _ = ∑ v : s.1, f v :=
      (s.1.orderIsoOfFin s.2.2).toEquiv.sum_comp (fun v : s.1 => f v)
    _ = ∑ v ∈ s.1, if s.1.erase v = t.1 then
          (DifferentialGeometry.Topology.PiecewiseLinear.incidenceSign
            (inferInstance : LinearOrder ι) s.1 v : k) else 0 := by
      change (∑ v : s.1, f v) = ∑ v ∈ s.1, f v
      simpa only using Finset.sum_coe_sort s.1 f
    _ = _ := by
      rw [DifferentialGeometry.Topology.PiecewiseLinear.simplexBoundaryCoefficient]
      push_cast
      rfl

theorem orderedNormalizedBoundary_apply (K : PreAbstractSimplicialComplex ι)
    [Finite K.faces] (n : ℕ)
    (c : {s : Finset ι // s ∈ K ∧ s.card = n + 2} → k)
    (t : {t : Finset ι // t ∈ K ∧ t.card = n + 1}) :
    orderedNormalizedBoundary (k := k) K n c t =
      ∑ᶠ s, c s *
        (DifferentialGeometry.Topology.PiecewiseLinear.simplexBoundaryCoefficient
          (inferInstance : LinearOrder ι) s.1 t.1 : k) := by
  classical
  let _ : Finite {s : Finset ι // s ∈ K ∧ s.card = n + 2} :=
    Finite.of_injective
      (fun s => (⟨s.1, s.2.1⟩ : K.faces))
      (fun _ _ h => Subtype.ext (congrArg (fun x : K.faces => x.1) h))
  let _ : Fintype {s : Finset ι // s ∈ K ∧ s.card = n + 2} := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  have hdecomp : c = ∑ s, Pi.single s (c s) := by
    ext s
    simpa only [Finset.sum_apply] using (Fintype.sum_pi_single s c).symm
  calc
    orderedNormalizedBoundary (k := k) K n c t =
        orderedNormalizedBoundary (k := k) K n (∑ s, Pi.single s (c s)) t :=
      congrArg (fun x => orderedNormalizedBoundary (k := k) K n x t) hdecomp
    _ = ∑ s, orderedNormalizedBoundary (k := k) K n (Pi.single s (c s)) t := by
      rw [map_sum, Finset.sum_apply]
    _ = ∑ s, c s *
        (DifferentialGeometry.Topology.PiecewiseLinear.simplexBoundaryCoefficient
          (inferInstance : LinearOrder ι) s.1 t.1 : k) := by
      apply Finset.sum_congr rfl
      intro s hs
      have hsingle : Pi.single s (c s) = c s • Pi.single s (1 : k) := by
        ext u
        by_cases hsu : s = u <;> simp [hsu]
      rw [hsingle, map_smul, Pi.smul_apply,
        orderedNormalizedBoundary_single_apply]
      exact smul_eq_mul (c s) _

end DifferentialGeometry.Topology.SimplicialComplex
