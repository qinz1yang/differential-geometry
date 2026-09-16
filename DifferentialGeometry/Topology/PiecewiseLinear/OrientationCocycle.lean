import DifferentialGeometry.Topology.PiecewiseLinear.DerivedCarrier
import DifferentialGeometry.Topology.PiecewiseLinear.DoubleCoverComplex
import DifferentialGeometry.Topology.PiecewiseLinear.FaceStarBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Orientation

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (s : Finset E) :
    Finite (faceStarComplex K s).faces := (faceStarComplex_faces_finite K s).to_subtype

open Classical in
theorem faceStarComplex_antitone (K : Geometry.SimplicialComplex ℝ E)
    {s t : Finset E} (hst : s ⊆ t) : faceStarComplex K t ≤ faceStarComplex K s := by
  intro u hu
  exact ⟨hu.1, K.down_closed hu.2 (Finset.union_subset_union (Finset.Subset.refl u) hst)
    ((K.nonempty_of_mem_faces hu.1).mono Finset.subset_union_left)⟩

variable {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces] {n : ℕ}

open Classical in
private noncomputable def localOrientationSign (r : LinearOrder E)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s)) (s t : Finset E) : ℤ :=
  if hs : s ∈ K.faces then ((o s hs).changeVertexOrder r).sign t else 0

open Classical in
private theorem localOrientationSign_eq_one_or_neg_one (r : LinearOrder E)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    (hst : s ⊆ t) (htcard : t.card = n + 1) :
    localOrientationSign r o s t = 1 ∨ localOrientationSign r o s t = -1 := by
  simpa only [localOrientationSign, dif_pos hs] using
    ((o s hs).changeVertexOrder r).sign_top t (mem_faceStarComplex_faces_of_subset K ht hst) htcard

open Classical in
theorem faceCofaces_faceStarComplex_self (s : Finset E) (m : ℕ) :
    faceCofaces (faceStarComplex K s) s m = faceCofaces K s m := by
  ext t
  rw [mem_faceCofaces, mem_faceCofaces]
  constructor
  · rintro ⟨ht, hcard, hst⟩
    exact ⟨ht.1, hcard, hst⟩
  · rintro ⟨ht, hcard, hst⟩
    exact ⟨mem_faceStarComplex_faces_of_subset K ht hst, hcard, hst⟩

variable [FiniteDimensional ℝ E]

open Classical in
private theorem localOrientationSign_mul_eq
    (hK : IsCombinatorialManifoldWithBoundary n K) (r : LinearOrder E)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
    {s t u S T : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hu : u ∈ K.faces)
    (hsu : s ⊆ u) (htu : t ⊆ u) (hS : S ∈ K.faces) (hT : T ∈ K.faces)
    (hScard : S.card = n + 1) (hTcard : T.card = n + 1) (huS : u ⊆ S) (huT : u ⊆ T) :
    localOrientationSign r o s S * localOrientationSign r o t S =
      localOrientationSign r o s T * localOrientationSign r o t T := by
  let p := ((o s hs).changeVertexOrder r).restrict (faceStarComplex K s) (faceStarComplex K u)
    (faceStarComplex_antitone K hsu) (hK.faceStar hs) (hK.faceStar hu)
  let q := ((o t ht).changeVertexOrder r).restrict (faceStarComplex K t) (faceStarComplex K u)
    (faceStarComplex_antitone K htu) (hK.faceStar ht) (hK.faceStar hu)
  have hSu := mem_faceStarComplex_faces_of_subset K hS huS
  have hTu := mem_faceStarComplex_faces_of_subset K hT huT
  have heq := p.sign_mul_sign_eq_of_dualGraph_reachable (hK.faceStar hu) q rfl
    (hK.dualGraph_faceStarComplex_preconnected hu ⟨S, hSu, hScard⟩ ⟨T, hTu, hTcard⟩)
  simpa only [p, q, CoherentOrientation.restrict, localOrientationSign, dif_pos hs, dif_pos ht]
    using heq

open Classical in
private noncomputable def localOrientationParity
    (hK : IsCombinatorialManifoldWithBoundary n K) (r : LinearOrder E)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s)) (s t : Finset E) : Bool :=
  if h : s ∪ t ∈ K.faces then
    let S := (hK.exists_face_superset_card_eq h).choose
    decide (localOrientationSign r o s S * localOrientationSign r o t S = -1)
  else false

open Classical in
private theorem localOrientationParity_eq
    (hK : IsCombinatorialManifoldWithBoundary n K) (r : LinearOrder E)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
    {s t S : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hS : S ∈ K.faces)
    (hScard : S.card = n + 1) (hsS : s ⊆ S) (htS : t ⊆ S) :
    localOrientationParity hK r o s t =
      decide (localOrientationSign r o s S * localOrientationSign r o t S = -1) := by
  have hu : s ∪ t ∈ K.faces := K.down_closed hS (Finset.union_subset hsS htS)
    ((K.nonempty_of_mem_faces hs).mono Finset.subset_union_left)
  rw [localOrientationParity, dif_pos hu]
  dsimp only
  have htop := (hK.exists_face_superset_card_eq hu).choose_spec
  rw [localOrientationSign_mul_eq hK r o hs ht hu Finset.subset_union_left
    Finset.subset_union_right htop.1 hS htop.2.2 hScard htop.2.1
      (Finset.union_subset hsS htS)]

private theorem xor_decide_sign_mul {a b c : ℤ}
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) (hc : c = 1 ∨ c = -1) :
    Bool.xor (decide (a * b = -1)) (decide (b * c = -1)) = decide (a * c = -1) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> decide

open Classical in
private theorem exists_topFace_superset_carrierFaces
    (hK : IsCombinatorialManifoldWithBoundary n K) {f : Finset E}
    (hf : f ∈ (barycentricSubdivision K).faces) :
    ∃ S ∈ K.faces, S.card = n + 1 ∧ ∀ x ∈ f, carrierFace K x ⊆ S := by
  obtain ⟨s, hs, hsub⟩ := exists_face_superset_carrierFaces_of_mem_barycentricSubdivision hf
  obtain ⟨S, hS, hsS, hcard⟩ := hK.exists_face_superset_card_eq hs
  exact ⟨S, hS, hcard, fun x hx => (hsub x hx).trans hsS⟩

open Classical in
noncomputable def orientationCocycle
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s)) :
    SimplicialBoolCocycle (barycentricSubdivision K) := by
  let r : LinearOrder E := linearOrderOfSTO WellOrderingRel
  let _ : DecidableEq E := Classical.decEq E
  refine {
    parity := fun a b => localOrientationParity hK r o (carrierFace K a) (carrierFace K b)
    symm := ?_
    self := ?_
    cocycle := ?_ }
  · intro a b hab
    have ha : a ∈ ({a, b} : Finset E) := by simp
    have hb : b ∈ ({a, b} : Finset E) := by simp
    have haK := carrierFace_mem_of_mem_barycentricSubdivision hab ha
    have hbK := carrierFace_mem_of_mem_barycentricSubdivision hab hb
    obtain ⟨S, hS, hScard, hsub⟩ := exists_topFace_superset_carrierFaces hK hab
    rw [localOrientationParity_eq hK r o haK hbK hS hScard (hsub a ha) (hsub b hb),
      localOrientationParity_eq hK r o hbK haK hS hScard (hsub b hb) (hsub a ha), mul_comm]
  · intro a ha
    have haa := Finset.mem_singleton_self a
    have haK := carrierFace_mem_of_mem_barycentricSubdivision ha haa
    obtain ⟨S, hS, hScard, hsub⟩ := exists_topFace_superset_carrierFaces hK ha
    rw [localOrientationParity_eq hK r o haK haK hS hScard (hsub a haa) (hsub a haa)]
    rcases localOrientationSign_eq_one_or_neg_one r o haK hS (hsub a haa) hScard with h | h <;>
      rw [h] <;> decide
  · intro a b c habc
    have ha : a ∈ ({a, b, c} : Finset E) := by simp
    have hb : b ∈ ({a, b, c} : Finset E) := by simp
    have hc : c ∈ ({a, b, c} : Finset E) := by simp
    have haK := carrierFace_mem_of_mem_barycentricSubdivision habc ha
    have hbK := carrierFace_mem_of_mem_barycentricSubdivision habc hb
    have hcK := carrierFace_mem_of_mem_barycentricSubdivision habc hc
    obtain ⟨S, hS, hScard, hsub⟩ := exists_topFace_superset_carrierFaces hK habc
    rw [localOrientationParity_eq hK r o haK hbK hS hScard (hsub a ha) (hsub b hb),
      localOrientationParity_eq hK r o hbK hcK hS hScard (hsub b hb) (hsub c hc),
      localOrientationParity_eq hK r o haK hcK hS hScard (hsub a ha) (hsub c hc)]
    exact xor_decide_sign_mul
      (localOrientationSign_eq_one_or_neg_one r o haK hS (hsub a ha) hScard)
      (localOrientationSign_eq_one_or_neg_one r o hbK hS (hsub b hb) hScard)
      (localOrientationSign_eq_one_or_neg_one r o hcK hS (hsub c hc) hScard)

open Classical in
private theorem orientationCocycle_isCoboundary_of_isOrientable
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
    (h : IsOrientable n K) : (orientationCocycle hK o).IsCoboundary := by
  obtain ⟨q⟩ := h
  let r : LinearOrder E := linearOrderOfSTO WellOrderingRel
  let _ : DecidableEq E := Classical.decEq E
  let p := q.changeVertexOrder r
  have hex (s : Finset E) (hs : s ∈ K.faces) : ∃ b : Bool,
      ∀ S ∈ K.faces, S.card = n + 1 → s ⊆ S →
        b = decide (p.sign S * localOrientationSign r o s S = -1) := by
    obtain ⟨T, hT, hsT, hTcard⟩ := hK.exists_face_superset_card_eq hs
    refine ⟨decide (p.sign T * localOrientationSign r o s T = -1), ?_⟩
    intro S hS hScard hsS
    let ps := p.restrict K (faceStarComplex K s) (faceStarComplex_faces_subset K s)
      hK (hK.faceStar hs)
    let os := (o s hs).changeVertexOrder r
    have hratio := ps.sign_mul_sign_eq_of_dualGraph_reachable (hK.faceStar hs) os rfl
      (hK.dualGraph_faceStarComplex_preconnected hs
        ⟨T, mem_faceStarComplex_faces_of_subset K hT hsT, hTcard⟩
        ⟨S, mem_faceStarComplex_faces_of_subset K hS hsS, hScard⟩)
    have heq : p.sign T * localOrientationSign r o s T =
        p.sign S * localOrientationSign r o s S := by
      simpa only [ps, os, CoherentOrientation.restrict, localOrientationSign, dif_pos hs] using hratio
    rw [heq]
  choose b hb using hex
  refine ⟨fun a => if ha : carrierFace K a ∈ K.faces then b (carrierFace K a) ha else false, ?_⟩
  intro a c hac
  have ha : a ∈ ({a, c} : Finset E) := by simp
  have hc : c ∈ ({a, c} : Finset E) := by simp
  have haK := carrierFace_mem_of_mem_barycentricSubdivision hac ha
  have hcK := carrierFace_mem_of_mem_barycentricSubdivision hac hc
  obtain ⟨S, hS, hScard, hsub⟩ := exists_topFace_superset_carrierFaces hK hac
  change localOrientationParity hK r o (carrierFace K a) (carrierFace K c) = _
  dsimp only
  rw [dif_pos haK, dif_pos hcK, hb _ haK S hS hScard (hsub a ha),
    hb _ hcK S hS hScard (hsub c hc),
    localOrientationParity_eq hK r o haK hcK hS hScard (hsub a ha) (hsub c hc)]
  simpa only [mul_comm] using
    (xor_decide_sign_mul
      (localOrientationSign_eq_one_or_neg_one r o haK hS (hsub a ha) hScard)
      (p.sign_top S hS hScard)
      (localOrientationSign_eq_one_or_neg_one r o hcK hS (hsub c hc) hScard)).symm

private theorem sign_flip_eq_of_parity {a b : ℤ}
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) (d e : Bool)
    (h : decide (a * b = -1) = Bool.xor d e) :
    (if d then -1 else 1) * a = (if e then -1 else 1) * b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> cases d <;> cases e <;> norm_num at *

open Classical in
private theorem isOrientable_of_orientationCocycle_isCoboundary
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
    (h : (orientationCocycle hK o).IsCoboundary) : IsOrientable n K := by
  obtain ⟨δ, hδ⟩ := h
  let r : LinearOrder E := linearOrderOfSTO WellOrderingRel
  let _ : DecidableEq E := Classical.decEq E
  let g (S : Finset E) : ℤ :=
    (if δ (S.centroid ℝ id) then -1 else 1) * localOrientationSign r o S S
  have hg (t S : Finset E) (ht : t ∈ K.faces) (hS : S ∈ K.faces)
      (hScard : S.card = n + 1) (htS : t ⊆ S) :
      g S = (if δ (t.centroid ℝ id) then -1 else 1) * localOrientationSign r o t S := by
    have heq := hδ _ _ (pair_centroid_mem_barycentricSubdivision ht hS htS)
    change localOrientationParity hK r o (carrierFace K (t.centroid ℝ id))
      (carrierFace K (S.centroid ℝ id)) = _ at heq
    rw [carrierFace_centroid ht, carrierFace_centroid hS,
      localOrientationParity_eq hK r o ht hS hS hScard htS (Finset.Subset.refl S)] at heq
    exact (sign_flip_eq_of_parity
      (localOrientationSign_eq_one_or_neg_one r o ht hS htS hScard)
      (localOrientationSign_eq_one_or_neg_one r o hS hS (Finset.Subset.refl S) hScard)
      _ _ heq).symm
  refine ⟨{
    vertexOrder := r
    sign := g
    sign_top := ?_
    coherent := ?_ }⟩
  · intro S hS hScard
    rcases localOrientationSign_eq_one_or_neg_one r o hS hS (Finset.Subset.refl S) hScard with hs | hs <;>
      cases hd : δ (S.centroid ℝ id) <;> simp only [g, hd, hs] <;> norm_num
  · intro t ht htcard hnotone
    let ot := (o t ht).changeVertexOrder r
    have htstar : t ∈ (faceStarComplex K t).faces :=
      mem_faceStarComplex_faces_of_subset K ht (Finset.Subset.refl t)
    have hold := ot.coherent t htstar htcard (by
      rwa [faceCofaces_faceStarComplex_self])
    rw [orientedBoundary_eq_sum_faceCofaces, faceCofaces_faceStarComplex_self] at hold
    have hsum : (∑ S ∈ faceCofaces K t (n + 1),
        localOrientationSign r o t S * simplexBoundaryCoefficient r S t) = 0 := by
      simpa only [ot, CoherentOrientation.changeVertexOrder, localOrientationSign, dif_pos ht]
        using hold
    rw [orientedBoundary_eq_sum_faceCofaces]
    calc
      (∑ S ∈ faceCofaces K t (n + 1), g S * simplexBoundaryCoefficient r S t) =
          (if δ (t.centroid ℝ id) then -1 else 1) *
            (∑ S ∈ faceCofaces K t (n + 1),
              localOrientationSign r o t S * simplexBoundaryCoefficient r S t) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S hS
        obtain ⟨hSK, hScard, htS⟩ := (mem_faceCofaces K).mp hS
        rw [hg t S ht hSK hScard htS, mul_assoc]
      _ = 0 := by rw [hsum, mul_zero]

open Classical in
theorem orientationCocycle_isCoboundary_iff
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s)) :
    (orientationCocycle hK o).IsCoboundary ↔ IsOrientable n K :=
  ⟨isOrientable_of_orientationCocycle_isCoboundary hK o,
    orientationCocycle_isCoboundary_of_isOrientable hK o⟩

open Classical in
theorem exists_orientationCocycle_of_not_isOrientable
    (hK : IsCombinatorialManifoldWithBoundary n K) (h : ¬IsOrientable n K) :
    ∃ ε : SimplicialBoolCocycle (barycentricSubdivision K), ¬ε.IsCoboundary := by
  let o (s : Finset E) (hs : s ∈ K.faces) : CoherentOrientation n (faceStarComplex K s) :=
    Classical.choice (isOrientable_faceStarComplex hK hs)
  exact ⟨orientationCocycle hK o, fun hε => h ((orientationCocycle_isCoboundary_iff hK o).mp hε)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
