/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
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
noncomputable def localOrientationSign (r : LinearOrder E)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s)) (s t : Finset E) : ℤ :=
  if hs : s ∈ K.faces then ((o s hs).changeVertexOrder r).sign t else 0

open Classical in
theorem localOrientationSign_eq_one_or_neg_one (r : LinearOrder E)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    (hst : s ⊆ t) (htcard : t.card = n + 1) :
    localOrientationSign r o s t = 1 ∨ localOrientationSign r o s t = -1 := by
  simpa only [localOrientationSign, dite_eq_left hs] using
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
  simpa only [p, q, CoherentOrientation.restrict, localOrientationSign, dite_eq_left hs, dite_eq_left ht]
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
  rw [localOrientationParity, dite_eq_left hu]
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
noncomputable def localSubdivisionOrientationSign
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
    (a : E) (q : Finset E) : ℤ :=
  let r : LinearOrder E := linearOrderOfSTO WellOrderingRel
  let _ : DecidableEq E := Classical.decEq E
  if hq : q.card = n + 1 then
    let S := carrierFace K (q.centroid ℝ id)
    if hS : S.card = n + 1 then
      affineSimplexOrientationSign r hq hS * localOrientationSign r o (carrierFace K a) S
    else 0
  else 0

open Classical in
theorem localSubdivisionOrientationSign_eq_one_or_neg_one
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
    {a : E} {q : Finset E} (hq : q ∈ (barycentricSubdivision K).faces)
    (ha : a ∈ q) (hqcard : q.card = n + 1) :
    localSubdivisionOrientationSign o a q = 1 ∨
      localSubdivisionOrientationSign o a q = -1 := by
  let r : LinearOrder E := linearOrderOfSTO WellOrderingRel
  let _ : DecidableEq E := Classical.decEq E
  let S := carrierFace K (q.centroid ℝ id)
  have hspec := subdivision_carrierFace_spec (barycentricSubdivision_isSubdivision K) hq
  have hbound : ∀ t ∈ K.faces, t.card ≤ n + 1 := by
    cases n with
    | zero => exact fun _ ht => hK.card_le_one ht
    | succ n => exact fun _ ht => hK.card_le K ht
  have hScard : S.card = n + 1 :=
    subdivision_carrierFace_card (barycentricSubdivision_isSubdivision K) hbound hq hqcard
  have haK := carrierFace_mem_of_mem_barycentricSubdivision hq ha
  have haSpace : a ∈ K.space := by
    rw [← (barycentricSubdivision_isSubdivision K).space_eq]
    exact (barycentricSubdivision K).subset_space hq ha
  have haS : carrierFace K a ⊆ S :=
    carrierFace_subset haSpace hspec.1 (hspec.2 (subset_convexHull ℝ _ ha))
  have haff := affineSimplexOrientationSign_eq_one_or_neg_one r hqcard hScard
    ((barycentricSubdivision K).indep hq) hspec.2
  have hlocal := localOrientationSign_eq_one_or_neg_one r o haK hspec.1 haS hScard
  rw [localSubdivisionOrientationSign, dite_eq_left hqcard, dite_eq_left hScard]
  change affineSimplexOrientationSign r hqcard hScard *
      localOrientationSign r o (carrierFace K a) S = 1 ∨
    affineSimplexOrientationSign r hqcard hScard *
      localOrientationSign r o (carrierFace K a) S = -1
  rcases haff with haff | haff <;> rcases hlocal with hlocal | hlocal
  all_goals rw [haff, hlocal]
  all_goals norm_num

open Classical in
theorem orientationCocycle_parity_eq_localSubdivisionOrientationSign
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
    {a b : E} {q : Finset E} (hq : q ∈ (barycentricSubdivision K).faces)
    (ha : a ∈ q) (hb : b ∈ q) (hqcard : q.card = n + 1) :
    (orientationCocycle hK o).parity a b =
      decide (localSubdivisionOrientationSign o a q *
        localSubdivisionOrientationSign o b q = -1) := by
  let r : LinearOrder E := linearOrderOfSTO WellOrderingRel
  let _ : DecidableEq E := Classical.decEq E
  let S := carrierFace K (q.centroid ℝ id)
  have hspec := subdivision_carrierFace_spec (barycentricSubdivision_isSubdivision K) hq
  have hbound : ∀ t ∈ K.faces, t.card ≤ n + 1 := by
    cases n with
    | zero => exact fun _ ht => hK.card_le_one ht
    | succ n => exact fun _ ht => hK.card_le K ht
  have hScard : S.card = n + 1 :=
    subdivision_carrierFace_card (barycentricSubdivision_isSubdivision K) hbound hq hqcard
  have haK := carrierFace_mem_of_mem_barycentricSubdivision hq ha
  have hbK := carrierFace_mem_of_mem_barycentricSubdivision hq hb
  have haSpace : a ∈ K.space := by
    rw [← (barycentricSubdivision_isSubdivision K).space_eq]
    exact (barycentricSubdivision K).subset_space hq ha
  have hbSpace : b ∈ K.space := by
    rw [← (barycentricSubdivision_isSubdivision K).space_eq]
    exact (barycentricSubdivision K).subset_space hq hb
  have haS : carrierFace K a ⊆ S :=
    carrierFace_subset haSpace hspec.1 (hspec.2 (subset_convexHull ℝ _ ha))
  have hbS : carrierFace K b ⊆ S :=
    carrierFace_subset hbSpace hspec.1 (hspec.2 (subset_convexHull ℝ _ hb))
  have haff := affineSimplexOrientationSign_eq_one_or_neg_one r hqcard hScard
    ((barycentricSubdivision K).indep hq) hspec.2
  have hlocalA := localOrientationSign_eq_one_or_neg_one r o haK hspec.1 haS hScard
  have hlocalB := localOrientationSign_eq_one_or_neg_one r o hbK hspec.1 hbS hScard
  change localOrientationParity hK r o (carrierFace K a) (carrierFace K b) = _
  rw [localOrientationParity_eq hK r o haK hbK hspec.1 hScard haS hbS]
  rw [localSubdivisionOrientationSign, dite_eq_left hqcard, dite_eq_left hScard,
    localSubdivisionOrientationSign, dite_eq_left hqcard, dite_eq_left hScard]
  change decide (localOrientationSign r o (carrierFace K a) S *
      localOrientationSign r o (carrierFace K b) S = -1) =
    decide ((affineSimplexOrientationSign r hqcard hScard *
      localOrientationSign r o (carrierFace K a) S) *
      (affineSimplexOrientationSign r hqcard hScard *
        localOrientationSign r o (carrierFace K b) S) = -1)
  rcases haff with haff | haff <;> rcases hlocalA with hlocalA | hlocalA <;>
    rcases hlocalB with hlocalB | hlocalB
  all_goals rw [haff, hlocalA, hlocalB]
  all_goals decide

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
      simpa only [ps, os, CoherentOrientation.restrict, localOrientationSign, dite_eq_left hs] using
          hratio
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
  rw [dite_eq_left haK, dite_eq_left hcK, hb _ haK S hS hScard (hsub a ha),
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
theorem localSubdivisionOrientationSign_flip_of_orientationCocycle
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
    {a b : E} {q : Finset E} (hq : q ∈ (barycentricSubdivision K).faces)
    (ha : a ∈ q) (hb : b ∈ q) (hqcard : q.card = n + 1)
    (d e : Bool)
    (hparity : (orientationCocycle hK o).parity a b = Bool.xor d e) :
    (if d then -1 else 1) * localSubdivisionOrientationSign o a q =
      (if e then -1 else 1) * localSubdivisionOrientationSign o b q := by
  apply sign_flip_eq_of_parity
    (localSubdivisionOrientationSign_eq_one_or_neg_one hK o hq ha hqcard)
    (localSubdivisionOrientationSign_eq_one_or_neg_one hK o hq hb hqcard)
  rw [← orientationCocycle_parity_eq_localSubdivisionOrientationSign hK o hq ha hb hqcard]
  exact hparity

open Classical in
theorem localSubdivisionOrientationSign_pair_cancel
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (o : ∀ s ∈ K.faces, CoherentOrientation (n + 1) (faceStarComplex K s))
    {a : E} {f q p : Finset E}
    (hf : f ∈ (barycentricSubdivision K).faces)
    (hq : q ∈ (barycentricSubdivision K).faces)
    (hp : p ∈ (barycentricSubdivision K).faces)
    (ha : a ∈ f) (hfq : f ⊆ q) (hfp : f ⊆ p) (hqp : q ≠ p)
    (hfcard : f.card = n + 1) (hqcard : q.card = n + 2)
    (hpcard : p.card = n + 2) :
    localSubdivisionOrientationSign o a q *
        simplexBoundaryCoefficient (linearOrderOfSTO WellOrderingRel) q f +
      localSubdivisionOrientationSign o a p *
        simplexBoundaryCoefficient (linearOrderOfSTO WellOrderingRel) p f = 0 := by
  let r : LinearOrder E := linearOrderOfSTO WellOrderingRel
  let _ : DecidableEq E := Classical.decEq E
  let s := carrierFace K a
  let S := carrierFace K (q.centroid ℝ id)
  let T := carrierFace K (p.centroid ℝ id)
  have hqspec := subdivision_carrierFace_spec (barycentricSubdivision_isSubdivision K) hq
  have hpspec := subdivision_carrierFace_spec (barycentricSubdivision_isSubdivision K) hp
  have hbound : ∀ u ∈ K.faces, u.card ≤ n + 2 := by
    intro u hu
    simpa [Nat.add_assoc] using hK.card_le K hu
  have hScard : S.card = n + 2 :=
    subdivision_carrierFace_card (barycentricSubdivision_isSubdivision K) hbound hq hqcard
  have hTcard : T.card = n + 2 :=
    subdivision_carrierFace_card (barycentricSubdivision_isSubdivision K) hbound hp hpcard
  have hqtop : q.card = (n + 1) + 1 := by omega
  have hptop : p.card = (n + 1) + 1 := by omega
  have hStop : S.card = (n + 1) + 1 := by omega
  have hTtop : T.card = (n + 1) + 1 := by omega
  have hStop' : (carrierFace K (q.centroid ℝ id)).card = (n + 1) + 1 := by
    simpa only [S] using hStop
  have hTtop' : (carrierFace K (p.centroid ℝ id)).card = (n + 1) + 1 := by
    simpa only [T] using hTtop
  have hs : s ∈ K.faces := carrierFace_mem_of_mem_barycentricSubdivision hf ha
  have hs' : carrierFace K a ∈ K.faces := by simpa only [s] using hs
  have haSpace : a ∈ K.space := by
    rw [← (barycentricSubdivision_isSubdivision K).space_eq]
    exact (barycentricSubdivision K).subset_space hf ha
  have hsS : s ⊆ S := carrierFace_subset haSpace hqspec.1
    (hqspec.2 (subset_convexHull ℝ (q : Set E) (hfq ha)))
  have hsT : s ⊆ T := carrierFace_subset haSpace hpspec.1
    (hpspec.2 (subset_convexHull ℝ (p : Set E) (hfp ha)))
  have hSlocal : S ∈ (faceStarComplex K s).faces :=
    mem_faceStarComplex_faces_of_subset K hqspec.1 hsS
  have hTlocal : T ∈ (faceStarComplex K s).faces :=
    mem_faceStarComplex_faces_of_subset K hpspec.1 hsT
  let olocal := (o s hs).changeVertexOrder r
  have hcancel := olocal.affine_coface_pair_cancel (hK.faceStar hs)
    (barycentricSubdivision K) hq hp hqp hfq hfp hfcard hqcard hpcard
    hSlocal hTlocal hScard hTcard hqspec.2 hpspec.2
  simpa only [r, s, S, T, olocal, CoherentOrientation.changeVertexOrder,
    localSubdivisionOrientationSign, dite_eq_left hqtop, dite_eq_left hStop',
    dite_eq_left hptop, dite_eq_left hTtop', localOrientationSign, dite_eq_left hs'] using hcancel

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
    rcases localOrientationSign_eq_one_or_neg_one r o hS hS (Finset.Subset.refl S) hScard with hs |
        hs <;>
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
      simpa only [ot, CoherentOrientation.changeVertexOrder, localOrientationSign, dite_eq_left ht]
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
