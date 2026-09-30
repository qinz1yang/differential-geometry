/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ComplexUnion
import DifferentialGeometry.Topology.PiecewiseLinear.Mesh
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexOrientationCocycle
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceBoundaryCapping
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSphereRecognition
import DifferentialGeometry.Topology.PiecewiseLinear.TorusOfOrientableEulerCharZero
import DifferentialGeometry.Topology.SimplicialComplex.EdgeConnectivity

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Gluing

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem SimplicialBoolCocycle.isCoboundary_of_isCoboundary_ofLe
    {M P Q I : Geometry.SimplicialComplex ℝ E} (ε : SimplicialBoolCocycle M)
    (hPM : P.faces ⊆ M.faces) (hQM : Q.faces ⊆ M.faces) (hIP : I.faces ⊆ P.faces)
    (hIQ : I.faces ⊆ Q.faces)
    (hedge : ∀ a b, {a, b} ∈ M.faces → {a, b} ∈ P.faces ∨ {a, b} ∈ Q.faces)
    (hvert : ∀ v, {v} ∈ P.faces → {v} ∈ Q.faces → {v} ∈ I.faces)
    (hconn : (SimplicialComplex.edgeGraph I).Preconnected)
    (hP : (ε.ofLe hPM).IsCoboundary) (hQ : (ε.ofLe hQM).IsCoboundary) : ε.IsCoboundary := by
  obtain ⟨δP, hδP⟩ := hP
  obtain ⟨δQ, hδQ⟩ := hQ
  have hstep : ∀ a b, {a, b} ∈ I.faces →
      Bool.xor (δP a) (δQ a) = Bool.xor (δP b) (δQ b) := by
    intro a b hab
    have h₁ : ε.parity a b = Bool.xor (δP a) (δP b) := hδP a b (hIP hab)
    have h₂ : ε.parity a b = Bool.xor (δQ a) (δQ b) := hδQ a b (hIQ hab)
    rw [h₁] at h₂
    revert h₂
    generalize δP a = p₁
    generalize δP b = p₂
    generalize δQ a = q₁
    generalize δQ b = q₂
    revert p₁ p₂ q₁ q₂
    decide
  have hconst : ∀ u w : I.vertices,
      Bool.xor (δP u) (δQ u) = Bool.xor (δP w) (δQ w) := by
    intro u w
    obtain ⟨p⟩ := hconn u w
    induction p with
    | nil => rfl
    | cons h _ ih => exact (hstep _ _ h.2).trans ih
  obtain ⟨c, hc⟩ : ∃ c : Bool, ∀ v, {v} ∈ I.faces → Bool.xor (δP v) (δQ v) = c := by
    by_cases hne : I.vertices.Nonempty
    · exact ⟨_, fun v hv => hconst ⟨v, hv⟩ ⟨hne.some, hne.some_mem⟩⟩
    · exact ⟨false, fun v hv => (hne ⟨v, hv⟩).elim⟩
  let δ : E → Bool := fun v => if {v} ∈ P.faces then δP v else Bool.xor (δQ v) c
  have hδQ' : ∀ v, {v} ∈ Q.faces → δ v = Bool.xor (δQ v) c := by
    intro v hvQ
    by_cases hvP : {v} ∈ P.faces
    · have h := hc v (hvert v hvP hvQ)
      simp only [δ, ite_eq_left hvP]
      revert h
      generalize δP v = p
      generalize δQ v = q
      cases p <;> cases q <;> cases c <;> simp
    · simp only [δ, ite_eq_right hvP]
  refine ⟨δ, fun a b hab => ?_⟩
  have ha : ({a} : Finset E) ⊆ {a, b} := by simp
  have hb : ({b} : Finset E) ⊆ {a, b} := by simp
  rcases hedge a b hab with habP | habQ
  · have haP := P.down_closed habP ha (Finset.singleton_nonempty a)
    have hbP := P.down_closed habP hb (Finset.singleton_nonempty b)
    have h : ε.parity a b = Bool.xor (δP a) (δP b) := hδP a b habP
    simp only [δ, ite_eq_left haP, ite_eq_left hbP]
    exact h
  · have h : ε.parity a b = Bool.xor (δQ a) (δQ b) := hδQ a b habQ
    rw [hδQ' a (Q.down_closed habQ ha (Finset.singleton_nonempty a)),
      hδQ' b (Q.down_closed habQ hb (Finset.singleton_nonempty b)), h]
    generalize δQ a = q₁
    generalize δQ b = q₂
    cases q₁ <;> cases q₂ <;> cases c <;> simp

open Classical in
private theorem mem_barycentricSubdivision_or_of_faces_subset_union
    {R A B : Geometry.SimplicialComplex ℝ E} (hRAB : R.faces ⊆ A.faces ∪ B.faces)
    {f : Finset E} (hf : f ∈ (barycentricSubdivision R).faces) :
    f ∈ (barycentricSubdivision A).faces ∨ f ∈ (barycentricSubdivision B).faces := by
  obtain ⟨d, hd, hne, rfl⟩ := hf
  obtain ⟨u, hu, htop⟩ := hd.exists_top hne
  have hflag : ∀ L : Geometry.SimplicialComplex ℝ E, u ∈ L.faces → IsFlag L d :=
    fun L huL => ⟨fun s hs => L.down_closed huL (htop s hs)
      (R.nonempty_of_mem_faces (hd.mem_faces hs)), hd.2⟩
  rcases hRAB (hd.mem_faces hu) with huA | huB
  · exact Or.inl ⟨d, hflag A huA, hne, rfl⟩
  · exact Or.inr ⟨d, hflag B huB, hne, rfl⟩

open Classical in
private theorem singleton_mem_barycentricSubdivision_intersectionComplex
    {R A B : Geometry.SimplicialComplex ℝ E} (hAR : A.faces ⊆ R.faces)
    (hBR : B.faces ⊆ R.faces) {v : E} (hvA : {v} ∈ (barycentricSubdivision A).faces)
    (hvB : {v} ∈ (barycentricSubdivision B).faces) :
    {v} ∈ (barycentricSubdivision (intersectionComplex A B)).faces := by
  obtain ⟨d, hd, ⟨s, hs⟩, hdv⟩ := hvA
  obtain ⟨d', hd', ⟨t, ht⟩, hdv'⟩ := hvB
  have hsv : s.centroid ℝ id = v := by
    have hmem : s.centroid ℝ id ∈ ({v} : Finset E) := by
      rw [hdv]
      exact Finset.mem_image_of_mem _ hs
    exact Finset.mem_singleton.mp hmem
  have htv : t.centroid ℝ id = v := by
    have hmem : t.centroid ℝ id ∈ ({v} : Finset E) := by
      rw [hdv']
      exact Finset.mem_image_of_mem _ ht
    exact Finset.mem_singleton.mp hmem
  have hst : s = t := injOn_faces_of_mem_openSimplex R (centroid_mem_openSimplex_of_mem_faces R)
    (hAR (hd.mem_faces hs)) (hBR (hd'.mem_faces ht)) (hsv.trans htv.symm)
  refine ⟨{s}, ⟨fun s' hs' => ?_, fun a ha b hb => ?_⟩, Finset.singleton_nonempty s, ?_⟩
  · rw [Finset.mem_singleton.mp hs']
    exact ⟨hd.mem_faces hs, hst ▸ hd'.mem_faces ht⟩
  · rw [Finset.mem_singleton.mp ha, Finset.mem_singleton.mp hb]
    exact Or.inl subset_rfl
  · rw [Finset.image_singleton]
    exact (congrArg (fun x : E => ({x} : Finset E)) hsv).symm

open Classical in
private theorem isCoboundary_of_barycentricSubdivision_union
    {R A B : Geometry.SimplicialComplex ℝ E} [Finite A.faces]
    (ε : SimplicialBoolCocycle (barycentricSubdivision R))
    (hAR : A.faces ⊆ R.faces) (hBR : B.faces ⊆ R.faces) (hRAB : R.faces ⊆ A.faces ∪ B.faces)
    (hconn : IsPreconnected (A.space ∩ B.space))
    (hA : (ε.ofLe (barycentricSubdivision_faces_subset hAR)).IsCoboundary)
    (hB : (ε.ofLe (barycentricSubdivision_faces_subset hBR)).IsCoboundary) :
    ε.IsCoboundary := by
  let I := intersectionComplex A B
  let _ : Finite I.faces := Finite.Set.subset A.faces fun _ h => h.1
  have hIconn : (SimplicialComplex.edgeGraph (barycentricSubdivision I)).Preconnected := by
    apply edgeGraph_preconnected_of_isPreconnected_space
    rw [(barycentricSubdivision_isSubdivision I).space_eq,
      intersectionComplex_space A B fun s hs t ht => R.inter_subset_convexHull (hAR hs) (hBR ht)]
    exact hconn
  exact ε.isCoboundary_of_isCoboundary_ofLe (I := barycentricSubdivision I)
    (barycentricSubdivision_faces_subset hAR) (barycentricSubdivision_faces_subset hBR)
    (barycentricSubdivision_faces_subset fun _ h => h.1)
    (barycentricSubdivision_faces_subset fun _ h => h.2)
    (fun _ _ h => mem_barycentricSubdivision_or_of_faces_subset_union hRAB h)
    (fun _ hvA hvB => singleton_mem_barycentricSubdivision_intersectionComplex hAR hBR hvA hvB)
    hIconn hA hB

variable [FiniteDimensional ℝ E]

local instance finite_faceStarComplex_faces_orientableGluing
    (M : Geometry.SimplicialComplex ℝ E) [Finite M.faces] (s : Finset E) :
    Finite (faceStarComplex M s).faces := (faceStarComplex_faces_finite M s).to_subtype

open Classical in
private theorem isCoboundary_ofLe_orientationCocycle {n : ℕ}
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
    (hLK : L.faces ⊆ K.faces) (hK : IsCombinatorialManifoldWithBoundary n K)
    (hL : IsCombinatorialManifoldWithBoundary n L)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s)) (hLo : IsOrientable n L) :
    ((orientationCocycle hK o).ofLe (barycentricSubdivision_faces_subset hLK)).IsCoboundary := by
  obtain ⟨δ, hδ⟩ := (orientationCocycle_isCoboundary_iff hL (orientationOfLe hLK hK hL o)).mpr hLo
  exact ⟨δ, fun a b hab =>
    (orientationCocycle_parity_of_faces_subset hLK hK hL o hab).symm.trans (hδ a b hab)⟩

open Classical in
theorem IsOrientable.of_faces_eq_union {n : ℕ} {R A B : Geometry.SimplicialComplex ℝ E}
    [Finite R.faces] [Finite A.faces] [Finite B.faces]
    (hR : IsCombinatorialManifoldWithBoundary n R) (hA : IsCombinatorialManifoldWithBoundary n A)
    (hB : IsCombinatorialManifoldWithBoundary n B) (hfaces : R.faces = A.faces ∪ B.faces)
    (hconn : IsPreconnected (A.space ∩ B.space)) (hAo : IsOrientable n A)
    (hBo : IsOrientable n B) : IsOrientable n R := by
  have hAR : A.faces ⊆ R.faces := by
    rw [hfaces]
    exact subset_union_left
  have hBR : B.faces ⊆ R.faces := by
    rw [hfaces]
    exact subset_union_right
  let o : ∀ s ∈ R.faces, CoherentOrientation n (faceStarComplex R s) := fun s hs =>
    Classical.choice (isOrientable_faceStarComplex hR hs)
  exact (orientationCocycle_isCoboundary_iff hR o).mp
    (isCoboundary_of_barycentricSubdivision_union (orientationCocycle hR o) hAR hBR
      hfaces.subset hconn (isCoboundary_ofLe_orientationCocycle hAR hR hA o hAo)
      (isCoboundary_ofLe_orientationCocycle hBR hR hB o hBo))

open Classical in
theorem IsOrientable.of_space_eq_union {n : ℕ} {R K L : Geometry.SimplicialComplex ℝ E}
    [Finite R.faces] [Finite K.faces] [Finite L.faces]
    (hR : IsCombinatorialManifoldWithBoundary n R) (hK : IsCombinatorialManifoldWithBoundary n K)
    (hL : IsCombinatorialManifoldWithBoundary n L) (hRspace : R.space = K.space ∪ L.space)
    (hconn : IsPreconnected (K.space ∩ L.space)) (hKo : IsOrientable n K)
    (hLo : IsOrientable n L) : IsOrientable n R := by
  obtain ⟨T, hTfin, -, hTK, hTL⟩ := exists_simplicialComplex_space_union K L
  let _ : Finite T.faces := hTfin.to_subtype
  let A := restrict T K.space
  let B := restrict T L.space
  let _ : Finite A.faces := (restrict_faces_finite T K.space).to_subtype
  let _ : Finite B.faces := (restrict_faces_finite T L.space).to_subtype
  have hc : ∀ s ∈ A.faces, ∀ t ∈ B.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E)) :=
    fun s hs t ht => T.inter_subset_convexHull hs.1 ht.1
  let U := unionComplex A B hc
  have hid : IsPLHomeomorphOn (id : E → E) R.space U.space := by
    rw [show U.space = R.space by rw [unionComplex_space, hTK.space_eq, hTL.space_eq, hRspace]]
    exact (isPolyhedron_space R).isPLHomeomorphOn_id
  have hU : IsCombinatorialManifoldWithBoundary n U := hR.of_isPLHomeomorphOn hid
  refine (isOrientable_iff_of_isPLHomeomorphOn hR hid).mpr ?_
  exact IsOrientable.of_faces_eq_union hU (hK.of_isSubdivision hTK) (hL.of_isSubdivision hTL) rfl
    (by rw [hTK.space_eq, hTL.space_eq]; exact hconn) (hKo.subdivision hK hTK)
    (hLo.subdivision hL hTL)

open Classical in
theorem IsOrientable.of_space_eq_union_union {n : ℕ}
    {R K L₀ L₁ : Geometry.SimplicialComplex ℝ E}
    [Finite R.faces] [Finite K.faces] [Finite L₀.faces] [Finite L₁.faces]
    (hR : IsCombinatorialManifoldWithBoundary n R) (hK : IsCombinatorialManifoldWithBoundary n K)
    (hL₀ : IsCombinatorialManifoldWithBoundary n L₀)
    (hL₁ : IsCombinatorialManifoldWithBoundary n L₁)
    (hRspace : R.space = K.space ∪ L₀.space ∪ L₁.space) (hL : Disjoint L₀.space L₁.space)
    (hconn₀ : IsPreconnected (K.space ∩ L₀.space))
    (hconn₁ : IsPreconnected (K.space ∩ L₁.space)) (hKo : IsOrientable n K)
    (hL₀o : IsOrientable n L₀) (hL₁o : IsOrientable n L₁) : IsOrientable n R := by
  obtain ⟨T, hTfin, -, hTK, hTL₀, hTL₁⟩ := exists_simplicialComplex_space_union_three K L₀ L₁
  let _ : Finite T.faces := hTfin.to_subtype
  let A := restrict T K.space
  let B₀ := restrict T L₀.space
  let B₁ := restrict T L₁.space
  let _ : Finite A.faces := (restrict_faces_finite T K.space).to_subtype
  let _ : Finite B₀.faces := (restrict_faces_finite T L₀.space).to_subtype
  let _ : Finite B₁.faces := (restrict_faces_finite T L₁.space).to_subtype
  have hc₀ : ∀ s ∈ A.faces, ∀ t ∈ B₀.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E)) :=
    fun s hs t ht => T.inter_subset_convexHull hs.1 ht.1
  let V := unionComplex A B₀ hc₀
  have hc₁ : ∀ s ∈ V.faces, ∀ t ∈ B₁.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E)) := by
    rintro s (hs | hs) t ht
    · exact T.inter_subset_convexHull hs.1 ht.1
    · exact T.inter_subset_convexHull hs.1 ht.1
  let U := unionComplex V B₁ hc₁
  have hVsp : V.space = K.space ∪ L₀.space := by
    rw [unionComplex_space, hTK.space_eq, hTL₀.space_eq]
  have hid : IsPLHomeomorphOn (id : E → E) R.space U.space := by
    rw [show U.space = R.space by rw [unionComplex_space, hVsp, hTL₁.space_eq, hRspace]]
    exact (isPolyhedron_space R).isPLHomeomorphOn_id
  have hU : IsCombinatorialManifoldWithBoundary n U := hR.of_isPLHomeomorphOn hid
  have hVU : V.faces ⊆ U.faces := fun _ h => Or.inl h
  have hB₁U : B₁.faces ⊆ U.faces := fun _ h => Or.inr h
  have hAU : A.faces ⊆ U.faces := fun _ h => Or.inl (Or.inl h)
  have hB₀U : B₀.faces ⊆ U.faces := fun _ h => Or.inl (Or.inr h)
  let o : ∀ s ∈ U.faces, CoherentOrientation n (faceStarComplex U s) := fun s hs =>
    Classical.choice (isOrientable_faceStarComplex hU hs)
  let ε := orientationCocycle hU o
  have hεV : (ε.ofLe (barycentricSubdivision_faces_subset hVU)).IsCoboundary :=
    isCoboundary_of_barycentricSubdivision_union
      (ε.ofLe (barycentricSubdivision_faces_subset hVU)) (fun _ h => Or.inl h)
      (fun _ h => Or.inr h) subset_rfl (by rw [hTK.space_eq, hTL₀.space_eq]; exact hconn₀)
      (isCoboundary_ofLe_orientationCocycle hAU hU (hK.of_isSubdivision hTK) o
        (hKo.subdivision hK hTK))
      (isCoboundary_ofLe_orientationCocycle hB₀U hU (hL₀.of_isSubdivision hTL₀) o
        (hL₀o.subdivision hL₀ hTL₀))
  refine (isOrientable_iff_of_isPLHomeomorphOn hR hid).mpr
    ((orientationCocycle_isCoboundary_iff hU o).mp ?_)
  refine isCoboundary_of_barycentricSubdivision_union ε hVU hB₁U subset_rfl ?_ hεV
    (isCoboundary_ofLe_orientationCocycle hB₁U hU (hL₁.of_isSubdivision hTL₁) o
      (hL₁o.subdivision hL₁ hTL₁))
  rw [hVsp, hTL₁.space_eq, union_inter_distrib_right, hL.inter_eq, union_empty]
  exact hconn₁

end Gluing

section Parity

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
private theorem exists_closed_cap_of_isPLSphere_one
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hconn : IsConnected K.space)
    {J : Set E} (hJ : IsPLSphere 1 J) (hbd : (boundaryComplex 2 K).space = J) :
    ∃ (P : Geometry.SimplicialComplex ℝ (E × ℝ)) (hPfin : P.faces.Finite)
      (D : Set (E × ℝ)) (r : (Fin 3 → ℝ) → E × ℝ),
      letI := hPfin.to_subtype
      IsCombinatorialManifold 2 P ∧ IsConnected P.space ∧ eulerChar P = eulerChar K + 1 ∧
      (IsOrientable 2 K → IsOrientable 2 P) ∧ IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧
      r '' stdSimplexBoundary 2 = J ×ˢ {0} ∧ K.space ×ˢ {0} ∩ D = J ×ˢ {0} ∧
      P.space = K.space ×ˢ {0} ∪ D := by
  classical
  have hKpoly := isPolyhedron_space K
  obtain ⟨K', hK'fin, hK'space⟩ :=
    (isPolyhedron_prod_singleton hKpoly (0 : ℝ)).exists_simplicialComplex
  let _ : Finite K'.faces := hK'fin.to_subtype
  have hι : IsPLHomeomorphOn (fun x : E => (x, (0 : ℝ))) K.space K'.space := by
    rw [hK'space]
    exact hKpoly.isPLHomeomorphOn_prod_const 0
  have hK' : IsCombinatorialManifoldWithBoundary 2 K' := hK.of_isPLHomeomorphOn hι
  have hK'c : IsConnected K'.space := by
    rw [hK'space, prod_singleton]
    exact hconn.image _ (continuous_id.prodMk continuous_const).continuousOn
  have hK'χ : eulerChar K' = eulerChar K := (eulerChar_eq_of_isPLHomeomorphOn K K' hι).symm
  have hJK : J ⊆ K.space := hbd ▸ boundaryComplex_space_subset 2 K
  have hK'bd : (boundaryComplex 2 K').space = J ×ˢ {0} := by
    have h := boundaryComplex_space_of_isPLHomeomorphOn (n := 1) K K' hK hι
    rw [prod_singleton, ← hbd]
    convert h
  obtain ⟨D, r, hr, hrb, hD⟩ := exists_cone_disk_of_isPLSphere_one hJ
  have hmeet : K'.space ∩ D = r '' stdSimplexBoundary 2 := by
    apply Subset.antisymm
    · rintro y ⟨hyK, hyD⟩
      rw [hrb]
      rw [hK'space] at hyK
      exact (hD y hyD).2 hyK.2
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨?_, hr.bijOn.mapsTo hx.1⟩
      have hmem : r x ∈ J ×ˢ ({0} : Set ℝ) := hrb ▸ mem_image_of_mem r hx
      rw [hK'space]
      exact ⟨hJK hmem.1, hmem.2⟩
  have hboundary : (boundaryComplex 2 K').space = r '' stdSimplexBoundary 2 := by
    rw [hK'bd, hrb]
  obtain ⟨P, hPfin, hP, hPc, hPχ, hPspace⟩ :=
    hK'.exists_closed_of_disk K' hK'c hr hmeet (by convert hboundary)
  let _ : Finite P.faces := hPfin.to_subtype
  refine ⟨P, hPfin, D, r, hP, hPc, by rw [hPχ, hK'χ], fun hor => ?_, hr, hrb,
    by rw [← hK'space, hmeet, hrb], by rw [hPspace, hK'space]⟩
  have hDball : IsPLBall 2 D := ⟨r, hr⟩
  obtain ⟨C, hCfin, hCspace⟩ := hDball.isPolyhedron.exists_simplicialComplex
  let _ : Finite C.faces := hCfin.to_subtype
  have hCball : IsPLBall 2 C.space := hCspace.symm ▸ hDball
  exact IsOrientable.of_space_eq_union hP.isCombinatorialManifoldWithBoundary hK'
    hCball.isCombinatorialManifoldWithBoundary (by rw [hPspace, hCspace])
    (by
      rw [hCspace, hmeet]
      exact hr.isPLSphere_image_stdSimplexBoundary.isConnected.isPreconnected)
    ((isOrientable_iff_of_isPLHomeomorphOn hK hι).mp hor) (isOrientable_of_isPLBall hCball)

open Classical in
private theorem exists_closed_cap_pair
    (R : Geometry.SimplicialComplex ℝ E) [Finite R.faces]
    (hR : IsCombinatorialManifoldWithBoundary 2 R) (hRc : IsConnected R.space)
    {C₀ C₁ : Set E} (hC₀ : IsPLSphere 1 C₀) (hC₁ : IsPLSphere 1 C₁) (hdis : Disjoint C₀ C₁)
    (hbd : (boundaryComplex 2 R).space = C₀ ∪ C₁) :
    ∃ (P : Geometry.SimplicialComplex ℝ (E × ℝ)) (hPfin : P.faces.Finite),
      letI := hPfin.to_subtype
      IsCombinatorialManifold 2 P ∧ IsConnected P.space ∧ eulerChar P = eulerChar R + 2 ∧
        (IsOrientable 2 R → IsOrientable 2 P) := by
  classical
  have hRpoly := isPolyhedron_space R
  obtain ⟨R', hR'fin, hR'space⟩ :=
    (isPolyhedron_prod_singleton hRpoly (0 : ℝ)).exists_simplicialComplex
  let _ : Finite R'.faces := hR'fin.to_subtype
  have hι : IsPLHomeomorphOn (fun x : E => (x, (0 : ℝ))) R.space R'.space := by
    rw [hR'space]
    exact hRpoly.isPLHomeomorphOn_prod_const 0
  have hR' : IsCombinatorialManifoldWithBoundary 2 R' := hR.of_isPLHomeomorphOn hι
  have hR'c : IsConnected R'.space := by
    rw [hR'space, prod_singleton]
    exact hRc.image _ (continuous_id.prodMk continuous_const).continuousOn
  have hR'χ : eulerChar R' = eulerChar R := (eulerChar_eq_of_isPLHomeomorphOn R R' hι).symm
  have hR'bd : (boundaryComplex 2 R').space = C₀ ×ˢ {0} ∪ C₁ ×ˢ {0} := by
    have h := boundaryComplex_space_of_isPLHomeomorphOn (n := 1) R R' hR hι
    rw [prod_singleton, prod_singleton, ← image_union, ← hbd]
    convert h
  have hCR : C₀ ∪ C₁ ⊆ R.space := hbd ▸ boundaryComplex_space_subset 2 R
  have hR'0 : ∀ y ∈ R'.space, y.2 = 0 := by
    rw [hR'space]
    rintro y ⟨-, hy⟩
    exact hy
  obtain ⟨D₀, r₀, hr₀, hr₀b, hD₀⟩ := exists_cone_disk_of_isPLSphere_one hC₀
  obtain ⟨D₁', r₁', hr₁', hr₁'b, hD₁'⟩ := exists_cone_disk_of_isPLSphere_one hC₁
  let σ : E × ℝ →ᵃ[ℝ] E × ℝ :=
    ((LinearMap.id : E →ₗ[ℝ] E).prodMap (-LinearMap.id : ℝ →ₗ[ℝ] ℝ)).toAffineMap
  have hσ (y : E × ℝ) : σ y = (y.1, -y.2) := rfl
  have hσinj : Function.Injective σ := by
    intro a b hab
    rw [hσ, hσ, Prod.mk.injEq, neg_inj] at hab
    exact Prod.ext hab.1 hab.2
  have hD₁'poly : IsPolyhedron D₁' := IsPLBall.isPolyhedron ⟨r₁', hr₁'⟩
  have hσD : IsPLHomeomorphOn σ D₁' (σ '' D₁') :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hD₁'poly
      ((isPiecewiseAffineOn_of_affine σ isOpen_univ).mono_of_isPolyhedron hD₁'poly
        (subset_univ _)) hσinj.injOn.bijOn_image
  have hr₁ : IsPLHomeomorphOn (σ ∘ r₁') (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (σ '' D₁') := hr₁'.trans hσD
  have hr₁b : (σ ∘ r₁') '' stdSimplexBoundary 2 = C₁ ×ˢ {0} := by
    rw [image_comp, hr₁'b]
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      rw [hσ]
      exact ⟨hz.1, by rw [mem_singleton_iff.mp hz.2, neg_zero]; rfl⟩
    · intro y hy
      refine ⟨y, hy, ?_⟩
      rw [hσ]
      exact Prod.ext rfl (by rw [mem_singleton_iff.mp hy.2, neg_zero])
  have hD₁ : ∀ y ∈ σ '' D₁', y.2 ≤ 0 ∧ (y.2 = 0 → y ∈ C₁ ×ˢ ({0} : Set ℝ)) := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨h1, h2⟩ := hD₁' z hz
    rw [hσ]
    refine ⟨neg_nonpos.mpr h1, fun h => ?_⟩
    have hz0 : z.2 = 0 := neg_eq_zero.mp h
    exact ⟨(h2 hz0).1, by rw [hz0, neg_zero]; rfl⟩
  have hdisD : Disjoint D₀ (σ '' D₁') := by
    rw [disjoint_left]
    intro y hy0 hy1
    obtain ⟨a0, b0⟩ := hD₀ y hy0
    obtain ⟨a1, b1⟩ := hD₁ y hy1
    have hy2 : y.2 = 0 := le_antisymm a1 a0
    exact disjoint_left.mp hdis (b0 hy2).1 (b1 hy2).1
  have hmeet₀ : R'.space ∩ D₀ = r₀ '' stdSimplexBoundary 2 := by
    apply Subset.antisymm
    · rintro y ⟨hyR, hyD⟩
      rw [hr₀b]
      exact (hD₀ y hyD).2 (hR'0 y hyR)
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨?_, hr₀.bijOn.mapsTo hx.1⟩
      have hmem : r₀ x ∈ C₀ ×ˢ ({0} : Set ℝ) := hr₀b ▸ mem_image_of_mem r₀ hx
      rw [hR'space]
      exact ⟨hCR (Or.inl hmem.1), hmem.2⟩
  have hmeet₁ : R'.space ∩ σ '' D₁' = (σ ∘ r₁') '' stdSimplexBoundary 2 := by
    apply Subset.antisymm
    · rintro y ⟨hyR, hyD⟩
      rw [hr₁b]
      exact (hD₁ y hyD).2 (hR'0 y hyR)
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨?_, hr₁.bijOn.mapsTo hx.1⟩
      have hmem : (σ ∘ r₁') x ∈ C₁ ×ˢ ({0} : Set ℝ) := hr₁b ▸ mem_image_of_mem _ hx
      rw [hR'space]
      exact ⟨hCR (Or.inr hmem.1), hmem.2⟩
  have hboundary : (boundaryComplex 2 R').space =
      r₀ '' stdSimplexBoundary 2 ∪ (σ ∘ r₁') '' stdSimplexBoundary 2 := by
    rw [hR'bd, hr₀b, hr₁b]
  obtain ⟨P, hPfin, hP, hPc, hPχ, hPspace⟩ :=
    hR'.exists_closed_of_disk_pair R' hR'c hr₀ hr₁ hdisD hmeet₀ hmeet₁ (by convert hboundary)
  let _ : Finite P.faces := hPfin.to_subtype
  refine ⟨P, hPfin, hP, hPc, by rw [hPχ, hR'χ], fun hor => ?_⟩
  have hB₀ : IsPLBall 2 D₀ := ⟨r₀, hr₀⟩
  have hB₁ : IsPLBall 2 (σ '' D₁') := ⟨σ ∘ r₁', hr₁⟩
  obtain ⟨A₀, hA₀fin, hA₀space⟩ := hB₀.isPolyhedron.exists_simplicialComplex
  obtain ⟨A₁, hA₁fin, hA₁space⟩ := hB₁.isPolyhedron.exists_simplicialComplex
  let _ : Finite A₀.faces := hA₀fin.to_subtype
  let _ : Finite A₁.faces := hA₁fin.to_subtype
  have hA₀ : IsPLBall 2 A₀.space := hA₀space.symm ▸ hB₀
  have hA₁ : IsPLBall 2 A₁.space := hA₁space.symm ▸ hB₁
  exact IsOrientable.of_space_eq_union_union hP.isCombinatorialManifoldWithBoundary hR'
    hA₀.isCombinatorialManifoldWithBoundary hA₁.isCombinatorialManifoldWithBoundary
    (by rw [hPspace, hA₀space, hA₁space]) (by rw [hA₀space, hA₁space]; exact hdisD)
    (by
      rw [hA₀space, hmeet₀]
      exact hr₀.isPLSphere_image_stdSimplexBoundary.isConnected.isPreconnected)
    (by
      rw [hA₁space, hmeet₁]
      exact hr₁.isPLSphere_image_stdSimplexBoundary.isConnected.isPreconnected)
    ((isOrientable_iff_of_isPLHomeomorphOn hR hι).mp hor) (isOrientable_of_isPLBall hA₀)
    (isOrientable_of_isPLBall hA₁)

open Classical in
private theorem even_eulerChar_of_add_eq_two (m : ℕ) : ∀ {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] (K : Geometry.SimplicialComplex ℝ F)
    [Finite K.faces], IsCombinatorialManifold 2 K → IsConnected K.space → IsOrientable 2 K →
      eulerChar K + m = 2 → Even (eulerChar K) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro F _ _ _ K _ hK hconn hor hm
  by_cases h2 : eulerChar K = 2
  · rw [h2]
    exact even_two
  obtain ⟨J, hJ, hJK, hnonsep⟩ := hK.exists_isPLSphere_one_isPreconnected_sdiff K hconn h2
  obtain ⟨R, hRfin, hR, hRo, hRc, hRχ, _, _, -, -, -, -, -, -, -, -, hRbd, -, -, hJ₀, hJ₁,
      hdis⟩ := hK.exists_connected_annulus_complement K hor hJ hJK hnonsep Filter.univ_mem
  let _ : Finite R.faces := hRfin.to_subtype
  obtain ⟨P, hPfin, hP, hPc, hPχ, hPo⟩ := exists_closed_cap_pair R hR hRc hJ₀ hJ₁ hdis (by
    rw [hRbd, ← singleton_union, prod_union, image_union])
  let _ : Finite P.faces := hPfin.to_subtype
  have hle : eulerChar P ≤ 2 := hP.faceEulerChar_le_two P hPc
  obtain ⟨k, hk⟩ := ih (m - 2) (by omega) P hP hPc (hPo hRo) (by omega)
  exact ⟨k - 1, by omega⟩

theorem IsCombinatorialManifold.even_eulerChar_of_isOrientable
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 2 K)
    (hconn : IsConnected K.space) (hor : IsOrientable 2 K) : Even (eulerChar K) := by
  have hle : eulerChar K ≤ 2 := hK.faceEulerChar_le_two K hconn
  have hcast := Int.toNat_of_nonneg (by omega : 0 ≤ 2 - eulerChar K)
  exact even_eulerChar_of_add_eq_two (2 - eulerChar K).toNat K hK hconn hor (by omega)

open Classical in
theorem IsCombinatorialManifoldWithBoundary.odd_eulerChar_of_isOrientable
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hconn : IsConnected K.space)
    (hor : IsOrientable 2 K) {J : Set E} (hJ : IsPLSphere 1 J)
    (hbd : (boundaryComplex 2 K).space = J) : Odd (eulerChar K) := by
  obtain ⟨P, hPfin, _, _, hP, hPc, hPχ, hPo, -⟩ :=
    exists_closed_cap_of_isPLSphere_one K hK hconn hJ hbd
  let _ : Finite P.faces := hPfin.to_subtype
  obtain ⟨k, hk⟩ := hP.even_eulerChar_of_isOrientable P hPc (hPo hor)
  exact ⟨k - 1, by omega⟩

open Classical in
theorem IsCombinatorialManifoldWithBoundary.eulerChar_le_one_of_isPLSphere_one
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hconn : IsConnected K.space)
    {J : Set E} (hJ : IsPLSphere 1 J) (hbd : (boundaryComplex 2 K).space = J) :
    eulerChar K ≤ 1 := by
  obtain ⟨P, hPfin, _, _, hP, hPc, hPχ, -⟩ :=
    exists_closed_cap_of_isPLSphere_one K hK hconn hJ hbd
  let _ : Finite P.faces := hPfin.to_subtype
  have hle : eulerChar P ≤ 2 := hP.faceEulerChar_le_two P hPc
  omega

open Classical in
theorem IsCombinatorialManifoldWithBoundary.eulerChar_nonpos_of_boundary_eq_union
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hconn : IsConnected K.space)
    {C₀ C₁ : Set E} (hC₀ : IsPLSphere 1 C₀) (hC₁ : IsPLSphere 1 C₁) (hdis : Disjoint C₀ C₁)
    (hbd : (boundaryComplex 2 K).space = C₀ ∪ C₁) : eulerChar K ≤ 0 := by
  obtain ⟨P, hPfin, hP, hPc, hPχ, -⟩ := exists_closed_cap_pair K hK hconn hC₀ hC₁ hdis hbd
  let _ : Finite P.faces := hPfin.to_subtype
  have hle : eulerChar P ≤ 2 := hP.faceEulerChar_le_two P hPc
  omega

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isPLHomeomorphOn_of_eulerChar_eq_one
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hconn : IsConnected K.space)
    {J : Set E} (hJ : IsPLSphere 1 J) (hbd : (boundaryComplex 2 K).space = J)
    (hχ : eulerChar K = 1) :
    ∃ r : (Fin 3 → ℝ) → E, IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) K.space ∧
      r '' stdSimplexBoundary 2 = J := by
  obtain ⟨P, hPfin, D, r, hP, hPc, hPχ, -, hr, hrb, hmeet, hPspace⟩ :=
    exists_closed_cap_of_isPLSphere_one K hK hconn hJ hbd
  let _ : Finite P.faces := hPfin.to_subtype
  have hJK : J ⊆ K.space := hbd ▸ boundaryComplex_space_subset 2 K
  have hS : IsPLSphere 2 P.space := hP.isPLSphere_two_of_faceEulerChar_eq_two P hPc (by
    change eulerChar P = 2
    rw [hPχ, hχ]
    norm_num)
  have hDball : IsPLBall 2 D := ⟨r, hr⟩
  have hDS : D ⊆ P.space := by
    rw [hPspace]
    exact subset_union_right
  have hcl : closure (P.space \ D) = K.space ×ˢ {0} := by
    rw [hS.closure_sdiff_eq_sdiff_image_stdSimplexBoundary hr hDS, hrb, hPspace]
    ext x
    constructor
    · rintro ⟨hx | hx, hxn⟩
      · exact hx
      · have hxJ : x ∈ J ×ˢ ({0} : Set ℝ) := not_not.mp fun h => hxn ⟨hx, h⟩
        exact ⟨hJK hxJ.1, hxJ.2⟩
    · intro hx
      exact ⟨Or.inl hx, fun h => h.2 (hmeet ▸ ⟨hx, h.1⟩)⟩
  obtain ⟨q, hq⟩ := hS.isPLBall_closure_sdiff hDball hDS
  have hqb := hS.image_stdSimplexBoundary_complement hDball hDS hq
  rw [hcl, hmeet] at hqb
  rw [hcl] at hq
  have hfst := (isPolyhedron_space K).isPLHomeomorphOn_fst_prod_const (0 : ℝ)
  refine ⟨Prod.fst ∘ q, hq.trans hfst, ?_⟩
  rw [image_comp, hqb, fst_image_prod _ (singleton_nonempty 0)]

end Parity

end DifferentialGeometry.Topology.PiecewiseLinear
