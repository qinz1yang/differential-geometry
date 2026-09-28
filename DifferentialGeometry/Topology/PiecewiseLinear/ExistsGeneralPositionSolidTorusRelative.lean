/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryFaces
import DifferentialGeometry.Topology.PiecewiseLinear.ComplexUnion
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsCombinatorialTriangulation
import DifferentialGeometry.Topology.PiecewiseLinear.NontrivialKernelInSolidTorus
import DifferentialGeometry.Topology.PiecewiseLinear.OneManifoldComponents
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonCircleParametrization
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBall
import DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.SolidTorusGeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexComplement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section General

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPolyhedron.frontier {P : Set E} (hP : IsPolyhedron P) : IsPolyhedron (frontier P) := by
  obtain ⟨T, hT, hTcard, hPT⟩ := exists_affineIndependent_openSimplex_superset
    (Module.finrank ℝ E) rfl hP.isCompact.isBounded
  have hΔ : IsPolyhedron (convexHull ℝ (T : Set E)) :=
    (isPLBall_convexHull_of_affineIndependent T hT hTcard).isPolyhedron
  have hint : interior (convexHull ℝ (T : Set E)) = openSimplex T :=
    interior_convexHull_eq_openSimplex hT hTcard
  have heq : _root_.frontier P = P ∩ closure (convexHull ℝ (T : Set E) \ P) := by
    apply Subset.antisymm
    · intro x hx
      have hxP : x ∈ P := hP.isClosed.frontier_subset hx
      have hxc : x ∈ closure Pᶜ := by
        rw [frontier_eq_closure_inter_closure] at hx
        exact hx.2
      refine ⟨hxP, mem_closure_iff.mpr fun O hO hxO => ?_⟩
      obtain ⟨y, ⟨hyO, hyint⟩, hyP⟩ := mem_closure_iff.mp hxc
        (O ∩ interior (convexHull ℝ (T : Set E))) (hO.inter isOpen_interior)
        ⟨hxO, by rw [hint]; exact hPT hxP⟩
      exact ⟨y, hyO, interior_subset hyint, hyP⟩
    · rintro x ⟨hxP, hxc⟩
      rw [frontier_eq_closure_inter_closure]
      exact ⟨subset_closure hxP, closure_mono (fun y hy => hy.2) hxc⟩
  rw [heq]
  exact hP.inter (hΔ.closure_sdiff hP)

theorem IsCombinatorialSolidTorus.isPolyhedron {S : Set E} (hS : IsCombinatorialSolidTorus S) :
    IsPolyhedron S := by
  obtain ⟨-, n, -, C, hCfin, hCunion, -, -⟩ := hS
  have _ (i : Fin n) : Finite (C i).faces := (hCfin i).to_subtype
  obtain ⟨R, hRfin, hRspace, -⟩ := exists_simplicialComplex_space_iUnion C
  let _ : Finite R.faces := hRfin.to_subtype
  rw [← hCunion, ← hRspace]
  exact isPolyhedron_space R

open Classical in
theorem IsCombinatorialSolidTorus.image_homeomorph {S : Set E}
    (hS : IsCombinatorialSolidTorus S) (H : E ≃ₜ E) (hH : IsPLHomeomorphOn H univ univ) :
    IsCombinatorialSolidTorus (H '' S) := by
  obtain ⟨⟨φ⟩, n, hn, C, hCfin, hCunion, hCball, hCadj⟩ := hS
  have _ (k : Fin n) : Finite (C k).faces := (hCfin k).to_subtype
  have hball (k : Fin n) : IsPLBall 3 (H '' (C k).space) :=
    (hCball k).of_isPLHomeomorphOn (hH.restrict (hCball k).isPolyhedron (subset_univ _))
  choose C' hC'fin hC'space using fun k => (hball k).isPolyhedron.exists_simplicialComplex
  have _ (k : Fin n) : Finite (C' k).faces := (hC'fin k).to_subtype
  have hbd (k : Fin n) :
      (boundaryComplex 3 (C' k)).space = H '' (boundaryComplex 3 (C k)).space := by
    have hf : IsPLHomeomorphOn H (C k).space (C' k).space := by
      rw [hC'space k]
      exact hH.restrict (hCball k).isPolyhedron (subset_univ _)
    exact boundaryComplex_space_of_isPLHomeomorphOn_of_isPLBall (C k) (C' k) (hCball k) hf
  refine ⟨⟨(H.image S).symm.trans φ⟩, n, hn, C', hC'fin, ?_, fun k => ?_, fun i j hij => ?_⟩
  · rw [← hCunion, image_iUnion]
    exact iUnion_congr hC'space
  · rw [hC'space k]
    exact hball k
  · have hinter : (C' i).space ∩ (C' j).space = H '' ((C i).space ∩ (C j).space) := by
      rw [hC'space, hC'space, image_inter H.injective]
    obtain ⟨hne, hadj⟩ := hCadj i j hij
    refine ⟨by rw [hinter, image_nonempty]; exact hne, fun hA => ?_⟩
    obtain ⟨hD, hDi, hDj⟩ := hadj hA
    refine ⟨?_, ?_, ?_⟩
    · rw [hinter]
      exact hD.of_isPLHomeomorphOn (hH.restrict hD.isPolyhedron (subset_univ _))
    · rw [hinter, hbd i]
      exact image_mono hDi
    · rw [hinter, hbd j]
      exact image_mono hDj

open Classical in
theorem exists_isPLSphere_cover_inter_of_transverse_faces (hdim : Module.finrank ℝ E = 3)
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifold 2 K) (hL : IsCombinatorialManifold 2 L)
    (htrans : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      (convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty →
        vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = ⊤) :
    (∀ x ∈ K.space ∩ L.space, HasPLCrossingAt K.space L.space x) ∧
      ∃ (ι : Type) (_ : Finite ι) (G : ι → Set E), (∀ i, IsPLSphere 1 (G i)) ∧
        (Pairwise fun i i' => Disjoint (G i) (G i')) ∧ K.space ∩ L.space = ⋃ i, G i := by
  have hKb := hK.isCombinatorialManifoldWithBoundary
  have hLb := hL.isCombinatorialManifoldWithBoundary
  refine ⟨fun x hx => hasPLCrossingAt_of_transverse_faces K L hKb hLb hdim htrans hx, ?_⟩
  have htrans' : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      ((fun x : E => x + 0) '' convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty →
        vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = ⊤ := by
    simpa only [add_zero, Set.image_id'] using htrans
  obtain ⟨G, hGfin, hGspace, hGfaces⟩ := exists_triangulation_inter_of_transverse_faces K L 0
    htrans'
  let _ : Finite G.faces := hGfin.to_subtype
  have hspace : G.space = K.space ∩ L.space := by
    simpa only [add_zero, Set.image_id'] using hGspace
  have hcarrier : ∀ u ∈ G.faces, ∃ v ∈ K.faces, ∃ z ∈ L.faces,
      convexHull ℝ (u : Set E) ⊆ convexHull ℝ (v : Set E) ∩ convexHull ℝ (z : Set E) := by
    intro u hu
    obtain ⟨s, hs, t, ht, hsub, _⟩ := hGfaces u hu
    exact ⟨s, hs, t, ht, by simpa only [add_zero, Set.image_id'] using hsub⟩
  have hGb : IsCombinatorialManifoldWithBoundary 1 G :=
    isCombinatorialManifoldWithBoundary_inter_of_transverse_faces K L G hKb hLb
      (m := 1) (n := 1) hdim hspace hcarrier htrans
  have hG : IsCombinatorialManifold 1 G := by
    apply (isCombinatorialManifold_one_iff G).mpr
    refine ⟨fun s hs => hGb.card_le G hs, fun x hxG => ?_⟩
    have hxspace : x ∈ G.space := G.subset_space hxG (Finset.mem_singleton_self _)
    rw [hspace] at hxspace
    obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex K hxspace.1
    obtain ⟨t, ht, hxt⟩ := exists_face_mem_openSimplex L hxspace.2
    have hst := htrans s hs t ht ⟨x, openSimplex_subset_convexHull _ hxs,
      openSimplex_subset_convexHull _ hxt⟩
    refine neighbors_eq_pair_of_transverse_face K L G hKb hLb hdim
      (fun s hs => hGb.card_le G hs) hspace hcarrier hs ht hxs hxt hxG hst ?_ ?_
    · rw [Geometry.SimplicialComplex.space, hK.boundaryComplex_faces_eq_empty]
      simp
    · rw [Geometry.SimplicialComplex.space, hL.boundaryComplex_faces_eq_empty]
      simp
  have hcomp (c : (SimplicialComplex.edgeGraph G).ConnectedComponent) :
      IsPLSphere 1 (graphComponentComplex G c).space := by
    let _ : Finite (graphComponentComplex G c).faces :=
      (graphComponentComplex_faces_finite G c).to_subtype
    apply isPLSphere_one_of_edgeGraph_connected _ ?_ (edgeGraph_graphComponentComplex_connected G c)
    apply (isCombinatorialManifold_one_iff _).mpr
    refine ⟨fun s hs => hGb.card_le G hs.1, fun x hx => ?_⟩
    let v : (graphComponentComplex G c).vertices := ⟨x, hx⟩
    let w : c.supp := (graphComponentVertexEquiv G c).symm v
    have hvw : graphComponentVertex G c w = v := (graphComponentVertexEquiv G c).apply_symm_apply v
    have hdegree := ncard_neighborSet_edgeGraph_eq_two hG w.1
    have htransfer :
        ((SimplicialComplex.edgeGraph (graphComponentComplex G c)).neighborSet v).ncard =
          ((SimplicialComplex.edgeGraph G).neighborSet w.1).ncard := by
      rw [← hvw]
      exact graphComponentEdgeGraph_neighborSet_ncard G c w
    rw [← htransfer, SimplicialComplex.ncard_neighborSet_edgeGraph] at hdegree
    exact Set.ncard_eq_two.mp hdegree
  let _ : Finite G.vertices := (SimplicialComplex.finite_vertices G).to_subtype
  refine ⟨(SimplicialComplex.edgeGraph G).ConnectedComponent, inferInstance,
    fun c => (graphComponentComplex G c).space, hcomp,
    pairwise_disjoint_graphComponentComplex_space G, ?_⟩
  rw [← hspace]
  exact space_eq_iUnion_graphComponentComplex G

end General

section Torus

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem notMem_interior_of_homeomorph_closedBall_prod_sphere {S : Set E3}
    (φ : S ≃ₜ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))
    (p : S) (hp : ‖((φ p).1 : EuclideanSpace ℝ (Fin 2))‖ = 1) : (p : E3) ∉ interior S := by
  classical
  intro hpint
  let ψ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) × ℝ :=
    fun u θ => ((2 + u 0) • θ, u 1)
  have hψcont : Continuous fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      ψ z.1 z.2 := by
    simp only [ψ]
    fun_prop
  have hψinj : ∀ u v θ θ' : EuclideanSpace ℝ (Fin 2), ‖u‖ < 2 → ‖v‖ < 2 → ‖θ‖ = 1 →
      ‖θ'‖ = 1 → ψ u θ = ψ v θ' → u = v ∧ θ = θ' := by
    intro u v θ θ' hu hv hθ hθ' heq
    have h1 : (2 + u 0) • θ = (2 + v 0) • θ' := congrArg Prod.fst heq
    have h2 : u 1 = v 1 := congrArg Prod.snd heq
    have hu0 : |u 0| < 2 := lt_of_le_of_lt (by simpa using PiLp.norm_apply_le u 0) hu
    have hv0 : |v 0| < 2 := lt_of_le_of_lt (by simpa using PiLp.norm_apply_le v 0) hv
    have hupos : 0 < 2 + u 0 := by linarith [neg_abs_le (u 0)]
    have hvpos : 0 < 2 + v 0 := by linarith [neg_abs_le (v 0)]
    have hn := congrArg norm h1
    rw [norm_smul, norm_smul, hθ, hθ', mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hupos, abs_of_pos hvpos] at hn
    have h0 : u 0 = v 0 := by linarith
    have huv : u = v := by
      ext i
      fin_cases i
      · exact h0
      · exact h2
    refine ⟨huv, ?_⟩
    rw [h0] at h1
    exact smul_right_injective _ hvpos.ne' h1
  let G : E3 → EuclideanSpace ℝ (Fin 2) × ℝ := fun x =>
    if h : x ∈ S then ψ ((φ ⟨x, h⟩).1 : EuclideanSpace ℝ (Fin 2))
      ((φ ⟨x, h⟩).2 : EuclideanSpace ℝ (Fin 2)) else 0
  have hGS : ∀ x (h : x ∈ S), G x = ψ ((φ ⟨x, h⟩).1 : EuclideanSpace ℝ (Fin 2))
      ((φ ⟨x, h⟩).2 : EuclideanSpace ℝ (Fin 2)) := fun x h => dite_eq_left h
  have hball2 : ∀ q : S, ‖((φ q).1 : EuclideanSpace ℝ (Fin 2))‖ < 2 := fun q =>
    lt_of_le_of_lt (mem_closedBall_zero_iff.mp (φ q).1.2) one_lt_two
  have hsph : ∀ q : S, ‖((φ q).2 : EuclideanSpace ℝ (Fin 2))‖ = 1 := fun q =>
    mem_sphere_zero_iff_norm.mp (φ q).2.2
  have hGcont : ContinuousOn G (interior S) := by
    apply ContinuousOn.mono _ interior_subset
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : S.domRestrict G = fun x : S => ψ ((φ x).1 : EuclideanSpace ℝ (Fin 2))
        ((φ x).2 : EuclideanSpace ℝ (Fin 2)) := by
      funext x
      exact hGS x x.2
    rw [heq]
    exact hψcont.comp ((continuous_subtype_val.comp (continuous_fst.comp φ.continuous)).prodMk
      (continuous_subtype_val.comp (continuous_snd.comp φ.continuous)))
  have hGinj : InjOn G (interior S) := by
    intro x hx y hy hxy
    have hxS := interior_subset hx
    have hyS := interior_subset hy
    rw [hGS x hxS, hGS y hyS] at hxy
    obtain ⟨h1, h2⟩ := hψinj _ _ _ _ (hball2 _) (hball2 _) (hsph _) (hsph _) hxy
    have hφ : φ ⟨x, hxS⟩ = φ ⟨y, hyS⟩ := Prod.ext (Subtype.ext h1) (Subtype.ext h2)
    exact congrArg Subtype.val (φ.injective hφ)
  have hO : IsOpen (G '' interior S) :=
    Topology.invariance_of_domain_isOpen_image_of_finrank_eq (by simp [Module.finrank_prod])
      isOpen_interior hGcont hGinj
  let w : ℝ → EuclideanSpace ℝ (Fin 2) × ℝ := fun t =>
    ψ (t • ((φ p).1 : EuclideanSpace ℝ (Fin 2))) ((φ p).2 : EuclideanSpace ℝ (Fin 2))
  have hwcont : Continuous w :=
    hψcont.comp ((continuous_id.smul continuous_const).prodMk continuous_const)
  have hw1 : w 1 ∈ G '' interior S := ⟨p, hpint, by rw [hGS p p.2]; simp [w]⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (hO.preimage hwcont) 1 hw1
  have hmin : 0 < min (δ / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
  have ht1 : 1 < 1 + min (δ / 2) (1 / 2) := by linarith
  have ht2 : 1 + min (δ / 2) (1 / 2) < 2 := by linarith [min_le_right (δ / 2) (1 / 2)]
  have htδ : dist (1 + min (δ / 2) (1 / 2)) 1 < δ := by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hmin]
    linarith [min_le_left (δ / 2) (1 / 2)]
  obtain ⟨y, hy, hyw⟩ := hball (Metric.mem_ball.mpr htδ)
  have hyS := interior_subset hy
  rw [hGS y hyS] at hyw
  have htb : ‖(1 + min (δ / 2) (1 / 2)) • ((φ p).1 : EuclideanSpace ℝ (Fin 2))‖ =
      1 + min (δ / 2) (1 / 2) := by
    rw [norm_smul, hp, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith)]
  obtain ⟨h1, -⟩ := hψinj _ _ _ _ (hball2 _) (by rw [htb]; exact ht2) (hsph _) (hsph p) hyw
  have hn := congrArg norm h1
  rw [htb] at hn
  have hle := mem_closedBall_zero_iff.mp (φ ⟨y, hyS⟩).1.2
  linarith

theorem mem_frontier_iff_norm_eq_one_of_homeomorph_closedBall_prod_sphere {S : Set E3}
    (hS : IsClosed S)
    (φ : S ≃ₜ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) (p : S) :
    (p : E3) ∈ frontier S ↔ ‖((φ p).1 : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
  rw [hS.frontier_eq]
  constructor
  · rintro ⟨-, hpint⟩
    by_contra hne
    have hlt : ‖((φ p).1 : EuclideanSpace ℝ (Fin 2))‖ < 1 :=
      lt_of_le_of_ne (mem_closedBall_zero_iff.mp (φ p).1.2) hne
    apply hpint
    have h := mem_interior_of_homeomorph_closedBall_prod_sphere φ (φ p).1 (φ p).2 hlt
    rwa [Prod.mk.eta, φ.symm_apply_apply] at h
  · intro h
    exact ⟨p.2, notMem_interior_of_homeomorph_closedBall_prod_sphere φ p h⟩

theorem IsTopologicalSolidTorus.nonempty_homeomorph_frontier {S : Set E3}
    (hS : IsTopologicalSolidTorus S) (hclosed : IsClosed S) :
    Nonempty (frontier S ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) := by
  obtain ⟨φ⟩ := hS
  have hfS : frontier S ⊆ S := hclosed.frontier_subset
  have hmem := mem_frontier_iff_norm_eq_one_of_homeomorph_closedBall_prod_sphere hclosed φ
  let f : frontier S → S := fun x => ⟨x, hfS x.2⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  let g : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → S :=
    fun z => φ.symm (⟨z.1, Metric.sphere_subset_closedBall z.1.2⟩, z.2)
  have hg : Continuous g := φ.symm.continuous.comp
    (((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd)
  have hφg : ∀ z, φ (g z) = (⟨z.1, Metric.sphere_subset_closedBall z.1.2⟩, z.2) := fun z =>
    φ.apply_symm_apply _
  have hgmem : ∀ z, ((g z : S) : E3) ∈ frontier S := fun z =>
    (hmem (g z)).mpr (by rw [hφg]; exact mem_sphere_zero_iff_norm.mp z.1.2)
  have hfmem : ∀ x : frontier S,
      ((φ (f x)).1 : EuclideanSpace ℝ (Fin 2)) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    fun x => mem_sphere_zero_iff_norm.mpr ((hmem (f x)).mp x.2)
  exact ⟨{
    toFun := fun x => (⟨(φ (f x)).1, hfmem x⟩, (φ (f x)).2)
    invFun := fun z => ⟨g z, hgmem z⟩
    left_inv := fun x => by
      apply Subtype.ext
      have hpair : ((⟨((⟨(φ (f x)).1, hfmem x⟩ :
          Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) : EuclideanSpace ℝ (Fin 2)),
          Metric.sphere_subset_closedBall (hfmem x)⟩ :
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1), (φ (f x)).2) = φ (f x) :=
        Prod.ext (Subtype.ext rfl) rfl
      change ((φ.symm _ : S) : E3) = x
      rw [hpair, φ.symm_apply_apply]
    right_inv := fun z => by
      have h := hφg z
      apply Prod.ext
      · apply Subtype.ext
        change ((φ (g z)).1 : EuclideanSpace ℝ (Fin 2)) = z.1
        rw [h]
      · change (φ (g z)).2 = z.2
        rw [h]
    continuous_toFun := by
      have h := φ.continuous.comp hf
      exact ((continuous_subtype_val.comp (continuous_fst.comp h)).subtype_mk _).prodMk
        (continuous_snd.comp h)
    continuous_invFun := (continuous_subtype_val.comp hg).subtype_mk _ }⟩

theorem IsCombinatorialSolidTorus.isPLTorus_frontier {S : Set E3}
    (hS : IsCombinatorialSolidTorus S) : IsPLTorus (frontier S) :=
  ⟨hS.isPolyhedron.frontier, hS.1.nonempty_homeomorph_frontier hS.isPolyhedron.isClosed⟩

end Torus

theorem exists_generalPosition_solidTorus_relative {A U S₀ : Set (EuclideanSpace ℝ (Fin 3))}
    {m : ℕ} (hA : IsCompact A) (hU : IsOpen U) (h₀ : Fits A U S₀)
    (F : Fin m → Set (EuclideanSpace ℝ (Fin 3))) (hF : ∀ i, IsCombinatorialSolidTorus (F i)) :
    ∃ S, Fits A U S ∧ ∀ i, PairGP S (F i) := by
  obtain ⟨hS₀, hAS₀, hS₀U⟩ := h₀
  obtain ⟨K, hKfin, hKspace⟩ := hS₀.isPLTorus_frontier.1.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  choose Lc hLcfin hLcspace using fun i => (hF i).isPLTorus_frontier.1.exists_simplicialComplex
  have _ (i : Fin m) : Finite (Lc i).faces := (hLcfin i).to_subtype
  obtain ⟨R, hRfin, -, hRsub⟩ := exists_simplicialComplex_space_iUnion Lc
  let _ : Finite R.faces := hRfin.to_subtype
  obtain ⟨ε₁, hε₁, hε₁U⟩ := hS₀.isPolyhedron.isCompact.exists_thickening_subset_open hU hS₀U
  obtain ⟨ε₂, hε₂, hε₂A⟩ := hA.exists_thickening_subset_open isOpen_interior hAS₀
  obtain ⟨a, h, -, hh, hclose, -, hKA, htrans⟩ :=
    exists_small_homeomorph_transverse_affineImage K R isOpen_univ (subset_univ _)
      (lt_min hε₁ hε₂)
  have hcont : Continuous h := continuousOn_univ.mp hh.isPiecewiseAffineOn.continuousOn
  have hcont' : Continuous (Function.invFunOn h univ) :=
    continuousOn_univ.mp hh.isPiecewiseAffineOn_invFunOn.continuousOn
  let H : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3) :=
    { toFun := h
      invFun := Function.invFunOn h univ
      left_inv := fun x => hh.bijOn.invOn_invFunOn.1 (mem_univ x)
      right_inv := fun y => hh.bijOn.invOn_invFunOn.2 (mem_univ y)
      continuous_toFun := hcont
      continuous_invFun := hcont' }
  have hS : IsCombinatorialSolidTorus (H '' S₀) := hS₀.image_homeomorph H hh
  refine ⟨H '' S₀, ⟨hS, ?_, ?_⟩, fun i => ?_⟩
  · intro y hy
    rw [← H.image_interior]
    refine ⟨H.symm y, hε₂A (Metric.mem_thickening_iff.mpr ⟨y, hy, ?_⟩), H.apply_symm_apply y⟩
    have hd := hclose (H.symm y)
    change dist (H (H.symm y)) (H.symm y) < min ε₁ ε₂ at hd
    rw [H.apply_symm_apply, dist_comm] at hd
    exact hd.trans_le (min_le_right _ _)
  · rintro _ ⟨x, hx, rfl⟩
    exact hε₁U (Metric.mem_thickening_iff.mpr ⟨x, hx, (hclose x).trans_le (min_le_left _ _)⟩)
  · let K' := affineImage K (AffineEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin 3)) a)
    let _ : Finite K'.faces := (affineImage_faces_finite K _).to_subtype
    have hK'space : K'.space = frontier (H '' S₀) := by
      rw [hKA, ← H.image_frontier, hKspace]
      rfl
    have hK' : IsCombinatorialManifold 2 K' := by
      obtain ⟨-, ⟨ψ⟩⟩ := hS.isPLTorus_frontier
      exact isCombinatorialManifold_two_of_homeomorph_sphere_prod K'
        ((Homeomorph.setCongr hK'space).trans ψ)
    let L := restrict R (Lc i).space
    let _ : Finite L.faces := (restrict_faces_finite R _).to_subtype
    have hLspace : L.space = frontier (F i) := (hRsub i).space_eq.trans (hLcspace i)
    have hL : IsCombinatorialManifold 2 L := by
      obtain ⟨-, ⟨ψ⟩⟩ := (hF i).isPLTorus_frontier
      exact isCombinatorialManifold_two_of_homeomorph_sphere_prod L
        ((Homeomorph.setCongr hLspace).trans ψ)
    have hpair := exists_isPLSphere_cover_inter_of_transverse_faces (by simp) K' L hK' hL
      (fun s hs t ht hst => htrans s hs t (restrict_faces_subset R _ ht) hst)
    rw [hK'space, hLspace] at hpair
    exact hpair

end DifferentialGeometry.Topology.PiecewiseLinear
