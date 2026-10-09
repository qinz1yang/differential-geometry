/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactGraphNeighborhoods
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactGraphRecognition
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualCutFrame
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactExteriorNeighborhoods
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactRimNeighborhoods
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFaceTorusCycle
import DifferentialGeometry.Topology.PiecewiseLinear.MarkedSolidTorusSandwich

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C V : Set (EuclideanSpace ℝ (Fin 3))}
  {h f₁ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)} {ε : ℝ}
  {K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {src srcBd : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3))}
  {H : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {env : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}

theorem exists_compactCutAndGraph (h331 : Moise331OnTube) (hC : IsPLBall 3 C) (hV : IsOpen V)
    (hCV : C ⊆ V) (hh : Topology.IsEmbedding (V.domRestrict h)) (hε : 0 < ε) :
    ∃ (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (src srcBd : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3)))
      (H : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
      (f₁ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)),
      Section34CompactCutFrame C K K' src srcBd ∧ Section34CompactCarrierControl K h ε H ∧
        Section34CompactGraphFrame V h ε K K' src H f₁ := by
  classical
  let : DecidableEq E3 := Classical.decEq E3
  have hcont : ContinuousOn h V := continuousOn_iff_continuous_domRestrict.mpr hh.continuous
  have hinj : InjOn h V := fun x hx y hy hxy =>
    congrArg Subtype.val (hh.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  obtain ⟨B, hB, hCB, hBV⟩ := hC.exists_isPLBall_subset_interior_of_isOpen hV hCV
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    ((IsPLBall.isPolyhedron hB).isCompact.uniformContinuousOn_of_continuous
      (hcont.mono hBV)) (ε / 100) (by positivity)
  have hBemb : IsEmbedding ((interior B).domRestrict h) :=
    hh.comp (IsEmbedding.inclusion (interior_subset.trans hBV))
  obtain ⟨M, hMfin, hM, hMB, hCM, hKC, hmesh, happ⟩ :=
    exists_compactGraphApproximation h331 hC isOpen_interior hCB hBemb hδ
  let _ : Finite M.faces := hMfin.to_subtype
  let K := restrict M C
  let L := restrict K (section34CompactGraphSkeleton K)
  have hKM : K.faces ⊆ M.faces := restrict_faces_subset M C
  let _ : Finite K.faces := (hMfin.subset hKM).to_subtype
  let _ : Finite (Section34CompactSimplexIndex K 3) :=
    finite_section34CompactSimplexIndex (hMfin.subset hKM) 3
  have hKspace : K.space = C := hKC
  have hK : IsCombinatorialManifoldWithBoundary 3 K :=
    (show IsPLBall 3 K.space from hKspace.symm ▸ hC).isCombinatorialManifoldWithBoundary
  have hKint : K.space ⊆ interior M.space := hKspace.symm ▸ hCM
  have hMV : M.space ⊆ V := hMB.trans (interior_subset.trans hBV)
  have hstar : ∀ v ∈ K.vertices, ∀ x ∈ closedStar M v, dist (h x) (h v) < ε / 100 := by
    intro v _ x hx
    exact dist_image_lt_of_mem_closedStar hmesh
      (fun x hx y hy hxy => hclose x (interior_subset (hMB hx))
        y (interior_subset (hMB hy)) hxy) hx
  obtain ⟨H, W₀, hH, hHC, hW₀open, hCW₀, hW₀small, hW₀H, hW₀avoid⟩ :=
    exists_compactGraphNeighborhoods M K hKM (hcont.mono hMV) (hinj.mono hMV) hε hstar
  obtain ⟨W₁, hW₁open, hCW₁, hW₁exterior⟩ :=
    exists_compactExteriorNeighborhoods M K hM hKM hKint hV hMV hcont hinj
  obtain ⟨P, hPM, -, Φ, hΦ, W₂, hW₂open, hCW₂, hW₂P⟩ :=
    exists_compactRimNeighborhoods M K hM hKM hKint hV hMV hcont hinj
  let W (v : E3) := W₀ v ∩ W₁ v ∩ W₂ v
  have hCW (v : E3) (hv : v ∈ K.vertices) : W v ∈ nhdsSet (h '' (graphDualCell M L v).space) :=
    ((hW₀open v).inter (hW₁open v) |>.inter (hW₂open v)).mem_nhdsSet.mpr
      (fun x hx => ⟨⟨hCW₀ v hv hx, hCW₁ v hv hx⟩, hCW₂ v hv hx⟩)
  obtain ⟨f₁, hf₁, hf₁N, hf₁W⟩ := happ W hCW
  have hf₁W₀ (v : E3) (hv : v ∈ K.vertices) :
      f₁ '' (graphDualCell M L v).space ⊆ W₀ v :=
    (hf₁W v hv).trans (inter_subset_left.trans inter_subset_left)
  have hf₁W₁ (v : E3) (hv : v ∈ K.vertices) :
      f₁ '' (graphDualCell M L v).space ⊆ W₁ v :=
    (hf₁W v hv).trans (inter_subset_left.trans inter_subset_right)
  have hf₁W₂ (v : E3) (hv : v ∈ K.vertices) :
      f₁ '' (graphDualCell M L v).space ⊆ W₂ v :=
    (hf₁W v hv).trans inter_subset_right
  have havoid : ∀ v ∈ K.vertices, ∀ t ∈ K.faces, v ∉ t →
      Disjoint (f₁ '' (graphDualCell M L v).space) (h '' convexHull ℝ (t : Set E3)) :=
    fun v hv t ht hvt => (hW₀avoid v t ht hvt).mono_left (hf₁W₀ v hv)
  obtain ⟨hvertex, hsplit, hincident, hrim⟩ :=
    section34CompactGraphRecognition M K hKM
      hf₁.2.1.continuousOn hf₁N havoid
  have hcut := section34CompactCutFrame_compactDual M K hKM hM hK hKint
  have hN : compactDualNeighborhood M K =
      section34CompactCutNeighborhood (compactDualCutCell M K hKM) :=
    compactDualNeighborhood_eq_cutNeighborhood M K hKM
  refine ⟨K, K, compactDualCutCell M K hKM, compactDualCutBoundary M K hKM, H, f₁,
    hKspace ▸ hcut, hH, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, hvertex, hsplit, hincident, hrim, ?_, ?_, hW₁exterior f₁ hf₁W₁⟩
  · rw [← hN]
    refine iUnion₂_subset fun v _ => ?_
    exact ((graphDualCell_space_subset M L v).trans
      (derivedNeighborhood_space_subset M L)).trans hMV
  · rwa [← hN]
  · rwa [← hN]
  · rw [← hN]
    intro x hx
    obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
    have h1 := Metric.mem_ball.mp (hW₀small v (hf₁W₀ v hv (mem_image_of_mem f₁ hxv)))
    have h2 := hstar v hv x ((closedStar_subset_of_isSubdivision
      (barycentricSubdivision_isSubdivision M) v) (graphDualCell_space_subset_closedStar M L v hxv))
    exact (dist_triangle_right (f₁ x) (h x) (h v)).trans_lt (by linarith)
  · intro s
    have hTP : section34CompactFaceTorus
        (section34CompactVertexBallImage (compactDualCutCell M K hKM) f₁) s ⊆
          interior (h '' P s) := by
      rw [section34CompactFaceTorus_compactDual_eq M K hKM f₁ s]
      rintro y ⟨x, hx, rfl⟩
      obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
      have hvK : v ∈ K.vertices := K.down_closed s.2.1
        (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
      exact hW₂P s v hv (hf₁W₂ v hvK (mem_image_of_mem f₁ hxv))
    obtain ⟨S₁, S₂, hS₁, hS₂, hS₁T, hTS₂, hshell, hspine⟩ :=
      exists_toroidalShell_sandwich_of_marked_product_image hh
        ((hPM s).trans (interior_subset.trans hMV)) (Φ s) (hΦ s) (hrim s) hTP
    exact ⟨S₁, S₂, hS₁, hS₂,
      isCombinatorialSolidTorus_compactFaceTorus_of_cycle M K hM hKM hf₁ s,
      hS₁T, hTS₂, hshell, hspine⟩
  · intro w t ht hwt
    let v := w.1.centroid ℝ id
    have hvK : v ∈ K.vertices := centroid_mem_vertices_compactVertexIndex w
    have hvw : v ∈ w.1 := by
      rw [← singleton_centroid_eq_compactVertexIndex w]
      exact Finset.mem_singleton_self _
    have hvt : v ∈ t := mem_of_mem_convexHull_of_singleton_mem K hvK ht (hwt hvw)
    exact union_subset (hHC t ht v hvt) ((hf₁W₀ v hvK).trans (hW₀H v t ht hvt))

end DifferentialGeometry.Topology.PiecewiseLinear
