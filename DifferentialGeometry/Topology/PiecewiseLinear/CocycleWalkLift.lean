/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CocycleMonodromy
import DifferentialGeometry.Topology.PiecewiseLinear.CoveringOrientation

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Set SimpleGraph
open scoped unitInterval

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Geometry.SimplicialComplex ℝ E}

theorem totalSpace_eq_mk {ι B F : Type*} [TopologicalSpace B] [TopologicalSpace F]
    {Z : FiberBundleCore ι B F} {z : Z.TotalSpace} {x : B} {c : F}
    (h1 : z.1 = x) (h2 : z.2 = c) : z = ⟨x, c⟩ := by
  cases z
  cases h1
  cases h2
  rfl

open Classical in
def vertexPoint (K : Geometry.SimplicialComplex ℝ E) (a : K.vertices) : K.space :=
  ⟨(a : E), K.subset_space (show ({(a : E)} : Finset E) ∈ K.faces from a.2) (by simp)⟩

open Classical in
noncomputable def edgePath {a b : K.vertices}
    (hab : (SimplicialComplex.edgeGraph K).Adj a b) :
    Path (vertexPoint K a) (vertexPoint K b) :=
  (segmentPath
      (⟨(a : E), subset_convexHull ℝ _ (by simp)⟩ :
        convexHull ℝ ((({(a : E), (b : E)} : Finset E) : Set E)))
      ⟨(b : E), subset_convexHull ℝ _ (by simp)⟩
      ((convex_convexHull ℝ _).segment_subset
        (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)))).map
    (faceInclusion K ((SimplicialComplex.edgeGraph_adj K a b).mp hab).2).continuous

open Classical in
noncomputable def walkPath {u w : K.vertices} :
    (SimplicialComplex.edgeGraph K).Walk u w → Path (vertexPoint K u) (vertexPoint K w)
  | .nil => Path.refl _
  | .cons h p => (edgePath h).trans (walkPath p)

open Classical in
theorem walkPath_nil {u : K.vertices} :
    walkPath (Walk.nil : (SimplicialComplex.edgeGraph K).Walk u u) =
      Path.refl (vertexPoint K u) := rfl

open Classical in
theorem walkPath_cons {u v w : K.vertices} (h : (SimplicialComplex.edgeGraph K).Adj u v)
    (p : (SimplicialComplex.edgeGraph K).Walk v w) :
    walkPath (Walk.cons h p) = (edgePath h).trans (walkPath p) := rfl

namespace SimplicialBoolCocycle

variable (ε : SimplicialBoolCocycle K)

theorem zmod2Bool_add (x y : ZMod 2) :
    zmod2Bool (x + y) = Bool.xor (zmod2Bool x) (zmod2Bool y) := by
  revert x y
  decide

theorem zmod2Bool_boolZMod2 (b : Bool) : zmod2Bool (boolZMod2 b) = b := by
  cases b <;> decide

def walkParity {u w : K.vertices} (p : (SimplicialComplex.edgeGraph K).Walk u w) : Bool :=
  zmod2Bool (ε.walkMonodromy p)

theorem boolZMod2_walkParity {u w : K.vertices}
    (p : (SimplicialComplex.edgeGraph K).Walk u w) :
    boolZMod2 (ε.walkParity p) = ε.walkMonodromy p := boolZMod2_zmod2Bool _

theorem walkParity_nil {u : K.vertices} :
    ε.walkParity (Walk.nil : (SimplicialComplex.edgeGraph K).Walk u u) = false := rfl

theorem walkParity_cons {u v w : K.vertices} (h : (SimplicialComplex.edgeGraph K).Adj u v)
    (p : (SimplicialComplex.edgeGraph K).Walk v w) :
    ε.walkParity (Walk.cons h p) =
      Bool.xor (ε.parity (u : E) (v : E)) (ε.walkParity p) := by
  rw [walkParity, ε.walkMonodromy_cons, zmod2Bool_add, zmod2Bool_boolZMod2, walkParity]

variable [FiniteDimensional ℝ E] [Finite K.faces]

open Classical in
theorem exists_edgeLift {a b : K.vertices}
    (hab : (SimplicialComplex.edgeGraph K).Adj a b) (s : Bool) :
    ∃ Γ : Path (⟨vertexPoint K a, s⟩ :
        ε.toBoolCocycle.toFiberBundleCore.TotalSpace)
      ⟨vertexPoint K b, Bool.xor s (ε.parity (a : E) (b : E))⟩,
      ∀ t, ε.toBoolCocycle.toFiberBundleCore.proj (Γ t) = edgePath hab t := by
  have hs : ({(a : E), (b : E)} : Finset E) ∈ K.faces :=
    ((SimplicialComplex.edgeGraph_adj K a b).mp hab).2
  let v : coveringVertex K ε.toBoolCocycle.toFiberBundleCore.proj :=
    ⟨⟨vertexPoint K a, s⟩, a.2⟩
  have hvw : {coveringVertex.base v, (b : E)} ∈ K.faces := hs
  let g := coveringEdgeLift ε.isCoveringMap v (b : E) hvw
  let xa : convexHull ℝ ((({(a : E), (b : E)} : Finset E) : Set E)) :=
    ⟨(a : E), subset_convexHull ℝ _ (by simp)⟩
  let xb : convexHull ℝ ((({(a : E), (b : E)} : Finset E) : Set E)) :=
    ⟨(b : E), subset_convexHull ℝ _ (by simp)⟩
  let seg : Path xa xb := segmentPath xa xb
    ((convex_convexHull ℝ _).segment_subset xa.2 xb.2)
  have hga : g xa = (⟨vertexPoint K a, s⟩ :
      ε.toBoolCocycle.toFiberBundleCore.TotalSpace) :=
    coveringEdgeLift_source ε.isCoveringMap v (b : E) hvw
  have hgb : g xb = (⟨vertexPoint K b, Bool.xor s (ε.parity (a : E) (b : E))⟩ :
      ε.toBoolCocycle.toFiberBundleCore.TotalSpace) := by
    have hmem : g xb = (coveringNeighbor ε.isCoveringMap v (b : E)).1 := by
      rw [coveringNeighbor, dite_eq_left hvw]
      rfl
    rw [hmem]
    refine totalSpace_eq_mk ?_ ?_
    · exact Subtype.ext (coveringNeighbor_base_of_face ε.isCoveringMap v (b : E) hvw)
    · exact ε.coveringNeighbor_side v (b : E) hvw
  refine ⟨(seg.map g.continuous).cast hga.symm hgb.symm, fun t => ?_⟩
  exact congrFun (coveringEdgeLift_projection ε.isCoveringMap v (b : E) hvw) (seg t)

open Classical in
theorem exists_walkLift {u w : K.vertices}
    (p : (SimplicialComplex.edgeGraph K).Walk u w) (s : Bool) :
    ∃ Γ : Path (⟨vertexPoint K u, s⟩ :
        ε.toBoolCocycle.toFiberBundleCore.TotalSpace)
      ⟨vertexPoint K w, Bool.xor s (ε.walkParity p)⟩,
      ∀ t, ε.toBoolCocycle.toFiberBundleCore.proj (Γ t) = walkPath p t := by
  induction p generalizing s with
  | @nil x =>
      have hpar : Bool.xor s
          (ε.walkParity (Walk.nil : (SimplicialComplex.edgeGraph K).Walk x x)) = s := by
        rw [ε.walkParity_nil, Bool.xor_false]
      exact ⟨(Path.refl _).cast rfl (congrArg (fun z : Bool =>
        (⟨vertexPoint K x, z⟩ : ε.toBoolCocycle.toFiberBundleCore.TotalSpace)) hpar),
        fun _ => rfl⟩
  | @cons a b c h q ih =>
      obtain ⟨Γ₁, hΓ₁⟩ := ε.exists_edgeLift h s
      obtain ⟨Γ₂, hΓ₂⟩ := ih (Bool.xor s (ε.parity (a : E) (b : E)))
      have hpar : Bool.xor s (ε.walkParity (Walk.cons h q)) =
          Bool.xor (Bool.xor s (ε.parity (a : E) (b : E))) (ε.walkParity q) := by
        rw [ε.walkParity_cons, ← Bool.xor_assoc]
      refine ⟨(Γ₁.trans Γ₂).cast rfl (congrArg (fun z : Bool =>
        (⟨vertexPoint K c, z⟩ : ε.toBoolCocycle.toFiberBundleCore.TotalSpace)) hpar),
        fun t => ?_⟩
      change ε.toBoolCocycle.toFiberBundleCore.proj ((Γ₁.trans Γ₂) t) =
        ((edgePath h).trans (walkPath q)) t
      simp only [Path.trans_apply]
      split_ifs
      · exact hΓ₁ _
      · exact hΓ₂ _

open Classical in
theorem walkParity_eq_false_of_homotopic_refl {u : K.vertices}
    (p : (SimplicialComplex.edgeGraph K).Walk u u)
    (hnull : (walkPath p).Homotopic (Path.refl (vertexPoint K u))) :
    ε.walkParity p = false := by
  obtain ⟨Γ, hΓ⟩ := ε.exists_walkLift p false
  have h0 : (walkPath p).toContinuousMap 0 =
      ε.toBoolCocycle.toFiberBundleCore.proj
        (⟨vertexPoint K u, false⟩ : ε.toBoolCocycle.toFiberBundleCore.TotalSpace) :=
    (walkPath p).source
  have h1 : (Path.refl (vertexPoint K u)).toContinuousMap 0 =
      ε.toBoolCocycle.toFiberBundleCore.proj
        (⟨vertexPoint K u, false⟩ : ε.toBoolCocycle.toFiberBundleCore.TotalSpace) := rfl
  have hlift : Γ.toContinuousMap =
      ε.isCoveringMap.liftPath (walkPath p).toContinuousMap
        (⟨vertexPoint K u, false⟩ : ε.toBoolCocycle.toFiberBundleCore.TotalSpace) h0 :=
    (ε.isCoveringMap.eq_liftPath_iff' h0).mpr ⟨funext fun t => hΓ t, Γ.source⟩
  have hconst : (ContinuousMap.const I
      (⟨vertexPoint K u, false⟩ : ε.toBoolCocycle.toFiberBundleCore.TotalSpace)) =
      ε.isCoveringMap.liftPath (Path.refl (vertexPoint K u)).toContinuousMap
        (⟨vertexPoint K u, false⟩ : ε.toBoolCocycle.toFiberBundleCore.TotalSpace) h1 :=
    (ε.isCoveringMap.eq_liftPath_iff' h1).mpr ⟨funext fun _ => rfl, rfl⟩
  have hsame := ε.isCoveringMap.liftPath_apply_one_eq_of_homotopicRel hnull
    (⟨vertexPoint K u, false⟩ : ε.toBoolCocycle.toFiberBundleCore.TotalSpace) h0 h1
  have hval : Γ.toContinuousMap 1 =
      (⟨vertexPoint K u, false⟩ : ε.toBoolCocycle.toFiberBundleCore.TotalSpace) := by
    rw [hlift, hsame, ← hconst]
    rfl
  have hend := Γ.target.symm.trans hval
  have hbool := Bundle.TotalSpace.mk_inj.mp hend
  rwa [Bool.false_xor] at hbool

open Classical in
theorem walkMonodromy_eq_zero_of_homotopic_refl {u : K.vertices}
    (p : (SimplicialComplex.edgeGraph K).Walk u u)
    (hnull : (walkPath p).Homotopic (Path.refl (vertexPoint K u))) :
    ε.walkMonodromy p = 0 := by
  rw [← ε.boolZMod2_walkParity p, ε.walkParity_eq_false_of_homotopic_refl p hnull]
  rfl

end SimplicialBoolCocycle

end DifferentialGeometry.Topology.PiecewiseLinear
