import DifferentialGeometry.Topology.Homology.HurewiczOneAbelianization

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module
open scoped Simplicial Topology

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem mem_stdSimplex_fin_three {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c = 1) : (![a, b, c] : Fin 3 → ℝ) ∈ stdSimplex ℝ (Fin 3) := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> assumption
  · simpa [Fin.sum_univ_three] using h

theorem unitInterval_sub_nonneg (s : unitInterval) : 0 ≤ 1 - (s : ℝ) := by linarith [s.2.2]

def simplexEdgePoint0 (s : unitInterval) : stdSimplex ℝ (Fin 3) :=
  ⟨![0, 1 - (s : ℝ), (s : ℝ)],
    mem_stdSimplex_fin_three le_rfl (unitInterval_sub_nonneg s) s.2.1 (by ring)⟩

def simplexEdgePoint1 (s : unitInterval) : stdSimplex ℝ (Fin 3) :=
  ⟨![1 - (s : ℝ), 0, (s : ℝ)],
    mem_stdSimplex_fin_three (unitInterval_sub_nonneg s) le_rfl s.2.1 (by ring)⟩

def simplexEdgePoint2 (s : unitInterval) : stdSimplex ℝ (Fin 3) :=
  ⟨![1 - (s : ℝ), (s : ℝ), 0],
    mem_stdSimplex_fin_three (unitInterval_sub_nonneg s) s.2.1 le_rfl (by ring)⟩

theorem continuous_simplexEdgePoint0 : Continuous simplexEdgePoint0 := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  fin_cases j <;> fun_prop

theorem continuous_simplexEdgePoint1 : Continuous simplexEdgePoint1 := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  fin_cases j <;> fun_prop

theorem continuous_simplexEdgePoint2 : Continuous simplexEdgePoint2 := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  fin_cases j <;> fun_prop

theorem simplexEdgePoint0_zero : simplexEdgePoint0 0 = stdSimplex.vertex (1 : Fin 3) := by
  apply Subtype.ext
  funext j
  fin_cases j <;> simp [simplexEdgePoint0]

theorem simplexEdgePoint0_one : simplexEdgePoint0 1 = stdSimplex.vertex (2 : Fin 3) := by
  apply Subtype.ext
  funext j
  fin_cases j <;> simp [simplexEdgePoint0]

theorem simplexEdgePoint1_zero : simplexEdgePoint1 0 = stdSimplex.vertex (0 : Fin 3) := by
  apply Subtype.ext
  funext j
  fin_cases j <;> simp [simplexEdgePoint1]

theorem simplexEdgePoint1_one : simplexEdgePoint1 1 = stdSimplex.vertex (2 : Fin 3) := by
  apply Subtype.ext
  funext j
  fin_cases j <;> simp [simplexEdgePoint1]

theorem simplexEdgePoint2_zero : simplexEdgePoint2 0 = stdSimplex.vertex (0 : Fin 3) := by
  apply Subtype.ext
  funext j
  fin_cases j <;> simp [simplexEdgePoint2]

theorem simplexEdgePoint2_one : simplexEdgePoint2 1 = stdSimplex.vertex (1 : Fin 3) := by
  apply Subtype.ext
  funext j
  fin_cases j <;> simp [simplexEdgePoint2]

def simplexEdgePath0 : Path (stdSimplex.vertex (S := ℝ) (1 : Fin 3)) (stdSimplex.vertex (S := ℝ) (2 : Fin 3)) where
  toFun := simplexEdgePoint0
  continuous_toFun := continuous_simplexEdgePoint0
  source' := simplexEdgePoint0_zero
  target' := simplexEdgePoint0_one

def simplexEdgePath1 : Path (stdSimplex.vertex (S := ℝ) (0 : Fin 3)) (stdSimplex.vertex (S := ℝ) (2 : Fin 3)) where
  toFun := simplexEdgePoint1
  continuous_toFun := continuous_simplexEdgePoint1
  source' := simplexEdgePoint1_zero
  target' := simplexEdgePoint1_one

def simplexEdgePath2 : Path (stdSimplex.vertex (S := ℝ) (0 : Fin 3)) (stdSimplex.vertex (S := ℝ) (1 : Fin 3)) where
  toFun := simplexEdgePoint2
  continuous_toFun := continuous_simplexEdgePoint2
  source' := simplexEdgePoint2_zero
  target' := simplexEdgePoint2_one

theorem stdSimplexHomeomorphUnitInterval_symm_val (s : unitInterval) :
    (stdSimplexHomeomorphUnitInterval.symm s).val = ![1 - (s : ℝ), (s : ℝ)] := by
  rw [stdSimplexHomeomorphUnitInterval]
  rfl

theorem simplexSourceVertex_delta_zero (τ : integralSingularSimplex 2 X) :
    simplexSourceVertex ((TopCat.toSSet.obj (TopCat.of X)).δ 0 τ) =
      (integralSingularSimplexEquiv 2 X τ) (stdSimplex.vertex (1 : Fin 3)) := by
  simp only [simplexSourceVertex]
  rw [TopCat.toSSetObj₀Equiv_apply, TopCat.toSSetObjEquiv_δ_apply,
    TopCat.toSSetObjEquiv_δ_apply]
  congr 1
  rw [show (default : stdSimplex ℝ (Fin 1)) = stdSimplex.vertex 0 from
    Subsingleton.elim _ _, stdSimplex.map_vertex, stdSimplex.map_vertex]
  congr 1

theorem simplexTargetVertex_delta_zero (τ : integralSingularSimplex 2 X) :
    simplexTargetVertex ((TopCat.toSSet.obj (TopCat.of X)).δ 0 τ) =
      (integralSingularSimplexEquiv 2 X τ) (stdSimplex.vertex (2 : Fin 3)) := by
  simp only [simplexTargetVertex]
  rw [TopCat.toSSetObj₀Equiv_apply, TopCat.toSSetObjEquiv_δ_apply,
    TopCat.toSSetObjEquiv_δ_apply]
  congr 1
  rw [show (default : stdSimplex ℝ (Fin 1)) = stdSimplex.vertex 0 from
    Subsingleton.elim _ _, stdSimplex.map_vertex, stdSimplex.map_vertex]
  congr 1

theorem simplexSourceVertex_delta_one (τ : integralSingularSimplex 2 X) :
    simplexSourceVertex ((TopCat.toSSet.obj (TopCat.of X)).δ 1 τ) =
      (integralSingularSimplexEquiv 2 X τ) (stdSimplex.vertex (0 : Fin 3)) := by
  simp only [simplexSourceVertex]
  rw [TopCat.toSSetObj₀Equiv_apply, TopCat.toSSetObjEquiv_δ_apply,
    TopCat.toSSetObjEquiv_δ_apply]
  congr 1
  rw [show (default : stdSimplex ℝ (Fin 1)) = stdSimplex.vertex 0 from
    Subsingleton.elim _ _, stdSimplex.map_vertex, stdSimplex.map_vertex]
  congr 1

theorem simplexTargetVertex_delta_one (τ : integralSingularSimplex 2 X) :
    simplexTargetVertex ((TopCat.toSSet.obj (TopCat.of X)).δ 1 τ) =
      (integralSingularSimplexEquiv 2 X τ) (stdSimplex.vertex (2 : Fin 3)) := by
  simp only [simplexTargetVertex]
  rw [TopCat.toSSetObj₀Equiv_apply, TopCat.toSSetObjEquiv_δ_apply,
    TopCat.toSSetObjEquiv_δ_apply]
  congr 1
  rw [show (default : stdSimplex ℝ (Fin 1)) = stdSimplex.vertex 0 from
    Subsingleton.elim _ _, stdSimplex.map_vertex, stdSimplex.map_vertex]
  congr 1

theorem simplexSourceVertex_delta_two (τ : integralSingularSimplex 2 X) :
    simplexSourceVertex ((TopCat.toSSet.obj (TopCat.of X)).δ 2 τ) =
      (integralSingularSimplexEquiv 2 X τ) (stdSimplex.vertex (0 : Fin 3)) := by
  simp only [simplexSourceVertex]
  rw [TopCat.toSSetObj₀Equiv_apply, TopCat.toSSetObjEquiv_δ_apply,
    TopCat.toSSetObjEquiv_δ_apply]
  congr 1
  rw [show (default : stdSimplex ℝ (Fin 1)) = stdSimplex.vertex 0 from
    Subsingleton.elim _ _, stdSimplex.map_vertex, stdSimplex.map_vertex]
  congr 1

theorem simplexTargetVertex_delta_two (τ : integralSingularSimplex 2 X) :
    simplexTargetVertex ((TopCat.toSSet.obj (TopCat.of X)).δ 2 τ) =
      (integralSingularSimplexEquiv 2 X τ) (stdSimplex.vertex (1 : Fin 3)) := by
  simp only [simplexTargetVertex]
  rw [TopCat.toSSetObj₀Equiv_apply, TopCat.toSSetObjEquiv_δ_apply,
    TopCat.toSSetObjEquiv_δ_apply]
  congr 1
  rw [show (default : stdSimplex ℝ (Fin 1)) = stdSimplex.vertex 0 from
    Subsingleton.elim _ _, stdSimplex.map_vertex, stdSimplex.map_vertex]
  congr 1

theorem simplexMap_succAbove_zero (s : unitInterval) :
    stdSimplex.map (Fin.succAbove (0 : Fin 3)) (stdSimplexHomeomorphUnitInterval.symm s) =
      simplexEdgePoint0 s := by
  apply Subtype.ext
  funext j
  fin_cases j <;>
    · simp only [stdSimplex.map, FunOnFinite.linearMap_apply_apply, simplexEdgePoint0,
        stdSimplexHomeomorphUnitInterval, stdSimplexEquivIcc]
      rw [Finset.sum_filter]
      simp [Fin.sum_univ_two, Fin.succAbove]
      try rfl

theorem simplexMap_succAbove_one (s : unitInterval) :
    stdSimplex.map (Fin.succAbove (1 : Fin 3)) (stdSimplexHomeomorphUnitInterval.symm s) =
      simplexEdgePoint1 s := by
  apply Subtype.ext
  funext j
  fin_cases j <;>
    · simp only [stdSimplex.map, FunOnFinite.linearMap_apply_apply, simplexEdgePoint1,
        stdSimplexHomeomorphUnitInterval, stdSimplexEquivIcc]
      rw [Finset.sum_filter]
      simp [Fin.sum_univ_two, Fin.succAbove]
      try rfl

theorem simplexMap_succAbove_two (s : unitInterval) :
    stdSimplex.map (Fin.succAbove (2 : Fin 3)) (stdSimplexHomeomorphUnitInterval.symm s) =
      simplexEdgePoint2 s := by
  apply Subtype.ext
  funext j
  fin_cases j <;>
    · simp only [stdSimplex.map, FunOnFinite.linearMap_apply_apply, simplexEdgePoint2,
        stdSimplexHomeomorphUnitInterval, stdSimplexEquivIcc]
      rw [Finset.sum_filter]
      simp [Fin.sum_univ_two, Fin.succAbove]
      try rfl

theorem integralSimplexPath_delta_zero (τ : integralSingularSimplex 2 X) (s : unitInterval) :
    integralSimplexPath ((TopCat.toSSet.obj (TopCat.of X)).δ 0 τ) s =
      (integralSingularSimplexEquiv 2 X τ) (simplexEdgePoint0 s) := by
  have h1 : integralSimplexPath ((TopCat.toSSet.obj (TopCat.of X)).δ 0 τ) s
      = (integralSingularSimplexEquiv 1 X ((TopCat.toSSet.obj (TopCat.of X)).δ 0 τ))
        (stdSimplexHomeomorphUnitInterval.symm s) := by rw [integralSimplexPath]; rfl
  rw [h1]
  simp only [integralSingularSimplexEquiv]
  rw [TopCat.toSSetObjEquiv_δ_apply, simplexMap_succAbove_zero]

theorem integralSimplexPath_delta_one (τ : integralSingularSimplex 2 X) (s : unitInterval) :
    integralSimplexPath ((TopCat.toSSet.obj (TopCat.of X)).δ 1 τ) s =
      (integralSingularSimplexEquiv 2 X τ) (simplexEdgePoint1 s) := by
  have h1 : integralSimplexPath ((TopCat.toSSet.obj (TopCat.of X)).δ 1 τ) s
      = (integralSingularSimplexEquiv 1 X ((TopCat.toSSet.obj (TopCat.of X)).δ 1 τ))
        (stdSimplexHomeomorphUnitInterval.symm s) := by rw [integralSimplexPath]; rfl
  rw [h1]
  simp only [integralSingularSimplexEquiv]
  rw [TopCat.toSSetObjEquiv_δ_apply, simplexMap_succAbove_one]

theorem integralSimplexPath_delta_two (τ : integralSingularSimplex 2 X) (s : unitInterval) :
    integralSimplexPath ((TopCat.toSSet.obj (TopCat.of X)).δ 2 τ) s =
      (integralSingularSimplexEquiv 2 X τ) (simplexEdgePoint2 s) := by
  have h1 : integralSimplexPath ((TopCat.toSSet.obj (TopCat.of X)).δ 2 τ) s
      = (integralSingularSimplexEquiv 1 X ((TopCat.toSSet.obj (TopCat.of X)).δ 2 τ))
        (stdSimplexHomeomorphUnitInterval.symm s) := by rw [integralSimplexPath]; rfl
  rw [h1]
  simp only [integralSingularSimplexEquiv]
  rw [TopCat.toSSetObjEquiv_δ_apply, simplexMap_succAbove_two]

def facePath0 (τ : integralSingularSimplex 2 X) :
    Path ((integralSingularSimplexEquiv 2 X τ) (stdSimplex.vertex (1 : Fin 3)))
      ((integralSingularSimplexEquiv 2 X τ) (stdSimplex.vertex (2 : Fin 3))) where
  toFun := fun s => integralSimplexPath ((TopCat.toSSet.obj (TopCat.of X)).δ 0 τ) s
  continuous_toFun := (integralSimplexPath ((TopCat.toSSet.obj (TopCat.of X)).δ 0 τ)).continuous
  source' := (integralSimplexPath ((TopCat.toSSet.obj (TopCat.of X)).δ 0 τ)).source.trans
    (simplexSourceVertex_delta_zero τ)
  target' := (integralSimplexPath ((TopCat.toSSet.obj (TopCat.of X)).δ 0 τ)).target.trans
    (simplexTargetVertex_delta_zero τ)

def facePath1 (τ : integralSingularSimplex 2 X) :
    Path ((integralSingularSimplexEquiv 2 X τ) (stdSimplex.vertex (0 : Fin 3)))
      ((integralSingularSimplexEquiv 2 X τ) (stdSimplex.vertex (2 : Fin 3))) where
  toFun := fun s => integralSimplexPath ((TopCat.toSSet.obj (TopCat.of X)).δ 1 τ) s
  continuous_toFun := (integralSimplexPath ((TopCat.toSSet.obj (TopCat.of X)).δ 1 τ)).continuous
  source' := (integralSimplexPath ((TopCat.toSSet.obj (TopCat.of X)).δ 1 τ)).source.trans
    (simplexSourceVertex_delta_one τ)
  target' := (integralSimplexPath ((TopCat.toSSet.obj (TopCat.of X)).δ 1 τ)).target.trans
    (simplexTargetVertex_delta_one τ)

def facePath2 (τ : integralSingularSimplex 2 X) :
    Path ((integralSingularSimplexEquiv 2 X τ) (stdSimplex.vertex (0 : Fin 3)))
      ((integralSingularSimplexEquiv 2 X τ) (stdSimplex.vertex (1 : Fin 3))) where
  toFun := fun s => integralSimplexPath ((TopCat.toSSet.obj (TopCat.of X)).δ 2 τ) s
  continuous_toFun := (integralSimplexPath ((TopCat.toSSet.obj (TopCat.of X)).δ 2 τ)).continuous
  source' := (integralSimplexPath ((TopCat.toSSet.obj (TopCat.of X)).δ 2 τ)).source.trans
    (simplexSourceVertex_delta_two τ)
  target' := (integralSimplexPath ((TopCat.toSSet.obj (TopCat.of X)).δ 2 τ)).target.trans
    (simplexTargetVertex_delta_two τ)

theorem facePath0_apply (τ : integralSingularSimplex 2 X) (s : unitInterval) :
    facePath0 τ s = (integralSingularSimplexEquiv 2 X τ) (simplexEdgePoint0 s) := by
  exact integralSimplexPath_delta_zero τ s

theorem facePath1_apply (τ : integralSingularSimplex 2 X) (s : unitInterval) :
    facePath1 τ s = (integralSingularSimplexEquiv 2 X τ) (simplexEdgePoint1 s) := by
  exact integralSimplexPath_delta_one τ s

theorem facePath2_apply (τ : integralSingularSimplex 2 X) (s : unitInterval) :
    facePath2 τ s = (integralSingularSimplexEquiv 2 X τ) (simplexEdgePoint2 s) := by
  exact integralSimplexPath_delta_two τ s

theorem facePath0_eq_map (τ : integralSingularSimplex 2 X) :
    facePath0 τ = simplexEdgePath0.map (integralSingularSimplexEquiv 2 X τ).continuous := by
  apply Path.ext
  funext s
  rw [facePath0_apply]
  rfl

theorem facePath1_eq_map (τ : integralSingularSimplex 2 X) :
    facePath1 τ = simplexEdgePath1.map (integralSingularSimplexEquiv 2 X τ).continuous := by
  apply Path.ext
  funext s
  rw [facePath1_apply]
  rfl

theorem facePath2_eq_map (τ : integralSingularSimplex 2 X) :
    facePath2 τ = simplexEdgePath2.map (integralSingularSimplexEquiv 2 X τ).continuous := by
  apply Path.ext
  funext s
  rw [facePath2_apply]
  rfl

theorem facePath_trans_homotopic (τ : integralSingularSimplex 2 X) :
    ((facePath2 τ).trans (facePath0 τ)).Homotopic (facePath1 τ) := by
  have hc : ContractibleSpace (stdSimplex ℝ (Fin 3)) :=
    (convex_stdSimplex ℝ (Fin 3)).contractibleSpace
      ⟨(stdSimplex.vertex (0 : Fin 3) : Fin 3 → ℝ), (stdSimplex.vertex (0 : Fin 3)).2⟩
  have hs : SimplyConnectedSpace (stdSimplex ℝ (Fin 3)) :=
    @SimplyConnectedSpace.ofContractible (stdSimplex ℝ (Fin 3)) _ hc
  have hN : ((simplexEdgePath2.trans simplexEdgePath0)).Homotopic simplexEdgePath1 :=
    @SimplyConnectedSpace.paths_homotopic (stdSimplex ℝ (Fin 3)) _ hs _ _
      (simplexEdgePath2.trans simplexEdgePath0) simplexEdgePath1
  have hM := hN.map (integralSingularSimplexEquiv 2 X τ)
  rw [Path.map_trans] at hM
  rw [show simplexEdgePath2.map (integralSingularSimplexEquiv 2 X τ).continuous = facePath2 τ
      from (facePath2_eq_map τ).symm,
    show simplexEdgePath0.map (integralSingularSimplexEquiv 2 X τ).continuous = facePath0 τ
      from (facePath0_eq_map τ).symm,
    show simplexEdgePath1.map (integralSingularSimplexEquiv 2 X τ).continuous = facePath1 τ
      from (facePath1_eq_map τ).symm] at hM
  exact hM

theorem pathLoop_conj_eq {x a b a' b' : X}
    (p : Path x a) (p' : Path x a') (hp : ∀ t, p t = p' t)
    (e : Path a b) (e' : Path a' b') (he : ∀ t, e t = e' t)
    (q : Path x b) (q' : Path x b') (hq : ∀ t, q t = q' t) :
    p.trans (e.trans q.symm) = p'.trans (e'.trans q'.symm) := by
  apply Path.ext
  funext t
  simp only [Path.trans_apply, Path.symm_apply, Function.comp_apply]
  split_ifs
  all_goals first | rw [hp] | rw [he] | rw [hq]

theorem pathLoopOfSimplex_delta_zero [PathConnectedSpace X] (x : X)
    (τ : integralSingularSimplex 2 X) :
    pathLoopOfSimplex x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 τ) =
      (PathConnectedSpace.somePath x
        ((integralSingularSimplexEquiv 2 X τ) (stdSimplex.vertex (1 : Fin 3)))).trans
      ((facePath0 τ).trans (PathConnectedSpace.somePath x
        ((integralSingularSimplexEquiv 2 X τ) (stdSimplex.vertex (2 : Fin 3)))).symm) := by
  rw [pathLoopOfSimplex]
  refine pathLoop_conj_eq _ _
    (fun t => congrArg (fun y => PathConnectedSpace.somePath x y t)
      (simplexSourceVertex_delta_zero τ)) _ _
    (fun t => (integralSimplexPath_delta_zero τ t).trans (facePath0_apply τ t).symm) _ _
    (fun t => congrArg (fun y => PathConnectedSpace.somePath x y t)
      (simplexTargetVertex_delta_zero τ))

theorem pathLoopOfSimplex_delta_one [PathConnectedSpace X] (x : X)
    (τ : integralSingularSimplex 2 X) :
    pathLoopOfSimplex x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 τ) =
      (PathConnectedSpace.somePath x
        ((integralSingularSimplexEquiv 2 X τ) (stdSimplex.vertex (0 : Fin 3)))).trans
      ((facePath1 τ).trans (PathConnectedSpace.somePath x
        ((integralSingularSimplexEquiv 2 X τ) (stdSimplex.vertex (2 : Fin 3)))).symm) := by
  rw [pathLoopOfSimplex]
  refine pathLoop_conj_eq _ _
    (fun t => congrArg (fun y => PathConnectedSpace.somePath x y t)
      (simplexSourceVertex_delta_one τ)) _ _
    (fun t => (integralSimplexPath_delta_one τ t).trans (facePath1_apply τ t).symm) _ _
    (fun t => congrArg (fun y => PathConnectedSpace.somePath x y t)
      (simplexTargetVertex_delta_one τ))

theorem pathLoopOfSimplex_delta_two [PathConnectedSpace X] (x : X)
    (τ : integralSingularSimplex 2 X) :
    pathLoopOfSimplex x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 τ) =
      (PathConnectedSpace.somePath x
        ((integralSingularSimplexEquiv 2 X τ) (stdSimplex.vertex (0 : Fin 3)))).trans
      ((facePath2 τ).trans (PathConnectedSpace.somePath x
        ((integralSingularSimplexEquiv 2 X τ) (stdSimplex.vertex (1 : Fin 3)))).symm) := by
  rw [pathLoopOfSimplex]
  refine pathLoop_conj_eq _ _
    (fun t => congrArg (fun y => PathConnectedSpace.somePath x y t)
      (simplexSourceVertex_delta_two τ)) _ _
    (fun t => (integralSimplexPath_delta_two τ t).trans (facePath2_apply τ t).symm) _ _
    (fun t => congrArg (fun y => PathConnectedSpace.somePath x y t)
      (simplexTargetVertex_delta_two τ))

theorem facePath_homotopic_trans (τ : integralSingularSimplex 2 X) :
    Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk (facePath2 τ))
      (Path.Homotopic.Quotient.mk (facePath0 τ)) =
      Path.Homotopic.Quotient.mk (facePath1 τ) :=
  Quotient.sound (facePath_trans_homotopic τ)

theorem pathLoopOfSimplex_delta_mul [PathConnectedSpace X] (x : X)
    (τ : integralSingularSimplex 2 X) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (pathLoopOfSimplex x
        ((TopCat.toSSet.obj (TopCat.of X)).δ 0 τ))) *
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (pathLoopOfSimplex x
        ((TopCat.toSSet.obj (TopCat.of X)).δ 2 τ))) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (pathLoopOfSimplex x
        ((TopCat.toSSet.obj (TopCat.of X)).δ 1 τ))) := by
  have hF := facePath_homotopic_trans τ
  rw [FundamentalGroup.mul_def, pathLoopOfSimplex_delta_two x τ,
    pathLoopOfSimplex_delta_zero x τ, pathLoopOfSimplex_delta_one x τ]
  dsimp only [FundamentalGroup.fromPath, FundamentalGroup.fromArrow]
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
  refine (Path.Homotopic.Quotient.trans_assoc _ _ _).trans ?_
  nth_rewrite 1 [Path.Homotopic.Quotient.trans_assoc]
  nth_rewrite 3 [← Path.Homotopic.Quotient.trans_assoc]
  rw [Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]
  nth_rewrite 2 [← Path.Homotopic.Quotient.trans_assoc]
  rw [hF]

theorem abelianization_face_product [PathConnectedSpace X] (x : X)
    (τ : integralSingularSimplex 2 X) :
    Abelianization.of (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (pathLoopOfSimplex x
          ((TopCat.toSSet.obj (TopCat.of X)).δ 0 τ)))) *
      (Abelianization.of (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (pathLoopOfSimplex x
          ((TopCat.toSSet.obj (TopCat.of X)).δ 1 τ)))))⁻¹ *
      Abelianization.of (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (pathLoopOfSimplex x
          ((TopCat.toSSet.obj (TopCat.of X)).δ 2 τ)))) = 1 := by
  have h := congrArg (Abelianization.of (G := FundamentalGroup X x))
    (pathLoopOfSimplex_delta_mul x τ)
  rw [map_mul] at h
  rw [mul_right_comm, ← h]
  exact mul_inv_cancel _

def hurewiczPairing [PathConnectedSpace X] (x : X) :
    (integralSingularChains X).X 1 →ₗ[ℤ] Additive (Abelianization (FundamentalGroup X x)) :=
  (integralSingularChainBasis 1 X).constr
    (M' := Additive (Abelianization (FundamentalGroup X x))) ℕ
    (fun σ => Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (pathLoopOfSimplex x σ)))))

theorem hurewiczPairing_simplex [PathConnectedSpace X] (x : X)
    (σ : integralSingularSimplex 1 X) :
    hurewiczPairing x (integralSimplexChain 1 σ) =
      Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (pathLoopOfSimplex x σ)))) := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis 1 X).constr_basis ℕ _ σ

theorem hurewiczPairing_boundary_simplex [PathConnectedSpace X] (x : X)
    (τ : integralSingularSimplex 2 X) :
    hurewiczPairing x ((integralSingularChains X).d 2 1 (integralSimplexChain 2 τ)) = 0 := by
  rw [integralSimplexChain_boundary_two, map_add, map_sub, hurewiczPairing_simplex,
    hurewiczPairing_simplex, hurewiczPairing_simplex]
  exact congrArg Additive.ofMul (abelianization_face_product x τ)

theorem hurewiczPairing_comp_boundary [PathConnectedSpace X] (x : X) :
    (hurewiczPairing x).comp (((integralSingularChains X).d 2 1).hom) = 0 := by
  apply (integralSingularChainBasis 2 X).ext
  intro σ
  rw [LinearMap.comp_apply, LinearMap.zero_apply, integralSingularChainBasis_apply]
  exact hurewiczPairing_boundary_simplex x σ

theorem hurewiczPairing_boundary [PathConnectedSpace X] (x : X)
    (c : (integralSingularChains X).X 2) :
    hurewiczPairing x ((integralSingularChains X).d 2 1 c) = 0 :=
  LinearMap.congr_fun (hurewiczPairing_comp_boundary x) c

end DifferentialGeometry.Topology
