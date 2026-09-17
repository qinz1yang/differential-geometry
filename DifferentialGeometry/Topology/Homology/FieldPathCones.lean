import DifferentialGeometry.Topology.Homology.PathCones
import DifferentialGeometry.Topology.Homology.BettiNumber

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Module
open scoped Simplicial Topology

namespace DifferentialGeometry.Topology

variable {k X : Type} [Field k] [TopologicalSpace X]

abbrev fieldSingularChains : ChainComplex (ModuleCat k) ℕ :=
  ((singularChainComplexFunctor (ModuleCat k)).obj (ModuleCat.of k k)).obj (TopCat.of X)

def fieldSimplexChain (n : ℕ) (σ : integralSingularSimplex n X) :
    (fieldSingularChains (k := k) (X := X)).X n :=
  ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := ModuleCat.of k k) σ).hom 1

def fieldSingularChainFinsuppIso (n : ℕ) :
    (fieldSingularChains (k := k) (X := X)).X n ≅
      ModuleCat.of k (integralSingularSimplex n X →₀ k) :=
  ((TopCat.toSSet.obj (TopCat.of X)).isColimitChainComplexXCofan (ModuleCat.of k k) n)
    |>.coconePointUniqueUpToIso
      (ModuleCat.finsuppCoconeIsColimit k k (integralSingularSimplex n X))

def fieldSingularChainBasis (n : ℕ) :
    Basis (integralSingularSimplex n X) k
      ((fieldSingularChains (k := k) (X := X)).X n) :=
  Basis.ofRepr (fieldSingularChainFinsuppIso (k := k) (X := X) n).toLinearEquiv

theorem fieldSingularChainFinsuppIso_simplex (n : ℕ) (σ : integralSingularSimplex n X) :
    (fieldSingularChainFinsuppIso (k := k) (X := X) n).hom
        (fieldSimplexChain (k := k) n σ) = Finsupp.single σ 1 := by
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    ((TopCat.toSSet.obj (TopCat.of X)).isColimitChainComplexXCofan (ModuleCat.of k k) n)
    (ModuleCat.finsuppCoconeIsColimit k k (integralSingularSimplex n X)) ⟨σ⟩
  have he := congrArg (fun f => f.hom (1 : k)) h
  change (fieldSingularChainFinsuppIso (k := k) (X := X) n).hom
      (fieldSimplexChain (k := k) n σ) = (Finsupp.lsingle σ) 1 at he
  simpa only [Finsupp.lsingle_apply] using he

theorem fieldSingularChainBasis_apply (n : ℕ) (σ : integralSingularSimplex n X) :
    fieldSingularChainBasis (k := k) (X := X) n σ = fieldSimplexChain (k := k) n σ := by
  apply (fieldSingularChainBasis (k := k) (X := X) n).repr.injective
  rw [(fieldSingularChainBasis (k := k) (X := X) n).repr_self]
  exact (fieldSingularChainFinsuppIso_simplex (k := k) (X := X) n σ).symm

theorem fieldSimplexChain_boundary (n : ℕ) (σ : integralSingularSimplex (n + 1) X) :
    (fieldSingularChains (k := k) (X := X)).d (n + 1) n
        (fieldSimplexChain (k := k) (n + 1) σ) =
      ∑ i : Fin (n + 2), (-1 : k) ^ i.val •
        fieldSimplexChain (k := k) n ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) := by
  have h := (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex_d
    (R := ModuleCat.of k k) σ
  let ev : (ModuleCat.of k k ⟶
      ((TopCat.toSSet.obj (TopCat.of X)).chainComplex (ModuleCat.of k k)).X n) →+
      ((TopCat.toSSet.obj (TopCat.of X)).chainComplex (ModuleCat.of k k)).X n :=
    { toFun := fun f => f 1
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have he := congrArg ev h
  refine he.trans ?_
  refine (map_sum ev _ Finset.univ).trans ?_
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, ← Int.cast_smul_eq_zsmul k]
  push_cast
  rfl

theorem fieldSimplexChain_boundary_one (σ : integralSingularSimplex 1 X) :
    (fieldSingularChains (k := k) (X := X)).d 1 0 (fieldSimplexChain (k := k) 1 σ) =
      fieldSimplexChain (k := k) 0 ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ) -
        fieldSimplexChain (k := k) 0 ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ) := by
  simpa [Fin.sum_univ_two, sub_eq_add_neg] using fieldSimplexChain_boundary (k := k) 0 σ

theorem fieldSimplexChain_boundary_two (σ : integralSingularSimplex 2 X) :
    (fieldSingularChains (k := k) (X := X)).d 2 1 (fieldSimplexChain (k := k) 2 σ) =
      fieldSimplexChain (k := k) 1 ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ) -
        fieldSimplexChain (k := k) 1 ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ) +
          fieldSimplexChain (k := k) 1 ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ) := by
  simpa [Fin.sum_univ_succ, Fin.sum_univ_two, sub_eq_add_neg, add_assoc] using
    fieldSimplexChain_boundary (k := k) 1 σ

def fieldPathChain {x y : X} (p : Path x y) :
    (fieldSingularChains (k := k) (X := X)).X 1 :=
  fieldSimplexChain (k := k) 1 (integralPathSimplex p)

theorem fieldPathChain_simplexPath (σ : integralSingularSimplex 1 X) :
    fieldPathChain (k := k) (integralSimplexPath σ) = fieldSimplexChain (k := k) 1 σ := by
  unfold fieldPathChain
  rw [integralPathSimplex_simplexPath]

variable [SimplyConnectedSpace X]

def fieldSingularConeZero (a : X) :
    (fieldSingularChains (k := k) (X := X)).X 0 →ₗ[k]
      (fieldSingularChains (k := k) (X := X)).X 1 :=
  (fieldSingularChainBasis (k := k) (X := X) 0).constr
    (M' := (fieldSingularChains (k := k) (X := X)).X 1) ℕ (fun σ =>
      fieldPathChain (k := k) (PathConnectedSpace.somePath a (TopCat.toSSetObj₀Equiv σ)))

theorem fieldSingularConeZero_simplex (a : X) (σ : integralSingularSimplex 0 X) :
    fieldSingularConeZero (k := k) a (fieldSimplexChain (k := k) 0 σ) =
      fieldPathChain (k := k) (PathConnectedSpace.somePath a (TopCat.toSSetObj₀Equiv σ)) := by
  rw [← fieldSingularChainBasis_apply]
  exact (fieldSingularChainBasis (k := k) (X := X) 0).constr_basis ℕ _ σ

def fieldSingularConeTriangle (a : X) (σ : integralSingularSimplex 1 X) :
    integralSingularSimplex 2 X :=
  (exists_integralPathTriangle (PathConnectedSpace.somePath a _)
    (integralSimplexPath σ) (PathConnectedSpace.somePath a _)).choose

theorem fieldSingularConeTriangle_faces (a : X) (σ : integralSingularSimplex 1 X) :
    ∀ i : Fin 3, (TopCat.toSSet.obj (TopCat.of X)).δ i (fieldSingularConeTriangle a σ) =
      ![integralPathSimplex (integralSimplexPath σ),
        integralPathSimplex (PathConnectedSpace.somePath a
          (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ))),
        integralPathSimplex (PathConnectedSpace.somePath a
          (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)))] i :=
  (exists_integralPathTriangle (PathConnectedSpace.somePath a _)
    (integralSimplexPath σ) (PathConnectedSpace.somePath a _)).choose_spec

def fieldSingularConeOne (a : X) :
    (fieldSingularChains (k := k) (X := X)).X 1 →ₗ[k]
      (fieldSingularChains (k := k) (X := X)).X 2 :=
  (fieldSingularChainBasis (k := k) (X := X) 1).constr
    (M' := (fieldSingularChains (k := k) (X := X)).X 2) ℕ (fun σ =>
      fieldSimplexChain (k := k) 2 (fieldSingularConeTriangle a σ))

theorem fieldSingularConeOne_simplex (a : X) (σ : integralSingularSimplex 1 X) :
    fieldSingularConeOne (k := k) a (fieldSimplexChain (k := k) 1 σ) =
      fieldSimplexChain (k := k) 2 (fieldSingularConeTriangle a σ) := by
  rw [← fieldSingularChainBasis_apply]
  exact (fieldSingularChainBasis (k := k) (X := X) 1).constr_basis ℕ _ σ

theorem fieldSingularConeTriangle_boundary (a : X) (σ : integralSingularSimplex 1 X) :
    (fieldSingularChains (k := k) (X := X)).d 2 1
        (fieldSimplexChain (k := k) 2 (fieldSingularConeTriangle a σ)) =
      fieldSimplexChain (k := k) 1 σ -
        fieldSingularConeZero (k := k) a
          (fieldSimplexChain (k := k) 0 ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)) +
        fieldSingularConeZero (k := k) a
          (fieldSimplexChain (k := k) 0 ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)) := by
  rw [fieldSimplexChain_boundary_two]
  rw [fieldSingularConeTriangle_faces a σ 0, fieldSingularConeTriangle_faces a σ 1,
    fieldSingularConeTriangle_faces a σ 2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  change fieldPathChain (k := k) (integralSimplexPath σ) -
      fieldPathChain (k := k) (PathConnectedSpace.somePath a
        (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ))) +
      fieldPathChain (k := k) (PathConnectedSpace.somePath a
        (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ))) = _
  rw [fieldPathChain_simplexPath]
  rw [fieldSingularConeZero_simplex, fieldSingularConeZero_simplex]

theorem fieldSingularConeOne_equation (a : X) :
    ((fieldSingularChains (k := k) (X := X)).d 2 1).hom.comp
        (fieldSingularConeOne (k := k) a) =
      LinearMap.id - (fieldSingularConeZero (k := k) a).comp
        ((fieldSingularChains (k := k) (X := X)).d 1 0).hom := by
  apply (fieldSingularChainBasis (k := k) (X := X) 1).ext
  intro σ
  rw [fieldSingularChainBasis_apply]
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    fieldSingularConeOne_simplex, fieldSingularConeTriangle_boundary,
    fieldSimplexChain_boundary_one, map_sub]
  abel

theorem fieldSingularConeOne_bounds (a : X)
    (c : (fieldSingularChains (k := k) (X := X)).X 1)
    (hc : (fieldSingularChains (k := k) (X := X)).d 1 0 c = 0) :
    (fieldSingularChains (k := k) (X := X)).d 2 1
        (fieldSingularConeOne (k := k) a c) = c := by
  have h := LinearMap.congr_fun (fieldSingularConeOne_equation (k := k) a) c
  simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    hc, map_zero, sub_zero] using h

omit [SimplyConnectedSpace X] in
theorem fieldSingularHomology_one_vanishing_iff :
    Subsingleton (((singularHomologyFunctor (ModuleCat k) 1).obj
      (ModuleCat.of k k)).obj (TopCat.of X)) ↔
      ∀ c : (fieldSingularChains (k := k) (X := X)).X 1,
        (fieldSingularChains (k := k) (X := X)).d 1 0 c = 0 →
          ∃ b : (fieldSingularChains (k := k) (X := X)).X 2,
            (fieldSingularChains (k := k) (X := X)).d 2 1 b = c := by
  change Subsingleton ((fieldSingularChains (k := k) (X := X)).homology 1) ↔ _
  rw [← ModuleCat.isZero_iff_subsingleton,
    ← _root_.HomologicalComplex.exactAt_iff_isZero_homology,
    _root_.HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp),
    CategoryTheory.ShortComplex.moduleCat_exact_iff]
  rfl

theorem fieldSingularHomology_one_subsingleton :
    Subsingleton (((singularHomologyFunctor (ModuleCat k) 1).obj
      (ModuleCat.of k k)).obj (TopCat.of X)) := by
  apply fieldSingularHomology_one_vanishing_iff.mpr
  intro c hc
  let a : X := Classical.choice (inferInstance : Nonempty X)
  exact ⟨fieldSingularConeOne (k := k) a c, fieldSingularConeOne_bounds a c hc⟩

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Homology

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem bettiOne_eq_zero_of_simplyConnectedSpace : bettiOne X = 0 := by
  let _ : Subsingleton (((singularHomologyFunctor (ModuleCat ℚ) 1).obj
    (ModuleCat.of ℚ ℚ)).obj (TopCat.of X)) :=
    Topology.fieldSingularHomology_one_subsingleton (k := ℚ) (X := X)
  exact Module.finrank_zero_of_subsingleton

end DifferentialGeometry.Homology
