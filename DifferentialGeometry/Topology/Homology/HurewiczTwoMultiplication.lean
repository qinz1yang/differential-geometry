import DifferentialGeometry.Topology.Homology.SquareFundamentalChain
import DifferentialGeometry.Topology.Homology.HurewiczFrontier
import DifferentialGeometry.Topology.Homology.ContractibleCoverChainEvaluation
import DifferentialGeometry.Topology.Homotopy.CubeSphereProjection

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module
open scoped Simplicial Topology

universe u v w

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]
variable {Y : Type u} [TopologicalSpace Y]

def integralChainHom (n : ℕ) (c : (integralSingularChains X).X n) :
    integralSingularCoefficients ⟶ (integralSingularChains X).X n :=
  ModuleCat.ofHom
    ((LinearMap.toSpanSingleton ℤ ((integralSingularChains X).X n) c).comp
      (ULift.moduleEquiv (R := ℤ) (M := ℤ) : integralSingularCoefficients →ₗ[ℤ] ℤ))

theorem integralChainHom_hom (n : ℕ) (c : (integralSingularChains X).X n) :
    (integralChainHom n c).hom =
      (LinearMap.toSpanSingleton ℤ ((integralSingularChains X).X n) c).comp
        (ULift.moduleEquiv (R := ℤ) (M := ℤ) : integralSingularCoefficients →ₗ[ℤ] ℤ) := rfl

@[simp] theorem integralChainHom_zero (n : ℕ) :
    integralChainHom n (0 : (integralSingularChains X).X n) = 0 := by
  apply ModuleCat.hom_ext
  rw [integralChainHom_hom, ModuleCat.hom_zero, LinearMap.toSpanSingleton_zero,
    LinearMap.zero_comp]

theorem integralChainHom_add (n : ℕ) (c d : (integralSingularChains X).X n) :
    integralChainHom n (c + d) = integralChainHom n c + integralChainHom n d := by
  apply ModuleCat.hom_ext
  rw [integralChainHom_hom, ModuleCat.hom_add, integralChainHom_hom, integralChainHom_hom,
    LinearMap.toSpanSingleton_add, LinearMap.add_comp]

theorem integralChainHom_comp_map {m : ℕ} (n : ℕ)
    (φ : (integralSingularChains X).X n ⟶ (integralSingularChains Y).X m)
    (c : (integralSingularChains X).X n) :
    integralChainHom n c ≫ φ = integralChainHom m (φ c) := by
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp, integralChainHom_hom, integralChainHom_hom, ← LinearMap.comp_assoc,
    LinearMap.comp_toSpanSingleton]

theorem integralSimplexChain_map_hom (n : ℕ) (f : C(X, Y)) (σ : integralSingularSimplex n X) :
    ((integralSingularChainMap f).f n).hom (integralSimplexChain n σ) =
      integralSimplexChain n (integralSingularSimplexMap n f σ) :=
  integralSimplexChain_map n f σ

theorem integralChainHom_d (n : ℕ) (c : (integralSingularChains X).X (n + 1)) :
    integralChainHom (n + 1) c ≫ (integralSingularChains X).d (n + 1) n =
      integralChainHom n ((integralSingularChains X).d (n + 1) n c) :=
  integralChainHom_comp_map (n + 1) ((integralSingularChains X).d (n + 1) n) c

theorem integralChainHom_chainMap_d (n : ℕ) (f : C(X, Y))
    (k : integralSingularCoefficients ⟶ (integralSingularChains X).X (n + 1))
    (hk : k ≫ (integralSingularChains X).d (n + 1) n = 0) :
    (k ≫ (integralSingularChainMap f).f (n + 1)) ≫ (integralSingularChains Y).d (n + 1) n = 0 := by
  calc (k ≫ (integralSingularChainMap f).f (n + 1)) ≫ (integralSingularChains Y).d (n + 1) n
      = k ≫ ((integralSingularChainMap f).f (n + 1) ≫
          (integralSingularChains Y).d (n + 1) n) := Category.assoc _ _ _
    _ = k ≫ ((integralSingularChains X).d (n + 1) n ≫
          (integralSingularChainMap f).f n) := by
        rw [(integralSingularChainMap f).comm (n + 1) n]
    _ = (k ≫ (integralSingularChains X).d (n + 1) n) ≫
          (integralSingularChainMap f).f n := (Category.assoc _ _ _).symm
    _ = 0 := by rw [hk, CategoryTheory.Limits.zero_comp]

theorem integralSingularChainMap_d (n : ℕ) (f : C(X, Y))
    (c : (integralSingularChains X).X (n + 1)) :
    (integralSingularChains Y).d (n + 1) n ((integralSingularChainMap f).f (n + 1) c) =
      (integralSingularChainMap f).f n ((integralSingularChains X).d (n + 1) n c) := by
  have h := congrArg (fun k : (integralSingularChains X).X (n + 1) ⟶
    (integralSingularChains Y).X n => k c) ((integralSingularChainMap f).comm (n + 1) n)
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at h
  exact h

def integralHomologyClassOf (n : ℕ)
    (z : integralSingularCoefficients ⟶ (integralSingularChains X).X (n + 1))
    (hz : z ≫ (integralSingularChains X).d (n + 1) n = 0) : integralSingularHomology (n + 1) X :=
  ((integralSingularChains X).liftCycles z n ((ComplexShape.down ℕ).next_eq' (by rfl)) hz ≫
    (integralSingularChains X).homologyπ (n + 1)) (ULift.up 1)

def integralHomologyClass (n : ℕ) (c : (integralSingularChains X).X (n + 1))
    (hc : (integralSingularChains X).d (n + 1) n c = 0) : integralSingularHomology (n + 1) X :=
  integralHomologyClassOf n (integralChainHom (n + 1) c) (by
    rw [integralChainHom_d n c, hc, integralChainHom_zero])

theorem integralHomologyClassOf_congr {n : ℕ}
    {z z' : integralSingularCoefficients ⟶ (integralSingularChains X).X (n + 1)}
    {hz : z ≫ (integralSingularChains X).d (n + 1) n = 0}
    {hz' : z' ≫ (integralSingularChains X).d (n + 1) n = 0} (h : z = z') :
    integralHomologyClassOf n z hz = integralHomologyClassOf n z' hz' := by
  cases h
  rw [Subsingleton.elim hz hz']

theorem integralHomologyClassOf_eq_of_sub_eq (n : ℕ)
    (k₁ k₂ : integralSingularCoefficients ⟶ (integralSingularChains X).X (n + 1))
    (h₁ : k₁ ≫ (integralSingularChains X).d (n + 1) n = 0)
    (h₂ : k₂ ≫ (integralSingularChains X).d (n + 1) n = 0)
    (w : integralSingularCoefficients ⟶ (integralSingularChains X).X (n + 2))
    (hw : k₁ - k₂ = w ≫ (integralSingularChains X).d (n + 2) (n + 1)) :
    integralHomologyClassOf n k₁ h₁ = integralHomologyClassOf n k₂ h₂ :=
  congrArg (fun k : integralSingularCoefficients ⟶ integralSingularHomology (n + 1) X =>
    k (ULift.up 1))
    (chainComplex_liftCycles_homologyπ_congr_of_sub_eq_boundary n k₁ k₂ h₁ h₂ w hw)

theorem integralHomologyClass_congr {n : ℕ} {c d : (integralSingularChains X).X (n + 1)}
    {hc : (integralSingularChains X).d (n + 1) n c = 0}
    {hd : (integralSingularChains X).d (n + 1) n d = 0} (h : c = d) :
    integralHomologyClass n c hc = integralHomologyClass n d hd := by
  unfold integralHomologyClass
  exact integralHomologyClassOf_congr (congrArg (integralChainHom (n + 1)) h)

theorem integralHomologyClass_eq_of_eq_add_boundary (n : ℕ)
    (c d : (integralSingularChains X).X (n + 1)) (b : (integralSingularChains X).X (n + 2))
    (hc : (integralSingularChains X).d (n + 1) n c = 0)
    (hd : (integralSingularChains X).d (n + 1) n d = 0)
    (h : c = d + (integralSingularChains X).d (n + 2) (n + 1) b) :
    integralHomologyClass n c hc = integralHomologyClass n d hd := by
  unfold integralHomologyClass
  refine integralHomologyClassOf_eq_of_sub_eq n _ _ _ _
    (integralChainHom (n + 2) b) ?_
  rw [h, integralChainHom_add, ← integralChainHom_comp_map (n + 2)
    ((integralSingularChains X).d (n + 2) (n + 1)) b]
  abel

theorem integralSingularHomologyMap_integralHomologyClassOf (n : ℕ) (f : C(X, Y))
    (z : integralSingularCoefficients ⟶ (integralSingularChains X).X (n + 1))
    (hz : z ≫ (integralSingularChains X).d (n + 1) n = 0) :
    integralSingularHomologyMap (n + 1) f (integralHomologyClassOf n z hz) =
      integralHomologyClassOf n (z ≫ (integralSingularChainMap f).f (n + 1))
        (integralChainHom_chainMap_d n f z hz) :=
  chainComplex_homologyMap_liftCycles_apply (integralSingularChainMap f) n z hz _

theorem integralSingularHomologyMap_integralHomologyClass (n : ℕ) (f : C(X, Y))
    (c : (integralSingularChains X).X (n + 1))
    (hc : (integralSingularChains X).d (n + 1) n c = 0) :
    integralSingularHomologyMap (n + 1) f (integralHomologyClass n c hc) =
      integralHomologyClass n ((integralSingularChainMap f).f (n + 1) c) (by
        rw [integralSingularChainMap_d n f c, hc]
        change ((integralSingularChainMap f).f n).hom 0 = 0
        rw [map_zero]) := by
  unfold integralHomologyClass
  rw [integralSingularHomologyMap_integralHomologyClassOf]
  exact integralHomologyClassOf_congr
    (integralChainHom_comp_map (n + 1) ((integralSingularChainMap f).f (n + 1)) c)


end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]
variable {Y : Type v} [TopologicalSpace Y]
variable {Z : Type w} [TopologicalSpace Z]

def singularSimplexImageGen (n : ℕ) (f : C(X, Y)) (σ : integralSingularSimplex n X) :
    integralSingularSimplex n Y :=
  ((TopCat.of Y).toSSetObjEquiv (Opposite.op ⦋n⦌)).symm
    (f.comp ((TopCat.of X).toSSetObjEquiv (Opposite.op ⦋n⦌) σ))

@[simp] theorem singularSimplexImageGen_val (n : ℕ) (f : C(X, Y))
    (σ : integralSingularSimplex n X) :
    (TopCat.of Y).toSSetObjEquiv (Opposite.op ⦋n⦌) (singularSimplexImageGen n f σ) =
      f.comp ((TopCat.of X).toSSetObjEquiv (Opposite.op ⦋n⦌) σ) :=
  Equiv.apply_symm_apply _ _

theorem singularSimplexImageGen_apply_val (n : ℕ) (f : C(X, Y))
    (σ : integralSingularSimplex n X) :
    integralSingularSimplexEquiv n Y (singularSimplexImageGen n f σ) =
      f.comp (integralSingularSimplexEquiv n X σ) :=
  singularSimplexImageGen_val n f σ

theorem singularSimplexImageGen_face (n : ℕ) (f : C(X, Y))
    (σ : integralSingularSimplex (n + 1) X) (i : Fin (n + 2)) :
    singularSimplexImageGen n f ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) =
      (TopCat.toSSet.obj (TopCat.of Y)).δ i (singularSimplexImageGen (n + 1) f σ) := by
  apply ((TopCat.of Y).toSSetObjEquiv (Opposite.op ⦋n⦌)).injective
  rw [singularSimplexImageGen_val]
  ext t
  simp only [ContinuousMap.comp_apply]
  rw [TopCat.toSSetObjEquiv_δ_apply, TopCat.toSSetObjEquiv_δ_apply, singularSimplexImageGen_val]
  rfl

def singularChainImageGen (n : ℕ) (f : C(X, Y)) :
    (integralSingularChains X).X n →ₗ[ℤ] (integralSingularChains Y).X n :=
  (integralSingularChainBasis n X).constr (M' := (integralSingularChains Y).X n) ℕ
    (fun σ => integralSimplexChain n (singularSimplexImageGen n f σ))

theorem singularChainImageGen_simplex (n : ℕ) (f : C(X, Y))
    (σ : integralSingularSimplex n X) :
    singularChainImageGen n f (integralSimplexChain n σ) =
      integralSimplexChain n (singularSimplexImageGen n f σ) := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis n X).constr_basis ℕ _ σ

theorem singularChainImageGen_d (n : ℕ) (f : C(X, Y)) :
    (singularChainImageGen n f).comp (((integralSingularChains X).d (n + 1) n).hom) =
      (((integralSingularChains Y).d (n + 1) n).hom).comp (singularChainImageGen (n + 1) f) := by
  apply (integralSingularChainBasis (n + 1) X).ext
  intro σ
  simp only [LinearMap.comp_apply, integralSingularChainBasis_apply]
  rw [integralSimplexChain_boundary, map_sum]
  conv_rhs => rw [singularChainImageGen_simplex, integralSimplexChain_boundary]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, singularChainImageGen_simplex, singularSimplexImageGen_face]

theorem singularChainImageGen_d_eq (n : ℕ) (f : C(X, Y))
    (c : (integralSingularChains X).X (n + 1)) :
    (integralSingularChains Y).d (n + 1) n (singularChainImageGen (n + 1) f c) =
      singularChainImageGen n f ((integralSingularChains X).d (n + 1) n c) := by
  have h := (LinearMap.congr_fun (singularChainImageGen_d n f) c).symm
  simpa only [LinearMap.comp_apply] using h

theorem singularSimplexImageGen_comp (n : ℕ) (f : C(X, Y)) (g : C(Y, Z))
    (σ : integralSingularSimplex n X) :
    singularSimplexImageGen n (g.comp f) σ =
      singularSimplexImageGen n g (singularSimplexImageGen n f σ) := by
  apply ((TopCat.of Z).toSSetObjEquiv (Opposite.op ⦋n⦌)).injective
  rw [singularSimplexImageGen_val, singularSimplexImageGen_val, singularSimplexImageGen_val,
    ContinuousMap.comp_assoc]

theorem singularChainImageGen_comp (n : ℕ) (f : C(X, Y)) (g : C(Y, Z)) :
    singularChainImageGen n (g.comp f) =
      (singularChainImageGen n g).comp (singularChainImageGen n f) := by
  apply (integralSingularChainBasis n X).ext
  intro σ
  simp only [LinearMap.comp_apply, integralSingularChainBasis_apply, singularChainImageGen_simplex]
  rw [singularSimplexImageGen_comp]

theorem singularSimplexImageGen_eq_simplexMap {X : Type u} [TopologicalSpace X]
    {Y : Type u} [TopologicalSpace Y] (n : ℕ) (f : C(X, Y))
    (σ : integralSingularSimplex n X) :
    singularSimplexImageGen n f σ = integralSingularSimplexMap n f σ := by
  apply ((TopCat.of Y).toSSetObjEquiv (Opposite.op ⦋n⦌)).injective
  rw [singularSimplexImageGen_val]
  change f.comp (integralSingularSimplexEquiv n X σ) =
    integralSingularSimplexEquiv n Y (integralSingularSimplexMap n f σ)
  rw [integralSingularSimplexMap_apply]

theorem singularChainImageGen_eq_chainMap {X : Type u} [TopologicalSpace X]
    {Y : Type u} [TopologicalSpace Y] (n : ℕ) (f : C(X, Y)) :
    singularChainImageGen n f = ((integralSingularChainMap f).f n).hom := by
  apply (integralSingularChainBasis n X).ext
  intro σ
  rw [integralSingularChainBasis_apply, singularChainImageGen_simplex, integralSimplexChain_map_hom]
  rw [singularSimplexImageGen_eq_simplexMap]

theorem integralSingularChainMap_apply_eq_singularChainImageGen {X : Type u} [TopologicalSpace X]
    {Y : Type u} [TopologicalSpace Y] (n : ℕ) (f : C(X, Y))
    (c : (integralSingularChains X).X n) :
    (integralSingularChainMap f).f n c = singularChainImageGen n f c :=
  congrArg (fun g : (integralSingularChains X).X n →ₗ[ℤ] (integralSingularChains Y).X n => g c)
    (singularChainImageGen_eq_chainMap (n := n) f).symm

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

def squareLeftScaling : C(Square, Square) where
  toFun u := ![(⟨(u 0 : ℝ) / 2, by
      constructor
      · exact div_nonneg (u 0).property.1 (by norm_num)
      · nlinarith [(u 0).property.2]⟩ : unitInterval), u 1]
  continuous_toFun := by
    rw [continuous_pi_iff]
    intro i
    fin_cases i
    · have hc : Continuous fun u : Square => ((u 0 : unitInterval) : ℝ) :=
        continuous_subtype_val.comp (continuous_apply 0)
      exact (hc.div_const 2).subtype_mk _
    · exact continuous_apply 1

def squareRightScaling : C(Square, Square) where
  toFun u := ![(⟨(u 0 : ℝ) / 2 + 1 / 2, by
      constructor
      · nlinarith [(u 0).property.1]
      · nlinarith [(u 0).property.2]⟩ : unitInterval), u 1]
  continuous_toFun := by
    rw [continuous_pi_iff]
    intro i
    fin_cases i
    · have hc : Continuous fun u : Square => ((u 0 : unitInterval) : ℝ) :=
        continuous_subtype_val.comp (continuous_apply 0)
      exact ((hc.div_const 2).add continuous_const).subtype_mk _
    · exact continuous_apply 1

theorem squareLeftScaling_apply_zero (u : Square) :
    (squareLeftScaling u ⟨0, by decide⟩ : ℝ) = (u 0 : ℝ) / 2 := rfl

theorem squareLeftScaling_apply_one (u : Square) :
    squareLeftScaling u ⟨1, by decide⟩ = u ⟨1, by decide⟩ := rfl

theorem squareRightScaling_apply_zero (u : Square) :
    (squareRightScaling u ⟨0, by decide⟩ : ℝ) = (u 0 : ℝ) / 2 + 1 / 2 := rfl

theorem squareRightScaling_apply_one (u : Square) :
    squareRightScaling u ⟨1, by decide⟩ = u ⟨1, by decide⟩ := rfl

theorem squareLeftScaling_comp_squareAffineMap (n : ℕ) (v : Fin (n + 1) → Square) :
    squareLeftScaling.comp (squareAffineMap n v) =
      squareAffineMap n (fun j => squareLeftScaling (v j)) := by
  apply ContinuousMap.ext
  intro t
  apply funext
  intro i
  apply Subtype.ext
  rw [ContinuousMap.comp_apply]
  fin_cases i
  · dsimp only
    rw [squareLeftScaling_apply_zero, squareAffineMap_apply_coe, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only
    rw [squareLeftScaling_apply_zero]
    ring
  · dsimp only
    rw [squareLeftScaling_apply_one, squareAffineMap_apply_coe]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only
    rw [squareLeftScaling_apply_one, smul_eq_mul]

theorem squareRightScaling_comp_squareAffineMap (n : ℕ) (v : Fin (n + 1) → Square) :
    squareRightScaling.comp (squareAffineMap n v) =
      squareAffineMap n (fun j => squareRightScaling (v j)) := by
  apply ContinuousMap.ext
  intro t
  apply funext
  intro i
  apply Subtype.ext
  rw [ContinuousMap.comp_apply]
  fin_cases i
  · dsimp only
    rw [squareRightScaling_apply_zero, squareAffineMap_apply_coe, squareAffineMap_apply_coe]
    simp only [squareRightScaling_apply_zero]
    have hterm : ∀ j : Fin (n + 1), (t.val j) * ((v j 0 : ℝ) / 2 + 1 / 2) =
        (t.val j * (v j 0 : ℝ)) / 2 + (t.val j) * (1 / 2) := by
      intro j
      ring
    have hR : (∑ j : Fin (n + 1), (t.val j) * ((v j 0 : ℝ) / 2 + 1 / 2)) =
        (∑ j : Fin (n + 1), t.val j * (v j 0 : ℝ)) / 2 + 1 / 2 := by
      calc (∑ j : Fin (n + 1), (t.val j) * ((v j 0 : ℝ) / 2 + 1 / 2))
          = ∑ j : Fin (n + 1), ((t.val j * (v j 0 : ℝ)) / 2 + (t.val j) * (1 / 2)) :=
              Finset.sum_congr rfl (fun j _ => hterm j)
        _ = (∑ j : Fin (n + 1), t.val j * (v j 0 : ℝ) / 2) +
              (∑ j : Fin (n + 1), (t.val j) * (1 / 2)) := Finset.sum_add_distrib
        _ = (∑ j : Fin (n + 1), t.val j * (v j 0 : ℝ)) / 2 +
              (∑ j : Fin (n + 1), t.val j) * (1 / 2) := by
              rw [Finset.sum_div, Finset.sum_mul]
        _ = (∑ j : Fin (n + 1), t.val j * (v j 0 : ℝ)) / 2 + 1 / 2 := by
              rw [t.property.2]
              ring
    rw [hR]
  · dsimp only
    rw [squareRightScaling_apply_one, squareAffineMap_apply_coe, squareAffineMap_apply_coe]
    apply Finset.sum_congr rfl
    intro j _
    rw [squareRightScaling_apply_one]

theorem squareLeftScaling_squareOrigin : squareLeftScaling squareOrigin = squareOrigin := by
  ext i
  fin_cases i
  · dsimp only
    rw [squareLeftScaling_apply_zero]
    norm_num [squareOrigin, squarePoint]
  · dsimp only
    rw [squareLeftScaling_apply_one]

theorem squareLeftScaling_squareEast : squareLeftScaling squareEast = squareMidEast := by
  ext i
  fin_cases i
  · dsimp only
    rw [squareLeftScaling_apply_zero]
    norm_num [squareEast, squareMidEast, squarePoint, halfPoint]
  · dsimp only
    rw [squareLeftScaling_apply_one]
    norm_num [squareEast, squareMidEast, squarePoint, halfPoint]

theorem squareLeftScaling_squareNorthEast :
    squareLeftScaling squareNorthEast = squareMidNorth := by
  ext i
  fin_cases i
  · dsimp only
    rw [squareLeftScaling_apply_zero]
    norm_num [squareNorthEast, squareMidNorth, squarePoint, halfPoint]
  · dsimp only
    rw [squareLeftScaling_apply_one]
    norm_num [squareNorthEast, squareMidNorth, squarePoint, halfPoint]

theorem squareLeftScaling_squareNorth : squareLeftScaling squareNorth = squareNorth := by
  ext i
  fin_cases i
  · dsimp only
    rw [squareLeftScaling_apply_zero]
    change ((0 : unitInterval) : ℝ) / 2 = ((0 : unitInterval) : ℝ)
    norm_num
  · dsimp only
    rw [squareLeftScaling_apply_one]

theorem squareRightScaling_squareOrigin : squareRightScaling squareOrigin = squareMidEast := by
  ext i
  fin_cases i
  · dsimp only
    rw [squareRightScaling_apply_zero]
    norm_num [squareOrigin, squareMidEast, squarePoint, halfPoint]
  · dsimp only
    rw [squareRightScaling_apply_one]
    norm_num [squareOrigin, squareMidEast, squarePoint, halfPoint]

theorem squareRightScaling_squareEast : squareRightScaling squareEast = squareEast := by
  ext i
  fin_cases i
  · dsimp only
    rw [squareRightScaling_apply_zero]
    norm_num [squareEast, squarePoint, halfPoint]
  · dsimp only
    rw [squareRightScaling_apply_one]

theorem squareRightScaling_squareNorthEast :
    squareRightScaling squareNorthEast = squareNorthEast := by
  ext i
  fin_cases i
  · dsimp only
    rw [squareRightScaling_apply_zero]
    norm_num [squareNorthEast, squarePoint, halfPoint]
  · dsimp only
    rw [squareRightScaling_apply_one]

theorem squareRightScaling_squareNorth : squareRightScaling squareNorth = squareMidNorth := by
  ext i
  fin_cases i
  · dsimp only
    rw [squareRightScaling_apply_zero]
    norm_num [squareNorth, squareMidNorth, squarePoint, halfPoint]
  · dsimp only
    rw [squareRightScaling_apply_one]
    norm_num [squareNorth, squareMidNorth, squarePoint, halfPoint]

theorem singularSimplexImageGen_squareAffineSimplex (n : ℕ) (f : C(Square, Square))
    (v : Fin (n + 1) → Square)
    (hf : f.comp (squareAffineMap n v) = squareAffineMap n (fun j => f (v j))) :
    singularSimplexImageGen n f (squareAffineSimplex n v) =
      squareAffineSimplex n (fun j => f (v j)) := by
  apply (integralSingularSimplexEquiv n Square).injective
  exact hf

theorem singularChainImageGen_squareTriangleChain_left (P Q R : Square) :
    singularChainImageGen 2 squareLeftScaling (squareTriangleChain P Q R) =
      squareTriangleChain (squareLeftScaling P) (squareLeftScaling Q) (squareLeftScaling R) := by
  rw [squareTriangleChain, singularChainImageGen_simplex]
  congr 1
  rw [singularSimplexImageGen_squareAffineSimplex 2 squareLeftScaling _
    (squareLeftScaling_comp_squareAffineMap 2 _)]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem singularChainImageGen_squareTriangleChain_right (P Q R : Square) :
    singularChainImageGen 2 squareRightScaling (squareTriangleChain P Q R) =
      squareTriangleChain (squareRightScaling P) (squareRightScaling Q) (squareRightScaling R) := by
  rw [squareTriangleChain, singularChainImageGen_simplex]
  congr 1
  rw [singularSimplexImageGen_squareAffineSimplex 2 squareRightScaling _
    (squareRightScaling_comp_squareAffineMap 2 _)]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem singularChainImageGen_squareLeftScaling_fundamentalChain :
    singularChainImageGen 2 squareLeftScaling squareFundamentalChain = squareLeftHalfChain := by
  simp only [squareFundamentalChain, squareLeftHalfChain, map_sub,
    singularChainImageGen_squareTriangleChain_left]
  rw [squareLeftScaling_squareOrigin, squareLeftScaling_squareEast,
    squareLeftScaling_squareNorthEast, squareLeftScaling_squareNorth]

theorem singularChainImageGen_squareRightScaling_fundamentalChain :
    singularChainImageGen 2 squareRightScaling squareFundamentalChain = squareRightHalfChain := by
  simp only [squareFundamentalChain, squareRightHalfChain, map_sub,
    singularChainImageGen_squareTriangleChain_right]
  rw [squareRightScaling_squareOrigin, squareRightScaling_squareEast,
    squareRightScaling_squareNorthEast, squareRightScaling_squareNorth]


end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

variable {Y : Type v} [TopologicalSpace Y]

def integralConstSimplex (n : ℕ) (y : Y) : integralSingularSimplex n Y :=
  (integralSingularSimplexEquiv n Y).symm (ContinuousMap.const (stdSimplex ℝ (Fin (n + 1))) y)

def integralConstChain (n : ℕ) (y : Y) : (integralSingularChains Y).X n :=
  integralSimplexChain n (integralConstSimplex n y)

theorem genLoop_boundary_property {N : Type*} {X : Type u} [TopologicalSpace X] {x : X}
    (Γ : GenLoop N X x) : ∀ t ∈ Cube.boundary N, Γ.val t = x :=
  Γ.property

theorem squareAffineSimplex_coe (n : ℕ) (v : Fin (n + 1) → Square) :
    integralSingularSimplexEquiv n Square (squareAffineSimplex n v) = squareAffineMap n v :=
  squareAffineSimplex_val n v

theorem squareAffineMap_mem_boundary_of_coord (n : ℕ) {v : Fin (n + 1) → Square} {i : Fin 2}
    {c : unitInterval} (hc : c = 0 ∨ c = 1) (hv : ∀ j, v j i = c)
    (t : stdSimplex ℝ (Fin (n + 1))) :
    squareAffineMap n v t ∈ Cube.boundary (Fin 2) := by
  have hcoord : ((squareAffineMap n v t i : unitInterval) : ℝ) = (c : ℝ) := by
    rw [squareAffineMap_apply_coe]
    calc (∑ j, (t.val j) * (v j i : ℝ)) = ∑ j, (t.val j) * (c : ℝ) :=
          Finset.sum_congr rfl (fun j _ => by rw [hv j])
      _ = (∑ j, t.val j) * (c : ℝ) :=
          (Finset.sum_mul Finset.univ (fun j => (t.val j : ℝ)) (c : ℝ)).symm
      _ = 1 * (c : ℝ) := by rw [t.property.2]
      _ = (c : ℝ) := one_mul _
  refine ⟨i, ?_⟩
  rcases hc with h | h
  · left
    apply Subtype.ext
    rw [hcoord, h]
  · right
    apply Subtype.ext
    rw [hcoord, h]

theorem singularChainImageGen_squareTriangleChain_eq_const (f : C(Square, Y)) (y : Y)
    (hf : ∀ t : Square, t ∈ Cube.boundary (Fin 2) → f t = y) {P Q R : Square}
    (hv : ∀ t : stdSimplex ℝ (Fin 3), squareAffineMap 2 ![P, Q, R] t ∈ Cube.boundary (Fin 2)) :
    singularChainImageGen 2 f (squareTriangleChain P Q R) = integralConstChain 2 y := by
  rw [squareTriangleChain, singularChainImageGen_simplex]
  congr 1
  apply (integralSingularSimplexEquiv 2 Y).injective
  rw [singularSimplexImageGen_apply_val, squareAffineSimplex_coe, integralConstSimplex,
    Equiv.apply_symm_apply]
  exact ContinuousMap.ext (fun t => hf _ (hv t))

theorem singularChainImageGen_squareSegmentChain_eq_const (f : C(Square, Y)) (y : Y)
    (hf : ∀ t : Square, t ∈ Cube.boundary (Fin 2) → f t = y) {P Q : Square}
    (hv : ∀ t : stdSimplex ℝ (Fin 2), squareAffineMap 1 ![P, Q] t ∈ Cube.boundary (Fin 2)) :
    singularChainImageGen 1 f (squareSegmentChain P Q) = integralConstChain 1 y := by
  rw [squareSegmentChain, singularChainImageGen_simplex]
  congr 1
  apply (integralSingularSimplexEquiv 1 Y).injective
  rw [singularSimplexImageGen_apply_val, squareAffineSimplex_coe, integralConstSimplex,
    Equiv.apply_symm_apply]
  exact ContinuousMap.ext (fun t => hf _ (hv t))

theorem squareAffineMap_boundary_east_northEast (t : stdSimplex ℝ (Fin 2)) :
    squareAffineMap 1 ![squareEast, squareNorthEast] t ∈ Cube.boundary (Fin 2) :=
  squareAffineMap_mem_boundary_of_coord 1 (i := 0) (c := 1) (Or.inr rfl)
    (fun j => by fin_cases j <;> rfl) t

theorem squareAffineMap_boundary_origin_east (t : stdSimplex ℝ (Fin 2)) :
    squareAffineMap 1 ![squareOrigin, squareEast] t ∈ Cube.boundary (Fin 2) :=
  squareAffineMap_mem_boundary_of_coord 1 (i := 1) (c := 0) (Or.inl rfl)
    (fun j => by fin_cases j <;> rfl) t

theorem squareAffineMap_boundary_north_northEast (t : stdSimplex ℝ (Fin 2)) :
    squareAffineMap 1 ![squareNorth, squareNorthEast] t ∈ Cube.boundary (Fin 2) :=
  squareAffineMap_mem_boundary_of_coord 1 (i := 1) (c := 1) (Or.inr rfl)
    (fun j => by fin_cases j <;> rfl) t

theorem squareAffineMap_boundary_origin_north (t : stdSimplex ℝ (Fin 2)) :
    squareAffineMap 1 ![squareOrigin, squareNorth] t ∈ Cube.boundary (Fin 2) :=
  squareAffineMap_mem_boundary_of_coord 1 (i := 0) (c := 0) (Or.inl rfl)
    (fun j => by fin_cases j <;> rfl) t

theorem singularChainImageGen_squareFundamentalChain_isCycle (f : C(Square, Y)) (y : Y)
    (hf : ∀ t : Square, t ∈ Cube.boundary (Fin 2) → f t = y) :
    (integralSingularChains Y).d 2 1 (singularChainImageGen 2 f squareFundamentalChain) = 0 := by
  rw [singularChainImageGen_d_eq 1 f squareFundamentalChain]
  have hdW : (integralSingularChains Square).d 2 1 squareFundamentalChain =
      squareSegmentChain squareEast squareNorthEast + squareSegmentChain squareOrigin squareEast -
        squareSegmentChain squareNorth squareNorthEast -
          squareSegmentChain squareOrigin squareNorth := by
    rw [squareFundamentalChain, map_sub, squareTriangleChain_boundary, squareTriangleChain_boundary]
    abel
  rw [hdW, map_sub, map_sub, map_add]
  rw [singularChainImageGen_squareSegmentChain_eq_const f y hf squareAffineMap_boundary_east_northEast,
    singularChainImageGen_squareSegmentChain_eq_const f y hf squareAffineMap_boundary_origin_east,
    singularChainImageGen_squareSegmentChain_eq_const f y hf squareAffineMap_boundary_north_northEast,
    singularChainImageGen_squareSegmentChain_eq_const f y hf squareAffineMap_boundary_origin_north]
  abel

theorem genLoop_squareCornerChain_eq_zero {X : Type u} [TopologicalSpace X] {x : X}
    (Γ : GenLoop (Fin 2) X x) :
    singularChainImageGen 2 Γ.val squareCornerChain = 0 := by
  have h1 : singularChainImageGen 2 Γ.val
      (squareTriangleChain squareOrigin squareMidEast squareEast) = integralConstChain 2 x := by
    refine singularChainImageGen_squareTriangleChain_eq_const Γ.val x Γ.property ?_
    intro t
    exact squareAffineMap_mem_boundary_of_coord 2 (i := 1) (c := 0) (Or.inl rfl)
      (fun j => by fin_cases j <;> rfl) t
  have h2 : singularChainImageGen 2 Γ.val
      (squareTriangleChain squareNorth squareMidNorth squareNorthEast) = integralConstChain 2 x := by
    refine singularChainImageGen_squareTriangleChain_eq_const Γ.val x Γ.property ?_
    intro t
    exact squareAffineMap_mem_boundary_of_coord 2 (i := 1) (c := 1) (Or.inr rfl)
      (fun j => by fin_cases j <;> rfl) t
  rw [squareCornerChain, map_sub, h1, h2, sub_self]

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] {x : X}

theorem squareLeftScaling_transAt (Γ Δ : GenLoop (Fin 2) X x) :
    (GenLoop.transAt 0 Γ Δ).val.comp squareLeftScaling = Γ.val := by
  apply ContinuousMap.ext
  intro u
  change (GenLoop.transAt 0 Γ Δ) (squareLeftScaling u) = Γ u
  have hz : ((squareLeftScaling u) (0 : Fin 2) : ℝ) = (u 0 : ℝ) / 2 := rfl
  have ho : squareLeftScaling u (1 : Fin 2) = u (1 : Fin 2) := rfl
  have hle : ((squareLeftScaling u) 0 : ℝ) ≤ 1 / 2 := by
    rw [hz]
    nlinarith [(u 0).property.2]
  have hproj : Set.projIcc 0 1 (by norm_num : (0:ℝ) ≤ 1)
      (2 * ((squareLeftScaling u) 0 : ℝ)) = u 0 := by
    have h2 : 2 * ((squareLeftScaling u) 0 : ℝ) = (u 0 : ℝ) := by
      rw [hz]
      ring
    rw [h2]
    exact Set.projIcc_of_mem (x := (u 0 : ℝ)) (by norm_num : (0:ℝ) ≤ 1) (u 0).property
  have hupd : Function.update (squareLeftScaling u) 0
      (Set.projIcc 0 1 (by norm_num : (0:ℝ) ≤ 1)
        (2 * ((squareLeftScaling u) 0 : ℝ))) = u := by
    funext i
    rw [Function.update_apply]
    by_cases hi : i = 0
    · rw [if_pos hi, hproj, hi]
    · rw [if_neg hi]
      have h1 : i = 1 := by fin_cases i <;> simp_all
      rw [h1, ho]
  simp only [GenLoop.transAt, GenLoop.coe_copy]
  rw [if_pos hle, hupd]

theorem squareRightScaling_transAt (Γ Δ : GenLoop (Fin 2) X x) :
    (GenLoop.transAt 0 Γ Δ).val.comp squareRightScaling = Δ.val := by
  apply ContinuousMap.ext
  intro u
  change (GenLoop.transAt 0 Γ Δ) (squareRightScaling u) = Δ u
  have hz : ((squareRightScaling u) (0 : Fin 2) : ℝ) = (u 0 : ℝ) / 2 + 1 / 2 := rfl
  have ho : squareRightScaling u (1 : Fin 2) = u (1 : Fin 2) := rfl
  have h0 : ((squareRightScaling u) 0 : ℝ) = (u 0 : ℝ) / 2 + 1 / 2 := hz
  by_cases hu : (u 0 : ℝ) = 0
  · have hle : ((squareRightScaling u) 0 : ℝ) ≤ 1 / 2 := by
      rw [h0, hu]
      norm_num
    have hproj : Set.projIcc 0 1 (by norm_num : (0:ℝ) ≤ 1)
        (2 * ((squareRightScaling u) 0 : ℝ)) = (1 : unitInterval) := by
      have h2 : 2 * ((squareRightScaling u) 0 : ℝ) = 1 := by
        rw [h0, hu]
        norm_num
      rw [h2]
      exact Set.projIcc_of_mem (x := (1 : ℝ)) (by norm_num : (0:ℝ) ≤ 1)
        (by norm_num : (1 : ℝ) ∈ Set.Icc (0:ℝ) 1)
    have hbound : Function.update (squareRightScaling u) 0 (1 : unitInterval) ∈
        Cube.boundary (Fin 2) :=
      ⟨0, Or.inr (by rw [Function.update_apply, if_pos rfl])⟩
    have hbu : u ∈ Cube.boundary (Fin 2) := ⟨0, Or.inl (Subtype.ext hu)⟩
    simp only [GenLoop.transAt, GenLoop.coe_copy]
    rw [if_pos hle, hproj]
    change Γ.val (Function.update (squareRightScaling u) 0 (1 : unitInterval)) = Δ.val u
    rw [Γ.property _ hbound, Δ.property _ hbu]
  · have hlt : 1 / 2 < ((squareRightScaling u) 0 : ℝ) := by
      rw [h0]
      have hpos : 0 < (u 0 : ℝ) := lt_of_le_of_ne (u 0).property.1 (Ne.symm hu)
      linarith
    have hnle : ¬ ((squareRightScaling u) 0 : ℝ) ≤ 1 / 2 := not_le.mpr hlt
    have hproj : Set.projIcc 0 1 (by norm_num : (0:ℝ) ≤ 1)
        (2 * ((squareRightScaling u) 0 : ℝ) - 1) = u 0 := by
      have h2 : 2 * ((squareRightScaling u) 0 : ℝ) - 1 = (u 0 : ℝ) := by
        rw [h0]
        ring
      rw [h2]
      exact Set.projIcc_of_mem (x := (u 0 : ℝ)) (by norm_num : (0:ℝ) ≤ 1) (u 0).property
    have hupd : Function.update (squareRightScaling u) 0
        (Set.projIcc 0 1 (by norm_num : (0:ℝ) ≤ 1)
          (2 * ((squareRightScaling u) 0 : ℝ) - 1)) = u := by
      funext i
      rw [Function.update_apply]
      by_cases hi : i = 0
      · rw [if_pos hi, hproj, hi]
      · rw [if_neg hi]
        have h1 : i = 1 := by fin_cases i <;> simp_all
        rw [h1, ho]
    simp only [GenLoop.transAt, GenLoop.coe_copy]
    rw [if_neg hnle, hupd]

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem integralHomologyClassOf_add (n : ℕ)
    (k₁ k₂ : integralSingularCoefficients ⟶ (integralSingularChains X).X (n + 1))
    (h₁ : k₁ ≫ (integralSingularChains X).d (n + 1) n = 0)
    (h₂ : k₂ ≫ (integralSingularChains X).d (n + 1) n = 0) :
    integralHomologyClassOf n k₁ h₁ + integralHomologyClassOf n k₂ h₂ =
      integralHomologyClassOf n (k₁ + k₂)
        (by rw [Preadditive.add_comp, h₁, h₂, add_zero]) := by
  have hz : (integralSingularChains X).liftCycles k₁ n ((ComplexShape.down ℕ).next_eq' (by rfl)) h₁ +
      (integralSingularChains X).liftCycles k₂ n ((ComplexShape.down ℕ).next_eq' (by rfl)) h₂ =
      (integralSingularChains X).liftCycles (k₁ + k₂) n ((ComplexShape.down ℕ).next_eq' (by rfl))
        (by rw [Preadditive.add_comp, h₁, h₂, add_zero]) := by
    apply (cancel_mono ((integralSingularChains X).iCycles (n + 1))).1
    rw [Preadditive.add_comp, HomologicalComplex.liftCycles_i, HomologicalComplex.liftCycles_i,
      HomologicalComplex.liftCycles_i]
  have hmain : ((integralSingularChains X).liftCycles k₁ n
        ((ComplexShape.down ℕ).next_eq' (by rfl)) h₁ ≫
        (integralSingularChains X).homologyπ (n + 1)) +
      ((integralSingularChains X).liftCycles k₂ n
        ((ComplexShape.down ℕ).next_eq' (by rfl)) h₂ ≫
        (integralSingularChains X).homologyπ (n + 1)) =
      ((integralSingularChains X).liftCycles (k₁ + k₂) n
        ((ComplexShape.down ℕ).next_eq' (by rfl))
        (by rw [Preadditive.add_comp, h₁, h₂, add_zero])) ≫
        (integralSingularChains X).homologyπ (n + 1) := by
    rw [← Preadditive.add_comp, hz]
  exact congrArg (fun k : integralSingularCoefficients ⟶ integralSingularHomology (n + 1) X =>
    k (ULift.up 1)) hmain

theorem integralHomologyClass_add (n : ℕ) (c d : (integralSingularChains X).X (n + 1))
    (hc : (integralSingularChains X).d (n + 1) n c = 0)
    (hd : (integralSingularChains X).d (n + 1) n d = 0) :
    integralHomologyClass n c hc + integralHomologyClass n d hd =
      integralHomologyClass n (c + d) (by
        change ((integralSingularChains X).d (n + 1) n).hom (c + d) = 0
        rw [map_add, hc, hd, add_zero]) := by
  unfold integralHomologyClass
  exact (integralHomologyClassOf_add n _ _ _ _).trans
    (integralHomologyClassOf_congr (integralChainHom_add (n + 1) c d).symm)

def squareSphereCollapse : C(Square, liftedHomotopySphere.{u} 1) where
  toFun t := ULift.up (cubeSphereProjection 1 t)
  continuous_toFun := continuous_uliftUp.comp (cubeSphereProjection 1).continuous

theorem squareSphereCollapse_boundary (t : Square) (ht : t ∈ Cube.boundary (Fin 2)) :
    squareSphereCollapse t = ULift.up (cubeSphereBasepoint 1) := by
  change ULift.up (cubeSphereProjection 1 t) = ULift.up (cubeSphereBasepoint 1)
  rw [cubeSphereProjection_boundary 1 t ht]

def squareSphereFundamentalChain : (integralSingularChains (liftedHomotopySphere.{u} 1)).X 2 :=
  singularChainImageGen 2 squareSphereCollapse squareFundamentalChain

theorem squareSphereFundamentalChain_boundary :
    (integralSingularChains (liftedHomotopySphere.{u} 1)).d 2 1
      squareSphereFundamentalChain = 0 :=
  singularChainImageGen_squareFundamentalChain_isCycle squareSphereCollapse _
    squareSphereCollapse_boundary

def squareSphereFundamentalClass : integralSingularHomology 2 (liftedHomotopySphere.{u} 1) :=
  integralHomologyClass 1 squareSphereFundamentalChain squareSphereFundamentalChain_boundary

theorem sphereHurewicz_squareSphereFundamentalClass_mk (x : X) (Γ : GenLoop (Fin 2) X x) :
    sphereHurewicz 1 x squareSphereFundamentalClass (Quotient.mk _ Γ) =
      integralHomologyClass 1 (singularChainImageGen 2 Γ.val squareFundamentalChain)
        (singularChainImageGen_squareFundamentalChain_isCycle Γ.val x
          (genLoop_boundary_property Γ)) := by
  rw [sphereHurewicz_mk, squareSphereFundamentalClass,
    integralSingularHomologyMap_integralHomologyClass]
  refine integralHomologyClass_congr ?_
  have hcomp : ((genLoopSphereHomeomorph 1 x Γ).val.comp (liftedHomotopySphereDown 1)).comp
      squareSphereCollapse = Γ.val := by
    ext t
    exact genLoopSphereHomeomorph_projection 1 x Γ t
  rw [integralSingularChainMap_apply_eq_singularChainImageGen 2
    ((genLoopSphereHomeomorph 1 x Γ).val.comp (liftedHomotopySphereDown 1))
    squareSphereFundamentalChain]
  change ((singularChainImageGen 2
        ((genLoopSphereHomeomorph 1 x Γ).val.comp (liftedHomotopySphereDown 1))).comp
      (singularChainImageGen 2 squareSphereCollapse)) squareFundamentalChain =
        singularChainImageGen 2 Γ.val squareFundamentalChain
  rw [← singularChainImageGen_comp 2 squareSphereCollapse
    ((genLoopSphereHomeomorph 1 x Γ).val.comp (liftedHomotopySphereDown 1)), hcomp]

theorem sphereHurewicz_squareSphereFundamentalClass_transAt (x : X)
    (Γ Δ : GenLoop (Fin 2) X x) :
    sphereHurewicz 1 x squareSphereFundamentalClass (Quotient.mk _ (GenLoop.transAt 0 Γ Δ)) =
      sphereHurewicz 1 x squareSphereFundamentalClass (Quotient.mk _ Γ) +
        sphereHurewicz 1 x squareSphereFundamentalClass (Quotient.mk _ Δ) := by
  obtain ⟨v, hv⟩ := (integralSingularHomology_vanishing_iff 1 Square).mp
    subsingleton_homology_two_square (squareFundamentalChain - squareLeftHalfChain -
      squareRightHalfChain + squareCornerChain) square_fold_identity
  have hpush : singularChainImageGen 2 (GenLoop.transAt 0 Γ Δ).val
      (squareFundamentalChain - squareLeftHalfChain - squareRightHalfChain + squareCornerChain) =
      (integralSingularChains X).d 3 2
        (singularChainImageGen 3 (GenLoop.transAt 0 Γ Δ).val v) := by
    rw [← hv, ← singularChainImageGen_d_eq 2 (GenLoop.transAt 0 Γ Δ).val v]
  have hLH : singularChainImageGen 2 (GenLoop.transAt 0 Γ Δ).val squareLeftHalfChain =
      singularChainImageGen 2 Γ.val squareFundamentalChain := by
    rw [← singularChainImageGen_squareLeftScaling_fundamentalChain]
    change (singularChainImageGen 2 (GenLoop.transAt 0 Γ Δ).val).comp
      (singularChainImageGen 2 squareLeftScaling) squareFundamentalChain =
        singularChainImageGen 2 Γ.val squareFundamentalChain
    rw [← singularChainImageGen_comp 2 squareLeftScaling (GenLoop.transAt 0 Γ Δ).val,
      squareLeftScaling_transAt]
  have hRH : singularChainImageGen 2 (GenLoop.transAt 0 Γ Δ).val squareRightHalfChain =
      singularChainImageGen 2 Δ.val squareFundamentalChain := by
    rw [← singularChainImageGen_squareRightScaling_fundamentalChain]
    change (singularChainImageGen 2 (GenLoop.transAt 0 Γ Δ).val).comp
      (singularChainImageGen 2 squareRightScaling) squareFundamentalChain =
        singularChainImageGen 2 Δ.val squareFundamentalChain
    rw [← singularChainImageGen_comp 2 squareRightScaling (GenLoop.transAt 0 Γ Δ).val,
      squareRightScaling_transAt]
  have hZ : singularChainImageGen 2 (GenLoop.transAt 0 Γ Δ).val
      (squareFundamentalChain - squareLeftHalfChain - squareRightHalfChain + squareCornerChain) =
      ((singularChainImageGen 2 (GenLoop.transAt 0 Γ Δ).val squareFundamentalChain -
          singularChainImageGen 2 (GenLoop.transAt 0 Γ Δ).val squareLeftHalfChain) -
          singularChainImageGen 2 (GenLoop.transAt 0 Γ Δ).val squareRightHalfChain) +
        singularChainImageGen 2 (GenLoop.transAt 0 Γ Δ).val squareCornerChain := by
    rw [map_add, map_sub, map_sub]
  have hchain : singularChainImageGen 2 (GenLoop.transAt 0 Γ Δ).val squareFundamentalChain =
      (singularChainImageGen 2 Γ.val squareFundamentalChain +
        singularChainImageGen 2 Δ.val squareFundamentalChain) +
      (integralSingularChains X).d 3 2
        (singularChainImageGen 3 (GenLoop.transAt 0 Γ Δ).val v) := by
    have h := hpush
    rw [hZ, hLH, hRH, genLoop_squareCornerChain_eq_zero (GenLoop.transAt 0 Γ Δ), add_zero] at h
    rw [← h]
    abel
  rw [sphereHurewicz_squareSphereFundamentalClass_mk x (GenLoop.transAt 0 Γ Δ),
    sphereHurewicz_squareSphereFundamentalClass_mk x Γ,
    sphereHurewicz_squareSphereFundamentalClass_mk x Δ]
  have h1 := integralHomologyClass_eq_of_eq_add_boundary 1
    (singularChainImageGen 2 (GenLoop.transAt 0 Γ Δ).val squareFundamentalChain)
    (singularChainImageGen 2 Γ.val squareFundamentalChain +
      singularChainImageGen 2 Δ.val squareFundamentalChain)
    (singularChainImageGen 3 (GenLoop.transAt 0 Γ Δ).val v)
    (singularChainImageGen_squareFundamentalChain_isCycle _ x
      (genLoop_boundary_property (GenLoop.transAt 0 Γ Δ)))
    (by
      change ((integralSingularChains X).d 2 1).hom
        (singularChainImageGen 2 Γ.val squareFundamentalChain +
          singularChainImageGen 2 Δ.val squareFundamentalChain) = 0
      rw [map_add, singularChainImageGen_squareFundamentalChain_isCycle Γ.val x
          (genLoop_boundary_property Γ),
        singularChainImageGen_squareFundamentalChain_isCycle Δ.val x
          (genLoop_boundary_property Δ),
        add_zero])
    hchain
  have h2 := integralHomologyClass_add 1
    (singularChainImageGen 2 Γ.val squareFundamentalChain)
    (singularChainImageGen 2 Δ.val squareFundamentalChain)
    (singularChainImageGen_squareFundamentalChain_isCycle Γ.val x (genLoop_boundary_property Γ))
    (singularChainImageGen_squareFundamentalChain_isCycle Δ.val x (genLoop_boundary_property Δ))
  rw [h1]
  exact h2.symm

theorem hurewicz_two_mul_squareSphereFundamentalClass (x : X) :
    ∀ a b : HomotopyGroup (Fin 2) X x,
      sphereHurewicz 1 x squareSphereFundamentalClass (a * b) =
        sphereHurewicz 1 x squareSphereFundamentalClass a +
          sphereHurewicz 1 x squareSphereFundamentalClass b := by
  intro a b
  induction a using Quotient.inductionOn with
  | h Δ =>
    induction b using Quotient.inductionOn with
    | h Γ =>
      have hm : ((· * ·) : _ → _ → HomotopyGroup (Fin 2) X x) ⟦Δ⟧ ⟦Γ⟧ =
          (⟦GenLoop.transAt 0 Γ Δ⟧ : HomotopyGroup (Fin 2) X x) :=
        HomotopyGroup.mul_spec (i := (0 : Fin 2)) (p := Δ) (q := Γ)
      exact (congrArg (sphereHurewicz 1 x squareSphereFundamentalClass) hm).trans
        ((sphereHurewicz_squareSphereFundamentalClass_transAt x Γ Δ).trans (add_comm _ _))

theorem hurewicz_two_mul (x : X)
    (hgen : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass)
    (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (hc : IsSphereHomologyGenerator 1 c) :
    ∀ a b : HomotopyGroup (Fin 2) X x,
      sphereHurewicz 1 x c (a * b) = sphereHurewicz 1 x c a + sphereHurewicz 1 x c b := by
  intro a b
  rcases IsSphereHomologyGenerator.eq_or_eq_neg.{u} 1 hc hgen with h | h
  · rw [h]
    exact hurewicz_two_mul_squareSphereFundamentalClass x a b
  · rw [h]
    have hneg : sphereHurewicz 1 x (-squareSphereFundamentalClass) =
        fun a => -sphereHurewicz 1 x squareSphereFundamentalClass a := by
      funext a
      simpa using sphereHurewicz_zsmul 1 (-1) x squareSphereFundamentalClass a
    rw [hneg]
    change -sphereHurewicz 1 x squareSphereFundamentalClass (a * b) =
      -sphereHurewicz 1 x squareSphereFundamentalClass a +
        -sphereHurewicz 1 x squareSphereFundamentalClass b
    rw [hurewicz_two_mul_squareSphereFundamentalClass x a b]
    abel

end DifferentialGeometry.Topology
