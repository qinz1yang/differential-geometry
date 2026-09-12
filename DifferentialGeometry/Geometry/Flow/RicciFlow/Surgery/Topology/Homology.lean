import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Background
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChartSimplexBlend
import DifferentialGeometry.Topology.Homology.LiftedSphere
import DifferentialGeometry.Topology.Homology.ContractibleCoverChainEvaluation
import DifferentialGeometry.Topology.Homology.EuclideanLocalTop
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Bounded

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Bundle Manifold Set
open scoped Simplicial Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u


def integralCoefficients : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)


def integralChainsFunctor : TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  (singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj integralCoefficients


def integralHomologyFunctor (n : ℕ) : TopCat.{u} ⥤ ModuleCat.{u} ℤ :=
  (singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj integralCoefficients

variable (X : Type u) [TopologicalSpace X]

abbrev IntegralChains := integralChainsFunctor.obj (TopCat.of X)

abbrev IntegralHomology (n : ℕ) := (integralHomologyFunctor n).obj (TopCat.of X)


def subspaceInclusion (A : Set X) : TopCat.of A ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩


def subspaceChainInclusion (A : Set X) : IntegralChains A ⟶ IntegralChains X :=
  integralChainsFunctor.map (subspaceInclusion X A)

abbrev RelativeIntegralChains (A : Set X) : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  cokernel (subspaceChainInclusion X A)


abbrev RelativeIntegralHomology (A : Set X) (n : ℕ) : ModuleCat.{u} ℤ :=
  (RelativeIntegralChains X A).homology n


def absoluteToRelative (A : Set X) (n : ℕ) :
    IntegralHomology X n ⟶ RelativeIntegralHomology X A n :=
  HomologicalComplex.homologyMap (cokernel.π (subspaceChainInclusion X A)) n


abbrev LocalIntegralHomology (x : X) (n : ℕ) :=
  RelativeIntegralHomology X ({x}ᶜ) n

variable {X} {Y : Type u} [TopologicalSpace Y]


def integralHomologyMap (n : ℕ) (f : C(X, Y)) :
    IntegralHomology X n ⟶ IntegralHomology Y n :=
  (integralHomologyFunctor n).map (TopCat.ofHom f)


theorem integralHomologyMap_eq_of_homotopic {f g : C(X, Y)}
    (H : ContinuousMap.Homotopic f g) :
    integralHomologyMap 3 f = integralHomologyMap 3 g := by
  exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
    (C := ModuleCat.{u} ℤ) (f := TopCat.ofHom f) (g := TopCat.ofHom g)
    (Classical.choice H) integralCoefficients 3

def pairSubspaceMap (f : C(X, Y)) (A : Set X) (B : Set Y)
    (hf : Set.MapsTo f A B) : TopCat.of A ⟶ TopCat.of B :=
  TopCat.ofHom ⟨fun x => ⟨f x, hf x.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩


theorem pair_chain_square (f : C(X, Y)) (A : Set X) (B : Set Y)
    (hf : Set.MapsTo f A B) :
    subspaceChainInclusion X A ≫ integralChainsFunctor.map (TopCat.ofHom f) =
      integralChainsFunctor.map (pairSubspaceMap f A B hf) ≫ subspaceChainInclusion Y B := by
  change integralChainsFunctor.map (subspaceInclusion X A) ≫ _ =
    _ ≫ integralChainsFunctor.map (subspaceInclusion Y B)
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl


def relativeIntegralChainMap (f : C(X, Y)) (A : Set X) (B : Set Y)
    (hf : Set.MapsTo f A B) : RelativeIntegralChains X A ⟶ RelativeIntegralChains Y B :=
  cokernel.map (subspaceChainInclusion X A) (subspaceChainInclusion Y B)
    (integralChainsFunctor.map (pairSubspaceMap f A B hf))
    (integralChainsFunctor.map (TopCat.ofHom f)) (pair_chain_square f A B hf)


def relativeIntegralHomologyMap (n : ℕ) (f : C(X, Y)) (A : Set X) (B : Set Y)
    (hf : Set.MapsTo f A B) :
    RelativeIntegralHomology X A n ⟶ RelativeIntegralHomology Y B n :=
  HomologicalComplex.homologyMap (relativeIntegralChainMap f A B hf) n


theorem absoluteToRelative_naturality (n : ℕ) (f : C(X, Y))
    (A : Set X) (B : Set Y) (hf : Set.MapsTo f A B) :
    absoluteToRelative X A n ≫ relativeIntegralHomologyMap n f A B hf =
      integralHomologyMap n f ≫ absoluteToRelative Y B n := by
  change HomologicalComplex.homologyMap (cokernel.π (subspaceChainInclusion X A)) n ≫
      HomologicalComplex.homologyMap (relativeIntegralChainMap f A B hf) n =
    HomologicalComplex.homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) n ≫
      HomologicalComplex.homologyMap (cokernel.π (subspaceChainInclusion Y B)) n
  calc
    _ = HomologicalComplex.homologyMap
        (cokernel.π (subspaceChainInclusion X A) ≫ relativeIntegralChainMap f A B hf) n :=
      (HomologicalComplex.homologyMap_comp _ _ n).symm
    _ = HomologicalComplex.homologyMap
        (integralChainsFunctor.map (TopCat.ofHom f) ≫ cokernel.π (subspaceChainInclusion Y B)) n :=
      congrArg (fun φ : IntegralChains X ⟶ RelativeIntegralChains Y B =>
        HomologicalComplex.homologyMap φ n) (cokernel.π_desc _ _ _)
    _ = _ := HomologicalComplex.homologyMap_comp _ _ n


theorem absoluteToRelative_injective_of_subsingleton (A : Set X) (n : ℕ)
    (h : Subsingleton (IntegralHomology A n)) :
    Function.Injective (absoluteToRelative X A n) :=
  DifferentialGeometry.Topology.integralAbsoluteToRelative_injective_of_subsingleton n A h


theorem absoluteToRelative_compl_singleton_injective_of_subsingleton (x : X)
    (h : Subsingleton (IntegralHomology ({x}ᶜ : Set X) 3)) :
    Function.Injective (absoluteToRelative X ({x}ᶜ) 3) :=
  absoluteToRelative_injective_of_subsingleton ({x}ᶜ) 3 h


def singularSimplexChain {n : ℕ} (f : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    integralCoefficients ⟶ (IntegralChains X).X n :=
  (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
    ((TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋n⦌)).symm f)


variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M]

private theorem orientation_map_comp_simplex
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module ℝ A] [Module ℝ B] [Module ℝ C]
    (a : A ≃ₗ[ℝ] B) (b : B ≃ₗ[ℝ] C) (o : Orientation ℝ A (Fin 3)) :
    Orientation.map (Fin 3) b (Orientation.map (Fin 3) a o) =
      Orientation.map (Fin 3) (a.trans b) o := by
  induction o using Quotient.inductionOn with
  | h o => rfl


private theorem exists_orientation_adjustment (o : Orientation ℝ ThreeSpace (Fin 3)) :
    ∃ L : ThreeSpace ≃L[ℝ] ThreeSpace,
      Orientation.map (Fin 3) L.toLinearEquiv o = standardThreeOrientation := by
  let b₀ := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  let b := b₀.adjustToOrientation o
  let L := (b.equiv b₀ (Equiv.refl (Fin 3))).toContinuousLinearEquiv
  refine ⟨L, ?_⟩
  have hb : b.orientation = o := b₀.orientation_adjustToOrientation o
  have he : b.map L.toLinearEquiv = b₀ := by
    change b.map (b.equiv b₀ (Equiv.refl (Fin 3))) = b₀
    simp
  rw [← hb, ← Module.Basis.orientation_map, he]
  rfl


private theorem exists_tetrahedron_radius (U : Set ThreeSpace) (hU : IsOpen U)
    (y : ThreeSpace) (hy : y ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ∀ q : stdSimplex ℝ (Fin 4),
      y + r • positiveTetrahedron q ∈ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU y hy
  obtain ⟨R, hR, hbound⟩ :=
    (isCompact_range positiveTetrahedron.continuous).isBounded.exists_pos_norm_le
  let r : ℝ := ε / (R + 1)
  have hden : 0 < R + 1 := by linarith
  have hr : 0 < r := div_pos hε hden
  refine ⟨r, hr, ?_⟩
  intro q
  apply hball
  have hnorm : ‖positiveTetrahedron q‖ ≤ R := hbound _ ⟨q, rfl⟩
  have hlt : r * ‖positiveTetrahedron q‖ < ε := calc
    r * ‖positiveTetrahedron q‖ ≤ r * R := mul_le_mul_of_nonneg_left hnorm hr.le
    _ < r * (R + 1) := mul_lt_mul_of_pos_left (by linarith) hr
    _ = ε := div_mul_cancel₀ ε (ne_of_gt hden)
  simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
    norm_smul, Real.norm_eq_abs, abs_of_pos hr] using hlt

theorem exists_orientedChartSimplex (o : TangentOrientationSection M) (x : M) :
    Nonempty (OrientedChartSimplex o x) := by
  let e₀ := chartAt ThreeSpace x
  have hx₀ : x ∈ e₀.source := mem_chart_source ThreeSpace x
  have hd₀ : MDifferentiableAt ThreeModel ThreeModel e₀ x := by
    have hd := mdifferentiableAt_extChartAt (I := ThreeModel) hx₀
    exact hd
  obtain ⟨Dnative, hD⟩ := isInvertible_mfderiv_extChartAt (I := ThreeModel)
    (mem_extChartAt_source (I := ThreeModel) x)
  let D : TangentSpace ThreeModel x ≃L[ℝ] ThreeSpace :=
    Dnative.trans (NormedSpace.fromTangentSpace (extChartAt ThreeModel x x))
  have hD₀ : D.toContinuousLinearMap =
      mfderiv ThreeModel ThreeModel e₀ x := hD
  obtain ⟨L, hL⟩ := exists_orientation_adjustment
    (Orientation.map (Fin 3) D.toLinearEquiv (o.orientation x))
  let e : OpenPartialHomeomorph M ThreeSpace :=
    e₀.trans L.toHomeomorph.toOpenPartialHomeomorph
  have hx : x ∈ e.source := by
    change x ∈ e₀.source ∩ e₀ ⁻¹' Set.univ
    exact ⟨hx₀, Set.mem_univ _⟩
  have hLd : HasMFDerivAt ThreeModel ThreeModel L (e₀ x)
      (L : ThreeSpace →L[ℝ] ThreeSpace) :=
    L.toContinuousLinearMap.hasFDerivAt.hasMFDerivAt
  have hd : MDifferentiableAt ThreeModel ThreeModel e x :=
    hLd.mdifferentiableAt.comp x hd₀
  have hderiv : mfderiv ThreeModel ThreeModel e x =
      (L : ThreeSpace →L[ℝ] ThreeSpace).comp D.toContinuousLinearMap := by
    have h := mfderiv_comp x hLd.mdifferentiableAt hd₀
    change mfderiv ThreeModel ThreeModel e x = _ at h
    rw [hLd.mfderiv, ← hD₀] at h
    exact h
  have hbij : Function.Bijective (mfderiv ThreeModel ThreeModel e x) := by
    rw [hderiv]
    exact L.bijective.comp D.bijective
  have hlinear :
      LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel e x).toLinearMap hbij =
        D.toLinearEquiv.trans L.toLinearEquiv := by
    ext v
    exact DFunLike.congr_fun hderiv v
  have hpositive : Orientation.map (Fin 3)
      (LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel e x).toLinearMap hbij)
        (o.orientation x) = standardThreeOrientation := by
    exact (congrArg (fun f => Orientation.map (Fin 3) f (o.orientation x)) hlinear).trans
      ((orientation_map_comp_simplex D.toLinearEquiv L.toLinearEquiv
        (o.orientation x)).symm.trans hL)
  obtain ⟨r, hr, hins⟩ := exists_tetrahedron_radius e.target e.open_target
    (e x) (e.map_source hx)
  exact ⟨{
    chart := e
    center_mem := hx
    differentiableAt := hd
    derivative_bijective := hbij
    positive := hpositive
    radius := r
    radius_pos := hr
    simplex_inside := hins }⟩

def OrientedChartSimplex.relativeChain {o : TangentOrientationSection M} {x : M}
    (S : OrientedChartSimplex o x) :
    integralCoefficients ⟶ (RelativeIntegralChains M ({x}ᶜ)).X 3 :=
  singularSimplexChain S.simplex ≫ (cokernel.π (subspaceChainInclusion M ({x}ᶜ))).f 3

private def orientedSimplexFace (i : Fin 4) :
    C(stdSimplex ℝ (Fin 3), stdSimplex ℝ (Fin 4)) :=
  ⟨stdSimplex.map (SimplexCategory.δ i).toOrderHom,
    stdSimplex.continuous_map (SimplexCategory.δ i).toOrderHom⟩

private theorem orientedSimplexFace_zero (i : Fin 4) (q : stdSimplex ℝ (Fin 3)) :
    (orientedSimplexFace i q).val i = 0 := by
  change FunOnFinite.linearMap ℝ ℝ i.succAbove (q : Fin 3 → ℝ) i = 0
  rw [FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_zero
  intro j hj
  exact False.elim (Fin.succAbove_ne i j (Finset.mem_filter.mp hj).2)

variable {o : TangentOrientationSection M} {x : M}

private theorem orientedSimplex_face_ne_center (S : OrientedChartSimplex o x)
    (i : Fin 4) (q : stdSimplex ℝ (Fin 3)) : S.simplex (orientedSimplexFace i q) ≠ x := by
  intro heq
  have hcoord := positiveTetrahedron_face_ne_zero (orientedSimplexFace i q) i
    (orientedSimplexFace_zero i q)
  have he := congrArg S.chart heq
  change S.chart (S.chart.symm
    (S.chart x + S.radius • positiveTetrahedron (orientedSimplexFace i q))) = S.chart x at he
  rw [S.chart.right_inv (S.simplex_inside (orientedSimplexFace i q))] at he
  have hs : S.radius • positiveTetrahedron (orientedSimplexFace i q) = 0 := by
    have h := congrArg (fun y : ThreeSpace => y - S.chart x) he
    simpa only [add_sub_cancel_left, sub_self] using h
  exact hcoord ((smul_eq_zero.mp hs).resolve_left (ne_of_gt S.radius_pos))

private def orientedSimplex_puncturedFace (S : OrientedChartSimplex o x) (i : Fin 4) :
    C(stdSimplex ℝ (Fin 3), ({x}ᶜ : Set M)) :=
  ⟨fun q => ⟨S.simplex (orientedSimplexFace i q), orientedSimplex_face_ne_center S i q⟩,
    (S.simplex.continuous.comp (orientedSimplexFace i).continuous).subtype_mk
      (fun q => orientedSimplex_face_ne_center S i q)⟩

private theorem orientedSimplex_face_chain (S : OrientedChartSimplex o x) (i : Fin 4) :
    singularSimplexChain (orientedSimplex_puncturedFace S i) ≫
      (subspaceChainInclusion M ({x}ᶜ)).f 2 =
        singularSimplexChain (S.simplex.comp (orientedSimplexFace i)) := by
  exact SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of ({x}ᶜ : Set M)))
    (TopCat.toSSet.obj (TopCat.of M))
    (TopCat.toSSet.map (subspaceInclusion M ({x}ᶜ))) integralCoefficients
    ((TopCat.toSSetObjEquiv (TopCat.of ({x}ᶜ : Set M)) (.op ⦋2⦌)).symm
      (orientedSimplex_puncturedFace S i))

private theorem orientedSimplex_chain_boundary (S : OrientedChartSimplex o x) :
    singularSimplexChain S.simplex ≫ (IntegralChains M).d 3 2 =
      ∑ i : Fin 4, (-1 : ℤ) ^ i.val •
        singularSimplexChain (S.simplex.comp (orientedSimplexFace i)) := by
  exact (TopCat.toSSet.obj (TopCat.of M)).ιChainComplex_d (R := integralCoefficients)
    ((TopCat.toSSetObjEquiv (TopCat.of M) (.op ⦋3⦌)).symm S.simplex)


theorem OrientedChartSimplex.relativeChain_boundary {o : TangentOrientationSection M} {x : M}
    (S : OrientedChartSimplex o x) :
    S.relativeChain ≫ (RelativeIntegralChains M ({x}ᶜ)).d 3 2 = 0 := by
  let quotientMap := cokernel.π (subspaceChainInclusion M ({x}ᶜ))
  have hπ : (subspaceChainInclusion M ({x}ᶜ)).f 2 ≫ quotientMap.f 2 = 0 := by
    exact congrArg (fun f => f.f 2) (cokernel.condition (subspaceChainInclusion M ({x}ᶜ)))
  have hf (i : Fin 4) :
      singularSimplexChain (S.simplex.comp (orientedSimplexFace i)) ≫ quotientMap.f 2 = 0 := by
    rw [← orientedSimplex_face_chain S i, Category.assoc, hπ, comp_zero]
  unfold OrientedChartSimplex.relativeChain
  change (singularSimplexChain S.simplex ≫ quotientMap.f 3) ≫ _ = 0
  rw [Category.assoc, quotientMap.comm 3 2, ← Category.assoc, orientedSimplex_chain_boundary]
  simp only [Preadditive.sum_comp, Linear.smul_comp, hf, smul_zero, Finset.sum_const_zero]


def OrientedChartSimplex.localClass {o : TangentOrientationSection M} {x : M}
    (S : OrientedChartSimplex o x) : LocalIntegralHomology M x 3 :=
  ((RelativeIntegralChains M ({x}ᶜ)).liftCycles S.relativeChain 2
    ((ComplexShape.down ℕ).next_eq' (by rfl))
    S.relativeChain_boundary ≫ (RelativeIntegralChains M ({x}ᶜ)).homologyπ 3) (ULift.up 1)

private abbrev RelativePrismVertex := Fin 2 × Fin 4
private def relativePrismCells : Fin 4 → Fin 5 → RelativePrismVertex :=
  ![![(0, 0), (1, 0), (1, 1), (1, 2), (1, 3)], ![(0, 0), (0, 1), (1, 1), (1, 2), (1, 3)], ![(0, 0), (0, 1), (0, 2), (1, 2), (1, 3)], ![(0, 0), (0, 1), (0, 2), (0, 3), (1, 3)]]
private def relativePrismSides : Fin 12 → Fin 4 → RelativePrismVertex :=
  ![![(0, 0), (1, 0), (1, 2), (1, 3)], ![(0, 0), (1, 0), (1, 1), (1, 3)], ![(0, 0), (1, 0), (1, 1), (1, 2)], ![(0, 1), (1, 1), (1, 2), (1, 3)], ![(0, 0), (0, 1), (1, 1), (1, 3)], ![(0, 0), (0, 1), (1, 1), (1, 2)], ![(0, 1), (0, 2), (1, 2), (1, 3)], ![(0, 0), (0, 2), (1, 2), (1, 3)], ![(0, 0), (0, 1), (0, 2), (1, 2)], ![(0, 1), (0, 2), (0, 3), (1, 3)], ![(0, 0), (0, 2), (0, 3), (1, 3)], ![(0, 0), (0, 1), (0, 3), (1, 3)]]
private def relativePrismSideSigns : Fin 12 → ℤ := ![1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1]
private def relativePrismEnd (b : Fin 2) : Fin 4 → RelativePrismVertex := fun j => (b, j)

private def relativePrismFaces : Fin 4 → Fin 5 → Fin 4 → RelativePrismVertex :=
  ![![![(1, 0), (1, 1), (1, 2), (1, 3)], ![(0, 0), (1, 1), (1, 2), (1, 3)], ![(0, 0), (1, 0), (1, 2), (1, 3)], ![(0, 0), (1, 0), (1, 1), (1, 3)], ![(0, 0), (1, 0), (1, 1), (1, 2)]],
    ![![(0, 1), (1, 1), (1, 2), (1, 3)], ![(0, 0), (1, 1), (1, 2), (1, 3)], ![(0, 0), (0, 1), (1, 2), (1, 3)], ![(0, 0), (0, 1), (1, 1), (1, 3)], ![(0, 0), (0, 1), (1, 1), (1, 2)]],
    ![![(0, 1), (0, 2), (1, 2), (1, 3)], ![(0, 0), (0, 2), (1, 2), (1, 3)], ![(0, 0), (0, 1), (1, 2), (1, 3)], ![(0, 0), (0, 1), (0, 2), (1, 3)], ![(0, 0), (0, 1), (0, 2), (1, 2)]],
    ![![(0, 1), (0, 2), (0, 3), (1, 3)], ![(0, 0), (0, 2), (0, 3), (1, 3)], ![(0, 0), (0, 1), (0, 3), (1, 3)], ![(0, 0), (0, 1), (0, 2), (1, 3)], ![(0, 0), (0, 1), (0, 2), (0, 3)]]]

private theorem relativePrismFaces_eq (k : Fin 4) (i : Fin 5) :
    (fun j => relativePrismCells k (i.succAbove j)) = relativePrismFaces k i := by
  fin_cases k <;> fin_cases i <;> funext j <;> fin_cases j <;> rfl

private theorem relativePrismEnd_eq (b : Fin 2) :
    relativePrismEnd b = ![(b, 0), (b, 1), (b, 2), (b, 3)] := by
  funext j
  fin_cases j <;> rfl

private theorem relativePrism_finite_boundary {A : Type*} [AddCommGroup A]
    (F : (Fin 4 → RelativePrismVertex) → A) :
    (∑ k : Fin 4, (-1 : ℤ) ^ k.val •
      ∑ i : Fin 5, (-1 : ℤ) ^ i.val •
        F (fun j => relativePrismCells k (i.succAbove j))) =
      F (relativePrismEnd 1) - F (relativePrismEnd 0) +
        ∑ k : Fin 12, relativePrismSideSigns k • F (relativePrismSides k) := by
  simp only [relativePrismFaces_eq, relativePrismEnd_eq]
  norm_num [relativePrismFaces, relativePrismSides, relativePrismSideSigns,
    Fin.sum_univ_succ]
  abel

private def relativePrismAffine {n : ℕ} (v : Fin (n + 1) → RelativePrismVertex) :
    C(stdSimplex ℝ (Fin (n + 1)), unitInterval × stdSimplex ℝ (Fin 4)) where
  toFun q :=
    (⟨(stdSimplex.map (fun j => (v j).1) q).val 1,
      (stdSimplex.map (fun j => (v j).1) q).property.1 1,
      stdSimplex.le_one _ _⟩, stdSimplex.map (fun j => (v j).2) q)
  continuous_toFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact (continuous_apply 1).comp
        (continuous_subtype_val.comp (stdSimplex.continuous_map (fun j => (v j).1)))
    · exact stdSimplex.continuous_map (fun j => (v j).2)

private def relativePrismFace (n : ℕ) (i : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 2))) :=
  ⟨stdSimplex.map (SimplexCategory.δ i).toOrderHom,
    stdSimplex.continuous_map (SimplexCategory.δ i).toOrderHom⟩

private theorem relativePrismAffine_face {n : ℕ}
    (v : Fin (n + 2) → RelativePrismVertex) (i : Fin (n + 2)) :
    (relativePrismAffine v).comp (relativePrismFace n i) =
      relativePrismAffine (fun j => v (i.succAbove j)) := by
  apply ContinuousMap.ext
  intro q
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun s : stdSimplex ℝ (Fin 2) => s.val 1)
      (stdSimplex.map_comp_apply i.succAbove (fun j => (v j).1) q)
  · exact stdSimplex.map_comp_apply i.succAbove (fun j => (v j).2) q

private theorem relativePrismAffine_end (b : Fin 2) (q : stdSimplex ℝ (Fin 4)) :
    relativePrismAffine (relativePrismEnd b) q = (⟨b.val, by
      constructor
      · exact Nat.cast_nonneg _
      · exact_mod_cast (show b.val ≤ 1 by omega)⟩, q) := by
  apply Prod.ext
  · apply Subtype.ext
    change FunOnFinite.linearMap ℝ ℝ (fun _ : Fin 4 => b) q.val 1 = (b.val : ℝ)
    fin_cases b
    · simp [FunOnFinite.linearMap_apply_apply]
    · simpa [FunOnFinite.linearMap_apply_apply] using q.property.2
  · exact stdSimplex.map_id_apply q

private theorem relativePrism_side_missing (k : Fin 12) :
    ∃ i : Fin 4, ∀ j : Fin 4, (relativePrismSides k j).2 ≠ i := by
  fin_cases k <;> decide

private theorem relativePrism_side_boundary (k : Fin 12)
    (q : stdSimplex ℝ (Fin 4)) :
    ∃ i : Fin 4, (relativePrismAffine (relativePrismSides k) q).2.val i = 0 := by
  obtain ⟨i, hi⟩ := relativePrism_side_missing k
  refine ⟨i, ?_⟩
  change FunOnFinite.linearMap ℝ ℝ (fun j => (relativePrismSides k j).2) q.val i = 0
  rw [FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_zero
  intro j hj
  exact False.elim (hi j (Finset.mem_filter.mp hj).2)

private theorem relativePrism_singular_boundary {X : Type u} [TopologicalSpace X] {n : ℕ}
    (s : C(stdSimplex ℝ (Fin (n + 2)), X)) :
    singularSimplexChain s ≫ (IntegralChains X).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        singularSimplexChain (s.comp (relativePrismFace n i)) := by
  exact (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex_d (R := integralCoefficients)
    ((TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋n + 1⦌)).symm s)

private def relativePrismChain {X : Type u} [TopologicalSpace X]
    {f g : C(stdSimplex ℝ (Fin 4), X)} (H : f.Homotopy g) :
    integralCoefficients ⟶ (IntegralChains X).X 4 :=
  ∑ k : Fin 4, (-1 : ℤ) ^ k.val •
    singularSimplexChain (H.toContinuousMap.comp (relativePrismAffine (relativePrismCells k)))

private theorem relativePrism_end_maps {X : Type u} [TopologicalSpace X]
    {f g : C(stdSimplex ℝ (Fin 4), X)} (H : f.Homotopy g) :
    H.toContinuousMap.comp (relativePrismAffine (relativePrismEnd 0)) = f ∧
      H.toContinuousMap.comp (relativePrismAffine (relativePrismEnd 1)) = g := by
  constructor
  · ext q
    change H (relativePrismAffine (relativePrismEnd 0) q) = f q
    have he : relativePrismAffine (relativePrismEnd 0) q = (0, q) := by
      convert relativePrismAffine_end 0 q using 1
      norm_num
    rw [he]
    exact H.map_zero_left q
  · ext q
    change H (relativePrismAffine (relativePrismEnd 1) q) = g q
    have he : relativePrismAffine (relativePrismEnd 1) q = (1, q) := by
      convert relativePrismAffine_end 1 q using 1
      norm_num
    rw [he]
    exact H.map_one_left q

private theorem relativePrismChain_boundary {X : Type u} [TopologicalSpace X]
    {f g : C(stdSimplex ℝ (Fin 4), X)} (H : f.Homotopy g) :
    relativePrismChain H ≫ (IntegralChains X).d 4 3 =
      singularSimplexChain g - singularSimplexChain f +
        ∑ k : Fin 12, relativePrismSideSigns k •
          singularSimplexChain (H.toContinuousMap.comp (relativePrismAffine (relativePrismSides k))) := by
  simp only [relativePrismChain, Preadditive.sum_comp, Linear.smul_comp,
    relativePrism_singular_boundary, ContinuousMap.comp_assoc, relativePrismAffine_face]
  have h := relativePrism_finite_boundary
    (fun v => singularSimplexChain (H.toContinuousMap.comp (relativePrismAffine v)))
  simpa only [(relativePrism_end_maps H).1, (relativePrism_end_maps H).2] using h

private def relativePrism_puncturedSide {X : Type u} [TopologicalSpace X] (x : X)
    {f g : C(stdSimplex ℝ (Fin 4), X)} (H : f.Homotopy g)
    (hside : ∀ (t : unitInterval) (q : stdSimplex ℝ (Fin 4)),
      (∃ i : Fin 4, q.val i = 0) → H (t, q) ≠ x) (k : Fin 12) :
    C(stdSimplex ℝ (Fin 4), ({x}ᶜ : Set X)) :=
  ⟨fun q => ⟨H (relativePrismAffine (relativePrismSides k) q),
    hside _ _ (relativePrism_side_boundary k q)⟩,
    (H.continuous.comp (relativePrismAffine (relativePrismSides k)).continuous).subtype_mk
      (fun q => hside _ _ (relativePrism_side_boundary k q))⟩

private theorem relativePrism_side_zero {X : Type u} [TopologicalSpace X] (x : X)
    {f g : C(stdSimplex ℝ (Fin 4), X)} (H : f.Homotopy g)
    (hside : ∀ (t : unitInterval) (q : stdSimplex ℝ (Fin 4)),
      (∃ i : Fin 4, q.val i = 0) → H (t, q) ≠ x) (k : Fin 12) :
    singularSimplexChain (H.toContinuousMap.comp (relativePrismAffine (relativePrismSides k))) ≫
      (cokernel.π (subspaceChainInclusion X ({x}ᶜ))).f 3 = 0 := by
  have hf : singularSimplexChain (relativePrism_puncturedSide x H hside k) ≫
      (subspaceChainInclusion X ({x}ᶜ)).f 3 =
        singularSimplexChain (H.toContinuousMap.comp (relativePrismAffine (relativePrismSides k))) :=
    SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of ({x}ᶜ : Set X)))
      (TopCat.toSSet.obj (TopCat.of X))
      (TopCat.toSSet.map (subspaceInclusion X ({x}ᶜ))) integralCoefficients
      ((TopCat.toSSetObjEquiv (TopCat.of ({x}ᶜ : Set X)) (.op ⦋3⦌)).symm
        (relativePrism_puncturedSide x H hside k))
  have hzero : (subspaceChainInclusion X ({x}ᶜ)).f 3 ≫
      (cokernel.π (subspaceChainInclusion X ({x}ᶜ))).f 3 = 0 :=
    congrArg (fun φ => φ.f 3) (cokernel.condition (subspaceChainInclusion X ({x}ᶜ)))
  rw [← hf, Category.assoc, hzero, comp_zero]

theorem OrientedChartSimplex.localClass_eq_of_simplexFamily
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] {o : TangentOrientationSection M} {x : M}
    (S T : OrientedChartSimplex o x) (H : S.simplex.Homotopy T.simplex)
    (hside : ∀ (t : unitInterval) (q : stdSimplex ℝ (Fin 4)),
      (∃ i : Fin 4, q.val i = 0) → H (t, q) ≠ x) :
    S.localClass = T.localClass := by
  let K := RelativeIntegralChains M ({x}ᶜ)
  let quotientMap := cokernel.π (subspaceChainInclusion M ({x}ᶜ))
  let W : integralCoefficients ⟶ K.X 4 := -(relativePrismChain H ≫ quotientMap.f 4)
  have hb : S.relativeChain - T.relativeChain = W ≫ K.d 4 3 := by
    have h := congrArg (fun φ : integralCoefficients ⟶ (IntegralChains M).X 3 =>
      φ ≫ quotientMap.f 3) (relativePrismChain_boundary H)
    have hside' (k : Fin 12) :
        singularSimplexChain (H.toContinuousMap.comp
          (relativePrismAffine (relativePrismSides k))) ≫ quotientMap.f 3 = 0 :=
      relativePrism_side_zero x H hside k
    simp only [Preadditive.add_comp, Preadditive.sub_comp, Preadditive.sum_comp,
      Linear.smul_comp, hside', smul_zero, Finset.sum_const_zero, add_zero] at h
    have hd := quotientMap.comm 4 3
    dsimp [W]
    rw [Preadditive.neg_comp, Category.assoc, hd, ← Category.assoc, h]
    change S.relativeChain - T.relativeChain = -(T.relativeChain - S.relativeChain)
    abel
  let z (R : OrientedChartSimplex o x) : integralCoefficients ⟶ K.cycles 3 :=
    K.liftCycles R.relativeChain 2 ((ComplexShape.down ℕ).next_eq' (by rfl))
      R.relativeChain_boundary
  have hz : z S - z T =
      K.liftCycles (S.relativeChain - T.relativeChain) 2
        ((ComplexShape.down ℕ).next_eq' (by rfl)) (by
          rw [Preadditive.sub_comp, S.relativeChain_boundary, T.relativeChain_boundary, sub_self]) := by
    apply (cancel_mono (K.iCycles 3)).mp
    simp only [Preadditive.sub_comp, HomologicalComplex.liftCycles_i, z]
  have hzero : (z S - z T) ≫ K.homologyπ 3 = 0 := by
    rw [hz]
    exact K.liftCycles_homologyπ_eq_zero_of_boundary _ 2
      ((ComplexShape.down ℕ).next_eq' (by rfl)) W hb
  have he : z S ≫ K.homologyπ 3 = z T ≫ K.homologyπ 3 := by
    simpa only [Preadditive.sub_comp, sub_eq_zero] using hzero
  exact congrArg (fun φ : integralCoefficients ⟶ LocalIntegralHomology M x 3 =>
    φ (ULift.up 1)) he

private def tetrahedronContract (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (q : stdSimplex ℝ (Fin 4)) : stdSimplex ℝ (Fin 4) :=
  ⟨fun j => a * q.val j + (1 - a) / 4, by
    constructor
    · intro j
      exact add_nonneg (mul_nonneg ha.1 (q.property.1 j))
        (div_nonneg (sub_nonneg.mpr ha.2) (by norm_num))
    · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, q.property.2,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring⟩

private theorem positiveTetrahedron_contract (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (q : stdSimplex ℝ (Fin 4)) :
    positiveTetrahedron (tetrahedronContract a ha q) = a • positiveTetrahedron q := by
  ext i
  rw [positiveTetrahedron_coordinate]
  change (a * q.val i.succ + (1 - a) / 4) - (a * q.val 0 + (1 - a) / 4) =
    a * positiveTetrahedron q i
  rw [positiveTetrahedron_coordinate]
  ring

private theorem positive_simplex_smaller_radius
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] {o : TangentOrientationSection M} {x : M}
    (S : OrientedChartSimplex o x) {r : ℝ} (hr : 0 ≤ r) (hrS : r ≤ S.radius)
    (q : stdSimplex ℝ (Fin 4)) :
    S.chart x + r • positiveTetrahedron q ∈ S.chart.target := by
  let a := r / S.radius
  have ha : a ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hr S.radius_pos.le, (div_le_one S.radius_pos).mpr hrS⟩
  have he : S.radius • positiveTetrahedron (tetrahedronContract a ha q) =
      r • positiveTetrahedron q := by
    rw [positiveTetrahedron_contract, smul_smul]
    congr 1
    dsimp [a]
    field_simp [ne_of_gt S.radius_pos]
  have h := S.simplex_inside (tetrahedronContract a ha q)
  rw [he] at h
  exact h

theorem OrientedChartSimplex.exists_sameChart_simplexFamily
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] {o : TangentOrientationSection M} {x : M}
    (S T : OrientedChartSimplex o x) (hchart : S.chart = T.chart) :
    ∃ H : S.simplex.Homotopy T.simplex,
      ∀ (t : unitInterval) (q : stdSimplex ℝ (Fin 4)),
        (∃ i : Fin 4, q.val i = 0) → H (t, q) ≠ x := by
  let r (t : unitInterval) : ℝ := (1 - (t : ℝ)) * S.radius + (t : ℝ) * T.radius
  have hrLower (t : unitInterval) : min S.radius T.radius ≤ r t := by
    have h₁ := mul_nonneg (sub_nonneg.mpr t.property.2)
      (sub_nonneg.mpr (min_le_left S.radius T.radius))
    have h₂ := mul_nonneg t.property.1
      (sub_nonneg.mpr (min_le_right S.radius T.radius))
    dsimp [r]
    nlinarith
  have hrPos (t : unitInterval) : 0 < r t :=
    lt_of_lt_of_le (lt_min S.radius_pos T.radius_pos) (hrLower t)
  have hrUpper (t : unitInterval) : r t ≤ max S.radius T.radius := by
    have h₁ := mul_nonneg (sub_nonneg.mpr t.property.2)
      (sub_nonneg.mpr (le_max_left S.radius T.radius))
    have h₂ := mul_nonneg t.property.1
      (sub_nonneg.mpr (le_max_right S.radius T.radius))
    dsimp [r]
    nlinarith
  have hinside (t : unitInterval) (q : stdSimplex ℝ (Fin 4)) :
      S.chart x + r t • positiveTetrahedron q ∈ S.chart.target := by
    by_cases hST : S.radius ≤ T.radius
    · have hrT : r t ≤ T.radius := by simpa only [max_eq_right hST] using hrUpper t
      have h := positive_simplex_smaller_radius T (hrPos t).le hrT q
      simpa only [← hchart] using h
    · have hrS : r t ≤ S.radius := by
        simpa only [max_eq_left (le_of_not_ge hST)] using hrUpper t
      exact positive_simplex_smaller_radius S (hrPos t).le hrS q
  let H : S.simplex.Homotopy T.simplex := {
    toFun := fun p => S.chart.symm (S.chart x + r p.1 • positiveTetrahedron p.2)
    continuous_toFun := S.chart.continuousOn_symm.comp_continuous
      (by
        have hr : Continuous r := by dsimp [r]; fun_prop
        exact continuous_const.add ((hr.comp continuous_fst).smul
          (positiveTetrahedron.continuous.comp continuous_snd)))
      (fun p => hinside p.1 p.2)
    map_zero_left := fun q => by
      change S.chart.symm (S.chart x + r 0 • positiveTetrahedron q) = S.simplex q
      simp [r, OrientedChartSimplex.simplex]
    map_one_left := fun q => by
      change S.chart.symm (S.chart x + r 1 • positiveTetrahedron q) = T.simplex q
      rw [hchart]
      simp [r, OrientedChartSimplex.simplex] }
  refine ⟨H, ?_⟩
  intro t q hboundary hzero
  obtain ⟨i, hi⟩ := hboundary
  have hq := positiveTetrahedron_face_ne_zero q i hi
  have he := congrArg S.chart hzero
  change S.chart (S.chart.symm (S.chart x + r t • positiveTetrahedron q)) = S.chart x at he
  rw [S.chart.right_inv (hinside t q)] at he
  have hs : r t • positiveTetrahedron q = 0 := by
    have h := congrArg (fun y : ThreeSpace => y - S.chart x) he
    simpa only [add_sub_cancel_left, sub_self] using h
  exact hq ((smul_eq_zero.mp hs).resolve_left (ne_of_gt (hrPos t)))


theorem OrientedChartSimplex.localClass_eq_of_sameChart
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] {o : TangentOrientationSection M} {x : M}
    (S T : OrientedChartSimplex o x) (hchart : S.chart = T.chart) :
    S.localClass = T.localClass := by
  obtain ⟨H, hH⟩ := S.exists_sameChart_simplexFamily T hchart
  exact S.localClass_eq_of_simplexFamily T H hH

theorem OrientedChartSimplex.localClass_eq_of_positive_charts
    (S T : OrientedChartSimplex o x) : S.localClass = T.localClass := by
  obtain ⟨H, hH⟩ := S.exists_positiveCharts_simplexFamily T
  exact S.localClass_eq_of_simplexFamily T H hH

theorem exists_unique_localOrientationClass (o : TangentOrientationSection M) (x : M) :
    ∃! xi : LocalIntegralHomology M x 3, ∀ S : OrientedChartSimplex o x, S.localClass = xi := by
  obtain ⟨S⟩ := exists_orientedChartSimplex o x
  exact ⟨S.localClass, fun T => T.localClass_eq_of_positive_charts S,
    fun xi hxi => (hxi S).symm⟩

def localOrientationClass (o : TangentOrientationSection M) (x : M) :
    LocalIntegralHomology M x 3 :=
  Classical.choose (exists_unique_localOrientationClass o x)


theorem localOrientationClass_spec (o : TangentOrientationSection M) (x : M)
    (S : OrientedChartSimplex o x) : S.localClass = localOrientationClass o x :=
  (Classical.choose_spec (exists_unique_localOrientationClass o x)).1 S


omit [IsManifold ThreeModel ∞ M] in
noncomputable def localIntegralHomologyEquivInt (x : M) :
    LocalIntegralHomology M x 3 ≃ₗ[ℤ] ℤ := by
  haveI : T1Space M := ChartedSpace.t1Space ThreeSpace M
  let uliftChart := (Homeomorph.ulift (X := ThreeSpace)).symm.toOpenPartialHomeomorph
  letI : InnerProductSpace ℝ (ULift.{u} ThreeSpace) :=
    { inner := fun x y => inner ℝ x.down y.down
      norm_sq_eq_re_inner := fun x => norm_sq_eq_re_inner x.down
      conj_inner_symm := fun x y => inner_conj_symm x.down y.down
      add_left := fun x y z => inner_add_left x.down y.down z.down
      smul_left := fun x y r => inner_smul_left x.down y.down r }
  letI : ChartedSpace (ULift.{u} ThreeSpace) M :=
    { atlas := (fun e : OpenPartialHomeomorph M ThreeSpace => e.trans uliftChart) ''
        atlas ThreeSpace M
      chartAt := fun x => (chartAt ThreeSpace x).trans uliftChart
      mem_chart_source := fun x => by
        rw [OpenPartialHomeomorph.trans_source]
        exact ⟨mem_chart_source ThreeSpace x, trivial⟩
      chart_mem_atlas := fun x => ⟨chartAt ThreeSpace x, chart_mem_atlas ThreeSpace x, rfl⟩ }
  have hfin : Module.finrank ℝ (ULift.{u} ThreeSpace) = 1 + 2 :=
    (ULift.moduleEquiv (R := ℝ) (M := ThreeSpace)).finrank_eq.trans (by simp)
  exact DifferentialGeometry.Topology.integralManifoldLocalTopEquiv
    (E := ULift.{u} ThreeSpace) 1 hfin M x


theorem localOrientationClass_generator_of_isUnit (o : TangentOrientationSection M) (x : M)
    (h : IsUnit (localIntegralHomologyEquivInt (M := M) x (localOrientationClass o x))) :
    Function.Bijective (fun z : ℤ => z • localOrientationClass o x) := by
  let e := localIntegralHomologyEquivInt (M := M) x
  obtain ⟨u, hu⟩ := h
  have hfun : (fun z : ℤ => z • localOrientationClass o x) =
      fun z : ℤ => e.symm ((z : ℤ) * (u : ℤ)) := by
    funext z
    apply e.injective
    rw [map_zsmul, hu, smul_eq_mul, LinearEquiv.apply_symm_apply]
  rw [hfun]
  constructor
  · intro a b hab
    have h2 : (a : ℤ) * (u : ℤ) = (b : ℤ) * (u : ℤ) := e.symm.injective hab
    exact mul_right_cancel₀ (Units.ne_zero u) h2
  · intro w
    refine ⟨e w * ((u⁻¹ : ℤˣ) : ℤ), ?_⟩
    change e.symm ((e w * ((u⁻¹ : ℤˣ) : ℤ)) * (u : ℤ)) = w
    rw [mul_assoc, Units.inv_mul, mul_one, e.symm_apply_apply]


section ZsmulGenerator

variable {A : Type*} [AddCommGroup A] [Module ℤ A]

theorem isUnit_apply_iff_bijective_zsmul (e : A ≃ₗ[ℤ] ℤ) (c : A) :
    IsUnit (e c) ↔ Function.Bijective (fun z : ℤ => z • c) := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := h
    have hfun : (fun z : ℤ => z • c) = fun z : ℤ => e.symm ((z : ℤ) * (u : ℤ)) := by
      funext z
      apply e.injective
      rw [map_zsmul, hu, smul_eq_mul, LinearEquiv.apply_symm_apply]
    rw [hfun]
    constructor
    · intro a b hab
      have h2 : (a : ℤ) * (u : ℤ) = (b : ℤ) * (u : ℤ) := e.symm.injective hab
      exact mul_right_cancel₀ (Units.ne_zero u) h2
    · intro w
      refine ⟨e w * ((u⁻¹ : ℤˣ) : ℤ), ?_⟩
      change e.symm ((e w * ((u⁻¹ : ℤˣ) : ℤ)) * (u : ℤ)) = w
      rw [mul_assoc, Units.inv_mul, mul_one, e.symm_apply_apply]
  · intro h
    obtain ⟨k, hk⟩ := h.surjective (e.symm 1)
    have hk' : k * e c = 1 := by
      have h := congrArg e hk
      rw [map_zsmul, LinearEquiv.apply_symm_apply, smul_eq_mul] at h
      exact h
    exact isUnit_iff_exists_inv.mpr ⟨k, by rw [mul_comm]; exact hk'⟩

theorem isUnit_apply_iff_of_int_linearEquiv (φ : ℤ ≃ₗ[ℤ] ℤ) (m : ℤ) :
    IsUnit (φ m) ↔ IsUnit m := by
  have hg : IsUnit (φ 1) := by
    refine isUnit_iff_exists_inv.mpr ⟨φ.symm 1, ?_⟩
    have hs := map_smul φ (φ.symm 1) (1 : ℤ)
    simp only [smul_eq_mul, mul_one, LinearEquiv.apply_symm_apply] at hs
    rw [mul_comm]
    exact hs.symm
  have hm : φ m = m * (φ 1) := by
    have hs := map_smul φ m (1 : ℤ)
    simpa only [smul_eq_mul, mul_one] using hs
  have hφ : φ 1 = 1 ∨ φ 1 = -1 := Int.isUnit_iff.mp hg
  rw [hm]
  rcases hφ with h | h
  · rw [h, mul_one]
  · rw [h, mul_neg_one]
    exact ⟨fun hh => by simpa using hh.neg, fun hh => hh.neg⟩

theorem isUnit_apply_iff_isUnit_apply_of_linearEquiv (e e' : A ≃ₗ[ℤ] ℤ) (c : A) :
    IsUnit (e c) ↔ IsUnit (e' c) := by
  have h : (e.symm.trans e') (e c) = e' c := by
    rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rw [← h]
  exact (isUnit_apply_iff_of_int_linearEquiv (e.symm.trans e') (e c)).symm

theorem isUnit_apply_iff_isUnit_apply_of_linearEquiv_trans {B : Type*} [AddCommGroup B]
    [Module ℤ B] (f : A ≃ₗ[ℤ] B) (e : B ≃ₗ[ℤ] ℤ) (e' : A ≃ₗ[ℤ] ℤ) (c : A) :
    IsUnit (e (f c)) ↔ IsUnit (e' c) :=
  isUnit_apply_iff_isUnit_apply_of_linearEquiv (f.trans e) e' c

theorem isUnit_apply_iff_exists_surjective_functional (e : A ≃ₗ[ℤ] ℤ) (c : A) :
    IsUnit (e c) ↔ ∃ φ : A →ₗ[ℤ] ℤ, Function.Surjective φ ∧ φ c = 1 := by
  constructor
  · intro h
    rcases Int.isUnit_iff.mp h with h | h
    · exact ⟨e.toLinearMap, fun y => ⟨e.symm y, e.apply_symm_apply y⟩, h⟩
    · refine ⟨-e.toLinearMap, fun y => ⟨e.symm (-y), ?_⟩, ?_⟩
      · simp only [LinearMap.neg_apply, LinearEquiv.coe_toLinearMap,
          LinearEquiv.apply_symm_apply, neg_neg]
      · simp only [LinearMap.neg_apply, LinearEquiv.coe_toLinearMap, h]
        norm_num
  · rintro ⟨φ, -, hc⟩
    have h2 : (e c) • e.symm 1 = c := by
      rw [← map_zsmul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
    have hmul : (e c) * φ (e.symm 1) = 1 := calc
      (e c) * φ (e.symm 1) = φ ((e c) • e.symm 1) := by rw [map_zsmul, smul_eq_mul]
      _ = φ c := by rw [h2]
      _ = 1 := hc
    exact Int.isUnit_iff.mpr (Int.eq_one_or_neg_one_of_mul_eq_one hmul)

theorem isUnit_apply_iff_forall_exists_zsmul (e : A ≃ₗ[ℤ] ℤ) (c : A) :
    IsUnit (e c) ↔ ∀ a : A, ∃ k : ℤ, a = k • c := by
  constructor
  · intro h a
    obtain ⟨v, hv⟩ := h
    refine ⟨e a * ((v⁻¹ : ℤˣ) : ℤ), ?_⟩
    apply e.injective
    rw [map_zsmul, smul_eq_mul, ← hv, mul_assoc, Units.inv_mul, mul_one]
  · intro h
    obtain ⟨k, hk⟩ := h (e.symm 1)
    have h1 : e c * k = 1 := by
      have h2 := congrArg e hk
      rw [map_zsmul, LinearEquiv.apply_symm_apply, smul_eq_mul] at h2
      rw [mul_comm]
      exact h2.symm
    exact Int.isUnit_iff.mpr (Int.eq_one_or_neg_one_of_mul_eq_one h1)

theorem bijective_zsmul_iff_of_linearEquiv {B : Type*} [AddCommGroup B] [Module ℤ B]
    (f : A ≃ₗ[ℤ] B) (c : A) :
    Function.Bijective (fun z : ℤ => z • f c) ↔ Function.Bijective (fun z : ℤ => z • c) := by
  have hfun : (fun z : ℤ => z • f c) = ⇑f ∘ fun z : ℤ => z • c := by
    funext z
    rw [Function.comp_apply, map_zsmul]
  rw [hfun]
  exact Equiv.comp_bijective (fun z : ℤ => z • c) f.toEquiv

end ZsmulGenerator


theorem localOrientationClass_generator_iff_isUnit (o : TangentOrientationSection M) (x : M) :
    Function.Bijective (fun z : ℤ => z • localOrientationClass o x) ↔
      IsUnit (localIntegralHomologyEquivInt (M := M) x (localOrientationClass o x)) :=
  (isUnit_apply_iff_bijective_zsmul (localIntegralHomologyEquivInt (M := M) x)
    (localOrientationClass o x)).symm


theorem localOrientationClass_generator_iff_exists_surjective_functional
    (o : TangentOrientationSection M) (x : M) :
    Function.Bijective (fun z : ℤ => z • localOrientationClass o x) ↔
      ∃ φ : LocalIntegralHomology M x 3 →ₗ[ℤ] ℤ,
        Function.Surjective φ ∧ φ (localOrientationClass o x) = 1 :=
  (localOrientationClass_generator_iff_isUnit o x).trans
    (isUnit_apply_iff_exists_surjective_functional _ _)


theorem localOrientationClass_generator_iff_forall_exists_zsmul
    (o : TangentOrientationSection M) (x : M) :
    Function.Bijective (fun z : ℤ => z • localOrientationClass o x) ↔
      ∀ a : LocalIntegralHomology M x 3, ∃ k : ℤ, a = k • localOrientationClass o x :=
  (localOrientationClass_generator_iff_isUnit o x).trans
    (isUnit_apply_iff_forall_exists_zsmul _ _)


theorem localOrientationClass_generator_of_exists_surjective_functional
    (o : TangentOrientationSection M) (x : M)
    (φ : LocalIntegralHomology M x 3 →ₗ[ℤ] ℤ) (hφ : Function.Surjective φ)
    (h : φ (localOrientationClass o x) = 1) :
    Function.Bijective (fun z : ℤ => z • localOrientationClass o x) :=
  (localOrientationClass_generator_iff_exists_surjective_functional o x).mpr ⟨φ, hφ, h⟩


section

open DifferentialGeometry.Topology

def integralSimplexChainMap {X : Type u} [TopologicalSpace X] (n : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    integralSingularCoefficients ⟶ (integralSingularChains X).X n :=
  (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
    ((TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋n⦌)).symm σ)

private def euclideanPuncturedFace {X : Type u} [TopologicalSpace X] (p : X)
    (σ : C(stdSimplex ℝ (Fin 4), X))
    (hσ : ∀ (i : Fin 4) (q : stdSimplex ℝ (Fin 3)), σ (orientedSimplexFace i q) ≠ p)
    (i : Fin 4) : C(stdSimplex ℝ (Fin 3), ({p}ᶜ : Set X)) :=
  ⟨fun q => ⟨σ (orientedSimplexFace i q), hσ i q⟩,
    (σ.continuous.comp (orientedSimplexFace i).continuous).subtype_mk _⟩

set_option backward.isDefEq.respectTransparency false in
private theorem euclideanPuncturedFace_chain {X : Type u} [TopologicalSpace X] (p : X)
    (σ : C(stdSimplex ℝ (Fin 4), X))
    (hσ : ∀ (i : Fin 4) (q : stdSimplex ℝ (Fin 3)), σ (orientedSimplexFace i q) ≠ p)
    (i : Fin 4) :
    integralSimplexChainMap 2 (euclideanPuncturedFace p σ hσ i) ≫
      (integralSingularChainMap (singularSubspaceInclusion ({(p : X)}ᶜ : Set X))).f 2 =
        integralSimplexChainMap 2 (σ.comp (orientedSimplexFace i)) :=
  SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of ({p}ᶜ : Set X)))
    (TopCat.toSSet.obj (TopCat.of X))
    (TopCat.toSSet.map (TopCat.ofHom (singularSubspaceInclusion ({(p : X)}ᶜ : Set X))))
    integralSingularCoefficients
    ((TopCat.toSSetObjEquiv (TopCat.of ({p}ᶜ : Set X)) (.op ⦋2⦌)).symm
      (euclideanPuncturedFace p σ hσ i))

set_option backward.isDefEq.respectTransparency false in
private theorem euclideanSimplexChain_boundary {X : Type u} [TopologicalSpace X]
    (σ : C(stdSimplex ℝ (Fin 4), X)) :
    integralSimplexChainMap 3 σ ≫ (integralSingularChains X).d 3 2 =
      ∑ i : Fin 4, (-1 : ℤ) ^ i.val •
        integralSimplexChainMap 2 (σ.comp (orientedSimplexFace i)) :=
  (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex_d (R := integralSingularCoefficients)
    ((TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋3⦌)).symm σ)

set_option backward.isDefEq.respectTransparency false in
private theorem euclideanRelativeChain_boundary {X : Type u} [TopologicalSpace X] (p : X)
    (σ : C(stdSimplex ℝ (Fin 4), X))
    (hσ : ∀ (i : Fin 4) (q : stdSimplex ℝ (Fin 3)), σ (orientedSimplexFace i q) ≠ p) :
    (integralSimplexChainMap 3 σ ≫ (cokernel.π (integralSingularChainMap
      (singularSubspaceInclusion ({(p : X)}ᶜ : Set X)))).f 3) ≫
      (integralRelativeChains ({(p : X)}ᶜ : Set X)).d 3 2 = 0 := by
  let quotientMap := cokernel.π (integralSingularChainMap
    (singularSubspaceInclusion ({(p : X)}ᶜ : Set X)))
  have hπ : (integralSingularChainMap (singularSubspaceInclusion ({(p : X)}ᶜ : Set X))).f 2 ≫
      quotientMap.f 2 = 0 :=
    congrArg (fun f => f.f 2) (cokernel.condition
      (integralSingularChainMap (singularSubspaceInclusion ({(p : X)}ᶜ : Set X))))
  have hf (i : Fin 4) :
      integralSimplexChainMap 2 (σ.comp (orientedSimplexFace i)) ≫ quotientMap.f 2 = 0 := by
    rw [← euclideanPuncturedFace_chain p σ hσ i, Category.assoc, hπ, comp_zero]
  change (integralSimplexChainMap 3 σ ≫ quotientMap.f 3) ≫
    (cokernel (integralSingularChainMap (singularSubspaceInclusion ({(p : X)}ᶜ : Set X)))).d 3 2 = 0
  rw [Category.assoc, quotientMap.comm 3 2, ← Category.assoc, euclideanSimplexChain_boundary]
  simp only [Preadditive.sum_comp, Linear.smul_comp, hf, smul_zero, Finset.sum_const_zero]

def simplexLocalClass {X : Type u} [TopologicalSpace X] (p : X)
    (σ : C(stdSimplex ℝ (Fin 4), X))
    (hσ : ∀ (i : Fin 4) (q : stdSimplex ℝ (Fin 3)), σ (orientedSimplexFace i q) ≠ p) :
    integralLocalHomology 3 p :=
  ((integralRelativeChains ({(p : X)}ᶜ : Set X)).liftCycles
      (integralSimplexChainMap 3 σ ≫ (cokernel.π (integralSingularChainMap
        (singularSubspaceInclusion ({(p : X)}ᶜ : Set X)))).f 3) 2
      ((ComplexShape.down ℕ).next_eq' (by rfl))
      (euclideanRelativeChain_boundary p σ hσ) ≫
    (integralRelativeChains ({(p : X)}ᶜ : Set X)).homologyπ 3) (ULift.up 1)

private def liftedPositiveTetrahedron : C(stdSimplex ℝ (Fin 4), DifferentialGeometry.Topology.liftedSphereSpace.{u} 1) where
  toFun q := (ULift.up (positiveTetrahedron q) : DifferentialGeometry.Topology.liftedSphereSpace.{u} 1)
  continuous_toFun :=
    (Homeomorph.ulift (X := ThreeSpace) : DifferentialGeometry.Topology.liftedSphereSpace.{u} 1 ≃ₜ ThreeSpace).symm.continuous.comp
      positiveTetrahedron.continuous

private theorem liftedPositiveTetrahedron_face_ne_zero (i : Fin 4)
    (q : stdSimplex ℝ (Fin 3)) :
    liftedPositiveTetrahedron (orientedSimplexFace i q) ≠ (0 : DifferentialGeometry.Topology.liftedSphereSpace.{u} 1) := by
  intro hh
  exact positiveTetrahedron_face_ne_zero (orientedSimplexFace i q) i
    (orientedSimplexFace_zero i q) (ULift.up_inj.mp hh)

def euclideanStandardSimplexClass : integralLocalHomology 3 (0 : DifferentialGeometry.Topology.liftedSphereSpace.{u} 1) :=
  simplexLocalClass (0 : DifferentialGeometry.Topology.liftedSphereSpace.{u} 1) liftedPositiveTetrahedron
    (fun i q => liftedPositiveTetrahedron_face_ne_zero i q)

theorem integralSimplexChainMap_naturality {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (f : C(X, Y)) (s : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    integralSimplexChainMap n s ≫ (integralSingularChainMap f).f n = integralSimplexChainMap n (f.comp s) := by
  have h := SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of X))
    (TopCat.toSSet.obj (TopCat.of Y)) (TopCat.toSSet.map (TopCat.ofHom f))
    integralSingularCoefficients ((TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋n⦌)).symm s)
  have hσ : (ConcreteCategory.hom ((TopCat.toSSet.map (TopCat.ofHom f)).app (Opposite.op ⦋n⦌)))
      (((TopCat.of X).toSSetObjEquiv (Opposite.op ⦋n⦌)).symm s) =
      ((TopCat.of Y).toSSetObjEquiv (Opposite.op ⦋n⦌)).symm (f.comp s) := by
    apply (TopCat.toSSetObjEquiv (TopCat.of Y) (Opposite.op ⦋n⦌)).injective
    rw [Equiv.apply_symm_apply]
    exact integralSingularSimplexMap_apply n f _
  rw [hσ] at h
  exact h

theorem integralRelativeHomologyMap_liftCycles_apply
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : MapsTo f A B)
    (z : integralSingularCoefficients ⟶ (integralRelativeChains A).X (n + 1))
    (hz : z ≫ (integralRelativeChains A).d (n + 1) n = 0)
    (h : (z ≫ (integralRelativeChainMap f hf).f (n + 1)) ≫
      (integralRelativeChains B).d (n + 1) n = 0) :
    integralRelativeHomologyMap (n + 1) f hf
      ((((integralRelativeChains A).liftCycles z n ((ComplexShape.down ℕ).next_eq' (by rfl)) hz) ≫
        (integralRelativeChains A).homologyπ (n + 1)) (ULift.up 1)) =
      ((((integralRelativeChains B).liftCycles (z ≫ (integralRelativeChainMap f hf).f (n + 1)) n
        ((ComplexShape.down ℕ).next_eq' (by rfl)) h) ≫
        (integralRelativeChains B).homologyπ (n + 1)) (ULift.up 1)) := by
  have hm :
      ((integralRelativeChains A).liftCycles z n ((ComplexShape.down ℕ).next_eq' (by rfl)) hz ≫
          (integralRelativeChains A).homologyπ (n + 1)) ≫
        HomologicalComplex.homologyMap (integralRelativeChainMap f hf) (n + 1) =
      (integralRelativeChains B).liftCycles (z ≫ (integralRelativeChainMap f hf).f (n + 1)) n
        ((ComplexShape.down ℕ).next_eq' (by rfl)) h ≫
      (integralRelativeChains B).homologyπ (n + 1) := by
    rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc,
      HomologicalComplex.liftCycles_comp_cyclesMap]
  exact congrArg (fun k => k (ULift.up 1)) hm

set_option backward.isDefEq.respectTransparency false in
theorem relativeChain_subspaceInclusion_apply {X : Type u} [TopologicalSpace X] (A : Set X) (p : A)
    (σ : C(stdSimplex ℝ (Fin 4), A)) :
    (integralSimplexChainMap 3 σ ≫ (cokernel.π (integralSingularChainMap
        (singularSubspaceInclusion ({(p : A)}ᶜ : Set A)))).f 3) ≫
      (integralRelativeChainMap (singularSubspaceInclusion A)
        (A := ({(p : A)}ᶜ : Set A)) (B := ({(p : X)}ᶜ : Set X))
        (fun _ hy hyx => hy (Subtype.ext hyx))).f 3 =
      integralSimplexChainMap 3 (⟨fun q => (σ q : X), σ.continuous.subtype_val⟩ :
        C(stdSimplex ℝ (Fin 4), X)) ≫
      (cokernel.π (integralSingularChainMap
        (singularSubspaceInclusion ({(p : X)}ᶜ : Set X)))).f 3 := by
  have hnat := congrArg (fun k => k.f 3) (integralRelativeChainMap_π
    (singularSubspaceInclusion A)
    (A := ({(p : A)}ᶜ : Set A)) (B := ({(p : X)}ᶜ : Set X))
    (fun _ hy hyx => hy (Subtype.ext hyx)))
  simp only [HomologicalComplex.comp_f] at hnat
  rw [Category.assoc, hnat, ← Category.assoc, integralSimplexChainMap_naturality]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem relativeChain_map_apply {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (g : C(X, Y)) {A : Set X} {B : Set Y} (hg : MapsTo g A B)
    (σ : C(stdSimplex ℝ (Fin 4), X)) (σ' : C(stdSimplex ℝ (Fin 4), Y)) (hσ' : σ' = g.comp σ) :
    (integralSimplexChainMap 3 σ ≫ (cokernel.π (integralSingularChainMap
        (singularSubspaceInclusion A))).f 3) ≫
      (integralRelativeChainMap g hg).f 3 =
      integralSimplexChainMap 3 σ' ≫
        (cokernel.π (integralSingularChainMap (singularSubspaceInclusion B))).f 3 := by
  have hnat := congrArg (fun k => k.f 3) (integralRelativeChainMap_π g hg)
  simp only [HomologicalComplex.comp_f] at hnat
  rw [Category.assoc, hnat, ← Category.assoc, integralSimplexChainMap_naturality, hσ']

set_option backward.isDefEq.respectTransparency false in
theorem integralLocalHomologyNeighborhoodIso_hom_liftCycles {X : Type u} [TopologicalSpace X] [T1Space X]
    (U : Set X) (hU : IsOpen U) (p : X) (hp : p ∈ U)
    (z : integralSingularCoefficients ⟶ (integralRelativeChains ({(⟨p, hp⟩ : U)}ᶜ : Set U)).X 3)
    (hz : z ≫ (integralRelativeChains ({(⟨p, hp⟩ : U)}ᶜ : Set U)).d 3 2 = 0)
    (z' : integralSingularCoefficients ⟶ (integralRelativeChains ({(p : X)}ᶜ : Set X)).X 3)
    (hz' : z' ≫ (integralRelativeChains ({(p : X)}ᶜ : Set X)).d 3 2 = 0)
    (hzz : z ≫ (integralRelativeChainMap (singularSubspaceInclusion U)
      (A := ({(⟨p, hp⟩ : U)}ᶜ : Set U)) (B := ({(p : X)}ᶜ : Set X))
      (neighborhoodPointComplement_mapsTo p U hp)).f 3 = z') :
    (integralLocalHomologyNeighborhoodIso 3 p U hU hp).hom.hom
      ((((integralRelativeChains ({(⟨p, hp⟩ : U)}ᶜ : Set U)).liftCycles z 2
        ((ComplexShape.down ℕ).next_eq' (by rfl)) hz) ≫
        (integralRelativeChains ({(⟨p, hp⟩ : U)}ᶜ : Set U)).homologyπ 3) (ULift.up 1)) =
      ((((integralRelativeChains ({(p : X)}ᶜ : Set X)).liftCycles z' 2
        ((ComplexShape.down ℕ).next_eq' (by rfl)) hz') ≫
        (integralRelativeChains ({(p : X)}ᶜ : Set X)).homologyπ 3) (ULift.up 1)) := by
  rw [integralLocalHomologyNeighborhoodIso_hom]
  rw [integralRelativeHomologyMap_liftCycles_apply (n := 2) (f := singularSubspaceInclusion U)
    (A := ({(⟨p, hp⟩ : U)}ᶜ : Set U)) (B := ({(p : X)}ᶜ : Set X))
    (hf := neighborhoodPointComplement_mapsTo p U hp) (z := z) (hz := hz)
    (h := hzz.symm ▸ hz')]
  exact congrArg (fun k : integralSingularCoefficients ⟶
      (integralRelativeChains ({(p : X)}ᶜ : Set X)).homology 3 => k (ULift.up 1))
    (chainComplex_liftCycles_homologyπ_congr 2 _ _ _ _ hzz)

set_option backward.isDefEq.respectTransparency false in
theorem integralLocalHomologyNeighborhoodIso_inv_liftCycles {X : Type u} [TopologicalSpace X] [T1Space X]
    (U : Set X) (hU : IsOpen U) (p : X) (hp : p ∈ U)
    (z : integralSingularCoefficients ⟶ (integralRelativeChains ({(⟨p, hp⟩ : U)}ᶜ : Set U)).X 3)
    (hz : z ≫ (integralRelativeChains ({(⟨p, hp⟩ : U)}ᶜ : Set U)).d 3 2 = 0)
    (z' : integralSingularCoefficients ⟶ (integralRelativeChains ({(p : X)}ᶜ : Set X)).X 3)
    (hz' : z' ≫ (integralRelativeChains ({(p : X)}ᶜ : Set X)).d 3 2 = 0)
    (hzz : z ≫ (integralRelativeChainMap (singularSubspaceInclusion U)
      (A := ({(⟨p, hp⟩ : U)}ᶜ : Set U)) (B := ({(p : X)}ᶜ : Set X))
      (neighborhoodPointComplement_mapsTo p U hp)).f 3 = z') :
    (integralLocalHomologyNeighborhoodIso 3 p U hU hp).inv.hom
      ((((integralRelativeChains ({(p : X)}ᶜ : Set X)).liftCycles z' 2
        ((ComplexShape.down ℕ).next_eq' (by rfl)) hz') ≫
        (integralRelativeChains ({(p : X)}ᶜ : Set X)).homologyπ 3) (ULift.up 1)) =
      ((((integralRelativeChains ({(⟨p, hp⟩ : U)}ᶜ : Set U)).liftCycles z 2
        ((ComplexShape.down ℕ).next_eq' (by rfl)) hz) ≫
        (integralRelativeChains ({(⟨p, hp⟩ : U)}ᶜ : Set U)).homologyπ 3) (ULift.up 1)) := by
  rw [← integralLocalHomologyNeighborhoodIso_hom_liftCycles U hU p hp z hz z' hz' hzz]
  exact Iso.hom_inv_id_apply (integralLocalHomologyNeighborhoodIso 3 p U hU hp) _

set_option backward.isDefEq.respectTransparency false in
theorem integralLocalHomologyHomeomorphIso_hom_liftCycles {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (g : X ≃ₜ Y) (p : X)
    (z : integralSingularCoefficients ⟶ (integralRelativeChains ({(p : X)}ᶜ : Set X)).X 3)
    (hz : z ≫ (integralRelativeChains ({(p : X)}ᶜ : Set X)).d 3 2 = 0)
    (z' : integralSingularCoefficients ⟶ (integralRelativeChains ({(g p : Y)}ᶜ : Set Y)).X 3)
    (hz' : z' ≫ (integralRelativeChains ({(g p : Y)}ᶜ : Set Y)).d 3 2 = 0)
    (hzz : z ≫ (integralRelativeChainMap (⟨g, g.continuous⟩ : C(X, Y))
      (A := ({(p : X)}ᶜ : Set X)) (B := ({(g p : Y)}ᶜ : Set Y))
      (fun _ hy => g.injective.ne hy)).f 3 = z') :
    (integralLocalHomologyHomeomorphIso 3 g p).hom.hom
      ((((integralRelativeChains ({(p : X)}ᶜ : Set X)).liftCycles z 2
        ((ComplexShape.down ℕ).next_eq' (by rfl)) hz) ≫
        (integralRelativeChains ({(p : X)}ᶜ : Set X)).homologyπ 3) (ULift.up 1)) =
      ((((integralRelativeChains ({(g p : Y)}ᶜ : Set Y)).liftCycles z' 2
        ((ComplexShape.down ℕ).next_eq' (by rfl)) hz') ≫
        (integralRelativeChains ({(g p : Y)}ᶜ : Set Y)).homologyπ 3) (ULift.up 1)) := by
  rw [integralLocalHomologyHomeomorphIso, integralRelativeHomologyHomeomorphIso_hom]
  rw [integralRelativeHomologyMap_liftCycles_apply (n := 2) (f := (⟨g, g.continuous⟩ : C(X, Y)))
    (A := ({(p : X)}ᶜ : Set X)) (B := ({(g p : Y)}ᶜ : Set Y))
    (hf := fun _ hy => g.injective.ne hy) (z := z) (hz := hz)
    (h := hzz.symm ▸ hz')]
  exact congrArg (fun k : integralSingularCoefficients ⟶
      (integralRelativeChains ({(g p : Y)}ᶜ : Set Y)).homology 3 => k (ULift.up 1))
    (chainComplex_liftCycles_homologyπ_congr 2 _ _ _ _ hzz)

private theorem bijective_zsmul_iff_of_linearEquiv_apply {A B : Type*} [AddCommGroup A] [Module ℤ A]
    [AddCommGroup B] [Module ℤ B] (f : A ≃ₗ[ℤ] B) (c : A) (c' : B) (h : f c = c') :
    Function.Bijective (fun z : ℤ => z • c) ↔ Function.Bijective (fun z : ℤ => z • c') := by
  rw [← h]
  exact (bijective_zsmul_iff_of_linearEquiv f c).symm

private theorem bijective_zsmul_simplexLocalClass_of_basepoint_eq {X : Type u} [TopologicalSpace X]
    {p q : X} (hp : p = q) (σ : C(stdSimplex ℝ (Fin 4), X))
    (hσp : ∀ (i : Fin 4) (t : stdSimplex ℝ (Fin 3)), σ (orientedSimplexFace i t) ≠ p)
    (hσq : ∀ (i : Fin 4) (t : stdSimplex ℝ (Fin 3)), σ (orientedSimplexFace i t) ≠ q)
    (h : Function.Bijective (fun z : ℤ => z • simplexLocalClass q σ hσq)) :
    Function.Bijective (fun z : ℤ => z • simplexLocalClass p σ hσp) := by
  subst hp
  have heq : simplexLocalClass p σ hσq = simplexLocalClass p σ hσp := by
    unfold simplexLocalClass
    exact congrArg (fun k => k (ULift.up 1))
      (chainComplex_liftCycles_homologyπ_congr
        (K := integralRelativeChains ({(p : X)}ᶜ)) 2 _ _ _ _ rfl)
  rwa [heq] at h

theorem localOrientationClass_generator_of_euclideanStandardSimplex
    (o : TangentOrientationSection M) (x : M)
    (h : Function.Bijective (fun z : ℤ => z • euclideanStandardSimplexClass.{u})) :
    Function.Bijective (fun z : ℤ => z • localOrientationClass o x) := by
  classical
  have : T1Space M := ChartedSpace.t1Space ThreeSpace M
  obtain ⟨S⟩ := exists_orientedChartSimplex o x
  let LM := DifferentialGeometry.Topology.liftedSphereSpace.{u} 1
  let uliftSymm : ThreeSpace ≃ₜ LM :=
    (Homeomorph.ulift (X := ThreeSpace) : LM ≃ₜ ThreeSpace).symm
  let chartU : OpenPartialHomeomorph M LM := S.chart.trans uliftSymm.toOpenPartialHomeomorph
  have hxU : x ∈ chartU.source := by
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨S.center_mem, Set.mem_univ _⟩
  have hSU : ∀ q : stdSimplex ℝ (Fin 4), S.simplex q ∈ chartU.source := by
    intro q
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨S.chart.map_target (S.simplex_inside q), Set.mem_univ _⟩
  let SU : C(stdSimplex ℝ (Fin 4), chartU.source) :=
    ⟨fun q => ⟨S.simplex q, hSU q⟩, S.simplex.continuous.subtype_mk hSU⟩
  have hSface : ∀ (i : Fin 4) (q : stdSimplex ℝ (Fin 3)),
      S.simplex (orientedSimplexFace i q) ≠ x := fun i q => orientedSimplex_face_ne_center S i q
  have hSUne : ∀ (i : Fin 4) (q : stdSimplex ℝ (Fin 3)),
      SU (orientedSimplexFace i q) ≠ (⟨x, hxU⟩ : chartU.source) :=
    fun i q hh => hSface i q (congrArg Subtype.val hh)
  let zU : integralSingularCoefficients ⟶
      (integralRelativeChains ({(⟨x, hxU⟩ : chartU.source)}ᶜ : Set chartU.source)).X 3 :=
    integralSimplexChainMap 3 SU ≫ (cokernel.π (integralSingularChainMap
      (singularSubspaceInclusion ({(⟨x, hxU⟩ : chartU.source)}ᶜ : Set chartU.source)))).f 3
  have hzU : (integralSimplexChainMap 3 SU ≫ (cokernel.π (integralSingularChainMap
      (singularSubspaceInclusion ({(⟨x, hxU⟩ : chartU.source)}ᶜ : Set chartU.source)))).f 3) ≫
      (integralRelativeChains ({(⟨x, hxU⟩ : chartU.source)}ᶜ : Set chartU.source)).d 3 2 = 0 :=
    euclideanRelativeChain_boundary (X := chartU.source) ⟨x, hxU⟩ SU hSUne
  let zX : integralSingularCoefficients ⟶
      (integralRelativeChains ({(x : M)}ᶜ : Set M)).X 3 :=
    integralSimplexChainMap 3 S.simplex ≫ (cokernel.π (integralSingularChainMap
      (singularSubspaceInclusion ({(x : M)}ᶜ : Set M)))).f 3
  have hzX : (integralSimplexChainMap 3 S.simplex ≫ (cokernel.π (integralSingularChainMap
      (singularSubspaceInclusion ({(x : M)}ᶜ : Set M)))).f 3) ≫
      (integralRelativeChains ({(x : M)}ᶜ : Set M)).d 3 2 = 0 :=
    euclideanRelativeChain_boundary (X := M) x S.simplex hSface
  have hchainU : zU ≫ (integralRelativeChainMap (singularSubspaceInclusion (chartU.source : Set M))
      (A := ({(⟨x, hxU⟩ : chartU.source)}ᶜ : Set chartU.source)) (B := ({(x : M)}ᶜ : Set M))
      (neighborhoodPointComplement_mapsTo x chartU.source hxU)).f 3 = zX :=
    relativeChain_map_apply (singularSubspaceInclusion (chartU.source : Set M))
      (neighborhoodPointComplement_mapsTo x chartU.source hxU) SU S.simplex rfl
  have hclassX : localOrientationClass o x =
      (((integralRelativeChains ({(x : M)}ᶜ : Set M)).liftCycles zX 2
        ((ComplexShape.down ℕ).next_eq' (by rfl)) hzX) ≫
        (integralRelativeChains ({(x : M)}ᶜ : Set M)).homologyπ 3) (ULift.up 1) := by
    rw [← localOrientationClass_spec o x S]
    rfl
  have hclassU : (integralLocalHomologyNeighborhoodIso 3 x chartU.source chartU.open_source hxU).inv.hom
      (localOrientationClass o x) =
      (((integralRelativeChains ({(⟨x, hxU⟩ : chartU.source)}ᶜ : Set chartU.source)).liftCycles zU 2
        ((ComplexShape.down ℕ).next_eq' (by rfl)) hzU) ≫
        (integralRelativeChains ({(⟨x, hxU⟩ : chartU.source)}ᶜ : Set chartU.source)).homologyπ 3)
        (ULift.up 1) := by
    rw [hclassX]
    exact integralLocalHomologyNeighborhoodIso_inv_liftCycles chartU.source chartU.open_source x hxU zU hzU zX hzX hchainU
  let cU : ↑(integralLocalHomology 3 (⟨x, hxU⟩ : chartU.source)) :=
    (integralLocalHomologyNeighborhoodIso 3 x chartU.source chartU.open_source hxU).toLinearEquiv.symm
      (localOrientationClass o x)
  have hcU : cU =
      (((integralRelativeChains ({(⟨x, hxU⟩ : chartU.source)}ᶜ : Set chartU.source)).liftCycles zU 2
        ((ComplexShape.down ℕ).next_eq' (by rfl)) hzU) ≫
        (integralRelativeChains ({(⟨x, hxU⟩ : chartU.source)}ᶜ : Set chartU.source)).homologyπ 3)
        (ULift.up 1) := hclassU
  have hstepU : Function.Bijective (fun z : ℤ => z • cU) ↔
      Function.Bijective (fun z : ℤ => z • localOrientationClass o x) :=
    (bijective_zsmul_iff_of_linearEquiv_apply
      ((integralLocalHomologyNeighborhoodIso 3 x chartU.source chartU.open_source hxU).toLinearEquiv.symm)
      (localOrientationClass o x) cU rfl).symm
  let tauU : C(stdSimplex ℝ (Fin 4), LM) :=
    ⟨fun q => chartU (S.simplex q), chartU.continuousOn.comp_continuous S.simplex.continuous hSU⟩
  have hchartU (q : stdSimplex ℝ (Fin 4)) :
      tauU q = (ULift.up (S.chart x + S.radius • positiveTetrahedron q) : LM) := by
    change chartU (S.simplex q) = (ULift.up (S.chart x + S.radius • positiveTetrahedron q) : LM)
    change uliftSymm (S.chart (S.chart.symm (S.chart x + S.radius • positiveTetrahedron q))) =
      (ULift.up (S.chart x + S.radius • positiveTetrahedron q) : LM)
    rw [S.chart.right_inv (S.simplex_inside q)]
    rfl
  have htauUne : ∀ (i : Fin 4) (q : stdSimplex ℝ (Fin 3)),
      tauU (orientedSimplexFace i q) ≠ chartU x := by
    intro i q hh
    exact hSface i q (chartU.injOn (hSU (orientedSimplexFace i q)) hxU hh)
  let tauV : C(stdSimplex ℝ (Fin 4), chartU.target) :=
    ⟨fun q => ⟨chartU (S.simplex q), chartU.map_source (hSU q)⟩,
      (chartU.continuousOn.comp_continuous S.simplex.continuous hSU).subtype_mk _⟩
  let p₀ : chartU.target := chartU.toHomeomorphSourceTarget (⟨x, hxU⟩ : chartU.source)
  have htauVne : ∀ (i : Fin 4) (q : stdSimplex ℝ (Fin 3)), tauV (orientedSimplexFace i q) ≠ p₀ :=
    fun i q hh => htauUne i q (congrArg Subtype.val hh)
  let zV : integralSingularCoefficients ⟶
      (integralRelativeChains ({(p₀ : chartU.target)}ᶜ : Set chartU.target)).X 3 :=
    integralSimplexChainMap 3 tauV ≫ (cokernel.π (integralSingularChainMap
      (singularSubspaceInclusion ({(p₀ : chartU.target)}ᶜ : Set chartU.target)))).f 3
  have hzV : (integralSimplexChainMap 3 tauV ≫ (cokernel.π (integralSingularChainMap
      (singularSubspaceInclusion ({(p₀ : chartU.target)}ᶜ : Set chartU.target)))).f 3) ≫
      (integralRelativeChains ({(p₀ : chartU.target)}ᶜ : Set chartU.target)).d 3 2 = 0 :=
    euclideanRelativeChain_boundary (X := chartU.target) p₀ tauV htauVne
  have hchainV : zU ≫ (integralRelativeChainMap
      (⟨chartU.toHomeomorphSourceTarget, chartU.toHomeomorphSourceTarget.continuous⟩ :
        C(chartU.source, chartU.target))
      (A := ({(⟨x, hxU⟩ : chartU.source)}ᶜ : Set chartU.source))
      (B := ({(p₀ : chartU.target)}ᶜ : Set chartU.target))
      (fun _ hy => chartU.toHomeomorphSourceTarget.injective.ne hy)).f 3 = zV :=
    relativeChain_map_apply
      (⟨chartU.toHomeomorphSourceTarget, chartU.toHomeomorphSourceTarget.continuous⟩ :
        C(chartU.source, chartU.target))
      (fun _ hy => chartU.toHomeomorphSourceTarget.injective.ne hy) SU tauV rfl
  have hV : (integralLocalHomologyHomeomorphIso 3 chartU.toHomeomorphSourceTarget
      (⟨x, hxU⟩ : chartU.source)).toLinearEquiv cU =
      (((integralRelativeChains ({(p₀ : chartU.target)}ᶜ : Set chartU.target)).liftCycles zV 2
        ((ComplexShape.down ℕ).next_eq' (by rfl)) hzV) ≫
        (integralRelativeChains ({(p₀ : chartU.target)}ᶜ : Set chartU.target)).homologyπ 3)
        (ULift.up 1) := by
    rw [hcU]
    exact integralLocalHomologyHomeomorphIso_hom_liftCycles chartU.toHomeomorphSourceTarget
      (⟨x, hxU⟩ : chartU.source) zU hzU zV hzV hchainV
  let cV : ↑(integralLocalHomology 3 (p₀ : chartU.target)) :=
    (integralLocalHomologyHomeomorphIso 3 chartU.toHomeomorphSourceTarget
      (⟨x, hxU⟩ : chartU.source)).toLinearEquiv cU
  have hstepV : Function.Bijective (fun z : ℤ => z • cV) ↔
      Function.Bijective (fun z : ℤ => z • cU) :=
    (bijective_zsmul_iff_of_linearEquiv_apply
      ((integralLocalHomologyHomeomorphIso 3 chartU.toHomeomorphSourceTarget
        (⟨x, hxU⟩ : chartU.source)).toLinearEquiv) cU cV rfl).symm
  let zT : integralSingularCoefficients ⟶
      (integralRelativeChains ({(chartU x : LM)}ᶜ : Set LM)).X 3 :=
    integralSimplexChainMap 3 tauU ≫ (cokernel.π (integralSingularChainMap
      (singularSubspaceInclusion ({(chartU x : LM)}ᶜ : Set LM)))).f 3
  have hzT : (integralSimplexChainMap 3 tauU ≫ (cokernel.π (integralSingularChainMap
      (singularSubspaceInclusion ({(chartU x : LM)}ᶜ : Set LM)))).f 3) ≫
      (integralRelativeChains ({(chartU x : LM)}ᶜ : Set LM)).d 3 2 = 0 :=
    euclideanRelativeChain_boundary (X := LM) (chartU x) tauU htauUne
  have hchainT : zV ≫ (integralRelativeChainMap (singularSubspaceInclusion (chartU.target : Set LM))
      (A := ({(p₀ : chartU.target)}ᶜ : Set chartU.target))
      (B := ({(chartU x : LM)}ᶜ : Set LM))
      (neighborhoodPointComplement_mapsTo (chartU x) chartU.target (chartU.map_source hxU))).f 3 = zT :=
    relativeChain_map_apply (singularSubspaceInclusion (chartU.target : Set LM))
      (neighborhoodPointComplement_mapsTo (chartU x) chartU.target (chartU.map_source hxU)) tauV tauU rfl
  have hdefV : cV =
      (integralLocalHomologyHomeomorphIso 3 chartU.toHomeomorphSourceTarget
        (⟨x, hxU⟩ : chartU.source)).toLinearEquiv cU := rfl
  have hT : (integralLocalHomologyNeighborhoodIso 3 p₀.val chartU.target chartU.open_target
      p₀.property).toLinearEquiv cV =
      (((integralRelativeChains ({(chartU x : LM)}ᶜ : Set LM)).liftCycles zT 2
        ((ComplexShape.down ℕ).next_eq' (by rfl)) hzT) ≫
        (integralRelativeChains ({(chartU x : LM)}ᶜ : Set LM)).homologyπ 3) (ULift.up 1) := by
    rw [hdefV, hV]
    exact integralLocalHomologyNeighborhoodIso_hom_liftCycles chartU.target chartU.open_target p₀.val p₀.property
      zV hzV zT hzT hchainT
  let cT : ↑(integralLocalHomology 3 (chartU x)) :=
    (integralLocalHomologyNeighborhoodIso 3 p₀.val chartU.target chartU.open_target
      p₀.property).toLinearEquiv cV
  have hstepT : Function.Bijective (fun z : ℤ => z • cT) ↔
      Function.Bijective (fun z : ℤ => z • cV) :=
    (bijective_zsmul_iff_of_linearEquiv_apply
      ((integralLocalHomologyNeighborhoodIso 3 p₀.val chartU.target chartU.open_target
        p₀.property).toLinearEquiv) cV cT rfl).symm
  let tr : LM ≃ₜ LM := Homeomorph.addRight (-(chartU x))
  have htr0 : tr (chartU x) = (0 : LM) := add_neg_cancel _
  let tauT : C(stdSimplex ℝ (Fin 4), LM) :=
    ⟨fun q => tr (tauU q), tr.continuous.comp tauU.continuous⟩
  have htauTne : ∀ (i : Fin 4) (q : stdSimplex ℝ (Fin 3)),
      tauT (orientedSimplexFace i q) ≠ tr (chartU x) := by
    intro i q hh
    exact htauUne i q (tr.injective hh)
  let zT' : integralSingularCoefficients ⟶
      (integralRelativeChains ({(tr (chartU x) : LM)}ᶜ : Set LM)).X 3 :=
    integralSimplexChainMap 3 tauT ≫ (cokernel.π (integralSingularChainMap
      (singularSubspaceInclusion ({(tr (chartU x) : LM)}ᶜ : Set LM)))).f 3
  have hzT' : (integralSimplexChainMap 3 tauT ≫ (cokernel.π (integralSingularChainMap
      (singularSubspaceInclusion ({(tr (chartU x) : LM)}ᶜ : Set LM)))).f 3) ≫
      (integralRelativeChains ({(tr (chartU x) : LM)}ᶜ : Set LM)).d 3 2 = 0 :=
    euclideanRelativeChain_boundary (X := LM) (tr (chartU x)) tauT htauTne
  have hchainT' : zT ≫ (integralRelativeChainMap (⟨tr, tr.continuous⟩ : C(LM, LM))
      (A := ({(chartU x : LM)}ᶜ : Set LM)) (B := ({(tr (chartU x) : LM)}ᶜ : Set LM))
      (fun _ hy => tr.injective.ne hy)).f 3 = zT' :=
    relativeChain_map_apply (⟨tr, tr.continuous⟩ : C(LM, LM)) (fun _ hy => tr.injective.ne hy)
      tauU tauT (by ext q; rfl)
  have hdefT : cT =
      (integralLocalHomologyNeighborhoodIso 3 p₀.val chartU.target chartU.open_target
        p₀.property).toLinearEquiv cV := rfl
  have hT' : (integralLocalHomologyHomeomorphIso 3 tr (chartU x)).toLinearEquiv cT =
      (((integralRelativeChains ({(tr (chartU x) : LM)}ᶜ : Set LM)).liftCycles zT' 2
        ((ComplexShape.down ℕ).next_eq' (by rfl)) hzT') ≫
        (integralRelativeChains ({(tr (chartU x) : LM)}ᶜ : Set LM)).homologyπ 3) (ULift.up 1) := by
    rw [hdefT, hT]
    exact integralLocalHomologyHomeomorphIso_hom_liftCycles tr (chartU x) zT hzT zT' hzT' hchainT'
  let cT' : ↑(integralLocalHomology 3 (tr (chartU x))) :=
    (integralLocalHomologyHomeomorphIso 3 tr (chartU x)).toLinearEquiv cT
  have hstepT' : Function.Bijective (fun z : ℤ => z • cT') ↔
      Function.Bijective (fun z : ℤ => z • cT) :=
    (bijective_zsmul_iff_of_linearEquiv_apply
      ((integralLocalHomologyHomeomorphIso 3 tr (chartU x)).toLinearEquiv) cT cT' rfl).symm
  let sc : LM ≃ₜ LM :=
    Homeomorph.smulOfNeZero (S.radius⁻¹) (inv_ne_zero (ne_of_gt S.radius_pos))
  let tauS : C(stdSimplex ℝ (Fin 4), LM) :=
    ⟨fun q => sc (tauT q), sc.continuous.comp tauT.continuous⟩
  have htauSne : ∀ (i : Fin 4) (q : stdSimplex ℝ (Fin 3)),
      tauS (orientedSimplexFace i q) ≠ sc (tr (chartU x)) := by
    intro i q hh
    exact htauTne i q (sc.injective hh)
  have hsc0 : (Homeomorph.smulOfNeZero (S.radius⁻¹) (inv_ne_zero (ne_of_gt S.radius_pos)) :
      LM ≃ₜ LM) (0 : LM) = S.radius⁻¹ • (0 : LM) := rfl
  have hzero : sc (tr (chartU x)) = (0 : LM) := by
    rw [htr0]
    change (Homeomorph.smulOfNeZero (S.radius⁻¹) (inv_ne_zero (ne_of_gt S.radius_pos)) :
      LM ≃ₜ LM) (0 : LM) = 0
    rw [hsc0]
    exact smul_zero _
  have htauS : tauS = liftedPositiveTetrahedron := by
    apply ContinuousMap.ext
    intro q
    change sc (tr (tauU q)) = (ULift.up (positiveTetrahedron q) : LM)
    rw [hchartU q]
    have htr : tr (ULift.up (S.chart x + S.radius • positiveTetrahedron q)) =
        (ULift.up (S.chart x + S.radius • positiveTetrahedron q + (-(S.chart x))) : LM) := rfl
    have hcancel : S.chart x + S.radius • positiveTetrahedron q + (-(S.chart x)) =
        S.radius • positiveTetrahedron q := by abel
    have hscT : sc (ULift.up (S.radius • positiveTetrahedron q)) =
        (ULift.up (S.radius⁻¹ • (S.radius • positiveTetrahedron q)) : LM) := rfl
    rw [htr, hcancel, hscT, smul_smul, inv_mul_cancel₀ (ne_of_gt S.radius_pos), one_smul]
  let zS : integralSingularCoefficients ⟶
      (integralRelativeChains ({(sc (tr (chartU x)) : LM)}ᶜ : Set LM)).X 3 :=
    integralSimplexChainMap 3 tauS ≫ (cokernel.π (integralSingularChainMap
      (singularSubspaceInclusion ({(sc (tr (chartU x)) : LM)}ᶜ : Set LM)))).f 3
  have hzS : (integralSimplexChainMap 3 tauS ≫ (cokernel.π (integralSingularChainMap
      (singularSubspaceInclusion ({(sc (tr (chartU x)) : LM)}ᶜ : Set LM)))).f 3) ≫
      (integralRelativeChains ({(sc (tr (chartU x)) : LM)}ᶜ : Set LM)).d 3 2 = 0 :=
    euclideanRelativeChain_boundary (X := LM) (sc (tr (chartU x))) tauS htauSne
  have hchainS : zT' ≫ (integralRelativeChainMap (⟨sc, sc.continuous⟩ : C(LM, LM))
      (A := ({(tr (chartU x) : LM)}ᶜ : Set LM)) (B := ({(sc (tr (chartU x)) : LM)}ᶜ : Set LM))
      (fun _ hy => sc.injective.ne hy)).f 3 = zS :=
    relativeChain_map_apply (⟨sc, sc.continuous⟩ : C(LM, LM)) (fun _ hy => sc.injective.ne hy)
      tauT tauS (by ext q; rfl)
  have hdefT' : cT' = (integralLocalHomologyHomeomorphIso 3 tr (chartU x)).toLinearEquiv cT := rfl
  have hS : (integralLocalHomologyHomeomorphIso 3 sc (tr (chartU x))).toLinearEquiv cT' =
      (((integralRelativeChains ({(sc (tr (chartU x)) : LM)}ᶜ : Set LM)).liftCycles zS 2
        ((ComplexShape.down ℕ).next_eq' (by rfl)) hzS) ≫
        (integralRelativeChains ({(sc (tr (chartU x)) : LM)}ᶜ : Set LM)).homologyπ 3) (ULift.up 1) := by
    rw [hdefT', hT']
    exact integralLocalHomologyHomeomorphIso_hom_liftCycles sc (tr (chartU x)) zT' hzT' zS hzS hchainS
  let cS : ↑(integralLocalHomology 3 (sc (tr (chartU x)))) :=
    (integralLocalHomologyHomeomorphIso 3 sc (tr (chartU x))).toLinearEquiv cT'
  have hstepS : Function.Bijective (fun z : ℤ => z • cS) ↔
      Function.Bijective (fun z : ℤ => z • cT') :=
    (bijective_zsmul_iff_of_linearEquiv_apply
      ((integralLocalHomologyHomeomorphIso 3 sc (tr (chartU x))).toLinearEquiv) cT' cS rfl).symm
  have hliftedSne : ∀ (i : Fin 4) (t : stdSimplex ℝ (Fin 3)),
      liftedPositiveTetrahedron (orientedSimplexFace i t) ≠ sc (tr (chartU x)) := by
    intro i t
    rw [← htauS]
    exact htauSne i t
  have hchainE : (integralSimplexChainMap 3 tauS ≫ (cokernel.π (integralSingularChainMap
      (singularSubspaceInclusion ({(sc (tr (chartU x)) : LM)}ᶜ : Set LM)))).f 3) =
      integralSimplexChainMap 3 liftedPositiveTetrahedron ≫ (cokernel.π (integralSingularChainMap
        (singularSubspaceInclusion ({(sc (tr (chartU x)) : LM)}ᶜ : Set LM)))).f 3 := by
    rw [htauS]
  have hcSraw : cS =
      (((integralRelativeChains ({(sc (tr (chartU x)) : LM)}ᶜ : Set LM)).liftCycles zS 2
        ((ComplexShape.down ℕ).next_eq' (by rfl)) hzS) ≫
        (integralRelativeChains ({(sc (tr (chartU x)) : LM)}ᶜ : Set LM)).homologyπ 3)
        (ULift.up 1) := hS
  have hclassS : cS =
      simplexLocalClass (sc (tr (chartU x))) liftedPositiveTetrahedron hliftedSne := by
    rw [hcSraw]
    unfold simplexLocalClass
    exact congrArg (fun k => k (ULift.up 1))
      (chainComplex_liftCycles_homologyπ_congr
        (K := integralRelativeChains ({(sc (tr (chartU x)) : LM)}ᶜ)) 2 _ _ _ _ hchainE)
  have hfinal : Function.Bijective (fun z : ℤ => z • cS) := by
    rw [hclassS]
    exact bijective_zsmul_simplexLocalClass_of_basepoint_eq hzero liftedPositiveTetrahedron hliftedSne
      (fun i t => liftedPositiveTetrahedron_face_ne_zero i t) h
  exact (hstepS.trans (hstepT'.trans (hstepT.trans (hstepV.trans hstepU)))).mp hfinal

end

theorem localOrientationClass_generator (o : TangentOrientationSection M) (x : M) :
    Function.Bijective (fun z : ℤ => z • localOrientationClass o x) := by
  sorry

variable [hT2 : T2Space M] [hCompact : CompactSpace M]
include hT2 hCompact

theorem exists_unique_fundamentalClass (o : TangentOrientationSection M) :
    ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x := by
  sorry

def fundamentalClass (o : TangentOrientationSection M) : IntegralHomology M 3 :=
  Classical.choose (exists_unique_fundamentalClass o)

theorem fundamentalClass_local (o : TangentOrientationSection M) (x : M) :
    absoluteToRelative M ({x}ᶜ) 3 (fundamentalClass o) = localOrientationClass o x :=
  (Classical.choose_spec (exists_unique_fundamentalClass o)).1 x

variable [hConnected : ConnectedSpace M]
include hConnected


theorem fundamentalClass_generator (o : TangentOrientationSection M) :
    Function.Bijective (fun z : ℤ => z • fundamentalClass o) := by
  sorry

omit hT2 hCompact hConnected in
theorem exists_unique_fundamentalClass_of_exists (o : TangentOrientationSection M)
    (h : ∃ z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x)
    (hinj : ∃ x : M, Function.Injective (absoluteToRelative M ({x}ᶜ) 3)) :
    ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x := by
  obtain ⟨z, hz⟩ := h
  refine ⟨z, hz, ?_⟩
  intro z' hz'
  obtain ⟨x, hx⟩ := hinj
  exact hx (by rw [hz, hz'])

omit hConnected in
theorem fundamentalClass_generator_of (o : TangentOrientationSection M) (x : M)
    (hlocal : Function.Bijective (fun z : ℤ => z • localOrientationClass o x))
    (hinj : Function.Injective (absoluteToRelative M ({x}ᶜ) 3)) :
    Function.Bijective (fun z : ℤ => z • fundamentalClass o) := by
  let A : IntegralHomology M 3 →ₗ[ℤ] LocalIntegralHomology M x 3 :=
    (absoluteToRelative M ({x}ᶜ) 3).hom
  have hA : ∀ z : ℤ, A (z • fundamentalClass o) = z • localOrientationClass o x := by
    intro z
    rw [map_zsmul, fundamentalClass_local]
  constructor
  · intro a b hab
    apply hlocal.injective
    have h := congrArg A hab
    rwa [hA, hA] at h
  · intro w
    obtain ⟨z, hz⟩ := hlocal.surjective (A w)
    exact ⟨z, hinj (hA z ▸ hz)⟩

def fundamentalClassEquiv (o : TangentOrientationSection M) :
    ℤ ≃ₗ[ℤ] IntegralHomology M 3 :=
  (AddEquiv.ofBijective
    ({ toFun := fun z : ℤ => z • fundamentalClass o
       map_zero' := zero_zsmul (fundamentalClass o)
       map_add' := fun z w => add_zsmul (fundamentalClass o) z w } :
      ℤ →+ IntegralHomology M 3)
    (fundamentalClass_generator o)).toIntLinearEquiv

@[simp] theorem fundamentalClassEquiv_one (o : TangentOrientationSection M) :
    fundamentalClassEquiv o 1 = fundamentalClass o := by
  change (1 : ℤ) • fundamentalClass o = fundamentalClass o
  exact one_smul ℤ (fundamentalClass o)

variable {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    [IsManifold ThreeModel ∞ N] [T2Space N] [CompactSpace N] [ConnectedSpace N]

def orientedDegree (oM : TangentOrientationSection M) (oN : TangentOrientationSection N)
    (f : C(M, N)) : ℤ :=
  Classical.choose ((fundamentalClass_generator oN).surjective
    (integralHomologyMap 3 f (fundamentalClass oM)))

omit hConnected in
theorem orientedDegree_spec (oM : TangentOrientationSection M) (oN : TangentOrientationSection N)
    (f : C(M, N)) :
    integralHomologyMap 3 f (fundamentalClass oM) =
      orientedDegree oM oN f • fundamentalClass oN :=
  (Classical.choose_spec ((fundamentalClass_generator oN).surjective
    (integralHomologyMap 3 f (fundamentalClass oM)))).symm

omit hConnected in
theorem orientedDegree_eq_iff (oM : TangentOrientationSection M) (oN : TangentOrientationSection N)
    (f : C(M, N)) (d : ℤ) :
    orientedDegree oM oN f = d ↔
      integralHomologyMap 3 f (fundamentalClass oM) = d • fundamentalClass oN := by
  rw [orientedDegree_spec]
  exact (fundamentalClass_generator oN).injective.eq_iff.symm

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
