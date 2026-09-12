import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Background
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChartSimplexBlend
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
