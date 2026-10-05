import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Tangent splitting along the actual zero section

The derivatives of fibre inclusions and the zero section give the vertical and base tangent
summands. Native bundle charts verify their bijectivity and continuity along continuous vectors.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.VectorBundle

variable {EB F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} [IB.Boundaryless]
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, NormedSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V IB]

variable (IB F V) in
def zeroSectionVerticalDerivative (b : B) :
    V b →L[ℝ] TangentSpace (IB.prod 𝓘(ℝ, F)) (zeroSection F V b) :=
  mfderiv 𝓘(ℝ, V b) (IB.prod 𝓘(ℝ, F)) (fun v : V b => (⟨b, v⟩ : TotalSpace F V)) 0

variable (IB F V) in
def zeroSectionTangentSplit (b : B) :
    (V b × TangentSpace IB b) →L[ℝ]
      TangentSpace (IB.prod 𝓘(ℝ, F)) (zeroSection F V b) :=
  (zeroSectionVerticalDerivative (IB := IB) (F := F) (V := V) b).comp
    (ContinuousLinearMap.fst ℝ (V b) EB) +
    (mfderiv IB (IB.prod 𝓘(ℝ, F)) (zeroSection F V) b).comp
      (ContinuousLinearMap.snd ℝ (V b) EB)

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ b, NormedSpace ℝ (V b)]
  [VectorBundle ℝ F V] in
private theorem zeroSection_mem_totalChart (b y : B)
    (he : y ∈ (trivializationAt F V b).baseSet) (hc : y ∈ (chartAt HB b).source) :
    zeroSection F V y ∈ (chartAt (ModelProd HB F) (zeroSection F V b)).source := by
  rw [FiberBundle.chartedSpace_chartAt, OpenPartialHomeomorph.trans_source]
  refine ⟨(trivializationAt F V b).mem_source.mpr he, ?_⟩
  simp only [Set.mem_preimage, OpenPartialHomeomorph.prod_source,
    OpenPartialHomeomorph.refl_source, Set.mem_prod, Set.mem_univ, and_true]
  change (trivializationAt F V b (zeroSection F V y)).1 ∈ (chartAt HB b).source
  rw [(trivializationAt F V b).coe_fst' he]
  exact hc

omit [FiniteDimensional ℝ F] [IB.Boundaryless] [IsManifold IB ∞ B]
  [∀ b, NormedSpace ℝ (V b)] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V IB] in
private theorem zeroSection_extChartAt_apply (b y : B) (v : V y)
    (he : y ∈ (trivializationAt F V b).baseSet) :
    extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F V b) (⟨y, v⟩ : TotalSpace F V) =
      (extChartAt IB b y, (trivializationAt F V b ⟨y, v⟩).2) := by
  rw [FiberBundle.extChartAt]
  simp only [PartialEquiv.coe_trans, Function.comp_apply, PartialEquiv.prod_coe,
    PartialEquiv.refl_coe, id]
  change (extChartAt IB b (trivializationAt F V b ⟨y, v⟩).1,
    (trivializationAt F V b ⟨y, v⟩).2) = _
  rw [(trivializationAt F V b).coe_fst' he]

omit [FiniteDimensional ℝ F] [IB.Boundaryless] [IsManifold IB ∞ B]
  [ContMDiffVectorBundle ∞ F V IB] in
private theorem contMDiff_fibreInclusion (y : B) :
    ContMDiff 𝓘(ℝ, V y) (IB.prod 𝓘(ℝ, F)) ∞
      (fun v : V y => (⟨y, v⟩ : TotalSpace F V)) := by
  intro v
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_const, ?_⟩
  have he : y ∈ (trivializationAt F V y).baseSet := mem_baseSet_trivializationAt F V y
  have hf : (fun w : V y => (trivializationAt F V y ⟨y, w⟩).2) =
      (trivializationAt F V y).continuousLinearMapAt ℝ y := by
    funext w
    exact ((trivializationAt F V y).continuousLinearMapAt_apply_of_mem ℝ he w).symm
  rw [hf]
  exact (trivializationAt F V y).continuousLinearMapAt ℝ y |>.contMDiff.contMDiffAt

omit [FiniteDimensional ℝ F] [IB.Boundaryless] in
theorem zeroSectionVerticalDerivative_chart (b y : B) (v : V y)
    (he : y ∈ (trivializationAt F V b).baseSet) (hc : y ∈ (chartAt HB b).source) :
    mfderiv (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, EB × F)
      (extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F V b)) (zeroSection F V y)
      (zeroSectionVerticalDerivative (F := F) (IB := IB) (V := V) y v) =
      (0, (trivializationAt F V b).continuousLinearMapAt ℝ y v) := by
  let ι : V y → TotalSpace F V := fun w => ⟨y, w⟩
  let L := (trivializationAt F V b).continuousLinearMapAt ℝ y
  have hι : MDifferentiableAt 𝓘(ℝ, V y) (IB.prod 𝓘(ℝ, F)) ι 0 :=
    (contMDiff_fibreInclusion y 0).mdifferentiableAt (by simp)
  have hm := zeroSection_mem_totalChart b y he hc
  have hd := mdifferentiableAt_extChartAt (I := IB.prod 𝓘(ℝ, F)) hm
  have heq : (extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F V b) ∘ ι) =
      fun w => (extChartAt IB b y, L w) := by
    funext w
    rw [Function.comp_apply, zeroSection_extChartAt_apply b y w he]
    exact congrArg (Prod.mk (extChartAt IB b y))
      ((trivializationAt F V b).continuousLinearMapAt_apply_of_mem ℝ he w).symm
  have hD := (hasFDerivAt_const (extChartAt IB b y) (0 : V y)).prodMk L.hasFDerivAt
  have hf := mfderiv_comp (I := 𝓘(ℝ, V y))
    (I' := IB.prod 𝓘(ℝ, F)) (I'' := 𝓘(ℝ, EB × F)) (x := (0 : V y)) hd hι
  have hval := congrArg (fun A => A v) hf
  rw [heq, hD.hasMFDerivAt.mfderiv] at hval
  change (0, L v) =
    mfderiv (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, EB × F)
      (extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F V b)) (zeroSection F V y)
      (zeroSectionVerticalDerivative (F := F) (IB := IB) (V := V) y v) at hval
  exact hval.symm

omit [FiniteDimensional ℝ F] [IB.Boundaryless] in
theorem zeroSectionDerivative_chart (b y : B) (w : TangentSpace IB y)
    (he : y ∈ (trivializationAt F V b).baseSet) (hc : y ∈ (chartAt HB b).source) :
    mfderiv (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, EB × F)
      (extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F V b)) (zeroSection F V y)
      (mfderiv IB (IB.prod 𝓘(ℝ, F)) (zeroSection F V) y w) =
      (mfderiv IB 𝓘(ℝ, EB) (extChartAt IB b) y w, 0) := by
  let ψ := extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F V b)
  have hz : MDifferentiableAt IB (IB.prod 𝓘(ℝ, F)) (zeroSection F V) y :=
    (contMDiff_zeroSection (F := F) (IB := IB) (n := ∞) ℝ V y).mdifferentiableAt (by simp)
  have hm := zeroSection_mem_totalChart b y he hc
  have hd := mdifferentiableAt_extChartAt (I := IB.prod 𝓘(ℝ, F)) hm
  have heq : (ψ ∘ zeroSection F V) =ᶠ[𝓝 y]
      fun x => (extChartAt IB b x, (0 : F)) := by
    filter_upwards [(trivializationAt F V b).open_baseSet.mem_nhds he] with x hx
    change extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F V b)
      (⟨x, (0 : V x)⟩ : TotalSpace F V) = (extChartAt IB b x, 0)
    rw [zeroSection_extChartAt_apply (IB := IB) b x (0 : V x) hx]
    exact congrArg (Prod.mk (extChartAt IB b x))
      (congrArg Prod.snd ((trivializationAt F V b).zeroSection ℝ hx))
  have hbase := mdifferentiableAt_extChartAt (I := IB) hc
  have hconst : HasMFDerivAt IB 𝓘(ℝ, F) (fun x : B => (0 : F)) y 0 :=
    hasMFDerivAt_const (0 : F) y
  have ht := hbase.hasMFDerivAt.prodMk hconst
  have hf := mfderiv_comp (I := IB) (I' := IB.prod 𝓘(ℝ, F))
    (I'' := 𝓘(ℝ, EB × F)) (x := y) hd hz
  have hval := congrArg (fun A => A w) hf
  rw [heq.mfderiv_eq] at hval
  change mfderiv IB 𝓘(ℝ, EB × F) (fun x => (extChartAt IB b x, (0 : F))) y w =
    mfderiv (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, EB × F)
      (extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F V b)) (zeroSection F V y)
      (mfderiv IB (IB.prod 𝓘(ℝ, F)) (zeroSection F V) y w) at hval
  have ht' : HasMFDerivAt IB 𝓘(ℝ, EB × F)
      (fun x => (extChartAt IB b x, (0 : F))) y
      ((mfderiv IB 𝓘(ℝ, EB) (extChartAt IB b) y).prod 0) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    convert! ht using 1
  have htval := congrArg (fun A => A w) ht'.mfderiv
  have htval' : mfderiv IB 𝓘(ℝ, EB × F)
      (fun x => (extChartAt IB b x, (0 : F))) y w =
      (mfderiv IB 𝓘(ℝ, EB) (extChartAt IB b) y w, 0) := by
    convert! htval using 1
  exact hval.symm.trans htval'

omit [FiniteDimensional ℝ F] [IB.Boundaryless] in
theorem zeroSectionTangentSplit_chart (b y : B) (v : V y) (w : TangentSpace IB y)
    (he : y ∈ (trivializationAt F V b).baseSet) (hc : y ∈ (chartAt HB b).source) :
    mfderiv (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, EB × F)
      (extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F V b)) (zeroSection F V y)
      (zeroSectionTangentSplit (F := F) (IB := IB) (V := V) y (v, w)) =
      (mfderiv IB 𝓘(ℝ, EB) (extChartAt IB b) y w,
        (trivializationAt F V b).continuousLinearMapAt ℝ y v) := by
  change (mfderiv (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, EB × F)
    (extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F V b)) (zeroSection F V y))
    ((zeroSectionVerticalDerivative (F := F) (IB := IB) (V := V) y v) +
    mfderiv IB (IB.prod 𝓘(ℝ, F)) (zeroSection F V) y w) = _
  rw [map_add, zeroSectionVerticalDerivative_chart b y v he hc,
    zeroSectionDerivative_chart b y w he hc]
  exact Prod.ext (zero_add _) (add_zero _)

omit [FiniteDimensional ℝ F] [IB.Boundaryless] in
theorem zeroSectionTangentSplit_apply (b : B) (v : V b) (w : TangentSpace IB b) :
    zeroSectionTangentSplit (F := F) (IB := IB) (V := V) b (v, w) =
      (w, (trivializationAt F V b).continuousLinearMapAt ℝ b v) := by
  have h := zeroSectionTangentSplit_chart b b v w
    (mem_baseSet_trivializationAt F V b) (mem_chart_source HB b)
  rw [mfderiv_extChartAt_self, mfderiv_extChartAt_self] at h
  exact h

omit [FiniteDimensional ℝ F] [IB.Boundaryless] in
theorem zeroSectionTangentSplit_bijective (b : B) :
    Function.Bijective (zeroSectionTangentSplit (F := F) (IB := IB) (V := V) b) := by
  let L := (trivializationAt F V b).continuousLinearEquivAt ℝ b
    (mem_baseSet_trivializationAt F V b)
  have heq : (zeroSectionTangentSplit (F := F) (IB := IB) (V := V) b :
      (V b × EB) → EB × F) = fun p => (p.2, L p.1) := by
    funext p
    rw [zeroSectionTangentSplit_apply]
    exact Prod.ext rfl (congrArg (fun A : V b →L[ℝ] F => A p.1)
      (Trivialization.coe_continuousLinearEquivAt_eq' (trivializationAt F V b)
        (mem_baseSet_trivializationAt F V b)).symm)
  rw [heq]
  exact (L.toEquiv.prodCongr (Equiv.refl EB) |>.trans (Equiv.prodComm F EB)).bijective

omit [FiniteDimensional ℝ F] [IB.Boundaryless] in
theorem continuous_zeroSectionVerticalDerivative {X : Type*} [TopologicalSpace X]
    (β : X → B) (ν : ∀ x, V (β x)) (hβ : Continuous β)
    (hν : Continuous (fun x => (⟨β x, ν x⟩ : TotalSpace F V))) :
    Continuous (fun x => (⟨zeroSection F V (β x),
      zeroSectionVerticalDerivative (F := F) (IB := IB) (V := V) (β x) (ν x)⟩ :
        TangentBundle (IB.prod 𝓘(ℝ, F)) (TotalSpace F V))) := by
  let IT := IB.prod 𝓘(ℝ, F)
  let s : X → TangentBundle IT (TotalSpace F V) := fun x =>
    ⟨zeroSection F V (β x),
      zeroSectionVerticalDerivative (F := F) (IB := IB) (V := V) (β x) (ν x)⟩
  change Continuous s
  apply continuous_iff_continuousAt.mpr
  intro x₀
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨((contMDiff_zeroSection (F := F) (IB := IB) (n := ∞) ℝ V).continuous.comp
    hβ).continuousAt, ?_⟩
  let e := trivializationAt F V (β x₀)
  have he : β x₀ ∈ e.baseSet := mem_baseSet_trivializationAt F V (β x₀)
  have hc : β x₀ ∈ (chartAt HB (β x₀)).source := mem_chart_source HB (β x₀)
  have hcoord : ContinuousAt (fun x => (e (⟨β x, ν x⟩ : TotalSpace F V)).2) x₀ :=
    (e.continuousOn.continuousAt (e.open_source.mem_nhds (e.mem_source.mpr he))).snd.comp
      hν.continuousAt
  have hbase : ∀ᶠ x in 𝓝 x₀, β x ∈ e.baseSet ∧
      β x ∈ (chartAt HB (β x₀)).source :=
    hβ.continuousAt.preimage_mem_nhds
      ((e.open_baseSet.inter (chartAt HB (β x₀)).open_source).mem_nhds ⟨he, hc⟩)
  have heq : (fun x => (trivializationAt (EB × F) (TangentSpace IT)
      (s x₀).proj (s x)).2) =ᶠ[𝓝 x₀] fun x => (0, (e ⟨β x, ν x⟩).2) := by
    filter_upwards [hbase] with x hx
    have hmem := zeroSection_mem_totalChart (β x₀) (β x) hx.1 hx.2
    have ht : zeroSection F V (β x) ∈
        (trivializationAt (EB × F) (TangentSpace IT) (zeroSection F V (β x₀))).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact hmem
    change (trivializationAt (EB × F) (TangentSpace IT) (zeroSection F V (β x₀))
      ⟨zeroSection F V (β x),
        zeroSectionVerticalDerivative (F := F) (IB := IB) (V := V) (β x) (ν x)⟩).2 = _
    let eT := trivializationAt (EB × F) (TangentSpace IT) (zeroSection F V (β x₀))
    rw [← Trivialization.continuousLinearMapAt_apply_of_mem ℝ eT ht,
      TangentBundle.continuousLinearMapAt_trivializationAt hmem]
    exact (zeroSectionVerticalDerivative_chart (IB := IB)
      (β x₀) (β x) (ν x) hx.1 hx.2).trans
      (congrArg (Prod.mk (0 : EB)) (e.continuousLinearMapAt_apply_of_mem ℝ hx.1 (ν x)))
  exact (continuousAt_const.prodMk hcoord).congr heq.symm

theorem trivialLine_zeroSectionTangentSplit_bijective :
    Function.Bijective (zeroSectionTangentSplit (IB := 𝓘(ℝ, ℝ))
      (F := ℝ) (V := Bundle.Trivial ℝ ℝ) 0) :=
  zeroSectionTangentSplit_bijective 0

end DifferentialGeometry.Topology.VectorBundle
