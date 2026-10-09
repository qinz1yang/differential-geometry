import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.AssemblyReduction
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SeamTransition
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientationPrelude
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientationTopology
import DifferentialGeometry.Topology.Manifold.SmoothOrientationComposition
import DifferentialGeometry.Topology.Manifold.SmoothOrientationComparison
import DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible

set_option autoImplicit false
noncomputable section
open Set Function Manifold Topology TopologicalSpace Metric
open scoped Manifold ContDiff Topology

namespace OrientationAssembly
open DifferentialGeometry.Topology ConnectedSumQuotient
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Topology.OrientationAssembly

universe u v

variable {M : ClosedOrientedManifold.{u} 3} {N : ClosedOrientedManifold.{v} 3}

variable (c : OrientedBallChart M) (d : OrientedBallChart N)
  (aD : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere)

variable [ChartedSpace csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)]
variable [IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)]

section OrientationIndexBridge

variable {ι : Type*}
variable {R M₁ M₂ M₃ : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
variable [AddCommGroup M₃] [Module R M₃]

theorem orientation_map_map_trans (e : M₁ ≃ₗ[R] M₂) (f : M₂ ≃ₗ[R] M₃)
    (o : Orientation R M₁ ι) :
    Orientation.map ι f (Orientation.map ι e o) = Orientation.map ι (e.trans f) o := by
  induction o using Module.Ray.ind R with
  | h v hv =>
    have hfun2 : AlternatingMap.compLinearMap
          (AlternatingMap.compLinearMap v (e.symm : M₂ →ₗ[R] M₁)) (f.symm : M₃ →ₗ[R] M₂) =
        AlternatingMap.compLinearMap v (((e.trans f).symm : M₃ →ₗ[R] M₁)) := by
      rw [LinearEquiv.trans_symm]
      ext g
      change v (fun i => e.symm (f.symm (g i))) = v (fun i => e.symm (f.symm (g i)))
      rfl
    simp only [Orientation.map_apply, hfun2]

theorem orientation_map_symm_map_self (e : M₁ ≃ₗ[R] M₂) (o : Orientation R M₂ ι) :
    Orientation.map ι e (Orientation.map ι e.symm o) = o := by
  rw [orientation_map_map_trans e.symm e o]
  have h : e.symm.trans e = LinearEquiv.refl R M₂ := LinearEquiv.ext (fun v => e.apply_symm_apply v)
  rw [h, Orientation.map_refl]
  rfl

end OrientationIndexBridge

section OrientationReindexBridge

variable {R M N : Type*} [CommRing R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

omit [PartialOrder R] [IsStrictOrderedRing R] in
theorem alternatingMap_domDomCongr_compLinearMap {ι ι' : Type*} (e : ι ≃ ι')
    (f : M ≃ₗ[R] N) (v : M [⋀^ι]→ₗ[R] R) :
    AlternatingMap.domDomCongr e (v.compLinearMap (f.symm : N →ₗ[R] M)) =
      AlternatingMap.compLinearMap (AlternatingMap.domDomCongr e v) (f.symm : N →ₗ[R] M) := by
  ext g
  change v (fun i => f.symm (g (e i))) = v (fun i => f.symm (g (e i)))
  rfl

theorem orientation_reindex_map_comm {ι ι' : Type*} (e : ι ≃ ι') (f : M ≃ₗ[R] N)
    (o : Orientation R M ι) :
    Orientation.reindex R N e (Orientation.map ι f o) =
      Orientation.map ι' f (Orientation.reindex R M e o) := by
  induction o using Module.Ray.ind R with
  | h v hv =>
    have hfun : AlternatingMap.domDomCongr e (v.compLinearMap (f.symm : N →ₗ[R] M)) =
        AlternatingMap.compLinearMap (AlternatingMap.domDomCongr e v) (f.symm : N →ₗ[R] M) :=
      alternatingMap_domDomCongr_compLinearMap e f v
    simp only [Orientation.map_apply, Orientation.reindex_apply, hfun]

end OrientationReindexBridge
abbrev AtlasLeft (c : OrientedBallChart M) (d : OrientedBallChart N)
    (aD : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere)
    [ChartedSpace csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)] : Prop :=
  ∀ (f : OpenPartialHomeomorph M.Carrier csModel), f ∈ atlas csModel M.Carrier →
    (leftChart c.toBallChart d.toBallChart aD.toHomeomorph hn3 f).symm ∈
      atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)

abbrev AtlasRight (c : OrientedBallChart M) (d : OrientedBallChart N)
    (aD : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere)
    [ChartedSpace csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)] : Prop :=
  ∀ (g : OpenPartialHomeomorph N.Carrier csModel), g ∈ atlas csModel N.Carrier →
    (rightChart c.toBallChart d.toBallChart aD.toHomeomorph hn3 g).symm ∈
      atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)


def csIdx : Fin 3 ≃ Fin (Module.finrank ℝ csModel) := finCongr (by simp)

def stdOrientation (x : csModel) :
    Orientation ℝ (TangentSpace 𝓘(ℝ, csModel) x) (Fin 3) :=
  ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.map
    (NormedSpace.fromTangentSpace x).symm.toLinearEquiv).orientation

theorem stdOrientation_eq (x y : csModel) : stdOrientation x = stdOrientation y := rfl

def stdOrientationModel : Orientation ℝ csModel (Fin (Module.finrank ℝ csModel)) :=
  Orientation.reindex ℝ csModel csIdx (stdOrientation 0)

theorem stdOrientationModel_eq_reindex (x : csModel) :
    stdOrientationModel = Orientation.reindex ℝ csModel csIdx (stdOrientation x) := rfl
theorem isOpen_range_interiorLeft' (hLq : AtlasLeft c d aD) :
    IsOpen (Set.range (interiorLeft c.toBallChart d.toBallChart aD)) :=
  (interiorLeft_isLocalDiffeomorph c.toBallChart d.toBallChart aD hLq).isOpen_range

theorem isOpen_range_interiorRight' (hRq : AtlasRight c d aD) :
    IsOpen (Set.range (interiorRight c.toBallChart d.toBallChart aD)) :=
  (interiorRight_isLocalDiffeomorph c.toBallChart d.toBallChart aD hRq).isOpen_range

def qL (hLq : AtlasLeft c d aD) :
    TopologicalSpace.Opens (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
  ⟨Set.range (interiorLeft c.toBallChart d.toBallChart aD),
    isOpen_range_interiorLeft' c d aD hLq⟩

def qR (hRq : AtlasRight c d aD) :
    TopologicalSpace.Opens (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
  ⟨Set.range (interiorRight c.toBallChart d.toBallChart aD),
    isOpen_range_interiorRight' c d aD hRq⟩

def qS : TopologicalSpace.Opens (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
  ⟨(seamChartX c.toBallChart d.toBallChart aD.toHomeomorph).source,
    (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph).open_source⟩

def gL (hLq : AtlasLeft c d aD) (x : qL c d aD hLq) : c.toBallChart.interior :=
  Classical.choose x.2

theorem gL_spec (hLq : AtlasLeft c d aD) (x : qL c d aD hLq) :
    interiorLeft c.toBallChart d.toBallChart aD (gL c d aD hLq x)
      = (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
  Classical.choose_spec x.2

def gR (hRq : AtlasRight c d aD) (x : qR c d aD hRq) : d.toBallChart.interior :=
  Classical.choose x.2

theorem gR_spec (hRq : AtlasRight c d aD) (x : qR c d aD hRq) :
    interiorRight c.toBallChart d.toBallChart aD (gR c d aD hRq x)
      = (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
  Classical.choose_spec x.2

theorem gL_apply (hLq : AtlasLeft c d aD) (u : c.toBallChart.interior) :
    gL c d aD hLq ⟨interiorLeft c.toBallChart d.toBallChart aD u, ⟨u, rfl⟩⟩ = u :=
  interiorLeft_injective c.toBallChart d.toBallChart aD
    (by rw [gL_spec])

theorem gR_apply (hRq : AtlasRight c d aD) (v : d.toBallChart.interior) :
    gR c d aD hRq ⟨interiorRight c.toBallChart d.toBallChart aD v, ⟨v, rfl⟩⟩ = v :=
  interiorRight_injective c.toBallChart d.toBallChart aD
    (by rw [gR_spec])

theorem gL_eventuallyEq_localInverse (hLq : AtlasLeft c d aD) (x : qL c d aD hLq) :
    gL c d aD hLq =ᶠ[𝓝 x]
      (fun y : qL c d aD hLq =>
        (interiorLeft_isLocalDiffeomorph c.toBallChart d.toBallChart aD hLq
          (gL c d aD hLq x)).localInverse ↑y) := by
  let hf := interiorLeft_isLocalDiffeomorph c.toBallChart d.toBallChart aD hLq (gL c d aD hLq x)
  have hx : interiorLeft c.toBallChart d.toBallChart aD (gL c d aD hLq x)
      = (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
    gL_spec c d aD hLq x
  have hmem : (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)
      ∈ hf.localInverse.source := by
    rw [← hx]
    exact hf.localInverse_mem_source
  refine Filter.eventuallyEq_of_mem
    ((continuous_subtype_val
      (X := ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)).continuousAt.preimage_mem_nhds
      (hf.localInverse.open_source.mem_nhds hmem)) ?_
  intro y hy
  have h1 : interiorLeft c.toBallChart d.toBallChart aD (gL c d aD hLq y)
      = (y : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
    gL_spec c d aD hLq y
  have h2 : interiorLeft c.toBallChart d.toBallChart aD (hf.localInverse ↑y)
      = (y : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
    hf.localInverse_right_inv hy
  exact interiorLeft_injective c.toBallChart d.toBallChart aD (h1.trans h2.symm)

theorem gR_eventuallyEq_localInverse (hRq : AtlasRight c d aD) (x : qR c d aD hRq) :
    gR c d aD hRq =ᶠ[𝓝 x]
      (fun y : qR c d aD hRq =>
        (interiorRight_isLocalDiffeomorph c.toBallChart d.toBallChart aD hRq
          (gR c d aD hRq x)).localInverse ↑y) := by
  let hf := interiorRight_isLocalDiffeomorph c.toBallChart d.toBallChart aD hRq (gR c d aD hRq x)
  have hx : interiorRight c.toBallChart d.toBallChart aD (gR c d aD hRq x)
      = (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
    gR_spec c d aD hRq x
  have hmem : (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)
      ∈ hf.localInverse.source := by
    rw [← hx]
    exact hf.localInverse_mem_source
  refine Filter.eventuallyEq_of_mem
    ((continuous_subtype_val
      (X := ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)).continuousAt.preimage_mem_nhds
      (hf.localInverse.open_source.mem_nhds hmem)) ?_
  intro y hy
  have h1 : interiorRight c.toBallChart d.toBallChart aD (gR c d aD hRq y)
      = (y : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
    gR_spec c d aD hRq y
  have h2 : interiorRight c.toBallChart d.toBallChart aD (hf.localInverse ↑y)
      = (y : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
    hf.localInverse_right_inv hy
  exact interiorRight_injective c.toBallChart d.toBallChart aD (h1.trans h2.symm)

theorem contMDiffAt_gL (hLq : AtlasLeft c d aD) (x : qL c d aD hLq) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (gL c d aD hLq) x := by
  have hx : interiorLeft c.toBallChart d.toBallChart aD (gL c d aD hLq x)
      = (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
    gL_spec c d aD hLq x
  have hfinv : ContMDiffAt (𝓡 3) (𝓡 3) ∞
      (interiorLeft_isLocalDiffeomorph c.toBallChart d.toBallChart aD hLq
        (gL c d aD hLq x)).localInverse
      (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
    hx ▸ (interiorLeft_isLocalDiffeomorph c.toBallChart d.toBallChart aD hLq
      (gL c d aD hLq x)).contMDiffAt_localInverse
  refine (hfinv.comp x contMDiff_subtype_val.contMDiffAt).congr_of_eventuallyEq ?_
  exact gL_eventuallyEq_localInverse c d aD hLq x

theorem contMDiff_gL (hLq : AtlasLeft c d aD) : ContMDiff (𝓡 3) (𝓡 3) ∞ (gL c d aD hLq) :=
  fun x => contMDiffAt_gL c d aD hLq x

theorem contMDiffAt_gR (hRq : AtlasRight c d aD) (x : qR c d aD hRq) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (gR c d aD hRq) x := by
  have hx : interiorRight c.toBallChart d.toBallChart aD (gR c d aD hRq x)
      = (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
    gR_spec c d aD hRq x
  have hfinv : ContMDiffAt (𝓡 3) (𝓡 3) ∞
      (interiorRight_isLocalDiffeomorph c.toBallChart d.toBallChart aD hRq
        (gR c d aD hRq x)).localInverse
      (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
    hx ▸ (interiorRight_isLocalDiffeomorph c.toBallChart d.toBallChart aD hRq
      (gR c d aD hRq x)).contMDiffAt_localInverse
  refine (hfinv.comp x contMDiff_subtype_val.contMDiffAt).congr_of_eventuallyEq ?_
  exact gR_eventuallyEq_localInverse c d aD hRq x

theorem contMDiff_gR (hRq : AtlasRight c d aD) : ContMDiff (𝓡 3) (𝓡 3) ∞ (gR c d aD hRq) :=
  fun x => contMDiffAt_gR c d aD hRq x


section ChainRules

theorem mfderiv_IL_comp_gL (hLq : AtlasLeft c d aD) (x : qL c d aD hLq) :
    (mfderiv (𝓡 3) (𝓡 3) (interiorLeft c.toBallChart d.toBallChart aD) (gL c d aD hLq x)).comp
      (mfderiv (𝓡 3) (𝓡 3) (gL c d aD hLq) x) = ContinuousLinearMap.id ℝ csModel := by
  have hdiffIL : MDifferentiableAt (𝓡 3) (𝓡 3) (interiorLeft c.toBallChart d.toBallChart aD)
      (gL c d aD hLq x) :=
    ((interiorLeft_isLocalDiffeomorph c.toBallChart d.toBallChart aD hLq)
      (gL c d aD hLq x)).mdifferentiableAt (show (∞ : ℕ∞ω) ≠ 0 by simp)
  have hdiffgL : MDifferentiableAt (𝓡 3) (𝓡 3) (gL c d aD hLq) x :=
    (contMDiffAt_gL c d aD hLq x).mdifferentiableAt (show (∞ : ℕ∞ω) ≠ 0 by simp)
  have hcomp := mfderiv_comp (x := x) (f := (gL c d aD hLq))
    (g := (interiorLeft c.toBallChart d.toBallChart aD)) hdiffIL hdiffgL
  have heq : (interiorLeft c.toBallChart d.toBallChart aD ∘ gL c d aD hLq) =
      (Subtype.val : qL c d aD hLq →
        ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) := by
    funext y
    exact gL_spec c d aD hLq y
  rw [heq, DifferentialGeometry.mfderiv_subtype_val] at hcomp
  exact hcomp.symm

theorem mfderiv_IR_comp_gR (hRq : AtlasRight c d aD) (x : qR c d aD hRq) :
    (mfderiv (𝓡 3) (𝓡 3) (interiorRight c.toBallChart d.toBallChart aD) (gR c d aD hRq x)).comp
      (mfderiv (𝓡 3) (𝓡 3) (gR c d aD hRq) x) = ContinuousLinearMap.id ℝ csModel := by
  have hdiffIR : MDifferentiableAt (𝓡 3) (𝓡 3) (interiorRight c.toBallChart d.toBallChart aD)
      (gR c d aD hRq x) :=
    ((interiorRight_isLocalDiffeomorph c.toBallChart d.toBallChart aD hRq)
      (gR c d aD hRq x)).mdifferentiableAt (show (∞ : ℕ∞ω) ≠ 0 by simp)
  have hdiffgR : MDifferentiableAt (𝓡 3) (𝓡 3) (gR c d aD hRq) x :=
    (contMDiffAt_gR c d aD hRq x).mdifferentiableAt (show (∞ : ℕ∞ω) ≠ 0 by simp)
  have hcomp := mfderiv_comp (x := x) (f := (gR c d aD hRq))
    (g := (interiorRight c.toBallChart d.toBallChart aD)) hdiffIR hdiffgR
  have heq : (interiorRight c.toBallChart d.toBallChart aD ∘ gR c d aD hRq) =
      (Subtype.val : qR c d aD hRq →
        ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) := by
    funext y
    exact gR_spec c d aD hRq y
  rw [heq, DifferentialGeometry.mfderiv_subtype_val] at hcomp
  exact hcomp.symm

def leftDifferential (hLq : AtlasLeft c d aD) (x : qL c d aD hLq) :
    TangentSpace (𝓡 3) (interiorLeft c.toBallChart d.toBallChart aD (gL c d aD hLq x)) ≃L[ℝ]
      TangentSpace (𝓡 3) (gL c d aD hLq x) where
  toFun := mfderiv (𝓡 3) (𝓡 3) (gL c d aD hLq) x
  invFun := mfderiv (𝓡 3) (𝓡 3) (interiorLeft c.toBallChart d.toBallChart aD) (gL c d aD hLq x)
  left_inv := by
    intro v
    exact DFunLike.congr_fun (mfderiv_IL_comp_gL c d aD hLq x) v
  right_inv := by
    intro w
    have hAB := mfderiv_IL_comp_gL c d aD hLq x
    have hinj : Function.Injective
        (mfderiv (𝓡 3) (𝓡 3) (interiorLeft c.toBallChart d.toBallChart aD) (gL c d aD hLq x)) := by
      have h := (((interiorLeft_isLocalDiffeomorph c.toBallChart d.toBallChart aD hLq)
        (gL c d aD hLq x)).mfderivToContinuousLinearEquiv
        (show (∞ : ℕ∞ω) ≠ 0 by simp)).injective
      exact h
    exact hinj (DFunLike.congr_fun hAB _)
  map_add' := (mfderiv (𝓡 3) (𝓡 3) (gL c d aD hLq) x).map_add
  map_smul' := (mfderiv (𝓡 3) (𝓡 3) (gL c d aD hLq) x).map_smul
  continuous_toFun := (mfderiv (𝓡 3) (𝓡 3) (gL c d aD hLq) x).cont
  continuous_invFun :=
    (mfderiv (𝓡 3) (𝓡 3) (interiorLeft c.toBallChart d.toBallChart aD)
      (gL c d aD hLq x)).cont

theorem mfderiv_gL_eq_leftDifferential (hLq : AtlasLeft c d aD) (x : qL c d aD hLq) :
    mfderiv (𝓡 3) (𝓡 3) (gL c d aD hLq) x
      = (leftDifferential c d aD hLq x).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem bijective_mfderiv_gL (hLq : AtlasLeft c d aD) (x : qL c d aD hLq) :
    Function.Bijective (mfderiv (𝓡 3) (𝓡 3) (gL c d aD hLq) x) := by
  rw [mfderiv_gL_eq_leftDifferential c d aD hLq x]
  exact (leftDifferential c d aD hLq x).bijective

def rightDifferential (hRq : AtlasRight c d aD) (x : qR c d aD hRq) :
    TangentSpace (𝓡 3) (interiorRight c.toBallChart d.toBallChart aD (gR c d aD hRq x)) ≃L[ℝ]
      TangentSpace (𝓡 3) (gR c d aD hRq x) where
  toFun := mfderiv (𝓡 3) (𝓡 3) (gR c d aD hRq) x
  invFun := mfderiv (𝓡 3) (𝓡 3) (interiorRight c.toBallChart d.toBallChart aD) (gR c d aD hRq x)
  left_inv := by
    intro v
    exact DFunLike.congr_fun (mfderiv_IR_comp_gR c d aD hRq x) v
  right_inv := by
    intro w
    have hAB := mfderiv_IR_comp_gR c d aD hRq x
    have hinj : Function.Injective
        (mfderiv (𝓡 3) (𝓡 3) (interiorRight c.toBallChart d.toBallChart aD) (gR c d aD hRq x)) := by
      have h := (((interiorRight_isLocalDiffeomorph c.toBallChart d.toBallChart aD hRq)
        (gR c d aD hRq x)).mfderivToContinuousLinearEquiv
        (show (∞ : ℕ∞ω) ≠ 0 by simp)).injective
      exact h
    exact hinj (DFunLike.congr_fun hAB _)
  map_add' := (mfderiv (𝓡 3) (𝓡 3) (gR c d aD hRq) x).map_add
  map_smul' := (mfderiv (𝓡 3) (𝓡 3) (gR c d aD hRq) x).map_smul
  continuous_toFun := (mfderiv (𝓡 3) (𝓡 3) (gR c d aD hRq) x).cont
  continuous_invFun :=
    (mfderiv (𝓡 3) (𝓡 3) (interiorRight c.toBallChart d.toBallChart aD)
      (gR c d aD hRq x)).cont

theorem mfderiv_gR_eq_rightDifferential (hRq : AtlasRight c d aD) (x : qR c d aD hRq) :
    mfderiv (𝓡 3) (𝓡 3) (gR c d aD hRq) x
      = (rightDifferential c d aD hRq x).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem bijective_mfderiv_gR (hRq : AtlasRight c d aD) (x : qR c d aD hRq) :
    Function.Bijective (mfderiv (𝓡 3) (𝓡 3) (gR c d aD hRq) x) := by
  rw [mfderiv_gR_eq_rightDifferential c d aD hRq x]
  exact (rightDifferential c d aD hRq x).bijective

end ChainRules

section Pieces

theorem finrank_csModel : Module.finrank ℝ csModel = 3 := by simp

def chartPartialDiffeomorph
    (e : OpenPartialHomeomorph (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) csModel)
    (he : e ∈ atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)) :
    PartialDiffeomorph (𝓡 3) (𝓡 3)
      (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) csModel ∞ where
  toPartialEquiv := e.toPartialEquiv
  open_source := e.open_source
  open_target := e.open_target
  contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he)
  contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he)

def reindexManifoldOrientation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H M' : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) [TopologicalSpace M'] [ChartedSpace H M']
    [IsManifold I ∞ M'] {n m : ℕ} (e : Fin n ≃ Fin m)
    (o : DifferentialGeometry.ManifoldOrientation I M' n) :
    DifferentialGeometry.ManifoldOrientation I M' m where
  dimension_eq := o.dimension_eq.trans (by simpa using Fintype.card_congr e)
  orientation x := Orientation.reindex ℝ E e (o.orientation x)
  locally_constant p x hx := by
    obtain ⟨U, hUo, hxU, hU, h⟩ := o.locally_constant p x hx
    refine ⟨U, hUo, hxU, hU, fun y hy => ?_⟩
    have h1 := orientation_reindex_map_comm (R := ℝ) (M := TangentSpace I y) (N := E) e
      (DifferentialGeometry.tangentChartEquiv I M' p y (hU hy)) (o.orientation y)
    have h2 := orientation_reindex_map_comm (R := ℝ) (M := TangentSpace I x) (N := E) e
      (DifferentialGeometry.tangentChartEquiv I M' p x hx) (o.orientation x)
    exact h1.symm.trans ((congrArg (Orientation.reindex ℝ E e) (h y hy)).trans h2)

def orientationFinrank (M : ClosedOrientedManifold.{u} 3) :
    DifferentialGeometry.ManifoldOrientation (𝓡 3) M.Carrier (Module.finrank ℝ csModel) :=
  reindexManifoldOrientation (𝓡 3) csIdx M.orientation

theorem orientationFinrank_orientation (M : ClosedOrientedManifold.{u} 3) (x : M.Carrier) :
    (orientationFinrank M).orientation x
      = Orientation.reindex ℝ csModel csIdx (M.orientation.orientation x) := rfl

def oMrestrict : SmoothOrientation (𝓡 3) c.toBallChart.interior :=
  restrictSmoothOrientation (𝓡 3) c.toBallChart.interior
    (smoothOrientationOfManifoldOrientation (𝓡 3) (orientationFinrank M))

theorem oMrestrict_apply (u : c.toBallChart.interior) :
    (oMrestrict c).val u
      = Orientation.reindex ℝ csModel csIdx (M.orientation.orientation u) := by
  unfold oMrestrict restrictSmoothOrientation smoothOrientationOfManifoldOrientation
    orientationFinrank reindexManifoldOrientation
  rfl

def oNrestrict : SmoothOrientation (𝓡 3) d.toBallChart.interior :=
  restrictSmoothOrientation (𝓡 3) d.toBallChart.interior
    (smoothOrientationOfManifoldOrientation (𝓡 3) (orientationFinrank N))

theorem oNrestrict_apply (v : d.toBallChart.interior) :
    (oNrestrict d).val v
      = Orientation.reindex ℝ csModel csIdx (N.orientation.orientation v) := by
  unfold oNrestrict restrictSmoothOrientation smoothOrientationOfManifoldOrientation
    orientationFinrank reindexManifoldOrientation
  rfl

def leftSmoothOrientation (hLq : AtlasLeft c d aD) : SmoothOrientation (𝓡 3) (qL c d aD hLq) :=
  pullbackSmoothOrientation (𝓡 3) (𝓡 3) (gL c d aD hLq)
    (contMDiff_gL c d aD hLq) (bijective_mfderiv_gL c d aD hLq) (oMrestrict c)

def rightSmoothOrientation (hRq : AtlasRight c d aD) : SmoothOrientation (𝓡 3) (qR c d aD hRq) :=
  pullbackSmoothOrientation (𝓡 3) (𝓡 3) (gR c d aD hRq)
    (contMDiff_gR c d aD hRq) (bijective_mfderiv_gR c d aD hRq) (oNrestrict d)

def seamChartFun : qS c d aD → csModel :=
  fun x => seamChartX c.toBallChart d.toBallChart aD.toHomeomorph x

theorem contMDiff_seamChartFun (hS : seamChartX c.toBallChart d.toBallChart aD.toHomeomorph ∈
    atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (seamChartFun c d aD) := by
  intro x
  have hcont : ContMDiffOn (𝓡 3) (𝓡 3) ∞
      (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph)
      (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph).source :=
    contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hS)
  have hx : (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) ∈
      (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph).source := x.2
  exact (contMDiffAt_subtype_iff (U := qS c d aD) (f :=
    (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph)) (x := x)).mpr
    (hcont.contMDiffAt ((seamChartX c.toBallChart d.toBallChart aD.toHomeomorph).open_source.mem_nhds hx))

theorem mfderiv_seamChartFun (hS : seamChartX c.toBallChart d.toBallChart aD.toHomeomorph ∈
    atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph))
    (x : qS c d aD) : mfderiv (𝓡 3) (𝓡 3) (seamChartFun c d aD) x =
      mfderiv (𝓡 3) (𝓡 3) (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph)
        (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) := by
  have hmd : MDifferentiableAt (𝓡 3) (𝓡 3)
      (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph)
      (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
    (PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
      (chartPartialDiffeomorph c d aD (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph) hS)
      x.2).mdifferentiableAt (show (∞ : ℕ∞ω) ≠ 0 by simp)
  have hcomp := mfderiv_comp (x := x) (f := (Subtype.val : qS c d aD →
      ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph))
    (g := (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph)) hmd
    (contMDiff_subtype_val.mdifferentiableAt (show (∞ : ℕ∞ω) ≠ 0 by simp))
  apply ContinuousLinearMap.ext
  intro v
  have h2 := DFunLike.congr_fun hcomp v
  change (mfderiv (𝓡 3) (𝓡 3)
      ((seamChartX c.toBallChart d.toBallChart aD.toHomeomorph) ∘
        (Subtype.val : qS c d aD →
          ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)) x) v =
    (mfderiv (𝓡 3) (𝓡 3) (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph)
      (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)) v
  simpa [DifferentialGeometry.mfderiv_subtype_val_apply] using h2

theorem bijective_mfderiv_seamChartFun (hS : seamChartX c.toBallChart d.toBallChart aD.toHomeomorph ∈
    atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph))
    (x : qS c d aD) : Function.Bijective (mfderiv (𝓡 3) (𝓡 3) (seamChartFun c d aD) x) := by
  rw [mfderiv_seamChartFun c d aD hS x]
  have hb := ((PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
      (chartPartialDiffeomorph c d aD (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph) hS)
      x.2).mfderivToContinuousLinearEquiv (show (∞ : ℕ∞ω) ≠ 0 by simp)).bijective
  exact hb

def seamSmoothOrientation (hS : seamChartX c.toBallChart d.toBallChart aD.toHomeomorph ∈
    atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)) :
    SmoothOrientation (𝓡 3) (qS c d aD) :=
  pullbackSmoothOrientation (𝓡 3) 𝓘(ℝ, csModel) (seamChartFun c d aD)
    (contMDiff_seamChartFun c d aD hS) (bijective_mfderiv_seamChartFun c d aD hS)
    (euclideanSmoothOrientation csModel stdOrientationModel)

end Pieces

section CoordinateDetection

theorem boundaryMap_mem_chart_closedBall' (z : csSphere) :
    ((c.toBallChart.boundaryMap z : c.toBallChart.Punctured) : M.Carrier) ∈
      c.toBallChart.chart '' Metric.closedBall (0 : csModel) 1 :=
  ⟨(z : csModel), by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_eq (norm_coe_sphere z), rfl⟩

theorem interiorToPunctured_not_mem_chart_closedBall' (u : c.toBallChart.interior) :
    ((c.toBallChart.interiorToPunctured u : c.toBallChart.Punctured) : M.Carrier) ∉
      c.toBallChart.chart '' Metric.closedBall (0 : csModel) 1 :=
  u.2

omit [ChartedSpace csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)]
  [IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)] in
theorem mem_qS_iff (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :
    x ∈ qS c d aD ↔
      x ∈ (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph).source := Iff.rfl

theorem interiorLeft_ne_inr (hLq : AtlasLeft c d aD) (x : qL c d aD hLq) (q : d.toBallChart.Punctured) :
    interiorLeft c.toBallChart d.toBallChart aD (gL c d aD hLq x) ≠
      inr c.toBallChart d.toBallChart aD.toHomeomorph q := by
  intro h
  obtain ⟨z, hz, -⟩ := (inl_eq_inr_iff c.toBallChart d.toBallChart aD.toHomeomorph
    (c.toBallChart.interiorToPunctured (gL c d aD hLq x)) q).mp h
  exact interiorToPunctured_not_mem_chart_closedBall' c (gL c d aD hLq x)
    (hz ▸ boundaryMap_mem_chart_closedBall' c z)

theorem exists_left_coordinate (hLq : AtlasLeft c d aD) (x : qL c d aD hLq)
    (hSp : (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) ∈ qS c d aD) :
    ∃ w : csModel, w ∈ SeamShell ∧ 1 < ‖w‖ ∧
      ((gL c d aD hLq x : c.toBallChart.interior) : M.Carrier) = c.toBallChart.chart w ∧
      seamChartX c.toBallChart d.toBallChart aD.toHomeomorph
        (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) = w := by
  rw [mem_qS_iff] at hSp
  rw [seamChartX_source c.toBallChart d.toBallChart aD.toHomeomorph] at hSp
  obtain ⟨⟨w, hw⟩, hwmap⟩ := hSp
  have hnotlt : ¬ ‖w‖ < 1 := by
    intro hlt
    have h2 := seamMap_eq_inr_puncturedOfCoord c.toBallChart d.toBallChart aD.toHomeomorph w hw hlt
    exact interiorLeft_ne_inr c d aD hLq x _
      ((gL_spec c d aD hLq x).trans (hwmap.symm.trans h2))
  have h1 : 1 ≤ ‖w‖ := le_of_not_gt hnotlt
  have hseam : seamChartX c.toBallChart d.toBallChart aD.toHomeomorph
      (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) = w := by
    rw [show (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) =
        seamMap c.toBallChart d.toBallChart aD.toHomeomorph ⟨w, hw⟩ from hwmap.symm,
      seamMap_eq_inl_puncturedOfCoord c.toBallChart d.toBallChart aD.toHomeomorph w hw h1]
    exact seamChartX_inl_puncturedOfCoord c.toBallChart d.toBallChart aD.toHomeomorph w hw h1
  have hdeep : ((gL c d aD hLq x : c.toBallChart.interior) : M.Carrier) = c.toBallChart.chart w := by
    have hkey : c.toBallChart.interiorToPunctured (gL c d aD hLq x) =
        puncturedOfCoord c.toBallChart w hw h1 :=
      inl_injective c.toBallChart d.toBallChart aD.toHomeomorph (by
        calc inl c.toBallChart d.toBallChart aD.toHomeomorph
              (c.toBallChart.interiorToPunctured (gL c d aD hLq x))
            = interiorLeft c.toBallChart d.toBallChart aD (gL c d aD hLq x) := rfl
          _ = (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
              gL_spec c d aD hLq x
          _ = seamMap c.toBallChart d.toBallChart aD.toHomeomorph ⟨w, hw⟩ := hwmap.symm
          _ = inl c.toBallChart d.toBallChart aD.toHomeomorph
                (puncturedOfCoord c.toBallChart w hw h1) :=
              seamMap_eq_inl_puncturedOfCoord c.toBallChart d.toBallChart aD.toHomeomorph w hw h1)
    calc ((gL c d aD hLq x : c.toBallChart.interior) : M.Carrier)
        = ((c.toBallChart.interiorToPunctured (gL c d aD hLq x) : c.toBallChart.Punctured) :
            M.Carrier) := rfl
      _ = ((puncturedOfCoord c.toBallChart w hw h1 : c.toBallChart.Punctured) : M.Carrier) := by
            rw [hkey]
      _ = c.toBallChart.chart w := puncturedOfCoord_val c.toBallChart w hw h1
  have hwpos : 1 < ‖w‖ := by
    rcases lt_or_eq_of_le h1 with h | h
    · exact h
    · exfalso
      refine (gL c d aD hLq x).2 ?_
      refine ⟨w, ?_, hdeep.symm⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_eq h.symm
  exact ⟨w, hw, hwpos, hdeep, hseam⟩

end CoordinateDetection

section LeftAgreement

variable (hLq : AtlasLeft c d aD)

theorem chart_source_of_mem_SeamShell (w : csModel) (hw : w ∈ SeamShell) :
    w ∈ c.toBallChart.chart.source := by
  apply c.toBallChart.closedBall_subset_source
  rw [Metric.mem_closedBall, dist_zero_right]
  linarith [hw.2]

theorem chart_target_of_coord (u : c.toBallChart.interior) (w : csModel)
    (hw : w ∈ SeamShell) (hu : (u : M.Carrier) = c.toBallChart.chart w) :
    (u : M.Carrier) ∈ c.toBallChart.chart.target := by
  rw [hu]
  exact c.toBallChart.chart.map_source (chart_source_of_mem_SeamShell c w hw)

theorem chart_symm_eq_of_coord (u : c.toBallChart.interior) (w : csModel)
    (hw : w ∈ SeamShell) (hu : (u : M.Carrier) = c.toBallChart.chart w) :
    c.toBallChart.chart.symm (u : M.Carrier) = w := by
  rw [hu]
  exact c.toBallChart.chart.left_inv (chart_source_of_mem_SeamShell c w hw)


theorem mdifferentiableAt_chartSymm (w : csModel) (hw : w ∈ c.toBallChart.chart.source) :
    MDifferentiableAt (𝓡 3) (𝓡 3) ((c.toBallChart.chart.symm : M.Carrier → csModel))
      (c.toBallChart.chart w) :=
  (c.toBallChart.chart.contMDiffOn_invFun.contMDiffAt
    (c.toBallChart.chart.open_target.mem_nhds (c.toBallChart.chart.map_source hw))).mdifferentiableAt
    (show (∞ : ℕ∞ω) ≠ 0 by simp)

theorem mdifferentiableAt_chart (w : csModel) (hw : w ∈ c.toBallChart.chart.source) :
    MDifferentiableAt (𝓡 3) (𝓡 3) ((c.toBallChart.chart : csModel → M.Carrier)) w :=
  (PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ c.toBallChart.chart hw).mdifferentiableAt
    (show (∞ : ℕ∞ω) ≠ 0 by simp)

theorem mfderiv_chartSymm_comp_chart (w : csModel) (hw : w ∈ c.toBallChart.chart.source) :
    (mfderiv (𝓡 3) (𝓡 3) ((c.toBallChart.chart.symm : M.Carrier → csModel))
        (c.toBallChart.chart w)).comp
      (mfderiv (𝓡 3) (𝓡 3) ((c.toBallChart.chart : csModel → M.Carrier)) w)
      = ContinuousLinearMap.id ℝ (TangentSpace (𝓡 3) w) := by
  have hev : ((c.toBallChart.chart.symm : M.Carrier → csModel)) ∘
      ((c.toBallChart.chart : csModel → M.Carrier)) =ᶠ[𝓝 w] id :=
    Filter.eventuallyEq_of_mem (c.toBallChart.chart.open_source.mem_nhds hw)
      (fun y hy => c.toBallChart.chart.left_inv hy)
  have hcomp := mfderiv_comp (x := w) (f := ((c.toBallChart.chart : csModel → M.Carrier)))
    (g := ((c.toBallChart.chart.symm : M.Carrier → csModel)))
    (mdifferentiableAt_chartSymm c w hw) (mdifferentiableAt_chart c w hw)
  rw [Filter.EventuallyEq.mfderiv_eq hev, mfderiv_id] at hcomp
  exact hcomp.symm

theorem chart_symm_chart_apply (w : csModel) (hw : w ∈ c.toBallChart.chart.source) :
    (c.toBallChart.chart.symm.toPartialEquiv) (c.toBallChart.chart.toPartialEquiv w) = w :=
  c.toBallChart.chart.left_inv hw

theorem mfderiv_chart_comp_chartSymm (w : csModel) (hw : w ∈ c.toBallChart.chart.source) :
    (mfderiv (𝓡 3) (𝓡 3) ((c.toBallChart.chart : csModel → M.Carrier)) w).comp
      (mfderiv (𝓡 3) (𝓡 3) ((c.toBallChart.chart.symm : M.Carrier → csModel))
        (c.toBallChart.chart w))
      = ContinuousLinearMap.id ℝ (TangentSpace (𝓡 3) (c.toBallChart.chart w)) := by
  have hev : ((c.toBallChart.chart : csModel → M.Carrier)) ∘
      ((c.toBallChart.chart.symm : M.Carrier → csModel)) =ᶠ[𝓝 (c.toBallChart.chart w)] id :=
    Filter.eventuallyEq_of_mem
      (c.toBallChart.chart.open_target.mem_nhds (c.toBallChart.chart.map_source hw))
      (fun y hy => c.toBallChart.chart.right_inv hy)
  have hmem : c.toBallChart.chart.symm (c.toBallChart.chart w) ∈ c.toBallChart.chart.source :=
    c.toBallChart.chart.map_target (c.toBallChart.chart.map_source hw)
  have hmd1' : MDifferentiableAt (𝓡 3) (𝓡 3) ((c.toBallChart.chart : csModel → M.Carrier))
      (c.toBallChart.chart.symm (c.toBallChart.chart w)) :=
    (c.toBallChart.chart.contMDiffOn_toFun.contMDiffAt
      (c.toBallChart.chart.open_source.mem_nhds hmem)).mdifferentiableAt
      (show (∞ : ℕ∞ω) ≠ 0 by simp)
  have hcomp := mfderiv_comp (x := c.toBallChart.chart w)
    (f := ((c.toBallChart.chart.symm : M.Carrier → csModel)))
    (g := ((c.toBallChart.chart : csModel → M.Carrier))) hmd1' (mdifferentiableAt_chartSymm c w hw)
  rw [Filter.EventuallyEq.mfderiv_eq hev, mfderiv_id] at hcomp
  rw [chart_symm_chart_apply c w hw] at hcomp
  exact hcomp.symm


def chartSymmEquiv (w : csModel) (hw : w ∈ c.toBallChart.chart.source) :
    TangentSpace (𝓡 3) (c.toBallChart.chart w) ≃L[ℝ] TangentSpace (𝓡 3) w where
  toFun := mfderiv (𝓡 3) (𝓡 3) ((c.toBallChart.chart.symm : M.Carrier → csModel))
    (c.toBallChart.chart w)
  invFun := mfderiv (𝓡 3) (𝓡 3) ((c.toBallChart.chart : csModel → M.Carrier)) w
  left_inv := by
    intro v
    exact DFunLike.congr_fun (mfderiv_chart_comp_chartSymm c w hw) v
  right_inv := by
    intro v
    exact DFunLike.congr_fun (mfderiv_chartSymm_comp_chart c w hw) v
  map_add' := (mfderiv (𝓡 3) (𝓡 3) ((c.toBallChart.chart.symm : M.Carrier → csModel))
    (c.toBallChart.chart w)).map_add
  map_smul' := (mfderiv (𝓡 3) (𝓡 3) ((c.toBallChart.chart.symm : M.Carrier → csModel))
    (c.toBallChart.chart w)).map_smul
  continuous_toFun := (mfderiv (𝓡 3) (𝓡 3)
    ((c.toBallChart.chart.symm : M.Carrier → csModel)) (c.toBallChart.chart w)).cont
  continuous_invFun := (mfderiv (𝓡 3) (𝓡 3)
    ((c.toBallChart.chart : csModel → M.Carrier)) w).cont

theorem seam_interiorLeft_eventuallyEq (x : qL c d aD hLq) (w : csModel)
    (hw : w ∈ SeamShell) (h1w : 1 < ‖w‖) (h2w : ‖w‖ < 3 / 2)
    (hu : ((gL c d aD hLq x : c.toBallChart.interior) : M.Carrier) = c.toBallChart.chart w) :
    (fun z : c.toBallChart.interior =>
        seamChartX c.toBallChart d.toBallChart aD.toHomeomorph
          (interiorLeft c.toBallChart d.toBallChart aD z)) =ᶠ[𝓝 (gL c d aD hLq x)]
      (fun z : c.toBallChart.interior => c.toBallChart.chart.symm (z : M.Carrier)) := by
  have hwsrc : w ∈ c.toBallChart.chart.source := chart_source_of_mem_SeamShell c w hw
  have hmemT : ((gL c d aD hLq x : c.toBallChart.interior) : M.Carrier) ∈
      c.toBallChart.chart.target := by
    rw [hu]
    exact c.toBallChart.chart.map_source hwsrc
  have hcontSymm : ContinuousAt
      (fun z : M.Carrier => c.toBallChart.chart.symm z)
      ((gL c d aD hLq x : c.toBallChart.interior) : M.Carrier) :=
    (c.toBallChart.chart.symm.contMDiffOn_toFun.contMDiffAt
      (c.toBallChart.chart.symm.open_source.mem_nhds hmemT)).continuousAt
  have hcont : ContinuousAt
      (fun z : c.toBallChart.interior => c.toBallChart.chart.symm (z : M.Carrier))
      (gL c d aD hLq x) :=
    hcontSymm.comp (continuous_subtype_val.continuousAt (x := gL c d aD hLq x))
  have hnhds1 : (fun z : c.toBallChart.interior => c.toBallChart.chart.symm (z : M.Carrier)) ⁻¹'
      {y : csModel | 1 < ‖y‖ ∧ ‖y‖ < 3 / 2} ∈ 𝓝 (gL c d aD hLq x) := by
    apply hcont.preimage_mem_nhds
    refine ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)).mem_nhds ⟨?_, ?_⟩
    · rw [hu, chart_symm_chart_apply c w hwsrc]; exact h1w
    · rw [hu, chart_symm_chart_apply c w hwsrc]; exact h2w
  have hnhds2 : {z : c.toBallChart.interior | (z : M.Carrier) ∈ c.toBallChart.chart.target}
      ∈ 𝓝 (gL c d aD hLq x) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds
      (c.toBallChart.chart.open_target.mem_nhds hmemT)
  filter_upwards [hnhds1, hnhds2] with z hz hzT
  have hzsrc : c.toBallChart.chart.symm (z : M.Carrier) ∈ c.toBallChart.chart.source :=
    c.toBallChart.chart.map_target hzT
  have hzchart : c.toBallChart.chart (c.toBallChart.chart.symm (z : M.Carrier)) =
      (z : M.Carrier) :=
    c.toBallChart.chart.right_inv hzT
  have hy1 : 1 ≤ ‖c.toBallChart.chart.symm (z : M.Carrier)‖ := le_of_lt hz.1
  have hyShell : c.toBallChart.chart.symm (z : M.Carrier) ∈ SeamShell :=
    ⟨by linarith [hz.1], hz.2⟩
  have hkey : puncturedOfCoord c.toBallChart (c.toBallChart.chart.symm (z : M.Carrier))
      hyShell hy1 = c.toBallChart.interiorToPunctured z := by
    apply Subtype.ext
    rw [puncturedOfCoord_val, BallChart.interiorToPunctured_val, hzchart]
  calc seamChartX c.toBallChart d.toBallChart aD.toHomeomorph
        (interiorLeft c.toBallChart d.toBallChart aD z)
      = seamChartX c.toBallChart d.toBallChart aD.toHomeomorph
          (inl c.toBallChart d.toBallChart aD.toHomeomorph
            (puncturedOfCoord c.toBallChart (c.toBallChart.chart.symm (z : M.Carrier))
              hyShell hy1)) := by
          rw [show interiorLeft c.toBallChart d.toBallChart aD z =
              inl c.toBallChart d.toBallChart aD.toHomeomorph
                (c.toBallChart.interiorToPunctured z) from rfl, ← hkey]
    _ = c.toBallChart.chart.symm (z : M.Carrier) :=
        seamChartX_inl_puncturedOfCoord c.toBallChart d.toBallChart aD.toHomeomorph _
          hyShell hy1

end LeftAgreement

section SeamDifferential

theorem mdifferentiableAt_seamChartX_of_atlas
    (hS : seamChartX c.toBallChart d.toBallChart aD.toHomeomorph ∈
      atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph))
    (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)
    (hx : x ∈ (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph).source) :
    MDifferentiableAt (𝓡 3) (𝓡 3)
      (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph) x :=
  (PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
    (chartPartialDiffeomorph c d aD
      (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph) hS) hx).mdifferentiableAt
    (show (∞ : ℕ∞ω) ≠ 0 by simp)

theorem seam_interiorLeft_chain (hLq : AtlasLeft c d aD)
    (hS : seamChartX c.toBallChart d.toBallChart aD.toHomeomorph ∈
      atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph))
    (x : qL c d aD hLq) (w : csModel) (hw : w ∈ SeamShell) (h1w : 1 < ‖w‖)
    (hu : ((gL c d aD hLq x : c.toBallChart.interior) : M.Carrier) = c.toBallChart.chart w)
    (hSp : (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) ∈ qS c d aD) :
    (mfderiv (𝓡 3) (𝓡 3) (seamChartFun c d aD)
        ⟨(x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph), hSp⟩).comp
      (mfderiv (𝓡 3) (𝓡 3) (interiorLeft c.toBallChart d.toBallChart aD)
        (gL c d aD hLq x))
    = mfderiv (𝓡 3) (𝓡 3) ((c.toBallChart.chart.symm : M.Carrier → csModel))
        (c.toBallChart.chart w) := by
  have hxsrc : (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) ∈
      (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph).source := hSp
  have hSx : MDifferentiableAt (𝓡 3) (𝓡 3)
      (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph)
      (interiorLeft c.toBallChart d.toBallChart aD (gL c d aD hLq x)) := by
    rw [gL_spec c d aD hLq x]
    exact mdifferentiableAt_seamChartX_of_atlas c d aD hS _ hxsrc
  have hIL : MDifferentiableAt (𝓡 3) (𝓡 3) (interiorLeft c.toBallChart d.toBallChart aD)
      (gL c d aD hLq x) :=
    ((interiorLeft_isLocalDiffeomorph c.toBallChart d.toBallChart aD hLq)
      (gL c d aD hLq x)).mdifferentiableAt (show (∞ : ℕ∞ω) ≠ 0 by simp)
  have hcomp := mfderiv_comp (x := gL c d aD hLq x)
    (f := (interiorLeft c.toBallChart d.toBallChart aD))
    (g := (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph)) hSx hIL
  have hcomp' : mfderiv (𝓡 3) (𝓡 3)
      (fun z : c.toBallChart.interior =>
        seamChartX c.toBallChart d.toBallChart aD.toHomeomorph
          (interiorLeft c.toBallChart d.toBallChart aD z)) (gL c d aD hLq x) =
      (mfderiv (𝓡 3) (𝓡 3) (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph)
          (interiorLeft c.toBallChart d.toBallChart aD (gL c d aD hLq x))).comp
        (mfderiv (𝓡 3) (𝓡 3) (interiorLeft c.toBallChart d.toBallChart aD)
          (gL c d aD hLq x)) := hcomp
  have hev' : (fun z : c.toBallChart.interior =>
        seamChartX c.toBallChart d.toBallChart aD.toHomeomorph
          (interiorLeft c.toBallChart d.toBallChart aD z)) =ᶠ[𝓝 (gL c d aD hLq x)]
      (fun z : c.toBallChart.interior => c.toBallChart.chart.symm (z : M.Carrier)) :=
    seam_interiorLeft_eventuallyEq c d aD hLq x w hw h1w hw.2 hu
  have hsub : MDifferentiableAt (𝓡 3) (𝓡 3)
      (Subtype.val : c.toBallChart.interior → M.Carrier) (gL c d aD hLq x) :=
    contMDiff_subtype_val.mdifferentiableAt (show (∞ : ℕ∞ω) ≠ 0 by simp)
  have hcs : MDifferentiableAt (𝓡 3) (𝓡 3)
      ((c.toBallChart.chart.symm : M.Carrier → csModel))
      ((Subtype.val : c.toBallChart.interior → M.Carrier) (gL c d aD hLq x)) := by
    rw [hu]
    exact mdifferentiableAt_chartSymm c w (chart_source_of_mem_SeamShell c w hw)
  have hA : mfderiv (𝓡 3) (𝓡 3)
      (fun z : c.toBallChart.interior => c.toBallChart.chart.symm (z : M.Carrier))
      (gL c d aD hLq x) =
      mfderiv (𝓡 3) (𝓡 3) ((c.toBallChart.chart.symm : M.Carrier → csModel))
        (c.toBallChart.chart w) := by
    rw [show (fun z : c.toBallChart.interior => c.toBallChart.chart.symm (z : M.Carrier)) =
        ((c.toBallChart.chart.symm : M.Carrier → csModel) ∘
          (Subtype.val : c.toBallChart.interior → M.Carrier)) from rfl]
    rw [mfderiv_comp (x := gL c d aD hLq x)
      (f := (Subtype.val : c.toBallChart.interior → M.Carrier))
      (g := (c.toBallChart.chart.symm : M.Carrier → csModel)) hcs hsub]
    rw [hu]
    apply ContinuousLinearMap.ext
    intro v
    change (mfderiv (𝓡 3) (𝓡 3) ((c.toBallChart.chart.symm : M.Carrier → csModel))
          (c.toBallChart.chart w))
        ((mfderiv (𝓡 3) (𝓡 3) (Subtype.val : c.toBallChart.interior → M.Carrier)
          (gL c d aD hLq x)) v) =
      (mfderiv (𝓡 3) (𝓡 3) ((c.toBallChart.chart.symm : M.Carrier → csModel))
        (c.toBallChart.chart w)) v
    rw [DifferentialGeometry.mfderiv_subtype_val_apply]
  have hSfun : mfderiv (𝓡 3) (𝓡 3) (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph)
      (interiorLeft c.toBallChart d.toBallChart aD (gL c d aD hLq x)) =
      mfderiv (𝓡 3) (𝓡 3) (seamChartFun c d aD)
        ⟨(x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph), hSp⟩ := by
    rw [gL_spec c d aD hLq x,
      ← mfderiv_seamChartFun c d aD hS
        ⟨(x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph), hSp⟩]
  rw [← hSfun]
  exact hcomp'.symm.trans (hev'.mfderiv_eq.trans hA)

end SeamDifferential

section Differentials

variable (hLq : AtlasLeft c d aD)
variable (hRq : AtlasRight c d aD)
variable (hS : seamChartX c.toBallChart d.toBallChart aD.toHomeomorph ∈
  atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph))

def seamDifferential (hS : seamChartX c.toBallChart d.toBallChart aD.toHomeomorph ∈
    atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph))
    (y : qS c d aD) : csModel ≃L[ℝ] csModel :=
  DifferentialGeometry.Topology.Manifold.differentialEquivOfBijective (𝓡 3) 𝓘(ℝ, csModel)
    (seamChartFun c d aD) (bijective_mfderiv_seamChartFun c d aD hS) y

theorem seamDifferential_apply (y : qS c d aD) (v : csModel) :
    seamDifferential c d aD hS y v =
      mfderiv (𝓡 3) (𝓡 3) (seamChartFun c d aD) y v := rfl

theorem seamSmoothOrientation_apply (y : qS c d aD) :
    (seamSmoothOrientation c d aD hS).val y =
      tangentOrientationEquiv (seamDifferential c d aD hS y).symm.toLinearEquiv
        stdOrientationModel := rfl

theorem seamSmoothOrientation_apply_map (y : qS c d aD) :
    (seamSmoothOrientation c d aD hS).val y =
      Orientation.map (Fin (Module.finrank ℝ csModel))
        (seamDifferential c d aD hS y).symm.toLinearEquiv stdOrientationModel := by
  rw [seamSmoothOrientation_apply, tangentOrientationEquiv_self]

def leftDifferentialEquiv (hLq : AtlasLeft c d aD) (x : qL c d aD hLq) :
    csModel ≃L[ℝ] csModel :=
  DifferentialGeometry.Topology.Manifold.differentialEquivOfBijective (𝓡 3) (𝓡 3)
    (gL c d aD hLq) (bijective_mfderiv_gL c d aD hLq) x

theorem leftDifferentialEquiv_apply (hLq : AtlasLeft c d aD) (x : qL c d aD hLq) (v : csModel) :
    leftDifferentialEquiv c d aD hLq x v =
      mfderiv (𝓡 3) (𝓡 3) (gL c d aD hLq) x v := rfl

theorem leftDifferentialEquiv_eq (hLq : AtlasLeft c d aD) (x : qL c d aD hLq) :
    leftDifferentialEquiv c d aD hLq x = leftDifferential c d aD hLq x := by
  apply ContinuousLinearEquiv.ext
  funext v
  rfl

theorem leftDifferential_symm_apply (hLq : AtlasLeft c d aD) (x : qL c d aD hLq) (v : csModel) :
    (leftDifferential c d aD hLq x).symm v =
      mfderiv (𝓡 3) (𝓡 3) (interiorLeft c.toBallChart d.toBallChart aD) (gL c d aD hLq x) v :=
  rfl

theorem leftSmoothOrientation_apply (hLq : AtlasLeft c d aD) (x : qL c d aD hLq) :
    (leftSmoothOrientation c d aD hLq).val x =
      tangentOrientationEquiv (leftDifferentialEquiv c d aD hLq x).symm.toLinearEquiv
        ((oMrestrict c).val (gL c d aD hLq x)) := rfl

theorem leftSmoothOrientation_apply_map (hLq : AtlasLeft c d aD) (x : qL c d aD hLq) :
    (leftSmoothOrientation c d aD hLq).val x =
      Orientation.map (Fin (Module.finrank ℝ csModel))
        (leftDifferentialEquiv c d aD hLq x).symm.toLinearEquiv
        (Orientation.reindex ℝ csModel csIdx
          (M.orientation.orientation (gL c d aD hLq x))) := by
  rw [leftSmoothOrientation_apply, oMrestrict_apply, tangentOrientationEquiv_self]

def rightDifferentialEquiv (hRq : AtlasRight c d aD) (x : qR c d aD hRq) :
    csModel ≃L[ℝ] csModel :=
  DifferentialGeometry.Topology.Manifold.differentialEquivOfBijective (𝓡 3) (𝓡 3)
    (gR c d aD hRq) (bijective_mfderiv_gR c d aD hRq) x

theorem rightDifferentialEquiv_eq (hRq : AtlasRight c d aD) (x : qR c d aD hRq) :
    rightDifferentialEquiv c d aD hRq x = rightDifferential c d aD hRq x := by
  apply ContinuousLinearEquiv.ext
  funext v
  rfl

theorem rightDifferential_symm_apply (hRq : AtlasRight c d aD) (x : qR c d aD hRq) (v : csModel) :
    (rightDifferential c d aD hRq x).symm v =
      mfderiv (𝓡 3) (𝓡 3) (interiorRight c.toBallChart d.toBallChart aD) (gR c d aD hRq x) v :=
  rfl

theorem rightSmoothOrientation_apply (hRq : AtlasRight c d aD) (x : qR c d aD hRq) :
    (rightSmoothOrientation c d aD hRq).val x =
      tangentOrientationEquiv (rightDifferentialEquiv c d aD hRq x).symm.toLinearEquiv
        ((oNrestrict d).val (gR c d aD hRq x)) := rfl

theorem rightSmoothOrientation_apply_map (hRq : AtlasRight c d aD) (x : qR c d aD hRq) :
    (rightSmoothOrientation c d aD hRq).val x =
      Orientation.map (Fin (Module.finrank ℝ csModel))
        (rightDifferentialEquiv c d aD hRq x).symm.toLinearEquiv
        (Orientation.reindex ℝ csModel csIdx
          (N.orientation.orientation (gR c d aD hRq x))) := by
  rw [rightSmoothOrientation_apply, oNrestrict_apply, tangentOrientationEquiv_self]

end Differentials

section LeftAgreement

theorem chartTangentEquiv_apply (c : OrientedBallChart M) {x : csModel} (hx : x ∈ c.chart.source)
    (v : csModel) : chartTangentEquiv c hx v = mfderiv (𝓡 3) (𝓡 3) (c.chart : csModel →
      M.Carrier) x v := rfl

theorem orientation_eq_map_chartTangentEquiv (c : OrientedBallChart M) {x : csModel}
    (hx : x ∈ c.chart.source) :
    M.orientation.orientation (c.chart x) =
      Orientation.map (Fin 3) (chartTangentEquiv c hx).toLinearEquiv (stdOrientation x) := by
  have h := congrArg (Orientation.map (Fin 3) (chartTangentEquiv c hx).toLinearEquiv)
    (orientation_map_chartTangentEquiv_symm c hx)
  rw [orientation_map_symm_map_self (chartTangentEquiv c hx).toLinearEquiv
    (M.orientation.orientation (c.chart x))] at h
  exact h

theorem seamDifferential_symm_eq (hLq : AtlasLeft c d aD)
    (hS : seamChartX c.toBallChart d.toBallChart aD.toHomeomorph ∈
      atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph))
    (x : qL c d aD hLq) (w : csModel) (hw : w ∈ SeamShell) (h1w : 1 < ‖w‖)
    (hu : ((gL c d aD hLq x : c.toBallChart.interior) : M.Carrier) = c.toBallChart.chart w)
    (hSp : (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) ∈ qS c d aD) :
    (seamDifferential c d aD hS ⟨(x : ConnectedSumQuotient c.toBallChart
        d.toBallChart aD.toHomeomorph), hSp⟩).symm.toLinearEquiv
      = (chartTangentEquiv c (chart_source_of_mem_SeamShell c w hw)).toLinearEquiv.trans
          (leftDifferential c d aD hLq x).symm.toLinearEquiv := by
  have hchain := seam_interiorLeft_chain c d aD hLq hS x w hw h1w hu hSp
  apply LinearEquiv.ext
  intro v
  change (seamDifferential c d aD hS ⟨(x : ConnectedSumQuotient c.toBallChart
      d.toBallChart aD.toHomeomorph), hSp⟩).symm v =
    (mfderiv (𝓡 3) (𝓡 3) (interiorLeft c.toBallChart d.toBallChart aD) (gL c d aD hLq x))
      (mfderiv (𝓡 3) (𝓡 3) ((c.toBallChart.chart : csModel → M.Carrier)) w v)
  refine (seamDifferential c d aD hS ⟨(x : ConnectedSumQuotient c.toBallChart
    d.toBallChart aD.toHomeomorph), hSp⟩).toLinearEquiv.injective ?_
  erw [show (seamDifferential c d aD hS ⟨(x : ConnectedSumQuotient c.toBallChart
        d.toBallChart aD.toHomeomorph), hSp⟩)
      ((seamDifferential c d aD hS ⟨(x : ConnectedSumQuotient c.toBallChart
        d.toBallChart aD.toHomeomorph), hSp⟩).symm v) = v from
    LinearEquiv.apply_symm_apply _ v]
  change v = ((mfderiv (𝓡 3) (𝓡 3) (seamChartFun c d aD)
      ⟨(x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph), hSp⟩).comp
    (mfderiv (𝓡 3) (𝓡 3) (interiorLeft c.toBallChart d.toBallChart aD) (gL c d aD hLq x)))
      (mfderiv (𝓡 3) (𝓡 3) ((c.toBallChart.chart : csModel → M.Carrier)) w v)
  erw [DFunLike.congr_fun hchain (mfderiv (𝓡 3) (𝓡 3)
    ((c.toBallChart.chart : csModel → M.Carrier)) w v)]
  exact ((chartSymmEquiv c w (chart_source_of_mem_SeamShell c w hw)).right_inv v).symm

theorem leftSmoothOrientation_apply_eq_seamSmoothOrientation (hLq : AtlasLeft c d aD)
    (hS : seamChartX c.toBallChart d.toBallChart aD.toHomeomorph ∈
      atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph))
    (x : qL c d aD hLq)
    (hSp : (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) ∈ qS c d aD) :
    (leftSmoothOrientation c d aD hLq).val x =
      (seamSmoothOrientation c d aD hS).val ⟨(x : ConnectedSumQuotient c.toBallChart
        d.toBallChart aD.toHomeomorph), hSp⟩ := by
  obtain ⟨w, hw, h1w, hdeep, -⟩ := exists_left_coordinate c d aD hLq x hSp
  have hchain := seamDifferential_symm_eq c d aD hLq hS x w hw h1w hdeep hSp
  have hchart : M.orientation.orientation
      ((gL c d aD hLq x : c.toBallChart.interior) : M.Carrier) =
      Orientation.map (Fin 3)
        (chartTangentEquiv c (chart_source_of_mem_SeamShell c w hw)).toLinearEquiv
        (stdOrientation w) := by
    rw [hdeep]
    exact orientation_eq_map_chartTangentEquiv c (chart_source_of_mem_SeamShell c w hw)
  rw [leftSmoothOrientation_apply_map, seamSmoothOrientation_apply_map, hchain]
  erw [← orientation_map_map_trans (R := ℝ)
    (chartTangentEquiv c (chart_source_of_mem_SeamShell c w hw)).toLinearEquiv
    (leftDifferential c d aD hLq x).symm.toLinearEquiv stdOrientationModel]
  erw [leftDifferentialEquiv_eq]
  erw [hchart]
  erw [show Orientation.reindex ℝ csModel csIdx
        (Orientation.map (Fin 3)
          (chartTangentEquiv c (chart_source_of_mem_SeamShell c w hw)).toLinearEquiv
          (stdOrientation w)) =
      Orientation.map (Fin (Module.finrank ℝ csModel))
        (chartTangentEquiv c (chart_source_of_mem_SeamShell c w hw)).toLinearEquiv
        (Orientation.reindex ℝ csModel csIdx (stdOrientation w)) from
    orientation_reindex_map_comm csIdx
      (chartTangentEquiv c (chart_source_of_mem_SeamShell c w hw)).toLinearEquiv (stdOrientation w)]
  erw [← stdOrientationModel_eq_reindex w]
  rfl

end LeftAgreement

section RightCoordinate

variable (hRq : AtlasRight c d aD)

theorem inl_ne_interiorRight (p : c.toBallChart.Punctured) (x : qR c d aD hRq) :
    inl c.toBallChart d.toBallChart aD.toHomeomorph p ≠
      interiorRight c.toBallChart d.toBallChart aD (gR c d aD hRq x) := by
  intro h
  obtain ⟨z, -, hz⟩ := (inl_eq_inr_iff c.toBallChart d.toBallChart aD.toHomeomorph p
    (d.toBallChart.interiorToPunctured (gR c d aD hRq x))).mp h
  have h1 : ((d.toBallChart.boundaryMap (aD.toHomeomorph z) : d.toBallChart.Punctured) :
      N.Carrier) = ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier) := by
    rw [← BallChart.interiorToPunctured_val (c := d.toBallChart) (gR c d aD hRq x), ← hz]
  exact interiorToPunctured_not_mem_chart_closedBall' d (gR c d aD hRq x)
    (h1 ▸ boundaryMap_mem_chart_closedBall' d (aD.toHomeomorph z))

theorem exists_right_coordinate (x : qR c d aD hRq)
    (hSp : (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) ∈ qS c d aD)
    (hT : 1 / 2 < ‖seamChartX c.toBallChart d.toBallChart aD.toHomeomorph
      (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)‖) :
    ∃ y : csModel, y ∈ SeamShell ∧ 1 < ‖y‖ ∧
      ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier) = d.toBallChart.chart y ∧
      seamChartX c.toBallChart d.toBallChart aD.toHomeomorph
        (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) =
        reflectMapInv aD.toHomeomorph y := by
  rw [mem_qS_iff] at hSp
  rw [seamChartX_source c.toBallChart d.toBallChart aD.toHomeomorph] at hSp
  obtain ⟨⟨w, hw⟩, hwmap⟩ := hSp
  have hnotle : ¬ 1 ≤ ‖w‖ := by
    intro h1
    refine inl_ne_interiorRight c d aD hRq (puncturedOfCoord c.toBallChart w hw h1) x ?_
    rw [← seamMap_eq_inl_puncturedOfCoord c.toBallChart d.toBallChart aD.toHomeomorph w hw h1,
      hwmap, ← gR_spec c d aD hRq x]
  have hlt : ‖w‖ < 1 := not_le.mp hnotle
  have hkey : puncturedOfCoord d.toBallChart (reflectMap aD.toHomeomorph w)
      (reflectMap_mem_SeamShell aD.toHomeomorph w hw)
      (one_le_norm_reflectMap aD.toHomeomorph w hlt)
      = d.toBallChart.interiorToPunctured (gR c d aD hRq x) :=
    inr_injective c.toBallChart d.toBallChart aD.toHomeomorph (by
      show inr c.toBallChart d.toBallChart aD.toHomeomorph (puncturedOfCoord d.toBallChart
          (reflectMap aD.toHomeomorph w) (reflectMap_mem_SeamShell aD.toHomeomorph w hw)
          (one_le_norm_reflectMap aD.toHomeomorph w hlt)) =
        inr c.toBallChart d.toBallChart aD.toHomeomorph
          (d.toBallChart.interiorToPunctured (gR c d aD hRq x))
      rw [← seamMap_eq_inr_puncturedOfCoord c.toBallChart d.toBallChart aD.toHomeomorph w hw hlt,
        hwmap]
      exact (gR_spec c d aD hRq x).symm)
  have hy_eq : ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier) =
      d.toBallChart.chart (reflectMap aD.toHomeomorph w) := by
    rw [← BallChart.interiorToPunctured_val (c := d.toBallChart) (gR c d aD hRq x), ← hkey]
    rfl
  have hwnorm : ‖w‖ = ‖seamChartX c.toBallChart d.toBallChart aD.toHomeomorph
      (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)‖ := by
    rw [← hwmap, seamChartX_apply_seamMap]
  have hnormy : ‖reflectMap aD.toHomeomorph w‖ = 2 - ‖w‖ :=
    norm_reflectMap (a := aD.toHomeomorph) (x := w) (by linarith [hw.2])
  refine ⟨reflectMap aD.toHomeomorph w, reflectMap_mem_SeamShell aD.toHomeomorph w hw, ?_, hy_eq, ?_⟩
  · rw [hnormy]; linarith
  · rw [← hwmap, seamChartX_apply_seamMap]
    change (w : csModel) = reflectMapInv aD.toHomeomorph (reflectMap aD.toHomeomorph w)
    exact (reflectMapInv_reflectMap aD.toHomeomorph ⟨w, hw⟩).symm

end RightCoordinate

section RightTransition

variable (hRq : AtlasRight c d aD)

theorem seam_interiorRight_eventuallyEq (x : qR c d aD hRq) (y : csModel)
    (hy : y ∈ SeamShell) (h1y : 1 < ‖y‖)
    (hu : ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier) = d.toBallChart.chart y) :
    (fun z : d.toBallChart.interior =>
        seamChartX c.toBallChart d.toBallChart aD.toHomeomorph
          (interiorRight c.toBallChart d.toBallChart aD z)) =ᶠ[𝓝 (gR c d aD hRq x)]
      (fun z : d.toBallChart.interior =>
        rightSeamTransition c.toBallChart d.toBallChart aD.toHomeomorph
          (d.toBallChart.chart.symm (z : N.Carrier))) := by
  have hysrc : y ∈ d.toBallChart.chart.source := chart_source_of_mem_SeamShell d y hy
  have hmemT : ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier) ∈
      d.toBallChart.chart.target := by
    rw [hu]
    exact d.toBallChart.chart.map_source hysrc
  have hcont : ContinuousAt
      (fun z : d.toBallChart.interior => d.toBallChart.chart.symm (z : N.Carrier))
      (gR c d aD hRq x) :=
    ((d.toBallChart.chart.symm.contMDiffOn_toFun.contMDiffAt
      (d.toBallChart.chart.symm.open_source.mem_nhds hmemT)).continuousAt).comp
      (continuous_subtype_val.continuousAt (x := gR c d aD hRq x))
  have hsymm : d.toBallChart.chart.symm
      ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier) = y := by
    rw [hu]
    exact d.toBallChart.chart.left_inv hysrc
  have hnhds1 : (fun z : d.toBallChart.interior =>
      d.toBallChart.chart.symm (z : N.Carrier)) ⁻¹'
      {y' : csModel | y' ∈ SeamShell ∧ 1 ≤ ‖y'‖} ∈ 𝓝 (gR c d aD hRq x) := by
    have hbase : {y' : csModel | y' ∈ SeamShell ∧ 1 < ‖y'‖} ∈
        𝓝 (d.toBallChart.chart.symm
          ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier)) := by
      rw [hsymm]
      exact (isOpen_seamShell.inter (isOpen_lt continuous_const continuous_norm)).mem_nhds
        ⟨hy, h1y⟩
    refine hcont.preimage_mem_nhds (Filter.mem_of_superset hbase ?_)
    intro y' hy'
    exact ⟨hy'.1, le_of_lt hy'.2⟩
  have hnhds2 : {z : d.toBallChart.interior |
      (z : N.Carrier) ∈ d.toBallChart.chart.target} ∈ 𝓝 (gR c d aD hRq x) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds
      (d.toBallChart.chart.open_target.mem_nhds hmemT)
  filter_upwards [hnhds1, hnhds2] with z hz hzT
  obtain ⟨hzShell, hz1⟩ := hz
  have hzchart : d.toBallChart.chart (d.toBallChart.chart.symm (z : N.Carrier)) =
      (z : N.Carrier) :=
    d.toBallChart.chart.right_inv hzT
  have hkey : puncturedOfCoord d.toBallChart (d.toBallChart.chart.symm (z : N.Carrier))
      hzShell hz1 = d.toBallChart.interiorToPunctured z := by
    apply Subtype.ext
    rw [puncturedOfCoord_val, BallChart.interiorToPunctured_val, hzchart]
  rw [rightSeamTransition, dite_eq_left ⟨hzShell, hz1⟩]
  congr 1
  rw [show interiorRight c.toBallChart d.toBallChart aD z =
      inr c.toBallChart d.toBallChart aD.toHomeomorph (d.toBallChart.interiorToPunctured z)
      from rfl, hkey]

end RightTransition

section RightChain

variable (hRq : AtlasRight c d aD)

theorem mdifferentiableAt_reflectMapInv {y : csModel} (hy : y ≠ 0) :
    MDifferentiableAt (𝓡 3) (𝓡 3) (reflectMapInv aD.toHomeomorph) y := by
  rw [reflectMapInv_eq_reflectMap_symm aD]
  exact mdifferentiableAt_iff_differentiableAt.mpr
    (hasFDerivAt_reflectMap aD.symm hy).differentiableAt

theorem mfderiv_chartSymm_subtype (v : d.toBallChart.interior) (y : csModel)
    (hy : y ∈ d.toBallChart.chart.source)
    (hu : ((v : d.toBallChart.interior) : N.Carrier) = d.toBallChart.chart y) :
    mfderiv (𝓡 3) (𝓡 3)
        (fun z : d.toBallChart.interior => d.toBallChart.chart.symm (z : N.Carrier)) v
      = mfderiv (𝓡 3) (𝓡 3) ((d.toBallChart.chart.symm : N.Carrier → csModel))
          ((v : d.toBallChart.interior) : N.Carrier) := by
  have hsub : MDifferentiableAt (𝓡 3) (𝓡 3)
      (Subtype.val : d.toBallChart.interior → N.Carrier) v :=
    contMDiff_subtype_val.mdifferentiableAt (show (∞ : ℕ∞ω) ≠ 0 by simp)
  have hchart : MDifferentiableAt (𝓡 3) (𝓡 3)
      ((d.toBallChart.chart.symm : N.Carrier → csModel))
      ((Subtype.val : d.toBallChart.interior → N.Carrier) v) := by
    rw [hu]
    exact mdifferentiableAt_chartSymm d y hy
  have hcomp := mfderiv_comp (x := v) (f := (Subtype.val : d.toBallChart.interior → N.Carrier))
    (g := ((d.toBallChart.chart.symm : N.Carrier → csModel))) hchart hsub
  have hcomp' : mfderiv (𝓡 3) (𝓡 3)
      (fun z : d.toBallChart.interior => d.toBallChart.chart.symm (z : N.Carrier)) v =
      (mfderiv (𝓡 3) (𝓡 3) ((d.toBallChart.chart.symm : N.Carrier → csModel))
        ((Subtype.val : d.toBallChart.interior → N.Carrier) v)).comp
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : d.toBallChart.interior → N.Carrier) v) := hcomp
  rw [hcomp']
  apply ContinuousLinearMap.ext
  intro w
  change (mfderiv (𝓡 3) (𝓡 3) ((d.toBallChart.chart.symm : N.Carrier → csModel))
      ((v : d.toBallChart.interior) : N.Carrier))
    ((mfderiv (𝓡 3) (𝓡 3) (Subtype.val : d.toBallChart.interior → N.Carrier) v) w) =
    (mfderiv (𝓡 3) (𝓡 3) ((d.toBallChart.chart.symm : N.Carrier → csModel))
      ((v : d.toBallChart.interior) : N.Carrier)) w
  rw [DifferentialGeometry.mfderiv_subtype_val_apply]

end RightChain

section RightChainRule

variable (hRq : AtlasRight c d aD)

theorem seam_interiorRight_chain
    (hS : seamChartX c.toBallChart d.toBallChart aD.toHomeomorph ∈
      atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph))
    (x : qR c d aD hRq) (y : csModel) (hy : y ∈ SeamShell) (h1y : 1 < ‖y‖)
    (hu : ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier) = d.toBallChart.chart y)
    (hSp : (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) ∈ qS c d aD) :
    (mfderiv (𝓡 3) (𝓡 3) (seamChartFun c d aD)
        ⟨(x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph), hSp⟩).comp
      (mfderiv (𝓡 3) (𝓡 3) (interiorRight c.toBallChart d.toBallChart aD) (gR c d aD hRq x))
    = (mfderiv (𝓡 3) (𝓡 3) (reflectMapInv aD.toHomeomorph) y).comp
        (mfderiv (𝓡 3) (𝓡 3) ((d.toBallChart.chart.symm : N.Carrier → csModel))
          ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier)) := by
  have hysrc : y ∈ d.toBallChart.chart.source := chart_source_of_mem_SeamShell d y hy
  have hyne : y ≠ 0 := by
    intro h
    rw [h, norm_zero] at h1y
    linarith
  have hyT : ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier) ∈
      d.toBallChart.chart.target := by
    rw [hu]
    exact d.toBallChart.chart.map_source hysrc
  have hxsrc : (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) ∈
      (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph).source := hSp
  have hSx : MDifferentiableAt (𝓡 3) (𝓡 3)
      (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph)
      (interiorRight c.toBallChart d.toBallChart aD (gR c d aD hRq x)) := by
    rw [gR_spec c d aD hRq x]
    exact mdifferentiableAt_seamChartX_of_atlas c d aD hS _ hxsrc
  have hIR : MDifferentiableAt (𝓡 3) (𝓡 3)
      (interiorRight c.toBallChart d.toBallChart aD) (gR c d aD hRq x) :=
    ((interiorRight_isLocalDiffeomorph c.toBallChart d.toBallChart aD hRq)
      (gR c d aD hRq x)).mdifferentiableAt (show (∞ : ℕ∞ω) ≠ 0 by simp)
  have hcomp := mfderiv_comp (x := gR c d aD hRq x)
    (f := (interiorRight c.toBallChart d.toBallChart aD))
    (g := (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph)) hSx hIR
  have hcomp' : mfderiv (𝓡 3) (𝓡 3)
      (fun z : d.toBallChart.interior =>
        seamChartX c.toBallChart d.toBallChart aD.toHomeomorph
          (interiorRight c.toBallChart d.toBallChart aD z)) (gR c d aD hRq x) =
      (mfderiv (𝓡 3) (𝓡 3) (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph)
          (interiorRight c.toBallChart d.toBallChart aD (gR c d aD hRq x))).comp
        (mfderiv (𝓡 3) (𝓡 3) (interiorRight c.toBallChart d.toBallChart aD)
          (gR c d aD hRq x)) := hcomp
  have hev' : (fun z : d.toBallChart.interior =>
        seamChartX c.toBallChart d.toBallChart aD.toHomeomorph
          (interiorRight c.toBallChart d.toBallChart aD z)) =ᶠ[𝓝 (gR c d aD hRq x)]
      (fun z : d.toBallChart.interior =>
        rightSeamTransition c.toBallChart d.toBallChart aD.toHomeomorph
          (d.toBallChart.chart.symm (z : N.Carrier))) :=
    seam_interiorRight_eventuallyEq c d aD hRq x y hy h1y hu
  have hcontSymm : Filter.Tendsto
      (fun z : d.toBallChart.interior => d.toBallChart.chart.symm (z : N.Carrier))
      (𝓝 (gR c d aD hRq x)) (𝓝 y) := by
    have hsymm : d.toBallChart.chart.symm
        ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier) = y := by
      rw [hu]
      exact d.toBallChart.chart.left_inv hysrc
    have hcont : ContinuousAt
        (fun z : d.toBallChart.interior => d.toBallChart.chart.symm (z : N.Carrier))
        (gR c d aD hRq x) :=
      ((d.toBallChart.chart.symm.contMDiffOn_toFun.contMDiffAt
        (d.toBallChart.chart.symm.open_source.mem_nhds hyT)).continuousAt).comp
        (continuous_subtype_val.continuousAt (x := gR c d aD hRq x))
    rw [← hsymm]
    exact hcont
  have hevT : (fun z : d.toBallChart.interior =>
        rightSeamTransition c.toBallChart d.toBallChart aD.toHomeomorph
          (d.toBallChart.chart.symm (z : N.Carrier))) =ᶠ[𝓝 (gR c d aD hRq x)]
      (fun z : d.toBallChart.interior =>
        reflectMapInv aD.toHomeomorph (d.toBallChart.chart.symm (z : N.Carrier))) :=
    (rightSeamTransition_eventuallyEq c.toBallChart d.toBallChart aD.toHomeomorph y hy h1y)
      |>.comp_tendsto hcontSymm
  have hsubM : MDifferentiableAt (𝓡 3) (𝓡 3)
      (Subtype.val : d.toBallChart.interior → N.Carrier) (gR c d aD hRq x) :=
    contMDiff_subtype_val.mdifferentiableAt (show (∞ : ℕ∞ω) ≠ 0 by simp)
  have hsymmM : MDifferentiableAt (𝓡 3) (𝓡 3)
      ((d.toBallChart.chart.symm : N.Carrier → csModel))
      ((Subtype.val : d.toBallChart.interior → N.Carrier) (gR c d aD hRq x)) := by
    rw [hu]
    exact mdifferentiableAt_chartSymm d y hysrc
  have hsymmFun : MDifferentiableAt (𝓡 3) (𝓡 3)
      (fun z : d.toBallChart.interior => d.toBallChart.chart.symm (z : N.Carrier))
      (gR c d aD hRq x) := hsymmM.comp (gR c d aD hRq x) hsubM
  have hrefl : MDifferentiableAt (𝓡 3) (𝓡 3) (reflectMapInv aD.toHomeomorph) y :=
    mdifferentiableAt_reflectMapInv (aD := aD) hyne
  have hA : mfderiv (𝓡 3) (𝓡 3)
      (fun z : d.toBallChart.interior =>
        reflectMapInv aD.toHomeomorph (d.toBallChart.chart.symm (z : N.Carrier)))
      (gR c d aD hRq x) =
      (mfderiv (𝓡 3) (𝓡 3) (reflectMapInv aD.toHomeomorph) y).comp
        (mfderiv (𝓡 3) (𝓡 3) ((d.toBallChart.chart.symm : N.Carrier → csModel))
          ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier)) := by
    have hval : d.toBallChart.chart.symm
        ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier) = y := by
      rw [hu]
      exact d.toBallChart.chart.left_inv hysrc
    have hrefl' : MDifferentiableAt (𝓡 3) (𝓡 3) (reflectMapInv aD.toHomeomorph)
        (d.toBallChart.chart.symm ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier)) :=
      hval.symm ▸ hrefl
    have hcomp2 := mfderiv_comp (x := gR c d aD hRq x)
      (f := (fun z : d.toBallChart.interior => d.toBallChart.chart.symm (z : N.Carrier)))
      (g := (reflectMapInv aD.toHomeomorph)) hrefl' hsymmFun
    have hcomp3 : mfderiv (𝓡 3) (𝓡 3)
        (fun z : d.toBallChart.interior => reflectMapInv aD.toHomeomorph
          (d.toBallChart.chart.symm (z : N.Carrier))) (gR c d aD hRq x) =
        (mfderiv (𝓡 3) (𝓡 3) (reflectMapInv aD.toHomeomorph)
            (d.toBallChart.chart.symm ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier))).comp
          (mfderiv (𝓡 3) (𝓡 3)
            (fun z : d.toBallChart.interior => d.toBallChart.chart.symm (z : N.Carrier))
            (gR c d aD hRq x)) := hcomp2
    rw [hval] at hcomp3
    rw [mfderiv_chartSymm_subtype (d := d) (gR c d aD hRq x) y hysrc hu] at hcomp3
    exact hcomp3
  have hSfun : mfderiv (𝓡 3) (𝓡 3) (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph)
      (interiorRight c.toBallChart d.toBallChart aD (gR c d aD hRq x)) =
      mfderiv (𝓡 3) (𝓡 3) (seamChartFun c d aD)
        ⟨(x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph), hSp⟩ := by
    rw [gR_spec c d aD hRq x,
      ← mfderiv_seamChartFun c d aD hS
        ⟨(x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph), hSp⟩]
  rw [← hSfun]
  exact hcomp'.symm.trans ((hev'.mfderiv_eq.trans hevT.mfderiv_eq).trans hA)

end RightChainRule

section ReflectDifferential

theorem mdifferentiableAt_reflectMap' {y : csModel} (hy : y ≠ 0) :
    MDifferentiableAt (𝓡 3) (𝓡 3) (reflectMap aD.toHomeomorph) y :=
  mdifferentiableAt_iff_differentiableAt.mpr (hasFDerivAt_reflectMap aD hy).differentiableAt

theorem reflectMapInv_comp_reflectMap_eventuallyEq {y : csModel} (hy : y ∈ SeamShell) :
    (fun z : csModel => reflectMapInv aD.toHomeomorph (reflectMap aD.toHomeomorph z))
      =ᶠ[𝓝 y] id := by
  refine Filter.eventually_of_mem (isOpen_seamShell.mem_nhds hy) ?_
  intro z hz
  exact reflectMapInv_reflectMap aD.toHomeomorph ⟨z, hz⟩

theorem reflectMap_comp_reflectMapInv_eventuallyEq {y : csModel} (hy : y ∈ SeamShell) :
    (fun z : csModel => reflectMap aD.toHomeomorph (reflectMapInv aD.toHomeomorph z))
      =ᶠ[𝓝 y] id := by
  refine Filter.eventually_of_mem (isOpen_seamShell.mem_nhds hy) ?_
  intro z hz
  exact reflectMap_reflectMapInv aD.toHomeomorph ⟨z, hz⟩

theorem mfderiv_reflectMap_comp_reflectMapInv {y : csModel} (hy : y ∈ SeamShell) :
    (mfderiv (𝓡 3) (𝓡 3) (reflectMap aD.toHomeomorph) (reflectMapInv aD.toHomeomorph y)).comp
      (mfderiv (𝓡 3) (𝓡 3) (reflectMapInv aD.toHomeomorph) y)
      = ContinuousLinearMap.id ℝ csModel := by
  have hyne : y ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (by linarith [hy.1]))
  have hinvne : reflectMapInv aD.toHomeomorph y ≠ 0 := by
    intro h
    have hnorm := norm_reflectMapInv (a := aD.toHomeomorph) (x := y) (by linarith [hy.2])
    rw [h, norm_zero] at hnorm
    linarith [hy.2]
  have hcomp := mfderiv_comp (x := y) (f := (reflectMapInv aD.toHomeomorph))
    (g := (reflectMap aD.toHomeomorph))
    (mdifferentiableAt_reflectMap' (aD := aD) (y := reflectMapInv aD.toHomeomorph y) hinvne)
    (mdifferentiableAt_reflectMapInv (aD := aD) (y := y) hyne)
  have hcomp' : mfderiv (𝓡 3) (𝓡 3)
      (fun z : csModel => reflectMap aD.toHomeomorph (reflectMapInv aD.toHomeomorph z)) y =
      (mfderiv (𝓡 3) (𝓡 3) (reflectMap aD.toHomeomorph) (reflectMapInv aD.toHomeomorph y)).comp
        (mfderiv (𝓡 3) (𝓡 3) (reflectMapInv aD.toHomeomorph) y) := hcomp
  rw [Filter.EventuallyEq.mfderiv_eq (reflectMap_comp_reflectMapInv_eventuallyEq (aD := aD) hy),
    mfderiv_id] at hcomp'
  exact hcomp'.symm

theorem mfderiv_reflectMapInv_comp_reflectMap {y : csModel} (hy : y ∈ SeamShell) :
    (mfderiv (𝓡 3) (𝓡 3) (reflectMapInv aD.toHomeomorph) y).comp
      (mfderiv (𝓡 3) (𝓡 3) (reflectMap aD.toHomeomorph) (reflectMapInv aD.toHomeomorph y))
      = ContinuousLinearMap.id ℝ csModel := by
  have hyne : y ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (by linarith [hy.1]))
  have hinvne : reflectMapInv aD.toHomeomorph y ≠ 0 := by
    intro h
    have hnorm := norm_reflectMapInv (a := aD.toHomeomorph) (x := y) (by linarith [hy.2])
    rw [h, norm_zero] at hnorm
    linarith [hy.2]
  have hmem : reflectMapInv aD.toHomeomorph y ∈ SeamShell :=
    reflectMapInv_mem_SeamShell aD.toHomeomorph y hy
  have hcomp := mfderiv_comp (x := reflectMapInv aD.toHomeomorph y)
    (f := (reflectMap aD.toHomeomorph)) (g := (reflectMapInv aD.toHomeomorph))
    (mdifferentiableAt_reflectMapInv (aD := aD)
      (y := reflectMap aD.toHomeomorph (reflectMapInv aD.toHomeomorph y)) (by
        rw [reflectMap_reflectMapInv aD.toHomeomorph ⟨y, hy⟩]
        exact hyne))
    (mdifferentiableAt_reflectMap' (aD := aD) (y := reflectMapInv aD.toHomeomorph y) hinvne)
  have hcomp' : mfderiv (𝓡 3) (𝓡 3)
      (fun z : csModel => reflectMapInv aD.toHomeomorph (reflectMap aD.toHomeomorph z))
      (reflectMapInv aD.toHomeomorph y) =
      (mfderiv (𝓡 3) (𝓡 3) (reflectMapInv aD.toHomeomorph)
        (reflectMap aD.toHomeomorph (reflectMapInv aD.toHomeomorph y))).comp
        (mfderiv (𝓡 3) (𝓡 3) (reflectMap aD.toHomeomorph)
          (reflectMapInv aD.toHomeomorph y)) := hcomp
  rw [Filter.EventuallyEq.mfderiv_eq (reflectMapInv_comp_reflectMap_eventuallyEq (aD := aD) hmem),
    mfderiv_id, reflectMap_reflectMapInv aD.toHomeomorph ⟨y, hy⟩] at hcomp'
  exact hcomp'.symm

theorem fderiv_reflectMap_comp_reflectMapInv {y : csModel} (hy : y ∈ SeamShell) :
    (fderiv ℝ (reflectMap aD.toHomeomorph) (reflectMapInv aD.toHomeomorph y)).comp
      (fderiv ℝ (reflectMapInv aD.toHomeomorph) y)
      = ContinuousLinearMap.id ℝ csModel := by
  have h := mfderiv_reflectMap_comp_reflectMapInv (aD := aD) hy
  rwa [mfderiv_eq_fderiv, mfderiv_eq_fderiv] at h

theorem fderiv_reflectMapInv_comp_reflectMap {y : csModel} (hy : y ∈ SeamShell) :
    (fderiv ℝ (reflectMapInv aD.toHomeomorph) y).comp
      (fderiv ℝ (reflectMap aD.toHomeomorph) (reflectMapInv aD.toHomeomorph y))
      = ContinuousLinearMap.id ℝ csModel := by
  have h := mfderiv_reflectMapInv_comp_reflectMap (aD := aD) hy
  rwa [mfderiv_eq_fderiv, mfderiv_eq_fderiv] at h

end ReflectDifferential

section ReflectDifferentialEquiv

def reflectDifferential {y : csModel} (hy : y ∈ SeamShell) :
    csModel ≃L[ℝ] csModel where
  toFun := fderiv ℝ (reflectMapInv aD.toHomeomorph) y
  invFun := fderiv ℝ (reflectMap aD.toHomeomorph) (reflectMapInv aD.toHomeomorph y)
  left_inv := fun v =>
    DFunLike.congr_fun (fderiv_reflectMap_comp_reflectMapInv (aD := aD) hy) v
  right_inv := fun v =>
    DFunLike.congr_fun (fderiv_reflectMapInv_comp_reflectMap (aD := aD) hy) v
  map_add' := (fderiv ℝ (reflectMapInv aD.toHomeomorph) y).map_add
  map_smul' := (fderiv ℝ (reflectMapInv aD.toHomeomorph) y).map_smul
  continuous_toFun := (fderiv ℝ (reflectMapInv aD.toHomeomorph) y).cont
  continuous_invFun :=
    (fderiv ℝ (reflectMap aD.toHomeomorph) (reflectMapInv aD.toHomeomorph y)).cont

theorem reflectDifferential_toLinearMap_eq {y : csModel} (hy : y ∈ SeamShell) :
    ((reflectDifferential (aD := aD) hy).toLinearEquiv : csModel →ₗ[ℝ] csModel)
      = fderiv ℝ (reflectMapInv aD.toHomeomorph) y :=
  rfl


theorem det_reflectDifferential_pos
    (ha : aD.preservesOrientation (DifferentialGeometry.sphereOrientation 2 (by decide))
      (DifferentialGeometry.sphereOrientation 2 (by decide)).opposite)
    {y : csModel} (hy : y ∈ SeamShell) :
    0 < LinearMap.det ((reflectDifferential (aD := aD) hy).toLinearEquiv :
      csModel →ₗ[ℝ] csModel) := by
  rw [reflectDifferential_toLinearMap_eq (aD := aD) hy]
  exact det_fderiv_reflectMapInv_pos aD ha (by linarith [hy.1]) (by linarith [hy.2])

theorem map_reflectDifferential_stdOrientationModel
    (ha : aD.preservesOrientation (DifferentialGeometry.sphereOrientation 2 (by decide))
      (DifferentialGeometry.sphereOrientation 2 (by decide)).opposite)
    {y : csModel} (hy : y ∈ SeamShell) :
    Orientation.map (Fin (Module.finrank ℝ csModel)) (reflectDifferential (aD := aD) hy).toLinearEquiv
      stdOrientationModel = stdOrientationModel :=
  (Orientation.map_eq_iff_det_pos stdOrientationModel
    (reflectDifferential (aD := aD) hy).toLinearEquiv (Fintype.card_fin _)).2
    (det_reflectDifferential_pos (aD := aD) ha hy)

theorem map_reflectDifferential_symm_stdOrientationModel
    (ha : aD.preservesOrientation (DifferentialGeometry.sphereOrientation 2 (by decide))
      (DifferentialGeometry.sphereOrientation 2 (by decide)).opposite)
    {y : csModel} (hy : y ∈ SeamShell) :
    Orientation.map (Fin (Module.finrank ℝ csModel))
      (reflectDifferential (aD := aD) hy).symm.toLinearEquiv stdOrientationModel
      = stdOrientationModel := by
  have h := congrArg (Orientation.map (Fin (Module.finrank ℝ csModel))
    (reflectDifferential (aD := aD) hy).symm.toLinearEquiv)
    (map_reflectDifferential_stdOrientationModel (aD := aD) ha hy)
  rw [orientation_map_map_trans (R := ℝ)
      (reflectDifferential (aD := aD) hy).toLinearEquiv
      (reflectDifferential (aD := aD) hy).symm.toLinearEquiv stdOrientationModel] at h
  have hcomp : (reflectDifferential (aD := aD) hy).toLinearEquiv.trans
      (reflectDifferential (aD := aD) hy).symm.toLinearEquiv = LinearEquiv.refl ℝ csModel :=
    LinearEquiv.ext (fun v => (reflectDifferential (aD := aD) hy).symm_apply_apply v)
  rw [hcomp, Orientation.map_refl] at h
  exact h.symm

end ReflectDifferentialEquiv

section RightAgreement

variable (hRq : AtlasRight c d aD)


theorem chartTangentEquiv_eq_chartSymmEquiv_symm (y : csModel)
    (hy : y ∈ d.toBallChart.chart.source) :
    (chartTangentEquiv d hy).toLinearEquiv
      = (chartSymmEquiv d y hy).symm.toLinearEquiv := by
  apply LinearEquiv.ext
  intro v
  rfl

end RightAgreement

section HalfBound

omit [ChartedSpace csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)]
  [IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)] in
theorem half_lt_norm_seamChartX_of_mem_qS (p : ConnectedSumQuotient c.toBallChart
    d.toBallChart aD.toHomeomorph) (hp : p ∈ qS c d aD) :
    1 / 2 < ‖seamChartX c.toBallChart d.toBallChart aD.toHomeomorph p‖ := by
  rw [mem_qS_iff] at hp
  rw [seamChartX_source c.toBallChart d.toBallChart aD.toHomeomorph] at hp
  obtain ⟨⟨w, hw⟩, hwmap⟩ := hp
  rw [← hwmap, seamChartX_apply_seamMap]
  exact hw.1

end HalfBound

section RightOrientation

variable (hRq : AtlasRight c d aD)

theorem seamDifferential_symm_eq_right
    (hS : seamChartX c.toBallChart d.toBallChart aD.toHomeomorph ∈
      atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph))
    (x : qR c d aD hRq) (y : csModel) (hy : y ∈ SeamShell) (h1y : 1 < ‖y‖)
    (hdeep : ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier) = d.toBallChart.chart y)
    (hSp : (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) ∈ qS c d aD) :
    (seamDifferential c d aD hS ⟨(x : ConnectedSumQuotient c.toBallChart
        d.toBallChart aD.toHomeomorph), hSp⟩).symm.toLinearEquiv
      = (reflectDifferential (aD := aD) hy).symm.toLinearEquiv.trans
          ((chartTangentEquiv d (chart_source_of_mem_SeamShell d y hy)).toLinearEquiv.trans
            (rightDifferential c d aD hRq x).symm.toLinearEquiv) := by
  have hysrc : y ∈ d.toBallChart.chart.source := chart_source_of_mem_SeamShell d y hy
  have hchain := seam_interiorRight_chain c d aD hRq hS x y hy h1y hdeep hSp
  apply LinearEquiv.ext
  intro w
  change (seamDifferential c d aD hS ⟨(x : ConnectedSumQuotient c.toBallChart
      d.toBallChart aD.toHomeomorph), hSp⟩).symm w =
    (mfderiv (𝓡 3) (𝓡 3) (interiorRight c.toBallChart d.toBallChart aD) (gR c d aD hRq x))
      ((mfderiv (𝓡 3) (𝓡 3) ((d.toBallChart.chart : csModel → N.Carrier)) y)
        ((fderiv ℝ (reflectMap aD.toHomeomorph) (reflectMapInv aD.toHomeomorph y)) w))
  refine (seamDifferential c d aD hS ⟨(x : ConnectedSumQuotient c.toBallChart
    d.toBallChart aD.toHomeomorph), hSp⟩).toLinearEquiv.injective ?_
  erw [show (seamDifferential c d aD hS ⟨(x : ConnectedSumQuotient c.toBallChart
        d.toBallChart aD.toHomeomorph), hSp⟩)
      ((seamDifferential c d aD hS ⟨(x : ConnectedSumQuotient c.toBallChart
        d.toBallChart aD.toHomeomorph), hSp⟩).symm w) = w from
    LinearEquiv.apply_symm_apply _ w]
  change w = (mfderiv (𝓡 3) (𝓡 3) (seamChartFun c d aD)
      ⟨(x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph), hSp⟩)
    ((mfderiv (𝓡 3) (𝓡 3) (interiorRight c.toBallChart d.toBallChart aD) (gR c d aD hRq x))
      ((mfderiv (𝓡 3) (𝓡 3) ((d.toBallChart.chart : csModel → N.Carrier)) y)
        ((fderiv ℝ (reflectMap aD.toHomeomorph) (reflectMapInv aD.toHomeomorph y)) w)))
  have hz : (mfderiv (𝓡 3) (𝓡 3) ((d.toBallChart.chart.symm : N.Carrier → csModel))
      ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier))
      ((mfderiv (𝓡 3) (𝓡 3) ((d.toBallChart.chart : csModel → N.Carrier)) y)
        ((fderiv ℝ (reflectMap aD.toHomeomorph) (reflectMapInv aD.toHomeomorph y)) w))
      = (fderiv ℝ (reflectMap aD.toHomeomorph) (reflectMapInv aD.toHomeomorph y)) w := by
    have h1 : (mfderiv (𝓡 3) (𝓡 3) ((d.toBallChart.chart.symm : N.Carrier → csModel))
        (d.toBallChart.chart y))
        ((mfderiv (𝓡 3) (𝓡 3) ((d.toBallChart.chart : csModel → N.Carrier)) y)
          ((fderiv ℝ (reflectMap aD.toHomeomorph) (reflectMapInv aD.toHomeomorph y)) w))
        = (fderiv ℝ (reflectMap aD.toHomeomorph) (reflectMapInv aD.toHomeomorph y)) w :=
      DFunLike.congr_fun (mfderiv_chartSymm_comp_chart d y hysrc) _
    exact hdeep.symm ▸ h1
  rw [show (mfderiv (𝓡 3) (𝓡 3) (seamChartFun c d aD)
        ⟨(x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph), hSp⟩)
      ((mfderiv (𝓡 3) (𝓡 3) (interiorRight c.toBallChart d.toBallChart aD)
        (gR c d aD hRq x))
        ((mfderiv (𝓡 3) (𝓡 3) ((d.toBallChart.chart : csModel → N.Carrier)) y)
          ((fderiv ℝ (reflectMap aD.toHomeomorph) (reflectMapInv aD.toHomeomorph y)) w)))
      = (mfderiv (𝓡 3) (𝓡 3) (reflectMapInv aD.toHomeomorph) y)
        ((mfderiv (𝓡 3) (𝓡 3) ((d.toBallChart.chart.symm : N.Carrier → csModel))
          ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier))
          ((mfderiv (𝓡 3) (𝓡 3) ((d.toBallChart.chart : csModel → N.Carrier)) y)
            ((fderiv ℝ (reflectMap aD.toHomeomorph) (reflectMapInv aD.toHomeomorph y)) w)))
      from DFunLike.congr_fun hchain _]
  rw [hz, mfderiv_eq_fderiv]
  exact ((ContinuousLinearEquiv.apply_symm_apply (reflectDifferential (aD := aD) hy) w)).symm

theorem rightSmoothOrientation_apply_eq_seamSmoothOrientation
    (ha : aD.preservesOrientation (DifferentialGeometry.sphereOrientation 2 (by decide))
      (DifferentialGeometry.sphereOrientation 2 (by decide)).opposite)
    (hS : seamChartX c.toBallChart d.toBallChart aD.toHomeomorph ∈
      atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph))
    (x : qR c d aD hRq)
    (hSp : (x : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) ∈ qS c d aD) :
    (rightSmoothOrientation c d aD hRq).val x =
      (seamSmoothOrientation c d aD hS).val ⟨(x : ConnectedSumQuotient c.toBallChart
        d.toBallChart aD.toHomeomorph), hSp⟩ := by
  obtain ⟨y, hy, h1y, hdeep, -⟩ := exists_right_coordinate c d aD hRq x hSp
    (half_lt_norm_seamChartX_of_mem_qS c d aD _ hSp)
  have hysrc : y ∈ d.toBallChart.chart.source := chart_source_of_mem_SeamShell d y hy
  have hchain := seamDifferential_symm_eq_right c d aD hRq hS x y hy h1y hdeep hSp
  have hchart : N.orientation.orientation
      ((gR c d aD hRq x : d.toBallChart.interior) : N.Carrier) =
      Orientation.map (Fin 3) (chartTangentEquiv d hysrc).toLinearEquiv (stdOrientation y) := by
    rw [hdeep]
    exact orientation_eq_map_chartTangentEquiv d hysrc
  rw [rightSmoothOrientation_apply_map, seamSmoothOrientation_apply_map, hchain,
    rightDifferentialEquiv_eq]
  erw [← orientation_map_map_trans (R := ℝ)
    (reflectDifferential (aD := aD) hy).symm.toLinearEquiv
    ((chartTangentEquiv d hysrc).toLinearEquiv.trans
      (rightDifferential c d aD hRq x).symm.toLinearEquiv) stdOrientationModel]
  rw [map_reflectDifferential_symm_stdOrientationModel (aD := aD) ha hy]
  erw [← orientation_map_map_trans (R := ℝ) (chartTangentEquiv d hysrc).toLinearEquiv
    (rightDifferential c d aD hRq x).symm.toLinearEquiv stdOrientationModel]
  rw [hchart]
  rw [show Orientation.reindex ℝ csModel csIdx
        (Orientation.map (Fin 3) (chartTangentEquiv d hysrc).toLinearEquiv (stdOrientation y)) =
      Orientation.map (Fin (Module.finrank ℝ csModel)) (chartTangentEquiv d hysrc).toLinearEquiv
        (Orientation.reindex ℝ csModel csIdx (stdOrientation y)) from
    orientation_reindex_map_comm csIdx (chartTangentEquiv d hysrc).toLinearEquiv (stdOrientation y)]
  rw [← stdOrientationModel_eq_reindex y]
  rfl

end RightOrientation

section IndexReindex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem reindex_symm_reindex {ι ι' : Type*} (e : ι ≃ ι') (o : Orientation ℝ E ι) :
    Orientation.reindex ℝ E e.symm (Orientation.reindex ℝ E e o) = o := by
  rw [← Orientation.reindex_symm]
  exact (Orientation.reindex ℝ E e).symm_apply_apply o

omit [FiniteDimensional ℝ E] in
theorem reindex_symm_map_reindex {ι ι' : Type*} (e : ι ≃ ι') (f : E ≃ₗ[ℝ] E)
    (o : Orientation ℝ E ι) :
    Orientation.reindex ℝ E e.symm
        (Orientation.map ι' f (Orientation.reindex ℝ E e o)) =
      Orientation.map ι f o := by
  rw [orientation_reindex_map_comm (R := ℝ) (e := e.symm) f (Orientation.reindex ℝ E e o)]
  rw [reindex_symm_reindex e o]

end IndexReindex

section Assembly

variable (hLq : AtlasLeft c d aD) (hRq : AtlasRight c d aD)
variable (hS : seamChartX c.toBallChart d.toBallChart aD.toHomeomorph ∈
  atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph))
include hLq hRq hS

omit hS in
theorem mem_qS_of_not_mem_qL_qR
    (p : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)
    (hL : p ∉ qL c d aD hLq) (hR : p ∉ qR c d aD hRq) : p ∈ qS c d aD := by
  have h := range_interior_left_right_union_seamChartX_source c d aD
  have hmem : p ∈ Set.range (interiorLeft c.toBallChart d.toBallChart aD) ∪
      Set.range (interiorRight c.toBallChart d.toBallChart aD) ∪
      (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph).source := by
    rw [h]
    exact Set.mem_univ p
  rcases hmem with (h1 | h2) | h3
  · exact absurd h1 hL
  · exact absurd h2 hR
  · exact h3

theorem exists_manifoldOrientation_of_pieces
    (ha : aD.preservesOrientation (DifferentialGeometry.sphereOrientation 2 (by decide))
      (DifferentialGeometry.sphereOrientation 2 (by decide)).opposite) :
    ∃ O : DifferentialGeometry.ManifoldOrientation (𝓡 3)
        (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) 3,
      (∀ x : c.toBallChart.interior, Orientation.map (Fin 3)
          ((interiorLeft_isLocalDiffeomorph c.toBallChart d.toBallChart aD hLq).mfderivToContinuousLinearEquiv
            (by simp) x).toLinearEquiv (M.orientation.orientation x)
        = O.orientation (interiorLeft c.toBallChart d.toBallChart aD x)) ∧
      (∀ x : d.toBallChart.interior, Orientation.map (Fin 3)
          ((interiorRight_isLocalDiffeomorph c.toBallChart d.toBallChart aD hRq).mfderivToContinuousLinearEquiv
            (by simp) x).toLinearEquiv (N.orientation.orientation x)
        = O.orientation (interiorRight c.toBallChart d.toBallChart aD x)) := by
  classical
  let U : Option Bool → TopologicalSpace.Opens
      (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) := fun i =>
    match i with
    | none => qL c d aD hLq
    | some false => qR c d aD hRq
    | some true => qS c d aD
  let piece : (i : Option Bool) → SmoothOrientation (𝓡 3) (U i) := fun i =>
    match i with
    | none => leftSmoothOrientation c d aD hLq
    | some false => rightSmoothOrientation c d aD hRq
    | some true => seamSmoothOrientation c d aD hS
  have hcover : ∀ p : ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph,
      ∃ i, p ∈ U i := by
    intro p
    by_cases hL : p ∈ qL c d aD hLq
    · exact ⟨none, hL⟩
    · by_cases hR : p ∈ qR c d aD hRq
      · exact ⟨some false, hR⟩
      · exact ⟨some true, mem_qS_of_not_mem_qL_qR c d aD hLq hRq p hL hR⟩
  have heq : ∀ (i j : Option Bool) (p : ConnectedSumQuotient c.toBallChart d.toBallChart
        aD.toHomeomorph) (hi : p ∈ U i) (hj : p ∈ U j),
      (piece i).val ⟨p, hi⟩ = (piece j).val ⟨p, hj⟩ := by
    intro i j p hi hj
    rcases i with _ | (b | b) <;> rcases j with _ | (b' | b')
    · rfl
    · exact absurd hj (Set.disjoint_left.mp
        (range_interiorLeft_disjoint_range_interiorRight c d aD) hi)
    · exact leftSmoothOrientation_apply_eq_seamSmoothOrientation c d aD hLq hS ⟨p, hi⟩ hj
    · exact absurd hi (Set.disjoint_left.mp
        (range_interiorLeft_disjoint_range_interiorRight c d aD) hj)
    · rfl
    · exact rightSmoothOrientation_apply_eq_seamSmoothOrientation c d aD hRq ha hS ⟨p, hi⟩ hj
    · exact (leftSmoothOrientation_apply_eq_seamSmoothOrientation c d aD hLq hS ⟨p, hj⟩ hi).symm
    · exact (rightSmoothOrientation_apply_eq_seamSmoothOrientation c d aD hRq ha hS ⟨p, hj⟩ hi).symm
    · rfl
  let SO : SmoothOrientation (𝓡 3)
      (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph) :=
    glueSmoothOrientations (𝓡 3) U piece hcover heq
  obtain ⟨O', hO'⟩ := exists_manifoldOrientation_eq_of_smoothOrientation (𝓡 3) SO
  refine ⟨reindexManifoldOrientation (𝓡 3) csIdx.symm O', ?_, ?_⟩
  · intro x
    have hSO : SO.val (interiorLeft c.toBallChart d.toBallChart aD x)
        = (leftSmoothOrientation c d aD hLq).val
            ⟨interiorLeft c.toBallChart d.toBallChart aD x, ⟨x, rfl⟩⟩ :=
      glueSmoothOrientations_apply (𝓡 3) U piece hcover heq none
        ⟨interiorLeft c.toBallChart d.toBallChart aD x, ⟨x, rfl⟩⟩
    have hgL : gL c d aD hLq
        ⟨interiorLeft c.toBallChart d.toBallChart aD x, ⟨x, rfl⟩⟩ = x := gL_apply c d aD hLq x
    have hval : (leftSmoothOrientation c d aD hLq).val
        ⟨interiorLeft c.toBallChart d.toBallChart aD x, ⟨x, rfl⟩⟩
        = Orientation.map (Fin (Module.finrank ℝ csModel))
            (leftDifferential c d aD hLq
              ⟨interiorLeft c.toBallChart d.toBallChart aD x, ⟨x, rfl⟩⟩).symm.toLinearEquiv
            (Orientation.reindex ℝ csModel csIdx (M.orientation.orientation x)) := by
      rw [leftSmoothOrientation_apply_map, hgL, leftDifferentialEquiv_eq]
      rfl
    have hleft : (leftDifferential c d aD hLq
          ⟨interiorLeft c.toBallChart d.toBallChart aD x, ⟨x, rfl⟩⟩).symm.toLinearEquiv
        = ((interiorLeft_isLocalDiffeomorph c.toBallChart d.toBallChart aD hLq).mfderivToContinuousLinearEquiv
            (by simp) x).toLinearEquiv := by
      apply LinearEquiv.ext
      intro v
      change (mfderiv (𝓡 3) (𝓡 3) (interiorLeft c.toBallChart d.toBallChart aD)
          (gL c d aD hLq ⟨interiorLeft c.toBallChart d.toBallChart aD x, ⟨x, rfl⟩⟩)) v
        = (mfderiv (𝓡 3) (𝓡 3) (interiorLeft c.toBallChart d.toBallChart aD) x) v
      rw [hgL]
    change Orientation.map (Fin 3)
        ((interiorLeft_isLocalDiffeomorph c.toBallChart d.toBallChart aD hLq).mfderivToContinuousLinearEquiv
          (by simp) x).toLinearEquiv (M.orientation.orientation x)
      = Orientation.reindex ℝ csModel csIdx.symm
          (O'.orientation (interiorLeft c.toBallChart d.toBallChart aD x))
    rw [hO']
    rw [hSO]
    rw [hval]
    rw [hleft]
    exact (reindex_symm_map_reindex (E := csModel) csIdx
      ((interiorLeft_isLocalDiffeomorph c.toBallChart d.toBallChart aD hLq).mfderivToContinuousLinearEquiv
        (by simp) x).toLinearEquiv (M.orientation.orientation x)).symm
  · intro x
    have hSO : SO.val (interiorRight c.toBallChart d.toBallChart aD x)
        = (rightSmoothOrientation c d aD hRq).val
            ⟨interiorRight c.toBallChart d.toBallChart aD x, ⟨x, rfl⟩⟩ :=
      glueSmoothOrientations_apply (𝓡 3) U piece hcover heq (some false)
        ⟨interiorRight c.toBallChart d.toBallChart aD x, ⟨x, rfl⟩⟩
    have hgR : gR c d aD hRq
        ⟨interiorRight c.toBallChart d.toBallChart aD x, ⟨x, rfl⟩⟩ = x := gR_apply c d aD hRq x
    have hval : (rightSmoothOrientation c d aD hRq).val
        ⟨interiorRight c.toBallChart d.toBallChart aD x, ⟨x, rfl⟩⟩
        = Orientation.map (Fin (Module.finrank ℝ csModel))
            (rightDifferential c d aD hRq
              ⟨interiorRight c.toBallChart d.toBallChart aD x, ⟨x, rfl⟩⟩).symm.toLinearEquiv
            (Orientation.reindex ℝ csModel csIdx (N.orientation.orientation x)) := by
      rw [rightSmoothOrientation_apply_map, hgR, rightDifferentialEquiv_eq]
      rfl
    have hright : (rightDifferential c d aD hRq
          ⟨interiorRight c.toBallChart d.toBallChart aD x, ⟨x, rfl⟩⟩).symm.toLinearEquiv
        = ((interiorRight_isLocalDiffeomorph c.toBallChart d.toBallChart aD hRq).mfderivToContinuousLinearEquiv
            (by simp) x).toLinearEquiv := by
      apply LinearEquiv.ext
      intro v
      change (mfderiv (𝓡 3) (𝓡 3) (interiorRight c.toBallChart d.toBallChart aD)
          (gR c d aD hRq ⟨interiorRight c.toBallChart d.toBallChart aD x, ⟨x, rfl⟩⟩)) v
        = (mfderiv (𝓡 3) (𝓡 3) (interiorRight c.toBallChart d.toBallChart aD) x) v
      rw [hgR]
    change Orientation.map (Fin 3)
        ((interiorRight_isLocalDiffeomorph c.toBallChart d.toBallChart aD hRq).mfderivToContinuousLinearEquiv
          (by simp) x).toLinearEquiv (N.orientation.orientation x)
      = Orientation.reindex ℝ csModel csIdx.symm
          (O'.orientation (interiorRight c.toBallChart d.toBallChart aD x))
    rw [hO']
    rw [hSO]
    rw [hval]
    rw [hright]
    exact (reindex_symm_map_reindex (E := csModel) csIdx
      ((interiorRight_isLocalDiffeomorph c.toBallChart d.toBallChart aD hRq).mfderivToContinuousLinearEquiv
        (by simp) x).toLinearEquiv (N.orientation.orientation x)).symm

end Assembly

theorem exists_smooth_connected_sum_of_orientation_data
    {M : ConnectedClosedOrientedManifold.{u} 3} {N : ConnectedClosedOrientedManifold.{v} 3}
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment) :
    Nonempty (SmoothConnectedSum c d a) := by
  refine AssemblyReduction.exists_smooth_connected_sum_of_orientation c d a ?_
  let _ := csChartedSpace c.toBallChart d.toBallChart a.1.toHomeomorph
  let _ := csIsManifold c.toBallChart d.toBallChart a.1.toHomeomorph (contDiffOn_reflectMap a.1)
    (contDiffOn_reflectMapInv a.1)
  exact exists_manifoldOrientation_of_pieces (M := M.toClosedOrientedManifold)
    (N := N.toClosedOrientedManifold) c d a.1
    (fun f hf => mem_atlas_leftChart c.toBallChart d.toBallChart a.1.toHomeomorph f hf)
    (fun g hg => mem_atlas_rightChart c.toBallChart d.toBallChart a.1.toHomeomorph g hg)
    (mem_atlas_seamChartX c.toBallChart d.toBallChart a.1.toHomeomorph) a.2


end OrientationAssembly
