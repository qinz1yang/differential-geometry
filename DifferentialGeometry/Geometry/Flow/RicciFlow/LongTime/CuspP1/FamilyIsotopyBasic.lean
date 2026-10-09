import DifferentialGeometry.Topology.Manifold.InverseFunction
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.FiniteOrder.CompactSupportFlow
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# CP1-D5: isotopy extension for a smooth family of embeddings, step 1

The graph map `G (t, x) = (t, F (t, x))` of a jointly smooth family `F` of immersions between
manifolds of equal dimension is a local diffeomorphism.
-/

set_option autoImplicit false
open scoped Manifold ContDiff Topology
open Set Function Filter
noncomputable section
namespace GC.LongTime.CuspP1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- the graph map of a family -/
def graphMap_CPD5 (F : ℝ × N → M) : ℝ × N → ℝ × M := fun p => (p.1, F p)

theorem isInvertible_of_injective_CPD5 {A : (ℝ × E) →L[ℝ] (ℝ × E)} (h : Function.Injective A) :
    A.IsInvertible := by
  have hs : Function.Surjective A := LinearMap.injective_iff_surjective.mp h
  exact ⟨ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr h)
    (LinearMap.range_eq_top.mpr hs), rfl⟩

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] [IsManifold I ∞ M] in
theorem mfderiv_slice_CPD5 {F : ℝ × N → M} {t : ℝ} {x : N}
    (hF : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) I F (t, x)) :
    mfderiv I I (fun y => F (t, y)) x =
      (mfderiv (𝓘(ℝ, ℝ).prod I) I F (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
  have h1 : (fun y => F (t, y)) = F ∘ (fun y : N => (t, y)) := rfl
  have hmd : MDifferentiableAt I (𝓘(ℝ, ℝ).prod I) (fun y : N => (t, y)) x :=
    mdifferentiableAt_const.prodMk mdifferentiableAt_id
  rw [h1, mfderiv_comp x hF hmd, mfderiv_prod_right]
  rfl

theorem isLocalDiffeomorphAt_graphMap_CPD5 {F : ℝ × N → M} {J : Set ℝ} {U : Set N}
    (hJ : IsOpen J) (hU : IsOpen U)
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ F (J ×ˢ U))
    (himm : ∀ t ∈ J, ∀ x ∈ U, Function.Injective (mfderiv I I (fun y => F (t, y)) x))
    {p : ℝ × N} (hp : p ∈ J ×ˢ U) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞ (graphMap_CPD5 F) p := by
  have hopen : IsOpen (J ×ˢ U) := hJ.prod hU
  have hG : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞ (graphMap_CPD5 F) (J ×ˢ U) :=
    contMDiffOn_fst.prodMk hF
  refine DifferentialGeometry.Topology.isLocalDiffeomorphAt_of_contMDiffOn_of_isInvertible_mfderiv
    hopen hp hG ?_
  have hFd : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) I F p :=
    (hF.contMDiffAt (hopen.mem_nhds hp)).mdifferentiableAt (by simp)
  have hfst : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) (Prod.fst : ℝ × N → ℝ) p :=
    mdifferentiableAt_fst
  have hder : mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) (graphMap_CPD5 F) p =
      (ContinuousLinearMap.fst ℝ ℝ E).prod (mfderiv (𝓘(ℝ, ℝ).prod I) I F p) := by
    have := mfderiv_prodMk hfst hFd
    rw [mfderiv_fst] at this
    exact this
  rw [hder]
  apply isInvertible_of_injective_CPD5
  intro v w hvw
  have hvw' : (v.1, mfderiv (𝓘(ℝ, ℝ).prod I) I F p v) = (w.1, mfderiv (𝓘(ℝ, ℝ).prod I) I F p w) :=
    hvw
  have h1 : v.1 = w.1 := (Prod.ext_iff.mp hvw').1
  obtain ⟨t, x⟩ := p
  have hslice := mfderiv_slice_CPD5 hFd
  have hinj := himm t hp.1 x hp.2
  let A : (ℝ × E) →L[ℝ] E := mfderiv (𝓘(ℝ, ℝ).prod I) I F (t, x)
  have h2 : A v = A w := (Prod.ext_iff.mp hvw').2
  have : v.2 = w.2 := by
    apply hinj
    rw [hslice]
    change A (0, v.2) = A (0, w.2)
    have hv : ((0 : ℝ), v.2) = v - (v.1, 0) := by ext <;> simp
    have hw : ((0 : ℝ), w.2) = w - (w.1, 0) := by ext <;> simp
    rw [hv, hw, map_sub, map_sub, h2, h1]
  exact Prod.ext h1 this

end GC.LongTime.CuspP1
