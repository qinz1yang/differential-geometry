import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0SRiemannian
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0SRiemannianBundle
import DifferentialGeometry.Tensor.Multilinear.Fiber
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Riemannian

/-!
# CLM-valued continuity of the bundle inner product on the `(0, s)`-tensor bundle

Given a smooth Riemannian metric `g` on a manifold `M`, the bundle-fibre inner
product `innerBundleCLM g s b : Tensor0SSpace s I b →L[ℝ] Tensor0SSpace s I b →L[ℝ] ℝ`
varies continuously with the base point `b ∈ M` when viewed as a section of the
bundle of bilinear maps. The precise statement is that the total-space-valued
map

  `b ↦ TotalSpace.mk' (Tensor0SModel s ℝ E →L[ℝ] Tensor0SModel s ℝ E →L[ℝ] ℝ) b (innerBundleCLM g s b)`

is continuous on each chart-`α` base set, and globally continuous.

From this we derive a `ContinuousRiemannianMetric` structure on the `(0, s)`-tensor
bundle, and through Mathlib's mechanism this yields the
`IsContinuousRiemannianBundle (Tensor0SModel s ℝ E) (Tensor0SSpace s I)` instance.

## Strategy

1. A general lemma: in a finite-dim normed space `F` with basis `v`, pointwise
   continuity of `b ↦ u b (v i)` at `b₀` for every `i` implies operator-norm
   continuity of `b ↦ u b` at `b₀`. This is iterated to bilinear CLMs.

2. The chart-α inner CLM `chartTensorInnerPointwise_0sCLM g s α b` is shown to
   be operator-norm continuous in `b` on the chart-α base set, by applying the
   basis-continuity lemma to the finite basis of `Tensor0SModel s ℝ E`.

3. Through the bridge identity `tensorInnerPointwise_0s_bridge_identity`, the
   chart-α inner CLM is identified with `innerBundleCLM` precomposed with the
   trivialisation; using `Mathlib.Topology.VectorBundle.Hom.inCoordinates_apply_eq₂`
   this becomes the `inCoordinates` form of the total-space section.

4. `continuousAt_hom_bundle` then upgrades pointwise continuity in coordinates to
   continuity of the total-space-valued section.

5. The `ContinuousRiemannianMetric` is assembled and the
   `IsContinuousRiemannianBundle` instance falls out.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set IsManifold ContinuousLinearMap Bornology
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Tensor
namespace Tensor0SInnerSectionContinuity

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor.Tensor0SRiemannian
open DifferentialGeometry.Tensor.Tensor0SRiemannianBundle
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Step 1: CLM-continuity from pointwise continuity on a basis -/

set_option linter.unusedFintypeInType false in
/-- In a finite-dim normed `ℝ`-vector space `F`, pointwise continuity of
`b ↦ u b (v i)` at `b₀` on a basis `v i` implies operator-norm continuity of
`b ↦ u b` at `b₀`, where `u : M → F →L[ℝ] G`. -/
lemma continuousAt_clm_of_basis_continuousAt
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {N : Type*} [TopologicalSpace N]
    {ι : Type*} [Fintype ι] (v : Module.Basis ι ℝ F)
    {u : N → F →L[ℝ] G} {x₀ : N}
    (h : ∀ i, ContinuousAt (fun b => u b (v i)) x₀) :
    ContinuousAt u x₀ := by
  classical

  obtain ⟨C, _hCpos, hC⟩ := v.exists_opNorm_le (E := F) (F := G)

  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε

  have hC_pos : 0 < max C 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  set M_const : ℝ := ε / (2 * max C 1) with hM_def
  have hM_pos : 0 < M_const := by
    have h1 : 0 < 2 * max C 1 := by positivity
    exact div_pos hε h1

  have h_each : ∀ i, ∀ᶠ b in 𝓝 x₀,
      ‖(u b - u x₀) (v i)‖ < M_const := by
    intro i
    have hci := h i
    rw [ContinuousAt, Metric.tendsto_nhds] at hci
    have hci' := hci M_const hM_pos
    filter_upwards [hci'] with b hb
    have hdist : ‖u b (v i) - u x₀ (v i)‖ < M_const := by
      rw [← dist_eq_norm]; exact hb
    have heq : (u b - u x₀) (v i) = u b (v i) - u x₀ (v i) :=
      ContinuousLinearMap.sub_apply _ _ _
    rw [heq]
    exact hdist

  have h_all : ∀ᶠ b in 𝓝 x₀, ∀ i, ‖(u b - u x₀) (v i)‖ ≤ M_const := by
    rw [Filter.eventually_all]
    intro i
    filter_upwards [h_each i] with b hb
    exact hb.le

  filter_upwards [h_all] with b hb
  have hM_const_nn : 0 ≤ M_const := le_of_lt hM_pos
  have hopBound : ‖u b - u x₀‖ ≤ C * M_const := hC hM_const_nn hb
  have hC_le : C ≤ max C 1 := le_max_left _ _
  have hM_eq : C * M_const ≤ max C 1 * M_const := by
    have : (0 : ℝ) ≤ M_const := hM_const_nn
    nlinarith
  have hChain : ‖u b - u x₀‖ ≤ max C 1 * M_const :=
    le_trans hopBound hM_eq
  have hsimp : max C 1 * M_const = ε / 2 := by
    rw [hM_def]
    have hne : max C 1 ≠ 0 := ne_of_gt hC_pos
    field_simp
  rw [hsimp] at hChain
  rw [dist_eq_norm]
  exact lt_of_le_of_lt hChain (by linarith)

/-! ## Step 2: Iterating to bilinear CLM-continuity -/

set_option linter.unusedFintypeInType false in
/-- Bilinear version of `continuousAt_clm_of_basis_continuousAt`: pointwise
continuity of `b ↦ u b (v i) (v j)` for every basis pair `(i, j)` implies
operator-norm continuity of `b ↦ u b` as a bilinear CLM. -/
lemma continuousAt_bilin_of_basis_continuousAt
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {N : Type*} [TopologicalSpace N]
    {ι : Type*} [Fintype ι] (v : Module.Basis ι ℝ F)
    {u : N → F →L[ℝ] F →L[ℝ] ℝ} {x₀ : N}
    (h : ∀ i j, ContinuousAt (fun b => u b (v i) (v j)) x₀) :
    ContinuousAt u x₀ := by

  have h_inner_each : ∀ i, ContinuousAt (fun b => u b (v i)) x₀ := by
    intro i
    refine continuousAt_clm_of_basis_continuousAt (F := F) (G := ℝ) (N := N)
      (v := v) (u := fun b => u b (v i)) (x₀ := x₀) ?_
    intro j
    exact h i j

  exact continuousAt_clm_of_basis_continuousAt
    (F := F) (G := F →L[ℝ] ℝ) (N := N) (v := v)
    (u := u) (x₀ := x₀) h_inner_each

/-! ## Step 4: Operator-norm continuity of the chart-local inner CLM on the base set

We apply Step 2 with the canonical finite basis of `Tensor0SModel s ℝ E`. For
each basis pair, the scalar function
`b ↦ chartTensorInnerPointwise_0sCLM g s α b (eᵢ) (eⱼ)` reduces to
`chartTensorInnerPointwise_0s s g α b eᵢ eⱼ`, which is `ContMDiffOn` on the
chart-α base set by `chartTensorInnerPointwise_0s_contMDiffOn`. In particular
it is continuous on the base set, so its pointwise restriction is
`ContinuousAt b` for every `b ∈ baseSet`. -/

set_option linter.unusedSectionVars false in
/-- Operator-norm continuity at each base-set point of the chart-α inner CLM
section `b ↦ chartTensorInnerPointwise_0sCLM g s α b`. -/
lemma chartTensorInnerPointwise_0sCLM_continuousAt_of_baseSet
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α : M)
    {b₀ : M} (hb₀ : b₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    ContinuousAt
      (fun b : M => chartTensorInnerPointwise_0sCLM g s α b) b₀ := by
  classical

  set basis := Module.finBasis ℝ (Tensor0SModel s ℝ E) with hbasis_def
  refine continuousAt_bilin_of_basis_continuousAt
    (F := Tensor0SModel s ℝ E) (N := M) (v := basis)
    (u := fun b => chartTensorInnerPointwise_0sCLM g s α b)
    (x₀ := b₀) ?_
  intro i j

  have heq : (fun b : M =>
      chartTensorInnerPointwise_0sCLM g s α b (basis i) (basis j))
      = (fun b : M =>
        chartTensorInnerPointwise_0s (I := I) (M := M) s g α b (basis i) (basis j)) := by
    funext b
    rw [chartTensorInnerPointwise_0sCLM_apply]
  rw [heq]

  have hSmooth := chartTensorInnerPointwise_0s_contMDiffOn (I := I) (M := M) g α s
    (basis i) (basis j)
  have hCont : ContinuousOn
      (fun b : M =>
        chartTensorInnerPointwise_0s (I := I) (M := M) s g α b (basis i) (basis j))
      (trivializationAt E (TangentSpace I) α).baseSet := hSmooth.continuousOn
  have hOpen : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  exact hCont.continuousAt (hOpen.mem_nhds hb₀)

/-! ## Step 5: Bridge from `chartTensorInnerPointwise_0sCLM` to `inCoordinates`

Reading the bundle-fibre inner CLM `innerBundleCLM g s b` in coordinates at
the chart-α trivialisation. Using the bridge identity and the inverse-
trivialisation formula `triv_symmL_eq_compContinuousLinearMap`, the
`inCoordinates`-form of `innerBundleCLM g s b` evaluated on test vectors
`v, w : Tensor0SModel s ℝ E` equals `chartTensorInnerPointwise_0sCLM g s α b v w`
for `b` in the chart-α base set. -/

set_option linter.unusedSectionVars false in
/-- Pointwise identification of the `inCoordinates` form of `innerBundleCLM`
with `chartTensorInnerPointwise_0sCLM`, evaluated on test vectors. -/
lemma innerBundleCLM_inCoordinates_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α : M)
    {b : M} (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (v w : Tensor0SModel s ℝ E) :
    ContinuousLinearMap.inCoordinates (Tensor0SModel s ℝ E)
        (fun b' : M => Tensor0SSpace s I b')
        (Tensor0SModel s ℝ E →L[ℝ] ℝ)
        (fun b' : M => Tensor0SSpace s I b' →L[ℝ] ℝ)
        α b α b
        (innerBundleCLM (I := I) (M := M) g s b) v w =
      chartTensorInnerPointwise_0sCLM g s α b v w := by

  have hb' : b ∈ (trivializationAt (Tensor0SModel s ℝ E)
      (fun b' : M => Tensor0SSpace s I b') α).baseSet := hb

  have hb_trivR :
      b ∈ (trivializationAt ℝ (Bundle.Trivial M ℝ) α).baseSet := by

    exact mem_univ _

  have hb_dual :
      b ∈ (trivializationAt (Tensor0SModel s ℝ E →L[ℝ] ℝ)
        (fun b' : M => Tensor0SSpace s I b' →L[ℝ] ℝ) α).baseSet := by

    simp only [hom_trivializationAt_baseSet]
    exact ⟨hb, mem_univ _⟩

  rw [inCoordinates_apply_eq₂ (𝕜 := ℝ)
    (F₁ := Tensor0SModel s ℝ E) (F₂ := Tensor0SModel s ℝ E)
    (F₃ := ℝ)
    (E₁ := fun b' : M => Tensor0SSpace s I b')
    (E₂ := fun b' : M => Tensor0SSpace s I b')
    (E₃ := Bundle.Trivial M ℝ)
    (x₀ := α) (x := b)
    (ϕ := innerBundleCLM (I := I) (M := M) g s b)
    (v := v) (w := w) hb' hb' hb_trivR]

  have h_lm_id : ∀ y : ℝ,
      (trivializationAt ℝ (Bundle.Trivial M ℝ) α).linearMapAt ℝ b y = y := by
    intro y
    have hmem : b ∈ (trivializationAt ℝ (Bundle.Trivial M ℝ) α).baseSet := mem_univ _
    rw [(trivializationAt ℝ (Bundle.Trivial M ℝ) α).coe_linearMapAt_of_mem hmem]

    rfl
  rw [h_lm_id]

  have hsymm : ∀ (z : Tensor0SModel s ℝ E),
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun b' : M => Tensor0SSpace s I b') α).symm b z =
      z.compContinuousLinearMap (fun _ : Fin s => chartJ (I := I) (M := M) α b) := by
    intro z

    have hsymmL_eq :
        ((trivializationAt (Tensor0SModel s ℝ E)
            (fun b' : M => Tensor0SSpace s I b') α).symmL ℝ b z :
              Tensor0SSpace s I b) =
          (trivializationAt (Tensor0SModel s ℝ E)
            (fun b' : M => Tensor0SSpace s I b') α).symm b z := by
      rw [Bundle.Trivialization.symmL_apply]
    rw [← hsymmL_eq]

    have :=
      Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap
        (𝕜 := ℝ) (B := M) (F := E) (E := (TangentSpace I : M → Type _))
        (s := s) (x₀ := α) (x := b) hb z

    convert this using 1
  rw [hsymm v, hsymm w]

  rw [innerBundleCLM_apply]

  rw [chartTensorInnerPointwise_0sCLM_apply]

  have h_toM : ∀ (z : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ),
      Tensor0SBundle.Tensor0SSpace.toModel
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
        (show Tensor0SSpace s I b from z) = z := by
    intro z
    exact Tensor0SBundle.tensor0SSpace_continuousLinearEquiv_apply (I := I) (M := M) s b z
  rw [h_toM, h_toM]

  rw [tensorInnerPointwise_0s_bridge_identity (I := I) (M := M) g α s hb]

  have hcomp : ∀ (z : Tensor0SModel s ℝ E),
      (z.compContinuousLinearMap (fun _ : Fin s => chartJ (I := I) (M := M) α b)).compContinuousLinearMap
        (fun _ : Fin s => chartJinv (I := I) (M := M) α b) = z := by
    intro z
    ext m

    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    exact chartJ_chartJinv (I := I) (M := M) α hb (m i)
  rw [hcomp v, hcomp w]

/-! ## Step 6: Total-space-valued continuity on each chart base set

We combine Steps 4 and 5 with `FiberBundle.continuousAt_totalSpace` and
`continuousAt_hom_bundle` to lift the operator-norm continuity of
`chartTensorInnerPointwise_0sCLM` to the total-space-valued continuity of
`b ↦ TotalSpace.mk' (Tensor0SModel s ℝ E →L[ℝ] Tensor0SModel s ℝ E →L[ℝ] ℝ) b (innerBundleCLM g s b)`.
-/

set_option linter.unusedSectionVars false in
/-- The bundle inner-product section is continuous (CLM-valued) in the basepoint
on each chart base set. -/
theorem innerBundleCLM_continuousOn (g : SmoothRiemannianMetric I M) (s : ℕ) (α : M) :
    ContinuousOn (fun b : M =>
      TotalSpace.mk' (Tensor0SModel s ℝ E →L[ℝ] Tensor0SModel s ℝ E →L[ℝ] ℝ) b
        (innerBundleCLM (I := I) (M := M) g s b))
      (chartAt H α).source := by

  have hOpen : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  rw [show (chartAt H α).source =
    (trivializationAt E (TangentSpace I) α).baseSet from
    (TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α).symm]

  rw [ContinuousOn]
  intro b₀ hb₀

  apply ContinuousAt.continuousWithinAt

  rw [continuousAt_hom_bundle]
  refine ⟨continuousAt_id, ?_⟩

  let HomBundle := fun b' : M =>
    Tensor0SSpace s I b' →L[ℝ] Tensor0SSpace s I b' →L[ℝ] ℝ

  have hb₀_self : b₀ ∈ (trivializationAt E (TangentSpace I) b₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt (F := E)
      (E := (TangentSpace I : M → Type _)) b₀
  have hOpen_b₀ : IsOpen (trivializationAt E (TangentSpace I) b₀).baseSet :=
    (trivializationAt E (TangentSpace I) b₀).open_baseSet
  have hCont_clm := chartTensorInnerPointwise_0sCLM_continuousAt_of_baseSet
    (I := I) (M := M) g s b₀ hb₀_self

  refine ContinuousAt.congr hCont_clm ?_

  have h_nhds : (trivializationAt E (TangentSpace I) b₀).baseSet ∈ 𝓝 b₀ :=
    hOpen_b₀.mem_nhds hb₀_self
  filter_upwards [h_nhds] with x hx

  refine ContinuousLinearMap.ext ?_
  intro v
  refine ContinuousLinearMap.ext ?_
  intro w

  exact (innerBundleCLM_inCoordinates_apply (I := I) (M := M) g s b₀ hx v w).symm

/-! ## Step 7: Global continuity and the `IsContinuousRiemannianBundle` instance

Glueing the chart-local continuity into a global continuity statement: for any
point `b ∈ M`, the chart at `b` is an open neighborhood; on that neighborhood,
`innerBundleCLM_continuousOn` gives continuity; hence `ContinuousAt b`. -/

set_option linter.unusedSectionVars false in
/-- Global continuity (CLM-valued) of the bundle inner-product section. -/
theorem innerBundleCLM_continuous (g : SmoothRiemannianMetric I M) (s : ℕ) :
    Continuous (fun b : M =>
      TotalSpace.mk' (Tensor0SModel s ℝ E →L[ℝ] Tensor0SModel s ℝ E →L[ℝ] ℝ) b
        (innerBundleCLM (I := I) (M := M) g s b)) := by
  rw [continuous_iff_continuousAt]
  intro b
  have hb_source : b ∈ (chartAt H b).source := mem_chart_source H b
  have hOpen : IsOpen (chartAt H b).source := (chartAt H b).open_source
  exact (innerBundleCLM_continuousOn (I := I) (M := M) g s b).continuousAt
    (hOpen.mem_nhds hb_source)

/-! ### Building `ContinuousRiemannianMetric` and the typeclass instance -/

set_option linter.unusedSectionVars false in
attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace in
/-- The `ContinuousRiemannianMetric` data for the `(0, s)`-tensor bundle: extends
the `RiemannianMetric` packaging (algebraic + diagonal continuity + von-Neumann
boundedness) with global continuity of the CLM-valued inner-product section. -/
noncomputable def tensor0SContinuousRiemannianMetric
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    Bundle.ContinuousRiemannianMetric (Tensor0SModel s ℝ E)
      (fun b : M => Tensor0SSpace s I b) where
  inner := fun b => tensor0SRiemannianInnerCLM (I := I) (M := M) g s b
  symm := fun b T S =>
    tensor0SRiemannianInner_symm (I := I) (M := M) g s b T S
  pos := fun b T hT =>
    tensor0SRiemannianInner_pos (I := I) (M := M) g s b T hT
  isVonNBounded := fun b =>
    tensor0SRiemannianInner_isVonNBounded (I := I) (M := M) g s b
  continuous := by

    have h := innerBundleCLM_continuous (I := I) (M := M) g s
    convert h using 0

/-! ### Installing `IsContinuousRiemannianBundle` via the `[∀ x, InnerProductSpace ℝ (E x)]`
hypothesis

The Mathlib `IsContinuousRiemannianBundle F E` class requires a pre-existing
`[∀ x, InnerProductSpace ℝ (E x)]` instance in scope. Downstream consumers who
need this typeclass instance on the `(0, s)`-tensor bundle should first install
the `Bundle.RiemannianBundle` structure derived from
`tensor0SContinuousRiemannianMetric` (which makes the per-fibre inner-product
structure available via Mathlib's scoped instance machinery), and then build
the `IsContinuousRiemannianBundle` instance from the constructor with the
inner-product bilinear form, the global continuity
`innerBundleCLM_continuous`, and the trivial identity `⟨v, w⟩ = inner b v w`.

Given the higher-order-unification difficulties of resolving
`[∀ x, InnerProductSpace ℝ (fun b => Tensor0SSpace s I b) x]` automatically,
the typeclass instance is most reliably constructed within a `letI`/`haveI`
block at the consumer site. The following auxiliary lemma packages the
constructor inputs (continuity + identity) so consumers can apply it once
the InnerProductSpace structure is in scope. -/

set_option linter.unusedSectionVars false in
/-- The constructor inputs for `IsContinuousRiemannianBundle` on the `(0, s)`-tensor
bundle: the bilinear form, its continuity, and the inner-product identity. Pair
this with a locally-installed `[∀ x, InnerProductSpace ℝ (Tensor0SSpace s I x)]`
instance (e.g. via the `Bundle.RiemannianBundle` mechanism on
`tensor0SContinuousRiemannianMetric`) to build the typeclass instance. -/
theorem isContinuousRiemannianBundle_data
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ (γ : Π b : M,
        Tensor0SSpace s I b →L[ℝ] Tensor0SSpace s I b →L[ℝ] ℝ),
      Continuous (fun b : M =>
        TotalSpace.mk' (Tensor0SModel s ℝ E →L[ℝ] Tensor0SModel s ℝ E →L[ℝ] ℝ) b (γ b))
      ∧ ∀ (b : M) (v w : Tensor0SSpace s I b),
        tensor0SRiemannianInnerCLM (I := I) (M := M) g s b v w = γ b v w := by
  refine ⟨fun b => tensor0SRiemannianInnerCLM (I := I) (M := M) g s b, ?_, ?_⟩
  · exact innerBundleCLM_continuous (I := I) (M := M) g s
  · intros; rfl

/-! ### Typeclass instance: `IsContinuousRiemannianBundle` on the `(0, s)`-tensor bundle

Following the Mathlib pattern `Bundle.ContinuousRiemannianMetric → IsContinuousRiemannianBundle`,
we install the instance with the auxiliary `RiemannianBundle` typeclass in scope (supplied
via `letI` from `tensor0S_riemannianBundle g s`). This brings the `InnerProductSpace ℝ`
fibre instance into scope through Mathlib's scoped `Bundle.instInnerProductSpaceReal`
derivation, allowing the typeclass to be stated and discharged from the
`ContinuousRiemannianMetric` data assembled in `tensor0SContinuousRiemannianMetric`.

The `attribute [-instance]` directive disables the project's operator-norm
`NormedAddCommGroup` / `NormedSpace` instances on `Bundle.continuousMultilinearMap`
in the scope of this instance declaration, matching the pattern used by
`tensor0SContinuousRiemannianMetric` itself; this resolves any residual normed-structure
mismatch at the typeclass-resolution layer between the operator-norm route and the
inner-product-derived route. -/

/-! ### Bundle structure on `Tensor0SSpace s I`

The Mathlib `IsContinuousRiemannianBundle` typeclass requires `[FiberBundle F E]` and
`[VectorBundle ℝ F E]` as instance arguments on the family `E`. Since `Tensor0SSpace` is
declared as a non-reducible `def`, these instances do not transfer automatically from
the underlying `Bundle.continuousMultilinearMap` family — we re-export them here, locally
to this file, so that they apply at the `Tensor0SSpace` level. The total-space topology is
likewise re-exported.

These declarations sit at file scope (before the `attribute [-instance]` block that
constructs the `IsContinuousRiemannianBundle` witness), so they participate in typeclass
resolution wherever `Tensor0SSpace` appears in this file. -/

instance tensor0SSpace_totalSpace_topologicalSpace (s : ℕ) :
    TopologicalSpace (Bundle.TotalSpace (Tensor0SModel s ℝ E)
      (Tensor0SSpace s I (M := M))) :=
  inferInstanceAs (TopologicalSpace (Bundle.TotalSpace (Tensor0SModel s ℝ E)
    (Bundle.continuousMultilinearMap ℝ s E (TangentSpace I))))

instance tensor0SSpace_fiberBundle (s : ℕ) :
    FiberBundle (Tensor0SModel s ℝ E) (Tensor0SSpace s I (M := M)) :=
  inferInstanceAs (FiberBundle (Tensor0SModel s ℝ E)
    (Bundle.continuousMultilinearMap ℝ s E (TangentSpace I)))

instance tensor0SSpace_vectorBundle (s : ℕ) :
    VectorBundle ℝ (Tensor0SModel s ℝ E) (Tensor0SSpace s I (M := M)) :=
  inferInstanceAs (VectorBundle ℝ (Tensor0SModel s ℝ E)
    (Bundle.continuousMultilinearMap ℝ s E (TangentSpace I)))

set_option synthInstance.maxHeartbeats 400000 in
/-- The `IsContinuousRiemannianBundle` typeclass instance on the `(0, s)`-tensor bundle,
built from a smooth tangent-bundle Riemannian metric `g`.

The `RiemannianBundle`-derived `NormedAddCommGroup` and `InnerProductSpace` (the ones for
which the squared norm matches the metric `g`) are installed in scope via `letI`, both with
the bundle family `fun b => Tensor0SSpace s I b` written literally. Pinning the family
avoids the higher-order unification that fails when Mathlib's scoped instances are asked to
recover the family from the reducible `Tensor0SSpace` abbreviation; installing the matching
`NormedAddCommGroup` first makes it the ambient norm, so that the operator-norm routes
reachable through the abbreviation do not compete with the inner-product route. -/
instance tensor0S_isContinuousRiemannianBundle
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    letI rb : Bundle.RiemannianBundle (fun b : M => Tensor0SSpace s I b) :=
      Tensor0SBundle.tensor0S_riemannianBundle (I := I) (M := M) g s
    letI nag : ∀ b : M, NormedAddCommGroup (Tensor0SSpace s I b) :=
      fun b => Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
        (E := fun b : M => Tensor0SSpace s I b) b
    letI : ∀ b : M, @InnerProductSpace ℝ (Tensor0SSpace s I b) _ (nag b).toSeminormedAddCommGroup :=
      fun b => @Bundle.instInnerProductSpaceReal M (fun b : M => Tensor0SSpace s I b)
        _ _ _ rb (fun _ => inferInstance) (fun _ => inferInstance) b
    IsContinuousRiemannianBundle (Tensor0SModel s ℝ E)
      (Tensor0SSpace s I (M := M)) := by
  letI rb : Bundle.RiemannianBundle (fun b : M => Tensor0SSpace s I b) :=
    Tensor0SBundle.tensor0S_riemannianBundle (I := I) (M := M) g s
  letI nag : ∀ b : M, NormedAddCommGroup (Tensor0SSpace s I b) :=
    fun b => Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
      (E := fun b : M => Tensor0SSpace s I b) b
  letI : ∀ b : M, @InnerProductSpace ℝ (Tensor0SSpace s I b) _ (nag b).toSeminormedAddCommGroup :=
    fun b => @Bundle.instInnerProductSpaceReal M (fun b : M => Tensor0SSpace s I b)
      _ _ _ rb (fun _ => inferInstance) (fun _ => inferInstance) b
  exact ⟨isContinuousRiemannianBundle_data (I := I) (M := M) g s⟩

end Tensor0SInnerSectionContinuity
end Tensor
end DifferentialGeometry

/-! ## Notes on `IsContinuousRiemannianBundle` typeclass instance for the `(0, s)`-tensor bundle

The `IsContinuousRiemannianBundle` typeclass instance is installed above as
`tensor0S_isContinuousRiemannianBundle (g) (s)`, parameterised by a smooth
tangent-bundle Riemannian metric `g` and the multilinear arity `s`. It uses
the partial-application form `Tensor0SSpace s I (M := M)` for the fibre
family to ensure higher-order unification can solve `E := Tensor0SSpace s I`
during typeclass resolution, and disables the project's operator-norm
`NormedAddCommGroup`/`NormedSpace` on `Tensor0SSpace` in its local
`attribute [-instance]` scope so that the `RiemannianBundle`-derived
`NormedAddCommGroup` (with squared norm matching the metric `g`) is the
unique route. The auxiliary `RiemannianBundle` typeclass is brought into
scope via `letI` from `tensor0S_riemannianBundle g s`. -/
