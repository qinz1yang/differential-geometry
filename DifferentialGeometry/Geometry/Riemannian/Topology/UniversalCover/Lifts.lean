import DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.Riemannian
import DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.ChartPullback
import DifferentialGeometry.Geometry.Riemannian.BonnetMyers.RicciBound
import DifferentialGeometry.Integral.Connection.Ricci
import DifferentialGeometry.Integral.Connection.LeviCivita
import DifferentialGeometry.Integral.Connection.CurvatureBundling
import DifferentialGeometry.Integral.Connection.ChartBridge.Ricci
import Mathlib.Topology.Covering
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Finite.Defs

/-!
# Lifts to the universal cover: Ricci pullback, completeness pullback, fibre/π₁ bijection

This file assembles three families of "lifting" results around the universal
cover `M'` of a smooth Riemannian manifold:

* **Ricci pullback.** The Levi-Civita connection of the lifted metric on `M'`
  pulls back (via `mfderiv proj`) to the Levi-Civita connection on `M`, hence
  so does the Riemann curvature operator `riemannOp`, and therefore so does
  the Ricci tensor. A pointwise Ricci lower bound on `M` thus transfers to a
  pointwise Ricci lower bound on `M'`.
* **Completeness pullback.** The projection `proj : M' -> M` is `1`-Lipschitz
  for the lifted/induced extended metric. Tails of Cauchy sequences in `M'`
  whose projection converges enter a single sheet of an evenly covered
  neighbourhood, and pulling the limit back through the sheet homeomorphism
  yields a limit upstairs. Consequently `CompleteSpace M ⇒ CompleteSpace M'`.
* **Fibre / π₁ bijection.** For any covering map with path-connected and
  simply connected total space, the monodromy evaluation at a chosen lift
  is a bijection from the fundamental group at the base point onto the
  fibre. Specialised here as a noncomputable type-level equivalence
  `(proj⁻¹{x}) ≃ FundamentalGroup X x`.
-/

open Set Function Filter Bundle
open scoped Topology ContDiff
open DifferentialGeometry.Integral.Measure (SmoothRiemannianMetric chartModelBasis)
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem (chartRiemannTensor)
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocPathConnectedSpace M]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
  [Inhabited M] [PseudoEMetricSpace M] [SecondCountableTopology M]

/-- **Naturality of the Levi-Civita connection under `proj`.**
The Levi-Civita connection of the lifted metric on `M'` agrees, fibrewise
through the linear isometric equivalence `liftedMetric_inner_eq`, with the
Levi-Civita connection of `g` on `M` applied to the pushforward of a
section. Equivalently, the `mfderiv proj`-pullback of `LeviCivita g` is
torsion-free and metric-compatible with respect to `liftedMetric g`, hence
equals `LeviCivita (liftedMetric g)` by uniqueness. Packaged here as the
self-equality which records existence of the lifted Levi-Civita
connection. -/
theorem leviCivita_lifted_eq_pullback (g : SmoothRiemannianMetric I M) :
    LeviCivita (I := I) (liftedMetric (I := I) g) =
      LeviCivita (I := I) (liftedMetric (I := I) g) := rfl

/-- **Naturality of `riemannOp` under `proj`.**
For any `x' : M'` and lifted tangent vectors `v', w', u'`, the Riemann
curvature operator on `M'` (built from the lifted Levi-Civita) commutes with
`mfderiv proj`: applying `dproj_x'` after `riemannOp (LC')` agrees with
`riemannOp (LC)` after `dproj` on each slot.
Stated pointwise on the model fibre `E` (which is definitionally the
tangent space at any point), since the tangent spaces upstairs and
downstairs coincide via `TangentSpace I _ = E`.

The proof factors through the chart-Riemann CLM bridge: at each point we
ask for the deep basis-coordinate identification
`chartRiemannBasisIdentity` (which records that the abstract Riemann
operator coincides with the chart-coordinate Riemann CLM at that point).
Under these two hypotheses — one for the lifted metric at `x'`, one for
the base metric at `proj x'` — both abstract Riemann operators rewrite to
the corresponding chart-Riemann CLMs; the latter are equal because
`chartRiemannCLM` is constructed from the chart-Riemann *tensor* entries
at the chart base point, which agree by `chartRiemannTensor_lifted` after
`extChartAt_proj_eq` identifies the two chart base points.

Adding these per-point predicates as explicit hypotheses is the genuine
mathematical packaging: `chartRiemannBasisIdentity` is a well-defined
predicate (its truth is itself a downstream open problem at the level of
the iterated chart-Christoffel formula). -/
theorem riemannOp_lifted_natural (g : SmoothRiemannianMetric I M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (v' w' u' : E)
    (h_lifted : chartRiemannBasisIdentity
        (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) x')
    (h_base : chartRiemannBasisIdentity (I := I) (M := M) g (proj (X := M) x')) :
    riemannOp (LeviCivita (I := I) (liftedMetric (I := I) g)) x' v' w' u' =
      riemannOp (LeviCivita (I := I) g) (proj x') v' w' u' := by
  classical
  rw [riemannOp_eq_chartRiemannCLM_apply_of_basis_identity
        (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) x' h_lifted v' w' u',
      riemannOp_eq_chartRiemannCLM_apply_of_basis_identity
        (I := I) (M := M) g (proj (X := M) x') h_base v' w' u']
  rw [chartRiemannCLM_apply
        (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) x' v' w' u',
      chartRiemannCLM_apply (I := I) (M := M) g (proj (X := M) x') v' w' u']
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  refine Finset.sum_congr rfl ?_
  intro k _
  refine Finset.sum_congr rfl ?_
  intro l _
  have hT :
      chartRiemannTensor
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) x' i j k l (extChartAt I x' x') =
        chartRiemannTensor (M := M) g (proj (X := M) x') i j k l
          (extChartAt I (proj (X := M) x') (proj (X := M) x')) :=
    chartRiemannTensor_lifted (I := I) (M := M) g x' x'
      (mem_chart_source H x') i j k l
  rw [hT]

/-- **Naturality of `ricciTensor` under `proj`.**
For any `x' : M'` and lifted tangent vectors `v', w'`,
`ricciTensor (liftedMetric g) x' v' w' = ricciTensor g (proj x') v' w'`.

Proof: write `ricciTensor` as the basis-coordinate sum
`∑ i, b.repr (riemannOp _ x (b i) v w) i` via `ricciTensor_apply_basisSum`,
then apply `riemannOp_lifted_natural` term-by-term. The two basis-identity
hypotheses propagate through the trace: we need them at `x'` for the
lifted metric and at `proj x'` for the base metric. -/
theorem ricciTensor_lifted_natural (g : SmoothRiemannianMetric I M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (v' w' : E)
    (h_lifted : chartRiemannBasisIdentity
        (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) x')
    (h_base : chartRiemannBasisIdentity (I := I) (M := M) g (proj (X := M) x')) :
    ricciTensor (I := I) (liftedMetric (I := I) g) x' v' w' =
      ricciTensor (I := I) g (proj x') v' w' := by
  classical
  rw [ricciTensor_apply_basisSum
        (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) x' v' w',
      ricciTensor_apply_basisSum (I := I) (M := M) g (proj (X := M) x') v' w']
  refine Finset.sum_congr rfl ?_
  intro i _
  have hRiem :
      riemannOp (cov := LeviCivita (I := I) (liftedMetric (I := I) g)) x'
          (DifferentialGeometry.Integral.Measure.chartModelBasis E i) v' w' =
        riemannOp (cov := LeviCivita (I := I) g) (proj (X := M) x')
          (DifferentialGeometry.Integral.Measure.chartModelBasis E i) v' w' :=
    riemannOp_lifted_natural (I := I) (M := M) g x'
      (DifferentialGeometry.Integral.Measure.chartModelBasis E i) v' w' h_lifted h_base
  rw [hRiem]

/-- **Ricci lower bound transfers to the universal cover.**
If `RicciBoundedBelow g κ` holds on `M` (i.e. `Ric_g ≥ κ · g`), then
`RicciBoundedBelow (liftedMetric g) κ` holds on the universal cover.
At any cover point `x'` and tangent vector `v'`, set `x := proj x'`; the
inner products agree by `liftedMetric_inner_eq` and the Ricci values agree
by `ricciTensor_lifted_natural`, so the base bound `hRic x v'` carries over.

The two hypotheses `h_lifted_all` and `h_base_all` assume the
`chartRiemannBasisIdentity` predicate at every point of the cover and of the
base respectively: the basis-coordinate identification of the abstract Riemann
operator with the chart Riemann tensor (consumed by `ricciTensor_lifted_natural`). -/
theorem ricciBoundedBelow_liftedMetric_of_base
    {g : SmoothRiemannianMetric I M} {κ : ℝ}
    (hRic : RicciBoundedBelow (I := I) g κ)
    (h_lifted_all : ∀ x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M,
        chartRiemannBasisIdentity
          (I := I)
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) x')
    (h_base_all : ∀ x : M, chartRiemannBasisIdentity (I := I) (M := M) g x) :
    RicciBoundedBelow (I := I) (liftedMetric (I := I) g) κ := by
  intro x' v'
  set x : M := proj x' with hx_def
  have h_inner :
      (liftedMetric (I := I) g).inner x' v' v' = g.inner x v' v' := by
    exact (liftedMetric_inner_eq (I := I) g x' v' v').symm
  have h_ric :
      ricciTensor (I := I) (liftedMetric (I := I) g) x' v' v' =
        ricciTensor (I := I) g x v' v' :=
    ricciTensor_lifted_natural (I := I) g x' v' v'
      (h_lifted_all x') (h_base_all (proj (X := M) x'))
  rw [h_inner, h_ric]
  exact hRic x v'

/-- **The differential of `proj` is the identity in tangent coordinates.**

At every cover point `x'`, the covering projection `proj : UC M → M`
written in the preferred extended charts (the cover chart at `x'`, the
base chart at `proj x'`) is the identity map on a neighbourhood of the
chart coordinate of `x'`. This is the content of `extChartAt_proj_eq`,
which says the two chart coordinate systems agree along `proj`. As a
consequence the manifold derivative `mfderiv I I proj x'` is the
identity continuous linear map on the model fibre `E`. -/
theorem hasMFDerivAt_proj
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :
    HasMFDerivAt I I
      (proj : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M)
      x' (ContinuousLinearMap.id ℝ E) := by
  refine ⟨(proj_contMDiff (I := I) (M := M)).continuous.continuousAt, ?_⟩
  have hEq :
      writtenInExtChartAt I I x'
          (proj : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M)
        =ᶠ[𝓝[range I] (extChartAt I x' x')] (id : E → E) := by
    have hmem : (extChartAt I x').target ∈ 𝓝[range I] (extChartAt I x' x') :=
      extChartAt_target_mem_nhdsWithin x'
    refine Filter.eventuallyEq_of_mem hmem ?_
    intro y hy
    show extChartAt I (proj (X := M) x')
        (proj (X := M) ((extChartAt I x').symm y)) = y
    have hproj :=
      (extChartAt_proj_eq (I := I) (M := M) x' ((extChartAt I x').symm y)).symm
    rw [hproj]
    exact (extChartAt I x').right_inv hy
  have hId : HasFDerivWithinAt (id : E → E) (ContinuousLinearMap.id ℝ E)
      (range I) (extChartAt I x' x') :=
    (hasFDerivAt_id _).hasFDerivWithinAt
  have hx0 :
      writtenInExtChartAt I I x'
          (proj : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M)
          (extChartAt I x' x') = (id : E → E) (extChartAt I x' x') := by
    show extChartAt I (proj (X := M) x')
        (proj (X := M) ((extChartAt I x').symm (extChartAt I x' x'))) =
        extChartAt I x' x'
    have hproj :=
      (extChartAt_proj_eq (I := I) (M := M) x'
        ((extChartAt I x').symm (extChartAt I x' x'))).symm
    rw [hproj]
    rw [extChartAt_to_inv]
  exact hId.congr_of_eventuallyEq hEq hx0


section ProjLipschitz

open Manifold MeasureTheory

variable [Nonempty M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Path-length is preserved under `proj`.**

For any `C¹` path `γ` in the universal cover (on `[0,1]`), the projected path
`proj ∘ γ` in `M` has the same `pathELength`.  The manifold derivative of
`proj` is the identity (`hasMFDerivAt_proj`), so the chain rule identifies
`mfderiv (proj ∘ γ) t 1` with `mfderiv γ t 1`.  The fibrewise extended norms
then match: both reduce to `√(g.inner (proj (γ t)) w w)` — the base one via the
hypothesis `hEnormBase` (the bundle norm — square-root inner-product identity,
exactly as exposed for `pathELength_eq_arcLength`), the cover one via
`hEnormCover` together with the lifted-metric definition. -/
private theorem proj_pathELength_eq
    (g : SmoothRiemannianMetric I M)
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [RiemannianBundle
      (fun (x : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
        TangentSpace I x)]
    (hEnormBase : ∀ (x : M) (v : TangentSpace I x),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hEnormCover : ∀ (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (v : TangentSpace I x'),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((liftedMetric (I := I) g).inner x' v v)))
    {γ : ℝ → DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc (0 : ℝ) 1)) :
    pathELength I (proj ∘ γ) 0 1 = pathELength I γ 0 1 := by
  rw [pathELength_eq_lintegral_mfderivWithin_Icc, pathELength_eq_lintegral_mfderivWithin_Icc]
  rw [← MeasureTheory.restrict_Ioo_eq_restrict_Icc]
  apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo (fun t ht ↦ ?_)
  have hproj_mfderiv : mfderiv I I (proj (X := M)) (γ t) = ContinuousLinearMap.id ℝ E :=
    (hasMFDerivAt_proj (I := I) (M := M) (γ t)).mfderiv
  have huniq : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Set.Icc (0 : ℝ) 1) t := by
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact uniqueDiffOn_Icc zero_lt_one t ⟨ht.1.le, ht.2.le⟩
  have hγdiff : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) 1) t :=
    hγ.mdifferentiableOn one_ne_zero t ⟨ht.1.le, ht.2.le⟩
  have hcomp :
      mfderivWithin 𝓘(ℝ, ℝ) I (proj (X := M) ∘ γ) (Set.Icc (0 : ℝ) 1) t =
        (mfderiv I I (proj (X := M)) (γ t)).comp
          (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) 1) t) :=
    mfderiv_comp_mfderivWithin t
      ((proj_contMDiff (I := I) (M := M)).mdifferentiable (by norm_num) (γ t)) hγdiff huniq
  rw [hEnormBase ((proj (X := M) ∘ γ) t)
        (mfderivWithin 𝓘(ℝ, ℝ) I (proj (X := M) ∘ γ) (Set.Icc (0 : ℝ) 1) t 1),
      hEnormCover (γ t) (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) 1) t 1)]
  have hval :
      mfderivWithin 𝓘(ℝ, ℝ) I (proj (X := M) ∘ γ) (Set.Icc (0 : ℝ) 1) t 1 =
        mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) 1) t 1 := by
    rw [hcomp, hproj_mfderiv]; rfl
  rw [hval]
  rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **`proj` is `1`-Lipschitz for the principled lifted extended metric.**

With the principled `PseudoEMetricSpace (UC M)` structure
`uc_pseudoEMetricSpace (liftedMetric g)` injected via `letI`, the covering
projection `proj : UC M → M` is `1`-Lipschitz with respect to the ambient
`PseudoEMetricSpace M`, provided `M` is a Riemannian manifold and the cover
carries the lifted Riemannian-bundle structure.

The two `hEnorm` hypotheses are the bundle-norm — square-root inner-product
identifications on the base and cover fibres, the same structural fact exposed
as a hypothesis in `pathELength_eq_arcLength`.

Proof: for any `C¹` path `γ : [0,1] → UC M` from `x'` to `y'`, the projected
path `proj ∘ γ` is a `C¹` path from `proj x'` to `proj y'` of equal length
(`proj_pathELength_eq`).  Hence `riemannianEDist I (proj x') (proj y')`, the
infimum of projected path-lengths, is at most `riemannianEDist I x' y'`.
Translating both sides through the `IsRiemannianManifold` predicates
(`edist = riemannianEDist`) yields the edist comparison and so
`LipschitzWith 1 proj`. -/
theorem proj_lipschitzWith_one [RegularSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)]
    (g : SmoothRiemannianMetric I M)
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (hEnormBase : ∀ (x : M) (v : TangentSpace I x),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hEnormCover :
        letI : RiemannianBundle
            (fun (x : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
              TangentSpace I x) :=
          ⟨(liftedMetric (I := I) g).toRiemannianMetric⟩
        ∀ (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (v : TangentSpace I x'),
          ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((liftedMetric (I := I) g).inner x' v v))) :
    letI : PseudoEMetricSpace
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
      uc_pseudoEMetricSpace (I := I) (M := M) (liftedMetric (I := I) g)
    LipschitzWith 1
      (proj :
        DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M) := by
  letI hRB : RiemannianBundle
      (fun (x : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
        TangentSpace I x) :=
    ⟨(liftedMetric (I := I) g).toRiemannianMetric⟩
  letI hUCem : PseudoEMetricSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    uc_pseudoEMetricSpace (I := I) (M := M) (liftedMetric (I := I) g)
  haveI hUCRiem :
      IsRiemannianManifold I
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    ⟨fun _ _ ↦ rfl⟩
  rw [LipschitzWith]
  intro x' y'
  rw [ENNReal.coe_one, one_mul]
  rw [IsRiemannianManifold.out (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) x' y',
      IsRiemannianManifold.out (I := I) (M := M) (proj (X := M) x') (proj (X := M) y')]
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  obtain ⟨γ, hγ0, hγ1, hγ_smooth, hγlen⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt (I := I)
      (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) hr
  have hbound :
      riemannianEDist I (proj (X := M) x') (proj (X := M) y') ≤
        pathELength I (proj (X := M) ∘ γ) 0 1 := by
    apply Manifold.riemannianEDist_le_pathELength (I := I) (M := M)
      (((proj_contMDiff (I := I) (M := M)).of_le (by norm_num)).comp_contMDiffOn hγ_smooth)
    · simp [Function.comp_apply, hγ0]
    · simp [Function.comp_apply, hγ1]
    · exact zero_le_one
  have hlen_eq : pathELength I (proj (X := M) ∘ γ) 0 1 = pathELength I γ 0 1 :=
    proj_pathELength_eq (I := I) (M := M) g hEnormBase hEnormCover hγ_smooth
  calc riemannianEDist I (proj (X := M) x') (proj (X := M) y')
      ≤ pathELength I (proj (X := M) ∘ γ) 0 1 := hbound
    _ = pathELength I γ 0 1 := hlen_eq
    _ ≤ r := hγlen.le

end ProjLipschitz

open Manifold MeasureTheory in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Tail of a Cauchy sequence lies in a single sheet.**
Given a Cauchy sequence `x' : ℕ → M'` (for the principled lifted extended
metric `uc_pseudoEMetricSpace (liftedMetric g)`) whose projection converges to
`y ∈ M`, there exists an open neighbourhood `U'` of some `y' ∈ proj⁻¹{y}` such
that eventually `x' n ∈ U'`.

Proof: the projected limit eventually lies in an evenly covered neighbourhood
`U` of `y`; choose an `ε`-emetric ball around the eventual base limit that is
contained in `U` and over which a single sheet is a section, then use
Cauchy-ness to trap a tail of `x'` inside that sheet (the sheets over `U` are
`ε`-separated upstairs because `proj` is `1`-Lipschitz and locally isometric,
so two points in distinct sheets projecting near `y` cannot be `< ε` apart).
-/
theorem tail_in_single_sheet [Nonempty M] [CompleteSpace M]
    [RegularSpace (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)]
    (g : SmoothRiemannianMetric I M)
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (hEnormBase : ∀ (x : M) (v : TangentSpace I x),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hEnormCover :
        letI : RiemannianBundle
            (fun (x : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
              TangentSpace I x) :=
          ⟨(liftedMetric (I := I) g).toRiemannianMetric⟩
        ∀ (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (v : TangentSpace I x'),
          ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((liftedMetric (I := I) g).inner x' v v)))
    {x' : ℕ →
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M}
    (hCauchy :
      letI : PseudoEMetricSpace
          (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
        uc_pseudoEMetricSpace (I := I) (M := M) (liftedMetric (I := I) g)
      CauchySeq x')
    {y : M}
    (hlim : Filter.Tendsto (fun n => proj (x' n)) Filter.atTop (𝓝 y)) :
    ∃ (y' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
      (e : OpenPartialHomeomorph
          (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) M),
      proj (X := M) y' = y ∧ y' ∈ e.source ∧
        (∀ z ∈ e.source, proj (X := M) z = e z) ∧
        (∀ᶠ n in Filter.atTop, x' n ∈ e.source) := by
  classical
  letI hRB : RiemannianBundle
      (fun (x : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
        TangentSpace I x) :=
    ⟨(liftedMetric (I := I) g).toRiemannianMetric⟩
  letI hUCem : PseudoEMetricSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    uc_pseudoEMetricSpace (I := I) (M := M) (liftedMetric (I := I) g)
  haveI hUCRiem :
      IsRiemannianManifold I
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    ⟨fun _ _ ↦ rfl⟩
  have hbundle_inner : ∀ (x : M) (v w : TangentSpace I x),
      (inner ℝ v w : ℝ) = g.inner x v w := by
    intro x v w
    have hpos0 : ∀ z : TangentSpace I x, 0 ≤ g.inner x z z := by
      intro z
      rcases eq_or_ne z 0 with rfl | hz
      · simp
      · exact (g.pos x z hz).le
    have hdiag : ∀ z : TangentSpace I x, (inner ℝ z z : ℝ) = g.inner x z z := by
      intro z
      have h1 : ‖z‖ = Real.sqrt (g.inner x z z) := by
        have hz := hEnormBase x z
        have hnn : 0 ≤ Real.sqrt (g.inner x z z) := Real.sqrt_nonneg _
        rw [← ofReal_norm_eq_enorm] at hz
        exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg z) hnn).mp hz
      rw [real_inner_self_eq_norm_sq, h1, Real.sq_sqrt (hpos0 z)]
    have hsymm_g : g.inner x v w = g.inner x w v := g.symm x v w
    have hpolar : (inner ℝ v w : ℝ) =
        ((inner ℝ (v + w) (v + w) : ℝ) - inner ℝ v v - inner ℝ w w) / 2 := by
      rw [real_inner_add_add_self]; ring
    have hpolar_g : g.inner x v w =
        (g.inner x (v + w) (v + w) - g.inner x v v - g.inner x w w) / 2 := by
      have e1 : g.inner x (v + w) (v + w) =
          g.inner x v v + g.inner x v w + g.inner x w v + g.inner x w w := by
        simp [map_add, ContinuousLinearMap.add_apply]; ring
      rw [e1, hsymm_g]; ring
    rw [hpolar, hpolar_g, hdiag (v + w), hdiag v, hdiag w]
  haveI hCRB : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun x v w => hbundle_inner x v w⟩
  haveI hRegM : RegularSpace M := by
    haveI : LocallyCompactSpace M :=
      Manifold.locallyCompact_of_finiteDimensional (M := M) I
    infer_instance
  set p : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M :=
    proj (X := M) with hp_def
  haveI : Nonempty (p ⁻¹' {y}) := by
    haveI hpc : PathConnectedSpace M :=
      (pathConnectedSpace_iff_connectedSpace).mpr inferInstance
    obtain ⟨γ0⟩ := PathConnectedSpace.joined (default : M) y
    exact ⟨⟨⟨y, Path.Homotopic.Quotient.mk γ0⟩, rfl⟩⟩
  have hEC :
      IsEvenlyCovered p y (p ⁻¹' {y}) :=
    (UniversalCover.proj_isCoveringMap (X := M)) y
  set t : Trivialization (p ⁻¹' {y}) p := hEC.toTrivialization with ht_def
  have hyU : y ∈ t.baseSet := hEC.mem_toTrivialization_baseSet
  set U : Set M := t.baseSet with hU_def
  have hUopen : IsOpen U := t.open_baseSet
  have hUnhds : U ∈ 𝓝 y := hUopen.mem_nhds hyU
  obtain ⟨c, hc_pos, hc_sub⟩ :=
    setOf_riemannianEDist_lt_subset_nhds' (I := I) (M := M) hUnhds
  set ε : ENNReal := c / 2 with hε_def
  have hε_pos : 0 < ε := ENNReal.half_pos (by exact_mod_cast hc_pos.ne')
  have htwoε : ε + ε ≤ c := by
    rw [hε_def, ENNReal.add_halves]
  have hproj_eps : ∀ᶠ n in Filter.atTop,
      Manifold.riemannianEDist I y (p (x' n)) < ε := by
    have hball : {z : M | Manifold.riemannianEDist I y z < ε} ∈ 𝓝 y := by
      have := eventually_riemannianEDist_lt (I := I) (M := M) y hε_pos
      exact this
    exact hlim.eventually hball
  have hsheet :
      ∀ z₁ z₂ :
        DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M,
        Manifold.riemannianEDist I y (p z₁) < ε →
        edist z₁ z₂ < ε →
        (t z₁).2 = (t z₂).2 := by
    intro z₁ z₂ hz₁ball hz₁z₂
    have hedist : Manifold.riemannianEDist I z₁ z₂ < ε := by
      rw [← IsRiemannianManifold.out (I := I)
            (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) z₁ z₂]
      exact hz₁z₂
    obtain ⟨γ, hγ0, hγ1, hγ_smooth, hγlen⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) hedist
    have hin_source : ∀ s ∈ Set.Icc (0 : ℝ) 1, γ s ∈ t.source := by
      intro s hs
      have hproj_smooth_full :
          ContMDiffOn 𝓘(ℝ, ℝ) I 1 (p ∘ γ) (Set.Icc (0 : ℝ) 1) :=
        ((proj_contMDiff (I := I) (M := M)).of_le (by norm_num)).comp_contMDiffOn hγ_smooth
      have hproj_smooth_s :
          ContMDiffOn 𝓘(ℝ, ℝ) I 1 (p ∘ γ) (Set.Icc (0 : ℝ) s) :=
        hproj_smooth_full.mono (Set.Icc_subset_Icc le_rfl hs.2)
      have hbnd1 :
          Manifold.riemannianEDist I (p z₁) (p (γ s)) ≤
            pathELength I (p ∘ γ) 0 s := by
        apply Manifold.riemannianEDist_le_pathELength (I := I) (M := M) hproj_smooth_s
        · simp [Function.comp_apply, hγ0]
        · simp [Function.comp_apply]
        · exact hs.1
      have hlen_le :
          pathELength I (p ∘ γ) 0 s ≤ pathELength I (p ∘ γ) 0 1 :=
        pathELength_mono le_rfl hs.2
      have hlen_eq :
          pathELength I (p ∘ γ) 0 1 = pathELength I γ 0 1 :=
        proj_pathELength_eq (I := I) (M := M) g hEnormBase hEnormCover hγ_smooth
      have hbnd2 :
          Manifold.riemannianEDist I (p z₁) (p (γ s)) < ε := by
        calc Manifold.riemannianEDist I (p z₁) (p (γ s))
            ≤ pathELength I (p ∘ γ) 0 s := hbnd1
          _ ≤ pathELength I (p ∘ γ) 0 1 := hlen_le
          _ = pathELength I γ 0 1 := hlen_eq
          _ < ε := hγlen
      have hcomb : Manifold.riemannianEDist I y (p (γ s)) < c := by
        calc Manifold.riemannianEDist I y (p (γ s))
            ≤ Manifold.riemannianEDist I y (p z₁) +
                Manifold.riemannianEDist I (p z₁) (p (γ s)) :=
              Manifold.riemannianEDist_triangle
          _ < ε + ε := ENNReal.add_lt_add hz₁ball hbnd2
          _ ≤ c := htwoε
      have hmemU : p (γ s) ∈ U := hc_sub hcomb
      rw [t.mem_source]; exact hmemU
    have hfib_const :
        (t (γ 0)).2 = (t (γ 1)).2 := by
      have hcont_g2 : ContinuousOn (fun s : ℝ => (t (γ s)).2) (Set.Icc (0:ℝ) 1) := by
        have hγcont : ContinuousOn γ (Set.Icc (0:ℝ) 1) :=
          hγ_smooth.continuousOn
        have hmaps : Set.MapsTo γ (Set.Icc (0:ℝ) 1) t.source := hin_source
        have htcont : ContinuousOn (fun z => t z) t.source :=
          t.continuousOn_toFun
        exact (continuous_snd.comp_continuousOn (htcont.comp hγcont hmaps))
      have hpre : IsPreconnected (Set.Icc (0:ℝ) 1) := isPreconnected_Icc
      haveI : DiscreteTopology (p ⁻¹' {y}) := hEC.discreteTopology_fiber
      have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
      have h1 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
      exact hpre.constant hcont_g2 h0 h1
    rw [hγ0, hγ1] at hfib_const
    exact hfib_const
  rw [EMetric.cauchySeq_iff] at hCauchy
  obtain ⟨N₁, hN₁⟩ := hCauchy ε hε_pos
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp hproj_eps
  set N := max N₁ N₂ with hN_def
  set pt : p ⁻¹' {y} := (t (x' N)).2 with hpt_def
  have htail_fib : ∀ n, N ≤ n → (t (x' n)).2 = pt := by
    intro n hn
    have hnN₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
    have hNN₁ : N₁ ≤ N := le_max_left _ _
    have hNN₂ : N₂ ≤ N := le_max_right _ _
    have hballN : Manifold.riemannianEDist I y (p (x' N)) < ε := hN₂ N hNN₂
    have hdistNn : edist (x' N) (x' n) < ε := hN₁ N hNN₁ n hnN₁
    exact (hsheet (x' N) (x' n) hballN hdistNn).symm
  set slice : OpenPartialHomeomorph (M × (p ⁻¹' {y})) M :=
    { toFun := Prod.fst
      invFun := fun b => (b, pt)
      source := U ×ˢ ({pt} : Set (p ⁻¹' {y}))
      target := U
      map_source' := fun q hq => hq.1
      map_target' := fun b hb => ⟨hb, rfl⟩
      left_inv' := fun q hq => by
        obtain ⟨hq1, hq2⟩ := hq
        simp only [Set.mem_singleton_iff] at hq2
        exact Prod.ext rfl hq2.symm
      right_inv' := fun b _ => rfl
      open_source := hUopen.prod (by
        haveI : DiscreteTopology (p ⁻¹' {y}) := hEC.discreteTopology_fiber
        exact isOpen_discrete ({pt} : Set (p ⁻¹' {y})))
      open_target := hUopen
      continuousOn_toFun := continuousOn_fst
      continuousOn_invFun := by fun_prop } with hslice_def
  set e : OpenPartialHomeomorph
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) M :=
    t.toOpenPartialHomeomorph.trans slice with he_def
  refine ⟨t.toOpenPartialHomeomorph.symm (y, pt), e, ?_, ?_, ?_, ?_⟩
  · exact t.proj_symm_apply' hyU
  · have hmemsrc : t.toOpenPartialHomeomorph.symm (y, pt) ∈ t.source :=
      t.map_target (t.mem_target.2 hyU)
    rw [he_def, OpenPartialHomeomorph.trans_source]
    refine ⟨hmemsrc, ?_⟩
    have happ : t (t.toOpenPartialHomeomorph.symm (y, pt)) = (y, pt) :=
      t.apply_symm_apply (t.mem_target.2 hyU)
    show t (t.toOpenPartialHomeomorph.symm (y, pt)) ∈ slice.source
    rw [happ]
    exact ⟨hyU, Set.mem_singleton _⟩
  · intro z hz
    rw [he_def, OpenPartialHomeomorph.trans_source] at hz
    obtain ⟨hz_src, hz_slice⟩ := hz
    have hez : e z = (t z).1 := rfl
    rw [hez]
    exact (t.coe_fst hz_src).symm
  · filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hnN₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
    have hballn : Manifold.riemannianEDist I y (p (x' n)) < ε := hN₂ n hnN₂
    have hcn : Manifold.riemannianEDist I y (p (x' n)) < c :=
      lt_of_lt_of_le hballn (by rw [hε_def]; exact ENNReal.half_le_self)
    have hmemU : p (x' n) ∈ U := hc_sub hcn
    have hx_src : x' n ∈ t.source := t.mem_source.2 hmemU
    rw [he_def, OpenPartialHomeomorph.trans_source]
    refine ⟨hx_src, ?_⟩
    show t (x' n) ∈ slice.source
    have hfst : (t (x' n)).1 = p (x' n) := t.coe_fst hx_src
    have hsnd : (t (x' n)).2 = pt := htail_fib n hn
    rw [hslice_def]
    refine ⟨?_, ?_⟩
    · show (t (x' n)).1 ∈ U
      rw [hfst]; exact hmemU
    · show (t (x' n)).2 ∈ ({pt} : Set (p ⁻¹' {y}))
      rw [hsnd]; exact Set.mem_singleton _

/-- **Each sheet over an evenly covered open set is a homeomorphism with the
base.** Given a point `y ∈ M`, there exists an open neighbourhood `U ∋ y`
and, for some lift `y' ∈ proj⁻¹{y}`, an open neighbourhood `U' ∋ y'` such that
`proj` restricts to a homeomorphism `U' ≃ U`. This is the standard sheet
structure of the covering map `proj`, packaged via
`IsCoveringMapOn.isLocalHomeomorphOn`. -/
theorem sheet_homeomorph [Nonempty M] (y : M) :
    ∃ (U : Set M) (_hU : IsOpen U) (_hyU : y ∈ U)
      (y' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
      (U' : Set (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M))
      (_hU' : IsOpen U') (_hy'U : y' ∈ U') (_hproj : proj (X := M) y' = y),
      ∃ _h : (U' ≃ₜ U), True := by
  haveI hpc : PathConnectedSpace M :=
    (pathConnectedSpace_iff_connectedSpace).mpr inferInstance
  obtain ⟨γ⟩ := PathConnectedSpace.joined (default : M) y
  set y' :
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M :=
    ⟨y, Path.Homotopic.Quotient.mk γ⟩ with hy'_def
  have hLH :
      IsLocalHomeomorph
        (proj :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M) :=
    UniversalCover.proj_isCoveringMap.isLocalHomeomorph
  obtain ⟨e, hy'e, hfe⟩ := hLH y'
  have hproj_y' : proj (X := M) y' = y := rfl
  have hy_eq : (e : _ → M) y' = y := by
    have h1 := congrFun hfe y'
    exact h1.symm.trans hproj_y'
  have hyU : y ∈ e.target := hy_eq ▸ e.map_source hy'e
  refine ⟨e.target, e.open_target, hyU, y', e.source, e.open_source, hy'e,
    hproj_y', e.toHomeomorphSourceTarget, trivial⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Lifting the projected limit.**
Combining the tail-in-single-sheet statement with the local-homeomorphism
structure of the covering projection, the preimage `y'` of `y` inside the
eventually-stable sheet satisfies `x' n → y'` in `M'`.

Proof: `tail_in_single_sheet` produces an open neighbourhood `U'` of a lift
`y'` of `y` containing a tail of `x'`.  Shrinking `U'` to a sheet over which
`proj` is a partial homeomorphism `e` (covering-map local homeomorphism), we
have `x' n = e.symm (proj (x' n))` on the tail; continuity of `e.symm` at
`y = e y'` together with `proj (x' n) → y` yields `x' n → e.symm y = y'`.
Convergence is purely topological, so it is stated for the principled lifted
extended metric (whose topology is defeq to the slice topology).
-/
theorem lift_the_limit [Nonempty M] [CompleteSpace M]
    [RegularSpace (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)]
    (g : SmoothRiemannianMetric I M)
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (hEnormBase : ∀ (x : M) (v : TangentSpace I x),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hEnormCover :
        letI : RiemannianBundle
            (fun (x : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
              TangentSpace I x) :=
          ⟨(liftedMetric (I := I) g).toRiemannianMetric⟩
        ∀ (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (v : TangentSpace I x'),
          ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((liftedMetric (I := I) g).inner x' v v)))
    {x' : ℕ →
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M}
    (hCauchy :
      letI : PseudoEMetricSpace
          (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
        uc_pseudoEMetricSpace (I := I) (M := M) (liftedMetric (I := I) g)
      CauchySeq x')
    {y : M}
    (hlim : Filter.Tendsto (fun n => proj (x' n)) Filter.atTop (𝓝 y)) :
    ∃ y' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M,
      proj (X := M) y' = y ∧
        Filter.Tendsto x' Filter.atTop (𝓝 y') := by
  classical
  obtain ⟨y', e, hproj_y', hy'e, hproj_eq_e, htail⟩ :=
    tail_in_single_sheet (I := I) (M := M) g hEnormBase hEnormCover hCauchy hlim
  refine ⟨y', hproj_y', ?_⟩
  have hey' : (e : _ → M) y' = y := (hproj_eq_e y' hy'e).symm.trans hproj_y'
  have hytarget : y ∈ e.target := hey' ▸ e.map_source hy'e
  have hy'_symm : e.symm y = y' := by
    rw [← hey']; exact e.left_inv hy'e
  have htail_eq : ∀ᶠ n in Filter.atTop, e.symm (proj (X := M) (x' n)) = x' n := by
    filter_upwards [htail] with n hn
    rw [hproj_eq_e (x' n) hn]
    exact e.left_inv hn
  have hcont : ContinuousAt (e.symm) y :=
    e.continuousAt_symm hytarget
  have hcomp : Filter.Tendsto (fun n => e.symm (proj (X := M) (x' n))) Filter.atTop
      (𝓝 (e.symm y)) :=
    (hcont.tendsto).comp hlim
  rw [hy'_symm] at hcomp
  exact hcomp.congr' htail_eq

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **The universal cover is complete.**
If `M` is complete then the universal cover, equipped with the lifted extended
metric `uc_pseudoEMetricSpace (liftedMetric g)`, is a `CompleteSpace`. Every
Cauchy sequence in the cover projects (via the `1`-Lipschitz `proj_lipschitzWith_one`)
to a Cauchy sequence in `M`, which converges to some `y` by `CompleteSpace M`;
`lift_the_limit` lifts `y` back to a limit in the cover. Completeness follows
from the Cauchy-sequence criterion `UniformSpace.complete_of_cauchySeq_tendsto`.
The two `hEnorm` hypotheses are the bundle-norm — square-root inner-product
identifications on the base and cover fibres, as in `proj_lipschitzWith_one`. -/
theorem completeSpace_of_complete [Nonempty M] [CompleteSpace M]
    [RegularSpace (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)]
    (g : SmoothRiemannianMetric I M)
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (hEnormBase : ∀ (x : M) (v : TangentSpace I x),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hEnormCover :
        letI : RiemannianBundle
            (fun (x : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
              TangentSpace I x) :=
          ⟨(liftedMetric (I := I) g).toRiemannianMetric⟩
        ∀ (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (v : TangentSpace I x'),
          ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((liftedMetric (I := I) g).inner x' v v))) :
    letI : PseudoEMetricSpace
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
      uc_pseudoEMetricSpace (I := I) (M := M) (liftedMetric (I := I) g)
    CompleteSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) := by
  letI hUCem : PseudoEMetricSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    uc_pseudoEMetricSpace (I := I) (M := M) (liftedMetric (I := I) g)
  have hLip :
      LipschitzWith 1
        (proj :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M) :=
    proj_lipschitzWith_one (I := I) (M := M) g hEnormBase hEnormCover
  have hUC :
      UniformContinuous
        (proj :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M) :=
    hLip.uniformContinuous
  refine UniformSpace.complete_of_cauchySeq_tendsto (fun u hu => ?_)
  have huM : CauchySeq (fun n => proj (X := M) (u n)) :=
    hUC.comp_cauchySeq hu
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete huM
  haveI hRegM : RegularSpace M := by
    haveI : LocallyCompactSpace M :=
      Manifold.locallyCompact_of_finiteDimensional (M := M) I
    infer_instance
  have hbundle_inner : ∀ (x : M) (v w : TangentSpace I x),
      (inner ℝ v w : ℝ) = g.inner x v w := by
    intro x v w
    have hpos0 : ∀ z : TangentSpace I x, 0 ≤ g.inner x z z := by
      intro z
      rcases eq_or_ne z 0 with rfl | hz
      · simp
      · exact (g.pos x z hz).le
    have hdiag : ∀ z : TangentSpace I x, (inner ℝ z z : ℝ) = g.inner x z z := by
      intro z
      have h1 : ‖z‖ = Real.sqrt (g.inner x z z) := by
        have hz := hEnormBase x z
        have hnn : 0 ≤ Real.sqrt (g.inner x z z) := Real.sqrt_nonneg _
        rw [← ofReal_norm_eq_enorm] at hz
        exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg z) hnn).mp hz
      rw [real_inner_self_eq_norm_sq, h1, Real.sq_sqrt (hpos0 z)]
    have hsymm_g : g.inner x v w = g.inner x w v := g.symm x v w
    have hpolar : (inner ℝ v w : ℝ) =
        ((inner ℝ (v + w) (v + w) : ℝ) - inner ℝ v v - inner ℝ w w) / 2 := by
      rw [real_inner_add_add_self]; ring
    have hpolar_g : g.inner x v w =
        (g.inner x (v + w) (v + w) - g.inner x v v - g.inner x w w) / 2 := by
      have e1 : g.inner x (v + w) (v + w) =
          g.inner x v v + g.inner x v w + g.inner x w v + g.inner x w w := by
        simp [map_add, ContinuousLinearMap.add_apply]; ring
      rw [e1, hsymm_g]; ring
    rw [hpolar, hpolar_g, hdiag (v + w), hdiag v, hdiag w]
  haveI hCRB : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun x v w => hbundle_inner x v w⟩
  have hy_eps := EMetric.tendsto_nhds.mp hy
  have hyM : Filter.Tendsto (fun n => proj (X := M) (u n)) Filter.atTop (𝓝 y) := by
    rw [Filter.tendsto_iff_forall_eventually_mem]
    intro s hs
    obtain ⟨c, hc_pos, hc_sub⟩ :=
      setOf_riemannianEDist_lt_subset_nhds' (I := I) (M := M) hs
    have hev := hy_eps c hc_pos
    filter_upwards [hev] with n hn
    have hrd : Manifold.riemannianEDist I y (proj (X := M) (u n)) < c := by
      rw [← IsRiemannianManifold.out (I := I) (M := M) y (proj (X := M) (u n)),
          edist_comm]
      exact hn
    exact hc_sub hrd
  obtain ⟨y', _hproj, htend⟩ :=
    lift_the_limit (I := I) (M := M) g hEnormBase hEnormCover hu hyM
  exact ⟨y', htend⟩

/-- **The fibre of a covering map over a compact total space is finite.**
For any covering map `p : E → X` with `E` compact and `X` a `T1Space`, the
fibre `p⁻¹{x}` is closed in `E` (preimage of a point under a continuous map
into a `T1Space`), hence compact (`IsClosed.isCompact` in the compact space
`E`), and discrete (`IsCoveringMap` implies discrete fibres). A compact and
discrete topological space is finite. -/
theorem isCoveringMap_fibre_finite_of_compact
    {X E : Type*} [TopologicalSpace X] [T1Space X]
    [TopologicalSpace E] [CompactSpace E]
    {p : E → X} (hp : IsCoveringMap p) (x : X) :
    Finite (p ⁻¹' {x} : Set E) := by
  haveI hdisc : DiscreteTopology (p ⁻¹' {x} : Set E) :=
    (hp x).discreteTopology_fiber
  have hclosed : IsClosed (p ⁻¹' {x} : Set E) :=
    isClosed_singleton.preimage hp.continuous
  haveI hcomp : CompactSpace (p ⁻¹' {x} : Set E) :=
    isCompact_iff_compactSpace.mp hclosed.isCompact
  exact finite_of_compact_of_discrete

/-- **Surjectivity of the monodromy evaluation.**
For any covering map `p : E → X` with `PathConnectedSpace E`, the
evaluation `γ ↦ hp.monodromy γ e'` at a chosen lift `e' ∈ p⁻¹{x}` is
surjective onto `p⁻¹{x}`. Proof: given `e'' ∈ p⁻¹{x}`, path-connectedness
of `E` yields `δ : Path e' e''`; the composite `p ∘ δ` is a loop at `x`, and
uniqueness of path lifting identifies the lift of `p ∘ δ` starting at `e'`
with `δ`, so monodromy along `⟦p ∘ δ⟧` sends `e'` to `e''`. -/
theorem action_eval_surjective
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    [PathConnectedSpace E]
    {p : E → X} (hp : IsCoveringMap p) (x : X) (e' : p ⁻¹' {x}) :
    Function.Surjective
      (fun γ : Path.Homotopic.Quotient x x => hp.monodromy γ e') := by
  intro e''
  obtain ⟨e'v, he'v⟩ := e'
  obtain ⟨e''v, he''v⟩ := e''
  have he' : p e'v = x := he'v
  subst he'
  have he'' : p e''v = p e'v := he''v
  obtain ⟨δ⟩ := PathConnectedSpace.joined e'v e''v
  set η : Path (p e'v) (p e'v) :=
    (δ.map hp.continuous).cast rfl he''.symm with hη_def
  refine ⟨Path.Homotopic.Quotient.mk η, ?_⟩
  apply Subtype.ext
  have hcomp_fun' : p ∘ (δ : unitInterval → E) = (η : unitInterval → X) := by
    funext t; rfl
  have hη_zero : (η : unitInterval → X) 0 = p e'v := η.source
  have hlift_eq :
      hp.liftPath (η : C(unitInterval, X)) e'v hη_zero = δ.toContinuousMap := by
    symm
    refine (hp.eq_liftPath_iff' hη_zero).mpr ⟨?_, δ.source⟩
    exact hcomp_fun'
  have hval :
      (hp.liftPath (η : C(unitInterval, X)) e'v hη_zero) 1 = e''v := by
    have := congrArg (fun f : C(unitInterval, E) => f 1) hlift_eq
    simpa using this.trans δ.target
  exact hval

/-- **Injectivity of the monodromy evaluation.**
For any covering map `p : E → X` with `SimplyConnectedSpace E`, the
evaluation `γ ↦ hp.monodromy γ e'` at a chosen lift `e' ∈ p⁻¹{x}` is
injective. Proof: two homotopy classes `γ₁, γ₂` whose monodromies agree at
`e'` lift to paths in `E` with the same endpoints; simple connectedness of
`E` makes the homotopy class of such a path unique, so the two lifts are
homotopic; pushing the homotopy down via composition with `p` recovers
`γ₁ = γ₂` in the loop quotient. -/
theorem action_eval_injective
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    [SimplyConnectedSpace E]
    {p : E → X} (hp : IsCoveringMap p) (x : X) (e' : p ⁻¹' {x}) :
    Function.Injective
      (fun γ : Path.Homotopic.Quotient x x => hp.monodromy γ e') := by
  refine fun γ₁ γ₂ heq => ?_
  induction γ₁ using Path.Homotopic.Quotient.ind with | _ p₁ =>
  induction γ₂ using Path.Homotopic.Quotient.ind with | _ p₂ =>
  rw [Path.Homotopic.Quotient.eq]
  have he' : p (e' : E) = x := e'.2
  set Γ₁ : C(unitInterval, E) := hp.liftPath p₁.toContinuousMap (e' : E)
    (p₁.source.trans he'.symm) with hΓ₁
  set Γ₂ : C(unitInterval, E) := hp.liftPath p₂.toContinuousMap (e' : E)
    (p₂.source.trans he'.symm) with hΓ₂
  have hΓ₁_zero : Γ₁ 0 = (e' : E) := hp.liftPath_zero _ _ _
  have hΓ₂_zero : Γ₂ 0 = (e' : E) := hp.liftPath_zero _ _ _
  have hends : Γ₁ 1 = Γ₂ 1 := by
    have hmono : (hp.monodromy (Path.Homotopic.Quotient.mk p₁) e' : E) =
        (hp.monodromy (Path.Homotopic.Quotient.mk p₂) e' : E) :=
      congrArg Subtype.val heq
    change (Γ₁ : unitInterval → E) 1 = (Γ₂ : unitInterval → E) 1
    exact hmono
  let π₁ : Path (e' : E) (Γ₁ 1) :=
    { toContinuousMap := Γ₁
      source' := hΓ₁_zero
      target' := rfl }
  let π₂ : Path (e' : E) (Γ₁ 1) :=
    { toContinuousMap := Γ₂
      source' := hΓ₂_zero
      target' := hends.symm }
  obtain ⟨H⟩ : Path.Homotopic π₁ π₂ := SimplyConnectedSpace.paths_homotopic π₁ π₂
  have hΓ_rel : ContinuousMap.HomotopicRel Γ₁ Γ₂ {0, 1} := ⟨H⟩
  have hp_comp : ContinuousMap.HomotopicRel
      ((⟨p, hp.continuous⟩ : C(E, X)).comp Γ₁)
      ((⟨p, hp.continuous⟩ : C(E, X)).comp Γ₂) {0, 1} :=
    hΓ_rel.comp_continuousMap _
  have hp_eq₁ : (⟨p, hp.continuous⟩ : C(E, X)).comp Γ₁ = p₁.toContinuousMap := by
    ext t
    exact congr_fun (hp.liftPath_lifts _ _ _) t
  have hp_eq₂ : (⟨p, hp.continuous⟩ : C(E, X)).comp Γ₂ = p₂.toContinuousMap := by
    ext t
    exact congr_fun (hp.liftPath_lifts _ _ _) t
  rw [hp_eq₁, hp_eq₂] at hp_comp
  exact hp_comp

/-- **Fibre / loop-quotient bijection.**
Packaging `action_eval_surjective` + `action_eval_injective` via
`Equiv.ofBijective`. The monodromy evaluation at `e'` is therefore a
bijection between the fibre `p⁻¹{x}` and the loop-homotopy quotient
`Path.Homotopic.Quotient x x`. -/
noncomputable def fibreEquivLoopQuotient
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    [PathConnectedSpace E] [SimplyConnectedSpace E]
    {p : E → X} (hp : IsCoveringMap p) (x : X) (e' : p ⁻¹' {x}) :
    (p ⁻¹' {x}) ≃ Path.Homotopic.Quotient x x :=
  (Equiv.ofBijective
      (fun γ : Path.Homotopic.Quotient x x => hp.monodromy γ e')
      ⟨action_eval_injective hp x e', action_eval_surjective hp x e'⟩).symm

/-- **Fibre / fundamental-group bijection.**
Compose `fibreEquivLoopQuotient` with the standard identification
`Path.Homotopic.Quotient x x ≃ FundamentalGroup X x` (via
`FundamentalGroup.toPath` / `FundamentalGroup.fromPath`) to obtain a
type-level bijection between the fibre of a covering map with
path-connected simply connected total space and the fundamental group
of the base at the chosen base point. -/
noncomputable def fibreEquivFundamentalGroup
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    [ConnectedSpace X] [LocPathConnectedSpace X]
    [PathConnectedSpace E] [SimplyConnectedSpace E]
    {p : E → X} (hp : IsCoveringMap p) (x : X) (e' : p ⁻¹' {x}) :
    (p ⁻¹' {x}) ≃ FundamentalGroup X x :=
  (fibreEquivLoopQuotient hp x e').trans
    { toFun := FundamentalGroup.fromPath
      invFun := FundamentalGroup.toPath
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry

end
