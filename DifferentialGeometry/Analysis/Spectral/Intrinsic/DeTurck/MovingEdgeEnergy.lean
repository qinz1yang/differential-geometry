import DifferentialGeometry.Analysis.Integration.Measure.FamilyContinuity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.EdgeDifferenceEnergy
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.EdgeStrongData
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.MetricDiffSmallC0
import DifferentialGeometry.Geometry.Connection.ChartBridge.MetricInverse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.IteratedRmTowerProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckChartRegularityFromJoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckRicciRHSSymmetric
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetricContinuity
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetricDeriv
import DifferentialGeometry.Tensor.RSTensor.QuadraticBounds.TimeSlab

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-!
# Moving-carrier energy at the initial Ricci--DeTurck edge

The coercive principal estimate in `EdgeDifferenceEnergy` uses one solution as
the carrier metric.  Consequently the natural difference energy also uses that
moving carrier.  This file supplies the two analytic bookkeeping facts needed
at the closed initial edge:

* joint `C^0` chart-Gram control of the carrier and joint bundle continuity of a
  covariant tensor family imply joint continuity of its moving fibre norm;
* hence the moving `L^2` energy of the difference of two metric families is
  continuous on a compact closed time set.

The second statement uses only the exact closed-edge regularity in forward
uniqueness.  In particular it assumes no time derivative, curvature bound, or
maximal-regularity representation at the endpoint.
-/

noncomputable section

open Bundle Filter Manifold MeasureTheory Set Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

/-! ## A closed-slab operator bound for the canonical carrier speed -/

/-- The continuous bilinear form represented by a covariant two-tensor.  This
is the component API needed by `gFibreOpBound`; no tensor representation is
unfolded. -/
def tensor02Bilin {x : M} (A : Tensor0SSpace 2 I x) :
    TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real :=
  (bilinFormToModel (TangentSpace I x)).symm (Tensor0SSpace.toModel A)

@[simp] theorem tensor02Bilin_apply {x : M} (A : Tensor0SSpace 2 I x)
    (v w : TangentSpace I x) :
    tensor02Bilin (I := I) (M := M) A v w =
      eval02 (I := I) (M := M) A v w := by
  rw [tensor02Bilin, bilinFormToModel_symm_apply]
  unfold eval02
  congr 1
  funext i
  fin_cases i <;> simp

/-- Half of minus the Ricci--DeTurck right-hand side.  If `g` solves the
Ricci--DeTurck equation, then its metric velocity is `-2 * carrierQ`. -/
def carrierQ (g_bg : SmoothRiemannianMetric I M)
    (g : Real → SmoothRiemannianMetric I M) (t : Real) (x : M) :
    Tensor0SSpace 2 I x :=
  (-1 / 2 : Real) • deTurckRHSField (I := I) g_bg (g t) x

/-- Bilinear realization of `carrierQ`. -/
def carrierQBilin (g_bg : SmoothRiemannianMetric I M)
    (g : Real → SmoothRiemannianMetric I M) (t : Real) (x : M) :
    TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real :=
  tensor02Bilin (I := I) (M := M) (carrierQ (I := I) (M := M) g_bg g t x)

@[simp] theorem carrierQBilin_apply
    (g_bg : SmoothRiemannianMetric I M)
    (g : Real → SmoothRiemannianMetric I M) (t : Real) (x : M)
    (v w : TangentSpace I x) :
    carrierQBilin (I := I) (M := M) g_bg g t x v w =
      (-1 / 2 : Real) * deTurckRicciRHS (I := I) g_bg (g t) x v w := by
  rw [carrierQBilin, tensor02Bilin_apply]
  unfold carrierQ eval02
  rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul,
    deTurckRHSField_toModel_apply]

/-- The carrier half-speed is symmetric. -/
theorem carrierQBilin_symm
    (g_bg : SmoothRiemannianMetric I M)
    (g : Real → SmoothRiemannianMetric I M) (t : Real) (x : M)
    (v w : TangentSpace I x) :
    carrierQBilin (I := I) (M := M) g_bg g t x v w =
      carrierQBilin (I := I) (M := M) g_bg g t x w v := by
  rw [carrierQBilin_apply, carrierQBilin_apply,
    deTurckRicciRHS_symm (I := I) g_bg (g t) x v w]

/-- Joint closed-slab tensor continuity of the Ricci--DeTurck right-hand side
along a `JointChartGramSmooth` metric family.  The proof reads the intrinsic
field in the canonical chart frame and uses the already proved joint chart
formula on the Levi-Civita good set. -/
theorem deTurckRHS_cont
    (g_bg : SmoothRiemannianMetric I M) {T : Real}
    (g : Real → SmoothRiemannianMetric I M)
    (hJ : JointChartGramSmooth (I := I) T g) :
    Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 (Set.Icc 0 T)
      (fun t x => deTurckRHSField (I := I) g_bg (g t) x) := by
  classical
  apply tensor0SFamilyContinuousOnSet_of_chartBasisComp
    (N := fun α => chartLeviCivitaGoodSet (I := I) α)
    (hN := fun α => (chartLeviCivitaGoodSet_isOpen (I := I) α).mem_nhds
      (self_mem_chartLeviCivitaGoodSet (I := I) α))
  intro α idx
  have hincl : Continuous
      (fun q : {t : Real // t ∈ Set.Icc 0 T} × M => ((q.1 : Real), q.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hchart : ContinuousOn
      (fun q : {t : Real // t ∈ Set.Icc 0 T} × M =>
        DeTurckCoefficients.chartDeTurckRicciRHS
          (I := I) (g q.1.1) g_bg α (idx 0) (idx 1) (extChartAt I α q.2))
      {q : {t : Real // t ∈ Set.Icc 0 T} × M |
        q.2 ∈ chartLeviCivitaGoodSet (I := I) α} := by
    exact
      (jointChartDeTurckRicciRHS_alongChart_contMDiffOn
        (I := I) g_bg T g hJ α (idx 0) (idx 1)).continuousOn.comp
        hincl.continuousOn (fun q hq => ⟨q.1.2, hq⟩)
  refine hchart.congr ?_
  intro q hq
  symm
  change Tensor0SSpace.toModel
      (deTurckRHSField (I := I) g_bg (g q.1.1) q.2)
      (fun k : Fin 2 => chartBasisVecFiber (I := I) α (idx k) q.2) = _
  rw [deTurckRHSField_toModel_apply]
  exact deTurckRicciRHS_chartBasisVecFiber_eq_chartDeTurckRicciRHS
    (I := I) (g q.1.1) g_bg α (idx 0) (idx 1) hq

/-- The canonical carrier half-speed is bounded in one fibre-operator norm on
the whole closed time slab.  The constant is extracted from compactness of the
moving unit tangent slab, so it is uniform down to `t = 0`. -/
theorem carrierEdge_bounds
    (g_bg : SmoothRiemannianMetric I M) {T : Real}
    (g : Real → SmoothRiemannianMetric I M)
    (hJ : JointChartGramSmooth (I := I) T g) :
    ∃ B : Real, 0 ≤ B ∧ ∀ t ∈ Set.Icc 0 T,
      gFibreOpBound (I := I) (M := M) (g t)
        (carrierQBilin (I := I) (M := M) g_bg g t) B := by
  classical
  have hgram : ∀ (α : M) (i j : Fin (Module.finrank Real E)),
      ContinuousOn
        (fun q : {t : Real // t ∈ Set.Icc 0 T} × M =>
          chartGramMatrix (I := I) (g q.1.1) α q.2 i j)
        {q : {t : Real // t ∈ Set.Icc 0 T} × M |
          q.2 ∈ (trivializationAt E (TangentSpace I) α).baseSet} := by
    intro α i j
    have hincl : Continuous
        (fun q : {t : Real // t ∈ Set.Icc 0 T} × M => ((q.1 : Real), q.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    exact (hJ α i j).continuousOn.comp hincl.continuousOn
      (fun q hq => ⟨q.1.2, hq⟩)
  have hmetric : Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2
      (Set.Icc 0 T)
      (fun t x => metricTensorField (I := I) (g t) x) :=
    metricTensorCont_of_chartGram (I := I) (M := M) g hgram
  have hquad : Continuous
      (metricTimeBundleQuad (I := I) (M := M) g (Set.Icc 0 T)) := by
    have hq := tensor0SFamily_quadCont (I := I) (M := M) hmetric
    simpa [metricTimeBundleQuad, quad02, metricTensorField_apply] using hq
  have hcompact := metricUnitTimeSlab_icc_compact_of_bundle
    (I := I) (M := M) g 0 T (g 0) hquad
  have hRHS := deTurckRHS_cont (I := I) (M := M) g_bg g hJ
  have hQ : Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2
      (Set.Icc 0 T) (carrierQ (I := I) (M := M) g_bg g) := by
    simpa only [carrierQ] using
      (Tensor0SFamilyContinuousOnSet.const_smul
        (I := I) (M := M) (-1 / 2 : Real) hRHS)
  have htotal := Tensor0SFamilyContinuousOnSet.tangentBundle
    (I := I) (M := M) hQ
  have habs := timeSlabAbsQuadCont (I := I) (M := M)
    (G := g) (A := carrierQ (I := I) (M := M) g_bg g)
    (Set.Icc 0 T) htotal
  obtain ⟨B, hB, hdiag⟩ := compactUnitTimeSlab_absBound
    (I := I) (M := M) g (carrierQ (I := I) (M := M) g_bg g)
    (Set.Icc 0 T) hcompact habs
  refine ⟨B, hB, ?_⟩
  intro t ht
  apply gOpBound_unitQuad (g t)
    (carrierQBilin (I := I) (M := M) g_bg g t)
    (carrierQBilin_symm (I := I) (M := M) g_bg g t) hB
  intro x u hu
  rw [carrierQBilin, tensor02Bilin_apply, eval02_self]
  simpa only [hu, mul_one] using hdiag t ht x u

/-! ## Joint continuity of a moving covariant-tensor norm -/

/-- A jointly continuous covariant tensor family has a jointly continuous
squared fibre norm when the carrier metric has jointly continuous chart-Gram
entries.  The time domain is already restricted to `K`; this is the exact form
used by `integral_family_cont` after passing to the subtype.

The proof is local in space.  In the tangent trivialization centred at the
current point, `normSq0S` is the finite inverse-Gram contraction of the tensor
components.  Bundle continuity supplies the components and Cramer's formula
supplies continuity of the inverse Gram matrix. -/
theorem normSq_family_cont
    {s : Nat} {K : Set Real}
    (g : Real → SmoothRiemannianMetric I M)
    (A : (t : Real) → (x : M) → Tensor0SSpace s I x)
    (hg : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContinuousOn
        (fun q : {t : Real // t ∈ K} × M ↦
          chartGramMatrix (I := I) (g q.1.1) x₀ q.2 i j)
        {q : {t : Real // t ∈ K} × M |
          q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet})
    (hA : Tensor0SFamilyContinuousOnSet (I := I) (M := M) s K A) :
    Continuous
      (fun q : {t : Real // t ∈ K} × M ↦
        normSq0S (I := I) (g q.1.1) q.2 s (A q.1.1 q.2)) := by
  classical
  unfold Tensor0SFamilyContinuousOnSet at hA
  rw [continuous_iff_continuousAt] at hA ⊢
  intro q₀
  let e := trivializationAt E (TangentSpace I : M → Type _) q₀.2
  let b : Module.Basis (Fin (Module.finrank Real E)) Real E := chartModelBasis E
  have hx₀ : q₀.2 ∈ e.baseSet := by
    simpa only [e] using
      mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) q₀.2
  let Gm : ({t : Real // t ∈ K} × M) →
      Matrix (Fin (Module.finrank Real E)) (Fin (Module.finrank Real E)) Real :=
    fun q ↦ chartGramMatrix (I := I) (g q.1.1) q₀.2 q.2
  have hopen : {q : {t : Real // t ∈ K} × M | q.2 ∈ e.baseSet} ∈ nhds q₀ := by
    exact (e.open_baseSet.preimage continuous_snd).mem_nhds hx₀
  have hGmEnt : ∀ i j : Fin (Module.finrank Real E),
      ContinuousAt (fun q ↦ Gm q i j) q₀ := by
    intro i j
    simpa only [Gm, e] using (hg q₀.2 i j).continuousAt hopen
  have hGmc : ContinuousAt Gm q₀ :=
    continuousAt_pi.2 fun i ↦ continuousAt_pi.2 fun j ↦ hGmEnt i j
  have hdetne : (Gm q₀).det ≠ 0 := by
    exact ne_of_gt
      (chartGramMatrix_det_pos (I := I) (g q₀.1.1) q₀.2 hx₀)
  have hGinvc : ContinuousAt (fun q ↦ (Gm q)⁻¹) q₀ := by
    have hdetc : ContinuousAt (fun q ↦ (Gm q).det) q₀ :=
      (continuous_id.matrix_det).continuousAt.comp hGmc
    have hadjc : ContinuousAt (fun q ↦ (Gm q).adjugate) q₀ :=
      (continuous_id.matrix_adjugate).continuousAt.comp hGmc
    have hcramer : ContinuousAt
        (fun q ↦ ((Gm q).det)⁻¹ • (Gm q).adjugate) q₀ :=
      (hdetc.inv₀ hdetne).smul hadjc
    have heq : (fun q ↦ (Gm q)⁻¹) =
        fun q ↦ ((Gm q).det)⁻¹ • (Gm q).adjugate := by
      funext q
      rw [Matrix.inv_def, Ring.inverse_eq_inv]
    rw [heq]
    exact hcramer
  have hGinvEnt : ∀ i j : Fin (Module.finrank Real E),
      ContinuousAt (fun q ↦ (Gm q)⁻¹ i j) q₀ := fun i j ↦
    continuousAt_pi.1 (continuousAt_pi.1 hGinvc i) j
  have hcoord := hA q₀
  rw [FiberBundle.continuousAt_totalSpace] at hcoord
  have hmodel : ContinuousAt
      (fun q : {t : Real // t ∈ K} × M ↦
        (trivializationAt (Tensor0SModel s Real E)
          (fun x : M ↦ Tensor0SSpace s I x) q₀.2
            ⟨q.2, A q.1.1 q.2⟩).2) q₀ := by
    exact hcoord.2
  have hslots : ∀ idx : Fin s → Fin (Module.finrank Real E),
      ContinuousAt
        (fun q : {t : Real // t ∈ K} × M ↦
          A q.1.1 q.2
            (fun k : Fin s ↦ e.symmL Real q.2 (b (idx k)))) q₀ := by
    intro idx
    have heval : ContinuousAt
        (fun q : {t : Real // t ∈ K} × M ↦
          eval0SCLE (E := E) s
            ((trivializationAt (Tensor0SModel s Real E)
              (fun x : M ↦ Tensor0SSpace s I x) q₀.2
                ⟨q.2, A q.1.1 q.2⟩).2) idx) q₀ := by
      have hall := (eval0SCLE (E := E) s).continuous.continuousAt.comp hmodel
      exact continuousAt_pi.1 hall idx
    have heq :
        (fun q : {t : Real // t ∈ K} × M ↦
          eval0SCLE (E := E) s
            ((trivializationAt (Tensor0SModel s Real E)
              (fun x : M ↦ Tensor0SSpace s I x) q₀.2
                ⟨q.2, A q.1.1 q.2⟩).2) idx) =
          fun q ↦ A q.1.1 q.2
            (fun k : Fin s ↦ e.symmL Real q.2 (b (idx k))) := by
      funext q
      rw [eval0SCLE_apply]
      change
        ((A q.1.1 q.2).compContinuousLinearMap
          (fun _ : Fin s ↦ e.symmL Real q.2))
            (fun k : Fin s ↦ b (idx k)) = _
      rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    rw [heq] at heval
    exact heval
  have hF : ContinuousAt
      (fun q : {t : Real // t ∈ K} × M ↦
        ∑ I₀ : Fin s → Fin (Module.finrank Real E),
          ∑ J₀ : Fin s → Fin (Module.finrank Real E),
            (∏ a : Fin s, (Gm q)⁻¹ (I₀ a) (J₀ a)) *
              (A q.1.1 q.2 (fun a : Fin s ↦ e.symmL Real q.2 (b (I₀ a)))) *
              (A q.1.1 q.2 (fun a : Fin s ↦ e.symmL Real q.2 (b (J₀ a))))) q₀ := by
    refine tendsto_finset_sum _ fun I₀ _ ↦ tendsto_finset_sum _ fun J₀ _ ↦ ?_
    have hp : ContinuousAt
        (fun q ↦ ∏ a : Fin s, (Gm q)⁻¹ (I₀ a) (J₀ a)) q₀ :=
      tendsto_finset_prod _ fun a _ ↦ hGinvEnt (I₀ a) (J₀ a)
    exact (hp.mul (hslots I₀)).mul (hslots J₀)
  have hev :
      (fun q : {t : Real // t ∈ K} × M ↦
        normSq0S (I := I) (g q.1.1) q.2 s (A q.1.1 q.2)) =ᵦ[nhds q₀]
      fun q ↦
        ∑ I₀ : Fin s → Fin (Module.finrank Real E),
          ∑ J₀ : Fin s → Fin (Module.finrank Real E),
            (∏ a : Fin s, (Gm q)⁻¹ (I₀ a) (J₀ a)) *
              (A q.1.1 q.2 (fun a : Fin s ↦ e.symmL Real q.2 (b (I₀ a)))) *
              (A q.1.1 q.2 (fun a : Fin s ↦ e.symmL Real q.2 (b (J₀ a)))) := by
    filter_upwards [hopen] with q hq
    have hinv : MetricInverseInBasis_gen (I := I) (g q.1.1) q.2
        (e.basisAt b hq) (fun i j ↦ (Gm q)⁻¹ i j) := by
      simpa only [e, b, Gm] using
        chartInvGram_inverse (I := I) (g q.1.1) q₀.2 hq
    rw [normSq0S_eq_coord (I := I) (g q.1.1) q.2 s
      (e.basisAt b hq) (fun i j ↦ (Gm q)⁻¹ i j) hinv (A q.1.1 q.2)]
    unfold coordInner0S
    refine Finset.sum_congr rfl fun I₀ _ ↦ Finset.sum_congr rfl fun J₀ _ ↦ ?_
    rw [tensor0SComponent_apply, tensor0SComponent_apply]
    have hI :
        (fun a : Fin s => (e.basisAt b hq) (I₀ a)) =
          fun a : Fin s => e.localFrame b (I₀ a) q.2 := by
      funext a
      exact (e.localFrame_apply_of_mem_baseSet (b := b) (i := I₀ a) hq).symm
    have hJ :
        (fun a : Fin s => (e.basisAt b hq) (J₀ a)) =
          fun a : Fin s => e.localFrame b (J₀ a) q.2 := by
      funext a
      exact (e.localFrame_apply_of_mem_baseSet (b := b) (i := J₀ a) hq).symm
    rw [hI, hJ]
  exact hF.congr hev.symm

/-! ## The closed-edge metric-difference energy -/

/-- Pointwise squared norm of `g₁ - g₀`, measured in the moving carrier
`g₀`. -/
def movingDiffNorm
    (g₀ g₁ : Real → SmoothRiemannianMetric I M) (t : Real) (x : M) : Real :=
  normSq0S (I := I) (g₀ t) x 2
    (metricDiff02Field (I := I) (g₁ t) (g₀ t) x)

/-- The inverse-metric reaction in the squared norm of a covariant two-tensor
when the carrier metric satisfies `∂ₜg = -2Q`.  The finite-basis expression is
the coordinate realization already used by `ricReactionContract`; the value is
the intrinsic metric-variation term. -/
def reactInBasis {Idx : Type*} [Fintype Idx]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Q W : Tensor0SSpace 2 I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) : Real :=
  ricReactionContract
    (basisInvMetric (I := I) g x basis)
    (fun i j => Q (fun a : Fin 2 => if a = 0 then basis i else basis j))
    (fun I₀ => tensor0SComponent (I := I) W (fun i => basis i) I₀)
    (fun J₀ => tensor0SComponent (I := I) W (fun i => basis i) J₀)

/-- Canonical-basis spelling of the intrinsic moving-metric reaction. -/
def movingMetricReact
    (g : SmoothRiemannianMetric I M) (x : M)
    (Q W : Tensor0SSpace 2 I x) : Real :=
  let basis : Module.Basis
      (Fin (Module.finrank Real (TangentSpace I x))) Real (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x)
  reactInBasis (I := I) (M := M) g x Q W basis

/-- In any fixed tangent basis, `reactInBasis` is the derivative of the same
intrinsic squared norm under the metric variation `-2Q`.  This is the
basis-free route to comparing the canonical finite basis with an orthonormal
basis; it does not compare raw component arrays by hand. -/
theorem reactInBasis_deriv
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} {t : Real}
    (g : Real → SmoothRiemannianMetric I M)
    (Q W : Tensor0SSpace 2 I x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hg : ∀ X Y : TangentSpace I x,
      HasDerivAt
        (fun r : Real => (g r).inner x X Y)
        ((-2 : Real) * Q (fun a : Fin 2 => if a = 0 then X else Y)) t) :
    HasDerivAt
      (fun r : Real => normSq0S (I := I) (g r) x 2 W)
      (reactInBasis (I := I) (M := M) (g t) x Q W basis) t := by
  classical
  let gInv : Real → Idx → Idx → Real := fun r =>
    basisInvMetric (I := I) (g r) x basis
  let ric : Idx → Idx → Real := fun i j =>
    Q (fun a : Fin 2 => if a = 0 then basis i else basis j)
  let gInvDt : Idx → Idx → Real := fun i j =>
    -(∑ p, ∑ q, gInv t i p * ((-2 : Real) * ric p q) * gInv t q j)
  let Tdt : (Fin 2 → Idx) → Real := fun _ => 0
  have hinvAll (r : Real) :
      MetricInverseInBasis (I := I) (g r) x basis (gInv r) := by
    simpa [gInv] using basisInvMetric_real (I := I) (g r) x basis
  have hgInv (i j : Idx) :
      HasDerivWithinAt (fun r : Real => gInv r i j) (gInvDt i j) Set.univ t := by
    simpa [gInv, gInvDt, ric] using
      (basisInv_time (I := I) g
        (fun p q => (-2 : Real) * ric p q) basis
        (fun p q => by simpa [ric] using hg (basis p) (basis q)) i j)
  have hT (I₀ : Fin 2 → Idx) :
      HasDerivWithinAt
        (fun _ : Real => tensor0SComponent (I := I) W (fun i => basis i) I₀)
        (Tdt I₀) Set.univ t := by
    simpa [Tdt] using
      (hasDerivAt_const t
        (tensor0SComponent (I := I) W (fun i => basis i) I₀)).hasDerivWithinAt
  have hTdot (I₀ : Fin 2 → Idx) :
      tensor0SComponent (I := I) (0 : Tensor0SSpace 2 I x)
          (fun i => basis i) I₀ = Tdt I₀ := by
    simp [Tdt]
  have hflow (i j : Idx) :
      gInvDt i j =
        2 * (∑ p, ∑ q, gInv t i p * gInv t j q * ric p q) := by
    have hterm :
        (∑ p, ∑ q, gInv t i p * ((-2 : Real) * ric p q) * gInv t q j) =
          ∑ p, ∑ q, (-2 : Real) *
            (gInv t i p * gInv t j q * ric p q) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [gInv]
      rw [basisInvMetric_symm (I := I) (g t) x basis q j]
      ring
    have hfactor :
        (∑ p, ∑ q, (-2 : Real) *
            (gInv t i p * gInv t j q * ric p q)) =
          (-2 : Real) *
            (∑ p, ∑ q, gInv t i p * gInv t j q * ric p q) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
    simp only [gInvDt]
    rw [hterm, hfactor]
    ring
  have hbase := hasDerivWithinAt_normSq0S_ricciFlow
    (I := I) (s := 2) (u := Set.univ) (t := t)
    g gInv gInvDt ric (fun _ => W) Tdt (0 : Tensor0SSpace 2 I x)
    basis hinvAll hgInv hT hTdot hflow
  have hat := hbase.hasDerivAt (by simp)
  simpa [reactInBasis, gInv, ric] using hat

/-- `reactInBasis` is independent of the chosen basis whenever `Q` is the
actual half-speed of the displayed metric family.  Both sides are identified
as the derivative of one intrinsic norm. -/
theorem reactInBasis_eq
    {Idx₁ Idx₂ : Type*}
    [Fintype Idx₁] [DecidableEq Idx₁]
    [Fintype Idx₂] [DecidableEq Idx₂]
    {x : M} {t : Real}
    (g : Real → SmoothRiemannianMetric I M)
    (Q W : Tensor0SSpace 2 I x)
    (basis₁ : Module.Basis Idx₁ Real (TangentSpace I x))
    (basis₂ : Module.Basis Idx₂ Real (TangentSpace I x))
    (hg : ∀ X Y : TangentSpace I x,
      HasDerivAt
        (fun r : Real => (g r).inner x X Y)
        ((-2 : Real) * Q (fun a : Fin 2 => if a = 0 then X else Y)) t) :
    reactInBasis (I := I) (M := M) (g t) x Q W basis₁ =
      reactInBasis (I := I) (M := M) (g t) x Q W basis₂ := by
  exact (reactInBasis_deriv (I := I) (M := M) g Q W basis₁ hg).unique
    (reactInBasis_deriv (I := I) (M := M) g Q W basis₂ hg)

/-- Rewrite the canonical moving reaction in any basis, without a raw
change-of-components proof. -/
theorem movingReact_basis
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} {t : Real}
    (g : Real → SmoothRiemannianMetric I M)
    (Q W : Tensor0SSpace 2 I x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hg : ∀ X Y : TangentSpace I x,
      HasDerivAt
        (fun r : Real => (g r).inner x X Y)
        ((-2 : Real) * Q (fun a : Fin 2 => if a = 0 then X else Y)) t) :
    movingMetricReact (I := I) (M := M) (g t) x Q W =
      reactInBasis (I := I) (M := M) (g t) x Q W basis := by
  classical
  unfold movingMetricReact
  exact reactInBasis_eq (I := I) (M := M) g Q W
    (Module.finBasis Real (TangentSpace I x)) basis hg

/-- Two arrays satisfying the two-sided inverse-metric equations in the same
basis agree. -/
private theorem metricInv_unique
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (A B : Idx → Idx → Real)
    (hA : MetricInverseInBasis (I := I) g x basis A)
    (hB : MetricInverseInBasis (I := I) g x basis B) :
    A = B := by
  classical
  funext i j
  calc
    A i j = ∑ k : Idx, A i k * (if k = j then (1 : Real) else 0) := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hkj
        simp [hkj]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    _ = ∑ k : Idx, A i k *
          (∑ l : Idx, g.inner x (basis k) (basis l) * B l j) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [(hB k j).2]
    _ = ∑ l : Idx,
          (∑ k : Idx, A i k * g.inner x (basis k) (basis l)) * B l j := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    _ = ∑ l : Idx, (if i = l then (1 : Real) else 0) * B l j := by
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [(hA i l).1]
    _ = B i j := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro l _ hli
        simp [hli]
      · intro hi
        exact absurd (Finset.mem_univ i) hi

/-- Orthonormal-component realization of the canonical moving reaction.  The
only basis change is `movingReact_basis`; after that the inverse metric is the
Kronecker delta and the standard reaction collapse applies verbatim. -/
theorem movingReact_ortho
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} {t : Real}
    (g : Real → SmoothRiemannianMetric I M)
    (Q W : Tensor0SSpace 2 I x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      (g t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (hg : ∀ X Y : TangentSpace I x,
      HasDerivAt
        (fun r : Real => (g r).inner x X Y)
        ((-2 : Real) * Q (fun a : Fin 2 => if a = 0 then X else Y)) t) :
    movingMetricReact (I := I) (M := M) (g t) x Q W =
      2 * ∑ I₀ : Fin 2 → Idx,
        tensor0SComponent (I := I) W (fun i => basis i) I₀ *
          ricStarArray
            (fun i j => Q
              (fun a : Fin 2 => if a = 0 then basis i else basis j))
            (fun J₀ => tensor0SComponent (I := I) W (fun i => basis i) J₀) I₀ := by
  classical
  rw [movingReact_basis (I := I) (M := M) g Q W basis hg]
  unfold reactInBasis
  have hcanon := basisInvMetric_real (I := I) (g t) x basis
  have hid := metricInverseInBasis_identity_of_orthonormal
    (I := I) (g t) basis horth
  have heq : basisInvMetric (I := I) (g t) x basis =
      identityInvMetric (Idx := Idx) :=
    metricInv_unique (I := I) (M := M) (g t) x basis _ _ hcanon hid
  rw [heq]
  exact ricReactionContract_delta_eq_compContract
    (Idx := Idx)
    (fun i j => Q (fun a : Fin 2 => if a = 0 then basis i else basis j))
    (fun I₀ => tensor0SComponent (I := I) W (fun i => basis i) I₀)
    (fun J₀ => tensor0SComponent (I := I) W (fun i => basis i) J₀)

/-- Pure component estimate for the rank-two reaction after orthonormal
collapse.  Deliberately keeping the finite-cardinality constant explicit makes
this independent of any dimension-specific simplification. -/
theorem ricReactArray_le
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (q : Idx → Idx → Real) (Wc : (Fin 2 → Idx) → Real)
    {B : Real} (hB : 0 ≤ B) (hq : ∀ i j : Idx, |q i j| ≤ B) :
    |2 * ∑ I₀ : Fin 2 → Idx, Wc I₀ * ricStarArray q Wc I₀| ≤
      2 * (Fintype.card (Fin 2 → Idx) : Real) *
        ((2 : Real) * (Fintype.card Idx : Real) * B) * compNormSqMulti Wc := by
  classical
  let N : Real := compNormSqMulti Wc
  have hN : 0 ≤ N := by
    simpa only [N] using compNormSqMulti_nonneg Wc
  have hsqrt : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hinner :
      |∑ I₀ : Fin 2 → Idx, Wc I₀ * ricStarArray q Wc I₀| ≤
        ∑ _I₀ : Fin 2 → Idx,
          Real.sqrt N *
            ((2 : Real) * (Fintype.card Idx : Real) * B * Real.sqrt N) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun I₀ _ => ?_
    rw [abs_mul]
    have hW : |Wc I₀| ≤ Real.sqrt N := by
      simpa only [N] using abs_le_sqrt_compNormSqMulti Wc I₀
    have hstar : |ricStarArray q Wc I₀| ≤
        (2 : Real) * (Fintype.card Idx : Real) * B * Real.sqrt N := by
      simpa only [N] using abs_ricStarArray_le q Wc B hB hq I₀
    exact mul_le_mul hW hstar (abs_nonneg _) hsqrt
  have hconst :
      (∑ _I₀ : Fin 2 → Idx,
          Real.sqrt N *
            ((2 : Real) * (Fintype.card Idx : Real) * B * Real.sqrt N)) =
        (Fintype.card (Fin 2 → Idx) : Real) *
          (Real.sqrt N *
            ((2 : Real) * (Fintype.card Idx : Real) * B * Real.sqrt N)) := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsqrt_sq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN
  rw [abs_mul, show |(2 : Real)| = 2 by norm_num]
  calc
    2 * |∑ I₀ : Fin 2 → Idx, Wc I₀ * ricStarArray q Wc I₀| ≤
        2 * ((Fintype.card (Fin 2 → Idx) : Real) *
          (Real.sqrt N *
            ((2 : Real) * (Fintype.card Idx : Real) * B * Real.sqrt N))) := by
      exact mul_le_mul_of_nonneg_left (le_trans hinner (le_of_eq hconst)) (by norm_num)
    _ = 2 * (Fintype.card (Fin 2 → Idx) : Real) *
          ((2 : Real) * (Fintype.card Idx : Real) * B) * N := by
      rw [show Real.sqrt N *
          ((2 : Real) * (Fintype.card Idx : Real) * B * Real.sqrt N) =
            ((2 : Real) * (Fintype.card Idx : Real) * B) *
              (Real.sqrt N * Real.sqrt N) by ring, hsqrt_sq]
      ring
    _ = 2 * (Fintype.card (Fin 2 → Idx) : Real) *
          ((2 : Real) * (Fintype.card Idx : Real) * B) *
            compNormSqMulti Wc := by simp only [N]

/-- Pointwise reaction bound in intrinsic norm.  It assumes only the carrier
metric equation at the time in question and an operator bound for `Q`; no
spatial derivative of the comparison path occurs. -/
theorem movingReact_le
    {x : M} {t B : Real}
    (g : Real → SmoothRiemannianMetric I M)
    (Q W : Tensor0SSpace 2 I x)
    (hB : 0 ≤ B)
    (hQ : ∀ v w : TangentSpace I x,
      |eval02 (I := I) (M := M) Q v w| ≤
        B * Real.sqrt ((g t).inner x v v) *
          Real.sqrt ((g t).inner x w w))
    (hg : ∀ X Y : TangentSpace I x,
      HasDerivAt
        (fun r : Real => (g r).inner x X Y)
        ((-2 : Real) * Q (fun a : Fin 2 => if a = 0 then X else Y)) t) :
    |movingMetricReact (I := I) (M := M) (g t) x Q W| ≤
      (2 * (Fintype.card
          (Fin 2 → Fin (Module.finrank Real E)) : Real) *
        ((2 : Real) * (Module.finrank Real E : Real) * B)) *
          normSq0S (I := I) (g t) x 2 W := by
  classical
  obtain ⟨e, basis, hbasis, horth⟩ :=
    DifferentialGeometry.Analysis.Sobolev.TensorHilbert.exists_orthoFrame_basis_E
      (I := I) (M := M) (g t) x
  have horth' : ∀ i j : Fin (Module.finrank Real E),
      (g t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0 := by
    intro i j
    rw [hbasis i, hbasis j]
    exact horth i j
  let q : Fin (Module.finrank Real E) → Fin (Module.finrank Real E) → Real :=
    fun i j => Q (fun a : Fin 2 => if a = 0 then basis i else basis j)
  let Wc : (Fin 2 → Fin (Module.finrank Real E)) → Real :=
    fun I₀ => tensor0SComponent (I := I) W (fun i => basis i) I₀
  have hq : ∀ i j : Fin (Module.finrank Real E), |q i j| ≤ B := by
    intro i j
    have hunit_i : (g t).inner x (basis i) (basis i) = 1 := by
      simpa using horth' i i
    have hunit_j : (g t).inner x (basis j) (basis j) = 1 := by
      simpa using horth' j j
    simpa [q, eval02, hunit_i, hunit_j] using hQ (basis i) (basis j)
  have harray := ricReactArray_le q Wc hB hq
  have harray' :
      |2 * ∑ I₀ : Fin 2 → Fin (Module.finrank Real E),
          tensor0SComponent (I := I) W (fun i => basis i) I₀ *
            ricStarArray
              (fun i j => Q
                (fun a : Fin 2 => if a = 0 then basis i else basis j))
              (fun J₀ => tensor0SComponent (I := I) W (fun i => basis i) J₀) I₀| ≤
        2 * (Fintype.card
            (Fin 2 → Fin (Module.finrank Real E)) : Real) *
          ((2 : Real) * (Fintype.card
            (Fin (Module.finrank Real E)) : Real) * B) * compNormSqMulti Wc := by
    simpa only [q, Wc] using harray
  have hreact := movingReact_ortho
    (I := I) (M := M) g Q W basis horth' hg
  rw [hreact]
  refine le_trans harray' ?_
  simp only [Wc]
  rw [compNormSqMulti_orthoBasis_eq_normSq0S
    (I := I) (g t) basis horth' W]
  simp only [Fintype.card_fin]

/-! ## The moving-volume trace from the same carrier bound -/

/-- A fibre-operator bound for a covariant two-tensor controls its intrinsic
metric trace by one factor of the tangent dimension. -/
theorem metricTrace_op_le
    {x : M} (g : SmoothRiemannianMetric I M)
    (Q : Tensor0SSpace 2 I x) {B : Real}
    (hQ : ∀ v w : TangentSpace I x,
      |eval02 (I := I) (M := M) Q v w| ≤
        B * Real.sqrt (g.inner x v v) *
          Real.sqrt (g.inner x w w)) :
    |metricTracePair0SAt (I := I) g Q| ≤
      (Module.finrank Real E : Real) * B := by
  classical
  obtain ⟨e, basis, hbasis, horth⟩ :=
    DifferentialGeometry.Analysis.Sobolev.TensorHilbert.exists_orthoFrame_basis_E
      (I := I) (M := M) g x
  have horth' : ∀ i j : Fin (Module.finrank Real E),
      g.inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0 := by
    intro i j
    rw [hbasis i, hbasis j]
    exact horth i j
  have hinv := metricInverseInBasis_identity_of_orthonormal
    (I := I) g basis horth'
  have htrace : metricTracePair0SAt (I := I) g Q =
      ∑ i : Fin (Module.finrank Real E),
        Q (vec2 (I := I) (basis i) (basis i)) := by
    rw [metricTracePair0SAt_eq_sum_basis (I := I) g basis
      (identityInvMetric (Idx := Fin (Module.finrank Real E))) hinv Q]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · simp only [identityInvMetric_apply_self, one_mul]
    · intro j _ hji
      rw [identityInvMetric,
        diagonalInvMetric_eq_zero_of_ne (fun hij => hji hij.symm), zero_mul]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [htrace]
  calc
    |∑ i : Fin (Module.finrank Real E),
        Q (vec2 (I := I) (basis i) (basis i))| ≤
        ∑ i : Fin (Module.finrank Real E),
          |Q (vec2 (I := I) (basis i) (basis i))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank Real E), B := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hunit : g.inner x (basis i) (basis i) = 1 := by
        simpa using horth' i i
      simpa [eval02, vec2, hunit] using hQ (basis i) (basis i)
    _ = (Module.finrank Real E : Real) * B := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Under the metric variation `∂ₜg = -2Q`, the chart-defined volume trace is
the intrinsic metric trace of `-2Q`. -/
theorem traceTime_rd
    {x : M} {t : Real}
    (g : Real → SmoothRiemannianMetric I M)
    (Q : Tensor0SSpace 2 I x)
    (hg : ∀ X Y : TangentSpace I x,
      HasDerivAt
        (fun r : Real => (g r).inner x X Y)
        ((-2 : Real) * Q (vec2 (I := I) X Y)) t) :
    traceTimeDerivMetric (I := I) g t x =
      (-2 : Real) * metricTracePair0SAt (I := I) (g t) Q := by
  classical
  let Gmat : Matrix (Fin (Module.finrank Real E))
      (Fin (Module.finrank Real E)) Real :=
    chartGramMatrix (I := I) (g t) x x
  let dG : Matrix (Fin (Module.finrank Real E))
      (Fin (Module.finrank Real E)) Real :=
    Matrix.of fun i j =>
      deriv (fun r : Real => chartGramMatrix (I := I) (g r) x x i j) t
  have htrace : traceTimeDerivMetric (I := I) g t x =
      Matrix.trace (Gmat⁻¹ * dG) := by
    simp only [traceTimeDerivMetric_eq, Gmat, dG]
  have hdG : dG =
      Matrix.of fun i j : Fin (Module.finrank Real E) =>
        (-2 : Real) * Q (vec2 (I := I)
          (chartBasisVecFiber (I := I) x i x)
          (chartBasisVecFiber (I := I) x j x)) := by
    ext i j
    simpa only [dG, Matrix.of_apply, chartGramMatrix_apply] using
      (hg (chartBasisVecFiber (I := I) x i x)
        (chartBasisVecFiber (I := I) x j x)).deriv
  have hInvSymm : ∀ i j : Fin (Module.finrank Real E),
      Gmat⁻¹ j i = Gmat⁻¹ i j := by
    intro i j
    have hHerm :
        ((chartGramMatrix (I := I) (g t) x x)⁻¹).IsHermitian :=
      (chartGramMatrix_isHermitian (I := I) (g t) x x).inv
    simpa only [Gmat, star_trivial] using hHerm.apply i j
  have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x
  let basis := chartBasisFamily (I := I) x hx
  have hinv := chartInvGram_inverse (I := I) (g t) x hx
  have hscalar : metricTracePair0SAt (I := I) (g t) Q =
      ∑ i : Fin (Module.finrank Real E),
        ∑ j : Fin (Module.finrank Real E),
          Gmat⁻¹ i j * Q (vec2 (I := I)
            (chartBasisVecFiber (I := I) x i x)
            (chartBasisVecFiber (I := I) x j x)) := by
    rw [metricTracePair0SAt_eq_sum_basis (I := I) (g t) basis
      (chartInvGramMatrix (I := I) (g t) x x) hinv Q]
    simp only [basis, Gmat, chartInvGramMatrix, chartBasisFamily_apply]
  rw [htrace, hdG]
  calc
    Matrix.trace
        (Gmat⁻¹ *
          Matrix.of fun i j : Fin (Module.finrank Real E) =>
            (-2 : Real) * Q (vec2 (I := I)
              (chartBasisVecFiber (I := I) x i x)
              (chartBasisVecFiber (I := I) x j x))) =
        Matrix.trace
          ((Matrix.of fun i j : Fin (Module.finrank Real E) =>
            (-2 : Real) * Q (vec2 (I := I)
              (chartBasisVecFiber (I := I) x i x)
              (chartBasisVecFiber (I := I) x j x))) * Gmat⁻¹) := by
      rw [Matrix.trace_mul_comm]
    _ = ∑ i : Fin (Module.finrank Real E),
          ∑ j : Fin (Module.finrank Real E),
            ((-2 : Real) * Q (vec2 (I := I)
              (chartBasisVecFiber (I := I) x i x)
              (chartBasisVecFiber (I := I) x j x))) * Gmat⁻¹ j i := by
      simp [Matrix.trace, Matrix.mul_apply]
    _ = (-2 : Real) *
          (∑ i : Fin (Module.finrank Real E),
            ∑ j : Fin (Module.finrank Real E),
              Gmat⁻¹ i j * Q (vec2 (I := I)
                (chartBasisVecFiber (I := I) x i x)
                (chartBasisVecFiber (I := I) x j x))) := by
      simp_rw [hInvSymm]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    _ = (-2 : Real) * metricTracePair0SAt (I := I) (g t) Q := by
      rw [hscalar]

/-- The inverse-metric and moving-volume reactions are controlled together by
the same closed-slab carrier half-speed bound. -/
theorem movingReactVol_le
    {x : M} {t B : Real}
    (g : Real → SmoothRiemannianMetric I M)
    (Q W : Tensor0SSpace 2 I x)
    (hB : 0 ≤ B)
    (hQ : ∀ v w : TangentSpace I x,
      |eval02 (I := I) (M := M) Q v w| ≤
        B * Real.sqrt ((g t).inner x v v) *
          Real.sqrt ((g t).inner x w w))
    (hg : ∀ X Y : TangentSpace I x,
      HasDerivAt
        (fun r : Real => (g r).inner x X Y)
        ((-2 : Real) * Q (vec2 (I := I) X Y)) t) :
    |movingMetricReact (I := I) (M := M) (g t) x Q W +
        (1 / 2 : Real) * traceTimeDerivMetric (I := I) g t x *
          normSq0S (I := I) (g t) x 2 W| ≤
      ((2 * (Fintype.card
          (Fin 2 → Fin (Module.finrank Real E)) : Real) *
        ((2 : Real) * (Module.finrank Real E : Real) * B)) +
        (Module.finrank Real E : Real) * B) *
          normSq0S (I := I) (g t) x 2 W := by
  have hg' : ∀ X Y : TangentSpace I x,
      HasDerivAt
        (fun r : Real => (g r).inner x X Y)
        ((-2 : Real) * Q
          (fun a : Fin 2 => if a = 0 then X else Y)) t := by
    simpa only [vec2] using hg
  have hreact := movingReact_le (I := I) (M := M)
    g Q W hB hQ hg'
  have htrace : |traceTimeDerivMetric (I := I) g t x| ≤
      2 * ((Module.finrank Real E : Real) * B) := by
    rw [traceTime_rd (I := I) (M := M) g Q hg, abs_mul]
    rw [show |(-2 : Real)| = 2 by norm_num]
    exact
      mul_le_mul_of_nonneg_left
        (metricTrace_op_le (I := I) (M := M) (g t) Q hQ)
        (show (0 : Real) ≤ 2 by norm_num)
  have hN : 0 ≤ normSq0S (I := I) (g t) x 2 W :=
    normSq0S_nonneg (I := I) (g t) x 2 W
  have hvol :
      |(1 / 2 : Real) * traceTimeDerivMetric (I := I) g t x *
          normSq0S (I := I) (g t) x 2 W| ≤
        ((Module.finrank Real E : Real) * B) *
          normSq0S (I := I) (g t) x 2 W := by
    calc
      |(1 / 2 : Real) * traceTimeDerivMetric (I := I) g t x *
          normSq0S (I := I) (g t) x 2 W| =
          (1 / 2 : Real) * |traceTimeDerivMetric (I := I) g t x| *
            normSq0S (I := I) (g t) x 2 W := by
        rw [abs_mul, abs_mul, abs_of_nonneg hN]
        norm_num
      _ ≤ (1 / 2 : Real) *
          (2 * ((Module.finrank Real E : Real) * B)) *
            normSq0S (I := I) (g t) x 2 W := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left htrace (by norm_num)) hN
      _ = ((Module.finrank Real E : Real) * B) *
          normSq0S (I := I) (g t) x 2 W := by ring
  calc
    |movingMetricReact (I := I) (M := M) (g t) x Q W +
        (1 / 2 : Real) * traceTimeDerivMetric (I := I) g t x *
          normSq0S (I := I) (g t) x 2 W| ≤
        |movingMetricReact (I := I) (M := M) (g t) x Q W| +
          |(1 / 2 : Real) * traceTimeDerivMetric (I := I) g t x *
            normSq0S (I := I) (g t) x 2 W| := abs_add _ _
    _ ≤ (2 * (Fintype.card
          (Fin 2 → Fin (Module.finrank Real E)) : Real) *
        ((2 : Real) * (Module.finrank Real E : Real) * B)) *
          normSq0S (I := I) (g t) x 2 W +
        ((Module.finrank Real E : Real) * B) *
          normSq0S (I := I) (g t) x 2 W := add_le_add hreact hvol
    _ = ((2 * (Fintype.card
          (Fin 2 → Fin (Module.finrank Real E)) : Real) *
        ((2 : Real) * (Module.finrank Real E : Real) * B)) +
        (Module.finrank Real E : Real) * B) *
          normSq0S (I := I) (g t) x 2 W := by ring

/-- The intrinsic `L²` energy of `g₁ - g₀`, measured in the moving carrier
`g₀` and its moving volume measure. -/
def movingDiffEnergy
    (g₀ g₁ : Real → SmoothRiemannianMetric I M) (t : Real) : Real :=
  ∫ x, movingDiffNorm (I := I) (M := M) g₀ g₁ t x
    ∂(riemannianMeasureFamily (I := I) (M := M) g₀ t)

/-- Closed-edge continuity of the moving metric-difference energy.  This is
the continuity input of `edgeGronwall_zero`; it follows from the two chart-Gram
`C⁰` hypotheses and compactness, without any derivative at the edge. -/
theorem movingEnergy_cont
    (g₀ g₁ : Real → SmoothRiemannianMetric I M) {K : Set Real}
    (hK : IsCompact K)
    (h₀ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContinuousOn
        (fun p : Real × M ↦
          chartGramMatrix (I := I) (g₀ p.1) x₀ p.2 i j)
        (K ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContinuousOn
        (fun p : Real × M ↦
          chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (K ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContinuousOn (movingDiffEnergy (I := I) (M := M) g₀ g₁) K := by
  classical
  have h₀' : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContinuousOn
        (fun q : {t : Real // t ∈ K} × M ↦
          chartGramMatrix (I := I) (g₀ q.1.1) x₀ q.2 i j)
        {q : {t : Real // t ∈ K} × M |
          q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet} := by
    intro x₀ i j
    exact (h₀ x₀ i j).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousOn
      (fun q hq ↦ ⟨q.1.2, hq⟩)
  have h₁' : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContinuousOn
        (fun q : {t : Real // t ∈ K} × M ↦
          chartGramMatrix (I := I) (g₁ q.1.1) x₀ q.2 i j)
        {q : {t : Real // t ∈ K} × M |
          q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet} := by
    intro x₀ i j
    exact (h₁ x₀ i j).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousOn
      (fun q hq ↦ ⟨q.1.2, hq⟩)
  have hmetric₀ := metricTensorCont_of_chartGram (I := I) (M := M) g₀ h₀'
  have hmetric₁ := metricTensorCont_of_chartGram (I := I) (M := M) g₁ h₁'
  have hdiffRaw := hmetric₁.add
    (Tensor0SFamilyContinuousOnSet.const_smul (I := I) (M := M) (-1) hmetric₀)
  have hdiff : Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K
      (fun t x ↦ metricDiff02Field (I := I) (g₁ t) (g₀ t) x) := by
    refine Tensor0SFamilyContinuousOnSet.congr (I := I) (M := M) hdiffRaw ?_
    intro t ht x
    apply Tensor0SSpace.toModel_injective
    ext v
    rw [metricDiff02Field_toModel_apply]
    simp only [Pi.add_apply, Pi.smul_apply, neg_one_smul,
      Tensor0SSpace.toModel_add, Tensor0SSpace.toModel_neg,
      metricTensorField_apply, metricDiff02_apply]
    ring
  have hnormSub := normSq_family_cont (I := I) (M := M) g₀
    (fun t x ↦ metricDiff02Field (I := I) (g₁ t) (g₀ t) x) h₀' hdiff
  have hnorm : ContinuousOn
      (fun p : Real × M ↦ normSq0S (I := I) (g₀ p.1) p.2 2
        (metricDiff02Field (I := I) (g₁ p.1) (g₀ p.1) p.2))
      (K ×ˢ (Set.univ : Set M)) := by
    rw [continuousOn_iff_continuous_restrict]
    let pull : {p : Real × M // p ∈ K ×ˢ (Set.univ : Set M)} →
        {t : Real // t ∈ K} × M := fun p ↦ (⟨p.1.1, p.2.1⟩, p.1.2)
    have hpull : Continuous pull := by
      exact (((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
        (continuous_snd.comp continuous_subtype_val))
    simpa only [pull] using hnormSub.comp hpull
  simpa only [movingDiffEnergy, movingDiffNorm] using
    integral_family_cont (I := I) (M := M) hK h₀ hnorm

/-! ## Interior smoothness and exact first variation -/

/-- On an open regular time set, joint smoothness of the two chart-Gram
families implies joint smoothness of the moving pointwise difference norm.

This is the smooth analogue of `normSq_family_cont`, specialized to the metric
difference.  In a carrier chart it is the finite contraction
`g₀⁻¹ g₀⁻¹ (g₁-g₀) (g₁-g₀)`. -/
theorem movingNorm_smooth
    (g₀ g₁ : Real → SmoothRiemannianMetric I M) {U : Set Real}
    (hU : IsOpen U)
    (h₀ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝒰(Real, Real).prod I) 𝒰(Real, Real) ∞
        (fun p : Real × M ↦
          chartGramMatrix (I := I) (g₀ p.1) x₀ p.2 i j)
        (U ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝒰(Real, Real).prod I) 𝒰(Real, Real) ∞
        (fun p : Real × M ↦
          chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (U ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContMDiffOn (𝒰(Real, Real).prod I) 𝒰(Real, Real) ∞
      (fun p : Real × M ↦
        movingDiffNorm (I := I) (M := M) g₀ g₁ p.1 p.2)
      (U ×ˢ (Set.univ : Set M)) := by
  classical
  intro p hp
  let x₀ : M := p.2
  let e := trivializationAt E (TangentSpace I : M → Type _) x₀
  let b : Module.Basis (Fin (Module.finrank Real E)) Real E := chartModelBasis E
  have hx : x₀ ∈ e.baseSet := by
    simpa only [e, x₀] using
      mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) p.2
  let G₀ : Real × M →
      Matrix (Fin (Module.finrank Real E)) (Fin (Module.finrank Real E)) Real :=
    fun q ↦ chartGramMatrix (I := I) (g₀ q.1) x₀ q.2
  let G₁ : Real × M →
      Matrix (Fin (Module.finrank Real E)) (Fin (Module.finrank Real E)) Real :=
    fun q ↦ chartGramMatrix (I := I) (g₁ q.1) x₀ q.2
  have hG₀ (i j : Fin (Module.finrank Real E)) :
      ContMDiffAt (𝒰(Real, Real).prod I) 𝒰(Real, Real) ∞
        (fun q ↦ G₀ q i j) p := by
    simpa only [G₀] using
      (h₀ x₀ i j).contMDiffAt
        ((hU.prod e.open_baseSet).mem_nhds ⟨hp.1, hx⟩)
  have hG₁ (i j : Fin (Module.finrank Real E)) :
      ContMDiffAt (𝒰(Real, Real).prod I) 𝒰(Real, Real) ∞
        (fun q ↦ G₁ q i j) p := by
    simpa only [G₁] using
      (h₁ x₀ i j).contMDiffAt
        ((hU.prod e.open_baseSet).mem_nhds ⟨hp.1, hx⟩)
  have det_smooth
      (G : Real × M →
        Matrix (Fin (Module.finrank Real E)) (Fin (Module.finrank Real E)) Real)
      (hG : ∀ i j : Fin (Module.finrank Real E),
        ContMDiffAt (𝒰(Real, Real).prod I) 𝒰(Real, Real) ∞
          (fun q ↦ G q i j) p) :
      ContMDiffAt (𝒰(Real, Real).prod I) 𝒰(Real, Real) ∞
        (fun q ↦ (G q).det) p := by
    have heq : (fun q ↦ (G q).det) = fun q ↦
        ∑ σ : Equiv.Perm (Fin (Module.finrank Real E)),
          ((Equiv.Perm.sign σ : Int) : Real) * ∏ i, G q (σ i) i := by
      funext q
      rw [Matrix.det_apply]
      simp [Units.smul_def]
    rw [heq]
    refine ContMDiffAt.sum fun σ _ ↦ ?_
    exact (contMDiffAt_const (c := (((Equiv.Perm.sign σ : ℤ) : Real))).mul
      (ContMDiffAt.prod fun i _ ↦ hG (σ i) i)
  have hdet := det_smooth G₀ hG₀
  have hadj (i j : Fin (Module.finrank Real E)) :
      ContMDiffAt (𝒰(Real, Real).prod I) 𝒰(Real, Real) ∞
        (fun q ↦ (G₀ q).adjugate i j) p := by
    simp_rw [Matrix.adjugate_apply]
    apply det_smooth
    intro a c
    by_cases ha : a = j
    · subst a
      simp only [Matrix.updateRow_self]
      exact contMDiffAt_const
    · simp only [Matrix.updateRow_ne ha]
      exact hG₀ a c
  have hdetne : (G₀ p).det ≠ 0 := by
    exact ne_of_gt
      (chartGramMatrix_det_pos (I := I) (g₀ p.1) x₀ hx)
  have hInv (i j : Fin (Module.finrank Real E)) :
      ContMDiffAt (𝒰(Real, Real).prod I) 𝒰(Real, Real) ∞
        (fun q ↦ (G₀ q)⁻¹ i j) p := by
    have heq : (fun q ↦ (G₀ q)⁻¹ i j) =
        fun q ↦ ((G₀ q).det)⁻¹ * (G₀ q).adjugate i j := by
      funext q
      rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
    rw [heq]
    exact (hdet.inv₀ hdetne).mul (hadj i j)
  let W : (Real × M) →
      (Fin 2 → Fin (Module.finrank Real E)) → Real := fun q I₀ ↦
    G₁ q (I₀ 0) (I₀ 1) - G₀ q (I₀ 0) (I₀ 1)
  have hW (I₀ : Fin 2 → Fin (Module.finrank Real E)) :
      ContMDiffAt (𝒰(Real, Real).prod I) 𝒰(Real, Real) ∞
        (fun q ↦ W q I₀) p := by
    exact (hG₁ (I₀ 0) (I₀ 1)).sub (hG₀ (I₀ 0) (I₀ 1))
  let rhs : Real × M → Real := fun q ↦
    ∑ I₀ : Fin 2 → Fin (Module.finrank Real E),
      ∑ J₀ : Fin 2 → Fin (Module.finrank Real E),
        (∏ a : Fin 2, (G₀ q)⁻¹ (I₀ a) (J₀ a)) * W q I₀ * W q J₀
  have hrhs : ContMDiffAt (𝒰(Real, Real).prod I) 𝒰(Real, Real) ∞ rhs p := by
    refine ContMDiffAt.sum fun I₀ _ ↦ ContMDiffAt.sum fun J₀ _ ↦ ?_
    have hpInv : ContMDiffAt (𝒰(Real, Real).prod I) 𝒰(Real, Real) ∞
        (fun q ↦ ∏ a : Fin 2, (G₀ q)⁻¹ (I₀ a) (J₀ a)) p :=
      ContMDiffAt.prod fun a _ ↦ hInv (I₀ a) (J₀ a)
    exact (hpInv.mul (hW I₀)).mul (hW J₀)
  have heq :
      (fun q : Real × M ↦
        movingDiffNorm (I := I) (M := M) g₀ g₁ q.1 q.2) =ᵦ[nhds p] rhs := by
    filter_upwards [(hU.prod e.open_baseSet).mem_nhds ⟨hp.1, hx⟩] with q hq
    have hinv : MetricInverseInBasis_gen (I := I) (g₀ q.1) q.2
        (e.basisAt b hq.2) (fun i j ↦ (G₀ q)⁻¹ i j) := by
      simpa only [e, b, G₀, x₀] using
        chartInvGram_inverse (I := I) (g₀ q.1) p.2 hq.2
    rw [movingDiffNorm,
      normSq0S_eq_coord (I := I) (g₀ q.1) q.2 2
        (e.basisAt b hq.2) (fun i j ↦ (G₀ q)⁻¹ i j) hinv
        (metricDiff02Field (I := I) (g₁ q.1) (g₀ q.1) q.2)]
    unfold coordInner0S rhs
    refine Finset.sum_congr rfl fun I₀ _ ↦ Finset.sum_congr rfl fun J₀ _ ↦ ?_
    have hcomp (K₀ : Fin 2 → Fin (Module.finrank Real E)) :
        tensor0SComponent (I := I)
            (metricDiff02Field (I := I) (g₁ q.1) (g₀ q.1) q.2)
            (fun i ↦ e.basisAt b hq.2 i) K₀ = W q K₀ := by
      rw [tensor0SComponent_apply]
      change Tensor0SSpace.toModel
          (metricDiff02Field (I := I) (g₁ q.1) (g₀ q.1) q.2)
          (fun a ↦ e.basisAt b hq.2 (K₀ a)) = _
      rw [metricDiff02Field_toModel_apply, metricDiff02_apply]
      simp only [e, b, G₀, G₁, W, x₀, chartBasisFamily_apply]
      have hslot (a : Fin 2) :
          (e.basisAt b hq.2) (K₀ a) = e.localFrame b (K₀ a) q.2 :=
        (e.localFrame_apply_of_mem_baseSet (b := b) (i := K₀ a) hq.2).symm
      rw [hslot 0, hslot 1]
      rfl
    rw [hcomp I₀, hcomp J₀]
  exact (hrhs.congr_of_eventuallyEq heq.symm).contMDiffWithinAt

/-- Exact pointwise time derivative of the moving squared norm.  Only
interior-time derivatives occur: the carrier has variation `-2Q` and the
metric difference has variation `Wdot`.  Thus this theorem can be applied on
`Ioo a b` while closed-edge continuity is supplied separately by
`movingEnergy_cont`. -/
theorem movingNorm_time {x : M} {t : Real}
    (g₀ g₁ : Real → SmoothRiemannianMetric I M)
    (Q Wdot : Tensor0SSpace 2 I x)
    (hg : ∀ X Y : TangentSpace I x,
      HasDerivAt
        (fun r : Real ↦ (g₀ r).inner x X Y)
        ((-2 : Real) * Q (fun a : Fin 2 => if a = 0 then X else Y)) t)
    (hW : ∀ X Y : TangentSpace I x,
      HasDerivAt
        (fun r : Real ↦ metricDiff02 (I := I) (g₁ r) (g₀ r) x X Y)
        (Tensor0SSpace.toModel Wdot
          (fun a : Fin 2 => if a = 0 then X else Y)) t) :
    HasDerivAt
      (fun r : Real ↦ movingDiffNorm (I := I) (M := M) g₀ g₁ r x)
      (movingMetricReact (I := I) (M := M) (g₀ t) x Q
          (metricDiff02Field (I := I) (g₁ t) (g₀ t) x) +
        2 * inner0S (I := I) (g₀ t) x 2 Wdot
          (metricDiff02Field (I := I) (g₁ t) (g₀ t) x)) t := by
  classical
  let basis : Module.Basis
      (Fin (Module.finrank Real (TangentSpace I x))) Real (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x)
  let gInv : Real →
      Fin (Module.finrank Real (TangentSpace I x)) →
      Fin (Module.finrank Real (TangentSpace I x)) → Real := fun r ↦
    basisInvMetric (I := I) (g₀ r) x basis
  let ric :
      Fin (Module.finrank Real (TangentSpace I x)) →
      Fin (Module.finrank Real (TangentSpace I x)) → Real := fun i j ↦
    Q (fun a : Fin 2 => if a = 0 then basis i else basis j)
  let gInvDt :
      Fin (Module.finrank Real (TangentSpace I x)) →
      Fin (Module.finrank Real (TangentSpace I x)) → Real := fun i j ↦
    -(∑ p, ∑ q, gInv t i p * ((-2 : Real) * ric p q) * gInv t q j)
  let T : Real → Tensor0SSpace 2 I x := fun r ↦
    metricDiff02Field (I := I) (g₁ r) (g₀ r) x
  let Tdt :
      (Fin 2 → Fin (Module.finrank Real (TangentSpace I x))) → Real := fun I₀ ↦
    tensor0SComponent (I := I) Wdot (fun i ↦ basis i) I₀
  have hinvAll (r : Real) :
      MetricInverseInBasis (I := I) (g₀ r) x basis (gInv r) := by
    simpa [gInv] using basisInvMetric_real (I := I) (g₀ r) x basis
  have hgInv (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      HasDerivWithinAt (fun r : Real ↦ gInv r i j) (gInvDt i j) Set.univ t := by
    simpa [gInv, gInvDt, ric] using
      (basisInv_time (I := I) g₀
        (fun p q ↦ (-2 : Real) * ric p q) basis
        (fun p q ↦ by simpa [ric] using hg (basis p) (basis q)) i j)
  have hT (I₀ : Fin 2 → Fin (Module.finrank Real (TangentSpace I x))) :
      HasDerivWithinAt
        (fun r : Real ↦ tensor0SComponent (I := I) (T r) (fun i ↦ basis i) I₀)
        (Tdt I₀) Set.univ t := by
    have hslots :
        (fun a : Fin 2 ↦ basis (I₀ a)) =
          fun a : Fin 2 ↦ if a = 0 then basis (I₀ 0) else basis (I₀ 1) := by
      funext a
      fin_cases a <;> simp
    rw [tensor0SComponent_apply]
    simp only [T, metricDiff02Field_toModel_apply, Tdt,
      tensor0SComponent_apply]
    simpa only [hslots] using
      (hW (basis (I₀ 0)) (basis (I₀ 1))).hasDerivWithinAt
  have hTdot (I₀ : Fin 2 → Fin (Module.finrank Real (TangentSpace I x))) :
      tensor0SComponent (I := I) Wdot (fun i ↦ basis i) I₀ = Tdt I₀ := by
    rfl
  have hflow (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      gInvDt i j =
        2 * (∑ p, ∑ q, gInv t i p * gInv t j q * ric p q) := by
    have hterm :
        (∑ p, ∑ q, gInv t i p * ((-2 : Real) * ric p q) * gInv t q j) =
          ∑ p, ∑ q, (-2 : Real) *
            (gInv t i p * gInv t j q * ric p q) := by
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      simp only [gInv]
      rw [basisInvMetric_symm (I := I) (g₀ t) x basis q j]
      ring
    have hfactor :
        (∑ p, ∑ q, (-2 : Real) *
            (gInv t i p * gInv t j q * ric p q)) =
          (-2 : Real) *
            (∑ p, ∑ q, gInv t i p * gInv t j q * ric p q) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [Finset.mul_sum]
    simp only [gInvDt]
    rw [hterm, hfactor]
    ring
  have hbase :=
    hasDerivWithinAt_normSq0S_ricciFlow
      (I := I) (s := 2) (u := Set.univ) (t := t)
      g₀ gInv gInvDt ric T Tdt Wdot basis hinvAll hgInv hT hTdot hflow
  have hat := hbase.hasDerivAt (by simp)
  simpa only [movingDiffNorm, movingMetricReact, T, gInv, ric] using hat

/-- The pointwise moving-norm derivative specialized to two genuine
Ricci--DeTurck equations.  The carrier reaction uses
`Q = -(1/2) RD(g₀)`, while the tensor derivative is exactly
`RD(g₁) - RD(g₀)`. -/
theorem movingNorm_rd {x : M} {t : Real}
    (g_bg : SmoothRiemannianMetric I M)
    (g₀ g₁ : Real → SmoothRiemannianMetric I M)
    (hPDE₀ : ∀ X Y : TangentSpace I x,
      HasDerivAt
        (fun r : Real ↦ (g₀ r).inner x X Y)
        (deTurckRicciRHS (I := I) g_bg (g₀ t) x X Y) t)
    (hPDE₁ : ∀ X Y : TangentSpace I x,
      HasDerivAt
        (fun r : Real ↦ (g₁ r).inner x X Y)
        (deTurckRicciRHS (I := I) g_bg (g₁ t) x X Y) t) :
    HasDerivAt
      (fun r : Real ↦ movingDiffNorm (I := I) (M := M) g₀ g₁ r x)
      (movingMetricReact (I := I) (M := M) (g₀ t) x
          ((-1 / 2 : Real) • deTurckRHSField (I := I) g_bg (g₀ t) x)
          (metricDiff02Field (I := I) (g₁ t) (g₀ t) x) +
        2 * inner0S (I := I) (g₀ t) x 2
          (deTurckRHSField (I := I) g_bg (g₁ t) x -
            deTurckRHSField (I := I) g_bg (g₀ t) x)
          (metricDiff02Field (I := I) (g₁ t) (g₀ t) x)) t := by
  apply movingNorm_time (I := I) (M := M) g₀ g₁
  · intro X Y
    convert hPDE₀ X Y using 1
    simp only [Tensor0SSpace.toModel_smul,
      ContinuousMultilinearMap.smul_apply, deTurckRHSField_toModel_apply,
      smul_eq_mul]
    ring
  · intro X Y
    have hsub := (hPDE₁ X Y).sub (hPDE₀ X Y)
    simpa only [metricDiff02_apply, Tensor0SSpace.toModel_sub,
      ContinuousMultilinearMap.sub_apply, deTurckRHSField_toModel_apply] using hsub

/-- Exact first variation of the moving metric-difference energy at an interior
regular time.  The first summand is the pointwise moving-norm derivative and
the second is the moving-volume trace term. -/
theorem movingEnergy_deriv
    (g₀ g₁ : Real → SmoothRiemannianMetric I M) {U : Set Real} {t : Real}
    (hU : IsOpen U) (ht : t ∈ U)
    (h₀ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝒰(Real, Real).prod I) 𝒰(Real, Real) ∞
        (fun p : Real × M ↦
          chartGramMatrix (I := I) (g₀ p.1) x₀ p.2 i j)
        (U ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝒰(Real, Real).prod I) 𝒰(Real, Real) ∞
        (fun p : Real × M ↦
          chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (U ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    HasDerivAt
      (movingDiffEnergy (I := I) (M := M) g₀ g₁)
      (∫ x,
        deriv (fun r : Real ↦
            movingDiffNorm (I := I) (M := M) g₀ g₁ r x) t +
          (1 / 2 : Real) *
            traceTimeDerivMetric (I := I) g₀ t x *
              movingDiffNorm (I := I) (M := M) g₀ g₁ t x
        ∂(riemannianMeasureFamily (I := I) (M := M) g₀ t)) t := by
  have hsmooth := movingNorm_smooth (I := I) (M := M) g₀ g₁ hU h₀ h₁
  simpa only [movingDiffEnergy] using
    first_var_joint (I := I) (M := M) hU ht h₀ hsmooth

/-- Exact interior first variation for two Ricci--DeTurck solutions.  This is
the energy-level form consumed by the boundary estimate: the three displayed
terms are respectively the carrier inverse-metric reaction, the pairing with
the Ricci--DeTurck RHS difference, and the moving-volume reaction. -/
theorem movingEnergy_rd
    (g_bg : SmoothRiemannianMetric I M)
    (g₀ g₁ : Real → SmoothRiemannianMetric I M) {U : Set Real} {t : Real}
    (hU : IsOpen U) (ht : t ∈ U)
    (h₀ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝒰(Real, Real).prod I) 𝒰(Real, Real) ∞
        (fun p : Real × M ↦
          chartGramMatrix (I := I) (g₀ p.1) x₀ p.2 i j)
        (U ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝒰(Real, Real).prod I) 𝒰(Real, Real) ∞
        (fun p : Real × M ↦
          chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (U ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hPDE₀ : ∀ x : M, ∀ X Y : TangentSpace I x,
      HasDerivAt
        (fun r : Real ↦ (g₀ r).inner x X Y)
        (deTurckRicciRHS (I := I) g_bg (g₀ t) x X Y) t)
    (hPDE₁ : ∀ x : M, ∀ X Y : TangentSpace I x,
      HasDerivAt
        (fun r : Real ↦ (g₁ r).inner x X Y)
        (deTurckRicciRHS (I := I) g_bg (g₁ t) x X Y) t) :
    HasDerivAt
      (movingDiffEnergy (I := I) (M := M) g₀ g₁)
      (∫ x,
        movingMetricReact (I := I) (M := M) (g₀ t) x
            ((-1 / 2 : Real) • deTurckRHSField (I := I) g_bg (g₀ t) x)
            (metricDiff02Field (I := I) (g₁ t) (g₀ t) x) +
          2 * inner0S (I := I) (g₀ t) x 2
            (deTurckRHSField (I := I) g_bg (g₁ t) x -
              deTurckRHSField (I := I) g_bg (g₀ t) x)
            (metricDiff02Field (I := I) (g₁ t) (g₀ t) x) +
          (1 / 2 : Real) * traceTimeDerivMetric (I := I) g₀ t x *
            movingDiffNorm (I := I) (M := M) g₀ g₁ t x
        ∂(riemannianMeasureFamily (I := I) (M := M) g₀ t)) t := by
  have hbase := movingEnergy_deriv (I := I) (M := M)
    g₀ g₁ hU ht h₀ h₁
  convert hbase using 1
  apply integral_congr_ae
  filter_upwards with x
  rw [(movingNorm_rd (I := I) (M := M) g_bg g₀ g₁
    (hPDE₀ x) (hPDE₁ x)).deriv]
  ring

/-! ## Grönwall-ready Ricci--DeTurck energy rate -/

/-- The exact scalar rate in `movingEnergy_rd`, packaged so that the analytic
pairing estimate can target one expression and `edgeGronwall_zero` can consume
it without any endpoint derivative. -/
def movingRate
    (g_bg : SmoothRiemannianMetric I M)
    (g₀ g₁ : Real → SmoothRiemannianMetric I M) (t : Real) : Real :=
  ∫ x,
    movingMetricReact (I := I) (M := M) (g₀ t) x
        ((-1 / 2 : Real) • deTurckRHSField (I := I) g_bg (g₀ t) x)
        (metricDiff02Field (I := I) (g₁ t) (g₀ t) x) +
      2 * inner0S (I := I) (g₀ t) x 2
        (deTurckRHSField (I := I) g_bg (g₁ t) x -
          deTurckRHSField (I := I) g_bg (g₀ t) x)
        (metricDiff02Field (I := I) (g₁ t) (g₀ t) x) +
      (1 / 2 : Real) * traceTimeDerivMetric (I := I) g₀ t x *
        movingDiffNorm (I := I) (M := M) g₀ g₁ t x
    ∂(riemannianMeasureFamily (I := I) (M := M) g₀ t)

/-- On the open regular window, the moving difference energy has derivative
`movingRate`. -/
theorem movingEnergy_rate
    (g_bg : SmoothRiemannianMetric I M)
    (g₀ g₁ : Real → SmoothRiemannianMetric I M) {U : Set Real} {t : Real}
    (hU : IsOpen U) (ht : t ∈ U)
    (h₀ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝒶(Real, Real).prod I) 𝒶(Real, Real) ∞
        (fun p : Real × M ↦
          chartGramMatrix (I := I) (g₀ p.1) x₀ p.2 i j)
        (U ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝒶(Real, Real).prod I) 𝒶(Real, Real) ∞
        (fun p : Real × M ↦
          chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (U ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hPDE₀ : ∀ x : M, ∀ X Y : TangentSpace I x,
      HasDerivAt
        (fun r : Real ↦ (g₀ r).inner x X Y)
        (deTurckRicciRHS (I := I) g_bg (g₀ t) x X Y) t)
    (hPDE₁ : ∀ x : M, ∀ X Y : TangentSpace I x,
      HasDerivAt
        (fun r : Real ↦ (g₁ r).inner x X Y)
        (deTurckRicciRHS (I := I) g_bg (g₁ t) x X Y) t) :
    HasDerivAt
      (movingDiffEnergy (I := I) (M := M) g₀ g₁)
      (movingRate (I := I) (M := M) g_bg g₀ g₁ t) t := by
  simpa only [movingRate] using
    movingEnergy_rd (I := I) (M := M) g_bg g₀ g₁
      hU ht h₀ h₁ hPDE₀ hPDE₁

/-- Exact closed-edge Grönwall closure for two Ricci--DeTurck paths.  The
metric paths need only be jointly smooth on `Ioo 0 T` and jointly continuous
on `Icc 0 T`; all time differentiation occurs in the open interval.  Thus the
remaining analytic task is precisely the scalar estimate
`movingRate t ≤ K * movingDiffEnergy t`. -/
theorem movingEnergy_zero
    (g_bg : SmoothRiemannianMetric I M)
    (g₀ g₁ : Real → SmoothRiemannianMetric I M) {T K : Real}
    (hT : 0 < T)
    (h₀s : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝒶(Real, Real).prod I) 𝒶(Real, Real) ∞
        (fun p : Real × M ↦
          chartGramMatrix (I := I) (g₀ p.1) x₀ p.2 i j)
        (Ioo (0 : Real) T ×ˢ
          (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h₁s : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝒶(Real, Real).prod I) 𝒶(Real, Real) ∞
        (fun p : Real × M ↦
          chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ioo (0 : Real) T ×ˢ
          (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h₀c : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContinuousOn
        (fun p : Real × M ↦
          chartGramMatrix (I := I) (g₀ p.1) x₀ p.2 i j)
        (Icc (0 : Real) T ×ˢ
          (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h₁c : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContinuousOn
        (fun p : Real × M ↦
          chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Icc (0 : Real) T ×ˢ
          (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hPDE₀ : ∀ t ∈ Ioo (0 : Real) T, ∀ x : M,
      ∀ X Y : TangentSpace I x,
        HasDerivAt
          (fun r : Real ↦ (g₀ r).inner x X Y)
          (deTurckRicciRHS (I := I) g_bg (g₀ t) x X Y) t)
    (hPDE₁ : ∀ t ∈ Ioo (0 : Real) T, ∀ x : M,
      ∀ X Y : TangentSpace I x,
        HasDerivAt
          (fun r : Real ↦ (g₁ r).inner x X Y)
          (deTurckRicciRHS (I := I) g_bg (g₁ t) x X Y) t)
    (hinit : g₁ 0 = g₀ 0)
    (hbound : ∀ t ∈ Ioo (0 : Real) T,
      movingRate (I := I) (M := M) g_bg g₀ g₁ t ≤
        K * movingDiffEnergy (I := I) (M := M) g₀ g₁ t) :
    ∀ t ∈ Icc (0 : Real) T,
      movingDiffEnergy (I := I) (M := M) g₀ g₁ t = 0 := by
  have hcont : ContinuousOn
      (movingDiffEnergy (I := I) (M := M) g₀ g₁) (Icc (0 : Real) T) :=
    movingEnergy_cont (I := I) (M := M) g₀ g₁ isCompact_Icc h₀c h₁c
  have hzero : movingDiffEnergy (I := I) (M := M) g₀ g₁ 0 = 0 := by
    have hfield : ∀ x : M,
        metricDiff02Field (I := I) (g₁ 0) (g₀ 0) x = 0 := by
      intro x
      rw [hinit]
      apply Tensor0SSpace.toModel_injective
      ext v
      rw [metricDiff02Field_toModel_apply, metricDiff02_apply]
      simp
    unfold movingDiffEnergy movingDiffNorm
    simp [hfield, normSq0S, inner0S, MetricFiberData.inner]
  have hnonneg : ∀ t ∈ Icc (0 : Real) T,
      0 ≤ movingDiffEnergy (I := I) (M := M) g₀ g₁ t := by
    intro t _
    exact integral_nonneg fun x ↦
      normSq0S_nonneg (I := I) (g₀ t) x 2
        (metricDiff02Field (I := I) (g₁ t) (g₀ t) x)
  have hderiv : ∀ t ∈ Ioo (0 : Real) T,
      HasDerivAt
        (movingDiffEnergy (I := I) (M := M) g₀ g₁)
        (movingRate (I := I) (M := M) g_bg g₀ g₁ t) t := by
    intro t ht
    exact movingEnergy_rate (I := I) (M := M) g_bg g₀ g₁
      isOpen_Ioo ht h₀s h₁s (hPDE₀ t ht) (hPDE₁ t ht)
  exact edgeGronwall_zero hT
    (movingDiffEnergy (I := I) (M := M) g₀ g₁)
    (movingRate (I := I) (M := M) g_bg g₀ g₁)
    hcont hzero hnonneg hderiv hbound

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
