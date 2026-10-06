import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TransferIsotopyJets_CX3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TransferIsotopyFinal_S15

set_option autoImplicit false

/-!
# CH12-CX3: all finite orders of the transfer-isotopy displacement

The atlas is fixed before either the smallness threshold or the vector field.
The estimates concern the actual chart expression of `exp_p(t X p)`.
-/

noncomputable section
open scoped Manifold ContDiff Topology ENNReal
open Set Function Bundle Filter Metric

namespace GC.LongTime.Ch12
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The displacement of an actual map in one fixed chart. -/
def chartDisplacement_CX3 (c : M) (Φ : M → M) : E → E :=
  fun x => extChartAt I c (Φ ((extChartAt I c).symm x)) - x

section Complete
variable [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

variable (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)

/-- **H1-D(iii), every finite order.**  The estimate is linear in the input
smallness and uniform in the chart, the point, and `|t| ≤ 2`. -/
theorem transfer_isotopy_Ck_bound_CX3 (A : CkAtlas_S15 I M) (k : ℕ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ X : (∀ p : M, TangentSpace I p),
        ContMDiff I I.tangent ∞ (secBundle_S15 X) →
        ∀ ε : ℝ, 0 ≤ ε → ε ≤ δ → CkSmall_S15 g A X k ε →
          ∀ t : ℝ, |t| ≤ 2 → ∀ i : Fin A.n,
            ∀ x ∈ closedBall (extChartAt I (A.ctr i) (A.ctr i)) (A.rad i),
              scaledExp_S15 g hEnorm X t ((extChartAt I (A.ctr i)).symm x) ∈
                (extChartAt I (A.ctr i)).source ∧
              ∀ j ≤ k, ‖iteratedFDeriv ℝ j
                (chartDisplacement_CX3 (I := I) (A.ctr i) (scaledExp_S15 g hEnorm X t)) x‖ ≤
                  C * ε := by
  classical
  have hlocal := fun i : Fin A.n => exists_graph_jet_bound_CX3
    (isCompact_closedBall (extChartAt I (A.ctr i) (A.ctr i)) (A.rad i))
    (chartDom_isOpen_S15 g hEnorm (A.ctr i))
    (chartPsi_contDiffOn_S15 g hEnorm (A.ctr i))
    (fun x hx => chartDom_zero_S15 g hEnorm (A.ctr i) (A.closedBall_sub i hx)) k
  choose d C hd hC hlocal using hlocal
  obtain ⟨d₀, hd₀, hd₀le⟩ := exists_pos_forall_le_fin_S15 A.n d hd
  let C₀ : ℝ := 1 + ∑ i : Fin A.n, C i
  have hC₀ : 0 < C₀ := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => (hC i).le)
    dsimp [C₀]
    linarith
  refine ⟨d₀ / 2, 2 * C₀, by positivity, by positivity, ?_⟩
  intro X hX ε hε hεδ hsmall t ht i x hx
  have hxT := A.closedBall_sub i hx
  have hcsmooth : ContDiffAt ℝ ∞ (coordSec_S15 (A.ctr i) X) x :=
    (coordSec_contDiffOn_S15 (A.ctr i) X hX).contDiffAt
      ((isOpen_extChartAt_target (A.ctr i)).mem_nhds hxT)
  have hc : ContDiffAt ℝ k (coordSec_S15 (A.ctr i) X) x :=
    hcsmooth.of_le (by exact_mod_cast le_top)
  have htc : ContDiffAt ℝ k (fun y => t • coordSec_S15 (A.ctr i) X y) x := hc.const_smul t
  have hbound : ∀ j ≤ k,
      ‖iteratedFDeriv ℝ j (fun y => t • coordSec_S15 (A.ctr i) X y) x‖ ≤ 2 * ε := by
    intro j hj
    rw [iteratedFDeriv_const_smul_apply' (hc.of_le (by exact_mod_cast hj)), norm_smul,
      Real.norm_eq_abs]
    exact mul_le_mul ht ((hsmall i x hx).2 j hj).le (norm_nonneg _) (by norm_num)
  obtain ⟨hdom, hjet⟩ := hlocal i (fun y => t • coordSec_S15 (A.ctr i) X y) x hx htc
    (2 * ε) (by positivity) (by linarith [hd₀le i]) hbound
  refine ⟨?_, ?_⟩
  · rw [scaledExp_coord_S15 g hEnorm (A.ctr i) X t hxT]
    exact hdom.2
  · intro j hj
    have hout : ContDiffAt ℝ j (chartPsi_S15 g hEnorm (A.ctr i))
        (x, t • coordSec_S15 (A.ctr i) X x) :=
      ((chartPsi_contDiffOn_S15 g hEnorm (A.ctr i)).contDiffAt
        ((chartDom_isOpen_S15 g hEnorm (A.ctr i)).mem_nhds hdom)).of_le
          (by exact_mod_cast le_top)
    have hin : ContDiffAt ℝ j (fun y : E => (y, t • coordSec_S15 (A.ctr i) X y)) x :=
      contDiffAt_id.prodMk (htc.of_le (by exact_mod_cast hj))
    have hψat : ContDiffAt ℝ j
        (fun y => chartPsi_S15 g hEnorm (A.ctr i) (y, t • coordSec_S15 (A.ctr i) X y)) x :=
      ContDiffAt.comp (f := fun y : E => (y, t • coordSec_S15 (A.ctr i) X y))
        (g := chartPsi_S15 g hEnorm (A.ctr i)) x hout hin
    have hdisp : chartDisplacement_CX3 (I := I) (A.ctr i) (scaledExp_S15 g hEnorm X t)
        =ᶠ[𝓝 x] fun y => chartPsi_S15 g hEnorm (A.ctr i)
          (y, t • coordSec_S15 (A.ctr i) X y) - y := by
      filter_upwards [(isOpen_extChartAt_target (A.ctr i)).mem_nhds hxT] with y hy
      rw [chartDisplacement_CX3, scaledExp_ext_S15 g hEnorm (A.ctr i) X t hy]
    have hzero : (fun y => chartPsi_S15 g hEnorm (A.ctr i) (y, (0 : E))) =ᶠ[𝓝 x]
        (fun y : E => y) := by
      filter_upwards [(isOpen_extChartAt_target (A.ctr i)).mem_nhds hxT] with y hy
      exact chartPsi_zero_S15 g hEnorm (A.ctr i) hy
    rw [(hdisp.iteratedFDeriv ℝ j).eq_of_nhds]
    change ‖iteratedFDeriv ℝ j
      ((fun y => chartPsi_S15 g hEnorm (A.ctr i) (y, t • coordSec_S15 (A.ctr i) X y)) -
        (fun y : E => y)) x‖ ≤ _
    rw [iteratedFDeriv_sub_apply (g := fun y : E => y) hψat contDiffAt_id,
      ← (hzero.iteratedFDeriv ℝ j).eq_of_nhds]
    refine (hjet j hj).trans ?_
    have hCi : C i ≤ C₀ := by
      have := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (hC j).le)
        (Finset.mem_univ i)
      dsimp [C₀]
      linarith
    nlinarith

end Complete
end GC.LongTime.Ch12
