import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ScalarNonautUniform

/-!
# Uniform scalar nonautonomous estimates on compact time spans

This file upgrades the local fixed-background metric-difference estimate to a
single prescribed radius on a compact regular-time interval.  It is the first
producer needed to replay the scalar Galerkin construction on a finite interior
time slab without repeatedly choosing unrelated existential lifetimes.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- A compact regular-time interval has one backward radius on which every
frozen-background metric difference is quarter-small and has a common spatial
jet envelope at that frozen time. -/
theorem metricDiff_span
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    {a b : ℝ} (hab : Set.Icc a b ⊆ D.regular) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
      ∀ (T : D.RegularTime), (T : ℝ) ∈ Set.Icc a b →
        ∀ h : ℝ, 0 < h → h ≤ ρ → a ≤ (T : ℝ) - h →
          ∃ B : ℕ → ℝ, (∀ i, 0 ≤ B i) ∧
            ∀ s ∈ Set.Icc (0 : ℝ) h,
              ((T : ℝ) - s ∈ D.regular) ∧
              gFibreOpBound (I := I) (G.metric (T : ℝ))
                (ccTensorBilinSymm (I := I) (G.metric (T : ℝ))
                  (metricDifferenceCcTensor (I := I) (M := M)
                    (G.metric (T : ℝ)) (G.metric ((T : ℝ) - s))))
                (1 / 4 : ℝ) ∧
              ∀ i x,
                riemannianFiberNormSq (I := I) (M := M) (G.metric (T : ℝ))
                    0 (2 + i) x
                    ((iteratedCovGrad (I := I) (G.metric (T : ℝ)) 0 2 i
                      (metricDifferenceCcTensor (I := I) (M := M)
                        (G.metric (T : ℝ))
                        (G.metric ((T : ℝ) - s)))).toSection x) ≤ B i := by
  classical
  obtain ⟨ρ₀, hρ₀, hmetric⟩ :=
    DifferentialGeometry.HCGCompactness.metric_c1_span
      (I := I) G hG hab (by norm_num : (0 : ℝ) < 1 / 4)
  let ρ : ℝ := min 1 ρ₀
  have hρ : 0 < ρ := lt_min one_pos hρ₀
  have hρone : ρ ≤ 1 := min_le_left _ _
  have hρ₀' : ρ ≤ ρ₀ := min_le_right _ _
  refine ⟨ρ, hρ, hρone, ?_⟩
  intro T hT h hh hhρ hleft
  let q : SmoothRiemannianMetric I M := G.metric (T : ℝ)
  let K : Set ℝ := Set.Icc ((T : ℝ) - h) (T : ℝ)
  let P : ℝ → SmoothCcTensor q 0 2 := fun t ↦
    metricDifferenceCcTensor (I := I) (M := M) q (G.metric t)
  have hK : IsCompact K := by
    simpa only [K] using isCompact_Icc
  have hKreg : K ⊆ D.regular := by
    intro t ht
    apply hab
    dsimp only [K] at ht
    exact ⟨hleft.trans ht.1, ht.2.trans hT.2⟩
  have hPjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ ↦ TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun z : M ↦ TensorRSSpace 0 2 I z) p.1
        ((P p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ D.regular) := by
    simpa only [P, q] using metricDiff_joint (I := I) (M := M) G hG q
  obtain ⟨B, hB, hjet⟩ := joint_jet_bdd (I := I) (M := M) q 0 2 P
    hK hKreg hPjoint
  refine ⟨B, hB, ?_⟩
  intro s hs
  have htK : (T : ℝ) - s ∈ K := by
    constructor <;> dsimp only [K] <;> linarith [hs.1, hs.2]
  have hvar : (T : ℝ) - s ∈ Set.Icc a b := by
    exact ⟨hleft.trans htK.1, htK.2.trans hT.2⟩
  have hdist : |((T : ℝ) - s) - (T : ℝ)| ≤ ρ₀ := by
    rw [show ((T : ℝ) - s) - (T : ℝ) = -s by ring, abs_neg,
      abs_of_nonneg hs.1]
    exact hs.2.trans (hhρ.trans hρ₀')
  have hsup := hmetric (T : ℝ) hT ((T : ℝ) - s) hvar hdist
  have hbound : gFibreOpBound (I := I) q
      (ccTensorBilinSymm (I := I) q (P ((T : ℝ) - s))) (1 / 4 : ℝ) := by
    intro y v w
    rw [metricDiff_bilin (I := I) (M := M)]
    have hnorm :
        DifferentialGeometry.HCGCompactness.metricDerivNorm (I := I) 0
          (G.metric ((T : ℝ) - s)) q q y ≤ 1 / 4 := by
      exact (DifferentialGeometry.HCGCompactness.derivNorm_le_sup
        (I := I) (K := Set.univ) isCompact_univ (a := 0) (p := 1)
        (by omega) (G.metric ((T : ℝ) - s)) q q (Set.mem_univ y)).trans
        (by simpa only [q] using hsup)
    have heval := DifferentialGeometry.HCGCompactness.metricDiff_abs_le
      (I := I) (G.metric ((T : ℝ) - s)) q q y v w
    have hfinal :
        |(G.metric ((T : ℝ) - s)).inner y v w - q.inner y v w| ≤
          (1 / 4 : ℝ) * Real.sqrt (q.inner y v v) *
            Real.sqrt (q.inner y w w) :=
      heval.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hnorm (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _))
    simpa only [q, P, ContinuousLinearMap.sub_apply] using hfinal
  refine ⟨hab hvar, ?_, ?_⟩
  · simpa only [q, P] using hbound
  · intro i x
    simpa only [q, P] using hjet i ((T : ℝ) - s) htK x

/-- The metric-difference span radius also gives an order-dependent uniform
jet envelope for the exact scalar-flux coefficient on every admissible
backward interval. -/
theorem scalarFlux_span
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    {a b : ℝ} (hab : Set.Icc a b ⊆ D.regular) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
      ∀ (T : D.RegularTime), (T : ℝ) ∈ Set.Icc a b →
        ∀ h : ℝ, 0 < h → h ≤ ρ → a ≤ (T : ℝ) - h →
          ∃ B : ℕ → ℝ, (∀ i, 0 ≤ B i) ∧
            ∀ s ∈ Set.Icc (0 : ℝ) h, ∀ i x,
              riemannianFiberNormSq (I := I) (M := M) (G.metric (T : ℝ))
                  1 (1 + i) x
                  ((iteratedCovGrad (I := I) (G.metric (T : ℝ)) 1 1 i
                    (scalarFluxCoeff (I := I) (G.metric (T : ℝ))
                      (G.metric ((T : ℝ) - s)))).toSection x) ≤ B i := by
  classical
  obtain ⟨ρ, hρ, hρone, hspan⟩ := metricDiff_span (I := I) (M := M) G hG hab
  refine ⟨ρ, hρ, hρone, ?_⟩
  intro T hT h hh hhρ hleft
  obtain ⟨J, hJ, hdata⟩ := hspan T hT h hh hhρ hleft
  let q : SmoothRiemannianMetric I M := G.metric (T : ℝ)
  let P : ℝ → SmoothCcTensor q 0 2 := fun t ↦
    metricDifferenceCcTensor (I := I) (M := M) q (G.metric t)
  obtain ⟨C, hC, hflux⟩ :=
    scalarFlux_jet_grid (I := I) (M := M) q (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨fun i ↦
    C i * DifferentialGeometry.Combinatorics.antidiagonalTupleGrid J i,
    fun i ↦ mul_nonneg (hC i)
      (DifferentialGeometry.Combinatorics.antidiagonalTupleGrid_nonneg J hJ i), ?_⟩
  intro s hs i x
  have hsdata := hdata s hs
  have htie : ∀ y v w,
      (G.metric ((T : ℝ) - s)).inner y v w =
        q.inner y v w + ccTensorBilinSymm (I := I) q (P ((T : ℝ) - s)) y v w := by
    intro y v w
    rw [metricDiff_bilin (I := I) (M := M)]
    ring
  have hbound : gFibreOpBound (I := I) q
      (ccTensorBilinSymm (I := I) q (P ((T : ℝ) - s))) (1 / 4 : ℝ) := by
    simpa only [q, P] using hsdata.2.1
  have hlocal := hflux (G.metric ((T : ℝ) - s)) (P ((T : ℝ) - s)) htie
    (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    hbound i x
  have hgrid :
      DifferentialGeometry.Combinatorics.antidiagonalTupleGrid
          (fun j ↦ riemannianFiberNormSq (I := I) (M := M) q 0 (2 + j) x
            ((iteratedCovGrad (I := I) q 0 2 j (P ((T : ℝ) - s))).toSection x)) i ≤
        DifferentialGeometry.Combinatorics.antidiagonalTupleGrid J i := by
    rw [DifferentialGeometry.Combinatorics.antidiagonalTupleGrid,
      DifferentialGeometry.Combinatorics.antidiagonalTupleGrid]
    refine Finset.sum_le_sum (fun n _ ↦ Finset.sum_le_sum (fun e _ ↦ ?_))
    exact Finset.prod_le_prod
      (fun m _ ↦ riemannianFiberNormSq_nonneg
        (I := I) (M := M) q 0 (2 + e m) x _)
      (fun m _ ↦ by simpa only [q, P] using hsdata.2.2 (e m) x)
  exact hlocal.trans (mul_le_mul_of_nonneg_left hgrid (hC i))

/-- On every admissible prescribed backward interval, the principal scalar
commutator pairing has support-independent constants at every order. -/
theorem cc_comm_span
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    {a b : ℝ} (hab : Set.Icc a b ⊆ D.regular) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
      ∀ (T : D.RegularTime), (T : ℝ) ∈ Set.Icc a b →
        ∀ h : ℝ, 0 < h → h ≤ ρ → a ≤ (T : ℝ) - h →
          ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
            ∀ s ∈ Set.Icc (0 : ℝ) h,
              ∀ U : SmoothCcTensor (G.metric (T : ℝ)) 0 0,
                |tensorL2Inner (I := I) (M := M) (G.metric (T : ℝ)) 0 0
                    (oneMinusConnLapSmoothIter (I := I) (G.metric (T : ℝ)) 0 0 n U).toFun
                    (appCc (I := I) (M := M) (G.metric (T : ℝ)) 2 0
                      (scalarTraceCoeff (I := I) (G.metric (T : ℝ))
                        (G.metric ((T : ℝ) - s)))
                      (iteratedCovGrad (I := I) (G.metric (T : ℝ)) 0 0 2 U)).toFun +
                  tensorL2Inner (I := I) (M := M) (G.metric (T : ℝ)) 0 (1 + n)
                    (iteratedCovGrad (I := I) (G.metric (T : ℝ)) 0 1 n
                      (covGrad (I := I) (M := M) (G.metric (T : ℝ)) 0 0 U)).toFun
                    (appCcRS (I := I) (M := M) (G.metric (T : ℝ)) 0 (1 + n) (1 + n)
                      (slotExtendIter (I := I) (M := M) (G.metric (T : ℝ)) 1 1 n
                        (scalarFluxCoeff (I := I) (G.metric (T : ℝ))
                          (G.metric ((T : ℝ) - s))))
                      (iteratedCovGrad (I := I) (G.metric (T : ℝ)) 0 1 n
                        (covGrad (I := I) (M := M) (G.metric (T : ℝ)) 0 0 U))).toFun| ≤
                  C * ((∑ j ∈ Finset.range (n + 1),
                      ‖iteratedCovGrad (I := I) (G.metric (T : ℝ)) 0 0 j U‖) *
                    (∑ j ∈ Finset.range (n + 2),
                      ‖iteratedCovGrad (I := I) (G.metric (T : ℝ)) 0 0 j U‖)) := by
  classical
  obtain ⟨ρ, hρ, hρone, hflux⟩ := scalarFlux_span (I := I) (M := M) G hG hab
  refine ⟨ρ, hρ, hρone, ?_⟩
  intro T hT h hh hhρ hleft
  obtain ⟨B, hB_nn, hB⟩ := hflux T hT h hh hhρ hleft
  let q : SmoothRiemannianMetric I M := G.metric (T : ℝ)
  let A : Set ℝ := Set.Icc (0 : ℝ) h
  let C₀ : ℝ → SmoothCcTensor q 1 1 := fun s ↦
    scalarFluxCoeff (I := I) q (G.metric ((T : ℝ) - s))
  let Φ : ℝ → SmoothCcTensor q 1 0 := fun s ↦
    appCcRS (I := I) (M := M) q 1 2 0
      (cometricDoubleTraceField (I := I) q 0)
      (covGrad (I := I) (M := M) q 1 1 (C₀ s))
  have hC₀ : ∀ i s, s ∈ A → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) q 1 (1 + i) x
        ((iteratedCovGrad (I := I) q 1 1 i (C₀ s)).toSection x) ≤ B i := by
    intro i s hs x
    simpa only [q, A, C₀] using hB s hs i x
  obtain ⟨D₀, hD₀_nn, hD₀⟩ :=
    fluxDiv_jet_bdd (I := I) (M := M) q C₀ A B hB_nn hC₀
  have hΦ : ∀ i s, s ∈ A → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) q 1 (0 + i) x
        ((iteratedCovGrad (I := I) q 1 0 i (Φ s)).toSection x) ≤ D₀ i := by
    simpa only [Φ] using hD₀
  obtain ⟨CG, hCG_nn, hCG⟩ :=
    app_jet_of_bdd (I := I) (M := M) q 1 0 Φ A D₀ hD₀_nn hΦ
  intro n
  obtain ⟨Ct, hCt_nn, hCt⟩ :=
    slot_iterL_unif (I := I) (M := M) q 0 n C₀ A B hB_nn hC₀
  obtain ⟨Cd, hCd_nn, hCd⟩ :=
    iterL_pair_jet_of (I := I) (M := M) q 0 n Φ A CG hCG_nn hCG
  refine ⟨Ct + Cd, add_nonneg hCt_nn hCd_nn, ?_⟩
  intro s hs U
  let P : ℝ := tensorL2Inner (I := I) (M := M) q 0 0
    (oneMinusConnLapSmoothIter (I := I) q 0 0 n U).toFun
    (appCc (I := I) (M := M) q 2 0
      (scalarTraceCoeff (I := I) q (G.metric ((T : ℝ) - s)))
      (iteratedCovGrad (I := I) q 0 0 2 U)).toFun
  let G₀ : ℝ := tensorL2Inner (I := I) (M := M) q 0 1
    (covGrad (I := I) (M := M) q 0 0
      (oneMinusConnLapSmoothIter (I := I) q 0 0 n U)).toFun
    (appCc (I := I) (M := M) q 1 1 (C₀ s)
      (covGrad (I := I) (M := M) q 0 0 U)).toFun
  let Htop : ℝ := tensorL2Inner (I := I) (M := M) q 0 (1 + n)
    (iteratedCovGrad (I := I) q 0 1 n
      (covGrad (I := I) (M := M) q 0 0 U)).toFun
    (appCcRS (I := I) (M := M) q 0 (1 + n) (1 + n)
      (slotExtendIter (I := I) (M := M) q 1 1 n (C₀ s))
      (iteratedCovGrad (I := I) q 0 1 n
        (covGrad (I := I) (M := M) q 0 0 U))).toFun
  let R : ℝ := tensorL2Inner (I := I) (M := M) q 0 0
    (oneMinusConnLapSmoothIter (I := I) q 0 0 n U).toFun
    (appCc (I := I) (M := M) q 1 0 (Φ s)
      (covGrad (I := I) (M := M) q 0 0 U)).toFun
  let J : ℝ := (∑ j ∈ Finset.range (n + 1),
      ‖iteratedCovGrad (I := I) q 0 0 j U‖) *
    (∑ j ∈ Finset.range (n + 2),
      ‖iteratedCovGrad (I := I) q 0 0 j U‖)
  have htrans : |G₀ - Htop| ≤ Ct * J := by
    simpa only [G₀, Htop, J] using hCt s hs U
  have hder : |R| ≤ Cd * J := by
    simpa only [R, J] using hCd s hs U
  have hgrad : iteratedCovGrad (I := I) q 0 0 1 U =
      covGrad (I := I) (M := M) q 0 0 U := rfl
  have hsplit : P = -G₀ - R := by
    simpa only [P, G₀, R, C₀, Φ, hgrad,
      scalarFlux_eq_slot (I := I) (M := M)] using
      cc_pair_split (I := I) (M := M) q (G.metric ((T : ℝ) - s))
        (oneMinusConnLapSmoothIter (I := I) q 0 0 n U) U
  have hid : P + Htop = -(G₀ - Htop) - R := by
    linarith
  change |P + Htop| ≤ (Ct + Cd) * J
  rw [hid]
  calc
    |-(G₀ - Htop) - R| = |-(G₀ - Htop) + -R| := by rw [sub_eq_add_neg]
    _ ≤ |-(G₀ - Htop)| + |-R| := abs_add_le _ _
    _ = |G₀ - Htop| + |R| := by rw [abs_neg, abs_neg]
    _ ≤ Ct * J + Cd * J := add_le_add htrans hder
    _ = (Ct + Cd) * J := by ring

/-- On every admissible prescribed backward interval, the traced
connection-difference arm has support-independent adjacent-window constants. -/
theorem cc_conn_span
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    {a b : ℝ} (hab : Set.Icc a b ⊆ D.regular) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
      ∀ (T : D.RegularTime), (T : ℝ) ∈ Set.Icc a b →
        ∀ h : ℝ, 0 < h → h ≤ ρ → a ≤ (T : ℝ) - h →
          (∀ s ∈ Set.Icc (0 : ℝ) h, (T : ℝ) - s ∈ D.regular) ∧
          ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
            ∀ s ∈ Set.Icc (0 : ℝ) h,
              ∀ U : SmoothCcTensor (G.metric (T : ℝ)) 0 0,
                |tensorL2Inner (I := I) (M := M) (G.metric (T : ℝ)) 0 0
                    (oneMinusConnLapSmoothIter (I := I) (G.metric (T : ℝ)) 0 0 n U).toFun
                    (appCc (I := I) (M := M) (G.metric (T : ℝ)) 1 0
                      (connTraceCoeff (I := I) (G.metric (T : ℝ))
                        (G.metric ((T : ℝ) - s)))
                      (iteratedCovGrad (I := I) (G.metric (T : ℝ)) 0 0 1 U)).toFun| ≤
                  C * ((∑ j ∈ Finset.range (n + 1),
                      ‖iteratedCovGrad (I := I) (G.metric (T : ℝ)) 0 0 j U‖) *
                    (∑ j ∈ Finset.range (n + 2),
                      ‖iteratedCovGrad (I := I) (G.metric (T : ℝ)) 0 0 j U‖)) := by
  classical
  refine ⟨1, one_pos, le_rfl, ?_⟩
  intro T hT h hh _ hleft
  let q : SmoothRiemannianMetric I M := G.metric (T : ℝ)
  let K : Set ℝ := Set.Icc ((T : ℝ) - h) (T : ℝ)
  let A : Set ℝ := Set.Icc (0 : ℝ) h
  let Q : ℝ → SmoothCcTensor q 1 0 := fun t ↦
    connTraceCoeff (I := I) q (G.metric t)
  let Φ : ℝ → SmoothCcTensor q 1 0 := fun s ↦ Q ((T : ℝ) - s)
  have hK : IsCompact K := by
    simpa only [K] using isCompact_Icc
  have hKreg : K ⊆ D.regular := by
    intro t ht
    apply hab
    dsimp only [K] at ht
    exact ⟨hleft.trans ht.1, ht.2.trans hT.2⟩
  have hQjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 1 0 ℝ E)) ∞
      (fun p : M × ℝ ↦ TotalSpace.mk' (TensorRSModel 1 0 ℝ E)
        (E := fun z : M ↦ TensorRSSpace 1 0 I z) p.1
        ((Q p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ D.regular) := by
    simpa only [Q, q] using connTrace_joint (I := I) (M := M) G hG q
  obtain ⟨B, hB_nn, hQ⟩ := joint_jet_bdd (I := I) (M := M) q 1 0 Q
    hK hKreg hQjoint
  have hreg : ∀ s ∈ A, (T : ℝ) - s ∈ D.regular := by
    intro s hs
    apply hKreg
    constructor <;> dsimp only [K, A] at hs ⊢ <;> linarith [hs.1, hs.2]
  have hΦ : ∀ i s, s ∈ A → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) q 1 (0 + i) x
        ((iteratedCovGrad (I := I) q 1 0 i (Φ s)).toSection x) ≤ B i := by
    intro i s hs x
    have htK : (T : ℝ) - s ∈ K := by
      constructor <;> dsimp only [K, A] at hs ⊢ <;> linarith [hs.1, hs.2]
    simpa only [Φ] using hQ i ((T : ℝ) - s) htK x
  obtain ⟨CG, hCG_nn, hCG⟩ :=
    app_jet_of_bdd (I := I) (M := M) q 1 0 Φ A B hB_nn hΦ
  refine ⟨?_, fun n ↦ ?_⟩
  · intro s hs
    exact hreg s hs
  · obtain ⟨C, hC_nn, hC⟩ :=
      iterL_pair_jet_of (I := I) (M := M) q 0 n Φ A CG hCG_nn hCG
    refine ⟨C, hC_nn, ?_⟩
    intro s hs U
    simpa only [q, A, Φ, Q] using hC s hs U

/-- A compact regular-time slab has one prescribed backward radius on which
the complete scalar moving-minus-fixed Laplacian pairing has its fixed top
coefficient and support-independent remainder constants. -/
theorem cc_lap_span
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    {a b : ℝ} (hab : Set.Icc a b ⊆ D.regular) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
      ∀ (T : D.RegularTime), (T : ℝ) ∈ Set.Icc a b →
        ∀ h : ℝ, 0 < h → h ≤ ρ → a ≤ (T : ℝ) - h →
          (∀ s ∈ Set.Icc (0 : ℝ) h, (T : ℝ) - s ∈ D.regular) ∧
          ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
            ∀ s ∈ Set.Icc (0 : ℝ) h,
              ∀ U : SmoothCcTensor (G.metric (T : ℝ)) 0 0,
                tensorL2Inner (I := I) (M := M) (G.metric (T : ℝ)) 0 0
                    (oneMinusConnLapSmoothIter (I := I) (G.metric (T : ℝ)) 0 0 n U).toFun
                    (scalarLapDiffCc (I := I) (G.metric (T : ℝ))
                      (G.metric ((T : ℝ) - s)) U).toFun ≤
                  ((1 : ℝ) / 3) *
                      ‖SmoothCcTensor.toL2
                        (castRankCc_db (I := I) (M := M) (G.metric (T : ℝ)) 0
                          (by omega : 0 + (n + 1) = 1 + n)
                          (iteratedCovGrad (I := I) (G.metric (T : ℝ)) 0 0 (n + 1) U))‖ ^ 2 +
                    C * ((∑ j ∈ Finset.range (n + 1),
                        ‖iteratedCovGrad (I := I) (G.metric (T : ℝ)) 0 0 j U‖) *
                      (∑ j ∈ Finset.range (n + 2),
                        ‖iteratedCovGrad (I := I) (G.metric (T : ℝ)) 0 0 j U‖)) := by
  classical
  obtain ⟨ρp, hρp, hρp_one, hp⟩ := cc_comm_span (I := I) (M := M) G hG hab
  obtain ⟨ρc, hρc, _, hc⟩ := cc_conn_span (I := I) (M := M) G hG hab
  obtain ⟨ρm, hρm, _, hm⟩ := metricDiff_span (I := I) (M := M) G hG hab
  let ρ : ℝ := min ρp (min ρc ρm)
  have hρ : 0 < ρ := lt_min hρp (lt_min hρc hρm)
  have hρ_one : ρ ≤ 1 := (min_le_left ρp (min ρc ρm)).trans hρp_one
  have hρp_le : ρ ≤ ρp := min_le_left _ _
  have hρc_le : ρ ≤ ρc :=
    (min_le_right ρp (min ρc ρm)).trans (min_le_left ρc ρm)
  have hρm_le : ρ ≤ ρm :=
    (min_le_right ρp (min ρc ρm)).trans (min_le_right ρc ρm)
  refine ⟨ρ, hρ, hρ_one, ?_⟩
  intro T hT h hh hhρ hleft
  have hp' := hp T hT h hh (hhρ.trans hρp_le) hleft
  obtain ⟨hreg, hc'⟩ := hc T hT h hh (hhρ.trans hρc_le) hleft
  obtain ⟨Jm, hJm, hm'⟩ := hm T hT h hh (hhρ.trans hρm_le) hleft
  refine ⟨hreg, fun n ↦ ?_⟩
  obtain ⟨Cp, hCp_nn, hCp⟩ := hp' n
  obtain ⟨Cc, hCc_nn, hCc⟩ := hc' n
  refine ⟨Cp + Cc, add_nonneg hCp_nn hCc_nn, ?_⟩
  intro s hs U
  let q : SmoothRiemannianMetric I M := G.metric (T : ℝ)
  let g : SmoothRiemannianMetric I M := G.metric ((T : ℝ) - s)
  let K : SmoothCcTensor q 0 2 :=
    metricDifferenceCcTensor (I := I) (M := M) q g
  let k : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ :=
    ccTensorBilinSymm (I := I) q K
  have htie : ∀ y v w, g.inner y v w = q.inner y v w + k y v w := by
    intro y v w
    simp only [k, K]
    rw [metricDiff_bilin (I := I) (M := M)]
    ring
  have hsmall : gFibreOpBound (I := I) q k (1 / 4 : ℝ) := by
    simpa only [q, g, K, k] using (hm' s hs).2.1
  let X : SmoothCcTensor q 0 0 :=
    oneMinusConnLapSmoothIter (I := I) q 0 0 n U
  let A : SmoothCcTensor q 0 0 :=
    appCc (I := I) (M := M) q 2 0 (scalarTraceCoeff (I := I) q g)
      (iteratedCovGrad (I := I) q 0 0 2 U)
  let B : SmoothCcTensor q 0 0 :=
    appCc (I := I) (M := M) q 1 0 (connTraceCoeff (I := I) q g)
      (iteratedCovGrad (I := I) q 0 0 1 U)
  let Atop : SmoothCcTensor q 0 (1 + n) :=
    castRankCc_db (I := I) (M := M) q 0
      (by omega : 0 + (n + 1) = 1 + n)
      (iteratedCovGrad (I := I) q 0 0 (n + 1) U)
  let P : ℝ := tensorL2Inner (I := I) (M := M) q 0 0 X.toFun A.toFun
  let Q : ℝ := tensorL2Inner (I := I) (M := M) q 0 0 X.toFun B.toFun
  let Htop : ℝ := tensorL2Inner (I := I) (M := M) q 0 (1 + n) Atop.toFun
    (appCcRS (I := I) (M := M) q 0 (1 + n) (1 + n)
      (slotExtendIter (I := I) (M := M) q 1 1 n
        (scalarFluxCoeff (I := I) q g)) Atop).toFun
  let Dtop : ℝ := ((1 : ℝ) / 3) * ‖SmoothCcTensor.toL2 Atop‖ ^ 2
  let J : ℝ := (∑ j ∈ Finset.range (n + 1),
      ‖iteratedCovGrad (I := I) q 0 0 j U‖) *
    (∑ j ∈ Finset.range (n + 2),
      ‖iteratedCovGrad (I := I) q 0 0 j U‖)
  have hfront :
      iteratedCovGrad (I := I) q 0 1 n
          (covGrad (I := I) (M := M) q 0 0 U) = Atop := by
    dsimp only [Atop]
    apply eq_of_heq
    exact HEq.trans
      (iteratedCovGrad_covGrad_comm_heq' (I := I) (M := M) q 0 0 n U)
      (castRankCc_db_heq (I := I) (M := M) q 0
        (by omega : 0 + (n + 1) = 1 + n)
        (iteratedCovGrad (I := I) q 0 0 (n + 1) U)).symm
  have hcomm : |P + Htop| ≤ Cp * J := by
    have hcomm' := hCp s hs U
    rw [hfront] at hcomm'
    simpa only [q, g, X, A, P, Htop, J] using hcomm'
  have hlast : -Htop ≤ Dtop := by
    have hlast' := cc_last_pair (I := I) (M := M) q g k htie
      (by norm_num : (1 / 4 : ℝ) < 1) (by norm_num : (0 : ℝ) ≤ 1 / 4)
      hsmall n U
    rw [show ((1 / 4 : ℝ) / (1 - 1 / 4)) = 1 / 3 by norm_num] at hlast'
    simpa only [Htop, Atop, Dtop, scalarFlux_eq_slot (I := I) (M := M)] using hlast'
  have hprincipal : P ≤ Dtop + Cp * J := by
    have hsum : P + Htop ≤ Cp * J :=
      le_trans (le_abs_self (P + Htop)) hcomm
    linarith
  have hconnection : -Q ≤ Cc * J := by
    exact le_trans (neg_le_abs Q)
      (by simpa only [q, g, X, B, Q, J] using hCc s hs U)
  have hsplit :
      tensorL2Inner (I := I) (M := M) q 0 0 X.toFun
          (scalarLapDiffCc (I := I) q g U).toFun = P - Q := by
    rw [scalarLapDiffCc]
    calc
      tensorL2Inner (I := I) (M := M) q 0 0 X.toFun (A - B).toFun =
          (⟪X, A - B⟫_ℝ : ℝ) :=
        (SmoothCcTensor.inner_def (I := I) (M := M) X (A - B)).symm
      _ = (⟪X, A⟫_ℝ : ℝ) - (⟪X, B⟫_ℝ : ℝ) := by rw [inner_sub_right]
      _ = P - Q := by
        rw [SmoothCcTensor.inner_def, SmoothCcTensor.inner_def]
  rw [show
    tensorL2Inner (I := I) (M := M) q 0 0
        (oneMinusConnLapSmoothIter (I := I) q 0 0 n U).toFun
        (scalarLapDiffCc (I := I) q g U).toFun = P - Q by
      simpa only [X] using hsplit]
  change P - Q ≤ Dtop + (Cp + Cc) * J
  rw [sub_eq_add_neg]
  calc
    P + -Q ≤ (Dtop + Cp * J) + Cc * J := add_le_add hprincipal hconnection
    _ = Dtop + (Cp + Cc) * J := by ring

/-- A compact regular-time slab has one prescribed backward radius supporting
the finite scalar `A2` closure at every Sobolev order, uniformly in spectral
support. -/
theorem cc_a2_span
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    {a b : ℝ} (hab : Set.Icc a b ⊆ D.regular) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
      ∀ (T : D.RegularTime), (T : ℝ) ∈ Set.Icc a b →
        ∀ h : ℝ, 0 < h → h ≤ ρ → a ≤ (T : ℝ) - h →
          (∀ s ∈ Set.Icc (0 : ℝ) h, (T : ℝ) - s ∈ D.regular) ∧
          ∀ n : ℕ, ∃ Cmid : ℝ, 0 ≤ Cmid ∧
            ∀ s ∈ Set.Icc (0 : ℝ) h,
              ∀ (F : Finset
                  (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
                    (I := I) (M := M) (G.metric (T : ℝ)) 0 0))
                (v : tensorHs (I := I) (M := M) (G.metric (T : ℝ)) 0 0 0)
                (hv : (Function.support v.coeff).Finite),
                hv.toFinset ⊆ F →
                  2 * ∑ i ∈ F,
                      tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
                        (v.coeff i *
                          tensorL2Coeff (I := I) (M := M)
                            (tensorResolventL2_isCompactOperator
                              (I := I) (M := M) (G.metric (T : ℝ)) 0 0)
                            (SmoothCcTensor.toL2
                              (scalarLapDiffCc (I := I) (G.metric (T : ℝ))
                                (G.metric ((T : ℝ) - s))
                                (tensorHsSmoothRepr (I := I) (M := M) v hv))) i) ≤
                    ((5 : ℝ) / 3) *
                        (∑ i ∈ F,
                          tensorSobolevWeight (I := I) (M := M) i
                            ((n + 1 : ℕ) : ℝ) * (v.coeff i) ^ 2) +
                      Cmid *
                        (∑ i ∈ F,
                          tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
                            (v.coeff i) ^ 2) := by
  classical
  obtain ⟨ρ, hρ, hρone, hlap⟩ := cc_lap_span (I := I) (M := M) G hG hab
  refine ⟨ρ, hρ, hρone, ?_⟩
  intro T hT h hh hhρ hleft
  obtain ⟨hreg, hlap'⟩ := hlap T hT h hh hhρ hleft
  let q : SmoothRiemannianMetric I M := G.metric (T : ℝ)
  let gm : ℝ → SmoothRiemannianMetric I M := fun s ↦ G.metric ((T : ℝ) - s)
  let A : Set ℝ := Set.Icc (0 : ℝ) h
  refine ⟨hreg, fun n ↦ ?_⟩
  obtain ⟨Clap, hClap_nn, hClap⟩ := hlap' n
  have hlap'' : ∀ s, s ∈ A → ∀ U : SmoothCcTensor q 0 0,
      tensorL2Inner (I := I) (M := M) q 0 0
          (oneMinusConnLapSmoothIter (I := I) q 0 0 n U).toFun
          (scalarLapDiffCc (I := I) q (gm s) U).toFun ≤
        ((1 : ℝ) / 3) *
            ‖SmoothCcTensor.toL2
              (castRankCc_db (I := I) (M := M) q 0
                (by omega : 0 + (n + 1) = 1 + n)
                (iteratedCovGrad (I := I) q 0 0 (n + 1) U))‖ ^ 2 +
          Clap * ((∑ j ∈ Finset.range (n + 1),
              ‖iteratedCovGrad (I := I) q 0 0 j U‖) *
            (∑ j ∈ Finset.range (n + 2),
              ‖iteratedCovGrad (I := I) q 0 0 j U‖)) := by
    intro s hs U
    simpa only [q, gm, A] using hClap s hs U
  obtain ⟨Cmid, hCmid_nn, hcore⟩ :=
    finite_lap_unif (I := I) (M := M) q gm A n Clap hClap_nn hlap''
  refine ⟨Cmid, hCmid_nn, ?_⟩
  intro s hs F v hv hsub
  have hcoeff : ∀ i, i ∉ hv.toFinset → v.coeff i = 0 := by
    intro i hi
    by_contra hne
    exact hi (hv.mem_toFinset.mpr (Function.mem_support.mpr hne))
  have hlhs :
      (∑ i ∈ hv.toFinset,
          tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
            (v.coeff i *
              tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 0)
                (SmoothCcTensor.toL2
                  (scalarLapDiffCc (I := I) q (gm s)
                    (tensorHsSmoothRepr (I := I) (M := M) v hv))) i)) =
        ∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
            (v.coeff i *
              tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 0)
                (SmoothCcTensor.toL2
                  (scalarLapDiffCc (I := I) q (gm s)
                    (tensorHsSmoothRepr (I := I) (M := M) v hv))) i) := by
    apply Finset.sum_subset hsub
    intro i hi hiF
    rw [hcoeff i hiF, zero_mul, mul_zero]
  have hhi :
      (∑ i ∈ hv.toFinset,
          tensorSobolevWeight (I := I) (M := M) i ((n + 1 : ℕ) : ℝ) *
            (v.coeff i) ^ 2) =
        ∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i ((n + 1 : ℕ) : ℝ) *
            (v.coeff i) ^ 2 := by
    apply Finset.sum_subset hsub
    intro i hi hiF
    norm_num [hcoeff i hiF]
  have hlo :
      (∑ i ∈ hv.toFinset,
          tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
            (v.coeff i) ^ 2) =
        ∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
            (v.coeff i) ^ 2 := by
    apply Finset.sum_subset hsub
    intro i hi hiF
    norm_num [hcoeff i hiF]
  have hmain := hcore s (by simpa only [A] using hs) v hv
  rw [hlhs, hhi, hlo] at hmain
  simpa only [q, gm, A] using hmain

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
