import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ChartCovNorm_O43
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ChartJets_S80

/-!
# CH12-O43 G2a: S80 `hchart` from the chart-model bound

`[FROZEN] CH12-O43 G2`: the binder `hchart` of `ckErr_of_chartJets_S80` ([FROZEN v2] CH12-S80) is
assembled from (a) the per-chart compact sets `K_i = closedBall_i ∩ symm_i⁻¹ D` of the fixed atlas
(no Lebesgue number is needed: `CkCloseInAtlas_CX3` controls the jets at every chart point over `D`),
(d) `chartCovRev_O43` (covariant fibre norms ≤ coordinate jets, constant uniform in the open set
`O` where `F` is smooth) and (c) the chart-model bound `hmodel` (inline binder, pure chart
calculus: `model₂(F^*h − h) = (I+Du)ᵀ G(y+u) (I+Du) − G(y)`; discharged in G2b).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor.RSTensor DifferentialGeometry.TensorLieDeriv
open DifferentialGeometry.Geometry.Hyperbolic
open Bundle Set Metric
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

/-- The pullback-error field inside `ckErr_S45 H H.metric 1 F` is a smooth section on `O`. -/
theorem errField_contMDiffOn_O43 (H : FiniteVolumeHyperbolicModel.{u})
    {F : H.Carrier → H.Carrier} {O : Set H.Carrier} (hO : IsOpen O)
    (hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ F O) :
    ContMDiffOn (𝓡 3) ((𝓡 3).prod 𝓘(ℝ, Tensor0SModel 2 ℝ (EuclideanSpace ℝ (Fin 3)))) ∞
      (fun p => (⟨p, ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) p) ℝ).symm.toContinuousLinearMap.comp
          ((1 : ℝ) • localPullInner H.metric F p - H.metric.inner p)).uncurryLeft⟩ :
        TotalSpace (Tensor0SModel 2 ℝ (EuclideanSpace ℝ (Fin 3)))
          (fun q => Tensor0SSpace 2 (𝓡 3) q))) O := by
  intro p hp
  have hFp : ContMDiffAt (𝓡 3) (𝓡 3) ∞ F p := hF.contMDiffAt (hO.mem_nhds hp)
  refine ContMDiffAt.contMDiffWithinAt ?_
  rw [contMDiffAt_infty]
  intro n
  have h := contMDiffAt_localPullMetricError_of_contMDiffAt H.metric H.metric (n := n)
    (hFp.of_le (by exact_mod_cast le_top))
  simp only [one_smul]
  exact h

/-- One chart point: `ckErr` of `F` at `q` from the S80-form chartCov (`hr`) and the chart-model
bound (`hmod`) with displacement jets `< δ`. -/
theorem ckErr_le_chart_O43 (H : FiniteVolumeHyperbolicModel.{u}) (c : H.Carrier)
    (K : Set (EuclideanSpace ℝ (Fin 3))) (j k : ℕ) (Cr Cm δ : ℝ) (hCr : 0 ≤ Cr) (hCm : 0 ≤ Cm)
    (hr : ∀ W : Set H.Carrier, IsOpen W → K ⊆ (extChartAt (𝓡 3) c).symm ⁻¹' W →
      ∀ T : (p : H.Carrier) → Tensor0SSpace 2 (𝓡 3) p,
      ContMDiffOn (𝓡 3) ((𝓡 3).prod 𝓘(ℝ, Tensor0SModel 2 ℝ (EuclideanSpace ℝ (Fin 3)))) ∞
        (fun p => (⟨p, T p⟩ : TotalSpace (Tensor0SModel 2 ℝ (EuclideanSpace ℝ (Fin 3)))
          (fun q => Tensor0SSpace 2 (𝓡 3) q))) W →
      ∀ y ∈ K, tensor0SFiberNorm H.metric ((extChartAt (𝓡 3) c).symm y) (2 + j)
          (iteratedMetricCovariantDerivative H.metric 2 T j ((extChartAt (𝓡 3) c).symm y)) ≤
        Cr * ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ i (tensor0SModelInChart 2 c T) y‖)
    (F : H.Carrier → H.Carrier) (O : Set H.Carrier) (hO : IsOpen O)
    (hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ F O) (hKO : K ⊆ (extChartAt (𝓡 3) c).symm ⁻¹' O)
    (q : H.Carrier) (hqs : q ∈ (extChartAt (𝓡 3) c).source) (hxK : extChartAt (𝓡 3) c q ∈ K)
    (hmod : ∀ l ≤ k, ‖iteratedFDeriv ℝ l (tensor0SModelInChart (I := 𝓡 3) 2 c (fun q : H.Carrier =>
            ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) q) ℝ).symm.toContinuousLinearMap.comp
              ((1 : ℝ) • localPullInner H.metric F q - H.metric.inner q)).uncurryLeft))
              (extChartAt (𝓡 3) c q)‖ ≤
      Cm * ∑ l' ∈ Finset.range (k + 2),
        ‖iteratedFDeriv ℝ l' (chartDisplacement_CX3 (I := 𝓡 3) c F) (extChartAt (𝓡 3) c q)‖)
    (hjet : ∀ l ≤ k + 1,
      ‖iteratedFDeriv ℝ l (chartDisplacement_CX3 (I := 𝓡 3) c F) (extChartAt (𝓡 3) c q)‖ < δ)
    (hj : j ≤ k) :
    ckErr_S45 H H.metric 1 F j q ≤ Cr * ((j + 1 : ℝ) * (Cm * ((k + 2 : ℝ) * δ))) := by
  have hxq : (extChartAt (𝓡 3) c).symm (extChartAt (𝓡 3) c q) = q :=
    (extChartAt (𝓡 3) c).left_inv hqs
  have hrev := hr O hO hKO _ (errField_contMDiffOn_O43 H hO hF) _ hxK
  have hck : ckErr_S45 H H.metric 1 F j q =
      tensor0SFiberNorm H.metric ((extChartAt (𝓡 3) c).symm (extChartAt (𝓡 3) c q))
        (2 + j) (iteratedMetricCovariantDerivative H.metric 2 (fun q : H.Carrier =>
          ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) q) ℝ).symm.toContinuousLinearMap.comp
            ((1 : ℝ) • localPullInner H.metric F q - H.metric.inner q)).uncurryLeft) j
          ((extChartAt (𝓡 3) c).symm (extChartAt (𝓡 3) c q))) := by
    rw [hxq]
    rfl
  rw [hck]
  refine hrev.trans (mul_le_mul_of_nonneg_left ?_ hCr)
  have hsum : ∑ l' ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ l' (chartDisplacement_CX3 (I := 𝓡 3) c F)
      (extChartAt (𝓡 3) c q)‖ ≤ (k + 2 : ℝ) * δ := by
    calc _ ≤ ∑ l' ∈ Finset.range (k + 2), δ :=
          Finset.sum_le_sum fun l hl => (hjet l (by rw [Finset.mem_range] at hl; omega)).le
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_ofNat]
  have hmodsum : ∑ l ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ l (tensor0SModelInChart (I := 𝓡 3) 2 c
      (fun q : H.Carrier =>
        ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) q) ℝ).symm.toContinuousLinearMap.comp
          ((1 : ℝ) • localPullInner H.metric F q - H.metric.inner q)).uncurryLeft))
      (extChartAt (𝓡 3) c q)‖ ≤ (j + 1 : ℝ) * (Cm * ((k + 2 : ℝ) * δ)) := by
    calc _ ≤ ∑ l ∈ Finset.range (j + 1), Cm * ((k + 2 : ℝ) * δ) :=
          Finset.sum_le_sum fun l hl =>
            (hmod l (by rw [Finset.mem_range] at hl; omega)).trans
              (mul_le_mul_of_nonneg_left hsum hCm)
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  exact hmodsum

/-- **G2a** (`[FROZEN] CH12-O43 G2`): S80's `hchart` ([FROZEN v2] CH12-S80, verbatim) from the
chart-model bound `hmodel`. -/
theorem hchart_of_model_O43 (H : FiniteVolumeHyperbolicModel.{u})
    (hmodel : ∀ (c : H.Carrier) (K : Set (EuclideanSpace ℝ (Fin 3))) (k : ℕ), IsCompact K →
      K ⊆ (extChartAt (𝓡 3) c).target → ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
        ∀ (F : H.Carrier → H.Carrier) (O : Set H.Carrier), IsOpen O →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ F O → ∀ x ∈ K, (extChartAt (𝓡 3) c).symm x ∈ O →
          F ((extChartAt (𝓡 3) c).symm x) ∈ (extChartAt (𝓡 3) c).source →
          (∀ l ≤ k + 1, ‖iteratedFDeriv ℝ l (chartDisplacement_CX3 (I := 𝓡 3) c F) x‖ < δ) →
          ∀ l ≤ k, ‖iteratedFDeriv ℝ l (tensor0SModelInChart (I := 𝓡 3) 2 c (fun q : H.Carrier =>
            ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) q) ℝ).symm.toContinuousLinearMap.comp
              ((1 : ℝ) • localPullInner H.metric F q - H.metric.inner q)).uncurryLeft)) x‖ ≤
            C * ∑ l' ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ l' (chartDisplacement_CX3 (I := 𝓡 3) c F) x‖) :
    ∀ (A : CkAtlas_S15 (𝓡 3) H.Carrier) (D : Set H.Carrier) (k : ℕ) (ε : ℝ),
      IsCompact D → D ⊆ A.cover → 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ (F : H.Carrier → H.Carrier) (O : Set H.Carrier), IsOpen O → D ⊆ O →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ F O → CkCloseInAtlas_CX3 A D (k + 1) δ F →
          ∀ j : ℕ, j ≤ k → ∀ q ∈ D, ckErr_S45 H H.metric 1 F j q ≤ ε := by
  intro A D k ε hD hDA hε
  let K : Fin A.n → Set (EuclideanSpace ℝ (Fin 3)) := fun i =>
    closedBall (extChartAt (𝓡 3) (A.ctr i) (A.ctr i)) (A.rad i) ∩
      (extChartAt (𝓡 3) (A.ctr i)).symm ⁻¹' D
  have hKt : ∀ i, K i ⊆ (extChartAt (𝓡 3) (A.ctr i)).target :=
    fun i => inter_subset_left.trans (A.closedBall_sub i)
  have hKc : ∀ i, IsCompact (K i) := fun i =>
    (isCompact_closedBall _ _).of_isClosed_subset
      (((continuousOn_extChartAt_symm (A.ctr i)).mono (A.closedBall_sub i)).preimage_isClosed_of_isClosed
        isClosed_closedBall hD.isClosed) inter_subset_left
  choose δm Cm hδm hCm hm using fun i => hmodel (A.ctr i) (K i) k (hKc i) (hKt i)
  choose Cr hCr hr using fun (i : Fin A.n) (j : ℕ) =>
    chartCovRev_O43 H.metric (A.ctr i) (hKc i) (hKt i) 2 j
  set τ : Fin A.n → ℕ → ℝ := fun i j => Cr i j * ((j + 1 : ℝ) * (Cm i * (k + 2 : ℝ))) with hτ
  have hτ0 : ∀ i j, 0 ≤ τ i j := fun i j => by
    have := hCr i j; have := hCm i; positivity
  set Q : ℝ := 1 + ∑ i, ∑ j ∈ Finset.range (k + 1), τ i j with hQ
  have hτQ : ∀ i, ∀ j ≤ k, τ i j ≤ Q := by
    intro i j hj
    have h1 : τ i j ≤ ∑ j' ∈ Finset.range (k + 1), τ i j' :=
      Finset.single_le_sum (f := τ i) (fun j' _ => hτ0 i j') (Finset.mem_range.2 (by omega))
    have h2 : ∑ j' ∈ Finset.range (k + 1), τ i j' ≤ ∑ i', ∑ j' ∈ Finset.range (k + 1), τ i' j' :=
      Finset.single_le_sum (f := fun i' => ∑ j' ∈ Finset.range (k + 1), τ i' j')
        (fun i' _ => Finset.sum_nonneg fun j' _ => hτ0 i' j') (Finset.mem_univ i)
    linarith
  have hQ0 : 0 < Q := by
    have : 0 ≤ ∑ i, ∑ j ∈ Finset.range (k + 1), τ i j :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hτ0 i j
    linarith
  set P : ℝ := ∏ i, min 1 (δm i) with hP
  have hP0 : 0 < P := Finset.prod_pos fun i _ => lt_min one_pos (hδm i)
  have hPle : ∀ i, P ≤ δm i := by
    intro i
    have h1 : P ≤ min 1 (δm i) := by
      rw [hP, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
      exact mul_le_of_le_one_right (le_min zero_le_one (hδm i).le)
        (Finset.prod_le_one₀ (fun j _ => le_min zero_le_one (hδm j).le)
          (fun j _ => min_le_left _ _))
    exact h1.trans (min_le_right _ _)
  set δ := min (ε / Q) P with hδ
  have hδ0 : 0 < δ := lt_min (div_pos hε hQ0) hP0
  refine ⟨δ, hδ0, ?_⟩
  intro F O hO hDO hF hjets j hj q hq
  obtain ⟨i, hqi⟩ := mem_iUnion.1 (hDA hq)
  have hqs : q ∈ (extChartAt (𝓡 3) (A.ctr i)).source := hqi.1
  have hxq : (extChartAt (𝓡 3) (A.ctr i)).symm (extChartAt (𝓡 3) (A.ctr i) q) = q :=
    (extChartAt (𝓡 3) (A.ctr i)).left_inv hqs
  have hxB : extChartAt (𝓡 3) (A.ctr i) q ∈
      closedBall (extChartAt (𝓡 3) (A.ctr i) (A.ctr i)) (A.rad i) := ball_subset_closedBall hqi.2
  have hxD : (extChartAt (𝓡 3) (A.ctr i)).symm (extChartAt (𝓡 3) (A.ctr i) q) ∈ D := by
    rw [hxq]; exact hq
  have hxK : extChartAt (𝓡 3) (A.ctr i) q ∈ K i := ⟨hxB, hxD⟩
  obtain ⟨hsrc, hjet⟩ := hjets i _ hxB hxD
  have hjet' : ∀ l ≤ k + 1, ‖iteratedFDeriv ℝ l (chartDisplacement_CX3 (I := 𝓡 3) (A.ctr i) F)
      (extChartAt (𝓡 3) (A.ctr i) q)‖ < δm i :=
    fun l hl => (hjet l hl).trans_le ((min_le_right _ _).trans (hPle i))
  have hmod := hm i F O hO hF _ hxK (hDO hxD) hsrc hjet'
  have h1 := ckErr_le_chart_O43 H (A.ctr i) (K i) j k (Cr i j) (Cm i) δ (hCr i j) (hCm i)
    (hr i j) F O hO hF (fun y hy => hDO hy.2) q hqs hxK
    (hm i F O hO hF _ hxK (hDO hxD) hsrc hjet') (fun l hl => hjet l hl) hj
  refine h1.trans ?_
  calc Cr i j * ((j + 1 : ℝ) * (Cm i * ((k + 2 : ℝ) * δ))) = τ i j * δ := by rw [hτ]; ring
    _ ≤ Q * (ε / Q) := mul_le_mul (hτQ i j hj) (min_le_left _ _) hδ0.le hQ0.le
    _ = ε := by field_simp

end GC.LongTime.Ch12
