import DifferentialGeometry.Analysis.Heat.Kernel.Basic
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.ScalarPathReconstruct

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Analysis.HeatEquation
open Spectral Sobolev.Chart
open Sobolev (tensorComponentEuclideanChart)
open Parabolic.TensorHeatEquation
open Parabolic.TensorSpectral (eigenvectorSmooth)
open Set
open scoped Manifold ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [CompactSpace M]
local notation "EuclN" => EuclideanSpace Real (Fin (Module.finrank Real E))

private theorem heatKernel_pair_jet_uniform (g : SmoothRiemannianMetric I M)
    (α β : M) (N : Nat) {K L : Set EuclN} (hK : IsCompact K) (hL : IsCompact L)
    (hKsub : K ⊆ chartTargetEuclid (I := I) α)
    (hLsub : L ⊆ chartTargetEuclid (I := I) β) :
    ∃ (C : Real) (p : Nat), 0 ≤ C ∧ ∀ m : Nat, m ≤ N →
      ∀ (i : TensorEigenIdx g 0 0) z, z ∈ K ×ˢ L →
        ‖iteratedFDerivWithin Real m
          (fun q : EuclN × EuclN =>
            tensorComponentEuclideanChart g 0 0 (eigenvectorSmooth g 0 0 i)
              α Fin.elim0 Fin.elim0 q.1 *
            tensorComponentEuclideanChart g 0 0 (eigenvectorSmooth g 0 0 i)
              β Fin.elim0 Fin.elim0 q.2)
          (chartTargetEuclid (I := I) α ×ˢ chartTargetEuclid (I := I) β) z‖ ≤
          C * (1 + TensorEigenIdx.lambda i) ^ p := by
  obtain ⟨Cα, pα, hCα, hα⟩ := scalar_jet_uniform g α N hK hKsub
  obtain ⟨Cβ, pβ, hCβ, hβ⟩ := scalar_jet_uniform g β N hL hLsub
  let Oα := chartTargetEuclid (I := I) α
  let Oβ := chartTargetEuclid (I := I) β
  have hOα : IsOpen Oα := chartTargetEuclid_isOpen α
  have hOβ : IsOpen Oβ := chartTargetEuclid_isOpen β
  let ψα := fun i : TensorEigenIdx g 0 0 =>
    tensorComponentEuclideanChart g 0 0 (eigenvectorSmooth g 0 0 i) α Fin.elim0 Fin.elim0
  let ψβ := fun i : TensorEigenIdx g 0 0 =>
    tensorComponentEuclideanChart g 0 0 (eigenvectorSmooth g 0 0 i) β Fin.elim0 Fin.elim0
  have hψα (i : TensorEigenIdx g 0 0) : ContDiffOn Real ∞ (ψα i) Oα :=
    Sobolev.rawPullR_contDiffOn g 0 0 (eigenvectorSmooth g 0 0 i) α Fin.elim0 Fin.elim0
  have hψβ (i : TensorEigenIdx g 0 0) : ContDiffOn Real ∞ (ψβ i) Oβ :=
    Sobolev.rawPullR_contDiffOn g 0 0 (eigenvectorSmooth g 0 0 i) β Fin.elim0 Fin.elim0
  refine ⟨2 ^ N * Cα * Cβ, pα + pβ, by positivity, ?_⟩
  intro m hm i z hz
  have hzO : z ∈ Oα ×ˢ Oβ := ⟨hKsub hz.1, hLsub hz.2⟩
  have hfst : ContDiffOn Real ∞ (fun q : EuclN × EuclN => ψα i q.1) (Oα ×ˢ Oβ) :=
    (hψα i).comp contDiffOn_fst (fun q hq => hq.1)
  have hsnd : ContDiffOn Real ∞ (fun q : EuclN × EuclN => ψβ i q.2) (Oα ×ˢ Oβ) :=
    (hψβ i).comp contDiffOn_snd (fun q hq => hq.2)
  have hleft (j : Nat) (hj : j ≤ N) :
      ‖iteratedFDerivWithin Real j (fun q : EuclN × EuclN => ψα i q.1) (Oα ×ˢ Oβ) z‖ ≤
        Cα * (1 + TensorEigenIdx.lambda i) ^ pα := by
    let F : (EuclN × EuclN) →L[Real] EuclN := ContinuousLinearMap.fst Real EuclN EuclN
    have hpre : IsOpen (F ⁻¹' Oα) := hOα.preimage F.continuous
    have heq := F.iteratedFDerivWithin_comp_right (hψα i) hOα.uniqueDiffOn
      hpre.uniqueDiffOn hzO.1 (i := j) (by exact_mod_cast le_top)
    rw [iteratedFDerivWithin_of_isOpen j (hOα.prod hOβ) hzO]
    rw [iteratedFDerivWithin_of_isOpen j hpre hzO.1] at heq
    change iteratedFDeriv Real j (fun q : EuclN × EuclN => ψα i q.1) z = _ at heq
    rw [heq]
    refine ((ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_).trans
      (hα j hj i z.1 hz.1)
    have hprod : (∏ _j : Fin j, ‖F‖) ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg F) (fun _ _ => ContinuousLinearMap.norm_fst_le ..)
    exact mul_le_of_le_one_right (norm_nonneg _) hprod
  have hright (j : Nat) (hj : j ≤ N) :
      ‖iteratedFDerivWithin Real j (fun q : EuclN × EuclN => ψβ i q.2) (Oα ×ˢ Oβ) z‖ ≤
        Cβ * (1 + TensorEigenIdx.lambda i) ^ pβ := by
    let F : (EuclN × EuclN) →L[Real] EuclN := ContinuousLinearMap.snd Real EuclN EuclN
    have hpre : IsOpen (F ⁻¹' Oβ) := hOβ.preimage F.continuous
    have heq := F.iteratedFDerivWithin_comp_right (hψβ i) hOβ.uniqueDiffOn
      hpre.uniqueDiffOn hzO.2 (i := j) (by exact_mod_cast le_top)
    rw [iteratedFDerivWithin_of_isOpen j (hOα.prod hOβ) hzO]
    rw [iteratedFDerivWithin_of_isOpen j hpre hzO.2] at heq
    change iteratedFDeriv Real j (fun q : EuclN × EuclN => ψβ i q.2) z = _ at heq
    rw [heq]
    refine ((ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_).trans
      (hβ j hj i z.2 hz.2)
    have hprod : (∏ _j : Fin j, ‖F‖) ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg F) (fun _ _ => ContinuousLinearMap.norm_snd_le ..)
    exact mul_le_of_le_one_right (norm_nonneg _) hprod
  have hbase : 0 ≤ 1 + TensorEigenIdx.lambda i := by
    linarith [tensor_lambda_nonneg (I := I) (M := M) i]
  have hle := norm_iteratedFDerivWithin_mul_le hfst hsnd (hOα.prod hOβ).uniqueDiffOn hzO
    (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤))
  refine hle.trans ?_
  calc
    _ ≤ ∑ j ∈ Finset.range (m + 1), (m.choose j : Real) *
        ((Cα * (1 + TensorEigenIdx.lambda i) ^ pα) *
          (Cβ * (1 + TensorEigenIdx.lambda i) ^ pβ)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hprod := mul_le_mul (hleft j (hjm.trans hm))
        (hright (m - j) ((Nat.sub_le m j).trans hm))
        (norm_nonneg _) (mul_nonneg hCα (pow_nonneg hbase _))
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod
        (Nat.cast_nonneg (m.choose j))
    _ = 2 ^ m * (Cα * Cβ) * (1 + TensorEigenIdx.lambda i) ^ (pα + pβ) := by
      rw [← Finset.sum_mul]
      have hsum : (∑ j ∈ Finset.range (m + 1), (m.choose j : Real)) = 2 ^ m := by
        exact_mod_cast Nat.sum_range_choose m
      rw [hsum, pow_add]
      ring
    _ ≤ _ := by
      simp only [mul_assoc]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 2) hm)
        (mul_nonneg hCα (mul_nonneg hCβ (pow_nonneg hbase _)))

private theorem heatKernel_time_deriv_majorant (g : SmoothRiemannianMetric I M)
    {a : Real} (ha : 0 < a) (j m : Nat) :
    ∃ C : TensorEigenIdx g 0 0 → Real, Summable C ∧ ∀ i t, a ≤ t →
      tensorSobolevWeight i (m : Real) *
        (iteratedDeriv j (fun s => Real.exp (-TensorEigenIdx.lambda i * s)) t) ^ 2 ≤ C i := by
  have hsum := summable_weighted_heat_trace (scalar_eigen_tail g)
    (m + 2 * j : Nat) (by positivity) ha
  refine ⟨fun i => tensorSobolevWeight i (m + 2 * j : Nat) *
    Real.exp (-(2 * TensorEigenIdx.lambda i * a)), hsum, ?_⟩
  intro i t hat
  have hnonneg := tensor_lambda_nonneg (I := I) (M := M) i
  have hbase : 0 ≤ 1 + TensorEigenIdx.lambda i := by linarith
  have hpow : ((-TensorEigenIdx.lambda i) ^ j) ^ 2 =
      TensorEigenIdx.lambda i ^ (2 * j) := by
    rw [← pow_mul, Nat.mul_comm j 2, pow_mul, neg_sq, ← pow_mul]
  have hexp : (Real.exp (-TensorEigenIdx.lambda i * t)) ^ 2 =
      Real.exp (-(2 * TensorEigenIdx.lambda i * t)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [iteratedDeriv_exp_const_mul]
  dsimp only
  rw [mul_pow, hpow, hexp]
  have hpower : TensorEigenIdx.lambda i ^ (2 * j) ≤
      (1 + TensorEigenIdx.lambda i) ^ (2 * j) :=
    pow_le_pow_left₀ hnonneg (by linarith) _
  have htime : Real.exp (-(2 * TensorEigenIdx.lambda i * t)) ≤
      Real.exp (-(2 * TensorEigenIdx.lambda i * a)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  simp only [tensorSobolevWeight, Real.rpow_natCast]
  calc
    _ ≤ (1 + TensorEigenIdx.lambda i) ^ m *
        ((1 + TensorEigenIdx.lambda i) ^ (2 * j) *
          Real.exp (-(2 * TensorEigenIdx.lambda i * a))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hpower htime (Real.exp_pos _).le (pow_nonneg hbase _))
        (pow_nonneg hbase _)
    _ = _ := by rw [← mul_assoc, ← pow_add]


private theorem heatKernel_chart_contDiffOn (g : SmoothRiemannianMetric I M)
    {a b : Real} (ha : 0 < a) (hab : a < b) (α β : M) (N : Nat)
    {K L : Set EuclN} (hK : IsCompact K) (hL : IsCompact L)
    (hKuniq : UniqueDiffOn Real K) (hLuniq : UniqueDiffOn Real L)
    (hKconv : Convex Real K) (hLconv : Convex Real L)
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKsub : K ⊆ chartTargetEuclid (I := I) α)
    (hLsub : L ⊆ chartTargetEuclid (I := I) β) :
    ContDiffOn Real (N : Nat)
      (fun q : Real × (EuclN × EuclN) =>
        ∑' i : TensorEigenIdx g 0 0,
          Real.exp (-TensorEigenIdx.lambda i * q.1) *
            (tensorComponentEuclideanChart g 0 0 (eigenvectorSmooth g 0 0 i)
              α Fin.elim0 Fin.elim0 q.2.1 *
            tensorComponentEuclideanChart g 0 0 (eigenvectorSmooth g 0 0 i)
              β Fin.elim0 Fin.elim0 q.2.2))
      (Icc a b ×ˢ (K ×ˢ L)) := by
  let Oα := chartTargetEuclid (I := I) α
  let Oβ := chartTargetEuclid (I := I) β
  let ψ := fun (i : TensorEigenIdx g 0 0) (z : EuclN × EuclN) =>
    tensorComponentEuclideanChart g 0 0 (eigenvectorSmooth g 0 0 i)
      α Fin.elim0 Fin.elim0 z.1 *
    tensorComponentEuclideanChart g 0 0 (eigenvectorSmooth g 0 0 i)
      β Fin.elim0 Fin.elim0 z.2
  let c := fun (i : TensorEigenIdx g 0 0) (t : Real) => Real.exp (-TensorEigenIdx.lambda i * t)
  have hψ (i : TensorEigenIdx g 0 0) : ContDiffOn Real ∞ (ψ i) (Oα ×ˢ Oβ) :=
    ((Sobolev.rawPullR_contDiffOn g 0 0 (eigenvectorSmooth g 0 0 i)
      α Fin.elim0 Fin.elim0).comp contDiffOn_fst (fun z hz => hz.1)).mul
      ((Sobolev.rawPullR_contDiffOn g 0 0 (eigenvectorSmooth g 0 0 i)
        β Fin.elim0 Fin.elim0).comp contDiffOn_snd (fun z hz => hz.2))
  have hc (i : TensorEigenIdx g 0 0) : ContDiff Real ∞ (c i) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  obtain ⟨Csp, pSp, hCsp, hsp⟩ := heatKernel_pair_jet_uniform g α β N hK hL hKsub hLsub
  have hmajor (k : Nat) : ∃ v : TensorEigenIdx g 0 0 → Real, k ≤ N → Summable v ∧
      ∀ i q, q ∈ Icc a b ×ˢ (K ×ˢ L) →
        ‖iteratedFDerivWithin Real k
          (fun z : Real × (EuclN × EuclN) => c i z.1 * ψ i z.2)
          (Icc a b ×ˢ (K ×ˢ L)) q‖ ≤ v i := by
    by_cases hk : k ≤ N
    · obtain ⟨v, hv, hbound⟩ := prodMode_majorant g (scalar_eigen_tail g) hab k c
        isOpen_univ (subset_univ _) (fun i => (hc i).contDiffOn.of_le (by exact_mod_cast le_top))
        (fun j _ m => by
          obtain ⟨C, hC, hbound⟩ := heatKernel_time_deriv_majorant g ha j m
          exact ⟨C, hC, fun i t ht => hbound i t ht.1⟩)
        ψ ((chartTargetEuclid_isOpen α).prod (chartTargetEuclid_isOpen β)) hψ
        (hKuniq.prod hLuniq) (prod_mono hKsub hLsub) Csp pSp hCsp
        (fun m hm i z hz => hsp m (hm.trans hk) i z hz)
      exact ⟨v, fun _ => ⟨hv, hbound⟩⟩
    · exact ⟨fun _ => 0, fun h => absurd h hk⟩
  choose v hv using hmajor
  have hmode (i : TensorEigenIdx g 0 0) :
      ContDiffOn Real (N : Nat) (fun z : Real × (EuclN × EuclN) => c i z.1 * ψ i z.2)
        (Icc a b ×ˢ (K ×ˢ L)) := by
    exact ((hc i).contDiffOn.comp contDiffOn_fst (mapsTo_univ _ _)).mul
      ((hψ i).comp contDiffOn_snd (fun z hz => ⟨hKsub hz.2.1, hLsub hz.2.2⟩)) |>.of_le
        (by exact_mod_cast le_top)
  obtain ⟨x, hx⟩ := hKne
  obtain ⟨y, hy⟩ := hLne
  have hpoint : (a, (x, y)) ∈ Icc a b ×ˢ (K ×ˢ L) := ⟨⟨le_rfl, hab.le⟩, hx, hy⟩
  exact DifferentialGeometry.Analysis.contDiffOn_tsum
    ((uniqueDiffOn_Icc hab).prod (hKuniq.prod hLuniq))
    (convex_Icc a b |>.prod (hKconv.prod hLconv)) hmode
    (fun k hk => (hv k (by exact_mod_cast hk)).1)
    (fun k i q hq hk => (hv k (by exact_mod_cast hk)).2 i q hq)
    hpoint


theorem contMDiffOn_heatKernel (g : SmoothRiemannianMetric I M) :
    ContMDiffOn (𝓘(Real, Real).prod (I.prod I)) 𝓘(Real, Real) ∞
      (fun q : Real × (M × M) => heatKernel g q.1 q.2.1 q.2.2) (Ioi 0 ×ˢ univ) := by
  rw [contMDiffOn_infty]
  intro N q hq
  have ht : 0 < q.1 := hq.1
  let α := q.2.1
  let β := q.2.2
  let x : EuclN := toEuclidean (E := E) (extChartAt I α α)
  let y : EuclN := toEuclidean (E := E) (extChartAt I β β)
  have hxO : x ∈ chartTargetEuclid (I := I) α :=
    Parabolic.TensorSpectral.toEuclidean_extChartAt_mem_chartTargetEuclid α (mem_chart_source H α)
  have hyO : y ∈ chartTargetEuclid (I := I) β :=
    Parabolic.TensorSpectral.toEuclidean_extChartAt_mem_chartTargetEuclid β (mem_chart_source H β)
  obtain ⟨rx, hrx, hxball⟩ := Metric.isOpen_iff.mp (chartTargetEuclid_isOpen (I := I) α) x hxO
  obtain ⟨ry, hry, hyball⟩ := Metric.isOpen_iff.mp (chartTargetEuclid_isOpen (I := I) β) y hyO
  let K := Metric.closedBall x (rx / 2)
  let L := Metric.closedBall y (ry / 2)
  have hKsub : K ⊆ chartTargetEuclid (I := I) α := by
    intro z hz
    apply hxball
    rw [Metric.mem_ball]
    have h := Metric.mem_closedBall.mp hz
    linarith
  have hLsub : L ⊆ chartTargetEuclid (I := I) β := by
    intro z hz
    apply hyball
    rw [Metric.mem_ball]
    have h := Metric.mem_closedBall.mp hz
    linarith
  have hKint : (interior K).Nonempty := by
    rw [show interior K = Metric.ball x (rx / 2) by
      exact interior_closedBall x (ne_of_gt (half_pos hrx))]
    exact ⟨x, Metric.mem_ball_self (half_pos hrx)⟩
  have hLint : (interior L).Nonempty := by
    rw [show interior L = Metric.ball y (ry / 2) by
      exact interior_closedBall y (ne_of_gt (half_pos hry))]
    exact ⟨y, Metric.mem_ball_self (half_pos hry)⟩
  have hab : q.1 / 2 < q.1 + 1 := by linarith
  let G : Real × (EuclN × EuclN) → Real := fun z =>
    ∑' i : TensorEigenIdx g 0 0, Real.exp (-TensorEigenIdx.lambda i * z.1) *
      (tensorComponentEuclideanChart g 0 0 (eigenvectorSmooth g 0 0 i)
        α Fin.elim0 Fin.elim0 z.2.1 *
      tensorComponentEuclideanChart g 0 0 (eigenvectorSmooth g 0 0 i)
        β Fin.elim0 Fin.elim0 z.2.2)
  have hG : ContDiffOn Real (N : Nat) G (Icc (q.1 / 2) (q.1 + 1) ×ˢ (K ×ˢ L)) :=
    heatKernel_chart_contDiffOn g (half_pos ht) hab α β N
      (isCompact_closedBall x (rx / 2)) (isCompact_closedBall y (ry / 2))
      (uniqueDiffOn_convex (convex_closedBall x (rx / 2)) hKint)
      (uniqueDiffOn_convex (convex_closedBall y (ry / 2)) hLint)
      (convex_closedBall x (rx / 2)) (convex_closedBall y (ry / 2))
      ⟨x, Metric.mem_closedBall_self (half_pos hrx).le⟩
      ⟨y, Metric.mem_closedBall_self (half_pos hry).le⟩ hKsub hLsub
  have hGa : ContDiffAt Real (N : Nat) G (q.1, (x, y)) :=
    hG.contDiffAt (prod_mem_nhds
      (Icc_mem_nhds (half_lt_self ht) (by linarith : q.1 < q.1 + 1))
      (prod_mem_nhds (Metric.closedBall_mem_nhds x (half_pos hrx))
        (Metric.closedBall_mem_nhds y (half_pos hry))))
  let F : Real × (M × M) → Real × (EuclN × EuclN) := fun z =>
    (z.1, (toEuclidean (E := E) (extChartAt I α z.2.1),
      toEuclidean (E := E) (extChartAt I β z.2.2)))
  have hα : ContMDiffAt I 𝓘(Real, EuclN) ∞
      (fun z => toEuclidean (E := E) (extChartAt I α z)) α :=
    (toEuclidean (E := E)).toContinuousLinearMap.contMDiff.contMDiffAt.comp α
      (contMDiffAt_extChartAt (I := I))
  have hβ : ContMDiffAt I 𝓘(Real, EuclN) ∞
      (fun z => toEuclidean (E := E) (extChartAt I β z)) β :=
    (toEuclidean (E := E)).toContinuousLinearMap.contMDiff.contMDiffAt.comp β
      (contMDiffAt_extChartAt (I := I))
  have hF : ContMDiffAt (𝓘(Real, Real).prod (I.prod I))
      𝓘(Real, Real × (EuclN × EuclN)) (N : Nat) F q :=
    (contMDiffAt_fst.prodMk_space
      ((hα.comp q contMDiffAt_snd.fst).prodMk_space
        (hβ.comp q contMDiffAt_snd.snd))).of_le (by exact_mod_cast le_top)
  have hcomp : ContMDiffAt (𝓘(Real, Real).prod (I.prod I)) 𝓘(Real, Real) (N : Nat) (G ∘ F) q :=
    hGa.comp_contMDiffAt (f := F) (x := q) hF
  have hEq : (fun z : Real × (M × M) => heatKernel g z.1 z.2.1 z.2.2) =ᶠ[𝓝 q] G ∘ F := by
    have hnx := (continuous_snd.fst.tendsto q)
      ((chartAt H α).open_source.mem_nhds (mem_chart_source H α))
    have hny := (continuous_snd.snd.tendsto q)
      ((chartAt H β).open_source.mem_nhds (mem_chart_source H β))
    filter_upwards [hnx, hny] with z hx hy
    have hchart (γ w : M) (hw : w ∈ (chartAt H γ).source) (i : TensorEigenIdx g 0 0) :
        tensorComponentEuclideanChart g 0 0 (eigenvectorSmooth g 0 0 i) γ Fin.elim0 Fin.elim0
          (toEuclidean (E := E) (extChartAt I γ w)) = (scalarEigenFunction g i).toFun w := by
      have h := scalarMode_eq g (fun _ _ => 1) γ i (t := 0)
        (Parabolic.TensorSpectral.toEuclidean_extChartAt_mem_chartTargetEuclid γ hw)
      dsimp only [scalarMode, one_mul] at h
      rw [Parabolic.TensorSpectral.symm_toEuclidean_symm_toEuclidean_extChartAt γ hw] at h
      simpa only [one_mul, scalarEigenFunction] using h
    change (∑' i : TensorEigenIdx g 0 0,
      Real.exp (-TensorEigenIdx.lambda i * z.1) * (scalarEigenFunction g i).toFun z.2.1 *
        (scalarEigenFunction g i).toFun z.2.2) = _
    dsimp only [Function.comp_apply, G, F]
    apply tsum_congr
    intro i
    rw [hchart α z.2.1 hx i, hchart β z.2.2 hy i]
    ring
  exact (hcomp.congr_of_eventuallyEq hEq).contMDiffWithinAt

end DifferentialGeometry.Analysis.HeatEquation
