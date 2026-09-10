import DifferentialGeometry.Geometry.Comparison.DistanceHessianLowerBound
import DifferentialGeometry.Geometry.Curvature.Naturality.OpenRestriction
import DifferentialGeometry.Geometry.Metric.CompleteMetricExists

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Set Topology
open scoped ContDiff ENNReal Manifold

namespace DifferentialGeometry

open Geometry.Riemannian
open Geometry.Riemannian.Exponential
open Geometry.Riemannian.HopfRinow
open Geometry.Riemannian.Variation
open Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
theorem gradientFun_congr_metric (g g' : SmoothRiemannianMetric I M)
    (f : M → Real) {x : M} (heq : g'.inner x = g.inner x) :
    gradientFun (I := I) g' f x = gradientFun (I := I) g f x := by
  refine SmoothRiemannianMetric.eq_of_inner_eq_gen g (fun ζ => ?_)
  calc
    g.inner x (gradientFun (I := I) g' f x) ζ =
        g'.inner x (gradientFun (I := I) g' f x) ζ := by rw [heq]
    _ = mvfderiv (I := I) f x ζ := inner_gradientFun (I := I) g' f x ζ
    _ = g.inner x (gradientFun (I := I) g f x) ζ :=
      (inner_gradientFun (I := I) g f x ζ).symm

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
theorem chartChristoffel_congr_metric (g g' : SmoothRiemannianMetric I M)
    {W : Set M} (hW : IsOpen W) (heq : ∀ z ∈ W, g'.inner z = g.inner z)
    {x : M} (hx : x ∈ W) (i j k : Fin (Module.finrank Real E)) :
    chartChristoffel (I := I) g' x i j k (extChartAt I x x) =
      chartChristoffel (I := I) g x i j k (extChartAt I x x) := by
  classical
  have hsymm : (extChartAt I x).symm (extChartAt I x x) = x := extChartAt_to_inv x
  have hnhds : (extChartAt I x).symm ⁻¹' W ∈ 𝓝 (extChartAt I x x) := by
    refine (continuousAt_extChartAt_symm x).preimage_mem_nhds ?_
    rw [hsymm]
    exact hW.mem_nhds hx
  have hgram : ∀ l m : Fin (Module.finrank Real E),
      chartGramOnE (I := I) g' x l m =ᶠ[𝓝 (extChartAt I x x)]
        chartGramOnE (I := I) g x l m := by
    intro l m
    filter_upwards [hnhds] with y hy
    change chartGramMatrix (I := I) g' x ((extChartAt I x).symm y) l m =
      chartGramMatrix (I := I) g x ((extChartAt I x).symm y) l m
    rw [chartGramMatrix_apply, chartGramMatrix_apply, heq _ hy]
  have hpartial : ∀ l m n : Fin (Module.finrank Real E),
      partialDeriv (E := E) n (chartGramOnE (I := I) g' x l m) (extChartAt I x x) =
        partialDeriv (E := E) n (chartGramOnE (I := I) g x l m) (extChartAt I x x) := by
    intro l m n
    unfold partialDeriv
    rw [(hgram l m).fderiv_eq]
  have hinv :
      chartInvGramMatrix (I := I) g' x ((extChartAt I x).symm (extChartAt I x x)) =
        chartInvGramMatrix (I := I) g x ((extChartAt I x).symm (extChartAt I x x)) := by
    rw [hsymm]
    unfold chartInvGramMatrix
    congr 1
    ext a b
    rw [chartGramMatrix_apply, chartGramMatrix_apply, heq _ hx]
  rw [chartChristoffel_def, chartChristoffel_def, hinv]
  simp only [hpartial]

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
theorem hessFun_apply_congr_metric (g g' : SmoothRiemannianMetric I M)
    {W : Set M} (hW : IsOpen W) (heq : ∀ z ∈ W, g'.inner z = g.inner z)
    (f : M → Real) {x : M} (hx : x ∈ W) (v w : TangentSpace I x) :
    hessFun (I := I) g' f x v w = hessFun (I := I) g f x v w := by
  classical
  rw [hessFun_apply, hessFun_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [chartHessianTensor_def, chartHessianTensor_def]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [chartChristoffel_congr_metric (I := I) g g' hW heq hx i j k]

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] in
theorem metricRm04StandardAt_congr_metric (g g' : SmoothRiemannianMetric I M)
    {W : Set M} (hW : IsOpen W) (heq : ∀ z ∈ W, g'.inner z = g.inner z)
    {x : M} (hx : x ∈ W) (X Y Z V : TangentSpace I x) :
    metricRm04StandardAt (I := I) (M := M) g' x X Y Z V =
      metricRm04StandardAt (I := I) (M := M) g x X Y Z V := by
  classical
  have _hSCH : SecondCountableTopology H := I.secondCountableTopology
  have _hSCM : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact H M
  have _hLCM : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) I
  let U : TopologicalSpace.Opens M := ⟨W, hW⟩
  have _hLCU : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let _ : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let _ : IsManifold I 1 U :=
    IsManifold.of_le (I := I) (M := U) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let xU : U := ⟨x, hx⟩
  have hres : g'.restrictOpen (I := I) U = g.restrictOpen (I := I) U := by
    refine SmoothRiemannianMetric.ext_inner (fun z v w => ?_)
    rw [SmoothRiemannianMetric.restrictOpen_inner,
      SmoothRiemannianMetric.restrictOpen_inner, heq (z : M) z.2]
  have h1 := Geometry.Curvature.metricRm04StandardAt_restrictOpen (I := I) g' U xU X Y Z V
  have h2 := Geometry.Curvature.metricRm04StandardAt_restrictOpen (I := I) g U xU X Y Z V
  rw [hres] at h1
  have h3 := h1.symm.trans h2
  simp only [mfderiv_subtype_val] at h3
  exact h3

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] in
theorem sectionalBoundedBelowAt_congr_metric (g g' : SmoothRiemannianMetric I M)
    {W : Set M} (hW : IsOpen W) (heq : ∀ z ∈ W, g'.inner z = g.inner z)
    {y : M} (hy : y ∈ W) {K : Real} :
    Geometry.Riemannian.SectionalBoundedBelowAt (I := I) g' y K ↔
      Geometry.Riemannian.SectionalBoundedBelowAt (I := I) g y K := by
  have hinner := heq y hy
  constructor
  · intro h v w
    have hv := h v w
    rwa [hinner, metricRm04StandardAt_congr_metric (I := I) g g' hW heq hy v w w v] at hv
  · intro h v w
    have hv := h v w
    rwa [← hinner, ← metricRm04StandardAt_congr_metric (I := I) g g' hW heq hy v w w v] at hv



attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def metricPathELength (g : SmoothRiemannianMetric I M)
    (γ : Real → M) (a b : Real) : ℝ≥0∞ :=
  letI : RiemannianBundle (fun z : M => TangentSpace I z) := ⟨g.toRiemannianMetric⟩
  Manifold.pathELength I γ a b

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem metricPathELength_eq (g : SmoothRiemannianMetric I M)
    (γ : Real → M) (a b : Real) :
    metricPathELength (I := I) g γ a b =
      ∫⁻ t in Set.Ioo a b, ENNReal.ofReal (Real.sqrt
        (g.inner (γ t) (mfderiv% γ t 1) (mfderiv% γ t 1))) := by
  let _ : RiemannianBundle (fun z : M => TangentSpace I z) := ⟨g.toRiemannianMetric⟩
  change Manifold.pathELength I γ a b = _
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  refine lintegral_congr fun t => ?_
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  congr 2

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem metricPathELength_congr (g g' : SmoothRiemannianMetric I M)
    {γ : Real → M} {a b : Real}
    (h : ∀ t ∈ Set.Ioo a b, g'.inner (γ t) = g.inner (γ t)) :
    metricPathELength (I := I) g' γ a b = metricPathELength (I := I) g γ a b := by
  rw [metricPathELength_eq, metricPathELength_eq]
  refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  rw [h t ht]

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem metricPathELength_mono (g : SmoothRiemannianMetric I M)
    (γ : Real → M) {a b a' b' : Real} (ha : a' ≤ a) (hb : b ≤ b') :
    metricPathELength (I := I) g γ a b ≤ metricPathELength (I := I) g γ a' b' := by
  let _ : RiemannianBundle (fun z : M => TangentSpace I z) := ⟨g.toRiemannianMetric⟩
  exact Manifold.pathELength_mono ha hb

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem edistOf_le_metricPathELength (g : SmoothRiemannianMetric I M)
    {γ : Real → M} {a b : Real} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(Real, Real) I 1 γ (Set.Icc a b)) :
    riemannianEDistOf (I := I) g (γ a) (γ b) ≤
      metricPathELength (I := I) g γ a b := by
  let _ : RiemannianBundle (fun z : M => TangentSpace I z) := ⟨g.toRiemannianMetric⟩
  change Manifold.riemannianEDist I (γ a) (γ b) ≤ Manifold.pathELength I γ a b
  exact Manifold.riemannianEDist_le_pathELength hγ rfl rfl hab

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_lt_of_edistOf_lt (g : SmoothRiemannianMetric I M)
    {x y : M} {r : ℝ≥0∞} (hr : riemannianEDistOf (I := I) g x y < r) :
    ∃ γ : Real → M, γ 0 = x ∧ γ 1 = y ∧
      ContMDiffOn 𝓘(Real, Real) I 1 γ (Set.Icc 0 1) ∧
      metricPathELength (I := I) g γ 0 1 < r := by
  let _ : RiemannianBundle (fun z : M => TangentSpace I z) := ⟨g.toRiemannianMetric⟩
  exact Manifold.exists_lt_of_riemannianEDist_lt hr

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_eq_of_eqOn_ball (g g' : SmoothRiemannianMetric I M)
    {W : Set M} {p : M} {R : Real}
    (hballW : {z : M | riemannianEDistOf (I := I) g p z ≤ ENNReal.ofReal R} ⊆ W)
    (heqW : ∀ z ∈ W, g'.inner z = g.inner z)
    (hle : ∀ (z : M) (v : TangentSpace I z), g.inner z v v ≤ g'.inner z v v)
    {y : M} (hy : riemannianEDistOf (I := I) g p y < ENNReal.ofReal R) :
    riemannianEDistOf (I := I) g' p y = riemannianEDistOf (I := I) g p y := by
  refine le_antisymm ?_ (edistOf_mono (I := I) g g' (fun z v => hle z v) p y)
  by_contra hcon
  obtain ⟨c, hc1, hc2⟩ := exists_between (lt_min (not_le.mp hcon) hy)
  have hcR : c < ENNReal.ofReal R := hc2.trans_le (min_le_right _ _)
  have hcd : c < riemannianEDistOf (I := I) g' p y := hc2.trans_le (min_le_left _ _)
  obtain ⟨γ, hγ0, hγ1, hγC1, hlen⟩ := exists_lt_of_edistOf_lt (I := I) g hc1
  have hmem : ∀ s ∈ Set.Icc (0 : Real) 1, γ s ∈ W := by
    intro s hs
    refine hballW ?_
    change riemannianEDistOf (I := I) g p (γ s) ≤ ENNReal.ofReal R
    have h1 : riemannianEDistOf (I := I) g (γ 0) (γ s) ≤
        metricPathELength (I := I) g γ 0 s :=
      edistOf_le_metricPathELength (I := I) g hs.1
        (hγC1.mono (Set.Icc_subset_Icc le_rfl hs.2))
    have h2 : metricPathELength (I := I) g γ 0 s ≤ metricPathELength (I := I) g γ 0 1 :=
      metricPathELength_mono (I := I) g γ le_rfl hs.2
    rw [hγ0] at h1
    exact ((h1.trans h2).trans hlen.le).trans hcR.le
  have hlen' : metricPathELength (I := I) g' γ 0 1 = metricPathELength (I := I) g γ 0 1 :=
    metricPathELength_congr (I := I) g g'
      (fun t ht => heqW _ (hmem t ⟨ht.1.le, ht.2.le⟩))
  have hbound : riemannianEDistOf (I := I) g' p y ≤
      metricPathELength (I := I) g' γ 0 1 := by
    have h := edistOf_le_metricPathELength (I := I) g' (by norm_num : (0 : Real) ≤ 1) hγC1
    rwa [hγ0, hγ1] at h
  exact absurd ((hbound.trans hlen'.le).trans_lt hlen) (not_lt.mpr hcd.le)



attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem calabiDist_hess_support_on_of_sectional_lower_bound_lt
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {K : Real} (hK : K ≤ 0) {O x : M} {R : Real}
    (hsec : ∀ y : M, riemannianEDist I O y < ENNReal.ofReal R →
      Geometry.Riemannian.SectionalBoundedBelowAt (I := I) g y K)
    (hOx : O ≠ x)
    (hfin : riemannianEDist I O x ≠ (⊤ : ENNReal))
    (hR : (riemannianEDist I O x).toReal < R) :
    let r := (riemannianEDist I O x).toReal
    ∃ rho : M → Real, ∃ U : Set M,
      IsOpen U ∧
      x ∈ U ∧
      ContMDiffOn I 𝓘(Real, Real) ∞ rho U ∧
      rho x = r ∧
      (∀ᶠ y in nhds x, (riemannianEDist I O y).toReal ≤ rho y) ∧
      g.inner x
          (gradientFun (I := I) g rho x)
          (gradientFun (I := I) g rho x) = 1 ∧
      ∀ Y : TangentSpace I x,
        hessFun (I := I) g rho x Y Y ≤
          (2 / r + Real.sqrt (-K)) * g.inner x Y Y := by
  dsimp only
  let r : Real := (riemannianEDist I O x).toReal
  have hdist_ne : riemannianEDist I O x ≠ 0 := by
    intro hzero
    exact hOx (riemannianEDist_eq_zero_imp_eq (I := I) O x hzero)
  have hr : 0 < r := ENNReal.toReal_pos hdist_ne hfin
  have hR0 : 0 < R := hr.trans hR
  have hq2 : Real.sqrt (-K) ^ 2 = -K := Real.sq_sqrt (by linarith)
  have hcoef :
      -(((Module.finrank Real E - 1 : Nat) : Real) * Real.sqrt (-K) ^ 2) =
        ((Module.finrank Real E - 1 : Nat) : Real) * K := by
    rw [hq2]
    ring
  have hRicBall : 0 < Module.finrank Real E - 1 →
      ∀ y ∈ Metric.eball O (ENNReal.ofReal R),
        ∀ w : TangentSpace I y,
          -(((Module.finrank Real E - 1 : Nat) : Real) * Real.sqrt (-K) ^ 2) *
              g.inner y w w ≤ ricciTensor (I := I) g y w w := by
    intro _ y hy w
    rw [hcoef]
    refine Geometry.Riemannian.ricci_lower_of_sectionalBoundedBelowAt (I := I) g y ?_ w
    refine hsec y ?_
    rw [Metric.mem_eball'] at hy
    rwa [IsRiemannianManifold.out (I := I) O y] at hy
  obtain ⟨tail, hreach, _hrho_inf, hrho_x, hupper, _hrho_ev, _hrho_grad,
      hgrad_norm, _hlap⟩ :=
    exists_calabi_support_lt (I := I) g hEnorm (Real.sqrt (-K))
      (Real.sqrt_nonneg _) hRicBall hOx hfin hR
  let rho : M → Real := fun y =>
    tail.initialLength + branchRadius (I := I) g tail.branch y
  have hrad_x :
      branchRadius (I := I) g tail.branch x = tail.terminalLength := by
    calc
      branchRadius (I := I) g tail.branch x =
          branchRadius (I := I) g tail.branch
            (expMapIntrinsic (I := I) g hEnorm tail.splitPoint tail.endpointVector) :=
        congrArg (branchRadius (I := I) g tail.branch) tail.exp_eq.symm
      _ = Real.sqrt (g.inner tail.splitPoint tail.endpointVector tail.endpointVector) :=
        branchRadius_exp (I := I) tail.branch tail.source_mem
      _ = tail.terminalLength := tail.endpointVector_norm
  have hpx_upper :
      riemannianEDist I tail.splitPoint x ≤ ENNReal.ofReal tail.terminalLength := by
    have h := tail.branch.edist_le_radius tail.target_mem
    rw [hrad_x] at h
    exact h
  have hfull : riemannianEDist I O x = ENNReal.ofReal r := by
    dsimp only [r]
    exact (ENNReal.ofReal_toReal hfin).symm
  have hsplit :
      ENNReal.ofReal r =
        ENNReal.ofReal tail.initialLength + ENNReal.ofReal tail.terminalLength := by
    rw [← ENNReal.ofReal_add tail.initialLength_nonneg tail.terminalLength_pos.le, tail.length_sum]
  have hpx_lower :
      ENNReal.ofReal tail.terminalLength ≤ riemannianEDist I tail.splitPoint x := by
    apply (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).mp
    calc
      ENNReal.ofReal tail.initialLength + ENNReal.ofReal tail.terminalLength =
          ENNReal.ofReal r := hsplit.symm
      _ = riemannianEDist I O x := hfull.symm
      _ ≤ riemannianEDist I O tail.splitPoint + riemannianEDist I tail.splitPoint x :=
        riemannianEDist_triangle
      _ = ENNReal.ofReal tail.initialLength + riemannianEDist I tail.splitPoint x := by
        rw [tail.initial_edist]
  have hpx :
      riemannianEDist I tail.splitPoint x = ENNReal.ofReal tail.terminalLength :=
    le_antisymm hpx_upper hpx_lower
  have hu_sq : g.inner tail.splitPoint tail.endpointVector tail.endpointVector = tail.terminalLength ^ 2 := by
    have hsq := Real.sq_sqrt
      (gInner_self_nonneg (I := I) g tail.splitPoint tail.endpointVector)
    rw [tail.endpointVector_norm] at hsq
    exact hsq.symm
  let e : TangentSpace I tail.splitPoint := tail.terminalLength⁻¹ • tail.endpointVector
  have he_unit : g.inner tail.splitPoint e e = 1 := by
    dsimp only [e]
    rw [gInner_smul_self (I := I) g tail.splitPoint, hu_sq]
    field_simp [tail.terminalLength_pos.ne']
  have hscale : tail.terminalLength • e = tail.endpointVector := by
    dsimp only [e]
    rw [smul_smul, mul_inv_cancel₀ tail.terminalLength_pos.ne', one_smul]
  let gamma : Real → M :=
    intrinsicGeodesic (I := I) g hEnorm tail.splitPoint e
  have hend : gamma tail.terminalLength = x := by
    dsimp only [gamma]
    rw [← intrinsicGeodesic_smul (I := I) g hEnorm tail.splitPoint e tail.terminalLength,
      hscale, ← expMapIntrinsic_def]
    exact tail.exp_eq
  have hmin : ∀ eta : Real → M,
      ContMDiffOn 𝓘(Real, Real) I 1 eta (Set.Icc 0 tail.terminalLength) →
      eta 0 = tail.splitPoint → eta tail.terminalLength = gamma tail.terminalLength →
      arcLength (I := I) g gamma 0 tail.terminalLength ≤
        arcLength (I := I) g eta 0 tail.terminalLength := by
    intro eta heta heta0 hetaell
    have heta_end : eta tail.terminalLength = x := hetaell.trans hend
    have heta_nonneg : 0 ≤ arcLength (I := I) g eta 0 tail.terminalLength := by
      unfold arcLength
      exact intervalIntegral.integral_nonneg tail.terminalLength_pos.le
        (fun _ _ => Real.sqrt_nonneg _)
    have hed :
        riemannianEDist I (eta 0) (eta tail.terminalLength) ≤
          ENNReal.ofReal (arcLength (I := I) g eta 0 tail.terminalLength) :=
      Geometry.Riemannian.Geodesic.riemannianEDist_le_arcLength
        (I := I) g tail.terminalLength_pos.le heta
        (fun t _ => hEnorm (eta t) _)
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hed
    have hell_le : tail.terminalLength ≤ arcLength (I := I) g eta 0 tail.terminalLength := by
      rw [heta0, heta_end, hpx, ENNReal.toReal_ofReal tail.terminalLength_pos.le,
        ENNReal.toReal_ofReal heta_nonneg] at hreal
      exact hreal
    dsimp only [gamma]
    rw [arcLength_radial (I := I) g hEnorm tail.splitPoint e,
      he_unit, Real.sqrt_one, sub_zero, mul_one]
    exact hell_le
  have hsrc :
      tangentSpaceModelContinuousLinearEquiv (I := I) tail.splitPoint
          (tail.terminalLength • e) ∈ tail.branch.hom.source := by
    rw [hscale]
    with_unfolding_all exact tail.source_mem
  have hsec_tail : ∀ t ∈ Set.Icc (0 : Real) tail.terminalLength,
      Geometry.Riemannian.SectionalBoundedBelowAt (I := I) g (gamma t) K := by
    intro t ht
    refine hsec (gamma t) ?_
    have hgeo :=
      intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm tail.splitPoint e
        (s := (0 : Real)) (t := t) ht.1
    rw [intrinsicGeodesic_zero (I := I) g hEnorm tail.splitPoint e, he_unit,
      Real.sqrt_one, one_mul, sub_zero] at hgeo
    calc
      riemannianEDist I O (gamma t) ≤
          riemannianEDist I O tail.splitPoint + riemannianEDist I tail.splitPoint (gamma t) :=
        riemannianEDist_triangle
      _ ≤ ENNReal.ofReal tail.initialLength + ENNReal.ofReal t :=
        add_le_add tail.initial_edist.le hgeo
      _ = ENNReal.ofReal (tail.initialLength + t) :=
        (ENNReal.ofReal_add tail.initialLength_nonneg ht.1).symm
      _ < ENNReal.ofReal R := by
        refine (ENNReal.ofReal_lt_ofReal_iff hR0).2 ?_
        have hsplit' := tail.length_sum
        have hrR : r < R := hR
        linarith [ht.2]
  have hend' :
      intrinsicGeodesic (I := I) g hEnorm tail.splitPoint (tail.terminalLength • e) 1 = x := by
    rw [hscale, ← expMapIntrinsic_def]
    exact tail.exp_eq
  have hcomp :=
    Geometry.Riemannian.branchHess_le_of_minimizing_of_sectional_lower_bound
      (I := I) g hEnorm tail.splitPoint e tail.terminalLength K tail.branch hK tail.terminalLength_pos he_unit
        hsrc hmin hsec_tail
  rw [hend'] at hcomp
  obtain ⟨U, hUopen, hxU, hbrU⟩ :=
    branchRadius_open (I := I) tail.branch tail.source_mem
      (Real.sqrt_pos.mp (tail.endpointVector_norm.symm ▸ tail.terminalLength_pos))
  rw [tail.exp_eq] at hxU
  have hhess := hessFun_add_const (I := I) g tail.initialLength hUopen hbrU hxU
  refine ⟨rho, U, hUopen, hxU, contMDiffOn_const.add hbrU,
    hrho_x, hupper, hgrad_norm, ?_⟩
  intro Y
  have htail_bound :
      hessFun (I := I) g rho x Y Y ≤
        Geometry.Riemannian.modelRadialLogDeriv K tail.terminalLength * g.inner x Y Y := by
    change hessFun (I := I) g
        (fun y => tail.initialLength + branchRadius (I := I) g tail.branch y) x Y Y ≤ _
    rw [show hessFun (I := I) g
        (fun y => tail.initialLength + branchRadius (I := I) g tail.branch y) x =
          hessFun (I := I) g (branchRadius (I := I) g tail.branch) x from hhess]
    exact hcomp Y
  refine htail_bound.trans ?_
  have hnorm : 0 ≤ g.inner x Y Y := gInner_self_nonneg (I := I) g x Y
  have hmodel :=
    Geometry.Riemannian.modelRadialLogDeriv_le hK tail.terminalLength_pos
  have hell : 1 / tail.terminalLength ≤ 2 / r := by
    rw [div_le_div_iff₀ tail.terminalLength_pos hr]
    linarith [tail.half_le_terminalLength]
  exact mul_le_mul_of_nonneg_right (by linarith) hnorm



attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem calabiDist_hess_support_on_of_sectional_lower_bound_of_auxiliary_complete_metric
    (g g' : SmoothRiemannianMetric I M) {W : Set M} {p : M} {R : Real}
    (hcomplete : RiemannianMetricComplete (I := I) g')
    (hWopen : IsOpen W)
    (hballW : {z : M | riemannianEDistOf (I := I) g p z ≤ ENNReal.ofReal R} ⊆ W)
    (heqW : ∀ z ∈ W, g'.inner z = g.inner z)
    (hle : ∀ (z : M) (v : TangentSpace I z), g.inner z v v ≤ g'.inner z v v)
    {K : Real} (hK : K ≤ 0)
    (hsec : ∀ y : M, riemannianEDistOf (I := I) g p y ≤ ENNReal.ofReal R →
      Geometry.Riemannian.SectionalBoundedBelowAt (I := I) g y K)
    {x : M} (hpx : p ≠ x)
    (hx : riemannianEDistOf (I := I) g p x < ENNReal.ofReal R) :
    ∃ rho : M → Real, ∃ U : Set M,
      IsOpen U ∧
      x ∈ U ∧
      ContMDiffOn I 𝓘(Real, Real) ∞ rho U ∧
      rho x = (riemannianEDistOf (I := I) g p x).toReal ∧
      (∀ᶠ y in nhds x, (riemannianEDistOf (I := I) g p y).toReal ≤ rho y) ∧
      g.inner x
          (gradientFun (I := I) g rho x)
          (gradientFun (I := I) g rho x) = 1 ∧
      ∀ Y : TangentSpace I x,
        hessFun (I := I) g rho x Y Y ≤
          (2 / rho x + Real.sqrt (-K)) * g.inner x Y Y := by
  classical
  let _ : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : RiemannianBundle (fun y : M => TangentSpace I y) :=
    ⟨g'.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    ⟨⟨g'.inner, g'.contMDiff.continuous, by intro y v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : PseudoEMetricSpace M := inferInstance
  let _ : CompleteSpace M := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) (M := M) g' := by
    intro y v
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g' y v
  have hdist' : ∀ y z : M,
      riemannianEDistOf (I := I) g' y z = riemannianEDist I y z :=
    fun y z => riemannianEDistOf_eq_riemannianEDist (I := I) g' hEnorm y z
  have hxW : x ∈ W := hballW hx.le
  have hmono : ∀ y : M,
      riemannianEDistOf (I := I) g p y ≤ riemannianEDist I p y := by
    intro y
    rw [← hdist' p y]
    exact edistOf_mono (I := I) g g' (fun z v => hle z v) p y
  have hdx : riemannianEDist I p x = riemannianEDistOf (I := I) g p x := by
    rw [← hdist' p x]
    exact riemannianEDistOf_eq_of_eqOn_ball (I := I) g g' hballW heqW hle hx
  have hfin : riemannianEDist I p x ≠ (⊤ : ENNReal) := by
    rw [hdx]
    exact (hx.trans_le le_top).ne
  have hRlt : (riemannianEDist I p x).toReal < R := by
    rw [hdx]
    exact ENNReal.toReal_lt_of_lt_ofReal hx
  have hsec' : ∀ y : M, riemannianEDist I p y < ENNReal.ofReal R →
      Geometry.Riemannian.SectionalBoundedBelowAt (I := I) g' y K := by
    intro y hy
    have hy' : riemannianEDistOf (I := I) g p y ≤ ENNReal.ofReal R :=
      (hmono y).trans hy.le
    exact (sectionalBoundedBelowAt_congr_metric (I := I) g g' hWopen heqW
      (hballW hy')).2 (hsec y hy')
  obtain ⟨rho, U, hUopen, hxU, hrhoOn, hvalue, hupper, hgrad, hhess⟩ :=
    calabiDist_hess_support_on_of_sectional_lower_bound_lt (I := I) (M := M)
      g' hEnorm hK hsec' hpx hfin hRlt
  have hvalue' : rho x = (riemannianEDistOf (I := I) g p x).toReal := by
    rw [hvalue, hdx]
  have hgx : g'.inner x = g.inner x := heqW x hxW
  refine ⟨rho, U ∩ W, hUopen.inter hWopen, ⟨hxU, hxW⟩,
    hrhoOn.mono Set.inter_subset_left, hvalue', ?_, ?_, ?_⟩
  · have hfinite : ∀ᶠ y in nhds x, riemannianEDist I p y ≠ (⊤ : ENNReal) := by
      filter_upwards [Metric.eball_mem_nhds x (by norm_num : (0 : ℝ≥0∞) < 1)] with y hy
      rw [Metric.mem_eball'] at hy
      rw [← IsRiemannianManifold.out (I := I) p y]
      refine ne_top_of_le_ne_top ?_ (edist_triangle p x y)
      refine ENNReal.add_ne_top.mpr ⟨?_, (hy.trans_le le_top).ne⟩
      rw [IsRiemannianManifold.out (I := I) p x]
      exact hfin
    filter_upwards [hupper, hfinite] with y hy1 hy2
    exact (ENNReal.toReal_mono hy2 (hmono y)).trans hy1
  · have hgr : gradientFun (I := I) g' rho x = gradientFun (I := I) g rho x :=
      gradientFun_congr_metric (I := I) g g' rho hgx
    rw [← hgr, ← hgx]
    exact hgrad
  · intro Y
    have hbound := hhess Y
    rw [hessFun_apply_congr_metric (I := I) g g' hWopen heqW rho hxW Y Y] at hbound
    rw [hvalue', ← hdx, ← hgx]
    exact hbound

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem calabiDist_hess_support_on_of_sectional_lower_bound_of_isCompact_closedBall
    (g : SmoothRiemannianMetric I M) {p : M} {R : Real}
    (hball : IsCompact {y : M | riemannianEDistOf (I := I) g p y ≤ ENNReal.ofReal R})
    {K : Real} (hK : K ≤ 0)
    (hsec : ∀ y : M, riemannianEDistOf (I := I) g p y ≤ ENNReal.ofReal R →
      Geometry.Riemannian.SectionalBoundedBelowAt (I := I) g y K)
    {x : M} (hpx : p ≠ x)
    (hx : riemannianEDistOf (I := I) g p x < ENNReal.ofReal R) :
    ∃ rho : M → Real, ∃ U : Set M,
      IsOpen U ∧
      x ∈ U ∧
      ContMDiffOn I 𝓘(Real, Real) ∞ rho U ∧
      rho x = (riemannianEDistOf (I := I) g p x).toReal ∧
      (∀ᶠ y in nhds x, (riemannianEDistOf (I := I) g p y).toReal ≤ rho y) ∧
      g.inner x
          (gradientFun (I := I) g rho x)
          (gradientFun (I := I) g rho x) = 1 ∧
      ∀ Y : TangentSpace I x,
        hessFun (I := I) g rho x Y Y ≤
          (2 / rho x + Real.sqrt (-K)) * g.inner x Y Y := by
  obtain ⟨g', W, hcomplete, hWopen, hballW, heqW, hle⟩ :=
    exists_riemannianMetricComplete_eqOn_of_isCompact (I := I) g hball
  exact calabiDist_hess_support_on_of_sectional_lower_bound_of_auxiliary_complete_metric
    (I := I) g g' hcomplete hWopen hballW heqW hle hK hsec hpx hx

end DifferentialGeometry

end
