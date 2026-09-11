import DifferentialGeometry.Geometry.Comparison.Toponogov.SharpDistanceSupport

set_option autoImplicit false
noncomputable section
open Bundle Filter Manifold Set Topology
open scoped ContDiff ENNReal Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem calabiDist_sharp_hess_support_on_minimizing_lens
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {O x : M}
    (hsec : ∀ y : M, riemannianEDist I O y + riemannianEDist I y x =
        riemannianEDist I O x →
      metricRm04At (I := I) g y ∈ tensor04SectionalNonnegativeCone (I := I) (M := M))
    (hOx : O ≠ x) (hfin : riemannianEDist I O x ≠ (⊤ : ENNReal))
    (s : Real) (hs : 0 < s) (hs_half : s ≤ 1 / 2) :
    let r := (riemannianEDist I O x).toReal
    ∃ rho : M → Real, ∃ U : Set M,
      IsOpen U ∧ x ∈ U ∧ ContMDiffOn I 𝓘(Real, Real) ∞ rho U ∧
      rho x = r ∧
      (∀ᶠ y in nhds x, (riemannianEDist I O y).toReal ≤ rho y) ∧
      ∀ Y : TangentSpace I x,
        hessFun (I := I) g rho x Y Y ≤
          (g.inner x Y Y -
            (g.inner x (gradientFun (I := I) g rho x) Y) ^ 2) / ((1 - s) * r) := by
  dsimp only
  let r : Real := (riemannianEDist I O x).toReal
  have hdist_ne : riemannianEDist I O x ≠ 0 := by
    intro hzero
    exact hOx (riemannianEDist_eq_zero_imp_eq (I := I) O x hzero)
  have hr : 0 < r := ENNReal.toReal_pos hdist_ne hfin
  obtain ⟨v, hexp, hlen⟩ := minExp_of_ne_top (I := I) g hEnorm O x hfin
  obtain ⟨tail, _hleft, hell⟩ :=
    exists_calabiTail_fraction (I := I) g hEnorm v hexp hlen hr rfl s hs hs_half
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
  have hrho_x : rho x = r := by
    dsimp only [rho]
    rw [hrad_x, tail.length_sum]
  have hupper : ∀ᶠ y in nhds x, (riemannianEDist I O y).toReal ≤ rho y := by
    filter_upwards [tail.branch.hom.open_target.mem_nhds tail.target_mem] with y hy
    have hdist : riemannianEDist I O y ≤
        ENNReal.ofReal tail.initialLength + ENNReal.ofReal (branchRadius (I := I) g tail.branch y) :=
      Manifold.riemannianEDist_triangle.trans
        (add_le_add tail.initial_edist.le (tail.branch.edist_le_radius hy))
    have hreal := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩) hdist
    rwa [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal tail.initialLength_nonneg,
      ENNReal.toReal_ofReal (show 0 ≤ branchRadius (I := I) g tail.branch y
        from Real.sqrt_nonneg _)] at hreal
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
      metricRm04At (I := I) g (gamma t) ∈
        tensor04SectionalNonnegativeCone (I := I) (M := M) := by
    intro t ht
    apply hsec (gamma t)
    have hleft : riemannianEDist I tail.splitPoint (gamma t) ≤ ENNReal.ofReal t := by
      simpa only [intrinsicGeodesic_zero, he_unit, Real.sqrt_one, one_mul, sub_zero] using
        intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm tail.splitPoint e
          (s := (0 : ℝ)) (t := t) ht.1
    have hright : riemannianEDist I (gamma t) x ≤ ENNReal.ofReal (tail.terminalLength - t) := by
      calc
        riemannianEDist I (gamma t) x =
            riemannianEDist I (gamma t) (gamma tail.terminalLength) :=
          congrArg (riemannianEDist I (gamma t)) hend.symm
        _ ≤ ENNReal.ofReal (tail.terminalLength - t) := by
          simpa only [he_unit, Real.sqrt_one, one_mul] using
            intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm tail.splitPoint e
              (s := t) (t := tail.terminalLength) ht.2
    refine le_antisymm ?_ Manifold.riemannianEDist_triangle
    have htriangle : riemannianEDist I O (gamma t) ≤
        riemannianEDist I O tail.splitPoint +
          riemannianEDist I tail.splitPoint (gamma t) :=
      Manifold.riemannianEDist_triangle
    calc
      _ ≤ (riemannianEDist I O tail.splitPoint + riemannianEDist I tail.splitPoint (gamma t)) +
          riemannianEDist I (gamma t) x :=
        add_le_add htriangle (le_refl _)
      _ ≤ (ENNReal.ofReal tail.initialLength + ENNReal.ofReal t) +
          ENNReal.ofReal (tail.terminalLength - t) :=
        add_le_add (add_le_add tail.initial_edist.le hleft) hright
      _ = ENNReal.ofReal (tail.initialLength + tail.terminalLength) := by
        rw [← ENNReal.ofReal_add tail.initialLength_nonneg ht.1,
          ← ENNReal.ofReal_add (add_nonneg tail.initialLength_nonneg ht.1) (sub_nonneg.mpr ht.2)]
        congr 1
        ring
      _ = riemannianEDist I O x := by rw [tail.length_sum]; exact hfull.symm
  have hend' :
      intrinsicGeodesic (I := I) g hEnorm tail.splitPoint (tail.terminalLength • e) 1 = x := by
    rw [hscale, ← expMapIntrinsic_def]
    exact tail.exp_eq
  have hcomp :=
    Geometry.Riemannian.branchHess_gradient_le_of_minimizing_of_sectional_curvature_nonnegative
      (I := I) g hEnorm tail.splitPoint e tail.terminalLength tail.branch tail.terminalLength_pos he_unit
        hsrc hmin hsec_tail
  rw [hend'] at hcomp
  obtain ⟨U, hUopen, hxU, hbrU⟩ :=
    branchRadius_open (I := I) tail.branch tail.source_mem
      (Real.sqrt_pos.mp (tail.endpointVector_norm.symm ▸ tail.terminalLength_pos))
  rw [tail.exp_eq] at hxU
  have hhess := hessFun_add_const (I := I) g tail.initialLength hUopen hbrU hxU
  have hbrDiff := (hbrU x hxU).contMDiffAt (hUopen.mem_nhds hxU) |>.mdifferentiableAt
    (by simp)
  have hgrad : gradientFun (I := I) g rho x =
      gradientFun (I := I) g (branchRadius (I := I) g tail.branch) x := by
    dsimp only [rho]
    rw [gradientFun_add (I := I) g mdifferentiableAt_const hbrDiff,
      gradientFun_const, zero_add]
  refine ⟨rho, U, hUopen, hxU, contMDiffOn_const.add hbrU,
    hrho_x, hupper, ?_⟩
  intro Y
  change hessFun (I := I) g
    (fun y => tail.initialLength + branchRadius (I := I) g tail.branch y) x Y Y ≤ _
  rw [hhess, hgrad, ← hell]
  exact hcomp Y

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
