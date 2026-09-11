import DifferentialGeometry.Geometry.Comparison.Busemann.Ray.BusemannUpperSupport

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Manifold Function
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem smooth_calabi_unit_upper_support_of_complete_metric
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (hRic : ∀ y : M, ∀ v : TangentSpace I y, 0 ≤ ricciTensor g y v v)
    {O x : M} (hOx : O ≠ x) (hfin : riemannianEDistOf g O x ≠ (⊤ : ENNReal)) :
    ∃ (rho : M → ℝ) (U : Set M),
      IsOpen U ∧ x ∈ U ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ rho U ∧
      rho x = (riemannianEDistOf g O x).toReal ∧
      (∀ᶠ y in 𝓝 x, (riemannianEDistOf g O y).toReal ≤ rho y) ∧
      laplacian (LeviCivita g) g rho x ≤
        2 * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) / (riemannianEDistOf g O x).toReal ∧
      g.inner x (gradientFun g rho x) (gradientFun g rho x) = 1 := by
  let : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞)
    (by decide : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro y v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M := inferInstance
  let : CompleteSpace M := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) g := by
    intro y v
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm g y v
  have hRic0 : BonnetMyers.RicciBoundedBelow g 0 := by
    intro y v
    simpa only [zero_mul] using hRic y v
  have hRicq : BonnetMyers.RicciBoundedBelow g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (0 : ℝ) ^ 2)) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, neg_zero] using hRic0
  obtain ⟨tail, _hAt, heq, hupper, _hdiff, _hgrad, hunit, hlap⟩ :=
    exists_calabiData_of_complete_metric g hcomplete 0 le_rfl hRicq hOx hfin
  let rho : M → ℝ := fun y ↦ tail.initialLength + branchRadius g tail.branch y
  have hu : 0 < g.inner tail.splitPoint tail.endpointVector tail.endpointVector := Real.sqrt_pos.mp (by
    rw [tail.endpointVector_norm]
    exact tail.terminalLength_pos)
  obtain ⟨U, hUopen, hxU, hbr⟩ := branchRadius_open tail.branch tail.source_mem hu
  rw [tail.exp_eq] at hxU
  have hrho : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ rho U := contMDiffOn_const.add hbr
  have hed (y : M) : (riemannianEDist I O y).toReal = (riemannianEDistOf g O y).toReal := by
    rw [riemannianEDistOf_eq_riemannianEDist g hEnorm]
  refine ⟨rho, U, hUopen, hxU, hrho, ?_, ?_, ?_, ?_⟩
  · simpa only [rho, hed] using heq
  · simpa only [rho, hed] using hupper
  · simpa only [rho, hed, mul_zero, add_zero] using hlap
  · simpa only [rho] using hunit

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem busemannFunction_exists_smooth_unit_upper_support
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (hRic : ∀ y : M, ∀ v : TangentSpace I y, 0 ≤ ricciTensor g y v v)
    (gamma : ℝ → M)
    (hgamma : ∀ s t : ℝ,
      riemannianEDistOf g (gamma s) (gamma t) = ENNReal.ofReal |s - t|)
    (x : M) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    let b : M → ℝ := fun y ↦ ⨅ t : ℝ, (riemannianEDistOf g y (gamma t)).toReal - t
    ∃ (phi : M → ℝ) (U : Set M),
      IsOpen U ∧ x ∈ U ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ phi U ∧ phi x = b x ∧
      (∀ y ∈ U, b y ≤ phi y) ∧
      laplacian (LeviCivita g) g phi x ≤ epsilon ∧
      g.inner x (gradientFun g phi x) (gradientFun g phi x) = 1 := by
  let b : M → ℝ := fun y ↦ ⨅ t : ℝ, (riemannianEDistOf g y (gamma t)).toReal - t
  let : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞)
    (by decide : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro y v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let m : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  let : MetricSpace M := m
  let : PseudoMetricSpace M := m.toPseudoMetricSpace
  let : PseudoEMetricSpace M := m.toPseudoEMetricSpace
  let : UniformSpace M := m.toUniformSpace
  let : IsRiemannianManifold I M := ⟨by intro y z; rfl⟩
  have hEnorm : IsMetricNorm (I := I) g := by
    intro y v
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm g y v
  have hed (y z : M) : edist y z = riemannianEDistOf g y z := by
    rw [riemannianEDistOf_eq_riemannianEDist g hEnorm]
    exact IsRiemannianManifold.out (I := I) y z
  have hdist (y z : M) : dist y z = (riemannianEDistOf g y z).toReal := by
    rw [← hed, edist_dist, ENNReal.toReal_ofReal dist_nonneg]
  have hisometry : Isometry gamma := by
    intro s t
    rw [hed, hgamma, edist_dist, Real.dist_eq]
  have hb (y : M) : b y = busemannFunction gamma y := by
    simp only [b, busemannFunction, hdist]
  have hmajor (y z : M) : b y ≤ b z + dist y z := by
    have h := (busemannFunction_lipschitz hisometry).dist_le_mul y z
    rw [Real.dist_eq, ← hb y, ← hb z, NNReal.coe_one, one_mul] at h
    have h' := (abs_le.mp h).2
    linarith
  obtain ⟨sigma, _hsmooth, _hgeo, hzero, hmin, hcalib⟩ :=
    exists_calibrated_ray_of_complete_metric g hcomplete gamma hgamma x
  let N : ℝ := ((Module.finrank ℝ E - 1 : ℕ) : ℝ)
  let R : ℝ := 2 * N / epsilon + 1
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hR : 0 < R := by
    have hh : 0 ≤ 2 * N / epsilon := div_nonneg (mul_nonneg (by norm_num) hN) hepsilon.le
    dsimp only [R]
    linarith
  have herror : 2 * N / R ≤ epsilon := (div_le_iff₀ hR).mpr (by
    have hh := div_mul_cancel₀ (2 * N) hepsilon.ne'
    dsimp only [R]
    nlinarith)
  let O : M := sigma R
  have hOxDist : riemannianEDistOf g O x = ENNReal.ofReal R := by
    simpa only [O, hzero, sub_zero, abs_of_pos hR] using hmin R hR.le 0 le_rfl
  have hdistR : dist O x = R := by
    rw [hdist, hOxDist, ENNReal.toReal_ofReal hR.le]
  have hOx : O ≠ x := dist_pos.mp (by rw [hdistR]; exact hR)
  have hfin : riemannianEDistOf g O x ≠ (⊤ : ENNReal) := by
    rw [hOxDist]
    exact ENNReal.ofReal_ne_top
  have hcalibR : b O = b x - R := hcalib R hR.le
  obtain ⟨rho, U, hUopen, hxU, hrho, hrhoeq, hupper, hlap, hunit⟩ :=
    smooth_calabi_unit_upper_support_of_complete_metric g hcomplete hRic hOx hfin
  rw [hOxDist, ENNReal.toReal_ofReal hR.le] at hrhoeq hlap
  let phi : M → ℝ := fun y ↦ (b x - R) + rho y
  have hphiUpper : ∀ᶠ y in 𝓝 x, b y ≤ phi y := by
    filter_upwards [hupper] with y hy
    rw [← hdist O y, dist_comm] at hy
    have hh := hmajor y O
    rw [hcalibR] at hh
    change b y ≤ (b x - R) + rho y
    linarith
  obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp hphiUpper
  have hdiff : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) rho y := by
    filter_upwards [hUopen.mem_nhds hxU] with y hy
    exact ((hrho y hy).contMDiffAt (hUopen.mem_nhds hy)).mdifferentiableAt (by simp)
  have hdiffAt : MDifferentiableAt I 𝓘(ℝ, ℝ) rho x :=
    ((hrho x hxU).contMDiffAt (hUopen.mem_nhds hxU)).mdifferentiableAt (by simp)
  have hphiGrad : gradientFun g phi x = gradientFun g rho x := by
    change gradientFun g (fun y ↦ (b x - R) + rho y) x = gradientFun g rho x
    rw [gradientFun_add g (mdifferentiableAt_const (c := b x - R)) hdiffAt,
      gradientFun_const, zero_add]
  refine ⟨phi, U ∩ V, hUopen.inter hVopen, ⟨hxU, hxV⟩,
    (contMDiffOn_const.add hrho).mono inter_subset_left, ?_, ?_, ?_, ?_⟩
  · change (b x - R) + rho x = b x
    rw [hrhoeq]
    ring
  · intro y hy
    exact hVsub hy.2
  · have hgrad := gradientFun_mdiffOn g hUopen hrho hxU
    change laplacian (LeviCivita g) g (fun y ↦ (b x - R) + rho y) x ≤ epsilon
    rw [laplacian_add_const (LeviCivita g) g (b x - R) hdiff hgrad]
    exact hlap.trans herror
  · rw [hphiGrad]
    exact hunit

end DifferentialGeometry.Geometry.Metric

end
