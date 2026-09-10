import DifferentialGeometry.Geometry.Comparison.Busemann.Support.CoraySmoothSupport
import DifferentialGeometry.Geometry.Comparison.Toponogov.CalabiTail
import DifferentialGeometry.Geometry.Operator.Laplacian.Minimum

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology NNReal ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section LocalOperators

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] in
private theorem eventually_mdifferentiable_of_smooth {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f x) :
    ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) f y := by
  have h : ∀ᶠ y in 𝓝 x, ContMDiffAt I 𝓘(ℝ, ℝ) 1 f y :=
    (contMDiffAt_iff_contMDiffAt_nhds (by decide)).mp (hf.of_le (by simp))
  exact h.mono fun _ hy => hy.mdifferentiableAt (by simp)


theorem laplacian_sub_of_contMDiffAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (g : SmoothRiemannianMetric I M) {f h : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f x)
    (hh : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ h x) :
    laplacian (I := I) cov g (fun y => f y - h y) x =
      laplacian (I := I) cov g f x - laplacian (I := I) cov g h x := by
  have hgradf := (gradientFun_contMDiffAt (I := I) g hf).mdifferentiableAt (by simp)
  have hgradh := (gradientFun_contMDiffAt (I := I) g hh).mdifferentiableAt (by simp)
  have hgradsub := (gradientFun_contMDiffAt (I := I) g (hf.sub hh)).mdifferentiableAt
    (by simp)
  have hdiff : MDiffAt (T% fun y => gradientFun (I := I) g f y -
      gradientFun (I := I) g h y) x := by
    simpa only [sub_eq_add_neg, Pi.add_apply, Pi.neg_apply] using
      mdifferentiableAt_add_section hgradf (mdifferentiableAt_neg_section hgradh)
  have heq : (fun y => gradientFun (I := I) g (fun z => f z - h z) y) =ᶠ[𝓝 x]
      (fun y => gradientFun (I := I) g f y - gradientFun (I := I) g h y) := by
    filter_upwards [eventually_mdifferentiable_of_smooth hf,
      eventually_mdifferentiable_of_smooth hh] with y hyf hyh
    exact gradientFun_sub (I := I) g hyf hyh
  have hcov := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    hgradsub hdiff Filter.univ_mem heq
  calc
    laplacian (I := I) cov g (fun y => f y - h y) x =
        divergence (I := I) cov
          (fun y => gradientFun (I := I) g f y - gradientFun (I := I) g h y) x := by
      unfold laplacian divergence
      rw [hcov]
    _ = laplacian (I := I) cov g f x - laplacian (I := I) cov g h x :=
      divergence_sub (I := I) cov hgradf hgradh


theorem laplacian_le_of_smooth_upper_support [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f h : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f x)
    (hh : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ h x)
    (hcontact : f x = h x) (hupper : ∀ᶠ y in 𝓝 x, f y ≤ h y) :
    laplacian (I := I) (LeviCivita (I := I) g) g f x ≤
      laplacian (I := I) (LeviCivita (I := I) g) g h x := by
  have hmin : IsLocalMin (fun y => h y - f y) x := by
    filter_upwards [hupper] with y hy
    change h x - f x ≤ h y - f y
    rw [hcontact, sub_self]
    exact sub_nonneg.mpr hy
  have hmc : IsMetricCompatible (I := I) (LeviCivita (I := I) g) g := by
    simpa only [LeviCivita] using
      leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g
  have hnonneg := laplacian_nonneg_at_spatial_min_of_metricCompatible
    (I := I) (LeviCivita (I := I) g) g hmc hmin
    ((hh.sub hf).mdifferentiableAt (by simp))
    (eventually_mdifferentiable_of_smooth (hh.sub hf))
    ((gradientFun_contMDiffAt (I := I) g (hh.sub hf)).mdifferentiableAt (by simp))
  rw [laplacian_sub_of_contMDiffAt (I := I) _ g hh hf] at hnonneg
  exact sub_nonneg.mp hnonneg

end LocalOperators

section CompleteMetric

variable [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem riemannian_toReal_eq_dist (p q : M) :
    (riemannianEDist I p q).toReal = dist p q := by
  rw [← IsRiemannianManifold.out (I := I), edist_dist,
    ENNReal.toReal_ofReal dist_nonneg]

private theorem calabi_tail_laplacian_le
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    {p x : M} {r : ℝ} (tail : CalabiTail (I := I) g hEnorm p x r) :
    laplacian (I := I) (LeviCivita (I := I) g) g
        (fun y => tail.initialLength + branchRadius (I := I) g tail.branch y) x ≤
      ((Module.finrank ℝ E - 1 : ℕ) : ℝ) / tail.terminalLength := by
  have hu : 0 < g.inner tail.splitPoint tail.endpointVector tail.endpointVector := by
    apply Real.sqrt_pos.mp
    rw [tail.endpointVector_norm]
    exact tail.terminalLength_pos
  obtain ⟨v, hv, hperp, hmean⟩ := exists_intrMean_on (I := I) g hEnorm
    tail.splitPoint tail.endpointVector 0 tail.conjugateScale le_rfl tail.one_lt_conjugateScale hu tail.no_conjugate (by
      intro _
      dsimp only
      intro t _
      simpa using hRic _ _)
  obtain ⟨U, hU, hxU, hbrU⟩ := branchRadius_open (I := I) tail.branch tail.source_mem hu
  rw [tail.exp_eq] at hxU
  have hbr_ev : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(ℝ, ℝ) (branchRadius (I := I) g tail.branch) y := by
    filter_upwards [hU.mem_nhds hxU] with y hy
    exact ((hbrU y hy).contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)
  rw [laplacian_add_const (I := I) _ g tail.initialLength hbr_ev
    (gradientFun_mdiffOn (I := I) g hU hbrU hxU)]
  have hlap := branchLap_eq_mean (I := I) g hEnorm tail.branch tail.endpointVector v
    tail.source_mem hu hv hperp (by simp)
  dsimp only at hlap hmean
  rw [← expMapIntrinsic_def, tail.exp_eq, tail.endpointVector_norm] at hlap
  rw [hlap]
  simpa only [tail.endpointVector_norm, mul_zero, add_zero] using hmean

theorem laplacian_dist_le_of_ricci_nonneg
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    {p x : M} (hpx : p ≠ x)
    (hd : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => dist p y) x) :
    laplacian (I := I) (LeviCivita (I := I) g) g (fun y => dist p y) x ≤
      ((Module.finrank ℝ E - 1 : ℕ) : ℝ) / dist p x := by
  have hr : 0 < dist p x := dist_pos.mpr hpx
  have hfin : riemannianEDist I p x ≠ ⊤ := by
    rw [← IsRiemannianManifold.out (I := I)]
    exact edist_ne_top p x
  obtain ⟨v, hexp, hlen⟩ := minExp_of_ne_top (I := I) g hEnorm p x hfin
  rw [riemannian_toReal_eq_dist (I := I)] at hlen
  have hbound (s : ℝ) (hs : 0 < s) (hs_half : s ≤ 1 / 2) :
      laplacian (I := I) (LeviCivita (I := I) g) g (fun y => dist p y) x ≤
        ((Module.finrank ℝ E - 1 : ℕ) : ℝ) / ((1 - s) * dist p x) := by
    obtain ⟨tail, _, hell⟩ := exists_calabiTail_fraction (I := I) g hEnorm v hexp hlen
      hr (riemannian_toReal_eq_dist (I := I) p x).symm s hs hs_half
    obtain ⟨hrho, hcontact, hupper, _, _, _, _⟩ :=
      calabi_support_of_tail (I := I) g hEnorm 0 le_rfl tail (by
        intro _
        dsimp only
        intro t _
        simpa using hRic _ _)
    have hle := laplacian_le_of_smooth_upper_support (I := I) g hd hrho
      hcontact.symm (by simpa only [riemannian_toReal_eq_dist (I := I)] using hupper)
    have hsharp := calabi_tail_laplacian_le (I := I) g hEnorm hRic tail
    rw [hell] at hsharp
    exact hle.trans hsharp
  let s : ℕ → ℝ := fun n => (1 / 2) * (1 / ((n : ℝ) + 1))
  have hs (n : ℕ) : 0 < s n ∧ s n ≤ 1 / 2 := by
    have hden : 0 < (n : ℝ) + 1 := by positivity
    have hfrac : 1 / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ hden).mpr
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    dsimp only [s]
    constructor
    · positivity
    · nlinarith
  have hs0 : Tendsto s atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 2 : ℝ)
  have hlim : Tendsto
      (fun n => ((Module.finrank ℝ E - 1 : ℕ) : ℝ) / ((1 - s n) * dist p x))
      atTop (𝓝 (((Module.finrank ℝ E - 1 : ℕ) : ℝ) / dist p x)) := by
    have hden := ((tendsto_const_nhds (x := (1 : ℝ))).sub hs0).mul_const (dist p x)
    have h := (tendsto_const_nhds
      (x := ((Module.finrank ℝ E - 1 : ℕ) : ℝ))).div hden (by simpa using hr.ne')
    convert h using 1 <;> first | rfl | simp only [sub_zero, one_mul]
  exact ge_of_tendsto hlim (Eventually.of_forall fun n => hbound (s n) (hs n).1 (hs n).2)

theorem intrinsic_ray_support_laplacian_ge
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (fun t : ℝ≥0 => intrinsicGeodesic (I := I) g hEnorm p u t))
    (a s : ℝ) (hs : 0 < s) :
    -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) / s) ≤
      laplacian (I := I) (LeviCivita (I := I) g) g
        (fun y => a + s - dist y (intrinsicGeodesic (I := I) g hEnorm p u s)) p := by
  have hdist : dist p (intrinsicGeodesic (I := I) g hEnorm p u s) = s := by
    have h := hiso.dist_eq 0 ⟨s, hs.le⟩
    change dist (intrinsicGeodesic (I := I) g hEnorm p u 0)
      (intrinsicGeodesic (I := I) g hEnorm p u s) = |(0 : ℝ) - s| at h
    simpa only [intrinsicGeodesic_zero (I := I) g hEnorm p u, zero_sub,
      abs_neg, abs_of_nonneg hs.le] using h
  have hqp : intrinsicGeodesic (I := I) g hEnorm p u s ≠ p := by
    apply dist_pos.mp
    rw [dist_comm, hdist]
    exact hs
  have hd := contMDiffAt_dist_from_intrinsic_ray (I := I) g hEnorm p u hu hiso s hs
  have hfun : (fun y => dist (intrinsicGeodesic (I := I) g hEnorm p u s) y) =
      (fun y => dist y (intrinsicGeodesic (I := I) g hEnorm p u s)) :=
    funext fun y => dist_comm _ y
  have hcompare := laplacian_dist_le_of_ricci_nonneg (I := I) g hEnorm hRic hqp
    (by rw [hfun]; exact hd)
  rw [hfun, dist_comm (intrinsicGeodesic (I := I) g hEnorm p u s) p, hdist] at hcompare
  rw [laplacian_sub_of_contMDiffAt (I := I) _ g contMDiffAt_const hd, laplacian_const]
  linarith

theorem exists_busemann_support_laplacian_gt
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    (c : ℝ≥0 → M) (hc : Isometry c) (p : M) (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : M → ℝ, ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ φ U ∧
      (∀ x, φ x ≤ busemann c x) ∧ φ p = busemann c p ∧
      -ε < laplacian (I := I) (LeviCivita (I := I) g) g φ p := by
  obtain ⟨u, hu, hiso, _, hsupport⟩ :=
    exists_smooth_intrinsic_coray_support (I := I) g hEnorm c hc p
  let d : ℝ := ((Module.finrank ℝ E - 1 : ℕ) : ℝ)
  let s : ℝ := d / ε + 1
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hs : 0 < s := add_pos_of_nonneg_of_pos (div_nonneg hd hε.le) zero_lt_one
  obtain ⟨U, hU, hp, hφ, hbelow, hcontact⟩ := hsupport s hs
  refine ⟨fun y => busemann c p + s -
    dist y (intrinsicGeodesic (I := I) g hEnorm p u s), U, hU, hp, hφ, hbelow,
    hcontact, ?_⟩
  have hsmall : d / s < ε := by
    apply (div_lt_iff₀ hs).mpr
    dsimp only [s]
    rw [mul_add, mul_div_cancel₀ _ hε.ne', mul_one]
    linarith
  exact lt_of_lt_of_le (neg_lt_neg hsmall)
    (intrinsic_ray_support_laplacian_ge (I := I) g hEnorm hRic p u hu hiso
      (busemann c p) s hs)

end CompleteMetric

end DifferentialGeometry.Geometry.Topology

end
