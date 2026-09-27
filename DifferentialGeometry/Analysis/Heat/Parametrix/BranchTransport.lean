import DifferentialGeometry.Analysis.Heat.Parametrix.CoordinateCoefficient
import DifferentialGeometry.Geometry.Comparison.Volume.BranchDensityTransport

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch

open DifferentialGeometry.Analysis.HeatEquation
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral
open DifferentialGeometry.Integral.Measure
open VolumeComparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

private theorem contDiffOn_density
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) :
    ContDiffOn ℝ ∞ (paramDensity g B.hom) B.hom.source := by
  let D1 : PartialDiffeomorph 𝓘(ℝ, E) I E M 1 :=
    { toPartialEquiv := B.hom.toPartialEquiv, open_source := B.hom.open_source,
      open_target := B.hom.open_target, contMDiffOn_toFun := B.hom.contMDiffOn.of_le (by simp),
      contMDiffOn_invFun := B.hom.contMDiffOn_invFun.of_le (by simp) }
  exact contDiffOn_paramDensity g D1 B.hom.open_source (fun _ hv => hv)
    (by simpa using B.hom.contMDiffOn)

theorem contMDiffOn_heatParametrixCoefficientInCoordinates
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {U : Set E}
    (hU : IsOpen U) (hstar : StarConvex ℝ 0 U) (hsub : U ⊆ B.hom.source) (k : ℕ) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (heatParametrixCoefficientInCoordinates g B.hom B.inv
        (fun v => paramDensity g B.hom v / paramDensity g B.hom 0) k)
      (B.dom ∩ B.inv ⁻¹' U) := by
  have hV : IsOpen (B.dom ∩ B.inv ⁻¹' U) :=
    B.inv_contMDiffOn.continuousOn.isOpen_inter_preimage B.hom.open_target hU
  have hJ : ContDiffOn ℝ ∞
      (fun v => paramDensity g B.hom v / paramDensity g B.hom 0) U :=
    ((contDiffOn_density B).mono hsub).div_const _
  have hpos : ∀ v ∈ U, 0 < paramDensity g B.hom v / paramDensity g B.hom 0 := by
    intro v hv
    have h0 : (0 : E) ∈ U := by
      simpa only [zero_smul] using hstar.smul_mem hv (le_refl (0 : ℝ)) zero_le_one
    exact div_pos (paramDensity_pos_branch B (hsub hv)) (paramDensity_pos_branch B (hsub h0))
  apply DifferentialGeometry.Analysis.HeatEquation.contMDiffOn_heatParametrixCoefficientInCoordinates
    g hU hstar hV (B.hom.contMDiffOn.mono hsub) (B.inv_contMDiffOn.mono inter_subset_left) _
      (fun _ hq => hq.2) hJ hpos k
  intro v hv
  refine ⟨B.hom.map_source (hsub hv), ?_⟩
  change B.inv (B.hom v) ∈ U
  rw [show B.inv (B.hom v) = v from B.hom.left_inv (hsub hv)]
  exact hv

private theorem inv_intrinsicGeodesic_eventuallyEq
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {x : E} (hx : x ∈ B.hom.source) :
    (fun t : ℝ => B.inv (intrinsicGeodesic g hEnorm p (show TangentSpace I p from x) t))
      =ᶠ[𝓝 1] fun t : ℝ => t • x := by
  have hev : ∀ᶠ t : ℝ in 𝓝 1, t • x ∈ B.hom.source :=
    (B.hom.open_source.preimage (by fun_prop)).mem_nhds (by
      simpa only [mem_preimage, one_smul] using hx)
  filter_upwards [hev] with t ht
  have hexp : expMapIntrinsic g hEnorm p (t • (show TangentSpace I p from x)) =
      intrinsicGeodesic g hEnorm p (show TangentSpace I p from x) t :=
    (expMapIntrinsic_def g hEnorm p _).trans (intrinsicGeodesic_smul g hEnorm p _ t)
  rw [← hexp]
  exact B.left_inv ht

theorem hasDerivAt_heatParametrixCoefficientInCoordinates_zero_intrinsicGeodesic
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {x : E} (hx : x ∈ B.hom.source)
    (h0 : (0 : E) ∈ B.hom.source) :
    HasDerivAt (fun t : ℝ => heatParametrixCoefficientInCoordinates g B.hom B.inv
        (fun v => paramDensity g B.hom v / paramDensity g B.hom 0) 0
        (intrinsicGeodesic g hEnorm p (show TangentSpace I p from x) t))
      ((Module.finrank ℝ E - laplacian (LeviCivita g) g (branchEnergy g B)
          (expMapIntrinsic g hEnorm p (show TangentSpace I p from x))) / 2 *
        heatParametrixCoefficientInCoordinates g B.hom B.inv
          (fun v => paramDensity g B.hom v / paramDensity g B.hom 0) 0
          (expMapIntrinsic g hEnorm p (show TangentSpace I p from x))) 1 := by
  have hd := hasDerivAt_paramDensity_ratio_inv_sqrt_radial_one B hx h0
  have hq : B.inv (expMapIntrinsic g hEnorm p (show TangentSpace I p from x)) = x :=
    B.left_inv hx
  simp only [heatParametrixCoefficientInCoordinates, hq]
  apply hd.congr_of_eventuallyEq
  filter_upwards [inv_intrinsicGeodesic_eventuallyEq B hx] with t ht
  rw [ht]

theorem hasDerivAt_heatParametrixCoefficientInCoordinates_succ_intrinsicGeodesic
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {U : Set E}
    (hU : IsOpen U) (hstar : StarConvex ℝ 0 U) (hsub : U ⊆ B.hom.source)
    (k : ℕ) {x : E} (hx : x ∈ U) :
    HasDerivAt (fun t : ℝ => heatParametrixCoefficientInCoordinates g B.hom B.inv
        (fun v => paramDensity g B.hom v / paramDensity g B.hom 0) (k + 1)
        (intrinsicGeodesic g hEnorm p (show TangentSpace I p from x) t))
      (((Module.finrank ℝ E - laplacian (LeviCivita g) g (branchEnergy g B)
          (expMapIntrinsic g hEnorm p (show TangentSpace I p from x))) / 2 - (k + 1 : ℝ)) *
        heatParametrixCoefficientInCoordinates g B.hom B.inv
          (fun v => paramDensity g B.hom v / paramDensity g B.hom 0) (k + 1)
          (expMapIntrinsic g hEnorm p (show TangentSpace I p from x)) +
        laplacian (LeviCivita g) g
          (heatParametrixCoefficientInCoordinates g B.hom B.inv
            (fun v => paramDensity g B.hom v / paramDensity g B.hom 0) k)
          (expMapIntrinsic g hEnorm p (show TangentSpace I p from x))) 1 := by
  let J := fun v : E => paramDensity g B.hom v / paramDensity g B.hom 0
  let Q := fun v : E => Real.sqrt (J v) *
    laplacian (LeviCivita g) g (heatParametrixCoefficientInCoordinates g B.hom B.inv J k) (B.hom v)
  have hV : IsOpen (B.dom ∩ B.inv ⁻¹' U) :=
    B.inv_contMDiffOn.continuousOn.isOpen_inter_preimage B.hom.open_target hU
  have hΔ := (contMDiffOn_laplacian_leviCivita g hV
    (B.contMDiffOn_heatParametrixCoefficientInCoordinates hU hstar hsub k)).continuousOn
  have hQ : ContinuousOn Q U := by
    apply (((contDiffOn_density B).continuousOn.mono hsub).div_const _).sqrt.mul
    apply hΔ.comp (B.hom.contMDiffOn.continuousOn.mono hsub)
    intro v hv
    refine ⟨B.hom.map_source (hsub hv), ?_⟩
    change B.inv (B.hom v) ∈ U
    rw [show B.inv (B.hom v) = v from B.hom.left_inv (hsub hv)]
    exact hv
  have hzero : (0 : E) ∈ B.hom.source := hsub (by
    simpa only [zero_smul] using hstar.smul_mem hx (le_refl (0 : ℝ)) zero_le_one)
  have hI := hasDerivAt_radialIntegral_smul k hU hstar hQ hx
  have h0 := hasDerivAt_paramDensity_ratio_inv_sqrt_radial_one B (hsub hx) hzero
  have hd := h0.mul hI
  have heq : (fun t : ℝ => heatParametrixCoefficientInCoordinates g B.hom B.inv J (k + 1)
      (intrinsicGeodesic g hEnorm p (show TangentSpace I p from x) t)) =ᶠ[𝓝 1]
      fun t : ℝ => (Real.sqrt (J (t • x)))⁻¹ * radialIntegral k Q (t • x) := by
    filter_upwards [inv_intrinsicGeodesic_eventuallyEq B (hsub hx)] with t ht
    simp only [heatParametrixCoefficientInCoordinates, ht, Q]
  have hq : B.inv (expMapIntrinsic g hEnorm p (show TangentSpace I p from x)) = x :=
    B.left_inv (hsub hx)
  have ha : heatParametrixCoefficientInCoordinates g B.hom B.inv J (k + 1)
      (expMapIntrinsic g hEnorm p (show TangentSpace I p from x)) =
      (Real.sqrt (J x))⁻¹ * radialIntegral k Q x := by
    simp only [heatParametrixCoefficientInCoordinates, hq, Q]
  have hxexp : B.hom x = expMapIntrinsic g hEnorm p (show TangentSpace I p from x) :=
    (B.hom_eq (hsub hx)).symm
  have hs : Real.sqrt (J x) ≠ 0 := Real.sqrt_ne_zero'.mpr
    (div_pos (paramDensity_pos_branch B (hsub hx)) (paramDensity_pos_branch B hzero))
  apply (hd.congr_of_eventuallyEq heq).congr_deriv
  change _ = ((_ / 2 - (k + 1 : ℝ)) *
    heatParametrixCoefficientInCoordinates g B.hom B.inv J (k + 1) _ + _)
  simp only [one_smul, Q, smul_eq_mul, hxexp, ha]
  change _ * (Real.sqrt (J x))⁻¹ * radialIntegral k Q x +
    (Real.sqrt (J x))⁻¹ * (Real.sqrt (J x) * _ - _ * radialIntegral k Q x) = _
  field_simp
  ring

theorem heatParametrixCoefficientInCoordinates_transport
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {U : Set E}
    (hU : IsOpen U) (hstar : StarConvex ℝ 0 U) (hsub : U ⊆ B.hom.source)
    (k : ℕ) {x : E} (hx : x ∈ U) :
    deriv (fun t : ℝ => heatParametrixCoefficientInCoordinates g B.hom B.inv
        (fun v => paramDensity g B.hom v / paramDensity g B.hom 0) k
        (intrinsicGeodesic g hEnorm p (show TangentSpace I p from x) t)) 1 +
      ((k : ℝ) + (laplacian (LeviCivita g) g (branchEnergy g B)
          (expMapIntrinsic g hEnorm p (show TangentSpace I p from x)) -
        Module.finrank ℝ E) / 2) *
        heatParametrixCoefficientInCoordinates g B.hom B.inv
          (fun v => paramDensity g B.hom v / paramDensity g B.hom 0) k
          (expMapIntrinsic g hEnorm p (show TangentSpace I p from x)) =
      match k with
      | 0 => 0
      | j + 1 => laplacian (LeviCivita g) g
          (heatParametrixCoefficientInCoordinates g B.hom B.inv
            (fun v => paramDensity g B.hom v / paramDensity g B.hom 0) j)
          (expMapIntrinsic g hEnorm p (show TangentSpace I p from x)) := by
  cases k with
  | zero =>
    have hzero : (0 : E) ∈ B.hom.source := hsub (by
      simpa only [zero_smul] using hstar.smul_mem hx (le_refl (0 : ℝ)) zero_le_one)
    rw [(B.hasDerivAt_heatParametrixCoefficientInCoordinates_zero_intrinsicGeodesic
      (hsub hx) hzero).deriv]
    simp only [Nat.cast_zero, zero_add]
    ring
  | succ k =>
    rw [(B.hasDerivAt_heatParametrixCoefficientInCoordinates_succ_intrinsicGeodesic
      hU hstar hsub k hx).deriv]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

end DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch
