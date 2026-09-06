import DifferentialGeometry.Geometry.Metric.InnerExpansion
import DifferentialGeometry.Geometry.Operator.LaplacianBridge
import DifferentialGeometry.Geometry.Operator.LaplacianMinimum
import DifferentialGeometry.Geometry.Operator.NormGradSq
import DifferentialGeometry.Geometry.Operator.WeightedLaplacian
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry.Operator

open Connection Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

def isWeightedLaplacianUpperSupportAt
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (psi : M → Real) (x : M) (A B : Real) (phi : M → Real) : Prop :=
  ContMDiffAt I 𝓘(Real, Real) ∞ phi x ∧
    phi x = psi x ∧
    (∀ᶠ y in 𝓝 x, psi y ≤ phi y) ∧
    (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(Real, Real) phi y) ∧
    MDifferentiableAt I (I.prod 𝓘(Real, E))
      (T% fun y : M => gradientFun (I := I) g phi y) x ∧
    Real.sqrt
        (g.inner x (gradientFun (I := I) g phi x)
          (gradientFun (I := I) g phi x)) ≤ A ∧
    laplacian (I := I) (LeviCivita (I := I) g) g phi x -
        g.inner x (gradFun (I := I) g f x)
          (gradientFun (I := I) g phi x) ≤ B

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem weightedOmoriYau_of_upperSupports
    (g : SmoothRiemannianMetric I M) (f u : C^∞⟮I, M; Real⟯)
    (psi : M → Real) (hpsi : Continuous psi)
    (hpsi_nonneg : ∀ x, 0 ≤ psi x)
    (hpsi_atTop : Tendsto psi (cocompact M) atTop)
    (hlower : ∃ m : Real, ∀ x, m ≤ u x)
    {A B epsilon : Real} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hepsilon : 0 < epsilon)
    (hsupport : ∀ x : M, ∃ phi : M → Real,
      isWeightedLaplacianUpperSupportAt (I := I) g f psi x A B phi)
    (y : M) :
    ∃ x : M,
      u x ≤ u y + epsilon ∧
      Real.sqrt (normGradSqFun (I := I) g u x) ≤ epsilon * A ∧
      -epsilon * B ≤ weightedLaplacian (I := I) g f u x := by
  let delta : Real := epsilon / (1 + psi y)
  have hden : 0 < 1 + psi y := by
    linarith [hpsi_nonneg y]
  have hdelta : 0 < delta := by
    exact div_pos hepsilon hden
  have hdelta_le : delta ≤ epsilon := by
    dsimp only [delta]
    apply (div_le_iff₀ hden).2
    nlinarith [hpsi_nonneg y, hepsilon.le]
  let F : M → Real := fun x => u x + delta * psi x
  have hF_cont : Continuous F := by
    exact u.contMDiff.continuous.add (continuous_const.mul hpsi)
  obtain ⟨m, hm⟩ := hlower
  have hF_atTop : Tendsto F (cocompact M) atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    have hpsi_eventually :=
      hpsi_atTop (Filter.eventually_ge_atTop ((b - m) / delta))
    filter_upwards [hpsi_eventually] with z hz
    have hscale := mul_le_mul_of_nonneg_left hz hdelta.le
    have hcancel : delta * ((b - m) / delta) = b - m := by
      field_simp [hdelta.ne']
    change b ≤ u z + delta * psi z
    calc
      b = m + delta * ((b - m) / delta) := by rw [hcancel]; ring
      _ ≤ m + delta * psi z := by nlinarith
      _ ≤ u z + delta * psi z := by nlinarith [hm z]
  let _ : Nonempty M := ⟨y⟩
  obtain ⟨x, hx⟩ := hF_cont.exists_forall_le hF_atTop
  obtain ⟨phi, hphi_inf, hphi_x, hupper, hphi_eventually,
      hgrad_phi, hphi_norm, hphi_weighted⟩ := hsupport x
  have hpenalty_x : 0 ≤ delta * psi x :=
    mul_nonneg hdelta.le (hpsi_nonneg x)
  have hpenalty_y : delta * psi y ≤ epsilon := by
    have hfrac : psi y / (1 + psi y) ≤ 1 :=
      (div_le_one hden).2 (by linarith [hpsi_nonneg y])
    calc
      delta * psi y = epsilon * (psi y / (1 + psi y)) := by
        dsimp only [delta]
        ring
      _ ≤ epsilon * 1 := mul_le_mul_of_nonneg_left hfrac hepsilon.le
      _ = epsilon := mul_one _
  have hu_value : u x ≤ u y + epsilon := by
    have hxy := hx y
    dsimp only [F] at hxy
    nlinarith
  let v : M → Real := fun z => u z + delta * phi z
  have hv_min : IsLocalMin v x := by
    unfold IsLocalMin IsMinFilter
    filter_upwards [hupper] with z hz
    have hscale := mul_le_mul_of_nonneg_left hz hdelta.le
    have hxz := hx z
    dsimp only [F, v] at hxz ⊢
    rw [hphi_x]
    nlinarith
  have hphi_mdiff : MDifferentiableAt I 𝓘(Real, Real) phi x :=
    hphi_inf.mdifferentiableAt (by simp)
  have hv_inf : ContMDiffAt I 𝓘(Real, Real) ∞ v x := by
    exact u.contMDiff.contMDiffAt.add (contMDiffAt_const.mul hphi_inf)
  have hv_mdiff : MDifferentiableAt I 𝓘(Real, Real) v x :=
    hv_inf.mdifferentiableAt (by simp)
  have hv_eventually :
      ∀ᶠ z in 𝓝 x, MDifferentiableAt I 𝓘(Real, Real) v z := by
    filter_upwards [hphi_eventually] with z hz
    exact (u.contMDiff.mdifferentiableAt (by simp)).add
      (mdifferentiableAt_const.mul hz)
  have hgrad_v : MDifferentiableAt I (I.prod 𝓘(Real, E))
      (T% fun z : M => gradientFun (I := I) g v z) x :=
    (gradientFun_contMDiffAt (I := I) g hv_inf).mdifferentiableAt (by simp)
  have hmetric : IsMetricCompatibleGen (I := I) (LeviCivita (I := I) g) g := by
    simpa [LeviCivita] using
      (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
  have hlap_v_nonneg :
      0 ≤ laplacian (I := I) (LeviCivita (I := I) g) g v x :=
    laplacian_nonneg_at_spatial_min_of_metricCompatible
      (I := I) (LeviCivita (I := I) g) g hmetric
        hv_min hv_mdiff hv_eventually hgrad_v
  have hgrad_v_zero : gradientFun (I := I) g v x = 0 :=
    gradientFun_eq_zero_at_spatial_min (I := I) g hv_min hv_mdiff
  have hgrad_sum :
      gradientFun (I := I) g u x +
          delta • gradientFun (I := I) g phi x = 0 := by
    change gradientFun (I := I) g
        (fun z : M => u z + (delta • phi) z) x = 0 at hgrad_v_zero
    rw [gradientFun_add (I := I) g (u.contMDiff.mdifferentiableAt (by simp))
      (hphi_mdiff.const_smul delta),
      gradientFun_const_smul (I := I) g delta hphi_mdiff] at hgrad_v_zero
    exact hgrad_v_zero
  have hgrad_u :
      gradientFun (I := I) g u x =
        (-delta) • gradientFun (I := I) g phi x := by
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_left hgrad_sum
  have hu_norm :
      Real.sqrt (normGradSqFun (I := I) g u x) ≤ epsilon * A := by
    change Real.sqrt
      (g.inner x (gradientFun (I := I) g u x)
        (gradientFun (I := I) g u x)) ≤ epsilon * A
    rw [hgrad_u, sqrt_inner_smul, abs_neg, abs_of_nonneg hdelta.le]
    calc
      delta * Real.sqrt
          (g.inner x (gradientFun (I := I) g phi x)
            (gradientFun (I := I) g phi x)) ≤ delta * A :=
        mul_le_mul_of_nonneg_left hphi_norm hdelta.le
      _ ≤ epsilon * A := mul_le_mul_of_nonneg_right hdelta_le hA
  have hu_eventually :
      ∀ᶠ z in 𝓝 x, MDifferentiableAt I 𝓘(Real, Real) u z :=
    Filter.Eventually.of_forall fun z =>
      u.contMDiff.mdifferentiableAt (by simp)
  have hscaled_eventually :
      ∀ᶠ z in 𝓝 x, MDifferentiableAt I 𝓘(Real, Real) (delta • phi) z :=
    hphi_eventually.mono fun z hz => hz.const_smul delta
  have hgrad_u_mdiff : MDifferentiableAt I (I.prod 𝓘(Real, E))
      (T% fun z : M => gradientFun (I := I) g u z) x :=
    gradientFun_mdiffAt (I := I) g u.contMDiff x
  have hscaled_inf :
      ContMDiffAt I 𝓘(Real, Real) ∞ (delta • phi) x := by
    change ContMDiffAt I 𝓘(Real, Real) ∞ (fun z => delta * phi z) x
    exact contMDiffAt_const.mul hphi_inf
  have hgrad_scaled : MDifferentiableAt I (I.prod 𝓘(Real, E))
      (T% fun z : M => gradientFun (I := I) g (delta • phi) z) x :=
    (gradientFun_contMDiffAt (I := I) g hscaled_inf).mdifferentiableAt (by simp)
  have hlap_v :
      laplacian (I := I) (LeviCivita (I := I) g) g v x =
        laplacian (I := I) (LeviCivita (I := I) g) g u x +
          delta * laplacian (I := I) (LeviCivita (I := I) g) g phi x := by
    change laplacian (I := I) (LeviCivita (I := I) g) g
        (fun z : M => u z + (delta • phi) z) x = _
    rw [laplacian_add_at (I := I) (LeviCivita (I := I) g) g
      hu_eventually hscaled_eventually hgrad_u_mdiff hgrad_scaled,
      laplacian_smul_at (I := I) (LeviCivita (I := I) g) g
        delta hphi_eventually hgrad_phi]
  have hinner_u :
      g.inner x (gradFun (I := I) g f x)
          (gradientFun (I := I) g u x) =
        -delta * g.inner x (gradFun (I := I) g f x)
          (gradientFun (I := I) g phi x) := by
    rw [hgrad_u, map_smul, smul_eq_mul]
  have hweighted_sum :
      0 ≤
        (laplacian (I := I) (LeviCivita (I := I) g) g u x -
          g.inner x (gradFun (I := I) g f x)
            (gradientFun (I := I) g u x)) +
        delta *
          (laplacian (I := I) (LeviCivita (I := I) g) g phi x -
            g.inner x (gradFun (I := I) g f x)
              (gradientFun (I := I) g phi x)) := by
    rw [hlap_v] at hlap_v_nonneg
    rw [hinner_u]
    nlinarith
  have hu_weighted :
      -delta * B ≤
        laplacian (I := I) (LeviCivita (I := I) g) g u x -
          g.inner x (gradFun (I := I) g f x)
            (gradientFun (I := I) g u x) := by
    have hscaled := mul_le_mul_of_nonneg_left hphi_weighted hdelta.le
    nlinarith
  have hepsilon_weighted :
      -epsilon * B ≤
        laplacian (I := I) (LeviCivita (I := I) g) g u x -
          g.inner x (gradFun (I := I) g f x)
            (gradientFun (I := I) g u x) := by
    have hmul := mul_le_mul_of_nonneg_right hdelta_le hB
    nlinarith
  refine ⟨x, hu_value, hu_norm, ?_⟩
  rw [weightedLaplacian_apply]
  have hbridge :
      laplacian (I := I) (LeviCivita (I := I) g) g u x =
        ΔG (I := I) g u x := by
    have h := laplacian_levi_eq (I := I) g u.contMDiff x
    have hu : (⟨(u : M → Real), u.contMDiff⟩ : C^∞⟮I, M; Real⟯) = u := by
      ext z
      rfl
    rw [hu] at h
    exact h
  rw [← hbridge]
  exact hepsilon_weighted

end DifferentialGeometry.Geometry.Operator
