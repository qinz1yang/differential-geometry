import DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.FluxBounds
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletSmoothMulDerivative
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletNirenbergDerivative
import DifferentialGeometry.Analysis.Elliptic.MetricDensity

noncomputable section

open Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Operator

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace M := borel _
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

omit [T2Space M] [CompactSpace M] in
private theorem continuousOn_chart_inverse_partial
    (α : M) {Ω : Set EuStd}
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (φ : C^∞⟮I_hs, M; ℝ⟯) (j : Fin (Module.finrank ℝ EuN)) :
    ContinuousOn (fun z => fderiv ℝ (fun y => φ ((extChartAt I_hs α).symm
      ((toEuclidean (E := EuN)).symm y))) z (EuclideanSpace.single j 1)) (closure Ω) := by
  let U := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hU : IsOpen U := (toEuclidean (E := EuN)).isOpenMap _ isOpen_interior
  have hP : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => φ ((extChartAt I_hs α).symm
      ((toEuclidean (E := EuN)).symm y))) U := by
    apply (scalarOnE_contDiffOn α φ.contMDiff).comp
      (toEuclidean (E := EuN)).symm.contDiff.contDiffOn
    rintro z ⟨y, hy, rfl⟩
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using interior_subset hy
  exact ((((hP.fderiv_of_isOpen hU (m := (⊤ : ℕ∞)) (by simp)).clm_apply
    (g := fun _ => EuclideanSpace.single j 1) contDiffOn_const).continuousOn).mono hΩs)

private theorem dirichletLocalWeakPartialLp_smoothMul_dirichletNirenbergTest_expanded
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (φ : C^∞⟮I_hs, M; ℝ⟯)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k j : Fin (Module.finrank ℝ EuN)) (s : ℝ)
    (hηs : Metric.cthickening |s| (tsupport η) ⊆ Ω) (v : H1ComplDirichlet q) :
    let P := fun z => φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
    let V := fun z => H1ComplDirichletToLp q v
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
    let D := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs
    (D j (smoothMulH1ComplDirichlet q φ
      (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k s hηs v)) : EuStd → ℝ) =ᵐ[volume.restrict Ω]
      fun z => P z * Sobolev.diffQuot k (-s) (fun y =>
        (η y)^2 * Sobolev.diffQuot k s (D j v) y +
          2 * η y * fderiv ℝ η y (EuclideanSpace.single j 1) * Sobolev.diffQuot k s V y) z +
        fderiv ℝ P z (EuclideanSpace.single j 1) * nirenbergTestFunction k s η V z := by
  intro P V D
  let w := dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k s hηs v
  filter_upwards [dirichletLocalWeakPartialLp_smoothMulH1ComplDirichlet q α hΩ hΩc hΩs φ j w,
    dirichletLocalWeakPartialLp_dirichletNirenbergTest_expanded q α hΩ hΩc hΩs hη hηc k j s hηs v,
    dirichletNirenbergTest_chartInverse_coeFn q α hΩ hΩc hΩs v hη hηc k s hηs] with z hz hd hv
  rw [hz, hd, hv]

private theorem integral_local_dirichlet_nirenberg_flux_eq
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (φ : C^∞⟮I_hs, M; ℝ⟯)
    (hφ : ∀ z ∈ Ω, densityOnEuclid q α z *
      φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) = 1)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k i j : Fin (Module.finrank ℝ EuN)) (s : ℝ)
    (hηs : Metric.cthickening |s| (tsupport η) ⊆ Ω) (u v : H1ComplDirichlet q)
    (A : EuStd → ℝ) (hA : ContinuousOn A (closure Ω)) :
    let P := fun z => φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
    let V := fun z => H1ComplDirichletToLp q v
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
    let D := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs
    let C := fun z => densityOnEuclid q α z * A z
    let R := fun z => C z * fderiv ℝ P z (EuclideanSpace.single j 1)
    (-(∫ z in Ω, D i u z * C z *
      D j (smoothMulH1ComplDirichlet q φ
        (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k s hηs v)) z)) =
      (∫ z, (Sobolev.translate k s A z * Sobolev.diffQuot k s (D i u) z +
        Sobolev.diffQuot k s A z * D i u z) *
          ((η z)^2 * Sobolev.diffQuot k s (D j v) z +
            2 * η z * fderiv ℝ η z (EuclideanSpace.single j 1) * Sobolev.diffQuot k s V z)) +
      ∫ z, (Sobolev.translate k s R z * Sobolev.diffQuot k s (D i u) z +
        Sobolev.diffQuot k s R z * D i u z) * ((η z)^2 * Sobolev.diffQuot k s V z) := by
  intro P V D C R
  let w := dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k s hηs v
  have hA' : MemLp A ∞ (volume.restrict Ω) :=
    hA.memLp_top_of_subset_isCompact hΩc hΩ.measurableSet subset_closure
  have hC : ContinuousOn C (closure Ω) :=
    ((densityOnEuclid_contDiffOn q α).continuousOn.mono
      (hΩs.trans (image_mono interior_subset))).mul hA
  have hR : MemLp R ∞ (volume.restrict Ω) :=
    (hC.mul (continuousOn_chart_inverse_partial α hΩs φ j)).memLp_top_of_subset_isCompact
      hΩc hΩ.measurableSet subset_closure
  have hfirst : MemLp (fun z => A z * D i u z) 2 (volume.restrict Ω) :=
    (Lp.memLp (D i u)).mul' (r := 2) hA'
  have hsecond : MemLp (fun z => R z * D i u z) 2 (volume.restrict Ω) :=
    (Lp.memLp (D i u)).mul' (r := 2) hR
  have hV : MemLp V 2 (volume.restrict Ω) :=
    (memWkp_chartInverse_H1ComplDirichletToLp q α hΩ hΩc hΩs v).memLp
  have hCP : EqOn (fun z => C z * P z) A Ω := by
    intro z hz
    dsimp only [C, P]
    calc
      _ = (densityOnEuclid q α z *
        φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) * A z := by ring
      _ = A z := by rw [hφ z hz, one_mul]
  have hi := integral_normalized_multiplier_nirenberg_flux_eq_local hΩ.measurableSet
    hfirst hCP hsecond hV (Lp.memLp (D j v)) hη hηc k j s hηs
  apply Eq.trans ?_ hi
  apply congrArg Neg.neg
  apply integral_congr_ae
  exact (dirichletLocalWeakPartialLp_smoothMul_dirichletNirenbergTest_expanded
    q α hΩ hΩc hΩs φ hη hηc k j s hηs v).mono fun z hz =>
      congrArg (fun r => D i u z * C z * r) hz

private theorem integral_local_dirichlet_nirenberg_sum_eq
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (φ : C^∞⟮I_hs, M; ℝ⟯)
    (hφ : ∀ z ∈ Ω, densityOnEuclid q α z *
      φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) = 1)
    (A : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → EuStd → ℝ)
    (hA : ∀ i j, ContinuousOn (A i j) (closure Ω))
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k : Fin (Module.finrank ℝ EuN)) (s : ℝ)
    (hηs : Metric.cthickening |s| (tsupport η) ⊆ Ω) (u : H1ComplDirichlet q) :
    let P := fun z => φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
    let U := fun z => H1ComplDirichletToLp q u
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
    let D := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs
    let R := fun i j z => (densityOnEuclid q α z * A i j z) *
      fderiv ℝ P z (EuclideanSpace.single j 1)
    (∑ i, ∑ j, ((∫ z, (Sobolev.translate k s (A i j) z * Sobolev.diffQuot k s (D i u) z +
        Sobolev.diffQuot k s (A i j) z * D i u z) *
          ((η z)^2 * Sobolev.diffQuot k s (D j u) z +
            2 * η z * fderiv ℝ η z (EuclideanSpace.single j 1) * Sobolev.diffQuot k s U z)) +
      ∫ z, (Sobolev.translate k s (R i j) z * Sobolev.diffQuot k s (D i u) z +
        Sobolev.diffQuot k s (R i j) z * D i u z) * ((η z)^2 * Sobolev.diffQuot k s U z))) =
      -∑ i, ∑ j, ∫ z in Ω, D i u z * (densityOnEuclid q α z * A i j z) *
        D j (smoothMulH1ComplDirichlet q φ (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k s hηs u)) z := by
  intro P U D R
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun j _ => (integral_local_dirichlet_nirenberg_flux_eq q α hΩ hΩc hΩs φ hφ
        hη hηc k i j s hηs u u (A i j) (hA i j)).symm))
  simpa only [Finset.sum_neg_distrib] using hs


theorem local_dirichlet_nirenberg_lower_bound
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (φ : C^∞⟮I_hs, M; ℝ⟯)
    (hφ : ∀ z ∈ Ω, densityOnEuclid q α z *
      φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) = 1)
    (A : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → EuStd → ℝ)
    (hA : ∀ i j, ContinuousOn (A i j) (closure Ω))
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k : Fin (Module.finrank ℝ EuN)) (s : ℝ)
    (hηs : Metric.cthickening |s| (tsupport η) ⊆ Ω) (u : H1ComplDirichlet q)
    (hηb : ∀ z, |η z| ≤ 1) {lam L : ℝ} (hlam : 0 < lam) (hL : 0 ≤ L) :
    let P := fun z => φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
    let U := fun z => H1ComplDirichletToLp q u
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
    let D := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs
    let R := fun i j z => (densityOnEuclid q α z * A i j z) *
      fderiv ℝ P z (EuclideanSpace.single j 1)
    (∀ y ∈ Ω, ∀ ξ : Fin (Module.finrank ℝ EuN) → ℝ,
      lam * ∑ i, (ξ i)^2 ≤ ∑ i, ∑ j, A i j y * ξ i * ξ j) →
    (∀ i j z, z ∈ tsupport η → |Sobolev.translate k s (A i j) z| ≤ L ∧
      |Sobolev.diffQuot k s (A i j) z| ≤ L) →
    (∀ i j z, z ∈ tsupport η → |Sobolev.translate k s (R i j) z| ≤ L ∧
      |Sobolev.diffQuot k s (R i j) z| ≤ L) →
    (∀ j z, z ∈ tsupport η → |fderiv ℝ η z (EuclideanSpace.single j 1)| ≤ L) →
    let d : ℝ := Module.finrank ℝ EuN
    let ε := lam / (2 * (3 * d + 1))
    let Cg := d * ((4 * ε)⁻¹ * L^2 + L^4) + d * (L^2 / 2) + L^2 / 2
    let Cw := d^2 * (ε⁻¹ * L^4 + 1) + d^2 * ((4 * ε)⁻¹ * L^2 + 1/2) +
      d * ((4 * ε)⁻¹ * L^2 + 1/2)
    let C := max 0 (max Cg Cw)
    0 ≤ C ∧ lam / 2 * (∑ i, ∫ z, (η z * Sobolev.diffQuot k s (D i u) z)^2) ≤
      -(∑ i, ∑ j, ∫ z in Ω, D i u z * (densityOnEuclid q α z * A i j z) *
        D j (smoothMulH1ComplDirichlet q φ
          (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k s hηs u)) z) +
      C * ((∑ i, ∫ z in tsupport η, (D i u z)^2) + ∫ z in tsupport η, (Sobolev.diffQuot k s U z)^2) := by
  intro P U D R hcoer hAL hRL hηd d ε Cg Cw C
  have hU : MemLp U 2 (volume.restrict Ω) :=
    (memWkp_chartInverse_H1ComplDirichletToLp q α hΩ hΩc hΩs u).memLp
  have hRcont (i j) : ContinuousOn (R i j) Ω :=
    ((((densityOnEuclid_contDiffOn q α).continuousOn.mono
      (hΩs.trans (image_mono interior_subset))).mul (hA i j)).mul
        (continuousOn_chart_inverse_partial α hΩs φ j)).mono subset_closure
  have hflux := integral_nirenberg_flux_lower_bound_local hΩ.measurableSet hU
    (fun i => Lp.memLp (D i u)) (fun i j => (hA i j).mono subset_closure)
    hRcont (B := fun _ _ => 0) (fun _ => continuousOn_const) hη hηc hηb hlam hcoer k s 0 hηs
    hAL hRL (fun _ _ _ => by
      change |(0 : ℝ)| ≤ L ∧ |Sobolev.diffQuot k s (0 : EuStd → ℝ) _| ≤ L
      simpa only [Sobolev.diffQuot_zero, Pi.zero_apply, abs_zero] using And.intro hL hL) hηd
  have htzero : Sobolev.translate k s (fun _ : EuStd => (0 : ℝ)) = (0 : EuStd → ℝ) := rfl
  have hzero : Sobolev.diffQuot k s (fun _ : EuStd => (0 : ℝ)) = (0 : EuStd → ℝ) :=
    Sobolev.diffQuot_zero k s
  simp only [htzero, hzero, Pi.zero_apply, zero_mul, add_zero,
    integral_zero, Finset.sum_const_zero, sub_zero, abs_zero] at hflux
  refine ⟨hflux.1, ?_⟩
  have hsum := integral_local_dirichlet_nirenberg_sum_eq q α hΩ hΩc hΩs φ hφ
    A hA hη hηc k s hηs u
  rw [hsum] at hflux
  exact hflux.2

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
