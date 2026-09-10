import DifferentialGeometry.Geometry.Comparison.Volume.PolarExpansion
import Mathlib.Analysis.Calculus.Taylor

set_option autoImplicit false

noncomputable section

open Set Function Bundle Manifold
open scoped Topology Manifold ContDiff

namespace Poincare.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem iteratedDeriv_radial_eq_iteratedFDeriv_apply
    {F : E → ℝ} {U : Set E} (hU : IsOpen U)
    {n : ℕ} (hF : ContDiffOn ℝ n F U)
    {u : E} {t : ℝ} (ht : t • u ∈ U) :
    iteratedDeriv n (fun s : ℝ ↦ F (s • u)) t =
      iteratedFDeriv ℝ n F (t • u) (fun _ ↦ u) := by
  let L : ℝ →L[ℝ] E := ContinuousLinearMap.toSpanSingleton ℝ u
  have hLU : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have htLU : t ∈ L ⁻¹' U := by
    simpa only [Set.mem_preimage, L, ContinuousLinearMap.toSpanSingleton_apply]
      using ht
  have hcomp : iteratedFDerivWithin ℝ n (F ∘ L) (L ⁻¹' U) t =
      (iteratedFDerivWithin ℝ n F U (L t)).compContinuousLinearMap
        (fun _ ↦ L) :=
    L.iteratedFDerivWithin_comp_right hF hU.uniqueDiffOn
      hLU.uniqueDiffOn ht le_rfl
  rw [iteratedFDerivWithin_of_isOpen n hLU htLU,
    iteratedFDerivWithin_of_isOpen n hU htLU] at hcomp
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change iteratedFDeriv ℝ n (F ∘ L) t (fun _ ↦ (1 : ℝ)) = _
  rw [hcomp]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, L,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul]

theorem exists_uniform_radial_taylor_remainder
    {F : E → ℝ} {U : Set E} (hU : IsOpen U) (h0U : (0 : E) ∈ U)
    (hF : ContDiffOn ℝ 3 F U)
    (a : ℝ) (q : E → ℝ)
    (hzero : F 0 = a)
    (hfirst : ∀ u : Metric.sphere (0 : E) 1,
      iteratedDeriv 1 (fun t : ℝ ↦ F (t • (u : E))) 0 = 0)
    (hsecond : ∀ u : Metric.sphere (0 : E) 1,
      iteratedDeriv 2 (fun t : ℝ ↦ F (t • (u : E))) 0 = q u) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : Metric.sphere (0 : E) 1) (t : ℝ),
        t ∈ Set.Icc 0 ρ →
          |F (t • (u : E)) - (a + (q u / 2) * t ^ 2)| ≤ C * t ^ 3 := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU 0 h0U
  let ρ : ℝ := ε / 2
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  have hclosedU : Metric.closedBall (0 : E) ρ ⊆ U :=
    (Metric.closedBall_subset_ball (by dsimp only [ρ]; linarith)).trans hεU
  have hD3cont : ContinuousOn (fun z : E ↦ ‖iteratedFDeriv ℝ 3 F z‖)
      (Metric.closedBall (0 : E) ρ) :=
    ((ContinuousOn.continuousOn_iteratedFDeriv hF hU le_rfl).norm).mono hclosedU
  have hD3bdd : BddAbove
      ((fun z : E ↦ ‖iteratedFDeriv ℝ 3 F z‖) ''
        Metric.closedBall (0 : E) ρ) :=
    (isCompact_closedBall (0 : E) ρ).bddAbove_image hD3cont
  obtain ⟨B, hB⟩ := bddAbove_def.mp hD3bdd
  let B0 : ℝ := max 0 B
  have hB0 : 0 ≤ B0 := le_max_left 0 B
  have hD3le : ∀ z ∈ Metric.closedBall (0 : E) ρ,
      ‖iteratedFDeriv ℝ 3 F z‖ ≤ B0 := by
    intro z hz
    exact (hB _ ⟨z, hz, rfl⟩).trans (le_max_right 0 B)
  refine ⟨ρ, hρ, B0 / 2, div_nonneg hB0 (by norm_num), ?_⟩
  intro u t ht
  let L : ℝ →L[ℝ] E := ContinuousLinearMap.toSpanSingleton ℝ (u : E)
  have hu_norm : ‖(u : E)‖ = 1 := by
    have hu := u.property
    rw [Metric.mem_sphere, dist_zero_right] at hu
    exact hu
  have hmaps : Set.Icc 0 ρ ⊆ L ⁻¹' U := by
    intro s hs
    apply hclosedU
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖s • (u : E)‖ ≤ ρ
    rw [norm_smul, Real.norm_eq_abs, hu_norm, mul_one, abs_of_nonneg hs.1]
    exact hs.2
  have hradial : ContDiffOn ℝ 3 (fun s : ℝ ↦ F (s • (u : E)))
      (Set.Icc 0 ρ) := by
    have hcomp : ContDiffOn ℝ 3 (F ∘ L) (L ⁻¹' U) :=
      hF.comp_continuousLinearMap L
    exact (hcomp.mono hmaps).congr fun s _ ↦ by
      simp only [Function.comp_apply, L,
        ContinuousLinearMap.toSpanSingleton_apply]
  have hthird : ∀ s ∈ Set.Icc 0 ρ,
      ‖iteratedDerivWithin 3 (fun x : ℝ ↦ F (x • (u : E)))
        (Set.Icc 0 ρ) s‖ ≤ B0 := by
    intro s hs
    have hsU : s • (u : E) ∈ U := hmaps hs
    have hsCont : ContDiffAt ℝ 3 (fun x : ℝ ↦ F (x • (u : E))) s := by
      have hpreopen : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
      have hsPre : s ∈ L ⁻¹' U := hmaps hs
      have hcomp : ContDiffOn ℝ 3 (F ∘ L) (L ⁻¹' U) :=
        hF.comp_continuousLinearMap L
      have := hcomp.contDiffAt (hpreopen.mem_nhds hsPre)
      exact this.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun x ↦ by
          simp only [Function.comp_apply, L,
            ContinuousLinearMap.toSpanSingleton_apply])
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hρ) hsCont hs]
    rw [iteratedDeriv_radial_eq_iteratedFDeriv_apply hU hF hsU]
    refine (iteratedFDeriv ℝ 3 F (s • (u : E))).le_opNorm
      (fun _ ↦ (u : E)) |>.trans ?_
    rw [Finset.prod_const, Finset.card_fin, hu_norm, one_pow, mul_one]
    apply hD3le
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      hu_norm, mul_one, abs_of_nonneg hs.1]
    exact hs.2
  have htaylor := taylor_mean_remainder_bound (n := 2) hρ.le hradial ht hthird
  have hpreopen : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have hzeroPre : (0 : ℝ) ∈ L ⁻¹' U := by
    simpa only [Set.mem_preimage, map_zero] using h0U
  have hcomp : ContDiffOn ℝ 3 (F ∘ L) (L ⁻¹' U) :=
    hF.comp_continuousLinearMap L
  have hzeroCont3 : ContDiffAt ℝ 3
      (fun x : ℝ ↦ F (x • (u : E))) 0 := by
    have hz := hcomp.contDiffAt (hpreopen.mem_nhds hzeroPre)
    exact hz.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x ↦ by
        simp only [Function.comp_apply, L,
          ContinuousLinearMap.toSpanSingleton_apply])
  have hzeroCont : ContDiffAt ℝ 2 (fun x : ℝ ↦ F (x • (u : E))) 0 :=
    hzeroCont3.of_le (by norm_num)
  have hfirstWithin : iteratedDerivWithin 1
      (fun x : ℝ ↦ F (x • (u : E))) (Set.Icc 0 ρ) 0 = 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hρ)
      (hzeroCont.of_le (by norm_num)) (show (0 : ℝ) ∈ Set.Icc 0 ρ from
        ⟨le_rfl, hρ.le⟩)]
    exact hfirst u
  have hsecondWithin : iteratedDerivWithin 2
      (fun x : ℝ ↦ F (x • (u : E))) (Set.Icc 0 ρ) 0 = q u := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hρ)
      hzeroCont (show (0 : ℝ) ∈ Set.Icc 0 ρ from ⟨le_rfl, hρ.le⟩)]
    exact hsecond u
  have hpoly : taylorWithinEval (fun x : ℝ ↦ F (x • (u : E))) 2
      (Set.Icc 0 ρ) 0 t = a + (q u / 2) * t ^ 2 := by
    norm_num [taylorWithinEval_succ, hzero, hfirstWithin, hsecondWithin]
    ring
  rw [hpoly, Real.norm_eq_abs] at htaylor
  convert htaylor using 1
  ring

variable [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]
variable [RiemannianBundle (fun x : M => TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem normalExpJacobian_uniform_taylor_remainder_of_radial_jets
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (hjets : ∀ u : Metric.sphere (0 : E) 1,
      iteratedDeriv 1
          (fun t : ℝ ↦ normalExpJacobian (I := I) g hEnorm p
            (t • (u : E))) 0 = 0 ∧
      iteratedDeriv 2
          (fun t : ℝ ↦ normalExpJacobian (I := I) g hEnorm p
            (t • (u : E))) 0 =
        -(1 / 3 : ℝ) * ricciTensor (I := I) g p
          (normalFrame (I := I) g p (u : E))
          (normalFrame (I := I) g p (u : E))) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : Metric.sphere (0 : E) 1) (t : ℝ),
        t ∈ Set.Icc 0 ρ →
          |normalExpJacobian (I := I) g hEnorm p (t • (u : E)) -
            (1 - (1 / 6 : ℝ) * ricciTensor (I := I) g p
              (normalFrame (I := I) g p (u : E))
              (normalFrame (I := I) g p (u : E)) * t ^ 2)| ≤
            C * t ^ 3 := by
  let U : Set E := {z : E | normalFrame (I := I) g p z ∈
    SegmentInt (I := I) g hEnorm p}
  have hU : IsOpen U := by
    exact (isOpen_segInt (I := I) g hEnorm p).preimage
      (normalFrame (I := I) (E := E) g p).continuous
  have h0U : (0 : E) ∈ U := by
    change normalFrame (I := I) g p (0 : E) ∈
      SegmentInt (I := I) g hEnorm p
    refine ⟨2, by norm_num, ?_⟩
    simpa only [map_zero, smul_zero] using
      (segmentDom_zero (I := I) g hEnorm p)
  have hJ : ContDiffOn ℝ 3
      (normalExpJacobian (I := I) g hEnorm p) U :=
    (normalExpJacobian_contDiffOn_segInt
      (I := I) g hEnorm p).of_le (by norm_cast)
  let q : E → ℝ := fun u ↦ -(1 / 3 : ℝ) * ricciTensor (I := I) g p
    (normalFrame (I := I) g p u) (normalFrame (I := I) g p u)
  obtain ⟨ρ, hρ, C, hC, hrem⟩ := exists_uniform_radial_taylor_remainder
    hU h0U hJ 1 q (normalExpJacobian_zero (I := I) g hEnorm p)
    (fun u ↦ (hjets u).1) (fun u ↦ by simpa only [q] using (hjets u).2)
  refine ⟨ρ, hρ, C, hC, fun u t ht ↦ ?_⟩
  have hcoeff : 1 + (q (u : E) / 2) * t ^ 2 =
      1 - (1 / 6 : ℝ) * ricciTensor (I := I) g p
        (normalFrame (I := I) g p (u : E))
        (normalFrame (I := I) g p (u : E)) * t ^ 2 := by
    dsimp only [q]
    ring
  rw [← hcoeff]
  exact hrem u t ht

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem normalPolarJacobian_uniform_taylor_remainder_of_radial_jets
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (hjets : ∀ u : Metric.sphere (0 : E) 1,
      iteratedDeriv 1
          (fun t : ℝ ↦ normalExpJacobian (I := I) g hEnorm p
            (t • (u : E))) 0 = 0 ∧
      iteratedDeriv 2
          (fun t : ℝ ↦ normalExpJacobian (I := I) g hEnorm p
            (t • (u : E))) 0 =
        -(1 / 3 : ℝ) * ricciTensor (I := I) g p
          (normalFrame (I := I) g p (u : E))
          (normalFrame (I := I) g p (u : E))) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : Metric.sphere (0 : E) 1) (t : ℝ),
        t ∈ Set.Icc 0 ρ →
          |normalPolarJacobian (I := I) g hEnorm p t u -
            t ^ (Module.finrank ℝ E - 1) *
              (1 - (1 / 6 : ℝ) * ricciTensor (I := I) g p
                (normalFrame (I := I) g p (u : E))
                (normalFrame (I := I) g p (u : E)) * t ^ 2)| ≤
            C * t ^ (Module.finrank ℝ E - 1) * t ^ 3 := by
  obtain ⟨ρ, hρ, C, hC, hrem⟩ :=
    normalExpJacobian_uniform_taylor_remainder_of_radial_jets
      (I := I) g hEnorm p hjets
  refine ⟨ρ, hρ, C, hC, fun u t ht ↦ ?_⟩
  let A : ℝ := 1 - (1 / 6 : ℝ) * ricciTensor (I := I) g p
    (normalFrame (I := I) g p (u : E))
    (normalFrame (I := I) g p (u : E)) * t ^ 2
  have hpow : 0 ≤ t ^ (Module.finrank ℝ E - 1) := pow_nonneg ht.1 _
  calc
    |normalPolarJacobian (I := I) g hEnorm p t u -
        t ^ (Module.finrank ℝ E - 1) * A| =
        t ^ (Module.finrank ℝ E - 1) *
          |normalExpJacobian (I := I) g hEnorm p (t • (u : E)) - A| := by
            rw [normalPolarJacobian_eq, ← mul_sub, abs_mul,
              abs_of_nonneg hpow]
    _ ≤ t ^ (Module.finrank ℝ E - 1) * (C * t ^ 3) :=
      mul_le_mul_of_nonneg_left (hrem u t ht) hpow
    _ = C * t ^ (Module.finrank ℝ E - 1) * t ^ 3 := by ring

end Poincare.Geometry.Riemannian.VolumeComparison

end
