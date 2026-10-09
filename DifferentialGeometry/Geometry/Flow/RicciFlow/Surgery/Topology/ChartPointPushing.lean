import DifferentialGeometry.Analysis.ODE.Flow.Planar.ConstantOutsideCompactFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ControlledExtinctionAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LocalClassRealizationTransport
import DifferentialGeometry.Topology.Manifold.BallChartPalaisTransport
import DifferentialGeometry.Topology.Manifold.IsotopyOrientation
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

noncomputable section

open Bundle Function Manifold Metric Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_diffeomorphIsotopy_translate_on_closedBall
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (a b : E) {r R : ℝ} (hr : 0 ≤ r) (hR : r + ‖b - a‖ < R) :
    ∃ D : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      D 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => D p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => (D p.1).symm p.2) ∧
      (∀ t, (D t).symm = D (-t)) ∧
      (∀ x ∈ closedBall a r, D 1 x = x + (b - a)) ∧
      ∀ t x, x ∉ closedBall a R → D t x = x := by
  obtain ⟨rIn, hrIn₁, hrIn₂⟩ := exists_between hR
  have hrIn_pos : 0 < rIn := lt_of_le_of_lt (add_nonneg hr (norm_nonneg _)) hrIn₁
  let β : ContDiffBump a := ⟨rIn, R, hrIn_pos, hrIn₂⟩
  let v : E → E := fun x => β x • (b - a)
  have hv : ContDiff ℝ ∞ v := β.contDiff.smul contDiff_const
  have hvc : HasCompactSupport v := β.hasCompactSupport.smul_right
  obtain ⟨D, hDc, hderiv, hzero, _hadd, hinv⟩ :=
    DifferentialGeometry.Analysis.exists_smoothFlow_of_eq_const_off_compact hv 0
      (by simpa using hvc)
  have hDci : ContDiff ℝ ∞ (fun p : ℝ × E => (D p.1).symm p.2) := by
    rw [show (fun p : ℝ × E => (D p.1).symm p.2) = (fun p : ℝ × E => D (-p.1) p.2)
      from funext fun p => by simp only [hinv]]
    have hneg : ContDiff ℝ ∞ (fun p : ℝ × E => (-p.1, p.2)) :=
      contDiff_fst.neg.prodMk contDiff_snd
    exact ContDiff.comp hDc hneg
  have hv_on : ∀ x ∈ closedBall a rIn, v x = b - a := fun x hx => by
    simp only [v, β.one_of_mem_closedBall hx, one_smul]
  have hsupport : tsupport v ⊆ closedBall a R := by
    have h1 : tsupport v ⊆ tsupport (β : E → ℝ) :=
      tsupport_smul_subset_left (β : E → ℝ) (fun _ : E => b - a)
    rw [β.tsupport_eq] at h1
    exact h1
  have hpoint : ∀ (t : ℝ) (x : E), x ∉ closedBall a R → D t x = x := by
    intro t x hx
    by_contra hne
    have hs := DifferentialGeometry.Analysis.tsupport_integralCurveFamily_sub_subset (v := v)
      (hv.of_le (by simp)) (Γ := fun y s => D s y) (fun y => by rw [hzero]; rfl) hderiv t
    exact hx (hsupport (hs (subset_closure (Function.mem_support.mpr (sub_ne_zero.mpr hne)))))
  have hclosed : ∀ x ∈ closedBall a r, D 1 x = x + (b - a) := by
    intro x hx
    have hxr : ‖x - a‖ ≤ r := by simpa [dist_eq_norm] using hx
    have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : x + t • (b - a) ∈ closedBall a rIn := by
      rw [mem_closedBall, dist_eq_norm]
      have hsplit : x + t • (b - a) - a = (x - a) + t • (b - a) := by abel
      rw [hsplit]
      have h1 : ‖(x - a) + t • (b - a)‖ ≤ ‖x - a‖ + ‖t • (b - a)‖ :=
        norm_add_le _ _
      have h2 : ‖t • (b - a)‖ = t * ‖b - a‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      have h3 : t * ‖b - a‖ ≤ ‖b - a‖ :=
        mul_le_of_le_one_left (norm_nonneg _) ht.2
      linarith
    have hγ : IsIntegralCurveOn (fun t : ℝ => x + t • (b - a)) (fun _ : ℝ => v)
        (Icc 0 1) := by
      intro t ht
      have hder : HasDerivAt (fun s : ℝ => x + s • (b - a)) (v (x + t • (b - a))) t := by
        rw [hv_on _ (hmem t ht)]
        simpa using (((hasDerivAt_id t).smul_const (b - a)).const_add x)
      exact hder.hasDerivWithinAt
    have hDcur : IsIntegralCurveOn (fun t : ℝ => D t x) (fun _ : ℝ => v) (Icc 0 1) :=
      fun t ht => (hderiv x t).hasDerivWithinAt
    have hinit : (fun t : ℝ => D t x) 0 = (fun t : ℝ => x + t • (b - a)) 0 := by
      simp only [hzero, Diffeomorph.coe_refl, id_eq, zero_smul, add_zero]
    have he := DifferentialGeometry.Analysis.ODE.Flow.orbit_unique_Icc hv
      (a := 0) (b := 1) hDcur hγ hinit
    have h1 := he ⟨zero_le_one, le_refl (1 : ℝ)⟩
    simpa using h1
  exact ⟨D, hzero, hDc, hDci, hinv, hclosed, hpoint⟩

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M]

theorem exists_diffeomorphIsotopy_apply_eq_of_mem_nhds [T2Space M] (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∀ z ∈ U,
      ∃ J : ℝ → Diffeomorph ThreeModel ThreeModel M M ∞,
        J 0 = Diffeomorph.refl ThreeModel M ∞ ∧
        ContMDiff ((𝓘(ℝ, ℝ)).prod ThreeModel) ThreeModel ∞
          (fun q : ℝ × M => J q.1 q.2) ∧
        J 1 x = z := by
  let φ : PartialDiffeomorph ThreeModel 𝓘(ℝ, ThreeSpace) M ThreeSpace ∞ :=
    PartialDiffeomorph.extChartAt ThreeModel ∞ x
  let e : OpenPartialHomeomorph M ThreeSpace := φ.toOpenPartialHomeomorph
  have hxsrc : x ∈ e.source := by
    dsimp only [e, φ, PartialDiffeomorph.extChartAt]
    exact mem_extChartAt_source x
  obtain ⟨R, hRpos, hRsub⟩ : ∃ R : ℝ, 0 < R ∧ closedBall (e x) R ⊆ e.target := by
    obtain ⟨ρ, hρpos, hρsub⟩ :=
      Metric.mem_nhds_iff.mp (e.open_target.mem_nhds (e.map_source hxsrc))
    exact ⟨ρ / 2, by linarith,
      fun y hy => hρsub (Metric.closedBall_subset_ball (by linarith) hy)⟩
  let U : Set M := e.source ∩ e ⁻¹' ball (e x) R
  have hUopen : IsOpen U := by simpa only [U] using e.isOpen_inter_preimage isOpen_ball
  have hxU : x ∈ U := ⟨hxsrc, mem_ball_self hRpos⟩
  refine ⟨U, hUopen, hxU, ?_⟩
  rintro z ⟨hzsrc, hzball⟩
  have hznorm : ‖e z - e x‖ < R := by
    simpa only [Set.mem_preimage, mem_ball, dist_eq_norm] using hzball
  obtain ⟨D, hD0, hDc, hDci, hinv, hmove, hpoint⟩ :=
    exists_diffeomorphIsotopy_translate_on_closedBall (e x) (e z) (r := 0) (R := R) le_rfl
      (by simpa using hznorm)
  obtain ⟨J, hJc, -, hJ, -, -, -⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_diffeomorph_extension_of_partial_chart_family
      e φ.contMDiffOn_toFun φ.contMDiffOn_invFun D hDc hDci
      (isCompact_closedBall (e x) R) hRsub
      (fun t y hy => ⟨hpoint t y hy, by rw [hinv t]; exact hpoint (-t) y hy⟩)
  have hD1 : D 1 (e x) = e z := by
    have h := hmove (e x) (mem_closedBall_self le_rfl)
    simpa using h
  have hJ0 : J 0 = Diffeomorph.refl ThreeModel M ∞ := by
    refine Diffeomorph.ext fun y => ?_
    rw [(hJ 0 y).1, hD0]
    rw [DifferentialGeometry.Topology.Manifold.extendChartById]
    by_cases hy : y ∈ e.source
    · rw [ite_eq_left hy, Diffeomorph.coe_refl, id_eq, e.left_inv hy]
      rfl
    · rw [ite_eq_right hy]
      rfl
  have hJx : J 1 x = z := by
    rw [(hJ 1 x).1, DifferentialGeometry.Topology.Manifold.extendChartById, ite_eq_left hxsrc, hD1,
      e.left_inv hzsrc]
  exact ⟨J, hJ0, hJc, hJx⟩

omit [IsManifold ThreeModel ∞ M] in
theorem homotopic_id_of_isotopy_from_refl {J : ℝ → Diffeomorph ThreeModel ThreeModel M M ∞}
    (hJ0 : J 0 = Diffeomorph.refl ThreeModel M ∞)
    (hJc : ContMDiff ((𝓘(ℝ, ℝ)).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × M => J q.1 q.2)) :
    (⟨⇑(J 1), (J 1).continuous⟩ : C(M, M)).Homotopic (ContinuousMap.id M) := by
  refine ⟨⟨⟨fun p : unitInterval × M => J (1 - (p.1 : ℝ)) p.2, ?_⟩, ?_, ?_⟩⟩
  · exact hJc.continuous.comp
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd)
  · intro y
    change (J (1 - ((0 : unitInterval) : ℝ))) y = (J 1) y
    norm_num
  · intro y
    change (J (1 - ((1 : unitInterval) : ℝ))) y = y
    rw [show ((1 : unitInterval) : ℝ) = 1 by norm_num, sub_self, hJ0, Diffeomorph.coe_refl]
    rfl

theorem preservesTangentOrientation_of_preservesManifoldOrientation
    {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N]
    (oM : TangentOrientationSection M) (oN : TangentOrientationSection N)
    (f : M ≃ₘ⟮ThreeModel, ThreeModel⟯ N)
    (h : f.preservesOrientation oM.toManifoldOrientation oN.toManifoldOrientation) :
    PreservesTangentOrientation oM oN f := by
  refine ⟨f.contMDiff, fun x => ?_⟩
  have hbij : Function.Bijective (mfderiv ThreeModel ThreeModel (⇑f) x) := by
    have hcoe := Diffeomorph.mfderivToContinuousLinearEquiv_coe f
      (show (∞ : ℕ∞ω) ≠ 0 from by simp) (x := x)
    rw [← hcoe]
    exact (f.mfderivToContinuousLinearEquiv (by simp) x).bijective
  refine ⟨hbij, ?_⟩
  unfold PreservesTangentOrientationAt
  rw [← mfderivToContinuousLinearEquiv_toLinearEquiv_eq_ofBijective f x hbij]
  exact h x

theorem localClassTransport_of_preconnectedSpace [T2Space M] [PreconnectedSpace M]
    (o : TangentOrientationSection M) : localClassTransport o := by
  intro x
  obtain ⟨U, hUopen, hxU, hloc⟩ := exists_diffeomorphIsotopy_apply_eq_of_mem_nhds (M := M) x
  refine ⟨U, hUopen, hxU, fun y hy => ?_⟩
  obtain ⟨J, hJ0, hJc, hJx⟩ := hloc y hy
  exact ⟨J 1, hJx, homotopic_id_of_isotopy_from_refl hJ0 hJc,
    localOrientationClass_natural_diffeomorph o o (J 1)
      (preservesTangentOrientation_of_preservesManifoldOrientation o o (J 1)
        (preservesOrientation_of_jointlySmooth_isotopy o.toManifoldOrientation J hJ0 hJc 1)) x⟩

theorem localClassRealizationLocallyConstant_of_preconnectedSpace [T2Space M]
    [PreconnectedSpace M] (o : TangentOrientationSection M) :
    localClassRealizationLocallyConstant o :=
  localClassRealizationLocallyConstant_of_localClassTransport o
    (localClassTransport_of_preconnectedSpace o)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
