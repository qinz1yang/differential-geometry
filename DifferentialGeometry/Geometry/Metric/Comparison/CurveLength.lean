import DifferentialGeometry.Geometry.Comparison.Variation.Curve.PathLength
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open DifferentialGeometry.Geometry.Riemannian
open scoped ENNReal Manifold ContDiff Topology Bundle

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_le_arcLength
    (g : SmoothRiemannianMetric I M) {x : Real → M} {a b : Real}
    (hab : a ≤ b)
    (hx : ContMDiffOn 𝓘(Real, Real) I 1 x (Icc a b)) :
    riemannianEDistOf (I := I) g (x a) (x b) ≤
      ENNReal.ofReal (Variation.arcLength (I := I) g x a b) := by
  let : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
    ⟨g.toRiemannianMetric⟩
  change riemannianEDist I (x a) (x b) ≤ _
  apply Geometry.Riemannian.Geodesic.riemannianEDist_le_arcLength
    (I := I) g hab hx
  intro t _ht
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  congr 2


attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_riemannianEDistOf_le_mul_abs_sub
    (g : SmoothRiemannianMetric I M) {x : Real → M} {a b : Real}
    (hx : ContMDiffOn 𝓘(Real, Real) I 1 x (Icc a b)) :
    ∃ C : NNReal, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      riemannianEDistOf (I := I) g (x s) (x t) ≤
        ENNReal.ofReal ((C : Real) * |t - s|) := by
  classical
  by_cases hab : a ≤ b
  swap
  · refine ⟨0, ?_⟩
    intro s hs
    exact False.elim (hab (hs.1.trans hs.2))
  rcases hab.eq_or_lt with rfl | hab
  · refine ⟨(0 : NNReal), ?_⟩
    intro s hs t ht
    have hs' : s = a := le_antisymm hs.2 hs.1
    have ht' : t = a := le_antisymm ht.2 ht.1
    subst s
    subst t
    simp only [riemannianEDistOf_self, ENNReal.ofReal_zero, sub_self,
      abs_zero, NNReal.coe_zero, zero_mul]
    exact le_rfl
  · have hUnique : UniqueMDiffOn 𝓘(Real, Real) (Icc a b) := by
      intro u hu
      rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact (uniqueDiffOn_Icc hab) u hu
    let v : (u : Real) → TangentSpace I (x u) := fun u ↦
      mfderivWithin 𝓘(Real, Real) I x (Icc a b) u (1 : Real)
    have hTan := hx.continuousOn_tangentMapWithin (le_refl 1) hUnique
    have hunit : Continuous (fun u : Real ↦
        (⟨u, (1 : Real)⟩ : TangentBundle 𝓘(Real, Real) Real)) := by
      exact (tangentBundleModelSpaceHomeomorph 𝓘(Real, Real)).symm.continuous.comp
        (continuous_id.prodMk continuous_const)
    have hunitMaps : MapsTo
        (fun u : Real ↦ (⟨u, (1 : Real)⟩ : TangentBundle 𝓘(Real, Real) Real))
        (Icc a b) (Bundle.TotalSpace.proj ⁻¹' Icc a b) := by
      intro u hu
      simpa using hu
    have hvel : ContinuousOn
        (fun u : Real ↦ TotalSpace.mk' E
          (E := fun y : M ↦ TangentSpace I y) (x u) (v u)) (Icc a b) := by
      exact (hTan.comp hunit.continuousOn hunitMaps).congr (fun _ _ ↦ rfl)
    let cg : Bundle.ContinuousRiemannianMetric E
        (fun y : M ↦ TangentSpace I y) := g.toContinuousRiemannianMetric
    let rb : Bundle.RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
      ⟨cg.toRiemannianMetric⟩
    have hquad : ContinuousOn (fun u ↦ g.inner (x u) (v u) (v u))
        (Icc a b) := by
      have h := ContinuousOn.inner_bundle (F := E) (B := M)
        (E := fun y : M ↦ TangentSpace I y) (b := x) (v := v) (w := v)
        (s := Icc a b) hvel hvel
      exact h.congr (fun _ _ ↦ rfl)
    let speedW : Real → Real := fun u ↦ Real.sqrt (g.inner (x u) (v u) (v u))
    have hspeedW : ContinuousOn speedW (Icc a b) := by
      exact Real.continuous_sqrt.comp_continuousOn hquad
    obtain ⟨C0, hC0⟩ := isCompact_Icc.bddAbove_image hspeedW
    let C : NNReal := ⟨max C0 0, le_max_right _ _⟩
    have hboundW : ∀ u ∈ Icc a b, speedW u ≤ (C : Real) := by
      intro u hu
      exact (hC0 ⟨u, hu, rfl⟩).trans (le_max_left _ _)
    refine ⟨C, ?_⟩
    have hforward : ∀ {s t : Real}, s ∈ Icc a b → t ∈ Icc a b → s ≤ t →
        riemannianEDistOf (I := I) g (x s) (x t) ≤
          ENNReal.ofReal ((C : Real) * |t - s|) := by
      intro s t hs ht hst
      let speed : Real → Real := fun u ↦ Real.sqrt
        (g.inner (x u)
          (mfderiv 𝓘(Real, Real) I x u (1 : Real))
          (mfderiv 𝓘(Real, Real) I x u (1 : Real)))
      have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
      have hspeedWInt : IntervalIntegrable speedW volume s t :=
        (hspeedW.mono hsub).intervalIntegrable_of_Icc hst
      have heq : ∀ᵐ u ∂(volume.restrict (uIoc s t)), speedW u = speed u := by
        have hmem : ∀ᵐ u ∂(volume.restrict (uIoc s t)), u ∈ Ioo s t := by
          rw [uIoc_of_le hst, ← restrict_Ioo_eq_restrict_Ioc]
          exact ae_restrict_mem measurableSet_Ioo
        filter_upwards [hmem] with u hu
        have huab : u ∈ Ioo a b :=
          ⟨hs.1.trans_lt hu.1, hu.2.trans_le ht.2⟩
        have hv : v u = mfderiv 𝓘(Real, Real) I x u (1 : Real) := by
          dsimp only [v]
          exact congrArg (fun A ↦ A (1 : Real))
            (mfderivWithin_of_mem_nhds (I := 𝓘(Real, Real)) (I' := I)
              (f := x) (s := Icc a b)
              (Icc_mem_nhds huab.1 huab.2))
        simp only [speedW, speed, hv]
      have hspeedInt : IntervalIntegrable speed volume s t :=
        hspeedWInt.congr_ae heq
      have hpoint : ∀ u ∈ Ioo s t, speed u ≤ (C : Real) := by
        intro u hu
        have huab : u ∈ Ioo a b :=
          ⟨hs.1.trans_lt hu.1, hu.2.trans_le ht.2⟩
        have huIcc : u ∈ Icc a b := ⟨huab.1.le, huab.2.le⟩
        have hv : v u = mfderiv 𝓘(Real, Real) I x u (1 : Real) := by
          dsimp only [v]
          exact congrArg (fun A ↦ A (1 : Real))
            (mfderivWithin_of_mem_nhds (I := 𝓘(Real, Real)) (I' := I)
              (f := x) (s := Icc a b)
              (Icc_mem_nhds huab.1 huab.2))
        simpa only [speedW, speed, hv] using hboundW u huIcc
      have hlen : Variation.arcLength (I := I) g x s t ≤
          (C : Real) * (t - s) := by
        unfold Variation.arcLength
        have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hst
          hspeedInt intervalIntegrable_const hpoint
        simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
          using hmono
      have hcurve : ContMDiffOn 𝓘(Real, Real) I 1 x (Icc s t) :=
        hx.mono hsub
      calc
        riemannianEDistOf (I := I) g (x s) (x t)
            ≤ ENNReal.ofReal (Variation.arcLength (I := I) g x s t) :=
          riemannianEDistOf_le_arcLength (I := I) g hst hcurve
        _ ≤ ENNReal.ofReal ((C : Real) * (t - s)) := ENNReal.ofReal_le_ofReal hlen
        _ = ENNReal.ofReal ((C : Real) * |t - s|) := by
          rw [abs_of_nonneg (sub_nonneg.mpr hst)]
    intro s hs t ht
    by_cases hst : s ≤ t
    · exact hforward hs ht hst
    · have hcomm : riemannianEDistOf (I := I) g (x s) (x t) =
          riemannianEDistOf (I := I) g (x t) (x s) := by
        change riemannianEDist I (x s) (x t) = riemannianEDist I (x t) (x s)
        exact riemannianEDist_comm
      rw [hcomm]
      simpa only [abs_sub_comm] using hforward ht hs (le_of_not_ge hst)

end DifferentialGeometry
