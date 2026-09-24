import DifferentialGeometry.Geometry.Metric.Family.Continuity
import DifferentialGeometry.Geometry.Coordinates.Frame.Chart
import DifferentialGeometry.Geometry.Metric.Pullback.Cross
import DifferentialGeometry.Bundle.PartialMfderiv.Parameter

noncomputable section

open Bundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Operator (chartGramOnE)
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Parameter

variable {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]

theorem metricCLMSection_jointContMDiffOn_of_local_coefficients {n : ℕ∞ω}
    (g : P → SmoothRiemannianMetric I M) (J : Set P)
    (hg : ∀ p : M, ∀ t ∈ J,
      ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
        U ⊆ (trivializationAt E (TangentSpace I) p).baseSet ∧
      ∃ V : Set P, IsOpen V ∧ t ∈ V ∧
      ∃ A : P × M → E → E → ℝ,
        (∀ v w, ContMDiffOn (IP.prod I) 𝓘(ℝ) n
          (fun q => A q v w) (V ×ˢ U)) ∧
        ∀ s ∈ V ∩ J, ∀ y ∈ U, ∀ v w,
          A (s, y) v w = (g s).inner y
            ((trivializationAt E (TangentSpace I) p).symmL ℝ y v)
            ((trivializationAt E (TangentSpace I) p).symmL ℝ y w)) :
    ContMDiffOn (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun q : P × M => (⟨q.2, (g q.1).inner q.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (J ×ˢ (Set.univ : Set M)) := by
  intro q hq
  obtain ⟨U, hU, hxU, hUb, V, hV, htV, A, hA, heq⟩ := hg q.2 q.1 hq.1
  rw [contMDiffWithinAt_hom_bundle]
  refine ⟨contMDiffWithinAt_snd, ?_⟩
  apply contMDiffWithinAt_clm_of_pointwise
  intro v
  apply contMDiffWithinAt_clm_of_pointwise
  intro w
  have hs : ContMDiffWithinAt (IP.prod I) 𝓘(ℝ) n
      (fun z : P × M => A z v w) (J ×ˢ Set.univ) q :=
    (hA v w q ⟨htV, hxU⟩).mono_of_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds ((hV.prod hU).mem_nhds ⟨htV, hxU⟩))
  have hin (s : P) (y : M) (hy : y ∈ U) (hs : s ∈ V ∩ J) :
      ContinuousLinearMap.inCoordinates E (TangentSpace I)
        (E →L[ℝ] ℝ) (fun y : M => TangentSpace I y →L[ℝ] ℝ)
        q.2 y q.2 y ((g s).inner y) v w = A (s, y) v w := by
    have hyR : y ∈ (trivializationAt ℝ (Bundle.Trivial M ℝ) q.2).baseSet := Set.mem_univ y
    rw [inCoordinates_apply_eq₂ (𝕜 := ℝ)
      (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (E₁ := TangentSpace I) (E₂ := TangentSpace I) (E₃ := Bundle.Trivial M ℝ)
      (x₀ := q.2) (x := y) (ϕ := (g s).inner y) (v := v) (w := w)
      (hUb hy) (hUb hy) hyR]
    rw [(trivializationAt ℝ (Bundle.Trivial M ℝ) q.2).coe_linearMapAt_of_mem hyR]
    simp only [Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.trivialization_apply]
    rw [← Trivialization.symmL_apply (R := ℝ) _ (hUb hy) v,
      ← Trivialization.symmL_apply (R := ℝ) _ (hUb hy) w]
    exact (heq s hs y hy v w).symm
  apply hs.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds ((hV.prod hU).mem_nhds ⟨htV, hxU⟩)] with z hz hzu
    exact hin z.1 z.2 hzu.2 ⟨hzu.1, hz.1⟩
  · exact hin q.1 q.2 hxU ⟨htV, hq.1⟩

theorem chartGramMatrix_joint_contMDiffOn {n : ℕ∞}
    (g : P → SmoothRiemannianMetric I M) (J : Set P)
    (hg : ContMDiffOn (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun p : P × M => (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (J ×ˢ (Set.univ : Set M)))
    (x₀ : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (IP.prod I) 𝓘(ℝ) n
      (fun p : P × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
      (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  have hmetric := hg.mono (fun p hp => ⟨hp.1, Set.mem_univ p.2⟩ :
    J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet ⊆ J ×ˢ Set.univ)
  have hsnd : ContMDiffOn (IP.prod I) I n (Prod.snd : P × M → M)
      (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := contMDiffOn_snd
  have hv := ((chartBasisVec_contMDiffOn (I := I) x₀ i).of_le (WithTop.coe_le_coe.mpr le_top)).comp hsnd (fun p hp => hp.2)
  have hw := ((chartBasisVec_contMDiffOn (I := I) x₀ j).of_le (WithTop.coe_le_coe.mpr le_top)).comp hsnd (fun p hp => hp.2)
  have happ := ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
    (E₁ := TangentSpace I (M := M)) (E₂ := TangentSpace I (M := M))
    (E₃ := Bundle.Trivial M ℝ) (b := fun p : P × M => p.2) hmetric hv hw
  intro p hp
  have h := happ p hp
  rw [Bundle.contMDiffWithinAt_totalSpace] at h
  exact h.2

end Parameter

section NormedParameter

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

private theorem chartGramOnE_contDiffOn_of_chartGram {n : ℕ∞}
    (g : P → SmoothRiemannianMetric I M) (A : Set P) (x : M)
    (i j : Fin (Module.finrank ℝ E))
    (hgram : ContMDiffOn (𝓘(ℝ, P).prod I) 𝓘(ℝ) n
      (fun p : P × M => chartGramMatrix (g p.1) x p.2 i j)
      (A ×ˢ (trivializationAt E (TangentSpace I) x).baseSet)) :
    ContDiffOn ℝ n (fun p : P × E => chartGramOnE (g p.1) x i j p.2)
      (A ×ˢ (extChartAt I x).target) := by
  have harg : ContMDiffOn (𝓘(ℝ, P).prod 𝓘(ℝ, E)) (𝓘(ℝ, P).prod I) n
      (fun p : P × E => (p.1, (extChartAt I x).symm p.2))
      (A ×ˢ (extChartAt I x).target) :=
    contMDiffOn_fst.prodMk ((contMDiffOn_extChartAt_symm x).comp contMDiffOn_snd
      (fun p hp => hp.2))
  have hh := hgram.comp harg (fun p hp =>
    ⟨hp.1, extChartAt_symm_mem_trivializationAt_baseSet x hp.2⟩)
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hh
  exact hh.contDiffOn

theorem chartGramOnE_joint_contDiffOn {n : ℕ∞}
    (g : P → SmoothRiemannianMetric I M) (A : Set P)
    (hg : ContMDiffOn (𝓘(ℝ, P).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun p : P × M => (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (A ×ˢ (Set.univ : Set M)))
    (x : M) (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ n (fun p : P × E => chartGramOnE (g p.1) x i j p.2)
      (A ×ˢ (extChartAt I x).target) :=
  chartGramOnE_contDiffOn_of_chartGram g A x i j
    (chartGramMatrix_joint_contMDiffOn g A hg x i j)

end NormedParameter

omit [FiniteDimensional ℝ E] in
private theorem metric_coeff_contDiffOn {n : ℕ∞ω}
    (J : Set ℝ) (g : ℝ → SmoothRiemannianMetric I M)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (J ×ˢ (Set.univ : Set M))) :
    ∀ x (X Y : TangentSpace I x),
      ContDiffOn ℝ n (fun t : ℝ => (g t).inner x X Y) J := by
  intro x X Y
  have hcurve : ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) n
      (fun t : ℝ => (t, x)) J := contMDiffOn_id.prodMk contMDiffOn_const
  have hmetric := hg.comp hcurve (fun t ht => ⟨ht, Set.mem_univ x⟩)
  have hv : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E)) n
      (fun _ : ℝ => TotalSpace.mk' E (E := TangentSpace I) x X) J :=
    contMDiffOn_const
  have hw : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E)) n
      (fun _ : ℝ => TotalSpace.mk' E (E := TangentSpace I) x Y) J :=
    contMDiffOn_const
  have happ := ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
    (E₁ := TangentSpace I (M := M)) (E₂ := TangentSpace I (M := M))
    (E₃ := Bundle.Trivial M ℝ) (b := fun _ : ℝ => x) hmetric hv hw
  have hscalar : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) n
      (fun t : ℝ => (g t).inner x X Y) J := by
    intro t ht
    have hpt := happ t ht
    rw [Bundle.contMDiffWithinAt_totalSpace] at hpt
    exact hpt.2
  exact hscalar.contDiffOn

omit [FiniteDimensional ℝ E] in
private theorem metric_frame_contMDiffOn
    (J : Set ℝ) (g : ℝ → SmoothRiemannianMetric I M)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (J ×ˢ (Set.univ : Set M)))
    {Idx : Type} (frame : Idx → (x : M) → TangentSpace I x) {u : Set M}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u) (i j : Idx) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (g p.1).inner p.2 (frame i p.2) (frame j p.2))
      (J ×ˢ u) := by
  have hmetric := hg.mono (fun p hp => ⟨hp.1, Set.mem_univ p.2⟩ :
    J ×ˢ u ⊆ J ×ˢ Set.univ)
  have hv : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' E p.2 (frame i p.2)) (J ×ˢ u) :=
    (hframe.contMDiffOn i).comp contMDiffOn_snd (fun p hp => hp.2)
  have hw : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' E p.2 (frame j p.2)) (J ×ˢ u) :=
    (hframe.contMDiffOn j).comp contMDiffOn_snd (fun p hp => hp.2)
  have happ := ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
    (E₁ := TangentSpace I (M := M)) (E₂ := TangentSpace I (M := M))
    (E₃ := Bundle.Trivial M ℝ) (b := fun p : ℝ × M => p.2) hmetric hv hw
  intro p hp
  have hpt := happ p hp
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpt
  exact hpt.2

theorem metricFamilySmoothOn_of_contMDiffOn
    (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I M)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (D.carrier ×ˢ (Set.univ : Set M))) :
    MetricFamilySmoothOn (I := I) (M := M) D g := by
  have hcoeff := metric_coeff_contDiffOn D.carrier g hg
  refine ⟨fun x X Y => (hcoeff x X Y).mono D.regular_subset,
    fun x X Y => (hcoeff x X Y).continuousOn, ?_, ?_⟩
  · apply metricTensorCont_of_chartGram (K := D.carrier) g
    intro x₀ i j
    have hincl : ContinuousOn
        (fun q : {t : ℝ // t ∈ D.carrier} × M => ((q.1 : ℝ), q.2))
        {q : {t : ℝ // t ∈ D.carrier} × M |
          q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet} :=
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousOn
    have hgram := (chartGramMatrix_joint_contMDiffOn g D.carrier hg x₀ i j).continuousOn
    have h := hgram.comp hincl (fun q hq => ⟨q.1.2, hq⟩)
    exact h
  · intro Idx _ frame u hframe i j
    exact (metric_frame_contMDiffOn D.carrier g hg frame hframe i j).mono
      (Set.prod_mono D.regular_subset Set.Subset.rfl)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

section Parametric

variable {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP 1 P]

omit [FiniteDimensional ℝ E] in
theorem chartGramMatrix_joint_contMDiffOn_of_parametric_pullback {n : ℕ∞}
    (g : P → SmoothRiemannianMetric I M) (A : Set P)
    (hg : ContMDiffOn (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun p : P × M => (⟨p.2, (g p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (A ×ˢ (Set.univ : Set M)))
    (h : P → SmoothRiemannianMetric J N) (Y : P → N → M)
    (hY : ContMDiff (IP.prod J) I ((n : ℕ∞ω) + 1) (Function.uncurry Y))
    (hinner : ∀ t ∈ A, ∀ x (u v : TangentSpace J x),
      (h t).inner x u v = (g t).inner (Y t x)
        (mfderiv J I (Y t) x u) (mfderiv J I (Y t) x v))
    (x₀ : N) (i j : Fin (Module.finrank ℝ F)) :
    ContMDiffOn (IP.prod J) 𝓘(ℝ) n
      (fun p : P × N => chartGramMatrix (I := J) (h p.1) x₀ p.2 i j)
      (A ×ˢ (trivializationAt F (TangentSpace J) x₀).baseSet) := by
  have hmap : ContMDiff (IP.prod J) (IP.prod I) n
      (fun p : P × N => (p.1, Y p.1 p.2)) :=
    contMDiff_fst.prodMk (hY.of_le (le_add_of_nonneg_right zero_le_one))
  have hmetric := hg.comp hmap.contMDiffOn (fun p hp => ⟨hp.1, Set.mem_univ _⟩ :
    Set.MapsTo (fun p : P × N => (p.1, Y p.1 p.2))
      (A ×ˢ (trivializationAt F (TangentSpace J) x₀).baseSet)
      (A ×ˢ (Set.univ : Set M)))
  have hvec (k : Fin (Module.finrank ℝ F)) :
      ContMDiffOn (IP.prod J) (I.prod 𝓘(ℝ, E)) n
        (fun p : P × N => TotalSpace.mk' E (E := TangentSpace I)
          (Y p.1 p.2) (mfderiv J I (Y p.1) p.2 (chartBasisVecFiber (I := J) x₀ k p.2)))
        (A ×ˢ (trivializationAt F (TangentSpace J) x₀).baseSet) := by
    intro p hp
    have hv := (chartBasisVec_contMDiffOn (I := J) x₀ k).contMDiffAt
      ((trivializationAt F (TangentSpace J) x₀).open_baseSet.mem_nhds hp.2)
    exact (hY.contMDiffAt.partial_mfderiv_apply
      ((hv.of_le (WithTop.coe_le_coe.mpr le_top)).comp p contMDiffAt_snd) le_rfl).contMDiffWithinAt
  have happ := ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
    (E₁ := TangentSpace I (M := M)) (E₂ := TangentSpace I (M := M))
    (E₃ := Bundle.Trivial M ℝ) (b := fun p : P × N => Y p.1 p.2)
    hmetric (hvec i) (hvec j)
  intro p hp
  have hs := happ p hp
  rw [Bundle.contMDiffWithinAt_totalSpace] at hs
  have heq : (fun q : P × N => chartGramMatrix (I := J) (h q.1) x₀ q.2 i j)
      =ᶠ[nhdsWithin p (A ×ˢ (trivializationAt F (TangentSpace J) x₀).baseSet)]
      (fun q : P × N => (g q.1).inner (Y q.1 q.2)
        (mfderiv J I (Y q.1) q.2 (chartBasisVecFiber (I := J) x₀ i q.2))
        (mfderiv J I (Y q.1) q.2 (chartBasisVecFiber (I := J) x₀ j q.2))) := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact hinner q.1 hq.1 q.2 _ _
  exact hs.2.congr_of_eventuallyEq heq (hinner p.1 hp.1 p.2 _ _)

omit [FiniteDimensional ℝ E] in
theorem chartGramMatrix_pullback_joint_contMDiffOn [T2Space N] {n : ℕ∞}
    (g : P → SmoothRiemannianMetric I M) (A : Set P)
    (hg : ContMDiffOn (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun p : P × M => (⟨p.2, (g p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (A ×ˢ (Set.univ : Set M)))
    (Y : P → N ≃ₘ⟮J, I⟯ M)
    (hY : ContMDiff (IP.prod J) I ((n : ℕ∞ω) + 1) (fun p : P × N => Y p.1 p.2))
    (x₀ : N) (i j : Fin (Module.finrank ℝ F)) :
    ContMDiffOn (IP.prod J) 𝓘(ℝ) n
      (fun p : P × N => chartGramMatrix (I := J)
        (Diffeomorph.pullbackMetricCross (g p.1) (Y p.1)) x₀ p.2 i j)
      (A ×ˢ (trivializationAt F (TangentSpace J) x₀).baseSet) :=
  chartGramMatrix_joint_contMDiffOn_of_parametric_pullback g A hg
    (fun t => Diffeomorph.pullbackMetricCross (g t) (Y t)) (fun t => Y t) hY
    (fun t _ x u v => Diffeomorph.pullbackMetricCross_inner (g t) (Y t) x u v) x₀ i j

end Parametric
section NormedParameterPullback

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [FiniteDimensional ℝ E] in
theorem chartGramOnE_pullback_joint_contDiffOn [T2Space N] {n : ℕ∞}
    (g : P → SmoothRiemannianMetric I M) (A : Set P)
    (hg : ContMDiffOn (𝓘(ℝ, P).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun p : P × M => (⟨p.2, (g p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (A ×ˢ (Set.univ : Set M)))
    (Y : P → N ≃ₘ⟮J, I⟯ M)
    (hY : ContMDiff (𝓘(ℝ, P).prod J) I ((n : ℕ∞ω) + 1) (fun p : P × N => Y p.1 p.2))
    (x₀ : N) (i j : Fin (Module.finrank ℝ F)) :
    ContDiffOn ℝ n
      (fun p : P × F => chartGramOnE (I := J)
        (Diffeomorph.pullbackMetricCross (g p.1) (Y p.1)) x₀ i j p.2)
      (A ×ˢ (extChartAt J x₀).target) :=
  chartGramOnE_contDiffOn_of_chartGram
    (fun p => Diffeomorph.pullbackMetricCross (g p) (Y p)) A x₀ i j
    (chartGramMatrix_pullback_joint_contMDiffOn g A hg Y hY x₀ i j)

end NormedParameterPullback


omit [FiniteDimensional ℝ E] in
theorem chartGramMatrix_joint_contMDiffOn_of_pullback
    (g : ℝ → SmoothRiemannianMetric I M) (A : Set ℝ)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (A ×ˢ (Set.univ : Set M)))
    (h : ℝ → SmoothRiemannianMetric J N) (Y : N → M) (hY : ContMDiff J I ∞ Y)
    (hinner : ∀ t ∈ A, ∀ x (u v : TangentSpace J x),
      (h t).inner x u v = (g t).inner (Y x) (mfderiv J I Y x u) (mfderiv J I Y x v))
    (x₀ : N) (i j : Fin (Module.finrank ℝ F)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ) ∞
      (fun p : ℝ × N => chartGramMatrix (I := J) (h p.1) x₀ p.2 i j)
      (A ×ˢ (trivializationAt F (TangentSpace J) x₀).baseSet) := by
  exact chartGramMatrix_joint_contMDiffOn_of_parametric_pullback g A hg h (fun _ => Y)
    (hY.comp contMDiff_snd) hinner x₀ i j

theorem metricCLMSection_jointContMDiffOn_restrictOpenOfSubset
    {U V : TopologicalSpace.Opens M} [T2Space V] (hVU : V ≤ U)
    (g : ℝ → SmoothRiemannianMetric I U) (A : Set ℝ)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × U => (⟨q.2, (g q.1).inner q.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (A ×ˢ (Set.univ : Set U))) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × V => (⟨q.2, ((g q.1).restrictOpenOfSubset hVU).inner q.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (A ×ˢ (Set.univ : Set V)) := by
  let _ : IsManifold I 1 V := IsManifold.of_le (n := ∞) (by decide)
  apply metricCLMSection_jointContMDiffOn_of_chartGram_on
    (fun t => (g t).restrictOpenOfSubset hVU) A
  intro p i j
  refine chartGramMatrix_joint_contMDiffOn_of_pullback g A hg
    (fun t => (g t).restrictOpenOfSubset hVU)
    (TopologicalSpace.Opens.inclusion hVU) (contMDiff_inclusion hVU) ?_ p i j
  intro t _ x v w
  rw [SmoothRiemannianMetric.restrictSubset_inner, mfderiv_opens_incl]
  rfl

theorem metricTensorField_contDiffOn_time {n : ℕ∞ω}
    (g : ℝ → SmoothRiemannianMetric I M) (A : Set ℝ)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun q : ℝ × M => (⟨q.2, (g q.1).inner q.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (A ×ˢ Set.univ)) (x : M) :
    ContDiffOn ℝ n (fun t => Tensor0SBundle.metricTensorField (g t) x) A := by
  classical
  let b := Module.finBasis ℝ (TangentSpace I x)
  have hc (slots : Fin 2 → Fin (Module.finrank ℝ (TangentSpace I x))) :
      ContDiffOn ℝ n
        (fun t => Tensor0SBundle.component0S b (Tensor0SBundle.metricTensorField (g t) x) slots) A :=
    metric_coeff_contDiffOn A g hg x (b (slots 0)) (b (slots 1))
  have hsum : ContDiffOn ℝ n
      (fun t => ∑ slots, Tensor0SBundle.component0S b
        (Tensor0SBundle.metricTensorField (g t) x) slots •
          Tensor0SBundle.tensor0SBasis b 2 slots) A :=
    ContDiffOn.sum fun slots _ => (hc slots).smul_const _
  simpa only [← Tensor0SBundle.tensor0SBasis_repr, Module.Basis.sum_repr] using hsum


end DifferentialGeometry.Geometry.Curvature
