import DifferentialGeometry.Geometry.Comparison.Nonnegative.RauchFocal
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Velocity

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Metric Set
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace



omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M] in
theorem contMDiffWithinAt_smul_section
    {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
    {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
    {b : P → M} (v : ∀ p : P, TangentSpace I (b p)) (f : P → ℝ)
    {s : Set P} {p₀ : P} {n : WithTop ℕ∞}
    (hf : ContMDiffWithinAt IP 𝓘(ℝ, ℝ) n f s p₀)
    (hv : ContMDiffWithinAt IP I.tangent n
      (fun p : P => TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (b p) (v p)) s p₀) :
    ContMDiffWithinAt IP I.tangent n
      (fun p : P => TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (b p) (f p • v p)) s p₀ := by
  classical
  rw [contMDiffWithinAt_totalSpace] at hv ⊢
  refine ⟨hv.1, ?_⟩
  have hmem₀ : b p₀ ∈ (trivializationAt E (TangentSpace I) (b p₀)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' (b p₀)
  have hbase : ∀ᶠ p in 𝓝[s] p₀,
      b p ∈ (trivializationAt E (TangentSpace I) (b p₀)).baseSet :=
    hv.1.continuousWithinAt.preimage_mem_nhdsWithin
      ((trivializationAt E (TangentSpace I) (b p₀)).open_baseSet.mem_nhds hmem₀)
  refine (hf.smul hv.2).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hbase] with p hp
    exact ((trivializationAt E (TangentSpace I) (b p₀)).linear ℝ hp).map_smul
      (f p) (v p)
  · exact ((trivializationAt E (TangentSpace I) (b p₀)).linear ℝ hmem₀).map_smul
      (f p₀) (v p₀)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M] in
theorem contMDiffOn_smul_section
    {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
    {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
    {b : P → M} (v : ∀ p : P, TangentSpace I (b p)) (f : P → ℝ)
    {s : Set P} {n : WithTop ℕ∞}
    (hf : ContMDiffOn IP 𝓘(ℝ, ℝ) n f s)
    (hv : ContMDiffOn IP I.tangent n
      (fun p : P => TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (b p) (v p)) s) :
    ContMDiffOn IP I.tangent n
      (fun p : P => TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (b p) (f p • v p)) s :=
  fun p₀ hp₀ =>
    contMDiffWithinAt_smul_section (I := I) v f (hf p₀ hp₀) (hv p₀ hp₀)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M] in
theorem contMDiff_smul_section
    {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
    {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
    {b : P → M} (v : ∀ p : P, TangentSpace I (b p)) (f : P → ℝ)
    {n : WithTop ℕ∞}
    (hf : ContMDiff IP 𝓘(ℝ, ℝ) n f)
    (hv : ContMDiff IP I.tangent n
      (fun p : P => TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (b p) (v p))) :
    ContMDiff IP I.tangent n
      (fun p : P => TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (b p) (f p • v p)) := by
  rw [← contMDiffOn_univ] at hf hv ⊢
  exact contMDiffOn_smul_section (I := I) v f hf hv

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M] in
theorem differentiableAt_chartRepAt_of_contMDiff (γ : ℝ → M)
    (V : ∀ t : ℝ, TangentSpace I (γ t))
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t : ℝ => TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (γ t) (V t))) (t : ℝ) :
    DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t := by
  have hsplit := Bundle.contMDiffAt_totalSpace.mp (hV t)
  have hnbd : ∀ᶠ s in 𝓝 t,
      γ s ∈ (trivializationAt E (TangentSpace I) (γ t)).baseSet :=
    hsplit.1.continuousAt.preimage_mem_nhds
      ((Trivialization.open_baseSet _).mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I) (γ t)))
  have heq : chartRepAt (I := I) γ V t =ᶠ[𝓝 t]
      (fun s : ℝ => (trivializationAt E (TangentSpace I) (γ t)
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ s) (V s))).2) := by
    filter_upwards [hnbd] with s hs
    change (trivializationAt E (TangentSpace I) (γ t)).linearMapAt ℝ (γ s) (V s) = _
    rw [Trivialization.coe_linearMapAt_of_mem _ hs]
  exact ((contMDiffAt_iff_contDiffAt.mp hsplit.2).differentiableAt
    (by simp)).congr_of_eventuallyEq heq

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]



omit [ConnectedSpace M] in
theorem contMDiffOn_parallelShift (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (y : M) (u : TangentSpace I y)
    (ξ : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t))
    {L : ℝ} (hL : 0 < L)
    (hξ : IsParallelPerpUnitField (I := I) g hEnorm y u ξ L) (h : ℝ) :
    ContMDiffOn 𝓘(ℝ, ℝ) I ∞
      (parallelShift (I := I) g hEnorm y u ξ h) (Icc 0 L) := by
  classical
  obtain ⟨δ, hδ, V, hVeq, -, hVsmooth⟩ :=
    exists_smooth_eq_of_isParallelPerpUnitField (I := I) g hEnorm y u ξ hL hξ
  have hsub : Icc (0 : ℝ) L ⊆ Ioo (-δ) (L + δ) := fun t ht =>
    ⟨by linarith [ht.1, hδ], by linarith [ht.2, hδ]⟩
  have hscaled : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t : ℝ => TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (intrinsicGeodesic (I := I) g hEnorm y u t) (h • V t)) (Icc 0 L) :=
    (contMDiffOn_smul_section (I := I) V (fun _ : ℝ => h) contMDiffOn_const
      hVsmooth).mono hsub
  have hexp : ContMDiffOn 𝓘(ℝ, ℝ) I ∞
      (fun t : ℝ => expMapIntrinsic (I := I) g hEnorm
        (intrinsicGeodesic (I := I) g hEnorm y u t) (h • V t)) (Icc 0 L) :=
    (intrinsicExp_smooth (I := I) g hEnorm).comp_contMDiffOn hscaled
  refine hexp.congr (fun t ht => ?_)
  rw [parallelShift, hVeq t ht]

omit [ConnectedSpace M] in
theorem hasParallelVariationC1 (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) :
    HasParallelVariationC1 (I := I) g hEnorm := by
  intro _ L hL
  refine ⟨1, one_pos, fun y _ u _ ξ hξ h _ _ => ?_⟩
  exact (contMDiffOn_parallelShift (I := I) g hEnorm y u ξ hL hξ h).of_le
    (by exact_mod_cast le_top)



omit [ConnectedSpace M] in
theorem exists_smooth_isParallelPerpUnitField (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (y : M) (u : TangentSpace I y)
    (ξ : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t))
    {L : ℝ} (hL : 0 < L)
    (hξ : IsParallelPerpUnitField (I := I) g hEnorm y u ξ L) :
    ∃ W : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t),
      (∀ t ∈ Icc (0 : ℝ) L, W t = ξ t) ∧
      IsParallelPerpUnitField (I := I) g hEnorm y u W L ∧
      ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
        (fun t : ℝ => TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (intrinsicGeodesic (I := I) g hEnorm y u t) (W t)) := by
  classical
  obtain ⟨δ, hδ, V, hVeq, hVpar, hVsmooth⟩ :=
    exists_smooth_eq_of_isParallelPerpUnitField (I := I) g hEnorm y u ξ hL hξ
  set bump : ContDiffBump (L / 2 : ℝ) :=
    { rIn := L / 2 + δ / 4
      rOut := L / 2 + δ / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith } with hbump
  set χ : ℝ → ℝ := fun t => bump t with hχdef
  set W : ∀ t : ℝ,
      TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t) :=
    fun t => χ t • V t with hWdef
  have hχsm : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ χ :=
    contMDiff_iff_contDiff.mpr bump.contDiff
  have hrIn : bump.rIn = L / 2 + δ / 4 := rfl
  have hrOut : bump.rOut = L / 2 + δ / 2 := rfl
  have hone : ∀ t ∈ Ioo (-(δ / 4)) (L + δ / 4), χ t = 1 := by
    intro t ht
    refine bump.one_of_mem_closedBall ?_
    rw [mem_closedBall, Real.dist_eq, abs_le, hrIn]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hIccsub : Icc (0 : ℝ) L ⊆ Ioo (-(δ / 4)) (L + δ / 4) := fun t ht =>
    ⟨by linarith [ht.1, hδ], by linarith [ht.2, hδ]⟩
  have hWV : ∀ t ∈ Ioo (-(δ / 4)) (L + δ / 4), W t = V t := by
    intro t ht
    simp only [hWdef, hone t ht, one_smul]
  have hWnhds : ∀ t ∈ Icc (0 : ℝ) L, ∀ᶠ s in 𝓝 t, W s = V s := by
    intro t ht
    filter_upwards [isOpen_Ioo.mem_nhds (hIccsub ht)] with s hs
    exact hWV s hs
  have hWξ : ∀ t ∈ Icc (0 : ℝ) L, W t = ξ t := by
    intro t ht
    rw [hWV t (hIccsub ht), hVeq t ht]
  have hτsm : ContMDiff 𝓘(ℝ, ℝ) I ∞ (intrinsicGeodesic (I := I) g hEnorm y u) :=
    intrinsicGeodesic_contMDiff (I := I) g hEnorm y u
  have hWsm : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t : ℝ => TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (intrinsicGeodesic (I := I) g hEnorm y u t) (W t)) := by
    intro t₀
    by_cases ht₀ : t₀ ∈ Ioo (-δ) (L + δ)
    · exact (contMDiffOn_smul_section (I := I) V χ hχsm.contMDiffOn
        hVsmooth).contMDiffAt (isOpen_Ioo.mem_nhds ht₀)
    · have hzero : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent ∞
          (fun t : ℝ => TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (intrinsicGeodesic (I := I) g hEnorm y u t)
            (0 : TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t))) t₀ :=
        ((Bundle.contMDiff_zeroSection ℝ
          (TangentSpace I (M := M))).comp hτsm).contMDiffAt
      refine hzero.congr_of_eventuallyEq ?_
      have hfar : ∀ᶠ t in 𝓝 t₀, bump.rOut ≤ dist t (L / 2) := by
        rcases not_and_or.1 ht₀ with hlt | hlt
        · have hle : t₀ ≤ -δ := le_of_not_gt hlt
          filter_upwards [Iio_mem_nhds (show t₀ < -(δ / 2) from by linarith)] with t ht
          have hlt' : t < -(δ / 2) := ht
          rw [Real.dist_eq, abs_of_nonpos (by linarith), hrOut]
          linarith
        · have hle : L + δ ≤ t₀ := le_of_not_gt hlt
          filter_upwards [Ioi_mem_nhds (show L + δ / 2 < t₀ from by linarith)] with t ht
          have hlt' : L + δ / 2 < t := ht
          rw [Real.dist_eq, abs_of_nonneg (by linarith), hrOut]
          linarith
      filter_upwards [hfar] with t ht
      have : χ t = 0 := bump.zero_of_le_dist ht
      rw [hWdef]
      simp only [this, zero_smul]
  refine ⟨W, hWξ, ⟨fun t _ => differentiableAt_chartRepAt_of_contMDiff (I := I) _
    W hWsm t, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩, hWsm⟩
  · rw [covDerivAlong_congr_of_eventuallyEq (I := I) g _ (hWnhds t ht)]
    exact hVpar t ⟨by linarith [ht.1, hδ], by linarith [ht.2, hδ]⟩
  · rw [hWξ t ht]; exact hξ.2.2.1 t ht
  · rw [hWξ t ht]; exact hξ.2.2.2 t ht

omit [ConnectedSpace M] in
theorem contMDiff_parallelShift (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (y : M) (u : TangentSpace I y)
    (W : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t))
    (hW : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t : ℝ => TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (intrinsicGeodesic (I := I) g hEnorm y u t) (W t))) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
      (fun p : ℝ × ℝ => parallelShift (I := I) g hEnorm y u W p.2 p.1) := by
  have hpair : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I.tangent ∞
      (fun p : ℝ × ℝ => TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (intrinsicGeodesic (I := I) g hEnorm y u p.1) (p.2 • W p.1)) :=
    contMDiff_smul_section (I := I) (fun p : ℝ × ℝ => W p.1)
      (fun p : ℝ × ℝ => p.2) contMDiff_snd (hW.comp contMDiff_fst)
  exact (intrinsicExp_smooth (I := I) g hEnorm).comp hpair

omit [ConnectedSpace M] in
theorem isSmoothVariation_parallelShift (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (y : M) (u : TangentSpace I y)
    (W : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t))
    (hW : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t : ℝ => TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (intrinsicGeodesic (I := I) g hEnorm y u t) (W t))) :
    IsSmoothVariation (I := I)
      (fun t h : ℝ => parallelShift (I := I) g hEnorm y u W h t) :=
  (contMDiff_parallelShift (I := I) g hEnorm y u W hW).of_le ENat.LEInfty.out

end DifferentialGeometry.Geometry.Topology

end
