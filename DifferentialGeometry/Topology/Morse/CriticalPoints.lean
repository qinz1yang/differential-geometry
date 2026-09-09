import DifferentialGeometry.Topology.Morse.Manifold
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.DiscreteSubset
import Mathlib.Geometry.Manifold.LocalDiffeomorph

open scoped Topology

namespace DifferentialGeometry.Topology.Morse

open Filter Manifold Set

noncomputable section

section Naturality

open scoped Manifold ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type} [TopologicalSpace N] [ChartedSpace G N]

theorem isCriticalPointAt_comp_iff
    {φ : M → N} {f : N → ℝ} {x : M}
    (hφ : MDifferentiableAt I J φ x)
    (hf : MDifferentiableAt J 𝓘(ℝ, ℝ) f (φ x))
    (hsurj : Function.Surjective (mfderiv I J φ x)) :
    IsCriticalPointAt I (f ∘ φ) x ↔ IsCriticalPointAt J f (φ x) := by
  unfold IsCriticalPointAt
  rw [mfderiv_comp x hf hφ]
  constructor
  · intro h
    ext v
    obtain ⟨w, rfl⟩ := hsurj v
    exact congrArg (fun L => L w) h
  · intro h
    rw [h, ContinuousLinearMap.zero_comp]

theorem isCriticalPointAt_comp_diffeomorph_iff
    (Φ : M ≃ₘ⟮I, J⟯ N) {f : N → ℝ} (x : M)
    (hf : MDifferentiableAt J 𝓘(ℝ, ℝ) f (Φ x)) :
    IsCriticalPointAt I (f ∘ Φ) x ↔ IsCriticalPointAt J f (Φ x) := by
  apply isCriticalPointAt_comp_iff (Φ.contMDiff.mdifferentiableAt (by simp)) hf
  change Function.Surjective (Φ.mfderivToContinuousLinearEquiv (by simp) x)
  exact (Φ.mfderivToContinuousLinearEquiv (by simp) x).surjective

theorem isCriticalPointAt_transContinuousLinearEquiv_iff
    (e : E ≃L[ℝ] F) {f : M → ℝ} (x : M)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) :
    IsCriticalPointAt (I.transContinuousLinearEquiv e) f x ↔ IsCriticalPointAt I f x :=
  isCriticalPointAt_comp_diffeomorph_iff
    (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e).symm x hf

end Naturality

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isNondegenerateCriticalPointAt_model_iff
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    IsNondegenerateCriticalPointAt (𝓘(ℝ, E)) f x ↔
      fderiv ℝ f x = 0 ∧ Function.Injective (fderiv ℝ (fderiv ℝ f) x) := by
  have hsymm : ∀ u v : E, chartHessianBilinAt f x u v = chartHessianBilinAt f x v u := by
    intro u v
    exact hf.isSymmSndFDerivAt (by norm_num [minSmoothness]) |>.eq u v
  have hassociated : QuadraticMap.associated (R := ℝ) (chartHessianAt f x) =
      chartHessianBilinAt f x :=
    QuadraticMap.associated_left_inverse (S := ℝ) hsymm
  simp only [IsNondegenerateCriticalPointAt, IsCriticalPointAt,
    mfderiv_eq_fderiv, extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
    PartialEquiv.refl_coe, id_eq, hassociated]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h u v huv
    rw [← sub_eq_zero]
    apply h (u - v)
    intro w
    change (fderiv ℝ (fderiv ℝ f) x (u - v)) w = 0
    rw [map_sub, huv, sub_self]
    rfl
  · intro h u hu
    apply h
    ext w
    simpa [chartHessianBilinAt] using hu w

variable [FiniteDimensional ℝ E]

private theorem eventually_fderiv_eq_zero_imp_eq (g : E → ℝ) (x : E)
    (hg : ContDiffAt ℝ 2 g x) (hcrit : fderiv ℝ g x = 0)
    (hnd : (QuadraticMap.associated (R := ℝ) (chartHessianAt g x)).SeparatingLeft) :
    ∀ᶠ y in 𝓝 x, fderiv ℝ g y = 0 → y = x := by
  let D : E →L[ℝ] (E →L[ℝ] ℝ) := fderiv ℝ (fderiv ℝ g) x
  have hsymm : ∀ u v : E, chartHessianBilinAt g x u v = chartHessianBilinAt g x v u := by
    intro u v
    exact hg.isSymmSndFDerivAt (by norm_num [minSmoothness]) |>.eq u v
  have hassociated :
      QuadraticMap.associated (R := ℝ) (chartHessianAt g x) =
        chartHessianBilinAt g x :=
    QuadraticMap.associated_left_inverse (S := ℝ) hsymm
  have hDinj : Function.Injective D := by
    intro u v huv
    rw [← sub_eq_zero]
    apply hnd (u - v)
    intro w
    rw [hassociated]
    change (D (u - v)) w = 0
    have hzero : D (u - v) = 0 := by
      rw [map_sub, huv, sub_self]
    rw [hzero]
    rfl
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) :=
    Subspace.dual_finrank_eq.symm.trans LinearMap.toContinuousLinearMap.finrank_eq
  have hDsurj : Function.Surjective D :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hDinj
  have hDker : D.ker = ⊥ := LinearMap.ker_eq_bot.mpr hDinj
  have hDrange : D.range = ⊤ := LinearMap.range_eq_top.mpr hDsurj
  let De : E ≃L[ℝ] (E →L[ℝ] ℝ) :=
    ContinuousLinearEquiv.ofBijective D hDker hDrange
  have hDe : (De : E →L[ℝ] (E →L[ℝ] ℝ)) = D := by
    exact ContinuousLinearEquiv.coe_ofBijective D hDker hDrange
  have hgrad : ContDiffAt ℝ 1 (fderiv ℝ g) x := hg.fderiv_right (by norm_num)
  have hgradDeriv : HasFDerivAt (fderiv ℝ g) (De : E →L[ℝ] (E →L[ℝ] ℝ)) x := by
    rw [hDe]
    have h := hgrad.differentiableAt (by norm_num) |>.hasFDerivAt
    simpa [D] using h
  let phi : OpenPartialHomeomorph E (E →L[ℝ] ℝ) :=
    hgrad.toOpenPartialHomeomorph (fderiv ℝ g) hgradDeriv (by norm_num)
  have hxsource : x ∈ phi.source := by
    exact hgrad.mem_toOpenPartialHomeomorph_source hgradDeriv (by norm_num)
  filter_upwards [phi.open_source.mem_nhds hxsource] with y hysource hyzero
  apply phi.injOn hysource hxsource
  change fderiv ℝ g y = fderiv ℝ g x
  rw [hyzero, hcrit]

variable {H : Type} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
private theorem chartRep_contDiffOn {n : WithTop ℕ∞} [IsManifold I n M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) n f) (p : M) :
    ContDiffOn ℝ n
      (fun y : E => f ((extChartAt I p).symm y)) (extChartAt I p).target := by
  have hc : ContMDiffOn I 𝓘(ℝ, ℝ) n f univ := by
    intro x hx
    exact hf x
  have hcsub : ContMDiffOn I 𝓘(ℝ, ℝ) n f
      (chartAt H p).source := hc.mono (by intro x hx; trivial)
  have hc' : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) n
      (f ∘ (extChartAt I p).symm) (extChartAt I p '' (chartAt H p).source) :=
    (contMDiffOn_iff_source_of_mem_maximalAtlas (I := I) (I' := 𝓘(ℝ, ℝ))
      (n := n) (e := chartAt H p)
      (IsManifold.chart_mem_maximalAtlas p) (s := (chartAt H p).source)
      (hs := by intro x hx; exact hx)).1 hcsub
  have hcd : ContDiffOn ℝ n
      (f ∘ (extChartAt I p).symm) (extChartAt I p '' (chartAt H p).source) :=
    (contMDiffOn_iff_contDiffOn).1 hc'
  have hrange : extChartAt I p '' (chartAt H p).source = (extChartAt I p).target :=
    (OpenPartialHomeomorph.extend_target_eq_image_source (f := chartAt H p) (I := I)).symm
  rw [show (fun y : E => f ((extChartAt I p).symm y)) =
    f ∘ (extChartAt I p).symm by rfl]
  rwa [← hrange]

omit [FiniteDimensional ℝ E] in
private theorem isCriticalPointAt_iff_fixed_chart_fderiv_of_mdifferentiableAt [IsManifold I 1 M]
    {f : M → ℝ} {p q : M} (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f q)
    (hq : q ∈ (extChartAt I p).source) :
    IsCriticalPointAt I f q ↔
      fderiv ℝ (fun y : E => f ((extChartAt I p).symm y)) (extChartAt I p q) = 0 := by
  let e := extChartAt I p
  have hqt : e q ∈ e.target := e.map_source hq
  have hqchart : q ∈ (chartAt H p).source := by
    rwa [extChartAt_source (I := I)] at hq
  have he : MDifferentiableAt I 𝓘(ℝ, E) e q :=
    mdifferentiableAt_extChartAt hqchart
  have hesymm : MDifferentiableAt 𝓘(ℝ, E) I e.symm (e q) :=
    (mdifferentiableOn_extChartAt_symm (I := I) (x := p) (e q) hqt).mdifferentiableAt
      ((isOpen_extChartAt_target p).mem_nhds hqt)
  have hf' : MDifferentiableAt I 𝓘(ℝ, ℝ) f (e.symm (e q)) := by
    simpa only [e.left_inv hq] using hf
  have hg : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (f ∘ e.symm) (e q) :=
    hf'.comp (e q) hesymm
  have hsurj : Function.Surjective (mfderiv I 𝓘(ℝ, E) e q) := by
    have hcomp := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' (I := I) hq
    intro v
    refine ⟨mfderivWithin 𝓘(ℝ, E) I e.symm (range I) (e q) v, ?_⟩
    exact DFunLike.congr_fun hcomp v
  have heq : f =ᶠ[𝓝 q] (f ∘ e.symm) ∘ e :=
    Filter.eventuallyEq_of_mem ((isOpen_extChartAt_source p).mem_nhds hq)
      (fun z hz => congrArg f (e.left_inv hz).symm)
  have hcrit : IsCriticalPointAt I f q ↔ IsCriticalPointAt I ((f ∘ e.symm) ∘ e) q := by
    unfold IsCriticalPointAt
    rw [heq.mfderiv_eq]
    rfl
  rw [hcrit, isCriticalPointAt_comp_iff he hg hsurj]
  unfold IsCriticalPointAt
  rw [mfderiv_eq_fderiv]
  rfl

omit [FiniteDimensional ℝ E] in
private theorem eventually_isCriticalPointAt_iff_fixedChartFderiv [IsManifold I 1 M]
    (f : M → ℝ) (hf : MDifferentiable I 𝓘(ℝ, ℝ) f) (p : M) :
    ∀ᶠ q in 𝓝 p, IsCriticalPointAt I f q ↔
      fderiv ℝ (fun y : E => f ((extChartAt I p).symm y)) (extChartAt I p q) = 0 := by
  filter_upwards [(isOpen_extChartAt_source (I := I) p).mem_nhds
    (mem_extChartAt_source (I := I) p)] with q hq
  exact isCriticalPointAt_iff_fixed_chart_fderiv_of_mdifferentiableAt (hf q) hq

private theorem eventually_eq_of_isCriticalPointAt_of_contMDiff_two [IsManifold I 2 M]
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (2 : WithTop ℕ∞) f)
    {p : M} (hp : IsNondegenerateCriticalPointAt I f p) :
    ∀ᶠ q in 𝓝 p, IsCriticalPointAt I f q → q = p := by
  let e : PartialEquiv M E := extChartAt I p
  let g : E → ℝ := fun y => f (e.symm y)
  have hgOn : ContDiffOn ℝ (2 : WithTop ℕ∞) g e.target := by
    simpa [g, e] using chartRep_contDiffOn (I := I) f hf p
  have hptarget : e p ∈ e.target := e.map_source (mem_extChartAt_source p)
  have hgAt : ContDiffAt ℝ 2 g (e p) :=
    (hgOn (e p) hptarget).contDiffAt (isOpen_extChartAt_target p |>.mem_nhds hptarget)
  have hcritCoord : fderiv ℝ g (e p) = 0 := by
    simpa [g, e] using
      (isCriticalPointAt_iff_fixed_chart_fderiv_of_mdifferentiableAt (I := I)
        (p := p) (hf p |>.mdifferentiableAt (by norm_num)) (mem_extChartAt_source p)).1 hp.1
  have hisolatedCoord : ∀ᶠ y in 𝓝 (e p), fderiv ℝ g y = 0 → y = e p :=
    eventually_fderiv_eq_zero_imp_eq g (e p) hgAt hcritCoord hp.2
  have hfixed := eventually_isCriticalPointAt_iff_fixedChartFderiv (I := I) f
    (hf.mdifferentiable (by norm_num)) p
  have hpsource : p ∈ e.source := mem_extChartAt_source p
  filter_upwards [isOpen_extChartAt_source p |>.mem_nhds hpsource, hfixed,
    (continuousAt_extChartAt p).eventually hisolatedCoord] with q hqsource hiff hqisolated hqcrit
  have heq : e q = e p := hqisolated (hiff.1 hqcrit)
  exact e.injOn hqsource hpsource heq
omit [FiniteDimensional ℝ E] in
private theorem isClosed_criticalPoints_of_contMDiff_one [IsManifold I 1 M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (1 : WithTop ℕ∞) f) :
    IsClosed (criticalPoints I f) := by
  rw [← isOpen_compl_iff]
  rw [isOpen_iff_mem_nhds]
  intro p hp
  have hnotCritical : ¬ IsCriticalPointAt I f p := by
    change ¬ IsCriticalPointAt I f p at hp
    exact hp
  let e : PartialEquiv M E := extChartAt I p
  let g : E → ℝ := fun y => f (e.symm y)
  have hgOn : ContDiffOn ℝ (1 : WithTop ℕ∞) g e.target := by
    simpa [g, e] using chartRep_contDiffOn (I := I) f hf p
  have hptarget : e p ∈ e.target := e.map_source (mem_extChartAt_source p)
  have hgAt : ContDiffAt ℝ 1 g (e p) :=
    (hgOn (e p) hptarget).contDiffAt (isOpen_extChartAt_target p |>.mem_nhds hptarget)
  have hcritCoord : fderiv ℝ g (e p) ≠ 0 := by
    intro hzero
    apply hnotCritical
    exact (isCriticalPointAt_iff_fixed_chart_fderiv_of_mdifferentiableAt (I := I)
      (p := p) (hf p |>.mdifferentiableAt (by norm_num)) (mem_extChartAt_source p)).2
      (by simpa [g, e] using hzero)
  have hgradContinuous : ContinuousAt (fderiv ℝ g) (e p) :=
    hgAt.continuousAt_fderiv (by norm_num)
  have hcoordNe : ∀ᶠ y in 𝓝 (e p), fderiv ℝ g y ≠ 0 :=
    hgradContinuous.eventually_ne hcritCoord
  have hfixed := eventually_isCriticalPointAt_iff_fixedChartFderiv (I := I) f
    (hf.mdifferentiable (by norm_num)) p
  filter_upwards [hfixed, (continuousAt_extChartAt p).eventually hcoordNe] with q hiff hne
  rw [mem_compl_iff]
  change ¬ IsCriticalPointAt I f q
  exact fun hq => hne (hiff.1 hq)

theorem finite_inter_criticalPoints_of_isCompact [IsManifold I 2 M]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) (2 : WithTop ℕ∞) f)
    {K : Set M} (hK : IsCompact K)
    (hnd : ∀ p ∈ K, IsCriticalPointAt I f p →
      IsNondegenerateCriticalPointAt I f p) :
    (K ∩ criticalPoints I f).Finite := by
  apply (hK.inter_right (isClosed_criticalPoints_of_contMDiff_one f (hf.of_le (by decide)))).finite
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro p hp
  have hisolated := eventually_eq_of_isCriticalPointAt_of_contMDiff_two f hf (hnd p hp.1 hp.2)
  obtain ⟨u, hu, huOpen, hpu⟩ := mem_nhds_iff.mp hisolated
  refine ⟨u, huOpen, Set.ext ?_⟩
  intro q
  constructor
  · rintro ⟨hqu, hqK, hqcrit⟩
    exact mem_singleton_iff.mpr (hu hqu hqcrit)
  · intro hqp
    rw [mem_singleton_iff] at hqp
    subst q
    exact ⟨hpu, hp⟩

variable [IsManifold I (↑(⊤ : ℕ∞) : WithTop ℕ∞) M]

theorem IsNondegenerateCriticalPointAt.eventually_eq_of_isCriticalPointAt
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    {p : M} (hp : IsNondegenerateCriticalPointAt I f p) :
    ∀ᶠ q in 𝓝 p, IsCriticalPointAt I f q → q = p :=
  eventually_eq_of_isCriticalPointAt_of_contMDiff_two f (hf.of_le (by decide)) hp
omit [FiniteDimensional ℝ E] in
theorem isClosed_criticalPoints (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) :
    IsClosed (criticalPoints I f) :=
  isClosed_criticalPoints_of_contMDiff_one f (hf.of_le (by decide))

theorem isDiscrete_criticalPoints_of_isNondegenerate (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hnd : ∀ p : M, IsCriticalPointAt I f p → IsNondegenerateCriticalPointAt I f p) :
    IsDiscrete (criticalPoints I f) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro p hp
  have hpcrit : IsCriticalPointAt I f p := hp
  have hisolated := (hnd p hpcrit).eventually_eq_of_isCriticalPointAt f hf
  change {q : M | IsCriticalPointAt I f q → q = p} ∈ 𝓝 p at hisolated
  obtain ⟨u, hu, huOpen, hpu⟩ := mem_nhds_iff.mp hisolated
  refine ⟨u, huOpen, Set.ext ?_⟩
  intro q
  constructor
  · rintro ⟨hqu, hqcrit⟩
    exact mem_singleton_iff.mpr (hu hqu hqcrit)
  · intro hqp
    rw [mem_singleton_iff] at hqp
    subst q
    exact ⟨hpu, hp⟩

theorem finite_criticalPoints_of_compact_of_isNondegenerate [CompactSpace M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hnd : ∀ p : M, IsCriticalPointAt I f p → IsNondegenerateCriticalPointAt I f p) :
    (criticalPoints I f).Finite := by
  simpa only [univ_inter] using
    finite_inter_criticalPoints_of_isCompact (hf.of_le (by decide)) isCompact_univ
      (fun p _ hp => hnd p hp)

end

end Morse
end Topology
end DifferentialGeometry
