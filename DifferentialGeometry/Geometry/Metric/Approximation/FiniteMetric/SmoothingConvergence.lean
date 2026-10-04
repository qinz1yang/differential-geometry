import DifferentialGeometry.Geometry.Metric.Approximation.FiniteMetric.Smoothing
import DifferentialGeometry.Analysis.Calculus.MapConvergence.FiniteOrder
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Locality
import DifferentialGeometry.Analysis.Calculus.SmoothApproximation.Bilinear
import DifferentialGeometry.Analysis.FiniteDimensional.Coercivity

/-!
# Global smoothing of a finite-regularity metric (LFR50, part A1)

`exists_smooth_metric_approximation`: on a compact manifold with a boundaryless model, every
`C^n` Riemannian metric `g`, `2 ≤ n`, is the chart-coefficient `C²` limit of smooth Riemannian
metrics `gSeq k`. The chart coefficients converge in `C²` on compact sets `L i` of finitely many
charts, and these sets cover the manifold. All `gSeq k` are bilipschitz to `gSeq 0` with one
constant `Λ` (review item 3 of the merged LFR50 design: comparison with ONE fixed smooth
approximant).

Construction: a finite chart cover, a smooth partition of unity `ρ` subordinate to it, uniform
quadratic bounds `C⁻¹ ≤ g ≤ C` of the chart coefficients near `Kᵢ = φᵢ(tsupport ρᵢ)`, the
chartwise positive smoothing `exists_smooth_bilinear_approx_on_compact` (which keeps the bounds
exactly, so the glued forms are positive definite), and gluing by `exists_smoothMetric_glued`.
The chart convergence uses the finite-order composition lemmas of
`Analysis/Calculus/MapConvergence/FiniteOrder.lean` and the transition law of chart
coefficients.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Geometry.MetricSmoothing

open DifferentialGeometry.CheegerGromovCompactness

section Term

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
private theorem contDiffOn_cutoff_symm (q : M) {ρ : M → ℝ} (hρ : ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ) :
    ContDiffOn ℝ ∞ (fun y => ρ ((extChartAt I q).symm y)) (extChartAt I q).target :=
  contMDiffOn_iff_contDiffOn.mp (hρ.comp_contMDiffOn (contMDiffOn_extChartAt_symm q))

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem isOpen_cutoff_zero (q : M) (ρ : M → ℝ) :
    IsOpen ((extChartAt I q).target ∩ (extChartAt I q).symm ⁻¹' (tsupport ρ)ᶜ) :=
  (continuousOn_extChartAt_symm q).isOpen_inter_preimage (isOpen_extChartAt_target q)
    (isClosed_tsupport ρ).isOpen_compl

omit [FiniteDimensional ℝ E] in
private theorem contDiff_smul_pullbackForm :
    ContDiff ℝ ∞ (fun z : ℝ × ((E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E)) =>
      z.1 • pullbackForm z.2) := by
  have h : (fun z : ℝ × ((E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E)) => z.1 • pullbackForm z.2) =
      fun z => (pullbackForm z.2).comp (z.1 • ContinuousLinearMap.id ℝ E) := by
    funext z
    ext v w
    simp
  rw [h]
  exact (pullbackForm.contDiff.comp contDiff_snd).clm_comp (contDiff_fst.smul contDiff_const)

omit [FiniteDimensional ℝ E] in
/-- One partition-of-unity term of the chart coefficients, written in the chart at `q`. -/
theorem contDiffOn_transitionTerm (p q : M) {ρ : M → ℝ} (hρ : ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ)
    (hρs : tsupport ρ ⊆ (extChartAt I p).source) {A : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hA : ContDiffOn ℝ ((2 : ℕ) : ℕ∞) A (extChartAt I p).target) :
    ContDiffOn ℝ ((2 : ℕ) : ℕ∞) (fun y => ρ ((extChartAt I q).symm y) •
      pullbackForm (A (chartTransition (I := I) p q y),
        fderiv ℝ (chartTransition (I := I) p q) y)) (extChartAt I q).target := by
  apply contDiffOn_of_locally_contDiffOn
  intro y hy
  by_cases hys : (extChartAt I q).symm y ∈ (extChartAt I p).source
  · refine ⟨transitionDomain (I := I) p q, isOpen_transitionDomain (I := I) p q, ⟨hy, hys⟩, ?_⟩
    have hW := isOpen_transitionDomain (I := I) p q
    have hT := contDiffOn_chartTransition (I := I) p q
    have hDT : ContDiffOn ℝ ∞ (fun y => fderiv ℝ (chartTransition (I := I) p q) y)
        (transitionDomain (I := I) p q) := hT.fderiv_of_isOpen hW (by simp)
    have hAT : ContDiffOn ℝ ((2 : ℕ) : ℕ∞) (fun y => A (chartTransition (I := I) p q y))
        (transitionDomain (I := I) p q) :=
      hA.comp (hT.of_le (by exact_mod_cast le_top)) (chartTransition_mapsTo (I := I) p q)
    have hr : ContDiffOn ℝ ((2 : ℕ) : ℕ∞) (fun y => ρ ((extChartAt I q).symm y))
        (transitionDomain (I := I) p q) :=
      ((contDiffOn_cutoff_symm (I := I) q hρ).mono inter_subset_left).of_le
        (by exact_mod_cast le_top)
    have hDT2 : ContDiffOn ℝ ((2 : ℕ) : ℕ∞)
        (fun y => fderiv ℝ (chartTransition (I := I) p q) y) (transitionDomain (I := I) p q) :=
      hDT.of_le (by exact_mod_cast le_top)
    have h := ((contDiff_smul_pullbackForm (E := E)).of_le
      (by exact_mod_cast le_top)).comp_contDiffOn (hr.prodMk (hAT.prodMk hDT2))
    exact h.mono inter_subset_right
  · have hyO : y ∈ (extChartAt I q).target ∩ (extChartAt I q).symm ⁻¹' (tsupport ρ)ᶜ :=
      ⟨hy, fun h => hys (hρs h)⟩
    refine ⟨_, isOpen_cutoff_zero (I := I) q ρ, hyO, ?_⟩
    refine (contDiffOn_const (c := (0 : E →L[ℝ] E →L[ℝ] ℝ))).congr ?_
    intro z hz
    rw [image_eq_zero_of_notMem_tsupport hz.2.2]
    ext v w
    simp

/-- **Chart change of `C²` convergence** for one partition-of-unity term: if `A k → A₀` in `C²`
on the image of `tsupport ρ` in the chart at `p`, the transformed terms converge in `C²` on every
compact subset of the chart target at `q`. -/
theorem mapCPConvergenceOn_transitionTerm (p q : M) {ρ : M → ℝ}
    (hρ : ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ) (hρs : tsupport ρ ⊆ (extChartAt I p).source)
    {L : Set E} (hL : IsCompact L) (hLq : L ⊆ (extChartAt I q).target)
    {A : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ} {A₀ : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hAc : ∀ k, ContDiffOn ℝ ((2 : ℕ) : ℕ∞) (A k) (extChartAt I p).target)
    (hA₀ : ContDiffOn ℝ ((2 : ℕ) : ℕ∞) A₀ (extChartAt I p).target)
    (hconv : MapCPConvergenceOn ((extChartAt I p) '' tsupport ρ) 2 A A₀) :
    MapCPConvergenceOn L 2
      (fun k y => ρ ((extChartAt I q).symm y) •
        pullbackForm (A k (chartTransition (I := I) p q y),
          fderiv ℝ (chartTransition (I := I) p q) y))
      (fun y => ρ ((extChartAt I q).symm y) •
        pullbackForm (A₀ (chartTransition (I := I) p q y),
          fderiv ℝ (chartTransition (I := I) p q) y)) := by
  set L₁ := L ∩ (extChartAt I q).symm ⁻¹' tsupport ρ with hL₁
  set L₂ := L \ (extChartAt I q).symm ⁻¹' tsupport ρ with hL₂
  have hcover : L ⊆ L₁ ∪ L₂ := fun y hy => by
    by_cases h : (extChartAt I q).symm y ∈ tsupport ρ
    · exact Or.inl ⟨hy, h⟩
    · exact Or.inr ⟨hy, h⟩
  refine (MapCPConvergenceOn.union ?_ ?_).mono_set hcover
  · have hW := isOpen_transitionDomain (I := I) p q
    have hT := contDiffOn_chartTransition (I := I) p q
    have hcl : IsClosed L₁ :=
      ((continuousOn_extChartAt_symm q).mono hLq).preimage_isClosed_of_isClosed hL.isClosed
        (isClosed_tsupport ρ)
    have hL₁ : IsCompact L₁ := hL.of_isClosed_subset hcl inter_subset_left
    have hL₁W : L₁ ⊆ transitionDomain (I := I) p q := fun y hy => ⟨hLq hy.1, hρs hy.2⟩
    have himage : chartTransition (I := I) p q '' L₁ ⊆ (extChartAt I p) '' tsupport ρ := by
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨_, hy.2, rfl⟩
    have hDT : ContDiffOn ℝ ∞ (fun y => fderiv ℝ (chartTransition (I := I) p q) y)
        (transitionDomain (I := I) p q) := hT.fderiv_of_isOpen hW (by simp)
    have hDT2 : ContDiffOn ℝ ((2 : ℕ) : ℕ∞)
        (fun y => fderiv ℝ (chartTransition (I := I) p q) y) (transitionDomain (I := I) p q) :=
      hDT.of_le (by exact_mod_cast le_top)
    have hT2 : ContDiffOn ℝ ((2 : ℕ) : ℕ∞) (chartTransition (I := I) p q)
        (transitionDomain (I := I) p q) := hT.of_le (by exact_mod_cast le_top)
    have hr : ContDiffOn ℝ ((2 : ℕ) : ℕ∞) (fun y => ρ ((extChartAt I q).symm y))
        (transitionDomain (I := I) p q) :=
      ((contDiffOn_cutoff_symm (I := I) q hρ).mono inter_subset_left).of_le
        (by exact_mod_cast le_top)
    have hATc : ∀ k, ContDiffOn ℝ ((2 : ℕ) : ℕ∞)
        (fun y => A k (chartTransition (I := I) p q y)) (transitionDomain (I := I) p q) :=
      fun k => (hAc k).comp hT2 (chartTransition_mapsTo (I := I) p q)
    have hAT₀c : ContDiffOn ℝ ((2 : ℕ) : ℕ∞)
        (fun y => A₀ (chartTransition (I := I) p q y)) (transitionDomain (I := I) p q) :=
      hA₀.comp hT2 (chartTransition_mapsTo (I := I) p q)
    have hAT : MapCPConvergenceOn L₁ 2 (fun k y => A k (chartTransition (I := I) p q y))
        (fun y => A₀ (chartTransition (I := I) p q y)) :=
      MapCPConvergenceOn.comp_contDiffOn_right hW (isOpen_extChartAt_target p) hL₁ hL₁W hT2
        (chartTransition_mapsTo (I := I) p q) (hconv.mono_set himage) hAc hA₀
    have hpair := MapCPConvergenceOn.prodMk_of_contDiffOn hW hL₁W hAT
      (MapCPConvergenceOn.const_seq (K := L₁) (p := 2)
        (fun y => fderiv ℝ (chartTransition (I := I) p q) y))
      hATc hAT₀c (fun _ => hDT2) hDT2
    have htrip := MapCPConvergenceOn.prodMk_of_contDiffOn hW hL₁W
      (MapCPConvergenceOn.const_seq (K := L₁) (p := 2) (fun y => ρ ((extChartAt I q).symm y)))
      hpair (fun _ => hr) hr (fun k => (hATc k).prodMk hDT2) (hAT₀c.prodMk hDT2)
    have hres := MapCPConvergenceOn.comp_contDiff_left
      (B := fun k y => (ρ ((extChartAt I q).symm y),
        (A k (chartTransition (I := I) p q y), fderiv ℝ (chartTransition (I := I) p q) y)))
      (Binf := fun y => (ρ ((extChartAt I q).symm y),
        (A₀ (chartTransition (I := I) p q y), fderiv ℝ (chartTransition (I := I) p q) y)))
      (Ψ := fun z : ℝ × ((E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E)) => z.1 • pullbackForm z.2)
      hW hL₁ hL₁W htrip (fun k => hr.prodMk ((hATc k).prodMk hDT2))
      (hr.prodMk (hAT₀c.prodMk hDT2))
      ((contDiff_smul_pullbackForm (E := E)).of_le (by exact_mod_cast le_top))
    exact hres
  · refine MapCPConvergenceOn.of_eventuallyEq fun y hy k => ?_
    have hyO : y ∈ (extChartAt I q).target ∩ (extChartAt I q).symm ⁻¹' (tsupport ρ)ᶜ :=
      ⟨hLq hy.1, hy.2⟩
    filter_upwards [(isOpen_cutoff_zero (I := I) q ρ).mem_nhds hyO] with z hz
    rw [image_eq_zero_of_notMem_tsupport hz.2]
    ext v w
    simp

end Term

section Main

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M]

/-- **LFR50 part A1 (global smoothing).** On a compact manifold with a boundaryless model, a
`C^n` Riemannian metric `g`, `2 ≤ n`, is the limit of smooth Riemannian metrics `gSeq k` in the
following sense: there are finitely many points `i ∈ t` and compact sets `L i` in the targets of
the extended charts at `i` whose preimages cover the manifold, and on each `L i` the chart
coefficients of `gSeq k` converge in `C²` to those of `g`. Moreover all `gSeq k` are uniformly
bilipschitz to the single smooth metric `gSeq 0`. -/
theorem exists_smooth_metric_approximation {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hn : (2 : ℕ∞ω) ≤ n) :
    ∃ (t : Finset M) (L : t → Set E) (gSeq : ℕ → SmoothRiemannianMetric I M) (Λ : ℝ),
      (∀ i : t, IsCompact (L i) ∧ L i ⊆ (extChartAt I (i : M)).target) ∧
      (∀ x : M, ∃ i : t, x ∈ (extChartAt I (i : M)).source ∧ extChartAt I (i : M) x ∈ L i) ∧
      (∀ i : t, MapCPConvergenceOn (L i) 2 (fun k => chartCoeff (gSeq k) (i : M))
        (chartCoeff g (i : M))) ∧
      0 < Λ ∧ ∀ k (x : M) (w : TangentSpace I x),
        (gSeq k).inner x w w ≤ Λ * (gSeq 0).inner x w w ∧
          (gSeq 0).inner x w w ≤ Λ * (gSeq k).inner x w w := by
  obtain ⟨t, ht⟩ : ∃ t : Finset M, (univ : Set M) ⊆ ⋃ p ∈ t, (extChartAt I p).source :=
    isCompact_univ.elim_finite_subcover (fun p => (extChartAt I p).source)
      (fun p => isOpen_extChartAt_source p)
      (fun x _ => mem_iUnion.2 ⟨x, mem_extChartAt_source x⟩)
  let c : t → M := Subtype.val
  have hcover : (univ : Set M) ⊆ ⋃ i : t, (extChartAt I (c i)).source := by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 (ht hx)
    exact mem_iUnion.2 ⟨⟨p, hp⟩, hxp⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ
    (fun i : t => (extChartAt I (c i)).source) (fun i => isOpen_extChartAt_source _) hcover
  have hρs : ∀ i, tsupport (ρ i) ⊆ (extChartAt I (c i)).source := hρ
  have hsum1 : ∀ x : M, ∑ i, ρ i x = 1 := fun x => sum_partition_eq_one ρ (mem_univ x)
  let K : t → Set E := fun i => extChartAt I (c i) '' tsupport (ρ i)
  have hK : ∀ i, IsCompact (K i) := fun i =>
    (isClosed_tsupport _).isCompact.image_of_continuousOn
      ((continuousOn_extChartAt (c i)).mono (hρs i))
  have hKt : ∀ i, K i ⊆ (extChartAt I (c i)).target := by
    rintro i _ ⟨x, hx, rfl⟩
    exact (extChartAt I (c i)).map_source (hρs i hx)
  have hb : ∀ i, ContDiffOn ℝ 2 (chartCoeff g (c i)) (extChartAt I (c i)).target :=
    fun i => contDiffOn_chartCoeff g hn (c i)
  have hb2 : ∀ i, ContDiffOn ℝ ((2 : ℕ) : ℕ∞) (chartCoeff g (c i)) (extChartAt I (c i)).target :=
    fun i => (hb i).of_le (by norm_num)
  have hbounds : ∀ i, ∃ C : ℝ, 1 ≤ C ∧ ∃ W : Set E, IsOpen W ∧ K i ⊆ W ∧
      closure W ⊆ (extChartAt I (c i)).target ∧ ∀ z ∈ closure W,
        ∀ v : E, C⁻¹ * ‖v‖ ^ 2 ≤ chartCoeff g (c i) z v v ∧
          chartCoeff g (c i) z v v ≤ C * ‖v‖ ^ 2 := fun i => by
    obtain ⟨C, hC, W, hWo, hKW, hWt, -, hCW⟩ :=
      (hb i).continuousOn.exists_uniform_bilin_quadratic_bounds_nhds
        (isOpen_extChartAt_target _) (hK i) (hKt i)
        (fun z hz v hv => chartCoeff_pos g (c i) hz hv)
    exact ⟨C, hC, W, hWo, hKW, hWt, hCW⟩
  choose C hC W hWo hKW hWt hCW using hbounds
  set C₀ : ℝ := 1 + ∑ i, C i with hC₀
  have hCnn : ∀ i, 0 ≤ C i := fun i => zero_le_one.trans (hC i)
  have hC₀i : ∀ i, C i ≤ C₀ := fun i => by
    have := Finset.single_le_sum (f := C) (fun j _ => hCnn j) (Finset.mem_univ i)
    linarith
  have hC₀1 : 1 ≤ C₀ := by
    have : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun j _ => hCnn j
    linarith
  have hC₀pos : 0 < C₀ := by linarith
  have hbd : ∀ i, ∀ z ∈ W i, ∀ v : E, C₀⁻¹ * ‖v‖ ^ 2 ≤ chartCoeff g (c i) z v v ∧
      chartCoeff g (c i) z v v ≤ C₀ * ‖v‖ ^ 2 := by
    intro i z hz v
    obtain ⟨h1, h2⟩ := hCW i z (subset_closure hz) v
    exact ⟨le_trans (mul_le_mul_of_nonneg_right
        (inv_anti₀ (lt_of_lt_of_le zero_lt_one (hC i)) (hC₀i i)) (sq_nonneg _)) h1,
      le_trans h2 (mul_le_mul_of_nonneg_right (hC₀i i) (sq_nonneg _))⟩
  have hlu : C₀⁻¹ ≤ C₀ := (inv_le_one_of_one_le₀ hC₀1).trans hC₀1
  have happrox : ∀ i, ∃ G : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ,
      (∀ k, ContDiff ℝ ∞ (G k)) ∧ (∀ k y v w, G k y v w = G k y w v) ∧
      (∀ k y v, C₀⁻¹ * ‖v‖ ^ 2 ≤ G k y v v ∧ G k y v v ≤ C₀ * ‖v‖ ^ 2) ∧
      ∀ j, j ≤ 2 → TendstoUniformlyOn (fun k => iteratedFDeriv ℝ j (G k))
        (iteratedFDeriv ℝ j (chartCoeff g (c i))) atTop (K i) := fun i =>
    DifferentialGeometry.Analysis.exists_smooth_bilinear_approx_on_compact (hK i) (hWo i)
      (hKW i) 2 (((hb i).mono (subset_closure.trans (hWt i))).of_le (by norm_num))
      (fun z _ v w => chartCoeff_symm g (c i) z v w) C₀⁻¹ C₀ hlu (hbd i)
  choose G hGs hGsymm hGb hGconv using happrox
  have hGconv' : ∀ i, MapCPConvergenceOn (K i) 2 (G i) (chartCoeff g (c i)) := fun i =>
    mapCPConvergenceOn_of_tendstoUniformlyOn (isOpen_extChartAt_target _) (hKt i)
      (fun k => (hGs i k).contDiffOn.of_le (by exact_mod_cast le_top)) (hb2 i)
      (fun r hr => hGconv i r hr)
  have hglue : ∀ k, ∃ h : SmoothRiemannianMetric I M, ∀ x (v w : TangentSpace I x),
      h.inner x v w = ∑ i, ρ i x * G i k (extChartAt I (c i) x)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I (c i)) x v)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I (c i)) x w) := fun k =>
    exists_smoothMetric_glued c ρ hρ (fun i => G i k) (fun i => hGs i k)
      (fun i => hGsymm i k) (fun i y v hv => lt_of_lt_of_le
        (mul_pos (inv_pos.2 hC₀pos) (pow_pos (norm_pos_iff.2 hv) 2)) (hGb i k y v).1)
  choose gSeq hgSeq using hglue
  refine ⟨t, K, gSeq, C₀ * C₀, fun i => ⟨hK i, hKt i⟩, ?_, ?_, mul_pos hC₀pos hC₀pos, ?_⟩
  · intro x
    obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, ρ i x ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have h := hsum1 x
      rw [Finset.sum_eq_zero hcon] at h
      exact zero_ne_one h
    have hxi : x ∈ tsupport (ρ i) := subset_tsupport _ (Function.mem_support.mpr hi)
    exact ⟨i, hρs i hxi, ⟨x, hxi, rfl⟩⟩
  · intro j
    have hT := isOpen_extChartAt_target (I := I) (c j)
    refine (MapCPConvergenceOn.sum_of_contDiffOn Finset.univ hT (hKt j)
      (Φ := fun i k y => ρ i ((extChartAt I (c j)).symm y) •
        pullbackForm (G i k (chartTransition (I := I) (c i) (c j) y),
          fderiv ℝ (chartTransition (I := I) (c i) (c j)) y))
      (Φinf := fun i y => ρ i ((extChartAt I (c j)).symm y) •
        pullbackForm (chartCoeff g (c i) (chartTransition (I := I) (c i) (c j) y),
          fderiv ℝ (chartTransition (I := I) (c i) (c j)) y))
      (fun i _ => mapCPConvergenceOn_transitionTerm (c i) (c j) (ρ i).contMDiff (hρs i)
        (hK j) (hKt j) (fun k => (hGs i k).contDiffOn.of_le (by exact_mod_cast le_top))
        (hb2 i) (hGconv' i))
      (fun i _ k => contDiffOn_transitionTerm (c i) (c j) (ρ i).contMDiff (hρs i)
        ((hGs i k).contDiffOn.of_le (by exact_mod_cast le_top)))
      (fun i _ => contDiffOn_transitionTerm (c i) (c j) (ρ i).contMDiff (hρs i)
        (hb2 i))).congr hT (hKt j) (fun k y hy => ?_) (fun y hy => ?_)
    · exact chartCoeff_glued c (fun i => ρ i) hρs (fun i => G i k) (gSeq k) (hgSeq k) (c j) hy
    · exact chartCoeff_eq_sum_transition g c (fun i => ρ i) hρs hsum1 (c j) hy
  · intro k x w
    let D : t → E →L[ℝ] E := fun i => mfderiv I 𝓘(ℝ, E) (extChartAt I (c i)) x
    let S : ℝ := ∑ i, ρ i x * ‖D i w‖ ^ 2
    have hup : ∀ m, (gSeq m).inner x w w ≤ C₀ * S := by
      intro m
      rw [hgSeq m, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      refine le_of_le_of_eq (mul_le_mul_of_nonneg_left
        (hGb i m (extChartAt I (c i) x) (D i w)).2 (ρ.nonneg i x)) ?_
      ring
    have hlow : ∀ m, C₀⁻¹ * S ≤ (gSeq m).inner x w w := by
      intro m
      rw [hgSeq m, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      refine le_of_eq_of_le ?_ (mul_le_mul_of_nonneg_left
        (hGb i m (extChartAt I (c i) x) (D i w)).1 (ρ.nonneg i x))
      ring
    have hkey : C₀ * S = C₀ * C₀ * (C₀⁻¹ * S) := by
      field_simp
    constructor
    · calc (gSeq k).inner x w w ≤ C₀ * S := hup k
        _ = C₀ * C₀ * (C₀⁻¹ * S) := hkey
        _ ≤ C₀ * C₀ * (gSeq 0).inner x w w :=
          mul_le_mul_of_nonneg_left (hlow 0) (by positivity)
    · calc (gSeq 0).inner x w w ≤ C₀ * S := hup 0
        _ = C₀ * C₀ * (C₀⁻¹ * S) := hkey
        _ ≤ C₀ * C₀ * (gSeq k).inner x w w :=
          mul_le_mul_of_nonneg_left (hlow k) (by positivity)

end Main

end DifferentialGeometry.Geometry.MetricSmoothing
