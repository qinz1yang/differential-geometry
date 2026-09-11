import DifferentialGeometry.Analysis.Calculus.SmoothExtension.Compact
import DifferentialGeometry.Topology.Morse.Perturbation
import DifferentialGeometry.Topology.Morse.Stability
import Mathlib.Geometry.Manifold.PartitionOfUnity

open Set Filter
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Topology.Morse

open DifferentialGeometry.Analysis

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
private theorem smooth_cutoff_chart (c : M) {χ : M → ℝ}
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ)
    (hsupp : tsupport χ ⊆ (chartAt H c).source) :
    ContMDiff I 𝓘(ℝ, E) ∞ (fun x => χ x • extChartAt I c x) := by
  refine contMDiff_of_tsupport fun x hx => ?_
  have hxs : x ∈ (chartAt H c).source :=
    hsupp (tsupport_smul_subset_left _ _ hx)
  exact (hχ x).smul ((contMDiffOn_extChartAt x hxs).contMDiffAt
    ((chartAt H c).open_source.mem_nhds hxs))

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
private theorem smooth_cutoff_linear_perturbation_joint (c : M) {χ : M → ℝ}
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ)
    (hsupp : tsupport χ ⊆ (chartAt H c).source) :
    ContMDiff ((𝓘(ℝ, E →L[ℝ] ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : (E →L[ℝ] ℝ) × M => χ p.2 * p.1 (extChartAt I c p.2)) := by
  have hc := smooth_cutoff_chart c hχ hsupp
  have hfst : ContMDiff ((𝓘(ℝ, E →L[ℝ] ℝ)).prod I)
      𝓘(ℝ, E →L[ℝ] ℝ) ∞ (Prod.fst : (E →L[ℝ] ℝ) × M → E →L[ℝ] ℝ) :=
    contMDiff_fst
  simpa only [Function.comp_def, map_smul, smul_eq_mul] using
    hfst.clm_apply (hc.comp contMDiff_snd)

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
private theorem smooth_sub_cutoff_linear_perturbation_joint {f χ : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (c : M)
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ)
    (hsupp : tsupport χ ⊆ (chartAt H c).source) :
    ContMDiff ((𝓘(ℝ, E →L[ℝ] ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : (E →L[ℝ] ℝ) × M => f p.2 - χ p.2 * p.1 (extChartAt I c p.2)) :=
  (hf.comp contMDiff_snd).sub (smooth_cutoff_linear_perturbation_joint c hχ hsupp)


omit [I.Boundaryless] [IsManifold I ∞ M] in
private theorem dense_cutoff_linear_perturbations_on_compact
    {f χ : E → ℝ} {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (hf : ContDiffOn ℝ 2 f U)
    (hχ : ∀ x ∈ K, χ =ᶠ[𝓝 x] 1) :
    Dense {a : E →L[ℝ] ℝ | ∀ x ∈ K,
      IsCriticalPointAt 𝓘(ℝ, E) (fun y => f y - χ y * a y) x →
        IsNondegenerateCriticalPointAt 𝓘(ℝ, E) (fun y => f y - χ y * a y) x} := by
  obtain ⟨g, hg, _, hgeq⟩ := exists_contDiff_compactSupport_extension_on_isCompact
    hK hU hKU hf
  apply (dense_linear_perturbations_isNondegenerateCriticalPointAt hg).mono
  intro a ha x hx hcrit
  have heq : (fun y => f y - χ y * a y) =ᶠ[𝓝 x] (fun y => g y - a y) := by
    have hext : g =ᶠ[𝓝 x] f := hgeq.filter_mono (nhds_le_nhdsSet hx)
    filter_upwards [hext, hχ x hx] with y hy hχy
    simp only [hχy, Pi.one_apply, one_mul, hy]
  have hfAt : ContDiffAt ℝ 2 (fun y => f y - χ y * a y) x :=
    (hg.sub a.contDiff).contDiffAt.congr_of_eventuallyEq heq
  apply (isNondegenerateCriticalPointAt_model_iff hfAt).mpr
  have hzero : fderiv ℝ (fun y => f y - χ y * a y) x = 0 := by
    unfold IsCriticalPointAt at hcrit
    rw [mfderiv_eq_fderiv] at hcrit
    exact hcrit
  have hzero' : fderiv ℝ (fun y => g y - a y) x = 0 := by
    rwa [← heq.fderiv_eq]
  have hcrit' : IsCriticalPointAt 𝓘(ℝ, E) (fun y => g y - a y) x := by
    unfold IsCriticalPointAt
    rw [mfderiv_eq_fderiv]
    exact hzero'
  have hnd := ((isNondegenerateCriticalPointAt_model_iff
    (hg.sub a.contDiff).contDiffAt).mp (ha x hcrit')).2
  refine ⟨hzero, ?_⟩
  rw [(heq.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)]
  exact hnd


private theorem dense_cutoff_linear_perturbations_on_compact_chart
    {f χ : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hχsmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ) (p : M)
    {K : Set M} (hK : IsCompact K) (hKchart : K ⊆ (extChartAt I p).source)
    (hχ : ∀ x ∈ K, χ =ᶠ[𝓝 x] 1)
    (hsupp : tsupport χ ⊆ (chartAt H p).source) :
    Dense {a : E →L[ℝ] ℝ | ∀ x ∈ K,
      IsCriticalPointAt I (fun y => f y - χ y * a (extChartAt I p y)) x →
        IsNondegenerateCriticalPointAt I (fun y => f y - χ y * a (extChartAt I p y)) x} := by
  let e := extChartAt I p
  have hKC : IsCompact (e '' K) := hK.image_of_continuousOn
    ((continuousOn_extChartAt p).mono hKchart)
  have hKU : e '' K ⊆ e.target := by
    rintro y ⟨x, hx, rfl⟩
    exact e.map_source (hKchart hx)
  have hfC : ContDiffOn ℝ 2 (f ∘ e.symm) e.target := by
    rw [← contMDiffOn_iff_contDiffOn]
    intro y hy
    exact ((hf.of_le (by decide)).contMDiffAt).comp_contMDiffWithinAt y
      (contMDiffOn_extChartAt_symm p y hy)
  have hχC : ∀ y ∈ e '' K, (χ ∘ e.symm) =ᶠ[𝓝 y] 1 := by
    rintro y ⟨x, hx, rfl⟩
    have hxs := hKchart hx
    have hec : ContinuousAt e.symm (e x) :=
      (continuousOn_extChartAt_symm p).continuousAt
        ((isOpen_extChartAt_target p).mem_nhds (e.map_source hxs))
    have hχx : χ =ᶠ[𝓝 (e.symm (e x))] 1 := by
      simpa only [e.left_inv hxs] using hχ x hx
    exact hχx.comp_tendsto hec
  have hd := dense_cutoff_linear_perturbations_on_compact hKC
    (isOpen_extChartAt_target p) hKU hfC hχC
  apply hd.mono
  intro a ha x hx hcrit
  let F : M → ℝ := fun y => f y - χ y * a (e y)
  have hF : ContMDiff I 𝓘(ℝ, ℝ) ∞ F := by
    have hj := smooth_sub_cutoff_linear_perturbation_joint hf p hχsmooth hsupp
    exact hj.comp (contMDiff_const.prodMk contMDiff_id)
  have hxs := hKchart hx
  have hxt := e.map_source hxs
  have heq : (F ∘ e.symm) =ᶠ[𝓝 (e x)]
      (fun y => (f ∘ e.symm) y - (χ ∘ e.symm) y * a y) := by
    filter_upwards [(isOpen_extChartAt_target p).mem_nhds hxt] with y hy
    dsimp [F, Function.comp_def]
    rw [e.right_inv hy]
  have hcritC : IsCriticalPointAt 𝓘(ℝ, E) (F ∘ e.symm) (e x) :=
    (isCriticalPointAt_iff_fixed_chart (hF.mdifferentiable (by simp) x) hxs).mp hcrit
  have hcritG : IsCriticalPointAt 𝓘(ℝ, E)
      (fun y => (f ∘ e.symm) y - (χ ∘ e.symm) y * a y) (e x) := by
    unfold IsCriticalPointAt at hcritC ⊢
    rw [heq.mfderiv_eq] at hcritC
    exact hcritC
  have hnd := ha (e x) ⟨x, hx, rfl⟩ hcritG
  apply (isNondegenerateCriticalPointAt_iff_fixed_chart
    ((hF.of_le (by decide)).contMDiffAt) hxs).mpr
  exact (isNondegenerateCriticalPointAt_congr_of_eventuallyEq heq).mpr hnd


omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] in
private theorem exists_contMDiff_nondegenerate_on_finset_union
    {ι : Type} {n : WithTop ℕ∞}
    (K : ι → Set M) (hK : ∀ i, IsCompact (K i))
    (hstep : ∀ i (f : M → ℝ), ContMDiff I 𝓘(ℝ, ℝ) n f →
      ∀ L : Set M, IsCompact L →
      (∀ x ∈ L, IsCriticalPointAt I f x → IsNondegenerateCriticalPointAt I f x) →
      ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) n g ∧
        ∀ x ∈ L ∪ K i, IsCriticalPointAt I g x → IsNondegenerateCriticalPointAt I g x)
    {L : Set M} (hL : IsCompact L) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) n f)
    (hfL : ∀ x ∈ L, IsCriticalPointAt I f x → IsNondegenerateCriticalPointAt I f x)
    (s : Finset ι) :
    ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) n g ∧
      ∀ x ∈ L ∪ ⋃ i ∈ s, K i,
        IsCriticalPointAt I g x → IsNondegenerateCriticalPointAt I g x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨f, hf, ?_⟩
      simpa using hfL
  | @insert i s hi ih =>
      obtain ⟨g, hg, hgL⟩ := ih
      have hLs : IsCompact (L ∪ ⋃ j ∈ s, K j) :=
        hL.union (s.finite_toSet.isCompact_biUnion (fun j _ => hK j))
      obtain ⟨g', hg', hg'L⟩ := hstep i g hg (L ∪ ⋃ j ∈ s, K j) hLs hgL
      refine ⟨g', hg', ?_⟩
      simpa only [Finset.set_biUnion_insert, union_assoc, union_left_comm,
        union_comm] using hg'L

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] in
private theorem exists_contMDiff_nondegenerate_of_finset_cover
    {ι : Type} {n : WithTop ℕ∞}
    (K : ι → Set M) (hK : ∀ i, IsCompact (K i)) (s : Finset ι)
    {C : Set M} (hcover : C ⊆ ⋃ i ∈ s, K i)
    (hstep : ∀ i (f : M → ℝ), ContMDiff I 𝓘(ℝ, ℝ) n f →
      ∀ L : Set M, IsCompact L →
      (∀ x ∈ L, IsCriticalPointAt I f x → IsNondegenerateCriticalPointAt I f x) →
      ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) n g ∧
        ∀ x ∈ L ∪ K i, IsCriticalPointAt I g x → IsNondegenerateCriticalPointAt I g x) :
    ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) n g ∧
      ∀ x ∈ C, IsCriticalPointAt I g x → IsNondegenerateCriticalPointAt I g x := by
  obtain ⟨g, hg, hgood⟩ := exists_contMDiff_nondegenerate_on_finset_union K hK hstep
    (L := ∅) isCompact_empty (f := fun _ => 0) contMDiff_const (by simp) s
  exact ⟨g, hg, fun x hx => hgood x (Or.inr (hcover hx))⟩


private theorem exists_small_perturbation_preserving_compact_and_morse
    {f χ : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hχsmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ) (p : M)
    {K L : Set M} (hK : IsCompact K) (hKchart : K ⊆ (extChartAt I p).source)
    (hL : IsCompact L)
    (hχ : ∀ x ∈ K, χ =ᶠ[𝓝 x] 1)
    (hsupp : tsupport χ ⊆ (chartAt H p).source)
    (hMorse : ∀ x ∈ L, IsCriticalPointAt I f x → IsNondegenerateCriticalPointAt I f x) :
    ∀ ε : ℝ, 0 < ε → ∃ a : E →L[ℝ] ℝ, ‖a‖ < ε ∧
      (∀ x ∈ K, IsCriticalPointAt I (fun y => f y - χ y * a (extChartAt I p y)) x →
        IsNondegenerateCriticalPointAt I (fun y => f y - χ y * a (extChartAt I p y)) x) ∧
      (∀ x ∈ L, IsCriticalPointAt I (fun y => f y - χ y * a (extChartAt I p y)) x →
        IsNondegenerateCriticalPointAt I (fun y => f y - χ y * a (extChartAt I p y)) x) := by
  let F : (E →L[ℝ] ℝ) → M → ℝ := fun a y => f y - χ y * a (extChartAt I p y)
  have hF : ContMDiff ((𝓘(ℝ, E →L[ℝ] ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
      (Function.uncurry F) := by
    change ContMDiff ((𝓘(ℝ, E →L[ℝ] ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : (E →L[ℝ] ℝ) × M => f q.2 - χ q.2 * q.1 (extChartAt I p q.2))
    exact smooth_sub_cutoff_linear_perturbation_joint hf p hχsmooth hsupp
  have hstable : ∀ᶠ a in 𝓝 (0 : E →L[ℝ] ℝ), ∀ x ∈ L,
      IsCriticalPointAt I (F a) x → IsNondegenerateCriticalPointAt I (F a) x :=
    eventually_isNondegenerateCriticalPointAt_on_isCompact
      hL (fun _ _ => (hF.of_le (by decide)).contMDiffAt) (a := 0) (by simpa [F] using hMorse)
  intro ε hε
  obtain ⟨U, hUsub, hUopen, h0U⟩ := mem_nhds_iff.mp hstable
  obtain ⟨a, haDense, haU, haBall⟩ :=
    (dense_cutoff_linear_perturbations_on_compact_chart hf hχsmooth p hK hKchart hχ hsupp).exists_mem_open
      (U := U ∩ Metric.ball (0 : E →L[ℝ] ℝ) ε)
      (hUopen.inter Metric.isOpen_ball) ⟨0, h0U, by simpa using hε⟩
  refine ⟨a, ?_, haDense, hUsub haU⟩
  simpa only [Metric.mem_ball, dist_zero_right] using haBall

omit [I.Boundaryless] in
private theorem exists_finite_compact_chart_cutoffs [T2Space M] [CompactSpace M] :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → M) (K : ι → Set M) (χ : ι → M → ℝ),
      (∀ i, IsCompact (K i)) ∧ (⋃ i, K i) = univ ∧
      (∀ i, K i ⊆ (extChartAt I (c i)).source) ∧
      (∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (χ i)) ∧
      (∀ i, HasCompactSupport (χ i)) ∧
      (∀ i, χ i =ᶠ[𝓝ˢ (K i)] 1) ∧
      (∀ i, tsupport (χ i) ⊆ (extChartAt I (c i)).source) := by
  classical
  obtain ⟨ι, fs, _⟩ := SmoothBumpCovering.exists_isSubordinate (I := I)
    isClosed_univ (U := fun _ : M => (univ : Set M)) (fun _ _ => univ_mem)
  let : Fintype ι := fs.fintype
  let K : ι → Set M := fun i => {x | fs i x = 1}
  have hK (i : ι) : IsCompact (K i) :=
    (isClosed_eq (fs i).continuous continuous_const).isCompact
  have hKU (i : ι) : K i ⊆ (extChartAt I (fs.c i)).source := by
    intro x hx
    exact fs.mem_extChartAt_source_of_eq_one hx
  have hcover : (⋃ i, K i) = univ := by
    apply eq_univ_of_forall
    intro x
    exact mem_iUnion.mpr ⟨fs.ind x (mem_univ x), fs.apply_ind x (mem_univ x)⟩
  choose χ hχsmooth hχcompact hχone hχsupport hχrange using
    fun i => DifferentialGeometry.Analysis.exists_mfd_bump (I := I)
      (hK i) (isOpen_extChartAt_source (I := I) (fs.c i)) (hKU i)
  exact ⟨ι, inferInstance, fs.c, K, χ, hK, hcover, hKU,
    hχsmooth, hχcompact, hχone, hχsupport⟩


theorem exists_morse_function [T2Space M] [CompactSpace M] :
    ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧
      ∀ x, IsCriticalPointAt I f x → IsNondegenerateCriticalPointAt I f x := by
  classical
  obtain ⟨ι, hι, c, K, χ, hK, hcover, hKchart, hχsmooth, _, hχone, hsupp⟩ :=
    exists_finite_compact_chart_cutoffs (I := I) (M := M)
  let : Fintype ι := hι
  have hstep : ∀ i (f : M → ℝ), ContMDiff I 𝓘(ℝ, ℝ) ∞ f →
      ∀ L : Set M, IsCompact L →
      (∀ x ∈ L, IsCriticalPointAt I f x → IsNondegenerateCriticalPointAt I f x) →
      ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ g ∧
        ∀ x ∈ L ∪ K i, IsCriticalPointAt I g x → IsNondegenerateCriticalPointAt I g x := by
    intro i f hf L hL hgood
    have hχnear : ∀ x ∈ K i, χ i =ᶠ[𝓝 x] 1 :=
      fun x hx => (hχone i).filter_mono (nhds_le_nhdsSet hx)
    have hsupp' : tsupport (χ i) ⊆ (chartAt H (c i)).source := by
      simpa only [extChartAt_source] using hsupp i
    obtain ⟨a, _, haK, haL⟩ := exists_small_perturbation_preserving_compact_and_morse hf
      (hχsmooth i) (c i) (hK i) (hKchart i) hL hχnear hsupp' hgood 1 zero_lt_one
    refine ⟨fun y => f y - χ i y * a (extChartAt I (c i) y), ?_, ?_⟩
    · exact (smooth_sub_cutoff_linear_perturbation_joint hf (c i) (hχsmooth i) hsupp').comp
        (contMDiff_const.prodMk contMDiff_id)
    · intro x hx
      rcases hx with hx | hx
      · exact haL x hx
      · exact haK x hx
  have hcover' : (univ : Set M) ⊆ ⋃ i ∈ (Finset.univ : Finset ι), K i := by
    simpa only [Finset.mem_univ, iUnion_true, hcover] using (Subset.rfl : (univ : Set M) ⊆ univ)
  obtain ⟨f, hf, hgood⟩ := exists_contMDiff_nondegenerate_of_finset_cover K hK
    Finset.univ hcover' hstep
  exact ⟨f, hf, fun x => hgood x (mem_univ x)⟩

end DifferentialGeometry.Topology.Morse
