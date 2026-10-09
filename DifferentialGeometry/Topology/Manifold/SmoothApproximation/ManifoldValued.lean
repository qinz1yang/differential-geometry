import DifferentialGeometry.Topology.Manifold.SmoothApproximation.EuclideanValued
import DifferentialGeometry.Analysis.Calculus.MapConvergence.FiniteComposition

/-!
# Smooth approximation of `C^k` maps into a compact manifold (W1)

`exists_smooth_seq_chart_tendsto`: for compact Hausdorff manifolds `A`, `B` with boundaryless
models, every `C^k` map `h : A → B` (`k : ℕ`, `k = 0` allowed) is the chart-wise `C^k` limit of
smooth maps `hs j`, in the following sense, used verbatim as the hypothesis of W2: for every
extended chart `φ_p` of `A`, every extended chart `ψ_q` of `B` and every compact `K` in the
target of `φ_p` with `h (φ_p⁻¹ K) ⊆ source ψ_q`,
* eventually `hs j (φ_p⁻¹ K) ⊆ source ψ_q` (so that `ψ_q ∘ hs j ∘ φ_p⁻¹` is the coordinate
  expression of `hs j` near `K`), and
* `ψ_q ∘ hs j ∘ φ_p⁻¹ → ψ_q ∘ h ∘ φ_p⁻¹` in `C^k` on `K` (`MapCPConvergenceOn K k`).

Route: embed `B` (Whitney) with a smooth retraction `r` on an open `U ⊇ e(B)`; approximate the
Euclidean-valued `e ∘ h` by W1a; eventually the approximants land in `U`; compose with `r`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

open DifferentialGeometry.CheegerGromovCompactness

private theorem eventually_mem_of_tendstoUniformly {α X : Type*} [PseudoMetricSpace X]
    {fs : ℕ → α → X} {f : α → X} (hu : TendstoUniformly fs f atTop) {C V : Set X}
    (hC : IsCompact C) (hV : IsOpen V) (hCV : C ⊆ V) :
    ∀ᶠ j in atTop, ∀ x, f x ∈ C → fs j x ∈ V := by
  obtain ⟨δ, hδ, hsub⟩ := hC.exists_thickening_subset_open hV hCV
  filter_upwards [Metric.tendstoUniformly_iff.mp hu δ hδ] with j hj x hx
  exact hsub (Metric.mem_thickening_iff.mpr ⟨f x, hx, by rw [dist_comm]; exact hj x⟩)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {A : Type*} [TopologicalSpace A] [ChartedSpace H A] [IsManifold I ∞ A]
  [T2Space A] [CompactSpace A]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  {B : Type*} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]

/-- **W1 (compact target).** A `C^k` map between compact boundaryless manifolds is the
chart-wise `C^k` limit of smooth maps: for all charts `φ_p` of `A`, `ψ_q` of `B` and every compact
`K ⊆ target φ_p` with `h (φ_p⁻¹ K) ⊆ source ψ_q`, eventually `hs j (φ_p⁻¹ K) ⊆ source ψ_q`, and
`ψ_q ∘ hs j ∘ φ_p⁻¹ → ψ_q ∘ h ∘ φ_p⁻¹` in `C^k` on `K`. -/
theorem exists_smooth_seq_chart_tendsto [T2Space B] [CompactSpace B]
    (k : ℕ) {h : A → B} (hh : ContMDiff I J k h) :
    ∃ hs : ℕ → A → B, (∀ j, ContMDiff I J ∞ (hs j)) ∧
      ∀ (p : A) (q : B) (K : Set E), IsCompact K → K ⊆ (extChartAt I p).target →
        MapsTo (fun y => h ((extChartAt I p).symm y)) K (extChartAt J q).source →
        (∀ᶠ j in atTop, MapsTo (fun y => hs j ((extChartAt I p).symm y)) K
            (extChartAt J q).source) ∧
          MapCPConvergenceOn K k (fun j y => extChartAt J q (hs j ((extChartAt I p).symm y)))
            (fun y => extChartAt J q (h ((extChartAt I p).symm y))) := by
  rcases isEmpty_or_nonempty A with hA | hA
  · exact ⟨fun _ => h, fun _ x => isEmptyElim x, fun p => isEmptyElim p⟩
  have hB : Nonempty B := ⟨h (Classical.arbitrary A)⟩
  obtain ⟨N, e, he, hemb, hi⟩ := exists_embedding_euclidean_of_compact (I := J) (M := B)
  obtain ⟨r, U, hU, heU, hr, hleft⟩ :=
    DifferentialGeometry.Geometry.exists_smooth_neighborhood_retraction he hemb.isEmbedding hi
  have hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) k (fun x => e (h x)) :=
    (he.of_le (by exact_mod_cast le_top)).comp hh
  obtain ⟨fs, hfs, hunif, hchart⟩ := exists_smooth_seq_chart_tendsto_of_contMDiff_normedSpace k hf
  have hS : IsCompact (range e) := isCompact_range he.continuous
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp
    (eventually_mem_of_tendstoUniformly hunif hS hU heU)
  have hfsU : ∀ j x, fs (j + j₀) x ∈ U := fun j x =>
    hj₀ (j + j₀) (Nat.le_add_left j₀ j) x (mem_range_self _)
  have hshift : StrictMono fun j : ℕ => j + j₀ := fun a b hab => Nat.add_lt_add_right hab j₀
  refine ⟨fun j x => r (fs (j + j₀) x), fun j => hr.comp_contMDiff (hfs (j + j₀)) (hfsU j), ?_⟩
  intro p q K hK hKt hKmap
  set W : Set E := (extChartAt I p).target ∩
    (extChartAt I p).symm ⁻¹' (h ⁻¹' (extChartAt J q).source) with hWdef
  have hWo : IsOpen W := (continuousOn_extChartAt_symm p).isOpen_inter_preimage
    (isOpen_extChartAt_target p) ((isOpen_extChartAt_source q).preimage hh.continuous)
  have hKW : K ⊆ W := fun y hy => ⟨hKt hy, hKmap hy⟩
  set V : Set (EuclideanSpace ℝ (Fin N)) := U ∩ r ⁻¹' (extChartAt J q).source with hVdef
  have hVo : IsOpen V := hr.continuousOn.isOpen_inter_preimage hU (isOpen_extChartAt_source q)
  have hΨ : ContDiffOn ℝ ∞ (fun z => extChartAt J q (r z)) V := by
    apply contMDiffOn_iff_contDiffOn.mp
    refine (contMDiffOn_extChartAt (x := q)).comp (hr.mono inter_subset_left) ?_
    intro z hz
    simpa only [extChartAt_source] using hz.2
  have hBinf : ContDiffOn ℝ ((k : ℕ∞) : WithTop ℕ∞)
      (fun y => e (h ((extChartAt I p).symm y))) (extChartAt I p).target :=
    contMDiffOn_iff_contDiffOn.mp (hf.comp_contMDiffOn
      ((contMDiffOn_extChartAt_symm (n := ∞) p).of_le (by exact_mod_cast le_top)))
  have hBj : ∀ j, ContDiffOn ℝ ((k : ℕ∞) : WithTop ℕ∞)
      (fun y => fs (j + j₀) ((extChartAt I p).symm y)) (extChartAt I p).target := fun j =>
    (contMDiffOn_iff_contDiffOn.mp ((hfs (j + j₀)).comp_contMDiffOn
      (contMDiffOn_extChartAt_symm p))).of_le (by exact_mod_cast le_top)
  have hmap : MapsTo (fun y => e (h ((extChartAt I p).symm y))) W V := by
    intro y hy
    refine ⟨heU (mem_range_self _), ?_⟩
    change r (e (h ((extChartAt I p).symm y))) ∈ (extChartAt J q).source
    rw [hleft]
    exact hy.2
  constructor
  · have hC : IsCompact ((fun y => e (h ((extChartAt I p).symm y))) '' K) :=
      hK.image_of_continuousOn (hBinf.continuousOn.mono hKt)
    have hev := (tendsto_add_atTop_nat j₀).eventually
      (eventually_mem_of_tendstoUniformly hunif hC hVo ((hmap.mono_left hKW).image_subset))
    filter_upwards [hev] with j hj y hy
    exact (hj ((extChartAt I p).symm y) ⟨y, hy, rfl⟩).2
  · have h := mapCPConvergenceOn_comp_of_eventually_contDiffOn
      (B := fun j y => fs (j + j₀) ((extChartAt I p).symm y))
      (Binf := fun y => e (h ((extChartAt I p).symm y)))
      (A := fun _ z => extChartAt J q (r z)) (Ainf := fun z => extChartAt J q (r z))
      hWo hVo
      (fun L hL hLW => (hchart p L hL (hLW.trans inter_subset_left)).comp_subseq hshift)
      (fun S _ _ => MapCPConvergenceOn.const_seq _)
      (fun L _ hLW => Eventually.of_forall fun j => (hBj j).mono (hLW.trans inter_subset_left))
      (hBinf.mono inter_subset_left)
      (fun S _ hSV => Eventually.of_forall fun _ =>
        (hΨ.of_le (by exact_mod_cast le_top)).mono hSV)
      (hΨ.of_le (by exact_mod_cast le_top)) hmap hK hKW
    simpa only [hleft] using h

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
