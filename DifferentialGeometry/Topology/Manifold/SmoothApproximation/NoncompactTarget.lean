import DifferentialGeometry.Topology.Manifold.Embedding.CompactRetraction
import DifferentialGeometry.Topology.Manifold.SmoothApproximation.EuclideanValued
import DifferentialGeometry.Topology.UniformConvergence
import DifferentialGeometry.Analysis.Calculus.MapConvergence.FiniteComposition

/-!
# Smooth approximation into an arbitrary target

Compactness is needed only for the source and its image. The target is Hausdorff and
boundaryless, but need not be compact. The local retraction is used only near that image.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

open DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {A : Type*} [TopologicalSpace A] [ChartedSpace H A] [IsManifold I ∞ A]
  [T2Space A] [CompactSpace A]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  {B : Type*} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B] [T2Space B]

theorem exists_compact_image_retraction {K : Set B}
    (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ (N : TopologicalSpace.Opens B) (n : ℕ)
      (e : B → EuclideanSpace ℝ (Fin n)) (r : EuclideanSpace ℝ (Fin n) → B)
      (V : Set (EuclideanSpace ℝ (Fin n))),
      K ⊆ N ∧ ContMDiff J 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e ∧
      HasCompactSupport e ∧ _root_.Topology.IsEmbedding (fun x : N => e x) ∧
      (∀ x ∈ N, Injective (mfderiv J 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e x)) ∧
      IsOpen V ∧ e '' (N : Set B) ⊆ V ∧ MapsTo r V N ∧
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) J ∞ r V ∧
      ∀ x ∈ N, r (e x) = x
 := by
  obtain ⟨N, n, e, r, U, hKN, he, hc, hi, hd, hU, heU, hr, hid⟩ :=
    DifferentialGeometry.Geometry.exists_contMDiff_embedding_retraction_near_isCompact
      (I := J) hK hne
  let V := U ∩ r ⁻¹' (N : Set B)
  have hV : IsOpen V := hr.continuousOn.isOpen_inter_preimage hU N.isOpen
  refine ⟨N, n, e, r, V, hKN, he, hc, hi, hd, hV, ?_, ?_,
    hr.mono inter_subset_left, hid⟩
  · rintro z ⟨x, hx, rfl⟩
    refine ⟨heU ⟨x, hx, rfl⟩, ?_⟩
    change r (e x) ∈ N
    rwa [hid x hx]
  · intro z hz
    exact hz.2

/-- Compact-source `C^k` approximation in arbitrary Hausdorff boundaryless targets. -/
theorem exists_smooth_seq_chart_tendsto_noncompact
    (k : ℕ) {h : A → B} (hh : ContMDiff I J k h) :
    ∃ hs : ℕ → A → B, (∀ j, ContMDiff I J ∞ (hs j)) ∧
      ∀ (p : A) (q : B) (K : Set E), IsCompact K → K ⊆ (extChartAt I p).target →
        MapsTo (fun y => h ((extChartAt I p).symm y)) K (extChartAt J q).source →
        (∀ᶠ j in atTop, MapsTo (fun y => hs j ((extChartAt I p).symm y)) K
            (extChartAt J q).source) ∧
          MapCPConvergenceOn K k (fun j y => extChartAt J q (hs j ((extChartAt I p).symm y)))
            (fun y => extChartAt J q (h ((extChartAt I p).symm y)))
 := by
  classical
  rcases isEmpty_or_nonempty A with hempty | hnonempty
  · refine ⟨fun j => h, ?_, ?_⟩
    · intro j x
      exact isEmptyElim x
    · intro p
      exact isEmptyElim p
  have himage : IsCompact (range h) := isCompact_range hh.continuous
  have hne : (range h).Nonempty := ⟨h (Classical.arbitrary A), mem_range_self _⟩
  obtain ⟨N, n, e, r, V, hN, he, hsupport, hemb, hderiv, hV, heV, hrV, hr, hleft⟩ :=
    exists_compact_image_retraction (J := J) himage hne
  have hfix (x : A) : r (e (h x)) = h x := hleft (h x) (hN (mem_range_self x))
  have hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) k (e ∘ h) :=
    (he.of_le (by exact_mod_cast le_top)).comp hh
  obtain ⟨fs, hsmooth, huniform, hcoordinates⟩ :=
    exists_smooth_seq_chart_tendsto_of_contMDiff_normedSpace k hf
  have hlimitV : MapsTo (e ∘ h) univ V := by
    intro x hx
    exact heV ⟨h x, hN (mem_range_self x), rfl⟩
  obtain ⟨a, ha⟩ := eventually_atTop.mp
    (DifferentialGeometry.eventually_mapsTo_of_tendstoUniformly huniform
      isCompact_univ hf.continuous.continuousOn hV hlimitV)
  have htail (j : ℕ) (x : A) : fs (j + a) x ∈ V :=
    ha (j + a) (Nat.le_add_left a j) (mem_univ x)
  have hshift : StrictMono (fun j : ℕ => j + a) :=
    fun j l hjl => Nat.add_lt_add_right hjl a
  let g : ℕ → A → B := fun j => r ∘ fs (j + a)
  have hg (j : ℕ) : ContMDiff I J ∞ (g j) :=
    hr.comp_contMDiff (hsmooth (j + a)) (htail j)
  refine ⟨g, hg, ?_⟩
  intro p q K hK hKt hKm
  let U : Set E := (extChartAt I p).target ∩
    (extChartAt I p).symm ⁻¹' (h ⁻¹' (extChartAt J q).source)
  let W : Set (EuclideanSpace ℝ (Fin n)) := V ∩ r ⁻¹' (extChartAt J q).source
  have hU : IsOpen U := (continuousOn_extChartAt_symm p).isOpen_inter_preimage
    (isOpen_extChartAt_target p) ((isOpen_extChartAt_source q).preimage hh.continuous)
  have hW : IsOpen W := hr.continuousOn.isOpen_inter_preimage hV (isOpen_extChartAt_source q)
  have hKU : K ⊆ U := fun y hy => ⟨hKt hy, hKm hy⟩
  let inner : E → EuclideanSpace ℝ (Fin n) := (e ∘ h) ∘ (extChartAt I p).symm
  let approx : ℕ → E → EuclideanSpace ℝ (Fin n) :=
    fun j => fs (j + a) ∘ (extChartAt I p).symm
  let outer : EuclideanSpace ℝ (Fin n) → E' := extChartAt J q ∘ r
  have houter : ContDiffOn ℝ ∞ outer W := by
    apply contMDiffOn_iff_contDiffOn.mp
    apply (contMDiffOn_extChartAt (x := q)).comp (hr.mono inter_subset_left)
    intro z hz
    simpa only [extChartAt_source] using hz.2
  have hinner : ContDiffOn ℝ ((k : ℕ∞) : WithTop ℕ∞) inner (extChartAt I p).target :=
    contMDiffOn_iff_contDiffOn.mp (hf.comp_contMDiffOn
      ((contMDiffOn_extChartAt_symm (n := ∞) p).of_le (by exact_mod_cast le_top)))
  have happ (j : ℕ) : ContDiffOn ℝ ((k : ℕ∞) : WithTop ℕ∞)
      (approx j) (extChartAt I p).target :=
    (contMDiffOn_iff_contDiffOn.mp ((hsmooth (j + a)).comp_contMDiffOn
      (contMDiffOn_extChartAt_symm p))).of_le (by exact_mod_cast le_top)
  have hmap : MapsTo inner U W := by
    intro y hy
    refine ⟨hlimitV (mem_univ _), ?_⟩
    change r (e (h ((extChartAt I p).symm y))) ∈ (extChartAt J q).source
    rw [hfix]
    exact hy.2
  have hconv : ∀ L : Set E, IsCompact L → L ⊆ U →
      MapCPConvergenceOn L k approx inner := by
    intro L hL hLU
    exact (hcoordinates p L hL (hLU.trans inter_subset_left)).comp_subseq hshift
  have hcapture : ∀ᶠ j in atTop, MapsTo (approx j) K W :=
    TendstoUniformlyOn.eventually_mapsTo_of_isCompact
      (tendstoUniformlyOn_of_cPConvergence ((hconv K hK hKU).mono_order (Nat.zero_le k)))
      hK (hinner.continuousOn.mono hKt) hW (hmap.mono_left hKU)
  have hcompose : MapCPConvergenceOn K k (fun j y => outer (approx j y))
      (fun y => outer (inner y)) :=
    mapCPConvergenceOn_comp_of_eventually_contDiffOn hU hW hconv
      (fun S hS hSW => MapCPConvergenceOn.const_seq outer)
      (fun L hL hLU => Eventually.of_forall fun j => (happ j).mono
        (hLU.trans inter_subset_left)) (hinner.mono inter_subset_left)
      (fun S hS hSW => Eventually.of_forall fun j =>
        (houter.of_le (by exact_mod_cast le_top)).mono hSW)
      (houter.of_le (by exact_mod_cast le_top)) hmap hK hKU
  constructor
  · filter_upwards [hcapture] with j hj
    intro y hy
    exact (hj hy).2
  · simpa only [outer, inner, approx, g, Function.comp_apply, hfix] using hcompose

/-- One smooth map simultaneously approximates a finite collection of chart pieces. -/
theorem exists_smooth_chart_close_noncompact (k : ℕ) {h : A → B}
    (hh : ContMDiff I J k h) {ι : Type*} (s : Finset ι)
    (p : ι → A) (q : ι → B) (K : ι → Set E)
    (hK : ∀ i ∈ s, IsCompact (K i) ∧ K i ⊆ (extChartAt I (p i)).target ∧
      MapsTo (fun y => h ((extChartAt I (p i)).symm y)) (K i) (extChartAt J (q i)).source)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : A → B, ContMDiff I J ∞ f ∧ ∀ i ∈ s,
      MapsTo (fun y => f ((extChartAt I (p i)).symm y)) (K i) (extChartAt J (q i)).source ∧
      ∀ r ≤ k, ∀ y ∈ K i,
        mapDerivNorm r (fun y => extChartAt J (q i) (f ((extChartAt I (p i)).symm y)))
          (fun y => extChartAt J (q i) (h ((extChartAt I (p i)).symm y))) y ≤ ε
 := by
  obtain ⟨fs, hsm, hconv⟩ := exists_smooth_seq_chart_tendsto_noncompact k hh
  have hall : ∀ᶠ j in atTop, ∀ i ∈ s,
      MapsTo (fun y => fs j ((extChartAt I (p i)).symm y)) (K i)
        (extChartAt J (q i)).source ∧ ∀ r ≤ k, ∀ y ∈ K i,
        mapDerivNorm r (fun y => extChartAt J (q i) (fs j ((extChartAt I (p i)).symm y)))
          (fun y => extChartAt J (q i) (h ((extChartAt I (p i)).symm y))) y ≤ ε := by
    apply (eventually_all_finset s).mpr
    intro i hi
    obtain ⟨hc, ht, hm⟩ := hK i hi
    obtain ⟨hevent, hlimit⟩ := hconv (p i) (q i) (K i) hc ht hm
    obtain ⟨a, ha⟩ := hlimit ε hε
    exact hevent.and ((eventually_ge_atTop a).mono fun j hj => ha j hj)
  obtain ⟨j, hj⟩ := hall.exists
  exact ⟨fs j, hsm j, hj⟩

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
