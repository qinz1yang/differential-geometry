import DifferentialGeometry.Integral.Measure.BorelManifold.Defs
import DifferentialGeometry.Integral.L2.SmoothSections.Defs
import DifferentialGeometry.Tensor.RSTensor.Defs
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Topology.VectorBundle.Hom
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# Borel-measurability of smooth bundle sections

For a `ChartedSpace H M` carrying the `IsBorelChartedSpace` typeclass, this file
proves that the underlying map of a smooth bundle section, viewed through the
canonical fibre-to-model identification, is Borel-measurable as a function
`M → ModelFiber`.

The argument:

1. The typeclass `IsBorelChartedSpace H M` gives a countable enumeration of the
   range of `chartAt H` together with Borel-measurability of each level set.
2. For each chart-index `n`, choose a representative `x_n` belonging to the
   level set `s n = {x | chartAt H x = c n}`.  The trivialization-projected
   map `g_n : M → ModelFiber`, defined by
   `g_n x = (trivializationAt _ _ x_n ⟨x, S.toSection x⟩).2`, is smooth on
   `(chartAt H x_n).source` (Mathlib's
   `Trivialization.contMDiffOn_section_baseSet_iff`), hence continuous there.
3. On the level set `s n` (where `chartAt H x = chartAt H x_n`, equivalently
   `achart H x = achart H x_n`), the trivialization-projection coincides with
   the intrinsic fibre-to-model coercion `TensorRSSpace.toModel` because the
   relevant tangent-bundle change-of-coordinates is the identity by
   `VectorBundleCore.coordChange_self`.
4. Combining (1)–(3) with the standard "Borel union of open / closed
   restrictions is Borel" lemma yields global Borel-measurability of
   `S.toFun`.

The headline export is `SmoothCcTensor.measurable_toFun`, with
`AEStronglyMeasurable` and `StronglyMeasurable` variants.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Set MeasureTheory Bundle Manifold Tensor0SBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Measure
namespace BorelManifold

open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Generic gluing principle.  If a function `f : M → F` to a Borel-measurable
codomain is continuous on every chart source of `M`, and `M` is a Borel-charted
space, then `f` is Borel-measurable.

The proof partitions `M` into countably many Borel pieces along the level sets
of `chartAt H`, uses chart-local continuity to express the preimage of any open
set as a relatively-open subset of a chart source, and assembles the pieces. -/
theorem measurable_of_continuousOn_chart_source
    [IsBorelChartedSpace H M] [Nonempty M]
    {F : Type*} [TopologicalSpace F]
    (f : M → F) (hf : ∀ α : M, ContinuousOn f (chartAt H α).source) :
    @Measurable M F (borel M) (borel F) f := by
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  letI : MeasurableSpace F := borel F
  haveI : BorelSpace F := ⟨rfl⟩
  classical
  have hcount := IsBorelChartedSpace.chartAt_range_countable (H := H) (M := M)
  have hmeas := IsBorelChartedSpace.measurableSet_chartAt_preimage (H := H) (M := M)
  have hrange_nonempty : (Set.range (fun x : M => chartAt H x)).Nonempty :=
    Set.range_nonempty (fun x : M => chartAt H x)
  obtain ⟨φ, hφ⟩ := hcount.exists_eq_range hrange_nonempty
  set s : ℕ → Set M := fun n => {x : M | chartAt H x = φ n} with hs_def
  have hsmeas : ∀ n, MeasurableSet (s n) := fun n => hmeas (φ n)
  have hssub : ∀ n, s n ⊆ (φ n).source := by
    intro n x hx
    have hxs : x ∈ (chartAt H x).source := ChartedSpace.mem_chart_source x
    have hxe : chartAt H x = φ n := hx
    rw [hxe] at hxs
    exact hxs
  have hcov : (⋃ n, s n) = univ := by
    refine Set.eq_univ_of_forall (fun x => ?_)
    have hxr : chartAt H x ∈ Set.range (fun y : M => chartAt H y) :=
      Set.mem_range_self x
    rw [hφ] at hxr
    obtain ⟨n, hn⟩ := hxr
    refine mem_iUnion.mpr ⟨n, ?_⟩
    change chartAt H x = φ n
    exact hn.symm
  have hsne : ∀ n, (s n).Nonempty := by
    intro n
    have hin : φ n ∈ Set.range (fun y : M => chartAt H y) := by
      rw [hφ]; exact Set.mem_range_self n
    obtain ⟨x, hx⟩ := hin
    exact ⟨x, hx⟩
  have hf_φ : ∀ n, ContinuousOn f (φ n).source := by
    intro n
    obtain ⟨x₀, hx₀⟩ := hsne n
    have hh : chartAt H x₀ = φ n := hx₀
    have hcx := hf x₀
    rw [hh] at hcx
    exact hcx
  have hopen_source : ∀ n, IsOpen (φ n).source := fun n => (φ n).open_source
  refine measurable_of_isOpen ?_
  intro U hU
  have hpre : f ⁻¹' U = ⋃ n, f ⁻¹' U ∩ s n := by
    ext x
    simp only [mem_preimage, mem_iUnion, mem_inter_iff]
    constructor
    · intro hx
      have hxc : x ∈ ⋃ n, s n := by rw [hcov]; exact mem_univ x
      obtain ⟨n, hn⟩ := mem_iUnion.mp hxc
      exact ⟨n, hx, hn⟩
    · rintro ⟨n, hx, _⟩
      exact hx
  rw [hpre]
  refine MeasurableSet.iUnion (fun n => ?_)
  have h1 : f ⁻¹' U ∩ s n = ((φ n).source ∩ f ⁻¹' U) ∩ s n := by
    ext y
    simp only [mem_inter_iff]
    constructor
    · rintro ⟨hyU, hys⟩
      exact ⟨⟨hssub n hys, hyU⟩, hys⟩
    · rintro ⟨⟨_, hyU⟩, hys⟩
      exact ⟨hyU, hys⟩
  rw [h1]
  have hopen : IsOpen ((φ n).source ∩ f ⁻¹' U) :=
    (hf_φ n).isOpen_inter_preimage (hopen_source n) hU
  exact MeasurableSet.inter hopen.measurableSet (hsmeas n)

private lemma rs_baseSet_eq_chart_source' (α : M) (r s : ℕ) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x) α).baseSet =
      (chartAt H α).source := by
  change ((trivializationAt (Tensor0SModel r ℝ E)
              (fun x : M => Tensor0SSpace r I x) α).baseSet) ∩
      ((trivializationAt (Tensor0SModel s ℝ E)
              (fun x : M => Tensor0SSpace s I x) α).baseSet) =
        (chartAt H α).source
  change (trivializationAt E (TangentSpace I) α).baseSet ∩
        (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source
  rw [Set.inter_self]
  rfl

private lemma contMDiffOn_trivProj
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) (α : M) :
    ContMDiffOn I (𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun x : M => (trivializationAt (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x) α
          ⟨x, S.toSection x⟩).2)
      ((chartAt H α).source) := by
  letI : IsManifold I (∞ + 1) M := by
    have : ((∞ : WithTop ℕ∞) + 1) = ∞ := by
      simp
    rw [this]; infer_instance
  letI : ContMDiffVectorBundle ∞ (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) I :=
    tensorRSBundle_smooth (n := ∞) r s
  have hbase := rs_baseSet_eq_chart_source' (I := I) (M := M) α r s
  have hsmooth_total :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E) x (S.toSection x)) :=
    S.toSection.contMDiff
  have hrewrite := (Bundle.Trivialization.contMDiffOn_section_baseSet_iff
    (e := trivializationAt (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) α)).mp hsmooth_total.contMDiffOn
  rw [hbase] at hrewrite
  exact hrewrite

private lemma continuousOn_trivProj
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) (α : M) :
    ContinuousOn
      (fun x : M => (trivializationAt (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x) α
          ⟨x, S.toSection x⟩).2)
      ((chartAt H α).source) :=
  (contMDiffOn_trivProj (I := I) (M := M) S α).continuousOn

/-- The tangent-bundle trivialization at `α`, restricted to the level set
`{x | chartAt H x = chartAt H α}`, has identity `continuousLinearMapAt` map. -/
private lemma tangent_continuousLinearMapAt_levelSet (α x : M)
    (hx : chartAt H x = chartAt H α) :
    (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x =
      (1 : E →L[ℝ] E) := by
  have hx_src : x ∈ (chartAt H α).source := by
    have hxs : x ∈ (chartAt H x).source := ChartedSpace.mem_chart_source x
    rw [hx] at hxs
    exact hxs
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
    (b₀ := α) (b := x) hx_src]
  have hach : achart H x = achart H α := by
    apply Subtype.ext
    change chartAt H x = chartAt H α
    exact hx
  ext v
  rw [hach]
  exact (tangentBundleCore I M).coordChange_self (achart H α) x
    (by rw [tangentBundleCore_baseSet, coe_achart]; exact hx_src) v

/-- The tangent-bundle trivialization at `α`, restricted to the level set
`{x | chartAt H x = chartAt H α}`, has identity `symmL` map. -/
private lemma tangent_symmL_levelSet (α x : M)
    (hx : chartAt H x = chartAt H α) :
    (trivializationAt E (TangentSpace I) α).symmL ℝ x = (1 : E →L[ℝ] E) := by
  have hx_src : x ∈ (chartAt H α).source := by
    have hxs : x ∈ (chartAt H x).source := ChartedSpace.mem_chart_source x
    rw [hx] at hxs
    exact hxs
  rw [TangentBundle.symmL_trivializationAt_eq_core
    (b₀ := α) (b := x) hx_src]
  have hach : achart H x = achart H α := by
    apply Subtype.ext
    change chartAt H x = chartAt H α
    exact hx
  ext v
  rw [hach]
  exact (tangentBundleCore I M).coordChange_self (achart H α) x
    (by rw [tangentBundleCore_baseSet, coe_achart]; exact hx_src) v

/-- The (0, s)-tensor trivialization at `α` evaluates to the identity on
fibre elements at any point of the level set. -/
private lemma tensor0S_continuousLinearMapAt_levelSet_apply
    (s : ℕ) (α x : M) (hx : chartAt H x = chartAt H α)
    (p : Tensor0SSpace s I x) :
    (trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) α).continuousLinearMapAt ℝ x p = p := by
  have hx_src : x ∈ (chartAt H α).source := by
    have hxs : x ∈ (chartAt H x).source := ChartedSpace.mem_chart_source x
    rw [hx] at hxs
    exact hxs
  have hx_base : x ∈ (trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) α).baseSet := by
    change x ∈ (trivializationAt E (TangentSpace I) α).baseSet
    change x ∈ (chartAt H α).source
    exact hx_src
  have hcLMAt :
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).continuousLinearMapAt ℝ x p =
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α ⟨x, p⟩).2 := by
    change (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).linearMapAt ℝ x p = _
    rw [Bundle.Trivialization.linearMapAt_apply, if_pos hx_base]
  rw [hcLMAt]
  have happly : (trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) α ⟨x, p⟩).2 =
      p.compContinuousLinearMap
        (fun _ => (trivializationAt E (TangentSpace I) α).symmL ℝ x) := rfl
  rw [happly, tangent_symmL_levelSet (I := I) (M := M) α x hx]
  ext v
  change p (fun i => (1 : E →L[ℝ] E) (v i)) = p v
  congr

/-- The (0, s)-tensor trivialization at `α` has identity `symmL` on fibre
elements at any point of the level set. -/
private lemma tensor0S_symmL_levelSet_apply
    (s : ℕ) (α x : M) (hx : chartAt H x = chartAt H α)
    (p : Tensor0SModel s ℝ E) :
    (trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) α).symmL ℝ x p = p := by
  have hx_src : x ∈ (chartAt H α).source := by
    have hxs : x ∈ (chartAt H x).source := ChartedSpace.mem_chart_source x
    rw [hx] at hxs
    exact hxs
  have hx_base : x ∈ (trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) α).baseSet := by
    change x ∈ (trivializationAt E (TangentSpace I) α).baseSet
    change x ∈ (chartAt H α).source
    exact hx_src
  have hinv : (trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) α).continuousLinearMapAt ℝ x
      ((trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).symmL ℝ x p) = p :=
    Bundle.Trivialization.continuousLinearMapAt_symmL
      (R := ℝ) (e := trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α) hx_base p
  have hid := tensor0S_continuousLinearMapAt_levelSet_apply (I := I) (M := M) s α x hx
    ((trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).symmL ℝ x p)
  exact hid.symm.trans hinv

/-- Level-set identity for the `(r, s)`-tensor bundle: on the level set
`{x | chartAt H x = chartAt H α}`, the trivialization at `α` evaluated at
`⟨x, S.toSection x⟩` agrees with `S.toFun x`.

The proof unfolds the `(r, s)`-tensor trivialization to its
`ContinuousLinearMap.inCoordinates` formula, then collapses the two
`(0, ·)`-tensor coordinate maps to identities via the level-set lemmas above. -/
private lemma tensorRS_levelSet_identity
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) (α x : M)
    (hx : chartAt H x = chartAt H α) :
    (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α ⟨x, S.toSection x⟩).2 = S.toFun x := by
  have heq :
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α ⟨x, S.toSection x⟩).2 =
      ContinuousLinearMap.inCoordinates (Tensor0SModel r ℝ E) (Tensor0SSpace r I)
        (Tensor0SModel s ℝ E) (Tensor0SSpace s I) α x α x (S.toSection x) := by
    rfl
  rw [heq]
  ext v
  unfold ContinuousLinearMap.inCoordinates
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  rw [tensor0S_symmL_levelSet_apply (I := I) (M := M) r α x hx v]
  rw [tensor0S_continuousLinearMapAt_levelSet_apply (I := I) (M := M) s α x hx
    ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from S.toSection x) v)]
  rfl

/-- The underlying map `S.toFun : M → TensorRSModel r s ℝ E` of a smooth
compactly-supported `(r, s)`-tensor section is Borel-measurable. -/
theorem SmoothCcTensor.measurable_toFun
    [IsBorelChartedSpace H M] [Nonempty M]
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) :
    @Measurable M (TensorRSModel r s ℝ E) (borel M) _ S.toFun := by
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace (TensorRSModel r s ℝ E) := borel (TensorRSModel r s ℝ E)
  haveI : BorelSpace (TensorRSModel r s ℝ E) := ⟨rfl⟩
  classical
  have hcount := IsBorelChartedSpace.chartAt_range_countable (H := H) (M := M)
  have hmeas_lvl := IsBorelChartedSpace.measurableSet_chartAt_preimage (H := H) (M := M)
  have hrange_nonempty : (Set.range (fun y : M => chartAt H y)).Nonempty :=
    Set.range_nonempty (fun y : M => chartAt H y)
  obtain ⟨φ, hφ⟩ := hcount.exists_eq_range hrange_nonempty
  set s' : ℕ → Set M := fun n => {x : M | chartAt H x = φ n} with hs'_def
  have hs'meas : ∀ n, MeasurableSet (s' n) := fun n => hmeas_lvl (φ n)
  have hs'sub : ∀ n, s' n ⊆ (φ n).source := by
    intro n x hx
    have hxs : x ∈ (chartAt H x).source := ChartedSpace.mem_chart_source x
    have hxe : chartAt H x = φ n := hx
    rw [hxe] at hxs
    exact hxs
  have hs'ne : ∀ n, (s' n).Nonempty := by
    intro n
    have hin : φ n ∈ Set.range (fun y : M => chartAt H y) := by
      rw [hφ]; exact Set.mem_range_self n
    obtain ⟨x, hx⟩ := hin
    exact ⟨x, hx⟩
  choose xn hxn using hs'ne
  have hcov : (⋃ n, s' n) = univ := by
    refine Set.eq_univ_of_forall (fun x => ?_)
    have hxr : chartAt H x ∈ Set.range (fun y : M => chartAt H y) :=
      Set.mem_range_self x
    rw [hφ] at hxr
    obtain ⟨n, hn⟩ := hxr
    refine mem_iUnion.mpr ⟨n, ?_⟩
    change chartAt H x = φ n
    exact hn.symm
  set g_n : ℕ → M → TensorRSModel r s ℝ E := fun n x =>
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) (xn n) ⟨x, S.toSection x⟩).2
    with hg_n_def
  have hg_n_cont : ∀ n, ContinuousOn (g_n n) (chartAt H (xn n)).source := by
    intro n
    exact continuousOn_trivProj (I := I) (M := M) S (xn n)
  have hg_n_eq : ∀ n, ∀ x ∈ s' n, g_n n x = S.toFun x := by
    intro n x hx
    have hxφ : chartAt H x = φ n := hx
    have hxnφ : chartAt H (xn n) = φ n := hxn n
    have hx_eq : chartAt H x = chartAt H (xn n) := by rw [hxφ, hxnφ]
    exact tensorRS_levelSet_identity (I := I) (M := M) S (xn n) x hx_eq
  have hs'sub_chartXn : ∀ n, s' n ⊆ (chartAt H (xn n)).source := by
    intro n x hx
    have h1 : x ∈ (φ n).source := hs'sub n hx
    have hxnφ : chartAt H (xn n) = φ n := hxn n
    rw [hxnφ]
    exact h1
  refine measurable_of_isOpen ?_
  intro U hU
  have hpre : S.toFun ⁻¹' U = ⋃ n, S.toFun ⁻¹' U ∩ s' n := by
    ext x
    simp only [mem_preimage, mem_iUnion, mem_inter_iff]
    constructor
    · intro hx
      have hxc : x ∈ ⋃ n, s' n := by rw [hcov]; exact mem_univ x
      obtain ⟨n, hn⟩ := mem_iUnion.mp hxc
      exact ⟨n, hx, hn⟩
    · rintro ⟨n, hx, _⟩
      exact hx
  rw [hpre]
  refine MeasurableSet.iUnion (fun n => ?_)
  have heq_pre : S.toFun ⁻¹' U ∩ s' n = (g_n n) ⁻¹' U ∩ s' n := by
    ext x
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hxU, hxs⟩
      have h := hg_n_eq n x hxs
      rw [h]
      exact ⟨hxU, hxs⟩
    · rintro ⟨hxU, hxs⟩
      have h := hg_n_eq n x hxs
      rw [h] at hxU
      exact ⟨hxU, hxs⟩
  rw [heq_pre]
  have h1 : (g_n n) ⁻¹' U ∩ s' n =
      ((chartAt H (xn n)).source ∩ ((g_n n) ⁻¹' U)) ∩ s' n := by
    ext y
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hyU, hys⟩
      exact ⟨⟨hs'sub_chartXn n hys, hyU⟩, hys⟩
    · rintro ⟨⟨_, hyU⟩, hys⟩
      exact ⟨hyU, hys⟩
  rw [h1]
  have hopen : IsOpen ((chartAt H (xn n)).source ∩ (g_n n) ⁻¹' U) :=
    (hg_n_cont n).isOpen_inter_preimage (chartAt H (xn n)).open_source hU
  exact MeasurableSet.inter hopen.measurableSet (hs'meas n)

/-- The underlying map `S.toFun : M → TensorRSModel r s ℝ E` is strongly
measurable.  The codomain is finite-dimensional (since `E` is), hence has
`SecondCountableTopology`, so Borel-measurability and strong measurability
coincide. -/
theorem SmoothCcTensor.stronglyMeasurable_toFun
    [IsBorelChartedSpace H M] [Nonempty M]
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) :
    @StronglyMeasurable M (TensorRSModel r s ℝ E) _ (borel M) S.toFun := by
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  letI : MeasurableSpace (TensorRSModel r s ℝ E) := borel (TensorRSModel r s ℝ E)
  haveI : BorelSpace (TensorRSModel r s ℝ E) := ⟨rfl⟩
  have hmeas := SmoothCcTensor.measurable_toFun (I := I) (M := M) S
  exact hmeas.stronglyMeasurable

/-- Almost-everywhere strong measurability of `S.toFun` against any measure.
This is the typical entry point for use within `Lp` / `Memℒp` arguments.

The Borel σ-algebra on `M` is installed inside the body, so the measure
parameter `μ` is supplied via a `letI`-bound `MeasurableSpace` instance to keep
the public signature free of measurable-space typeclass parameters. -/
theorem SmoothCcTensor.aestronglyMeasurable_toFun
    [IsBorelChartedSpace H M] [Nonempty M]
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s)
    (μ : letI : MeasurableSpace M := borel M; MeasureTheory.Measure M) :
    letI : MeasurableSpace M := borel M
    AEStronglyMeasurable S.toFun μ := by
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  exact (SmoothCcTensor.stronglyMeasurable_toFun (I := I) (M := M) S).aestronglyMeasurable

end BorelManifold

end Measure
end Integral
end DifferentialGeometry

end
