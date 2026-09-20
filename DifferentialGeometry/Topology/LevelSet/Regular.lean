import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Analysis.Convex.PathConnected

section

noncomputable section

open Set
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_local_coordinates_of_fderiv_ne_zero
    (hdim : Module.finrank ℝ E = 2) {f : E → ℝ} {p : E}
    (hf : ContDiffAt ℝ 1 f p) (hdf : fderiv ℝ f p ≠ 0)
    {D : Set E} (hD : IsOpen D) (hp : p ∈ D) :
    ∃ e : OpenPartialHomeomorph (ℝ × ℝ) E,
      (0 : ℝ × ℝ) ∈ e.source ∧ e 0 = p ∧ e.target ⊆ D ∧
      ∀ z ∈ e.source, f (e z) = f p + z.2 := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let L := fderiv ℝ f p
  have hLn : L.toLinearMap ≠ 0 := by
    intro h
    apply hdf
    exact ContinuousLinearMap.coe_injective h
  have hLr : L.range = ⊤ := Module.Dual.range_eq_top_of_ne_zero hLn
  have hLk : L.ker.ClosedComplemented := L.ker_closedComplemented_of_finiteDimensional_range
  have hkdim : Module.finrank ℝ L.ker = Module.finrank ℝ ℝ := by
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero hLn
    rw [hdim] at h
    rw [Module.finrank_self]
    omega
  let k : L.ker ≃L[ℝ] ℝ := ContinuousLinearEquiv.ofFinrankEq hkdim
  have hstrict : HasStrictFDerivAt f L p := hf.hasStrictFDerivAt (by norm_num)
  let φ₀ := hstrict.implicitToOpenPartialHomeomorphOfComplemented f L hLr hLk
  let φ := φ₀.restrOpen D hD
  have hpφ : p ∈ φ.source :=
    ⟨hstrict.mem_implicitToOpenPartialHomeomorphOfComplemented_source hLr hLk, hp⟩
  have hφp : φ p = (f p, 0) :=
    hstrict.implicitToOpenPartialHomeomorphOfComplemented_self hLr hLk
  let ψ : (ℝ × ℝ) ≃ₜ (ℝ × L.ker) := {
    toFun := fun z => (f p + z.2, k.symm z.1)
    invFun := fun z => (k z.2, z.1 - f p)
    left_inv := by intro z; simp
    right_inv := by intro z; simp
    continuous_toFun :=
      (continuous_const.add continuous_snd).prodMk (k.symm.continuous.comp continuous_fst)
    continuous_invFun :=
      (k.continuous.comp continuous_snd).prodMk (continuous_fst.sub continuous_const) }
  let e := ψ.toOpenPartialHomeomorph.trans φ.symm
  have hψ0 : ψ 0 = φ p := by rw [hφp]; simp [ψ]
  have hsource : (0 : ℝ × ℝ) ∈ e.source := by
    refine ⟨mem_univ _, ?_⟩
    change ψ 0 ∈ φ.target
    rw [hψ0]
    exact φ.map_source hpφ
  refine ⟨e, hsource, ?_, ?_, ?_⟩
  · change φ.symm (ψ 0) = p
    rw [hψ0]
    exact φ.left_inv hpφ
  · intro x hx
    exact hx.1.2
  · intro z hz
    have hzt : ψ z ∈ φ.target := hz.2
    have hval := congrArg Prod.fst (φ.right_inv hzt)
    change f (φ.symm (ψ z)) = f p + z.2 at hval
    exact hval

end DifferentialGeometry.Analysis

end

end

section

noncomputable section

open Set Metric Filter
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem mem_closure_strict_levels_of_fderiv_ne_zero
    (hdim : Module.finrank ℝ E = 2) {f : E → ℝ} {p : E}
    (hf : ContDiffAt ℝ 1 f p) (hdf : fderiv ℝ f p ≠ 0)
    {D : Set E} (hD : IsOpen D) (hp : p ∈ D) :
    p ∈ closure {x | x ∈ D ∧ f p < f x} ∧
      p ∈ closure {x | x ∈ D ∧ f x < f p} := by
  obtain ⟨e, he0, hep, heD, heval⟩ := exists_local_coordinates_of_fderiv_ne_zero hdim hf hdf hD hp
  change e (0, 0) = p at hep
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp (e.open_source.mem_nhds he0)
  have hsource (t : ℝ) (ht : |t| < r) : ((0 : ℝ), t) ∈ e.source := by
    apply hrsub
    rw [mem_ball, Prod.dist_eq]
    change max (dist (0 : ℝ) 0) (dist t 0) < r
    simpa only [dist_self, dist_zero_right, Real.norm_eq_abs, max_lt_iff] using And.intro hr ht
  have hcont : ContinuousAt (fun t : ℝ => e (0, t)) 0 :=
    (e.continuousOn.continuousAt (e.open_source.mem_nhds he0)).comp_of_eq
      (show ContinuousAt (fun t : ℝ => ((0 : ℝ), t)) 0 from
        (continuous_const.prodMk continuous_id).continuousAt) rfl
  have hpos : e (0, 0) ∈ closure {x | x ∈ D ∧ f p < f x} := by
    apply hcont.continuousWithinAt.mem_closure
      (show (0 : ℝ) ∈ closure (Ioo 0 r) by
        rw [closure_Ioo (by linarith : (0 : ℝ) ≠ r)]
        exact ⟨le_rfl, hr.le⟩)
    intro t ht
    have htS := hsource t (by rw [abs_of_pos ht.1]; exact ht.2)
    refine ⟨heD (e.map_source htS), ?_⟩
    rw [heval _ htS]
    exact lt_add_of_pos_right _ ht.1
  have hneg : e (0, 0) ∈ closure {x | x ∈ D ∧ f x < f p} := by
    apply hcont.continuousWithinAt.mem_closure
      (show (0 : ℝ) ∈ closure (Ioo (-r) 0) by
        rw [closure_Ioo (neg_lt_zero.mpr hr).ne]; exact ⟨by linarith, le_rfl⟩)
    intro t ht
    have htS := hsource t (by rw [abs_of_neg ht.2]; linarith [ht.1])
    refine ⟨heD (e.map_source htS), ?_⟩
    rw [heval _ htS]
    exact add_lt_of_neg_right _ ht.2
  simpa only [hep] using And.intro hpos hneg

end DifferentialGeometry.Analysis

end

end

section

noncomputable section

open Set Metric Filter
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_open_isPathConnected_level_inter
    (hdim : Module.finrank ℝ E = 2) {f : E → ℝ} {p : E}
    (hf : ContDiffAt ℝ 1 f p) (hdf : fderiv ℝ f p ≠ 0)
    {D : Set E} (hD : IsOpen D) (hp : p ∈ D) :
    ∃ W : Set E, IsOpen W ∧ p ∈ W ∧ W ⊆ D ∧
      IsPathConnected (W ∩ {x | f x = f p}) := by
  obtain ⟨e, he0, hep, heD, heval⟩ := exists_local_coordinates_of_fderiv_ne_zero hdim hf hdf hD hp
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp (e.open_source.mem_nhds he0)
  let W := e '' ball (0 : ℝ × ℝ) r
  have hline (t : ℝ) (ht : t ∈ Ioo (-r) r) : (t, (0 : ℝ)) ∈ ball (0 : ℝ × ℝ) r := by
    rw [mem_ball, Prod.dist_eq]
    change max (dist t 0) (dist (0 : ℝ) 0) < r
    simpa only [dist_self, dist_zero_right, Real.norm_eq_abs, max_lt_iff] using
      And.intro (abs_lt.mpr ht) hr
  have heq : W ∩ {x | f x = f p} = (fun t : ℝ => e (t, 0)) '' Ioo (-r) r := by
    ext x
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hzlevel⟩
      have hz0 : z.2 = 0 := by
        have h := heval z (hrsub hz)
        change f (e z) = f p at hzlevel
        linarith
      have hz1 : z.1 ∈ Ioo (-r) r := by
        rw [mem_ball, Prod.dist_eq] at hz
        have h := (max_lt_iff.mp hz).1
        change dist z.1 0 < r at h
        simpa only [dist_zero_right, Real.norm_eq_abs, abs_lt, mem_Ioo] using h
      exact ⟨z.1, hz1, congrArg e (Prod.ext rfl hz0.symm)⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨(t, 0), hline t ht, rfl⟩, by simpa using heval (t, 0) (hrsub (hline t ht))⟩
  refine ⟨W, e.isOpen_image_of_subset_source isOpen_ball hrsub,
    hep ▸ mem_image_of_mem e (mem_ball_self hr), ?_, ?_⟩
  · rintro x ⟨z, hz, rfl⟩
    exact heD (e.map_source (hrsub hz))
  · rw [heq]
    apply ((convex_Ioo (-r) r).isPathConnected ⟨0, by constructor <;> linarith⟩).image'
    exact e.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => hrsub (hline t ht))

theorem locallyPathConnectedSpace_level_of_fderiv_ne_zero
    (hdim : Module.finrank ℝ E = 2) {f : E → ℝ} {D : Set E} (hD : IsOpen D) (a : ℝ)
    (hf : ∀ p ∈ D, f p = a → ContDiffAt ℝ 1 f p)
    (hdf : ∀ p ∈ D, f p = a → fderiv ℝ f p ≠ 0) :
    LocallyPathConnectedSpace {x : E // x ∈ D ∧ f x = a} := by
  let L := {x : E | x ∈ D ∧ f x = a}
  refine ⟨fun p => ?_⟩
  rw [Filter.hasBasis_self]
  intro s hs
  obtain ⟨T, hTs, hT, hpT⟩ := _root_.mem_nhds_iff.mp hs
  obtain ⟨U, hU, hUT⟩ := _root_.Topology.IsInducing.subtypeVal.isOpen_iff.mp hT
  have hpU : (p : E) ∈ U := by
    have h := Set.ext_iff.mp hUT p
    exact h.mpr hpT
  obtain ⟨W, hW, hpW, hWD, hc⟩ := exists_open_isPathConnected_level_inter hdim
    (hf p p.property.1 p.property.2) (hdf p p.property.1 p.property.2)
    (hD.inter hU) ⟨p.property.1, hpU⟩
  let A := W ∩ {x : E | f x = a}
  have hAc : IsPathConnected A := by simpa only [p.property.2] using hc
  have hAL : A ⊆ L := fun x hx => ⟨(hWD hx.1).1, hx.2⟩
  have hpre : ((↑) : L → E) ⁻¹' A = ((↑) : L → E) ⁻¹' W := by
    ext x
    exact and_iff_left x.property.2
  refine ⟨((↑) : L → E) ⁻¹' A, ?_, hAc.preimage_coe hAL, ?_⟩
  · rw [hpre]
    exact (hW.preimage continuous_subtype_val).mem_nhds hpW
  · intro x hx
    apply hTs
    exact (Set.ext_iff.mp hUT x).mp (hWD hx.1).2

end DifferentialGeometry.Analysis

end

end
