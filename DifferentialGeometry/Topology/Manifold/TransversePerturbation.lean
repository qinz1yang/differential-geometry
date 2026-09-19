import DifferentialGeometry.Topology.Manifold.MapPerturbation
import DifferentialGeometry.Topology.Manifold.Coincidences
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Chart
import DifferentialGeometry.Topology.Compactness.FiniteRefinement
import DifferentialGeometry.Analysis.Calculus.CurvePerturbation
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Manifold

variable {E F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem exists_small_curve_chart_perturbation_transverse_on_disjoint_arcs
    (e : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞)
    {γ : ℝ × ℝ → M} {S : Set (ℝ × ℝ)}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ γ S)
    {p₀ : ℝ × ℝ} (φ : ContDiffBump p₀)
    (hsupp : closedBall p₀ φ.rOut ⊆ S ∩ γ ⁻¹' e.source)
    {U : Set (ℝ × ℝ × ℝ)} (hU : IsOpen U)
    (hpairs : ∀ q ∈ U,
      (q.1, q.2.1) ∈ S ∩ γ ⁻¹' e.source ∧ (q.1, q.2.2) ∈ S ∩ γ ⁻¹' e.source)
    (hleft : ∀ q ∈ U, (q.1, q.2.1) ∈ closedBall p₀ φ.rIn)
    (hright : ∀ q ∈ U, φ.rOut ≤ dist (q.1, q.2.2) p₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (v : F) (β : ℝ × ℝ → M),
      ‖v‖ < ε ∧
      β = e.patchMap γ (fun p => e (γ p) - φ p • v) ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ).prod I) ∞ (fun p => (p.1, β p)) S ∧
      (∀ p, φ.rOut ≤ dist p p₀ → β p = γ p) ∧
      (∀ p, γ p ∈ e.source →
        β p ∈ e.source ∧ e (β p) = e (γ p) - φ p • v ∧
          ‖e (β p) - e (γ p)‖ < ε) ∧
      ∀ q ∈ U, β (q.1, q.2.1) = β (q.1, q.2.2) →
        Function.Surjective (fderiv ℝ (fun r : ℝ × ℝ × ℝ =>
          e (β (r.1, r.2.1)) - e (β (r.1, r.2.2))) q) := by
  let c : ℝ × ℝ → F := fun p => e (γ p)
  have hc : ContDiffOn ℝ ∞ c (S ∩ γ ⁻¹' e.source) :=
    (e.contMDiffOn.comp (hγ.mono inter_subset_left) inter_subset_right).contDiffOn
  obtain ⟨v, hv, _, _, hfix, hsmall, htarget, _, htrans⟩ :=
    Calculus.exists_small_curve_perturbation_transverse_on_disjoint_arcs hc φ e.open_target
      hsupp (fun p hp => e.map_source (hsupp hp).2) hU hpairs hleft hright hε
  let d : ℝ × ℝ → F := fun p => c p - φ p • v
  let β := e.patchMap γ d
  have hβ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ β S := by
    apply e.contMDiffOn_patchMap hγ
      (hc.sub (φ.contDiff.contDiffOn.smul contDiffOn_const)).contMDiffOn
      (fun p hp => htarget p (e.map_source hp.2)) isClosed_closedBall
    · intro p hp
      exact (hsupp hp.2).2
    · intro p _ hp
      exact hfix p (not_le.mp hp).le
  have hcoords (p : ℝ × ℝ) (hp : γ p ∈ e.source) :
      β p ∈ e.source ∧ e (β p) = d p :=
    ⟨e.patchMap_mem_source γ d hp (htarget p (e.map_source hp)),
      e.apply_patchMap γ d hp (htarget p (e.map_source hp))⟩
  refine ⟨v, β, hv, rfl, contDiffOn_fst.contMDiffOn.prodMk hβ, ?_, ?_, ?_⟩
  · intro p hp
    exact e.patchMap_eq_self γ d (hfix p hp)
  · intro p hp
    refine ⟨(hcoords p hp).1, (hcoords p hp).2, ?_⟩
    rw [(hcoords p hp).2]
    exact hsmall p
  · intro q hq hcollision
    have heq : (fun r : ℝ × ℝ × ℝ => e (β (r.1, r.2.1)) - e (β (r.1, r.2.2)))
        =ᶠ[𝓝 q] (fun r => d (r.1, r.2.1) - d (r.1, r.2.2)) := by
      filter_upwards [hU.mem_nhds hq] with r hr
      rw [(hcoords _ (hpairs r hr).1.2).2, (hcoords _ (hpairs r hr).2.2).2]
    rw [heq.fderiv_eq]
    apply htrans q hq
    exact (hcoords _ (hpairs q hq).1.2).2.symm.trans
      ((congrArg e hcollision).trans (hcoords _ (hpairs q hq).2.2).2)

end DifferentialGeometry.Manifold

end

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff Manifold
namespace DifferentialGeometry.Manifold

variable {E F H Q : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace Q] [ChartedSpace H Q]

theorem exists_norm_lt_regular_value_on_partialDiffeomorph
    (a : PartialDiffeomorph I 𝓘(ℝ, E) Q E ∞)
    {f : Q → F} {U : Set Q} (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f U)
    (hU : IsOpen U) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : F, ‖v‖ < ε ∧ ∀ q ∈ U ∩ a.source, f q = v →
      Function.Surjective (mfderiv I 𝓘(ℝ, F) f q) := by
  borelize F
  let μ : Measure F := MeasureTheory.Measure.addHaar
  let V : Set E := a.target ∩ a.symm ⁻¹' U
  let g : E → F := f ∘ a.symm
  have hV : IsOpen V := a.toOpenPartialHomeomorph.isOpen_inter_preimage_symm hU
  have hg : ContDiffOn ℝ ∞ g V :=
    (hf.comp (a.symm.contMDiffOn.mono inter_subset_left) inter_subset_right).contDiffOn
  have hnull : μ (g '' {z | z ∈ V ∧ ¬ Function.Surjective (fderiv ℝ g z)}) = 0 :=
    hg.sard hV μ
  have hae : ∀ᵐ v ∂μ, ∀ z ∈ V, g z = v → Function.Surjective (fderiv ℝ g z) := by
    filter_upwards [(measure_eq_zero_iff_ae_notMem).mp hnull] with v hv z hz heq
    by_contra hn
    exact hv ⟨z, ⟨hz, hn⟩, heq⟩
  obtain ⟨v, hv, hreg⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (measure_ball_pos μ 0 hε).ne' (ae_restrict_of_ae hae)
  refine ⟨v, by simpa only [mem_ball, dist_zero_right] using hv, ?_⟩
  intro q hq hqv
  have hqa : a.symm (a q) = q := a.left_inv hq.2
  have hz : a q ∈ V := ⟨a.map_source hq.2, by change a.symm (a q) ∈ U; rw [hqa]; exact hq.1⟩
  have hsurj : Function.Surjective (fderiv ℝ g (a q)) :=
    hreg _ hz (by change f (a.symm (a q)) = v; rw [hqa]; exact hqv)
  have hinv := a.symm.mdifferentiableAt (by simp) (a.map_source hq.2)
  have hf' : MDifferentiableAt I 𝓘(ℝ, F) f (a.symm (a q)) := by
    rw [hqa]
    exact (hf.contMDiffAt (hU.mem_nhds hq.1)).mdifferentiableAt (by simp)
  have heq := mfderiv_comp (a q) hf' hinv
  rw [mfderiv_eq_fderiv, hqa] at heq
  change Function.Surjective (fderiv ℝ (f ∘ a.symm) (a q)) at hsurj
  rw [heq] at hsurj
  intro z
  obtain ⟨w, hw⟩ := hsurj z
  exact ⟨mfderiv 𝓘(ℝ, E) I a.symm (a q) w, hw⟩

end DifferentialGeometry.Manifold

namespace DifferentialGeometry.Manifold

variable {E F EP EQ H HP HQ M P Q : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [FiniteDimensional ℝ EQ]
  [TopologicalSpace H] [TopologicalSpace HP] [TopologicalSpace HQ]
  {I : ModelWithCorners ℝ E H} {IP : ModelWithCorners ℝ EP HP}
  {IQ : ModelWithCorners ℝ EQ HQ}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace P] [ChartedSpace HP P]
  [TopologicalSpace Q] [ChartedSpace HQ Q]

theorem exists_small_chart_perturbation_transverse_on_pair_region
    (e : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞)
    (a : PartialDiffeomorph IQ 𝓘(ℝ, EQ) Q EQ ∞)
    {f : P → M} {ρ : P → ℝ} {S : Set P}
    (hf : ContMDiffOn IP I ∞ f S) (hρ : ContMDiffOn IP 𝓘(ℝ) ∞ ρ S)
    (hcompact : IsCompact (S ∩ tsupport ρ)) (hsupport : S ∩ tsupport ρ ⊆ f ⁻¹' e.source)
    (hbound : ∀ x, ‖ρ x‖ ≤ 1)
    {U : Set Q} (hU : IsOpen U) {l r : Q → P}
    (hl : ContMDiffOn IQ IP ∞ l U) (hr : ContMDiffOn IQ IP ∞ r U)
    (hlmap : MapsTo l U (S ∩ f ⁻¹' e.source))
    (hrmap : MapsTo r U (S ∩ f ⁻¹' e.source))
    (hleft : ∀ q ∈ U, ρ (l q) = 1) (hright : ∀ q ∈ U, ρ (r q) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (v : F) (β : P → M), ‖v‖ < ε ∧
      β = e.patchMap f (fun p => e (f p) - ρ p • v) ∧
      ContMDiffOn IP I ∞ β S ∧
      (∀ p, p ∉ tsupport ρ → β p = f p) ∧
      (∀ p ∈ S, f p ∈ e.source →
        β p ∈ e.source ∧ e (β p) = e (f p) - ρ p • v ∧
          ‖e (β p) - e (f p)‖ < ε) ∧
      ∀ q ∈ U ∩ a.source, β (l q) = β (r q) →
        Function.Surjective ((show EQ →L[ℝ] E from mfderiv IQ I (β ∘ l) q) -
          (show EQ →L[ℝ] E from mfderiv IQ I (β ∘ r) q)) := by
  obtain ⟨δ, hδ, hjoint, htarget, hfixed, _, hsmall⟩ :=
    e.exists_pos_contMDiffOn_patchMap_bump hf hρ hcompact hsupport hbound
  let D : Q → F := fun q => e (f (l q)) - e (f (r q))
  have hc : ContMDiffOn IP 𝓘(ℝ, F) ∞ (fun p => e (f p)) (S ∩ f ⁻¹' e.source) :=
    e.contMDiffOn.comp (hf.mono inter_subset_left) inter_subset_right
  have hD : ContMDiffOn IQ 𝓘(ℝ, F) ∞ D U :=
    (hc.comp hl hlmap).sub (hc.comp hr hrmap)
  obtain ⟨v, hv, hreg⟩ := exists_norm_lt_regular_value_on_partialDiffeomorph a hD hU
    (lt_min hε hδ)
  have hvε : ‖v‖ < ε := hv.trans_le (min_le_left _ _)
  have hvδ : ‖v‖ < δ := hv.trans_le (min_le_right _ _)
  let d : P → F := fun p => e (f p) - ρ p • v
  let β := e.patchMap f d
  have hβ : ContMDiffOn IP I ∞ β S :=
    hjoint.comp (contMDiffOn_const.prodMk contMDiffOn_id)
      (fun p hp => ⟨by simpa only [mem_ball, dist_zero_right] using hvδ, hp⟩)
  have hcoords (p : P) (hp : p ∈ S) (hpf : f p ∈ e.source) :
      β p ∈ e.source ∧ e (β p) = d p :=
    ⟨e.patchMap_mem_source f d hpf (htarget v hvδ p hp hpf),
      e.apply_patchMap f d hpf (htarget v hvδ p hp hpf)⟩
  refine ⟨v, β, hvε, rfl, hβ, hfixed v, ?_, ?_⟩
  · intro p hp hpf
    refine ⟨(hcoords p hp hpf).1, (hcoords p hp hpf).2, ?_⟩
    rw [(hcoords p hp hpf).2]
    exact (hsmall v p).trans_lt hvε
  · intro q hq hcollision
    have hgl : MDifferentiableAt IQ I (β ∘ l) q :=
      ((hβ.comp hl (fun z hz => (hlmap hz).1)).contMDiffAt
        (hU.mem_nhds hq.1)).mdifferentiableAt (by simp)
    have hgr : MDifferentiableAt IQ I (β ∘ r) q :=
      ((hβ.comp hr (fun z hz => (hrmap hz).1)).contMDiffAt
        (hU.mem_nhds hq.1)).mdifferentiableAt (by simp)
    apply (surjective_mfderiv_coincidence_iff_in_chart e (by simp) hgl hgr hcollision
      (hcoords _ (hlmap hq.1).1 (hlmap hq.1).2).1).mp
    have heq : (fun z => e (β (l z)) - e (β (r z))) =ᶠ[𝓝 q] (fun z => D z - v) := by
      filter_upwards [hU.mem_nhds hq.1] with z hz
      rw [(hcoords _ (hlmap hz).1 (hlmap hz).2).2,
        (hcoords _ (hrmap hz).1 (hrmap hz).2).2]
      dsimp only [d, D]
      rw [hleft z hz, hright z hz, one_smul, zero_smul, sub_zero]
      abel
    have hderiv : mfderiv IQ 𝓘(ℝ, F) (fun z => D z - v) q =
        mfderiv IQ 𝓘(ℝ, F) D q := by
      change mfderiv IQ 𝓘(ℝ, F) (D - fun _ => v) q = _
      rw [mfderiv_sub ((hD.contMDiffAt (hU.mem_nhds hq.1)).mdifferentiableAt (by simp))
        mdifferentiableAt_const, mfderiv_const]
      exact sub_zero _
    dsimp only [Function.comp_apply]
    rw [heq.mfderiv_eq, hderiv]
    apply hreg q hq
    have hzero : e (β (l q)) - e (β (r q)) = 0 := by rw [hcollision, sub_self]
    rw [heq.eq_of_nhds] at hzero
    exact sub_eq_zero.mp hzero

end DifferentialGeometry.Manifold

namespace DifferentialGeometry.Manifold

variable {E F EP EQ H HP HQ M P Q : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP]
  [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [FiniteDimensional ℝ EQ]
  [TopologicalSpace H] [TopologicalSpace HP] [TopologicalSpace HQ]
  {I : ModelWithCorners ℝ E H} {IP : ModelWithCorners ℝ EP HP}
  {IQ : ModelWithCorners ℝ EQ HQ} [IQ.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace P] [ChartedSpace HP P] [T2Space P] [IsManifold IP ∞ P]
  [TopologicalSpace Q] [ChartedSpace HQ Q] [IsManifold IQ ∞ Q]

theorem exists_local_chart_perturbation_transverse
    (e : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞)
    {f : P → M} {S : Set P} (hf : ContMDiffOn IP I ∞ f S) (hS : IsOpen S)
    {l r : Q → P} (hl : ContMDiff IQ IP ∞ l) (hr : ContMDiff IQ IP ∞ r)
    (q₀ : Q) (hlS : l q₀ ∈ S) (hrS : r q₀ ∈ S) (hneq : l q₀ ≠ r q₀)
    (hlchart : f (l q₀) ∈ e.source) (hrchart : f (r q₀) ∈ e.source) :
    ∃ (ρ : P → ℝ) (U : Set Q) (δ : ℝ),
      ContMDiff IP 𝓘(ℝ) ∞ ρ ∧ HasCompactSupport ρ ∧
      (∀ x, ρ x ∈ Icc (0 : ℝ) 1) ∧ tsupport ρ ⊆ S ∩ f ⁻¹' e.source ∧
      IsOpen U ∧ q₀ ∈ U ∧
      (∀ q ∈ U, ρ (l q) = 1 ∧ ρ (r q) = 0 ∧
        l q ∈ S ∩ f ⁻¹' e.source ∧ r q ∈ S ∩ f ⁻¹' e.source) ∧ 0 < δ ∧
      ContMDiffOn (𝓘(ℝ, F).prod IP) I ∞
        (fun q : F × P => e.patchMap f (fun x => e (f x) - ρ x • q.1) q.2)
        (ball 0 δ ×ˢ S) ∧
      ∀ ε > 0, ∃ (v : F) (β : P → M), ‖v‖ < ε ∧
        β = e.patchMap f (fun p => e (f p) - ρ p • v) ∧
        ContMDiffOn IP I ∞ β S ∧
        (∀ p, p ∉ tsupport ρ → β p = f p) ∧
        (∀ p ∈ S, f p ∈ e.source →
          β p ∈ e.source ∧ e (β p) = e (f p) - ρ p • v ∧
            ‖e (β p) - e (f p)‖ < ε) ∧
        ∀ q ∈ U, β (l q) = β (r q) →
          Function.Surjective ((show EQ →L[ℝ] E from mfderiv IQ I (β ∘ l) q) -
            (show EQ →L[ℝ] E from mfderiv IQ I (β ∘ r) q)) := by
  let V : Set P := S ∩ f ⁻¹' e.source
  have hV : IsOpen V := hf.continuousOn.isOpen_inter_preimage hS e.open_source
  have hleftV : l q₀ ∈ V := ⟨hlS, hlchart⟩
  have hrightV : r q₀ ∈ V := ⟨hrS, hrchart⟩
  obtain ⟨φ, _, hφ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := IP) (l q₀)).mem_iff.mp
    (inter_mem (hV.mem_nhds hleftV)
      (isClosed_singleton.isOpen_compl.mem_nhds hneq))
  have hsupp : tsupport φ ⊆ S ∩ f ⁻¹' e.source := fun _ h => (hφ h).1
  have hcompact : IsCompact (S ∩ tsupport φ) := by
    rw [inter_eq_right.mpr (hsupp.trans inter_subset_left)]
    exact φ.hasCompactSupport
  have hzero : (φ : P → ℝ) =ᶠ[𝓝 (r q₀)] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp (fun h => (hφ h).2 (mem_singleton _))
  let a := DifferentialGeometry.PartialDiffeomorph.extChartAt IQ ∞ q₀
  have hqa : q₀ ∈ a.source := mem_extChartAt_source q₀
  have hev : ∀ᶠ q in 𝓝 q₀,
      q ∈ a.source ∧ φ (l q) = 1 ∧ φ (r q) = 0 ∧ l q ∈ V ∧ r q ∈ V := by
    filter_upwards [a.open_source.mem_nhds hqa,
      hl.continuous.continuousAt.tendsto.eventually φ.eventuallyEq_one,
      hr.continuous.continuousAt.tendsto.eventually hzero,
      hl.continuous.continuousAt.preimage_mem_nhds (hV.mem_nhds hleftV),
      hr.continuous.continuousAt.preimage_mem_nhds (hV.mem_nhds hrightV)] with q hqa h1 h0 hlq hrq
    exact ⟨hqa, h1, h0, hlq, hrq⟩
  obtain ⟨U, hUall, hU, hqU⟩ := eventually_nhds_iff.mp hev
  have hbound (x : P) : ‖φ x‖ ≤ 1 := by
    rw [Real.norm_of_nonneg φ.nonneg]
    exact φ.le_one
  have hsupp' : S ∩ tsupport φ ⊆ f ⁻¹' e.source := fun _ h => (hsupp h.2).2
  obtain ⟨δ, hδ, hjoint, _, _, _, _⟩ :=
    e.exists_pos_contMDiffOn_patchMap_bump hf φ.contMDiff.contMDiffOn hcompact hsupp' hbound
  refine ⟨φ, U, δ, φ.contMDiff, φ.hasCompactSupport, fun _ => ⟨φ.nonneg, φ.le_one⟩,
    hsupp, hU, hqU, fun q hq => (hUall q hq).2, hδ, hjoint, ?_⟩
  intro ε hε
  obtain ⟨v, β, hv, hβdef, hβ, hfixed, hcoords, htrans⟩ :=
    exists_small_chart_perturbation_transverse_on_pair_region e a hf φ.contMDiff.contMDiffOn
      hcompact hsupp' hbound hU hl.contMDiffOn hr.contMDiffOn
      (fun q hq => (hUall q hq).2.2.2.1)
      (fun q hq => (hUall q hq).2.2.2.2)
      (fun q hq => (hUall q hq).2.1) (fun q hq => (hUall q hq).2.2.1) hε
  exact ⟨v, β, hv, hβdef, hβ, hfixed, hcoords,
    fun q hq => htrans q ⟨hq, (hUall q hq).1⟩⟩

end DifferentialGeometry.Manifold

end

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Manifold

variable {E EP EQ H HP HQ M P Q : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP]
  [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [FiniteDimensional ℝ EQ]
  [TopologicalSpace H] [TopologicalSpace HP] [TopologicalSpace HQ]
  {I : ModelWithCorners ℝ E H} {IP : ModelWithCorners ℝ EP HP}
  {IQ : ModelWithCorners ℝ EQ HQ} [I.Boundaryless] [IQ.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [TopologicalSpace P] [ChartedSpace HP P] [T2Space P] [IsManifold IP ∞ P]
  [TopologicalSpace Q] [ChartedSpace HQ Q] [T2Space Q] [IsManifold IQ ∞ Q]

theorem exists_finite_compact_coincidence_cover
    {f : P → M} (hf : ContMDiff IP I ∞ f)
    {l r : Q → P} (hl : ContMDiff IQ IP ∞ l) (hr : ContMDiff IQ IP ∞ r)
    {K : Set Q} (hK : IsCompact K) (hneq : ∀ q ∈ K, l q ≠ r q) :
    let Z : Set Q := {q | q ∈ K ∧ f (l q) = f (r q)}
    ∃ (t : Finset Z)
      (e : Z → PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)
      (a : Z → PartialDiffeomorph IQ 𝓘(ℝ, EQ) Q EQ ∞)
      (ρ : Z → P → ℝ) (U A : Z → Set Q) (B : Z → Set P),
      (∀ i : Z,
        ContMDiff IP 𝓘(ℝ) ∞ (ρ i) ∧ HasCompactSupport (ρ i) ∧
        (∀ x, ρ i x ∈ Icc (0 : ℝ) 1) ∧
        IsOpen (U i) ∧ (i : Q) ∈ U i ∧ IsCompact (closure (U i)) ∧
        IsCompact (A i) ∧ A i ⊆ U i ∧ closure (U i) ⊆ (a i).source ∧
        IsCompact (B i) ∧ tsupport (ρ i) ⊆ B i ∧
        MapsTo l (closure (U i)) (B i) ∧ MapsTo r (closure (U i)) (B i) ∧
        B i ⊆ f ⁻¹' (e i).source ∧
        ∀ q ∈ closure (U i), ρ i (l q) = 1 ∧ ρ i (r q) = 0) ∧
      Z ⊆ ⋃ i ∈ t, interior (A i) := by
  classical
  let _ : LocallyCompactSpace Q := _root_.Manifold.locallyCompact_of_finiteDimensional IQ
  let Z : Set Q := {q | q ∈ K ∧ f (l q) = f (r q)}
  have hZ : IsCompact Z := hK.inter_right
    (isClosed_eq (hf.continuous.comp hl.continuous) (hf.continuous.comp hr.continuous))
  let e : Z → PartialDiffeomorph I 𝓘(ℝ, E) M E ∞ :=
    fun i => DifferentialGeometry.PartialDiffeomorph.extChartAt I ∞ (f (l i))
  let a : Z → PartialDiffeomorph IQ 𝓘(ℝ, EQ) Q EQ ∞ :=
    fun i => DifferentialGeometry.PartialDiffeomorph.extChartAt IQ ∞ (i : Q)
  have hlocal (i : Z) : ∃ (ρ : P → ℝ) (U : Set Q) (B : Set P),
      ContMDiff IP 𝓘(ℝ) ∞ ρ ∧ HasCompactSupport ρ ∧
      (∀ x, ρ x ∈ Icc (0 : ℝ) 1) ∧ IsOpen U ∧ (i : Q) ∈ U ∧
      IsCompact (closure U) ∧ closure U ⊆ (a i).source ∧
      IsCompact B ∧ tsupport ρ ⊆ B ∧
      MapsTo l (closure U) B ∧ MapsTo r (closure U) B ∧
      B ⊆ f ⁻¹' (e i).source ∧
      ∀ q ∈ closure U, ρ (l q) = 1 ∧ ρ (r q) = 0 := by
    have hlchart : f (l i) ∈ (e i).source := mem_extChartAt_source (f (l i))
    have hrchart : f (r i) ∈ (e i).source := i.property.2 ▸ hlchart
    obtain ⟨ρ, V, δ, hρ, hcompact, hbound, hsupp, hV, hiV, hpairs, _, _, _⟩ :=
      exists_local_chart_perturbation_transverse (e i) hf.contMDiffOn isOpen_univ hl hr
        (i : Q) (mem_univ _) (mem_univ _) (hneq i i.property.1) hlchart hrchart
    have hisource : (i : Q) ∈ (a i).source := mem_extChartAt_source (I := IQ) (i : Q)
    obtain ⟨U, hU, hiU, hUV, hUc⟩ := exists_open_between_and_isCompact_closure
      (isCompact_singleton (x := (i : Q))) (hV.inter (a i).open_source)
      (singleton_subset_iff.mpr ⟨hiV, hisource⟩)
    let B : Set P := tsupport ρ ∪ (l '' closure U) ∪ (r '' closure U)
    have hBc : IsCompact B := (hcompact.union (hUc.image hl.continuous)).union
      (hUc.image hr.continuous)
    have hsB : tsupport ρ ⊆ B := fun _ hx => Or.inl (Or.inl hx)
    have hlB : MapsTo l (closure U) B := fun q hq => Or.inl (Or.inr ⟨q, hq, rfl⟩)
    have hrB : MapsTo r (closure U) B := fun q hq => Or.inr ⟨q, hq, rfl⟩
    have hBsource : B ⊆ f ⁻¹' (e i).source := by
      intro x hx
      rcases hx with (hx | ⟨q, hq, rfl⟩) | ⟨q, hq, rfl⟩
      · exact (hsupp hx).2
      · exact (hpairs q (hUV hq).1).2.2.1.2
      · exact (hpairs q (hUV hq).1).2.2.2.2
    exact ⟨ρ, U, B, hρ, hcompact, hbound, hU, hiU (mem_singleton _), hUc,
      fun _ hq => (hUV hq).2, hBc, hsB, hlB, hrB, hBsource,
      fun q hq => ⟨(hpairs q (hUV hq).1).1, (hpairs q (hUV hq).1).2.1⟩⟩
  choose ρ U B hρ hcompact hbound hU hiU hUc hsource hBc hsB hlB hrB hBsource hpairs using hlocal
  obtain ⟨t, W, hW, hcover⟩ := hZ.exists_finite_subcover_isCompact_closure U
    (fun i => (hU i).mem_nhds (hiU i))
  refine ⟨t, e, a, ρ, U, fun i => closure (W i), B, ?_, ?_⟩
  · intro i
    exact ⟨hρ i, hcompact i, hbound i, hU i, hiU i, hUc i,
      (hW i).2.2.1, (hW i).2.2.2, hsource i, hBc i, hsB i, hlB i, hrB i,
      hBsource i, hpairs i⟩
  · intro q hq
    obtain ⟨i, hit, hqi⟩ := mem_iUnion₂.mp (hcover hq)
    exact mem_iUnion₂.mpr ⟨i, hit, mem_interior.mpr
      ⟨W i, subset_closure, (hW i).1, hqi⟩⟩

end DifferentialGeometry.Manifold

end
