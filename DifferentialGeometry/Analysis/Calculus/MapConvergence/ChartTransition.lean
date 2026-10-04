import DifferentialGeometry.Analysis.Calculus.MapConvergence.FiniteComposition
import DifferentialGeometry.Analysis.Calculus.MapConvergence.EventualCongruence
import DifferentialGeometry.Topology.UniformConvergence
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.CheegerGromovCompactness

theorem mapCPConvergenceOn_chart_inverse_comp_of_transition_convergence
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F]
    {Y : ℕ → Type*} [∀ i, TopologicalSpace (Y i)]
    {U K : Set E} {p : ℕ}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {e : ∀ i, OpenPartialHomeomorph F (Y i)}
    {d : ∀ i, OpenPartialHomeomorph E (Y i)}
    {g : ∀ i, E → Y i} (q : OpenPartialHomeomorph E F) (hUq : U ⊆ q.source)
    (himage : ∀ L : Set E, IsCompact L → L ⊆ U →
      ∀ᶠ i in atTop, MapsTo (g i) L (e i).target)
    (hg : ∀ L : Set E, IsCompact L → L ⊆ U →
      MapCPConvergenceOn L p (fun i x => (e i).symm (g i x)) q)
    (hτ : ∀ S : Set F, IsCompact S → S ⊆ q.target →
      MapCPConvergenceOn S p (fun i x => (d i).symm (e i x)) q.symm)
    (hgc : ∀ L : Set E, IsCompact L → L ⊆ U →
      ∀ᶠ i in atTop, ContDiffOn ℝ (p : ℕ∞) (fun x => (e i).symm (g i x)) L)
    (hqc : ContDiffOn ℝ (p : ℕ∞) q U)
    (hτc : ∀ S : Set F, IsCompact S → S ⊆ q.target →
      ∀ᶠ i in atTop, ContDiffOn ℝ (p : ℕ∞) (fun x => (d i).symm (e i x)) S)
    (hτinf : ContDiffOn ℝ (p : ℕ∞) q.symm q.target)
    (hτimage : ∀ S : Set F, IsCompact S → S ⊆ q.target →
      ∀ᶠ i in atTop, MapsTo (e i) S (d i).target) :
    (∀ᶠ i in atTop, MapsTo (g i) K (d i).target) ∧
      MapCPConvergenceOn K p (fun i x => (d i).symm (g i x)) id := by
  have hzero := tendstoUniformlyOn_of_cPConvergence
    ((hg K hK hKU).mono_order (Nat.zero_le p))
  obtain ⟨S, hS, hSq, _, hSimage⟩ :=
    hzero.exists_isCompact_eventually_mapsTo_of_isCompact hK
      (hqc.continuousOn.mono hKU) q.open_target
      (fun _ hx => q.map_source (hUq (hKU hx)))
  constructor
  · filter_upwards [hSimage, hτimage S hS hSq, himage K hK hKU] with i hi hτi hgi
    intro x hx
    have hmem := hτi (hi hx)
    rwa [(e i).right_inv (hgi hx)] at hmem
  · have hcomp := mapCPConvergenceOn_comp_of_eventually_contDiffOn
      hU q.open_target hg hτ hgc hqc hτc hτinf
      (fun _ hx => q.map_source (hUq hx)) hK hKU
    obtain ⟨W, hW, hKW, hWU, hWc⟩ :=
      exists_open_between_and_isCompact_closure hK hU hKU
    have hWU' : W ⊆ U := subset_closure.trans hWU
    apply hcomp.congr_eventually hW hKW ?_
      (fun _ hx => (q.left_inv (hUq (hWU' hx))).symm)
    filter_upwards [himage (closure W) hWc hWU] with i hi x hx
    dsimp only
    rw [(e i).right_inv (hi (subset_closure hx))]

theorem mapCPConvergenceOn_chart_inverse_comp_of_partialDiffeomorph_transitions
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
    {Y : ℕ → Type*} [∀ i, TopologicalSpace (Y i)] [∀ i, ChartedSpace E (Y i)]
    {p : ℕ} {W : Set X} {K : Set E} (hW : IsOpen W) (hK : IsCompact K)
    (σ ψ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E X p)
    (hKdomain : K ⊆ σ.source ∩ σ ⁻¹' (W ∩ ψ.target))
    (e d : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E (Y i) p)
    (g : ∀ i, X → Y i)
    (hgc : ∀ i, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) p (g i) W)
    (himage : ∀ L : Set E, IsCompact L → L ⊆ σ.source ∩ σ ⁻¹' (W ∩ ψ.target) →
      ∀ᶠ i in atTop, MapsTo (g i ∘ σ) L (e i).target)
    (hg : ∀ L : Set E, IsCompact L → L ⊆ σ.source ∩ σ ⁻¹' (W ∩ ψ.target) →
      MapCPConvergenceOn L p (fun i x => (e i).symm (g i (σ x))) (σ.trans ψ.symm))
    (hτ : ∀ S : Set E, IsCompact S → S ⊆ (σ.trans ψ.symm).target →
      MapCPConvergenceOn S p (fun i x => (d i).symm (e i x)) (σ.trans ψ.symm).symm)
    (hτsource : ∀ S : Set E, IsCompact S → S ⊆ (σ.trans ψ.symm).target →
      ∀ᶠ i in atTop, S ⊆ ((e i).trans (d i).symm).source) :
    (∀ᶠ i in atTop, MapsTo (g i ∘ σ) K (d i).target) ∧
      MapCPConvergenceOn K p (fun i x => (d i).symm (g i (σ x))) id := by
  let U : Set E := σ.source ∩ σ ⁻¹' (W ∩ ψ.target)
  have hU : IsOpen U :=
    σ.toOpenPartialHomeomorph.isOpen_inter_preimage (hW.inter ψ.open_target)
  have hUq : U ⊆ (σ.trans ψ.symm).source := fun _ hx => ⟨hx.1, hx.2.2⟩
  have hσ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) p σ U :=
    σ.contMDiffOn_toFun.mono inter_subset_left
  have hσW : MapsTo σ U W := fun _ hx => hx.2.1
  apply mapCPConvergenceOn_chart_inverse_comp_of_transition_convergence
    (E := E) (F := E) (Y := Y) (U := U) (K := K) (p := p)
    (e := fun i => (e i).toOpenPartialHomeomorph)
    (d := fun i => (d i).toOpenPartialHomeomorph)
    (g := fun i => g i ∘ σ)
    hU hK hKdomain (σ.trans ψ.symm).toOpenPartialHomeomorph hUq himage hg hτ
  · intro L hL hLU
    filter_upwards [himage L hL hLU] with i hi
    have hcomp := (e i).contMDiffOn_invFun.comp
      (((hgc i).comp hσ hσW).mono hLU) hi
    exact hcomp.contDiffOn
  · exact (σ.trans ψ.symm).contMDiffOn_toFun.contDiffOn.mono hUq
  · intro S hS hSq
    filter_upwards [hτsource S hS hSq] with i hi
    exact (((e i).trans (d i).symm).contMDiffOn_toFun.contDiffOn).mono hi
  · exact (σ.trans ψ.symm).contMDiffOn_invFun.contDiffOn
  · intro S hS hSq
    filter_upwards [hτsource S hS hSq] with i hi x hx
    exact (hi hx).2

theorem mapCPConvergenceOn_chart_inverse_comp_of_source_chart_convergence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E H'}
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    {Y : ℕ → Type*} [∀ i, TopologicalSpace (Y i)] [∀ i, ChartedSpace H' (Y i)]
    {p : ℕ} {V : Set X} {K : Set E} (hV : IsOpen V) (hK : IsCompact K)
    (σ ψ : PartialDiffeomorph 𝓘(ℝ, E) I E X p)
    (hKdomain : K ⊆ σ.source ∩ σ ⁻¹' (V ∩ ψ.target))
    (Φ : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) J E (Y i) p)
    (F : ∀ i, X → Y i)
    (hF : ∀ᶠ i in atTop, ContMDiffOn I J p (F i) V)
    (himage : ∀ L : Set E, IsCompact L → L ⊆ ψ.source ∩ ψ ⁻¹' V →
      ∀ᶠ i in atTop, MapsTo (F i ∘ ψ) L (Φ i).target)
    (hconv : ∀ L : Set E, IsCompact L → L ⊆ ψ.source ∩ ψ ⁻¹' V →
      MapCPConvergenceOn L p (fun i x => (Φ i).symm (F i (ψ x))) id) :
    (∀ᶠ i in atTop, MapsTo (F i ∘ σ) K (Φ i).target) ∧
      MapCPConvergenceOn K p (fun i x => (Φ i).symm (F i (σ x))) (σ.trans ψ.symm) := by
  let U : Set E := σ.source ∩ σ ⁻¹' (V ∩ ψ.target)
  let D : Set E := ψ.source ∩ ψ ⁻¹' V
  let q : E → E := σ.trans ψ.symm
  have hU : IsOpen U :=
    σ.toOpenPartialHomeomorph.isOpen_inter_preimage (hV.inter ψ.open_target)
  have hD : IsOpen D := ψ.toOpenPartialHomeomorph.isOpen_inter_preimage hV
  have hUq : U ⊆ (σ.trans ψ.symm).source := fun _ hx => ⟨hx.1, hx.2.2⟩
  have hqc : ContDiffOn ℝ (p : ℕ∞) q U :=
    (σ.trans ψ.symm).contMDiffOn_toFun.contDiffOn.mono hUq
  have hψinv (x : X) (hx : x ∈ ψ.target) : ψ (ψ.symm x) = x :=
    ψ.toPartialEquiv.right_inv hx
  have hmap : MapsTo q U D := by
    intro x hx
    refine ⟨ψ.toOpenPartialHomeomorph.map_target hx.2.2, ?_⟩
    change ψ (ψ.symm (σ x)) ∈ V
    rw [hψinv (σ x) hx.2.2]
    exact hx.2.1
  have hψc : ContMDiffOn 𝓘(ℝ, E) I p ψ D :=
    ψ.contMDiffOn_toFun.mono inter_subset_left
  have hψV : MapsTo ψ D V := fun _ hx => hx.2
  have hAc : ∀ S : Set E, IsCompact S → S ⊆ D →
      ∀ᶠ i in atTop, ContDiffOn ℝ (p : ℕ∞)
        (fun x => (Φ i).symm (F i (ψ x))) S := by
    intro S hS hSD
    filter_upwards [hF, himage S hS hSD] with i hi hiimage
    have hcomp := (Φ i).contMDiffOn_invFun.comp
      ((hi.comp hψc hψV).mono hSD) hiimage
    exact hcomp.contDiffOn
  have hqconv : ∀ L : Set E, IsCompact L → L ⊆ U →
      MapCPConvergenceOn L p (fun _ : ℕ => q) q :=
    fun L hL hLU => mapCInfConvergence_const q L hL hLU p
  have hcomp := mapCPConvergenceOn_comp_of_eventually_contDiffOn
    (E := E) (F := E) (G := E) (U := U) (V := D) (p := p)
    hU hD hqconv hconv
    (fun L _ hLU => Eventually.of_forall fun _ => hqc.mono hLU)
    hqc hAc contDiffOn_id hmap hK hKdomain
  constructor
  · have hqK : IsCompact (q '' K) :=
      hK.image_of_continuousOn (hqc.continuousOn.mono hKdomain)
    have hqKD : q '' K ⊆ D := by
      rintro _ ⟨x, hx, rfl⟩
      exact hmap (hKdomain hx)
    filter_upwards [himage (q '' K) hqK hqKD] with i hi x hx
    have hmem := hi ⟨x, hx, rfl⟩
    change F i (ψ (ψ.symm (σ x))) ∈ (Φ i).target at hmem
    rwa [hψinv (σ x) (hKdomain hx).2.2] at hmem
  · apply hcomp.congr_eventually hU hKdomain ?_ (Set.eqOn_refl _ _)
    apply Eventually.of_forall
    intro i x hx
    change (Φ i).symm (F i (σ x)) = (Φ i).symm (F i (ψ (ψ.symm (σ x))))
    rw [hψinv (σ x) hx.2.2]

end DifferentialGeometry.CheegerGromovCompactness
