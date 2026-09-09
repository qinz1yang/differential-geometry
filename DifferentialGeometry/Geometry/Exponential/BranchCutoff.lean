import DifferentialGeometry.Geometry.Exponential.DiagInvBranch
import DifferentialGeometry.Geometry.Exponential.BranchEnergyBounds
import DifferentialGeometry.Geometry.Operator.CutoffSupport
import DifferentialGeometry.Analysis.Calculus.CompactCutoff

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

theorem DiagInvBranch.exists_cutoff_uniform_energy_gap
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {c : M}
    (B : DiagInvBranch g hEnorm c)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {D : Set (M × M)} (hD : IsOpen D) (hcD : (c, c) ∈ D) :
    ∃ U : Set M, IsOpen U ∧ c ∈ U ∧ IsCompact (closure U) ∧
      (∀ p ∈ closure U, (0 : E) ∈ (B.fixed p).hom.source) ∧
      ∃ χ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ χ ∧ HasCompactSupport χ ∧
        (∀ p ∈ closure U, χ =ᶠ[nhds p] 1) ∧
        closure U ×ˢ tsupport χ ⊆ B.dom ∩ D ∧ range χ ⊆ Icc 0 1 ∧
        ∃ b : ℝ, 0 < b ∧ ∃ K : Set M, IsCompact K ∧ K ⊆ tsupport χ ∧
          (∀ p ∈ closure U, ∀ q ∈ K, b ≤ branchEnergy g (B.fixed p) q) ∧
          ∀ q ∉ K, Operator.laplacian cov g χ q = 0 ∧
            Operator.gradientFun g χ q = 0 := by
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : NormalSpace M := inferInstance
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have hn : B.dom ∩ D ∈ nhds (c, c) :=
    (B.hom.open_target.inter hD).mem_nhds ⟨B.center_mem, hcD⟩
  rw [nhds_prod_eq] at hn
  obtain ⟨S₁, hS₁, S₂, hS₂, hS⟩ := Filter.mem_prod_iff.mp hn
  obtain ⟨V₁, hV₁S, hV₁, hcV₁⟩ := mem_nhds_iff.mp hS₁
  obtain ⟨V₂, hV₂S, hV₂, hcV₂⟩ := mem_nhds_iff.mp hS₂
  let Z : Set M := (zeroSection E (TangentSpace I)) ⁻¹' B.hom.source
  have hZ : IsOpen Z := B.hom.open_source.preimage
    (Bundle.contMDiff_zeroSection (IB := I) (F := E) (n := ∞) ℝ (TangentSpace I)).continuous
  have hcZ : c ∈ Z := B.zero_mem
  let V := (V₁ ∩ V₂) ∩ Z
  have hV : IsOpen V := (hV₁.inter hV₂).inter hZ
  have hcV : c ∈ V := ⟨⟨hcV₁, hcV₂⟩, hcZ⟩
  have hVV : V ×ˢ V ⊆ B.dom ∩ D := fun z hz => hS ⟨hV₁S hz.1.1.1, hV₂S hz.2.1.2⟩
  obtain ⟨L, hL, hcL, hLV⟩ := exists_compact_between isCompact_singleton hV
    (singleton_subset_iff.mpr hcV)
  have hcLi : c ∈ interior L := hcL (mem_singleton c)
  obtain ⟨χ, hχ, hcχ, hχone, hsχ, hrχ⟩ := DifferentialGeometry.Analysis.exists_mfd_bump
    (I := I) hL hV hLV
  obtain ⟨W, hW, hLW, hWone⟩ := mem_nhdsSet_iff_exists.mp hχone
  let K := tsupport χ \ W
  have hK : IsCompact K := hcχ.diff hW
  have hvanish : ∀ q ∉ K, Operator.laplacian cov g χ q = 0 ∧
      Operator.gradientFun g χ q = 0 := by
    intro q hq
    have he : ∃ a : ℝ, χ =ᶠ[nhds q] fun _ => a := by
      by_cases hqs : q ∈ tsupport χ
      · have hqW : q ∈ W := by by_contra hqW; exact hq ⟨hqs, hqW⟩
        exact ⟨1, Filter.Eventually.mono (hW.mem_nhds hqW) hWone⟩
      · exact ⟨0, notMem_tsupport_iff_eventuallyEq.mp hqs⟩
    obtain ⟨a, ha⟩ := he
    exact Operator.laplacian_gradient_eq_zero_of_eventuallyEq_const cov g ha
  obtain ⟨L₀, hL₀, hcL₀, hL₀L⟩ := exists_compact_between isCompact_singleton isOpen_interior
    (singleton_subset_iff.mpr hcLi)
  let U := interior L₀
  have hUL₀ : closure U ⊆ L₀ := closure_minimal interior_subset hL₀.isClosed
  have hUL : closure U ⊆ L := hUL₀.trans (hL₀L.trans interior_subset)
  have hUc : IsCompact (closure U) := hL₀.of_isClosed_subset isClosed_closure hUL₀
  have hpair : closure U ×ˢ K ⊆ B.dom := fun z hz =>
    (hVV ⟨hLV (hUL hz.1), hsχ hz.2.1⟩).1
  obtain ⟨b, hb, hgap⟩ := B.exists_pos_le_branchEnergy_fixed_of_isCompact (hUc.prod hK)
    hpair (fun z hz heq => hz.2.2 (heq ▸ hLW (hUL hz.1)))
  have hzero : ∀ p ∈ closure U, (0 : E) ∈ (B.fixed p).hom.source := by
    intro p hp
    exact (hLV (hUL hp)).2
  refine ⟨U, isOpen_interior, hcL₀ (mem_singleton c), hUc, hzero, χ, hχ, hcχ, ?_, ?_, hrχ,
    b, hb, K, hK, sdiff_subset, ?_, hvanish⟩
  · intro p hp
    exact Filter.Eventually.mono (hW.mem_nhds (hLW (hUL hp))) hWone
  · intro z hz
    exact hVV ⟨hLV (hUL hz.1), hsχ hz.2⟩
  · intro p hp q hq
    exact hgap (p, q) ⟨hp, hq⟩

end DifferentialGeometry.Geometry.Riemannian.Exponential
